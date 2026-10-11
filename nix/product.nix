{
  pkgs,
  src,
  release,
}:
let
  lib = pkgs.lib;
  isLean = release.language == "lean";
  isLibrary = release.library or false;
  hasNativeZig = isLean && (release ? zig);
  hasZig = !isLean || hasNativeZig;
  # The driver certifies this count against the immutable source ledger.
  isConsumer =
    if !hasZig then
      false
    else if
      release ? zig_claim_count && builtins.isInt release.zig_claim_count && release.zig_claim_count == 0
    then
      true
    else
      throw "Zig release requires a certified zero claim count";
  workspaces = release.workspaces or [ ];
  # A library builds with the official Zig release its consumers have; an
  # application with zig-consumer, built from source.
  isOfficialZig = (release.zig_compiler or "zig-consumer") == "zig";
  zig =
    if isOfficialZig then
      import ./zig-official.nix {
        inherit pkgs;
        version = release.zig;
      }
    else
      import ./zig.nix {
        inherit pkgs;
        version = release.zig;
        consumer = isConsumer;
      };
  toolchain =
    if isLean then
      import ./lean.nix {
        inherit pkgs;
        toolchainFiles = [
          (src + "/lean-toolchain")
        ]
        ++ map (workspace: src + "/${workspace.root}/lean-toolchain") workspaces;
      }
    else
      zig;
  nativeZig = zig;
  lakeFlags = lib.optionalString hasNativeZig "-R -Kzig=${nativeZig}/bin/zig ";
  # Programs the release's declared checks run beyond its toolchain.
  checkTools = map (name: pkgs.${name}) (release.check_tools or [ ]);
  nativeInputs = [
    toolchain
  ]
  ++ checkTools
  ++ lib.optional (libraries != [ ]) pkgs.pkgconf
  ++ lib.optional (hasNativeZig && release.executables != [ ]) pkgs.makeWrapper
  ++ lib.optional (hasZig && pkgs.stdenv.hostPlatform.isDarwin) pkgs.nodejs
  ++ lib.optional hasNativeZig pkgs.python3
  ++ lib.optional hasNativeZig nativeZig;
  libraries = map (name: import (./. + "/${name}.nix") { inherit pkgs; }) (release.libraries or [ ]);
  environment =
    if isLean then
      {
        LEAN_CC = "${pkgs.stdenv.cc}/bin/cc";
        NIX_LDFLAGS = "-L${toolchain}/lib";
      }
      // lib.optionalAttrs hasNativeZig nativeZig.buildRunnerEnvironment
    else
      toolchain.buildRunnerEnvironment;
  # An explicit target turns off native framework discovery in the consumer
  # compiler, so a consumer release on Darwin builds for the host target.
  zigTargetArgs =
    (
      if isConsumer && pkgs.stdenv.hostPlatform.isDarwin then
        [ "-Dcpu=baseline" ]
      else
        [ "-Dtarget=${zig.hostTarget or ""}" ]
    )
    # The official Zig hands a compile a dangling dynamic linker path, and finds
    # the native one only through /usr/bin/env, which the sandbox lacks, so its
    # Linux target is static musl and names no dynamic linker.
    ++ lib.optional (
      pkgs.stdenv.hostPlatform.isLinux && !isOfficialZig
    ) "-Ddynamic-linker=${pkgs.stdenv.cc.bintools.dynamicLinker}";
  # The configure options of each Zig command, defined once. The commands below
  # and `configureProfiles` share these lists, so the gate configures what Nix runs.
  zigBuildArgs = zigTargetArgs ++ [ "--release=small" ];
  zigCheckArgs = zigTargetArgs;
  zigFlags = "-j$NIX_BUILD_CORES -fno-incremental";
  # Zig 0.17.0 resolves a dependency's configure inputs under the build root,
  # so builds run there.
  buildRoot = lib.escapeShellArg release.root;
  typst = import ./typst.nix { inherit pkgs; };
  fonts = [
    pkgs.libertinus
    pkgs.libertine
    pkgs.dejavu_fonts
    pkgs.inconsolata
    pkgs.noto-fonts
  ];
  package = pkgs.stdenv.mkDerivation (
    environment
    // {
      pname = release.name;
      version = lib.removePrefix "v" release.version;
      inherit src;
      nativeBuildInputs = nativeInputs;
      buildInputs = libraries;
      strictDeps = true;
      dontConfigure = true;
      dontStrip = true;
      preBuild = ''
        export ZIG_LOCAL_CACHE_DIR="$TMPDIR/zig-local-cache"
        export ZIG_GLOBAL_CACHE_DIR="$TMPDIR/zig-global-cache"
        export TINY_ZIG_CACHE_LEASE_ROOT="$TMPDIR/zig-cache-leases"
        export TINY_BUILD_RESOURCE_ROOT="$TMPDIR/build-resources"
      ''
      + lib.optionalString isLean ''
        export LEAN_NUM_THREADS="$NIX_BUILD_CORES"
      '';
      buildPhase = ''
        runHook preBuild
      ''
      + (
        if isLean then
          ''
            lake ${lakeFlags}build ${lib.escapeShellArgs release.targets}
          ''
        else
          ''
            (cd ${buildRoot} && zig build ${zigFlags} ${lib.escapeShellArgs zigBuildArgs} --prefix "$out")
          ''
      )
      + ''
        runHook postBuild
      '';
      doCheck = true;
      checkPhase = ''
        runHook preCheck
      ''
      + (
        if isLean then
          lib.optionalString (release.checks != [ ]) ''
            lake ${lakeFlags}build ${lib.escapeShellArgs release.checks}
          ''
          + lib.concatMapStringsSep "\n" (target: ''
            lake ${lakeFlags}exe ${lib.escapeShellArg target}
          '') release.tests
          + lib.concatMapStringsSep "\n" (workspace: ''
            (
              cd ${lib.escapeShellArg workspace.root}
              lake ${lakeFlags}build ${lib.escapeShellArgs workspace.targets}
              ${lib.concatStringsSep "\n" (
                map (audit: ''
                  lake ${lakeFlags}env lean ${lib.escapeShellArg audit}
                '') workspace.audits
                ++ map (test: ''
                  lake ${lakeFlags}exe ${lib.escapeShellArg test}
                '') (workspace.tests or [ ])
              )}
            )
          '') workspaces
          # The native root's own checks, built as a user's checkout builds
          # them, and each example file elaborated against the built library.
          + lib.concatMapStringsSep "\n" (step: ''
            zig build ${zigFlags} ${lib.escapeShellArgs zigCheckArgs} ${lib.escapeShellArg step}
          '') (release.native.checks or [ ])
          + lib.concatMapStringsSep "\n" (example: ''
            lake ${lakeFlags}env lean ${lib.escapeShellArg example}
          '') (release.examples or [ ])
        else
          lib.concatMapStringsSep "\n" (step: ''
            (cd ${buildRoot} && zig build ${zigFlags} ${lib.escapeShellArgs zigCheckArgs} ${lib.escapeShellArg step})
          '') release.checks
          # Each example builds its steps against the release root, as a user's
          # checkout of the release would.
          + lib.concatMapStringsSep "\n" (example: ''
            (cd ${buildRoot}/${lib.escapeShellArg example.root} && zig build ${zigFlags} ${lib.escapeShellArgs zigCheckArgs} ${lib.escapeShellArgs example.steps})
          '') (release.examples or [ ])
      )
      + ''
        runHook postCheck
      '';
      installPhase = ''
        runHook preInstall
        mkdir -p "$out/share/${release.name}"
        cp -R ${src}/. "$out/share/${release.name}/"
      ''
      + lib.optionalString isLean (
        lib.concatMapStringsSep "\n" (target: ''
          install -Dm755 .lake/build/bin/${lib.escapeShellArg target} "$out/bin/"${lib.escapeShellArg target}
        '') release.executables
      )
      + lib.optionalString hasNativeZig (
        lib.concatMapStringsSep "\n" (target: ''
          wrapProgram "$out/bin/"${lib.escapeShellArg target} \
            --prefix PATH : "${lib.makeBinPath [ nativeZig ]}"
        '') release.executables
      )
      + ''
        runHook postInstall
      '';
      # The compile evidence recipe patches this Zig's standard library.
      passthru = lib.optionalAttrs hasZig { inherit zig; };
      meta = {
        license = lib.licenses.agpl3Plus;
        homepage = "https://github.com/a-tiny-project/${release.name}";
      }
      // lib.optionalAttrs (!isLibrary) { mainProgram = release.name; };
      doInstallCheck = !isLibrary;
      installCheckPhase = ''
        "$out/bin/${release.name}" --help > "$TMPDIR/help"
        test -s "$TMPDIR/help"
      '';
    }
  );
in
{
  inherit package;
  # Each Zig command's configure options and the release root it runs in. The
  # checks share one list, since a step name does not change the configured graph.
  configureProfiles = lib.optionals (!isLean) (
    [
      {
        variant = "build";
        root = release.root;
        args = zigBuildArgs;
      }
    ]
    ++ lib.optional (release.checks != [ ]) {
      variant = "check";
      root = release.root;
      args = zigCheckArgs;
    }
  );
  shells = {
    default = pkgs.mkShell (
      environment
      // {
        packages = nativeInputs;
        buildInputs = libraries;
        shellHook = ''
          export TINY_ZIG_CACHE_LEASE_ROOT="''${XDG_CACHE_HOME:-$HOME/.cache}/a-tiny-project/zig-leases"
          export TINY_BUILD_RESOURCE_ROOT="''${XDG_CACHE_HOME:-$HOME/.cache}/a-tiny-project/build-resources"
        '';
      }
    );
  }
  // lib.optionalAttrs (release.paper or false) {
    paper = pkgs.mkShell {
      packages = [
        toolchain
        typst
        pkgs.gnumake
        pkgs.python3
      ];
      TYPST_FONT_PATHS = lib.concatStringsSep ":" (map (font: "${font}/share/fonts") fonts);
    };
  };
}
