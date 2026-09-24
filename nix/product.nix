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
  # A Zig release that names a consumer module builds with the consumer
  # compiler. Every other Zig release keeps the patched monorepo compiler.
  isConsumer = !isLean && (release ? consumer_module);
  workspaces = release.workspaces or [ ];
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
      import ./zig.nix {
        inherit pkgs;
        version = release.zig;
        consumer = isConsumer;
      };
  nativeZig = import ./zig.nix {
    inherit pkgs;
    version = release.zig;
  };
  lakeFlags = lib.optionalString hasNativeZig "-R -Kzig=${nativeZig}/bin/zig ";
  nativeInputs = [
    toolchain
  ]
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
  zigTarget =
    if isConsumer && pkgs.stdenv.hostPlatform.isDarwin then
      "-Dcpu=baseline"
    else
      "-Dtarget=${toolchain.hostTarget or ""}";
  zigFlags =
    "-j$NIX_BUILD_CORES -fno-incremental ${zigTarget}"
    + lib.optionalString pkgs.stdenv.hostPlatform.isLinux " -Ddynamic-linker=${pkgs.stdenv.cc.bintools.dynamicLinker}";
  buildFile = lib.escapeShellArg "${release.root}/build.zig";
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
            zig build ${zigFlags} --build-file ${buildFile} --release=small --prefix "$out"
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
              ${lib.concatMapStringsSep "\n" (audit: ''
                lake ${lakeFlags}env lean ${lib.escapeShellArg audit}
              '') workspace.audits}
            )
          '') workspaces
        else
          lib.concatMapStringsSep "\n" (step: ''
            zig build ${zigFlags} --build-file ${buildFile} ${lib.escapeShellArg step}
          '') release.checks
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
