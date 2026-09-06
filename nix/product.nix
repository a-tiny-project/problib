{
  pkgs,
  src,
  release,
}:
let
  lib = pkgs.lib;
  isLean = release.language == "lean";
  isLibrary = release.library or false;
  hasPlugin = release ? plugin;
  toolchain =
    if isLean then
      import ./lean.nix {
        inherit pkgs;
        toolchainFiles = [ (src + "/lean-toolchain") ];
      }
    else
      import ./zig.nix {
        inherit pkgs;
        version = release.zig;
      };
  nativeInputs = [
    toolchain
    pkgs.pkgconf
    pkgs.makeWrapper
    pkgs.nodejs
    pkgs.flock
  ]
  ++ lib.optional hasPlugin pkgs.jq
  ++ lib.optional isLean pkgs.python3;
  libraries = if isLean then [ ] else import ./platform.nix { inherit pkgs; };
  environment =
    if isLean then
      {
        LEAN_CC = "${pkgs.stdenv.cc}/bin/cc";
        NIX_LDFLAGS = "-L${toolchain}/lib";
      }
    else
      toolchain.buildRunnerEnvironment;
  zigFlags =
    "-j$NIX_BUILD_CORES -fno-incremental -Dtarget=${toolchain.hostTarget or ""}"
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
      '';
      buildPhase = ''
        runHook preBuild
      ''
      + (
        if isLean then
          ''
            lake build ${lib.escapeShellArgs release.targets}
          ''
        else
          ''
            zig build ${zigFlags} --build-file ${buildFile} --release=small --prefix "$out"
          ''
          + lib.optionalString hasPlugin ''
            zig build ${zigFlags} --build-file ${lib.escapeShellArg "${release.plugin}/build.zig"} \
              ${lib.escapeShellArgs (import ./stardust.nix)} --prefix "$out"
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
            lake build ${lib.escapeShellArgs release.checks}
          ''
          + lib.concatMapStringsSep "\n" (target: ''
            lake exe ${lib.escapeShellArg target}
          '') release.tests
        else
          lib.concatMapStringsSep "\n" (step: ''
            zig build ${zigFlags} --build-file ${buildFile} ${lib.escapeShellArg step}
          '') release.checks
      )
      + lib.optionalString hasPlugin ''
        export TINY_STARDUST_ZIG="${toolchain}/bin/zig"
        export TINY_STARDUST_PLUGIN="$out/lib/libtiny_stardust${pkgs.stdenv.hostPlatform.extensions.sharedLibrary}"
        set +e
        "$out/bin/stardust" zig ${lib.escapeShellArg "${release.plugin}/testdata/live.zig"} \
          --repository-root "$PWD/deps" --json > "$TMPDIR/live.json"
        stardust_status=$?
        set -e
        test "$stardust_status" -eq 2
        jq -e '.schema == "tiny.stardust.snapshot-document/v8" and
          .terminal == "complete" and .producer_counts.functions > 0 and
          .reconciliation == "matched"' "$TMPDIR/live.json"
      ''
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
      + lib.optionalString hasPlugin ''
        wrapProgram "$out/bin/stardust" \
          --set TINY_STARDUST_ZIG "${toolchain}/bin/zig" \
          --set TINY_STARDUST_PLUGIN "$out/lib/libtiny_stardust${pkgs.stdenv.hostPlatform.extensions.sharedLibrary}"
      ''
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
