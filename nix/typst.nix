{ pkgs }:
let
  lib = pkgs.lib;
  version = "0.15.1";
  buildHash = "9dfd3a08";
  releases = {
    x86_64-linux = {
      target = "x86_64-unknown-linux-musl";
      hash = "sha256-ptB30Kle7VouunFbLa4GvpVPYkzL+FdYoD84ne0zEYw=";
    };
    aarch64-linux = {
      target = "aarch64-unknown-linux-musl";
      hash = "sha256-WqjXSj2QbmDqEqZqwvN/ju8bFMutcYKnReOToQwj3O4=";
    };
    x86_64-darwin = {
      target = "x86_64-apple-darwin";
      hash = "sha256-f5/dlYSGYkXemnngrdj5I2+ub0CopF4sR3HMwU204Po=";
    };
    aarch64-darwin = {
      target = "aarch64-apple-darwin";
      hash = "sha256-SPYu0DSqOnl4MJV5rGygAEXi7w2nMRToryfP2OdNwFo=";
    };
  };
  release =
    releases.${pkgs.stdenv.hostPlatform.system}
      or (throw "unsupported Typst release host system: ${pkgs.stdenv.hostPlatform.system}");
in
pkgs.stdenvNoCC.mkDerivation {
  pname = "typst";
  inherit version;

  src = pkgs.fetchurl {
    url = "https://github.com/typst/typst/releases/download/v${version}/typst-${release.target}.tar.xz";
    name = "typst-${version}-${release.target}.tar.xz";
    inherit (release) hash;
  };
  sourceRoot = "typst-${release.target}";

  dontBuild = true;
  dontStrip = true;

  installPhase = ''
    runHook preInstall

    install -Dm755 typst "$out/bin/typst"
    install -Dm644 LICENSE "$out/share/licenses/typst/LICENSE"
    install -Dm644 NOTICE "$out/share/licenses/typst/NOTICE"

    runHook postInstall
  '';

  doInstallCheck = true;
  installCheckPhase = ''
    test "$("$out/bin/typst" --version)" = "typst ${version} (${buildHash})"
  '';

  meta = {
    description = "Official Typst release binary used for byte-locked figures";
    homepage = "https://typst.app";
    license = lib.licenses.asl20;
    mainProgram = "typst";
    platforms = builtins.attrNames releases;
    sourceProvenance = [ lib.sourceTypes.binaryNativeCode ];
  };
}
