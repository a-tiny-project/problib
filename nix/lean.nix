{ pkgs, toolchainFiles }:
let
  lib = pkgs.lib;
  parseVersion =
    path:
    let
      declaration = lib.removeSuffix "\n" (builtins.readFile path);
      matched = builtins.match "leanprover/lean4:v([0-9]+\\.[0-9]+\\.[0-9]+)" declaration;
    in
    if matched == null then
      throw "Lean toolchain ${toString path} must pin one stable leanprover/lean4 release"
    else
      builtins.head matched;
  versions = lib.unique (map parseVersion toolchainFiles);
  version =
    if toolchainFiles == [ ] then
      throw "no Lean toolchain files supplied"
    else if builtins.length versions != 1 then
      throw "Lean toolchains disagree: ${lib.concatStringsSep ", " versions}"
    else
      builtins.head versions;
  sources = {
    x86_64-linux = {
      platform = "linux";
      hash = "sha256-B6YzzI2RUcvAiCXqTN2lDUsCosnLhSwBMbEwRvScrX8=";
    };
    aarch64-linux = {
      platform = "linux_aarch64";
      hash = "sha256-sb8dPFhrds9KhiEqWV2Lnt2Z9DikHM6F1XgPqTR8gRs=";
    };
    x86_64-darwin = {
      platform = "darwin";
      hash = "sha256-bax6j51tC8M5tOqTdsBqiPP9Gn9GK+s8fe2fvJNPP7U=";
    };
    aarch64-darwin = {
      platform = "darwin_aarch64";
      hash = "sha256-JkEFUAyKvfN7aP/gM5Cng+0lmAeAciJpjajdktbOCic=";
    };
  };
  system = pkgs.stdenv.hostPlatform.system;
  source = sources.${system} or (throw "unsupported Lean host system: ${system}");
in
pkgs.stdenvNoCC.mkDerivation {
  pname = "lean4";
  inherit version;
  src = pkgs.fetchurl {
    url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${source.platform}.tar.zst";
    inherit (source) hash;
  };
  sourceRoot = "lean-${version}-${source.platform}";
  nativeBuildInputs = [
    pkgs.zstd
  ]
  ++ lib.optionals pkgs.stdenv.hostPlatform.isLinux [
    pkgs.patchelf
  ];
  dontConfigure = true;
  dontBuild = true;
  dontStrip = true;
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -R . "$out/"
    runHook postInstall
  '';
  postFixup = lib.optionalString pkgs.stdenv.hostPlatform.isLinux ''
    for executable in cadical clang lake ld.lld lean leanc leanchecker leanir llvm-ar; do
      patchelf --set-interpreter ${pkgs.stdenv.cc.bintools.dynamicLinker} \
        "$out/bin/$executable"
    done
  '';
  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    "$out/bin/lean" --version | grep -F "Lean (version ${version},"
    "$out/bin/lake" --version | grep -F "(Lean version ${version})"
    test -f "$out/lib/lean/Lean.olean"
    runHook postInstallCheck
  '';
  passthru = {
    inherit toolchainFiles;
  };
  meta = {
    description = "Lean theorem prover and Lake build tool";
    homepage = "https://lean-lang.org/";
    license = lib.licenses.asl20;
    mainProgram = "lean";
    platforms = builtins.attrNames sources;
  };
}
