{
  description = "Independent source release";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  outputs =
    { self, nixpkgs }:
    let
      release = builtins.fromJSON (builtins.readFile ./release.json);
      systems =
        release.systems or [
          "x86_64-linux"
          "aarch64-linux"
          "x86_64-darwin"
          "aarch64-darwin"
        ];
      eachSystem = nixpkgs.lib.genAttrs systems;
      products = eachSystem (
        system:
        import ./nix/product.nix {
          pkgs = import nixpkgs {
            inherit system;
            config.allowDeprecatedx86_64Darwin = true;
          };
          src = self;
          inherit release;
        }
      );
    in
    {
      packages = eachSystem (system: {
        default = products.${system}.package;
      });
      checks = eachSystem (system: {
        default = products.${system}.package;
      });
      devShells = eachSystem (system: products.${system}.shells);
    };
}
