{
  description = "Lean 4 Project";
  
  nixConfig = {
    substituters = [ "https://cache.nixos.org" ];
  };

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  outputs = inputs @ {
    flake-parts,
    ...
  }:
    flake-parts.lib.mkFlake {inherit inputs;} {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = {
        pkgs,
        ...
      }: {
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
            elan
            stdenv
            typst
          ];
          shellHook = ''
            export TYPST_ROOT="$PWD"
          '';
        };
      };
    };
}
