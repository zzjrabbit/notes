{
  description = "Lean 4 Project";
  
  nixConfig = {
    substituters = [ "https://cache.nixos.org" ];
  };

  inputs = {
    nixpkgs.url = "git+ssh://git@github.com/nixos/nixpkgs?ref=nixos-unstable&shallow=1";
    flake-parts.url = "git+ssh://git@github.com/hercules-ci/flake-parts?shallow=1";
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
            cargo
            elan
            rustc
            rustfmt
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
