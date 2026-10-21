{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
      };
  in {
    devShell = pkgs.mkShellNoCC {
      packages = with pkgs.coqPackages_8_20; [
        coq
        stdlib
        stdpp
        vscoq-language-server
      ];
    };
  });
}
