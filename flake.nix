{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-26.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = import nixpkgs {
        inherit system;
      };
  in {
    devShell = pkgs.mkShellNoCC {
      packages = with pkgs.rocqPackages_9_1; [
        rocq-core
        stdlib
        stdpp
        vsrocq-language-server
      ];
    };
  });
}
