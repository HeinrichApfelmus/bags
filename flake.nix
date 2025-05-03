{
  description = ''
    Development shell for the `bags` package
  '';

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    agda2hs.url = "github:agda/agda2hs?ref=47eb94934b18971b18ef45cc91c6e4f7200e1803";
  };

  outputs = {self, nixpkgs, flake-utils, agda2hs}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        # ###########################################
        # Imports

        pkgs = import nixpkgs { inherit system; };
        lib  = import ./nix/lib.nix {
          inherit pkgs;
          agda2hs-lib = agda2hs.lib.${system};
        };
        
        # ###########################################
        # Helpers

        # TODO: Specific Haskell compiler

        base-lib = lib.mkDerivation {
          pname = "base";
          meta = {};
          version = "4.18";
          preBuild = ''
            echo "{-# OPTIONS --sized-types #-}" > Everything.agda
            echo "module Everything where" >> Everything.agda
            find . -name '*.agda' ! -name 'Everything.agda' | sed -e 's/.\///;s/\//./g;s/\.agda$//;s/^/import /' >> Everything.agda
          '';
          src = pkgs.fetchFromGitHub {
            repo = "agda2hs";
            owner = "agda";
            rev = "47eb94934b18971b18ef45cc91c6e4f7200e1803";
            hash = "sha256-hMa+ESDHLTjKJwbLChwes4HUrMCNRSIDC5x79b2Z5a0=";
          };
          prePatch = ''
            cd lib/base
          '';
        };
        containers-lib = lib.mkDerivation {
          pname = "containers";
          meta = { };
          version = "0.8";
          buildInputs = [ base-lib ];
          everythingFile = "./agda/containers.agda";
          src = pkgs.fetchFromGitHub {
            repo = "agda2hs";
            owner = "agda";
            rev = "47eb94934b18971b18ef45cc91c6e4f7200e1803";
            hash = "sha256-hMa+ESDHLTjKJwbLChwes4HUrMCNRSIDC5x79b2Z5a0=";
          };
          prePatch = ''
            cd lib/containers
          '';
        };

        agda2hs-custom = agda2hs.lib.${system}.withPackages ([
          base-lib
          containers-lib
        ]);

      in rec {
        packages = {
          inherit agda2hs-custom;
          default = agda2hs-custom;
        };

        apps = {
          agda2hs = flake-utils.lib.mkApp {
            drv = packages.agda2hs-custom;
          };
        };

        devShells.default = pkgs.haskellPackages.shellFor {
          packages = p: with p; [];
          buildInputs = with pkgs.haskellPackages; [
            cabal-install
            cabal2nix
            haskell-language-server
            pkgs.just
            packages.agda2hs-custom
          ];
        };
      }
    );
}