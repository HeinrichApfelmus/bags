{
  description = ''
    Development shell for the `bags` package
  '';

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    agda2hs.url = "github:agda/agda2hs?ref=aedafce25dbb0eb17c49472ef240da17ed0fd294";
  };

  outputs = {self, nixpkgs, flake-utils, agda2hs}:
    flake-utils.lib.eachDefaultSystem (system:
      let
        # ###########################################
        # Imports

        pkgs = import nixpkgs { inherit system; };

        agda2hs-custom = agda2hs.lib.${system}.withPackages ([
          agda2hs.packages.${system}.base-lib
          agda2hs.packages.${system}.containers-lib
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