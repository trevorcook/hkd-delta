let
  pkgs = import <nixpkgs> { };

in
  { delta-HKD = pkgs.haskellPackages.callPackage ./delta-HKD.nix { };
  }
