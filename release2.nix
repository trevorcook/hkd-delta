let
  pkgs = import <nixpkgs> { };

in
  { hkd-delta = pkgs.haskellPackages.callPackage ./hkd-delta.nix { };
  }
