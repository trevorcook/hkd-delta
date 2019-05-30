{ mkDerivation, base, stdenv }:
mkDerivation {
  pname = "hkd-delta";
  version = "0.0.0.1";
  src = ./.;
  libraryHaskellDepends = [ base ];
  homepage = "github.com/trevorcook/hkd-delta";
  description = "Definition of \"Delta structures\" for higher kinded data";
  license = stdenv.lib.licenses.bsd3;
}
