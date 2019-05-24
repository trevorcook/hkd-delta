{ mkDerivation, base, one-liner, stdenv }:
mkDerivation {
  pname = "delta-HKD";
  version = "0.0.0.1";
  src = ./.;
  libraryHaskellDepends = [ base one-liner ];
  homepage = "github.com/trevorcook/delta-HKD";
  description = "Definition of \"Delta structures\" for higher kinded data";
  license = stdenv.lib.licenses.bsd3;
}
