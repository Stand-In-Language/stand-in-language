# Generated from telomare.cabal by `nix run .#cabal2nix`; don't edit it by
# hand. CI's cabal2nix workflow (.github/workflows/cabal2nix.yml) runs that
# on every push that can change this file and commits the result. It is
# checked in because the ekapkgs package set has no top-level cabal2nix,
# so `callCabal2nix` cannot run at evaluation time. nix/telomare.nix
# replaces `src` with the flake's source.
{ mkDerivation, aeson, base, binary, bytestring, containers
, cryptonite, data-fix, deepseq, Diff, directory, filepath, free
, genvalidity, haskeline, hspec, lens, lib, lsp, lsp-types
, megaparsec, memory, mtl, optparse-applicative, pretty-show
, process, QuickCheck, recursion-schemes, stm, strict, tasty
, tasty-hunit, tasty-quickcheck, text, time, transformers
, utf8-string, validity
}:
mkDerivation {
  pname = "telomare";
  version = "0.1.0.0";
  src = ./..;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base binary bytestring containers cryptonite data-fix deepseq
    filepath free genvalidity lens megaparsec memory mtl
    recursion-schemes transformers utf8-string validity
  ];
  executableHaskellDepends = [
    aeson base containers directory filepath free haskeline lens lsp
    lsp-types megaparsec mtl optparse-applicative process
    recursion-schemes stm strict text time
  ];
  testHaskellDepends = [
    base bytestring containers data-fix Diff free hspec megaparsec mtl
    pretty-show QuickCheck recursion-schemes strict tasty tasty-hunit
    tasty-quickcheck
  ];
  homepage = "https://github.com/Stand-In-Language/stand-in-language#readme";
  description = "A simple but robust virtual machine";
  license = lib.meta.getLicenseFromSpdxId "Apache-2.0";
}
