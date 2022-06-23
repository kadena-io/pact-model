args@{
  ghcCompiler ? "ghc923"
, rev    ? "e0a42267f73ea52adc061a64650fddc59906fc99"
, sha256 ? "0r1dsj51x2rm016xwvdnkm94v517jb1rpn4rk63k6krc4d0n3kh9"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let

haskellPackages = pkgs.haskell.packages.${ghcCompiler};

in haskellPackages.developPackage {
  root = ./.;

  overrides = with pkgs.haskell.lib; self: super: {};

  source-overrides = {};

  modifier = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
    buildTools = (attrs.buildTools or []) ++ [
      haskellPackages.cabal-install
      haskellPackages.ormolu
    ];

    enableLibraryProfiling = false;
  });
}
