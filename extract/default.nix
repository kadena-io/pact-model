args@{
  ghcCompiler ? "ghc8107"
, rev    ? "e0a42267f73ea52adc061a64650fddc59906fc99"
, sha256 ? "0r1dsj51x2rm016xwvdnkm94v517jb1rpn4rk63k6krc4d0n3kh9"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
, returnShellEnv ? pkgs.lib.inNixShell
, mkDerivation ? null
}:

let

haskellPackages = pkgs.haskell.packages.${ghcCompiler};

in haskellPackages.developPackage {
  root = ./.;

  overrides = with pkgs.haskell.lib; self: super: {
    statistics = self.callHackageDirect {
      pkg = "statistics";
      ver = "0.15.2.0";
      sha256 = "1sg1gv2sc8rdsl6qby6p80xv3iasy6w2khbkc6cx7j2iva67v33r";
    } {};
  };

  source-overrides = {
    ormolu = "0.5.0.0";
  };

  modifier = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
    buildTools = (attrs.buildTools or []) ++ [
      haskellPackages.cabal-install
      haskellPackages.ormolu
      (import ../. {}).pact-model_8_15.env
      pkgs.perl
    ];

    enableLibraryProfiling = false;
  });

  inherit returnShellEnv;
}


