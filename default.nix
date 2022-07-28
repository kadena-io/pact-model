args@{
  rev    ? "8f73de28e63988da02426ebb17209e3ae07f103b"
, sha256 ? "1mvq8wxdns802b1gvjvalbvdsp3xjgm370bimdd93mwpspz0250p"

, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let

inherit
  (pkgs.callPackages
    (pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "coq-haskell";
      rev = "347555e0f89c5729f81b18a881399ccdc79d7cb6";
      sha256 = "15n02zhi0w6iyqsbzqayfad3vhp5pnh2ny345dyqk30zk91ggk5n";
    }) {}) coq-haskell;

inherit
  (pkgs.callPackages
    (pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "category-theory";
      rev = "33857bdea4de0c567cfb6fae9435796e9f3cb33b";
      sha256 = "13fal1rzw5jd6idl1ainzsrbjamj9rk6hn8l5lqqammrfnjx157q";
    }) {}) category-theory;

pact-model = coqPackages: with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-pact-model-${version}";
  version = "1.0";

  src = if pkgs ? coqFilterSource
        then pkgs.coqFilterSource [] ./.
        else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib
    (category-theory coqPackages)
    (coq-haskell coqPackages)
    equations
    coqhammer pkgs.z3-tptp
    dpdgraph
    QuickChick
    pkgs.perl
  ];
  enableParallelBuilding = true;

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  shellHook = ''
    export PATH=$PATH:$PWD
  '';

  env = pkgs.buildEnv { inherit name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" ];
  };
};

in {
  inherit pact-model;
  pact-model_8_14 = pact-model "coqPackages_8_14";
  pact-model_8_15 = pact-model "coqPackages_8_15";
}
