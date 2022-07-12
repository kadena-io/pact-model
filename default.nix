args@{
  rev    ? "e0a42267f73ea52adc061a64650fddc59906fc99"
, sha256 ? "0r1dsj51x2rm016xwvdnkm94v517jb1rpn4rk63k6krc4d0n3kh9"
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
      rev = "c46434df74e0de8c398b55cce30e6a764916e9e7";
      sha256 = "01rd8zlgwb24lwxlzrb85zs3qzl6hp1ig88zv5a5g4b6pch0fliy";
    }) {}) coq-haskell;

pact-model = coqPackages: with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-pact-model-${version}";
  version = "1.0";

  src = if pkgs ? coqFilterSource
        then pkgs.coqFilterSource [] ./.
        else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib
    equations category-theory (coq-haskell coqPackages)
    coqhammer pkgs.z3-tptp
  ];
  enableParallelBuilding = true;

  buildFlags = [
    "JOBS=$(NIX_BUILD_CORES)"
  ];

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { inherit name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" ];
  };
};

in {
  pact-model_8_14 = pact-model "coqPackages_8_14";
  pact-model_8_15 = pact-model "coqPackages_8_15";
}
