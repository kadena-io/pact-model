args@{
  rev    ? "c5d810f4c74c824ae0fb788103003c6c9d366a08"
, sha256 ? "1lmizli5hbk7hlvss0ixx4zl5g4s77z493lr2xn37csph5xcl3rb"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let pact-model = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-pact-model-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib equations # coqhammer pkgs.z3-tptp
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
