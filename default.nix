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

Boogie = pkgs.buildDotnetModule rec {
  pname = "Boogie";
  version = "2.15.7";

  src = pkgs.fetchFromGitHub {
    owner = "boogie-org";
    repo = "boogie";
    rev = "v${version}";
    sha256 = "16kdvkbx2zwj7m43cra12vhczbpj23wyrdnj0ygxf7np7c2aassp";
  };

  buildInputs = [
    pkgs.dotnetPackages.NUnit
    pkgs.dotnetPackages.NUnitRunners
  ];

  projectFile = [ "Source/Boogie.sln" ];
  nugetDeps = ./nix/boogie-deps.nix;

  postInstall = ''
      mkdir -pv "$out/lib/dotnet/${pname}"
      ln -sv "${pkgs.z3}/bin/z3" "$out/lib/dotnet/${pname}/z3.exe"

      # so that this derivation can be used as a vim plugin to install syntax highlighting
      vimdir=$out/share/vim-plugins/boogie
      install -Dt $vimdir/syntax/ Util/vim/syntax/boogie.vim
      mkdir $vimdir/ftdetect
      echo 'au BufRead,BufNewFile *.bpl set filetype=boogie' > $vimdir/ftdetect/bpl.vim
  '';

  postFixup = ''
      ln -s "$out/bin/BoogieDriver" "$out/bin/boogie"
  '';

  meta = with pkgs.lib; {
    description = "An intermediate verification language";
    homepage = "https://github.com/boogie-org/boogie";
    longDescription = ''
      Boogie is an intermediate verification language (IVL), intended as a
      layer on which to build program verifiers for other languages.

      This derivation may be used as a vim plugin to provide syntax highlighting.
    '';
    license = licenses.mspl;
    maintainers = [ maintainers.taktoa ];
    platforms = with platforms; (linux ++ darwin);
  };
};

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
    Boogie
    pkgs.z3
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
  inherit pact-model Boogie;
  pact-model_8_14 = pact-model "coqPackages_8_14";
  pact-model_8_15 = pact-model "coqPackages_8_15";
}
