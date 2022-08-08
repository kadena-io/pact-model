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
      rm -f "$out/bin"/System.* "$out/bin"/Microsoft.*
      rm -f "$out/bin"/NUnit3.*
      rm -f "$out/bin"/*Tests
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

dafny = pkgs.buildDotnetModule rec {
  pname = "Dafny";
  version = "3.7.3";

  src = pkgs.fetchFromGitHub {
    owner = "Microsoft";
    repo = "dafny";
    rev = "v${version}";
    sha256 = "1knv6zvpq0bnngmlwkcqgjpdkqsgbiihs6a0cycb8ssn18s4ippr";
  };

  preBuild = ''
    ln -s ${pkgs.z3} Binaries/z3
  '';

  buildInputs = [ Boogie pkgs.jdk11 ];
  nugetDeps = ./nix/dafny-deps.nix;

  projectFile = [ "Source/Dafny.sln" ];

  # Boogie as an input is not enough. Boogie libraries need to be at the same
  # place as Dafny ones. Same for "*.dll.mdb". No idea why or how to fix.
  postFixup = ''
    for lib in ${Boogie}/lib/dotnet/${Boogie.pname}/*.dll{,.mdb}; do
      ln -s $lib $out/lib/dotnet/${pname}/
    done
    # We generate our own executable scripts
    rm -f $out/lib/dotnet/${pname}/dafny{,-server}

    mv "$out/bin/Dafny" "$out/bin/dafny"

    rm -f $out/bin/{coverlet,Microsoft,NUnit3,System}.*
    rm -f $out/bin/{ThirdPartyNotices.txt,XUnitExtensions}
  '';

  meta = with pkgs.lib; {
    description = "A programming language with built-in specification constructs";
    homepage = "https://research.microsoft.com/dafny";
    maintainers = with maintainers; [ layus ];
    license = licenses.mit;
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
    dafny
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
  inherit pact-model Boogie dafny;
  pact-model_8_14 = pact-model "coqPackages_8_14";
  pact-model_8_15 = pact-model "coqPackages_8_15";
}
