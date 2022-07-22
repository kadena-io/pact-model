MISSING	 =									\
	find . \( \( -name Extract.v \) -prune \)				\
	    -o \( -name '*.v'							\
		  -print \)						|	\
		xargs egrep -i -Hn '(admit|undefined|jww)'		|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: pact-model
	-@$(MISSING) || exit 0

#perl -i -pe 's/module Internal where/module Pact where/' Internal.hs
#mv Internal.hs extract/Pact/Internal.hs
pact-model: Makefile.coq $(wildcard *.v)
	rm -f Extract.hs
	touch extract/src/Extract.v
	$(MAKE) -f Makefile.coq
	mv *.hs extract/src
	perl -i extract/fixcode.pl extract/src/*.hs

# (cd extract;							\
#  hpack &&							\
#  nix-shell --command						\
#     "cabal configure --enable-tests --enable-benchmarks" &&	\
#  nix-shell --command "cabal build" &&				\
#  nix-shell --command "cabal test")

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq clean

install: _CoqProject Makefile.coq
	$(MAKE) -f Makefile.coq install

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.d
