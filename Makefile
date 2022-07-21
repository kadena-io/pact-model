JOBS = 1

MISSING	 =									\
	find . \( \( -name foo \) -prune \)					\
	    -o \( -name '*.v'							\
		  -print \)						|	\
		xargs egrep -i -Hn '(admit|undefined|jww)'		|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

all: pact-model
	-@$(MISSING) || exit 0

#perl -i extract/fixcode.pl Internal.hs
#perl -i -pe 's/module Internal where/module Pact where/' Internal.hs
#mv Internal.hs extract/Pact/Internal.hs
pact-model: Makefile.coq $(wildcard *.v)
	rm -f PactExt.hs
	touch extract/PactExt.v
	make -f Makefile.coq JOBS=$(JOBS)
	(cd extract;									\
	 hpack &&									\
	 nix-shell --command "cabal configure --enable-tests --enable-benchmarks" &&	\
	 cabal build &&									\
	 cabal test)

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean: _CoqProject Makefile.coq
	make -f Makefile.coq clean

install: _CoqProject Makefile.coq
	make -f Makefile.coq install

fullclean: clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.d
