build: Makefile.coq
	$(MAKE) -f Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

cleanall: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall

html: Makefile.coq
	COQDOCEXTRAFLAGS="--gallina" $(MAKE) -f Makefile.coq html

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@
