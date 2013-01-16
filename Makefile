COQC="c:/home/coq/bin/coqc"
COQDEP="c:/home/coq/bin/coqdep"

SRC=$(wildcard *.v)
VOFILES=$(SRC:.v=.vo)

all : $(VOFILES)

include .depend

.depend depend:
	rm -f .depend
	$(COQDEP) -I ./ $(SRC) >>.depend



.SUFFIXES: .v .vo 

.v.vo:
	$(COQC) $*
clean :
	rm -f *.vo *.glob


allclean :
	rm -f *.vo *.glob .depend

