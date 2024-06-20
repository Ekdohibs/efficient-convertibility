%.vo: %.v
	coqc $<

.depend: *.v
	coqdep $^ > $@

include .depend