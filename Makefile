all:	list_util.vo nat_theory.vo polynomial.vo combi.vo ModEq.vo LP.vo RegExp.vo

list_util.vo:	list_util.v
	coqc list_util.v

polynomial.vo:	polynomial.v ModEq.vo list_util.vo
	coqc polynomial.v

combi.vo:	combi.v ModEq.vo list_util.vo
	coqc combi.v

nat_theory.vo:	nat_theory.v ModEq.vo list_util.vo
	coqc nat_theory.v

ModEq.vo:	ModEq.v list_util.vo
	coqc ModEq.v

LP.vo:	LP.v list_util.vo
	coqc LP.v

RegExp.vo:	RegExp.v list_util.vo
	coqc RegExp.v

.PHONY: clean
clean:
	rm *.vo *.glob

