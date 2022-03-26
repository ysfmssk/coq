all:	list_util.vo nat_theory.vo polynomial.vo combi.vo ModEq.vo LP.vo RegExp.vo LQ.vo FSA.vo Peano_LQ.vo Peano_Func.vo Peano_rfunc.vo Peano_Godel.vo Carmichael.vo

list_util.vo:	list_util.v
	coqc list_util.v

polynomial.vo:	polynomial.v ModEq.vo list_util.vo
	coqc polynomial.v

combi.vo:	combi.v ModEq.vo list_util.vo
	coqc combi.v

nat_theory.vo:	nat_theory.v ModEq.vo list_util.vo combi.vo
	coqc nat_theory.v

Carmichael.vo:	Carmichael.v ModEq.vo list_util.vo combi.vo
	coqc Carmichael.v

ModEq.vo:	ModEq.v list_util.vo
	coqc ModEq.v

LP.vo:	LP.v list_util.vo
	coqc LP.v

LQ.vo:	LQ.v list_util.vo
	coqc LQ.v

FSA.vo:	FSA.v list_util.vo
	coqc FSA.v

RegExp.vo:	RegExp.v FSA.vo list_util.vo
	coqc RegExp.v

Peano_LQ.vo:	Peano_LQ.v list_util.vo
	coqc Peano_LQ.v

Peano_Func.vo:	Peano_Func.v list_util.vo ModEq.vo Peano_LQ.vo
	coqc Peano_Func.v

Peano_rfunc.vo:	Peano_rfunc.v list_util.vo ModEq.vo Peano_LQ.vo Peano_Func.vo
	coqc Peano_rfunc.v

Peano_Godel.vo:	Peano_Godel.v Peano_rfunc.vo list_util.vo ModEq.vo Peano_LQ.vo Peano_Func.vo
	coqc Peano_Godel.v

.PHONY: clean
clean:
	rm *.vo *.glob

