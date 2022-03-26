Require Import Arith.
Require Vector.
Require Import List.
Require Import Relations.
Require Import Wellfounded.

Inductive Func: nat -> Set:=
|FZero: Func 0
|FSucc: Func 1
|FProj: forall i n, i<n -> Func n
|FComp: forall n m (f:Func m) (fl:Vector.t (Func n) m), Func n
|FRecu: forall n (f:Func n) (g:Func (S (S n))), Func (S n)
.


Fixpoint funcDepth n (f:Func n) : nat := match f with |FZero => 0 |FSucc =>0 |FProj _ _ _=>0
|FComp n m f fl=>S (max (funcDepth m f) (Vector.fold_right max (Vector.map (funcDepth n) fl) 0))
|FRecu n f g=> S (max (funcDepth n f) (funcDepth (S (S n)) g)) end.

Inductive Term : Set :=
|Var: nat -> Term
|FuncT: forall n, Func n -> Vector.t Term n -> Term
.

Definition Zero : Term := FuncT 0 FZero (Vector.nil Term).
Definition Succ (t:Term) : Term := FuncT 1 FSucc (Vector.cons Term t 0 (Vector.nil Term)).

Fixpoint termDepth (t:Term): nat := match t with |Var _=>0
|FuncT _ _ tv => S (Vector.fold_right max (Vector.map termDepth tv) 0)
end.
Inductive FuncT_arg: relation Term := FuncT_arg_intro: forall n t l f, Vector.In t l -> FuncT_arg t (FuncT n f l).

Theorem WF_FuncT_arg: well_founded FuncT_arg. Proof. apply wf_incl with (ltof Term termDepth). unfold inclusion. unfold ltof. intros. inversion H. subst x y. simpl. apply le_n_S. admit. apply well_founded_ltof. Admitted.

Inductive VarInTerm: nat -> Term -> Prop:=
|VIT_Var: forall i, VarInTerm i (Var i)
|VIT_Func: forall n f tv t i, VarInTerm i t -> Vector.In t tv -> VarInTerm i (FuncT n f tv)
.
Hint Constructors VarInTerm.

Definition varInTerm_sig: forall t, {l|forall i, VarInTerm i t <-> In i l}. apply (Fix (well_founded_ltof Term termDepth)). intros t IH. destruct t. exists (n::nil). intros; split; intros. inversion H; left; auto. inversion H. subst i; auto. destruct H0.
  revert IH. revert f. induction t; intros. admit. destruct (IH h) as [l1 H1]. unfold ltof. simpl. apply le_n_S. apply Nat.le_max_l.

  destruct n. admit. revert IH. revert f. apply Vector.rectS with (n0:=n) (v:=t); intros. destruct (IH a) as [l H]. apply FuncT_arg_intro. apply Vector.In_cons_hd. exists l. intros; split; intros. apply H. inversion H0. subst n0 i. inversion H2.


  revert IH. revert f. induction t; intros. admit.

  remember (Vector.to_list t) as tl. revert Heqtl. induction tl; intros. exists nil. intros; split; intros. inversion H.

| FuncT _ _ tv => Vector.fold_right (app (A:=nat)) (Vector.map varInTerm tv) nil end.

Fixpoint varInTerm (t:Term):list nat:= match t with Var i=>i::nil
| FuncT _ _ tv => Vector.fold_right (app (A:=nat)) (Vector.map varInTerm tv) nil end.

Theorem varTerm_spec: forall t i, VarInTerm i t <-> In i (varInTerm t). Proof. induction t; intros; split; intros; simpl. inversion H; auto. simpl in H. inversion H. subst i; auto. inversion H0. admit.
  simpl in H. admit.



 
