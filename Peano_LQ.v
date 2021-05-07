Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.

Set Implicit Arguments.

Hint Resolve le_0_n lt_le_weak Nat.le_max_l Nat.le_max_r le_n_S le_not_lt lt_not_le.

Inductive Func : Set :=
|FZero : Func
|FSucc : Func
|FProj : nat -> Func
|FComp: Func -> list Func -> Func
|FRecu : Func -> Func -> Func
.
(* Well-formed funciton with arity *)
Inductive WFFunc : nat -> Func -> Prop :=
|WFF_Zero: WFFunc 0 FZero
|WFF_Succ: WFFunc 1 FSucc
|WFF_Proj: forall n i, i < n -> WFFunc n (FProj i)
|WFF_Comp: forall n f l, WFFunc (length l) f -> Forall (WFFunc n) l -> WFFunc n (FComp f l)
|WFF_Recu: forall n f g, WFFunc n f -> WFFunc (S (S n)) g -> WFFunc (S n) (FRecu f g)
.
Hint Constructors WFFunc.
Fixpoint funcDepth (f:Func) : nat := match f with |FZero => 0 |FSucc => 0 |FProj _ => 0 |FComp g l => S (maxl (map funcDepth (g::l))) |FRecu g h => S (max (funcDepth g) (funcDepth h)) end.
Definition wfFunc: forall f n, {WFFunc n f}+{~WFFunc n f}. intros f. apply (Fix (well_founded_ltof Func funcDepth)) with (P:=fun f=>forall n,{WFFunc n f}+{~WFFunc n f}). clear f. intros f IH n. destruct f. destruct (nat_eq_dec n 0); [subst n; left|right]; auto. contradict n0; inversion n0; auto. destruct (nat_eq_dec n 1); [subst n;left|right]; auto. contradict n0; inversion n0; auto. destruct (lt_dec n0 n); [left|right]; auto. contradict n1; inversion n1; auto.
  destruct (IH f) with (n:=length l);[| |right]. unfold ltof. simpl; auto. destruct Forall_dec with (P:=WFFunc n) (l:=l); auto. intros. apply IH. unfold ltof. simpl. apply le_n_S. apply le_trans with (maxl (map funcDepth l)); auto. apply maxl_le. apply in_map_iff; exists x; auto. right. destruct s as [x H]. contradict n0. inversion n0. apply Forall_forall with (x:=x) in H4; auto. contradict n0; inversion n0; auto. destruct n. right. intros C; inversion C. destruct (IH f1) with (n:=n); [| |right]. unfold ltof. simpl; auto. destruct (IH f2) with (n:=S (S n)); [|left|right]; auto. unfold ltof; simpl; auto. contradict n0; inversion n0; auto. contradict n0; inversion n0; auto. Defined.
Definition Func_eq_dec: forall f g:Func, {f=g}+{f<>g}. intros f. apply (Fix (well_founded_ltof Func funcDepth)) with (P:=fun f=>forall g,{f=g}+{f<>g}). clear f. intros f IH g. destruct f; destruct g; try (right; discriminate). left; auto. left; auto. destruct (nat_eq_dec n n0); [left|right]; auto. contradict n1; inversion n1; auto. destruct (IH f) with g; [| |right]. unfold ltof. simpl; auto. subst g. cut ({l=l0}+{l<>l0}). intros. destruct H; [subst l0;left|right]; auto. contradict n; inversion n; auto. revert l0. induction l; intros. destruct l0; [left|right]; auto; discriminate. destruct l0. right; discriminate. destruct (IH a) with f0. unfold ltof. simpl; auto. apply le_n_S. apply le_trans with (max (funcDepth a) (maxl (map funcDepth l))); auto. subst f0. destruct IHl with l0. intros. apply IH. unfold ltof. apply lt_le_trans with (funcDepth (FComp f l)); auto. simpl. apply le_n_S. apply Nat.max_le_compat_l. auto. subst l0; left; auto. right. contradict n; inversion n; auto. right. contradict n; inversion n; auto. contradict n; inversion n; auto.
  destruct (IH f1) with g1. unfold ltof. simpl; auto. subst g1. destruct (IH f2) with g2. unfold ltof. simpl; auto. subst g2; left; auto. right; contradict n; inversion n; auto. right; contradict n; inversion n; auto. Defined.

Inductive Term : Set :=
|Var: nat -> Term
|FuncT: Func -> list Term -> Term
.
(* Well-formed funciton with arity & Well-formed term *)
Inductive WFTerm : Term -> Prop :=
|WFTVar : forall i, WFTerm (Var i)
|WFTFunc: forall f l, WFFunc (length l) f -> Forall WFTerm l -> WFTerm (FuncT f l)
.
Hint Constructors WFTerm.

Definition Zero : Term := FuncT FZero nil.
Definition Succ (t:Term) : Term := FuncT FSucc (t::nil).
Hint Unfold Zero Succ.

Fixpoint termDepth (t:Term) : nat := match t with |Var _ => 0 |FuncT f l => S (maxl (map termDepth l)) end.
Definition wfTerm: forall t, {WFTerm t}+{~WFTerm t}. apply (Fix (well_founded_ltof Term termDepth)). intros t IH. destruct t. left; auto. destruct (wfFunc f (length l)); [|right]. destruct Forall_dec with (P:=WFTerm) (l:=l); [|right|left]; auto. intros. apply IH. unfold ltof. simpl. apply le_n_S. apply maxl_le. apply in_map_iff; exists x; auto. destruct s as [x H1]. contradict n. inversion n. apply Forall_forall with (x:=x) in H3; auto. contradict n; inversion n; auto. Defined.
Definition Term_eq_dec: forall t s:Term, {t=s}+{t<>s}. intros t. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun t=>forall s,{t=s}+{t<>s}). clear t. intros t IH s. destruct t; destruct s; try (right; discriminate). destruct (nat_eq_dec n n0); [subst n0; left|right]; auto. contradict n1; inversion n1; auto. destruct (Func_eq_dec f f0); [|right]. subst f0. cut ({l=l0}+{l<>l0}). intros. destruct H; [subst l0; left|right]; auto. contradict n; inversion n; auto. revert l0; induction l; intros. destruct l0; [left|right]; auto; discriminate. destruct l0. right; discriminate. destruct (IH a) with t. unfold ltof. simpl; auto. subst t. destruct IHl with l0. intros. apply IH. apply lt_le_trans with (termDepth (FuncT f l)); auto. simpl; auto. subst l0; left; auto. right; contradict n; inversion n; auto. right; contradict n; inversion n; auto. contradict n; inversion n; auto. Defined.

Inductive VarTerm: nat -> Term -> Prop :=
|VTvar: forall i, VarTerm i (Var i)
|VTarg: forall i t f l, VarTerm i t -> In t l -> VarTerm i (FuncT f l)
.
Hint Constructors VarTerm.

Definition varTerm_sig: forall t, {l|forall n, VarTerm n t<->In n l}. apply (Fix (well_founded_ltof Term termDepth)). intros t IH. destruct t. exists (n::nil). intros m; split; intros. inversion H; auto. destruct H. subst m; auto. destruct H. induction l. exists nil. intros; split; intros. inversion H. destruct H4. destruct H. destruct (IH a) as [l1 H]. unfold ltof. simpl; auto. destruct IHl as [l2 H0]. intros. apply IH. unfold ltof. apply lt_le_trans with (termDepth (FuncT f l)); auto. simpl; auto. exists (l1++l2). intros; split; intros. apply in_or_app. inversion H1. subst i f0 l0. destruct H6. subst t. left; apply H; auto. right; apply H0. apply VTarg with t; auto. apply in_app_or in H1. destruct H1. apply VTarg with a; auto. apply H; auto. apply H0 in H1. inversion H1. apply VTarg with t; auto. Defined.
Definition varTerm (t:Term) : list nat := match varTerm_sig t with |exist _ l _=> l end.
Theorem VT_var: forall i j, VarTerm i (Var j) -> i=j. Proof. intros. inversion H; auto. Qed.
Hint Resolve VT_var. 

Inductive Formula: Set :=
|Equal : Term -> Term -> Formula
|Neg   : Formula -> Formula
|Imply : Formula -> Formula -> Formula
|Any   : nat -> Formula -> Formula
.
Definition Formula_eq_dec: forall f g:Formula, {f=g}+{f<>g}. induction f; intros; destruct g; try (right; discriminate). destruct (Term_eq_dec t t1); [destruct (Term_eq_dec t0 t2); [left|right]|right]; f_equal; auto. contradict n; inversion n; auto. contradict n; inversion n; auto. destruct (IHf g); [subst g; left|right]; auto; contradict n; inversion n; auto. destruct (IHf1 g1); [subst g1; destruct (IHf2 g2); [subst g2; left|right]|right]; auto; contradict n; inversion n; auto. destruct (nat_eq_dec n n0); [subst n0|right]. destruct (IHf g); [subst g; left|right]; auto. contradict n0; inversion n0; auto. contradict n1; inversion n1; auto. Defined.
Inductive WFFormula: Formula -> Prop :=
|WFF_Eq: forall t u, WFTerm t -> WFTerm u -> WFFormula (Equal t u)
|WFF_Neg: forall f, WFFormula f-> WFFormula (Neg f)
|WFF_Imply: forall f g, WFFormula f -> WFFormula g -> WFFormula (Imply f g)
|WFF_Any: forall v f, WFFormula f -> WFFormula (Any v f)
.
Hint Constructors WFFormula.

Definition Land (f g:Formula) := Neg (Imply f (Neg g)).
Definition Lor (f g:Formula) := Imply (Neg f) g.
Definition Ex v f := Neg (Any v (Neg f)).
Fixpoint Imps (l:list Formula) (c:Formula) : Formula := match l with nil => c |p::l' => Imply p (Imps l' c) end.

(* Declare Scope LQ_scope. *)
Notation "# n" := (Var n) (at level 80, no associativity) : Peano_scope.
Notation "f == g" := (Equal f g) (at level 81, no associativity) : Peano_scope.
Notation "f != g" := (Neg (Equal f g)) (at level 81, no associativity) : Peano_scope.
Notation "! f" := (Neg f) (at level 82, no associativity) : Peano_scope.
Notation "f ==> g" := (Imply f g) (at level 85, right associativity) : Peano_scope.
Notation "f &^ g" := (Land f g) (at level 83, left associativity) : Peano_scope.
Notation "f |^ g" := (Lor f g) (at level 84, left associativity) : Peano_scope.

Open Scope Peano_scope.

Inductive VarFormula: nat -> Formula -> Prop :=
|VF_Eq1: forall i s t, VarTerm i s -> VarFormula i (s == t)
|VF_Eq2: forall i s t, VarTerm i t -> VarFormula i (s == t)
|VF_Neg: forall i f, VarFormula i f -> VarFormula i (!f)
|VF_Imp1: forall i f g, VarFormula i f -> VarFormula i (f==>g)
|VF_Imp2: forall i f g, VarFormula i g -> VarFormula i (f==>g)
|VF_Any1: forall i j f, VarFormula i f -> VarFormula i (Any j f)
|VF_Any2: forall i f, VarFormula i (Any i f)
.
Inductive FreeVar: nat -> Formula -> Prop :=
|FV_Eq1: forall i s t, VarTerm i s -> FreeVar i (s == t)
|FV_Eq2: forall i s t, VarTerm i t -> FreeVar i (s == t)
|FV_Neg: forall i f, FreeVar i f -> FreeVar i (!f)
|FV_Imp1: forall i f g, FreeVar i f -> FreeVar i (f==>g)
|FV_Imp2: forall i f g, FreeVar i g -> FreeVar i (f==>g)
|FV_Any: forall i j f, i<>j -> FreeVar i f -> FreeVar i (Any j f)
.
(* Quantified variables *)
Inductive QuVar: nat -> Formula -> Prop :=
|QV_Neg: forall i f, QuVar i f -> QuVar i (!f)
|QV_Imp1: forall i f g, QuVar i f -> QuVar i (f==>g)
|QV_Imp2: forall i f g, QuVar i g -> QuVar i (f==>g)
|QV_Any1: forall i f, QuVar i (Any i f)
|QV_Any2: forall i j f, QuVar i f -> QuVar i (Any j f)
.
Hint Constructors VarFormula FreeVar QuVar.

Theorem VF_Or1: forall i f g, VarFormula i f -> VarFormula i (f |^ g). Proof. intros. unfold Lor. auto. Qed.
Theorem VF_Or2: forall i f g, VarFormula i g -> VarFormula i (f |^ g). Proof. intros. unfold Lor. auto. Qed.
Theorem VF_And1: forall i f g, VarFormula i f -> VarFormula i (f &^ g). Proof. intros. unfold Land. auto. Qed.
Theorem VF_And2: forall i f g, VarFormula i g -> VarFormula i (f &^ g). Proof. intros. unfold Land. auto. Qed.
Theorem VF_Ex1: forall i j f, VarFormula i f -> VarFormula i (Ex j f). Proof. intros. unfold Ex. auto. Qed.
Theorem VF_Ex2: forall i f, VarFormula i (Ex i f). Proof. intros. unfold Ex. auto. Qed.

Theorem FV_Or1: forall i f g, FreeVar i f -> FreeVar i (f |^ g). Proof. intros. unfold Lor. auto. Qed.
Theorem FV_Or2: forall i f g, FreeVar i g -> FreeVar i (f |^ g). Proof. intros. unfold Lor. auto. Qed.
Theorem FV_And1: forall i f g, FreeVar i f -> FreeVar i (f &^ g). Proof. intros. unfold Land. auto. Qed.
Theorem FV_And2: forall i f g, FreeVar i g -> FreeVar i (f &^ g). Proof. intros. unfold Land. auto. Qed.
Theorem FV_Ex: forall i j f, i<>j -> FreeVar i f -> FreeVar i (Ex j f). Proof. intros. unfold Ex. auto. Qed.
Hint Resolve VF_Or1 VF_Or2 VF_And1 VF_And2 VF_Ex1 VF_Ex2 FV_Or1 FV_Or2 FV_And1 FV_And2 FV_Ex.

Theorem nFV_Eq: forall i s t, ~VarTerm i s->~VarTerm i t ->~FreeVar i (s==t). Proof. intros. intros C; inversion C; contradiction. Qed.
Theorem nFV_Neg: forall i f, ~FreeVar i f -> ~FreeVar i (!f). Proof. intros. contradict H; inversion H; auto. Qed.
Theorem nFV_Imp: forall i f g, ~FreeVar i f -> ~FreeVar i g -> ~FreeVar i (f==>g). Proof. intros. intros C; inversion C; contradiction. Qed.
Theorem nFV_Any1: forall i f, ~FreeVar i (Any i f). Proof. intros. intros C; inversion C. contradict H2; auto. Qed.
Theorem nFV_Any2: forall i j f, ~FreeVar i f -> ~FreeVar i (Any j f). Proof. intros. contradict H; inversion H; auto. Qed.
Theorem nFV_Or: forall i f g, ~FreeVar i f -> ~FreeVar i g -> ~FreeVar i (f|^g). Proof. intros. intros C; inversion C. apply H; inversion H3; auto. contradiction. Qed.
Theorem nFV_And: forall i f g, ~FreeVar i f -> ~FreeVar i g -> ~FreeVar i (f&^g). Proof. intros. intros C; inversion C. inversion H3. contradiction. apply H0; inversion H6; auto. Qed.
Theorem nFV_Ex1: forall i f, ~FreeVar i (Ex i f). Proof. intros. intros C; inversion C. contradict H1; apply nFV_Any1; auto. Qed.
Theorem nFV_Ex2: forall i j f, ~FreeVar i f -> ~FreeVar i (Ex j f). Proof. intros. contradict H; inversion H. inversion H2. inversion H7; auto. Qed.
Hint Resolve nFV_Eq nFV_Neg nFV_Imp nFV_Any1 nFV_Any2 nFV_Or nFV_And nFV_Ex1 nFV_Ex2.

Definition varFormula_sig: forall f, {l|forall n, VarFormula n f <-> In n l}. induction f. destruct (varTerm_sig t) as [l1 H1]. destruct (varTerm_sig t0) as [l2 H2]. exists (l1++l2). intros; split; intros. apply in_or_app. inversion H; [left; apply H1|right; apply H2]; auto. apply in_app_or in H. destruct H; [apply H1 in H|apply H2 in H]; auto. destruct IHf as [l H]. exists l. intros; split; intros. apply H; inversion H0; auto. apply H in H0; auto. destruct IHf1 as [l1 H1]. destruct IHf2 as [l2 H2]. exists (l1++l2). intros; split; intros. apply in_or_app. inversion H; [left; apply H1|right; apply H2]; auto. apply in_app_or in H. destruct H; [apply H1 in H|apply H2 in H]; auto. destruct IHf as [l H]. exists (n::l). intros m; split; intros. inversion H0; auto. right; apply H; auto. destruct H0. subst m; auto. apply H in H0; auto. Defined.
Definition varFormula (f:Formula): list nat := match varFormula_sig f with |exist _ l _ => l end.
Definition freeVar: forall f, {l|forall n, FreeVar n f <-> In n l}. induction f. destruct (varTerm_sig t) as [l1 H1]. destruct (varTerm_sig t0) as [l2 H2]. exists (l1++l2). intros; split; intros. apply in_or_app. inversion H; [left; apply H1|right; apply H2]; auto. apply in_app_or in H. destruct H; [apply H1 in H|apply H2 in H]; auto. destruct IHf as [l H]. exists l. intros; split; intros. apply H; inversion H0; auto. apply H in H0; auto. destruct IHf1 as [l1 H1]. destruct IHf2 as [l2 H2]. exists (l1++l2). intros; split; intros. apply in_or_app. inversion H; [left; apply H1|right; apply H2]; auto. apply in_app_or in H. destruct H; [apply H1 in H|apply H2 in H]; auto. destruct IHf as [l H]. exists (remove nat_eq_dec n l). intros m; split; intros. inversion H0. apply H in H5. apply in_in_remove; auto. apply FV_Any. contradict H0. subst m; apply remove_In. apply H. apply remove_In2 in H0; auto. Defined.
Theorem FreeVar__VarFormula: forall i f, FreeVar i f -> VarFormula i f. Proof. intros i f H. induction H; auto. Qed.
Theorem QuVar__VarFormula: forall i f, QuVar i f -> VarFormula i f. Proof. intros. induction H; auto. Qed.
Theorem notVarFormula__notFreeVar: forall i f, ~VarFormula i f -> ~FreeVar i f. Proof. intros i f H. contradict H. apply FreeVar__VarFormula; auto. Qed.
Hint Resolve FreeVar__VarFormula notVarFormula__notFreeVar QuVar__VarFormula.

(* Subsitution *)
Inductive SubTerm (v:nat) (t:Term) : relation Term :=
|ST_Var1: SubTerm v t (Var v) t
|ST_Var2: forall i, i<>v -> SubTerm v t (Var i) (Var i)
|ST_Func: forall f l m, MapR (SubTerm v t) l m -> SubTerm v t (FuncT f l) (FuncT f m)
.
Inductive Sub (v:nat) (t:Term) : relation Formula :=
|Sub_Eq: forall s1 s2 u1 u2, SubTerm v t s1 s2 -> SubTerm v t u1 u2 -> Sub v t (s1==u1) (s2==u2)
|Sub_Neg: forall f g, Sub v t f g -> Sub v t (!f) (!g)
|Sub_Imp: forall f1 f2 g1 g2, Sub v t f1 g1 -> Sub v t f2 g2 -> Sub v t (f1==>f2) (g1==>g2)
|Sub_Any1: forall f, Sub v t (Any v f) (Any v f)
|Sub_Any2: forall i f g, i<>v -> Sub v t f g -> Sub v t (Any i f) (Any i g)
.
Hint Constructors SubTerm Sub.

Theorem nVT_SubTerm: forall v t u, ~VarTerm v u -> SubTerm v t u u. Proof. intros v t u. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun u=>~VarTerm v u->SubTerm v t u u). clear u. intros u IH H. destruct u. destruct (nat_eq_dec v n); auto. subst n; auto. apply ST_Func. induction l; auto. apply MapR_cons. apply IHl. intros. apply IH; auto. unfold ltof. apply lt_le_trans with (termDepth (FuncT f l)); auto. simpl; auto. contradict H. inversion H. apply VTarg with t0; auto. apply IH. unfold ltof; simpl; auto. contradict H; apply VTarg with a; auto. Qed. 
Theorem SubTerm_refl: forall v t, SubTerm v (Var v) t t. Proof. intros. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun t=>SubTerm v (#v) t t). clear t. intros t IH. destruct t. destruct (nat_eq_dec v n). subst n; auto. auto. apply ST_Func. induction l; auto. apply MapR_cons. apply IHl. intros. apply IH. unfold ltof. apply lt_le_trans with (termDepth (FuncT f l)); auto. simpl; auto. apply IH. unfold ltof. simpl; auto. Qed.
Theorem SubTerm_swap: forall v v' t u, SubTerm v (Var v') t u -> ~VarTerm v' t -> SubTerm v' (Var v) u t. Proof. intros v v' t. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun t=>forall u, SubTerm v (Var v') t u->~VarTerm v' t->SubTerm v' (Var v) u t). clear t. intros t IH u H H0. destruct t. inversion H. subst n u; auto. subst n u; auto. destruct (nat_eq_dec v' i); auto. contradict H0; subst i; auto. inversion H. subst f0 l0 u. apply ST_Func; auto. clear -IH H4 H0. induction H4; auto. apply MapR_cons. apply IHMapR. intros. apply IH; auto. unfold ltof. apply lt_le_trans with (termDepth (FuncT f l)); simpl; auto. contradict H0. inversion H0. apply VTarg with t; auto. apply IH; auto. unfold ltof. simpl; auto. contradict H0. apply VTarg with a; auto. Qed.
Theorem SubTerm_via: forall x y t s s' u, ~VarTerm y s -> SubTerm x t s u -> SubTerm x (#y) s s' -> SubTerm y t s' u. Proof. intros x y t s. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun s=>forall s' u,~VarTerm y s->SubTerm x t s u->SubTerm x (#y) s s'->SubTerm y t s' u). clear s. intros s IH. intros. destruct s. inversion H0. subst n u. inversion H1; auto. contradict H3; auto. subst i u. inversion H1. contradict H3; auto. apply nVT_SubTerm; auto. inversion H0. subst f0 l0 u. inversion H1. subst f0 l0 s'. apply ST_Func. clear H0 H1. revert H6. revert H5. revert H. revert m m0. revert IH. induction l; intros. inversion H5; inversion H6; auto. inversion H5. subst a0 l0 m. inversion H6. subst a0 l0 m0. apply MapR_cons. apply IHl; auto. intros. apply IH with y0; auto. apply lt_le_trans with (termDepth (FuncT f l)); auto. simpl; auto. contradict H. inversion H. apply VTarg with t0; auto. apply IH with a; auto. unfold ltof; simpl; auto. contradict H. apply VTarg with a; auto. Qed.
Theorem SubTerm_nVT: forall v t s u, ~VarTerm v t -> SubTerm v t s u -> ~VarTerm v u. Proof. intros v t s u H. revert u. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun s=>forall u, SubTerm v t s u->~VarTerm v u). clear s. intros s IH u H0. destruct s. inversion H0. subst t n; auto. subst n u. contradict H2; inversion H2; auto. inversion H0. clear -H IH H4. induction H4. intros C. inversion C. destruct H4. intros C. inversion C. destruct H6. subst t0 i f0 l0. contradict H5. apply IH with a; auto. unfold ltof; simpl; auto. subst i f0 l0. contradict H5. apply in_MapR_2 with (x:=t0) in H4 as [y [H7 H8]]; auto.  apply IH with y; auto. unfold ltof. simpl; auto. apply le_n_S. apply le_trans with (maxl (map termDepth l)); auto. apply maxl_le. apply in_map_iff; exists y; auto. Qed.
Theorem SubTerm_or: forall v t s u i, SubTerm v t s u -> VarTerm i u -> VarTerm i t \/ VarTerm i s. Proof. intros t v s. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun s=>forall u i, SubTerm t v s u->VarTerm i u->VarTerm i v\/VarTerm i s). clear s. intros s IH u i. intros. destruct s. inversion H. subst n u; auto. subst i0 u. inversion H0; subst i i0; auto. inversion H. subst f0 l0 u. inversion H0. subst i0 f0 l0. apply (in_MapR_2) with (x:=t0) in H4. destruct H4 as [y [H7 H8]]. destruct (IH y) with (i:=i) (u:=t0); auto. unfold ltof. simpl. apply le_n_S; auto. apply maxl_le; auto. apply in_map_iff. exists y; auto. right. apply VTarg with y; auto. auto. Qed.
Theorem SubTerm_nVT2: forall v t s u v', SubTerm v t s u -> ~VarTerm v' t -> ~VarTerm v' s -> ~VarTerm v' u. Proof. Proof. intros. intros C. apply SubTerm_or with (v:=v) (t:=t) (s:=s)in C; auto. destruct C; contradiction. Qed.

Theorem nFV_Sub: forall v t f, ~FreeVar v f -> Sub v t f f. Proof. intros. induction f. apply Sub_Eq; auto; apply nVT_SubTerm; contradict H; auto. apply Sub_Neg. apply IHf. contradict H; auto. apply Sub_Imp; auto. destruct (nat_eq_dec n v). subst n; auto. apply Sub_Any2; auto. Qed.
Theorem Sub_nFV: forall v t f g, ~VarTerm v t -> Sub v t f g -> ~FreeVar v g. Proof. induction f; intros; auto. inversion H0. apply SubTerm_nVT in H3; auto. apply SubTerm_nVT in H5; auto. inversion H0. apply IHf in H2; auto. inversion H0. subst f0 f3 g. apply IHf1 in H3; auto. inversion H0. subst n f g. auto. subst n f g. apply IHf in H5; auto. Qed.
Theorem Sub_nFV2: forall v u t f g, ~VarTerm v t -> ~FreeVar v f -> Sub u t f g -> ~FreeVar v g. Proof. intros. destruct (nat_eq_dec v u). subst u. apply Sub_nFV with t f; auto. revert H0.  induction H1; intros. contradict H2. inversion H2. apply SubTerm_or with (i:=v) in H0; auto. destruct H0. contradiction. auto. apply SubTerm_or with (i:=v) in H1; auto. destruct H1; auto; contradiction. intros C. inversion C. contradict H4. apply IHSub. contradict H0; auto. intros C. inversion C; contradict H3. apply IHSub1. contradict H0; auto. apply IHSub2. contradict H0; auto. auto. intros C. inversion C. contradict H7. apply IHSub. contradict H2; auto. Qed.
Theorem Sub_Or: forall v t f g f' g', Sub v t f f' -> Sub v t g g' -> Sub v t (f|^g) (f'|^g'). Proof. intros. unfold Lor. auto. Qed.
Theorem Sub_And: forall v t f g f' g', Sub v t f f' -> Sub v t g g' -> Sub v t (f&^g) (f'&^g'). Proof. intros. unfold Land. auto. Qed.
Theorem Sub_Ex1: forall v t f, Sub v t (Ex v f) (Ex v f). Proof. intros. unfold Ex. auto. Qed.
Theorem Sub_Ex2: forall v t i f f', i<>v -> Sub v t f f' -> Sub v t (Ex i f) (Ex i f'). Proof. intros. unfold Ex. auto. Qed.
Theorem Sub_refl: forall v f, Sub v (Var v) f f. Proof. intros. induction f; auto. apply Sub_Eq; apply SubTerm_refl. destruct (nat_eq_dec v n). subst n; auto. apply Sub_Any2; auto. Qed.
Theorem Sub_VF_or: forall v t f g i, Sub v t f g -> VarFormula i g -> VarFormula i f \/ VarTerm i t. Proof. induction f; intros; auto. inversion H. subst g. subst t0 t1. inversion H0. apply SubTerm_or with (i:=i) in H3; auto. destruct H3; auto. apply SubTerm_or with (i:=i) in H5; auto. destruct H5; auto. inversion H. subst g f0. inversion H0. apply IHf with (i:=i) in H2; auto. destruct H2; auto. inversion H. subst f0 f3 g. inversion H0. subst i0 g1 g2. apply IHf1 with (i:=i) in H3; auto. destruct H3; auto. apply IHf2 with (i:=i) in H5; auto. destruct H5; auto. inversion H. subst n f0 g; auto. subst i0 f0 g. inversion H0. subst i0 j g0. apply IHf with (i:=i) in H5; auto. destruct H5; auto. subst i0 i g0. auto. Qed.
Hint Resolve nVT_SubTerm SubTerm_refl SubTerm_swap SubTerm_via SubTerm_nVT SubTerm_or SubTerm_nVT2 nFV_Sub Sub_nFV Sub_nFV2 Sub_Or Sub_And Sub_Ex1 Sub_Ex2 Sub_refl Sub_VF_or.

Definition subTerm_sig: forall v t s, {u|SubTerm v t s u & forall u', SubTerm v t s u' -> u'=u}. intros v t. apply (Fix (well_founded_ltof Term termDepth)). intros s IH. destruct s. destruct (nat_eq_dec v n). subst n. exists t; auto. intros. inversion H; auto. contradict H1; auto. exists (# n); auto. intros. inversion H; auto; contradiction. cut ({m|MapR (SubTerm v t) l m & forall m',MapR (SubTerm v t) l m' -> m'=m}). intros. destruct H as [m H0 H1]. exists (FuncT f m); auto. intros. inversion H. f_equal; auto. induction l. exists nil; auto. intros. inversion H; auto.
  destruct (IH a) as [u H0 H1]. unfold ltof. simpl; auto. destruct IHl as [m H2 H3]. intros. apply IH. unfold ltof. apply lt_le_trans with (termDepth (FuncT f l)); auto. simpl; auto. exists (u::m); auto. intros. inversion H. subst a0 l0 m'. apply H1 in H8. subst u. apply H3 in H6. subst m0; auto. Defined.
Definition subTerm v t s := match subTerm_sig v t s with |exist2 _ _ u _ _ => u end.
Definition sub_sig: forall v t f, {g|Sub v t f g & forall g', Sub v t f g' -> g' = g}. induction f. destruct (subTerm_sig v t t0) as [s0 H H0]. destruct (subTerm_sig v t t1) as [s1 H1 H2]. exists (s0==s1); auto. intros. inversion H3. f_equal; auto. destruct IHf as [g H]. exists (!g); auto. intros. inversion H0. f_equal; auto. destruct IHf1 as [g1 H1 H2]. destruct IHf2 as [g2 H3 H4]. exists (g1==>g2); auto. intros. inversion H. f_equal; auto. destruct IHf as [g H H0]. destruct (nat_eq_dec v n). subst n. exists (Any v f); auto. intros. inversion H1; auto. contradict H4; auto. exists (Any n g); auto. intros. inversion H1. contradiction. f_equal. apply H0; auto. Defined.
Definition sub v t f := match sub_sig v t f with |exist2 _ _ g _ _ => g end.

Theorem SubTerm_unique: forall v t s u1 u2, SubTerm v t s u1 -> SubTerm v t s u2 -> u1=u2. Proof. intros. destruct (subTerm_sig v t s) as [u H1 H2]. rewrite H2; auto. Qed.
Theorem subTerm_SubTerm: forall v t s, SubTerm v t s (subTerm v t s). Proof. intros. unfold subTerm. destruct (subTerm_sig v t s); auto. Qed.
Theorem sub_Sub: forall v t f, Sub v t f (sub v t f). Proof. intros. unfold sub. destruct (sub_sig v t f); auto. Qed.
Theorem Sub_unique: forall v t f g1 g2, Sub v t f g1 -> Sub v t f g2 -> g1=g2. Proof. intros. destruct (sub_sig v t f) as [g H1 H2]. rewrite H2; auto. Qed.
Theorem SubTerm_step: forall v u t1 t2, v<>u -> ~VarTerm u t1->~VarTerm v t2-> forall s0 s1 s2 s3, SubTerm v t1 s0 s1 ->SubTerm u t2 s1 s3->SubTerm u t2 s0 s2->SubTerm v t1 s2 s3. Proof. intros v u t1 t2 H H0 H1 s0. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun s0=>forall s1 s2 s3, SubTerm v t1 s0 s1->SubTerm u t2 s1 s3->SubTerm u t2 s0 s2->SubTerm v t1 s2 s3). clear s0. intros s0 IH. intros. destruct s0 as [v'|f l]. inversion H2. subst v' s1. assert (s3=t1). eapply SubTerm_unique; eauto. subst s3. inversion H4. contradict H; auto. subst i s2. auto. subst i s1. inversion H3. subst v' s3. inversion H4. subst s2. auto. contradict H7; auto. subst i s3. inversion H4. contradict H7; auto. subst i s2. auto.
  inversion H2. subst f0 l0 s1. inversion H3. subst f0 l0 s3. inversion H4. subst f0 l0 s2. apply ST_Func. revert H8 H9 H10. clear H3 H2 H4 H H0 H1. revert m m0 m1. induction l; intros. inversion H8. subst m. inversion H9. inversion H10; auto. inversion H8. subst a0 l0 m. inversion H9. subst a0 l0 m0. inversion H10. subst a0 l0 m1. clear H8 H9 H10. apply MapR_cons. apply IHl with m2; auto. intros. apply IH with y s1; auto. apply lt_le_trans with (termDepth (FuncT f l)); simpl; auto. apply IH with a b; auto. unfold ltof; simpl; auto. Qed. 
Hint Resolve SubTerm_unique subTerm_SubTerm sub_Sub SubTerm_step.

(* Bound by Replacement *)
Inductive BBR (n m:nat) : Formula -> Prop :=
|BBR_Neg: forall f, BBR n m f -> BBR n m (!f)
|BBR_Imp1: forall f g, BBR n m f -> BBR n m (f==>g)
|BBR_Imp2: forall f g, BBR n m g -> BBR n m (f==>g)
|BBR_Any1: forall f, n<>m -> FreeVar n f -> BBR n m (Any m f)
|BBR_Any2: forall i f, n<>i -> BBR n m f -> BBR n m (Any i f)
.
Hint Constructors BBR.
Theorem BBR__FreeVar: forall n m f, BBR n m f -> FreeVar n f. Proof. intros. induction H; auto. Qed.
Theorem BBR__QuVar: forall n m f, BBR n m f -> QuVar m f. Proof. intros. induction H; auto. Qed.
Theorem BBR__VarFormula: forall n m f, BBR n m f -> VarFormula m f. Proof. intros. apply QuVar__VarFormula. apply BBR__QuVar with n; auto. Qed.
Theorem BBR_Or1: forall n m f g, BBR n m f -> BBR n m (f |^ g). Proof. intros. unfold Lor. auto. Qed.
Theorem BBR_Or2: forall n m f g, BBR n m g -> BBR n m (f |^ g). Proof. intros. unfold Lor. auto. Qed.
Theorem BBR_And1: forall n m f g, BBR n m f -> BBR n m (f &^ g). Proof. intros. unfold Land. auto. Qed.
Theorem BBR_And2: forall n m f g, BBR n m g -> BBR n m (f &^ g). Proof. intros. unfold Land. auto. Qed.
Theorem BBR_Ex1: forall n m f, n<>m -> FreeVar n f -> BBR n m (Ex m f). Proof. intros. unfold Ex. auto. Qed.
Theorem BBR_Ex2: forall n m f, n<>m -> BBR n m f -> BBR n m (Ex m f). Proof. intros. unfold Ex. auto. Qed.
Theorem nBBR_Eq: forall n m s t, ~BBR n m (s == t). Proof. intros. intros C. inversion C. Qed.
Theorem nBBR_Neg: forall n m f, ~BBR n m f -> ~BBR n m (!f). Proof. intros. contradict H; inversion H; auto. Qed.
Theorem nBBR_Imp: forall n m f g, ~BBR n m f -> ~BBR n m g -> ~BBR n m (f==>g). Proof. intros. intros C; inversion C; contradiction. Qed.
Theorem nBBR_Any1: forall n m f, ~BBR n m (Any n f). Proof. intros. intros C; inversion C; contradict H1; auto. Qed.
Theorem nBBR_Any2: forall n m i f, m<>i -> ~BBR n m f -> ~BBR n m (Any i f). Proof. intros. contradict H. inversion H. auto. contradiction. Qed.
Theorem nBBR_Or: forall n m f g, ~BBR n m f -> ~BBR n m g -> ~BBR n m (f|^g). Proof. intros. intros C; inversion C. inversion H2; contradiction. contradiction. Qed.
Theorem nBBR_And: forall n m f g, ~BBR n m f -> ~BBR n m g -> ~BBR n m (f&^g). Proof. intros. intros C; inversion C. inversion H2. contradiction. inversion H4; contradiction. Qed.
Theorem nBBR_Ex1: forall n m f, ~BBR n m (Ex n f). Proof. intros. unfold Ex. intros C; inversion C. inversion H0; contradict H3; auto. Qed.
Theorem nBBR_Ex2: forall n m i f, m<>i -> ~BBR n m f -> ~BBR n m (Ex i f). Proof. intros. unfold Ex. intros C; inversion C. inversion H2. contradiction. inversion H6; contradiction. Qed.
Theorem nBBR_refl: forall n f, ~BBR n n f. Proof. induction f. apply nBBR_Eq. apply nBBR_Neg; auto. apply nBBR_Imp; auto. destruct (nat_eq_dec n0 n). subst n0; apply nBBR_Any1. apply nBBR_Any2; auto. Qed.
Theorem nVF_nBBR: forall n m f, ~VarFormula m f -> ~BBR n m f. Proof. induction f; intros; auto. apply nBBR_Eq. apply nBBR_Neg. apply IHf. auto. apply nBBR_Imp; auto. destruct (nat_eq_dec n n0). subst n0; apply nBBR_Any1. apply nBBR_Any2; auto. contradict H. subst n0; auto. Qed.
Hint Resolve BBR__FreeVar BBR__QuVar BBR__VarFormula BBR_Or1 BBR_Or2 BBR_And1 BBR_And2 BBR_Ex1 BBR_Ex2 nBBR_refl nBBR_Eq nBBR_Neg nBBR_Imp nBBR_Any1 nBBR_Any2 nBBR_Or nBBR_And nBBR_Ex1 nBBR_Ex2.

Definition BBR_dec: forall n m f,{BBR n m f}+{~BBR n m f}. induction f. right. intros C; inversion C. destruct IHf; [left|right]; auto. destruct IHf1; [left |destruct IHf2; [left|right]]; auto. destruct (nat_eq_dec n n0). subst n0; right; auto. destruct (nat_eq_dec m n0). subst n0. destruct (freeVar f) as [l H]. destruct (in_dec nat_eq_dec n l). left. apply H in i; auto. right. contradict n0. apply H. inversion n0; auto. apply BBR__FreeVar with m; auto. destruct IHf; [left|right]; auto. Defined.

(* Term free from subsitution *)
Inductive TFFSub v t f g := TFFSub_intro : Sub v t f g -> (forall i, VarTerm i t -> ~BBR v i f) -> TFFSub v t f g.
Hint Constructors TFFSub.
Definition tffSub_sig: forall v t f, {g|TFFSub v t f g & forall g', TFFSub v t f g' -> g'=g}+{forall g, ~TFFSub v t f g}. intros. destruct (sub_sig v t f) as [g H H0]. destruct (varTerm_sig t) as [l H1]. cut ({y|In y l & BBR v y f}+{forall n, In n l->~BBR v n f}). intros. destruct H2 as [[y H3 H4]|H3]; [right|left]; auto. intros g' C. inversion C. contradict H4. apply H5. apply H1; auto. exists g; auto. apply TFFSub_intro; auto. intros. apply H3. apply H1; auto. intros. apply H0. inversion H2; auto. clear -l. induction l. right. intros. destruct H. destruct (BBR_dec v a f) as [H|H]. left. exists a; auto. destruct IHl as [[y H0 H1]|H0]; [left|right]. exists y; auto. intros. destruct H1. subst a; auto. auto. Defined.

Theorem TFFSub_unique: forall v t f g1 g2, TFFSub v t f g1 -> TFFSub v t f g2 -> g1=g2. Proof. intros. destruct (tffSub_sig v t f) as [[g H1 H2]|H1]. rewrite H2; auto. contradict H; auto. Qed.
Theorem TFFSub_Sub: forall v t f g, TFFSub v t f g->Sub v t f g. Proof. intros. inversion H; auto. Qed.
Theorem TFFSub_Eq: forall v t s1 s2 u1 u2, SubTerm v t s1 s2 -> SubTerm v t u1 u2 -> TFFSub v t (s1==u1) (s2==u2). Proof. intros. auto. Qed.
Theorem TFFSub_Neg: forall v t f g, TFFSub v t f g -> TFFSub v t (!f) (!g). Proof. intros. inversion H. auto. Qed.
Theorem TFFSub_Imp: forall v t f g f' g', TFFSub v t f f' -> TFFSub v t g g' -> TFFSub v t (f==>g) (f'==>g'). Proof. intros. inversion H. inversion H0. auto. Qed.
Theorem TFFSub_Any1: forall v t f, TFFSub v t (Any v f) (Any v f). Proof. intros; auto. Qed.
Theorem TFFSub_Any2: forall v t i f f', i<>v -> TFFSub v t f f' -> ~VarTerm i t -> TFFSub v t (Any i f) (Any i f'). Proof. intros. inversion H0. apply TFFSub_intro; auto. intros. destruct (nat_eq_dec i0 i); auto. subst i0; contradiction. Qed.
Theorem TFFSub_Or: forall v t f g f' g', TFFSub v t f f' -> TFFSub v t g g' -> TFFSub v t (f|^g) (f'|^g'). Proof. intros. unfold Lor. inversion H. inversion H0. auto. Qed.
Theorem TFFSub_And: forall v t f g f' g', TFFSub v t f f' -> TFFSub v t g g' -> TFFSub v t (f&^g) (f'&^g'). Proof. intros. unfold Lor. inversion H. inversion H0. auto. Qed.
Theorem TFFSub_Ex1: forall v t f, TFFSub v t (Ex v f) (Ex v f). Proof. intros; auto. Qed.
Theorem TFFSub_Ex2: forall v t i f f', i<>v -> TFFSub v t f f' -> ~VarTerm i t -> TFFSub v t (Ex i f) (Ex i f'). Proof. intros. inversion H0. apply TFFSub_intro; auto. intros. destruct (nat_eq_dec i0 i); auto. subst i0; contradiction. Qed.
Hint Resolve TFFSub_Sub TFFSub_Eq TFFSub_Neg TFFSub_Imp TFFSub_Any1 TFFSub_Any2 TFFSub_Or TFFSub_And TFFSub_Ex1 TFFSub_Ex2.

Theorem TFFSub_Eq_inv: forall v t s1 u1 f, TFFSub v t (s1==u1) f -> f=(subTerm v t s1 == subTerm v t u1). Proof. intros. inversion H. inversion H0. unfold subTerm. f_equal. destruct (subTerm_sig v t s1); auto. destruct (subTerm_sig v t u1); auto. Qed.
Theorem TFFSub_Neg_inv: forall v t f g, TFFSub v t (!f) g -> g=(!sub v t f) /\ TFFSub v t f (sub v t f). Proof. intros. inversion H. inversion H0. unfold sub. destruct (sub_sig v t f). split. f_equal; auto. apply TFFSub_intro; auto. intros. apply H1 in H5; auto. Qed.
Theorem TFFSub_Imp_inv: forall v t f1 f2 g, TFFSub v t (f1==>f2) g -> g=(sub v t f1==>sub v t f2)/\TFFSub v t f1 (sub v t f1)/\TFFSub v t f2 (sub v t f2). Proof. intros. inversion H. inversion H0. subst f0 f3 g. unfold sub. destruct (sub_sig v t f1). destruct (sub_sig v t f2). split. f_equal; auto. split; apply TFFSub_intro; auto; intros; apply H1 in H2; auto. Qed.
Theorem TFFSub_Any_inv1: forall v t f g, TFFSub v t (Any v f) g -> g=Any v f. Proof. intros. inversion H. inversion H0; auto. contradict H4; auto. Qed.
Theorem TFFSub_Any_inv2: forall v t u f g, v<>u -> TFFSub v t (Any u f) g -> g=Any u (sub v t f) /\TFFSub v t f (sub v t f) /\ (~FreeVar v f \/ ~VarTerm u t). Proof. intros. inversion H0. inversion H1. contradiction. unfold sub. destruct (sub_sig v t f). split. f_equal; auto. split. apply TFFSub_intro; auto. intros. apply H2 in H8; auto. destruct (varTerm_sig t) as [vt Ht]. destruct (in_dec nat_eq_dec u vt). apply Ht in i0. left. apply H2 in i0. contradict i0; auto. right. contradict n; apply Ht; auto. Qed.
Hint Resolve TFFSub_Eq_inv TFFSub_Neg_inv TFFSub_Imp_inv TFFSub_Any_inv1 TFFSub_Any_inv2.

Theorem nFV_TFFSub: forall v t f, ~FreeVar v f -> TFFSub v t f f. Proof. intros. apply TFFSub_intro; auto. intros. contradict H. apply BBR__FreeVar with i; auto. Qed.
Theorem TFFSub_swap: forall v v' f g, TFFSub v (Var v') f g -> ~FreeVar v' f -> TFFSub v' (Var v) g f. Proof. induction f; intros. inversion H. inversion H1. subst t t0 g. apply TFFSub_intro. apply Sub_Eq; apply SubTerm_swap; auto. intros; auto. inversion H. inversion H1. subst f0 g. apply TFFSub_Neg. apply IHf; auto. apply TFFSub_intro; auto. intros. apply H2 in H3. contradict H3; auto. inversion H. inversion H1. subst f0 f3 g. apply TFFSub_Imp. apply IHf1; auto. apply TFFSub_intro; auto. intros. apply H2 in H3; auto. apply IHf2; auto. apply TFFSub_intro; auto. intros. apply H2 in H3; auto. inversion H. inversion H1. subst n f0 g. apply TFFSub_intro; auto. intros. contradict H0. apply BBR__FreeVar with i; auto.
  subst n f0 g. destruct (nat_eq_dec i v'). subst i. replace g0 with f; auto. destruct (sub_sig v (Var v') f) as [g H3 H4]. rewrite H4; auto. apply H4. apply nFV_Sub. assert (~BBR v v' (Any v' f)); auto. apply TFFSub_Any2; auto. apply IHf. inversion H. apply TFFSub_intro; auto. intros. apply H4 in H6; auto. contradict H0; auto. Qed. 
Theorem TFFSub_refl: forall v f, TFFSub v (Var v) f f. Proof. intros. apply TFFSub_intro; auto. intros. inversion H. auto. Qed.
Theorem TFFSub_Imps: forall v t l1 c1 l2 c2, MapR (TFFSub v t) l1 l2 -> TFFSub v t c1 c2 -> TFFSub v t (Imps l1 c1) (Imps l2 c2). Proof. induction l1; intros. inversion H. simpl; auto. inversion H. subst a0 l1 l2. simpl. apply TFFSub_Imp; auto. Qed.
Theorem TFFSub_step: forall v u t1 t2, v<>u -> ~VarTerm u t1 -> ~VarTerm v t2 -> forall f f1 f2 g, TFFSub v t1 f f1 -> TFFSub u t2 f1 g -> TFFSub u t2 f f2 -> TFFSub v t1 f2 g. Proof. intros v u t1 t2 Hv Ht1 Ht2. induction f; intros. inversion H. inversion H2. subst t t0 f1. clear H H2. inversion H0. inversion H. subst s2 u2 g. clear H0 H. inversion H1. inversion H. subst s1 u1 f2. clear H H1. apply TFFSub_intro; auto. apply Sub_Eq. apply SubTerm_step with u t2 s2 s0; auto. apply SubTerm_step with u t2 u2 u0; auto.
  apply TFFSub_Neg_inv in H. destruct H; subst f1. apply TFFSub_Neg_inv in H0. destruct H0; subst g. apply TFFSub_Neg_inv in H1. destruct H1; subst f2. apply TFFSub_Neg. apply IHf with (f2:=sub u t2 f) (g:=sub u t2(sub v t1 f)) in H2; auto. apply TFFSub_Imp_inv in H. destruct H; subst f0. destruct H2. apply TFFSub_Imp_inv in H0. destruct H0; subst g. destruct H3. apply TFFSub_Imp_inv in H1. destruct H1; subst f3. destruct H4. apply TFFSub_Imp. eapply IHf1; eauto. eapply IHf2; eauto. destruct (nat_eq_dec v n). subst n. apply TFFSub_Any_inv1 in H. subst f1. apply TFFSub_Any_inv2 in H0; auto. destruct H0; subst g. apply TFFSub_Any_inv2 in H1; auto. destruct H1; subst f2. apply TFFSub_Any1.
  apply TFFSub_Any_inv2 in H; auto. destruct H; subst f1. destruct H2. destruct (nat_eq_dec u n). subst n. apply TFFSub_Any_inv1 in H1. subst f2. apply TFFSub_Any_inv1 in H0; auto. subst g. apply TFFSub_Any2; auto. destruct H2. assert (f=sub v t1 f). unfold sub. destruct (sub_sig v t1 f); auto. rewrite <- H3 in H0. assert (g=f2). eapply TFFSub_unique; eauto. subst f2. apply nFV_TFFSub. apply TFFSub_Any_inv2 in H0; auto. destruct H0; subst g. destruct H4. apply nFV_Any2. apply Sub_nFV2 with u t2 f; auto. apply TFFSub_Any_inv2 in H0; auto. destruct H0; subst g. destruct H3. apply TFFSub_Any_inv2 in H1; auto. destruct H1; subst f2. destruct H4. apply TFFSub_Any2; auto. eapply IHf; eauto. Qed. 
Hint Resolve nFV_TFFSub TFFSub_swap TFFSub_Imps TFFSub_refl TFFSub_step.

Definition newVar (vs:list nat) (ts:list Term) (fs:list Formula) := Smaxl (vs++flat_map varTerm ts++flat_map varFormula fs).
Theorem newVar_nVT: forall i t vs ts fs, newVar vs ts fs <= i -> In t ts -> ~VarTerm i t. Proof. intros. contradict H. apply lt_not_le. apply Smaxl_lt. apply in_or_app. right. apply in_or_app. left. apply in_flat_map. exists t; split; auto. unfold varTerm. destruct (varTerm_sig t). apply i0; auto. Qed.
Theorem newVar_nVF: forall i f vs ts fs, newVar vs ts fs <= i -> In f fs -> ~VarFormula i f. Proof. intros. contradict H. apply lt_not_le. apply Smaxl_lt. apply in_or_app. right. apply in_or_app. right. apply in_flat_map. exists f; split; auto. unfold varFormula. destruct (varFormula_sig f). apply i0; auto. Qed.
Theorem newVar_nVar: forall i vs ts fs, newVar vs ts fs <= i -> ~In i vs. Proof. intros. contradict H. apply lt_not_le. apply Smaxl_lt. apply in_or_app; auto. Qed.
Hint Resolve newVar_nVT newVar_nVF newVar_nVar.

Fixpoint with_idx' {T:Type} (l:list T) (s:nat) : list (T*nat) := match l with nil => nil |a::l' => (a,s)::with_idx' l' (S s) end.
Definition with_idx {T:Type} (l:list T) : list (T*nat) := with_idx' l 0.

Inductive PAxiom: Formula -> Prop :=
|PAL1 : forall f g, PAxiom (f==>g==>f)
|PAL2 : forall f g h, PAxiom ((f==>g==>h)==>(f==>g)==>f==>h)
|PAL3 : forall f g, PAxiom ((!f==>!g)==>g==>f)
|PAL4 : forall f v t g, TFFSub v t f g -> PAxiom (Any v f ==> g)
|PAL5 : forall v f g, ~FreeVar v f -> PAxiom (Any v (f==>g) ==> f ==> Any v g)
|PAE1 : forall v, PAxiom (#v==#v)
|PAE2 : forall v x y t tx ty u ux uy, SubTerm v (#x) t tx -> SubTerm v (#x) u ux -> SubTerm v (#y) t ty -> SubTerm v (#y) u uy -> PAxiom (#x==#y ==> tx==ux ==> ty==uy) 
|PAP1 : forall x, PAxiom (Succ (#x) != Zero)
|PAP2 : forall x y, PAxiom (Succ (#x) == Succ (#y) ==> #x == #y)
|PAP3 : forall x f f0 fs, TFFSub x Zero f f0 -> TFFSub x (Succ (#x)) f fs -> PAxiom (f0 ==> Any x (f==>fs) ==> Any x f)
|PAF1 : forall i n j, i<n -> PAxiom (FuncT (FProj i) (map Var (seq j n)) == #i+j)
|PAF2 : forall f fs n j, WFFunc n (FComp f fs) -> PAxiom (Imps (map (fun p=> #((snd p)+n+j) == FuncT (fst p) (map Var (seq j n))) (with_idx fs)) (FuncT (FComp f fs) (map Var (seq j n)) == FuncT f (map Var (seq (n+j) (length fs)))))
|PAF3 : forall n f g j, WFFunc (S n) (FRecu f g) -> PAxiom (FuncT (FRecu f g) (Zero::map Var (seq j n)) == FuncT f (map Var (seq j n)))
|PAF4 : forall n f g j, WFFunc (S n) (FRecu f g) -> PAxiom (FuncT (FRecu f g) ((#n+j)::map Var (seq j n)) == (#S(n+j)) ==> FuncT (FRecu f g) (Succ (#n+j)::map Var (seq j n)) == FuncT g ((#S(n+j))::(#n+j)::map Var (seq j n)))
.
Inductive PTheorem: Formula -> Prop :=
|PTAx : forall f, PAxiom f -> PTheorem f
|PTMp : forall f g, PTheorem (f==>g) -> PTheorem f -> PTheorem g
|PTUg : forall f v, PTheorem f -> PTheorem (Any v f)
.
(* Inference *)
Inductive Inf (l:list Formula) : Formula -> Prop :=
|IAx: forall f, PAxiom f -> Inf l f
|IPre: forall f, In f l -> Inf l f
|IMP: forall f g m n, incl m l -> incl n l -> Inf m (f==>g) -> Inf n f -> Inf l g
|IUg: forall f v, (forall p, In p l-> ~FreeVar v p) -> Inf l f -> Inf l (Any v f)
.
Hint Constructors PAxiom PTheorem Inf.
Theorem IMp: forall l f g, Inf l (f==>g) -> Inf l f -> Inf l g. Proof. intros. apply IMP with f l l; auto. Qed.
Hint Resolve IMp.

Theorem Inf__PTheorem: forall f, Inf nil f -> PTheorem f. Proof. remember nil as l. intros. revert Heql. induction H; intros; auto. subst l; destruct H. subst l. apply PTMp with f; auto. Qed.
Theorem Imp_refl: forall l f, Inf l (f==>f). Proof. intros. apply IMp with (f==>f==>f); auto. apply IMp with (f==>(f==>f)==>f); auto. Qed.
Theorem Imp_intro: forall l f g, Inf l f -> Inf l (g==>f). Proof. intros. apply IMp with f; auto. Qed.
Theorem Inf_incl: forall f l m, incl l m -> Inf l f -> Inf m f. Proof. intros. induction H0; auto. apply IMp with f; auto. apply IHInf1. apply incl_trans with l; auto. apply IHInf2. apply incl_trans with l; auto. apply IMP with (Any v f) l l; auto. apply Imp_refl. Qed.
Theorem Inf_incl': forall f p l, Inf l f -> Inf (p::l) f. Proof. intros. apply Inf_incl with l; auto. Qed.
Theorem Inf_close: forall f l p, Inf l f -> (forall v, ~FreeVar v p) -> Inf (p::l) f. Proof. intros. induction H; auto. apply IMP with f (p::m) (p::n); auto. intros x Hx. destruct Hx; [subst x|]; auto. intros x Hx. destruct Hx; [subst x|]; auto. apply IUg; auto. intros. destruct H2; [subst p0|]; auto. Qed.
Theorem PTheorem__Inf: forall f l, PTheorem f -> Inf l f. Proof. intros. apply Inf_incl with nil; auto. induction H; auto. apply IMp with f; auto. Qed.
Hint Resolve Inf__PTheorem PTheorem__Inf Inf_close Imp_refl Imp_intro Inf_incl Inf_incl'.

Theorem Deduction': forall p l f, Inf l f -> Inf (remove Formula_eq_dec p l) (p==>f). Proof. intros. induction H; auto. apply remove_In3 with (T_eq_dec:=Formula_eq_dec) (a:=p) in H. destruct H. subst f; auto. auto. apply IMP with (p==>f) (remove Formula_eq_dec p l) (remove Formula_eq_dec p n); auto. apply IMP with (p==>f==>g) nil (remove Formula_eq_dec p m); auto. destruct (in_dec Formula_eq_dec p l) as [Hp|Hp]. apply IMp with (Any v (p==>f)); auto. apply IUg; auto. intros. apply H. apply remove_In2 in H1; auto. rewrite notin_remove; auto. Qed.
Theorem Deduction: forall p l m f, Add p l m -> Inf m f -> Inf l (p==>f). Proof. intros. apply Inf_incl with (remove Formula_eq_dec p m). intros x Hx. apply Add_in with (x:=x) in H. assert (In x m). apply remove_In2 in Hx; auto. apply H in H1. destruct H1; auto. subst x. contradict Hx. apply remove_In. apply Deduction'; auto. Qed.
Theorem Ded: forall p l f, Inf (p::l) f -> Inf l (p==>f). Proof. intros. apply Deduction with (m:=p::l); auto. Qed.
Hint Resolve Deduction Ded.

Theorem Imp_trans: forall l f g h, Inf l (f==>g) -> Inf l (g==>h) -> Inf l (f==>h). Proof. intros. apply Ded. apply IMp with g; auto. apply IMp with f; auto. Qed.
Theorem Imp_swap: forall l f g h, Inf l (f==>g==>h) -> Inf l (g==>f==>h). Proof. intros. apply Ded. apply Ded. apply IMp with g; auto. apply IMp with f; auto. Qed.
Theorem Absurd: forall l f g, Inf l f -> Inf l (!f) -> Inf l g. Proof. intros. apply IMp with f; auto. apply IMp with (!g==>!f); auto. Qed.
Theorem Contra: forall l f g, Inf ((!f)::l) g -> Inf ((!f)::l) (!g) -> Inf l f. Proof. intros. apply IMp with (f==>f); auto. apply IMp with (!f==>!(f==>f)); auto. apply Ded. apply Absurd with g; auto. Qed.
Theorem Neg_elim: forall l f, Inf l (!(!f)) -> Inf l f. Proof. intros. apply IMp with (f==>f); auto. apply IMp with (!f==>!(f==>f)); auto. apply IMp with (!(!(f==>f))==>!(!f)); auto. Qed.
Theorem Neg_intro: forall l f, Inf l f -> Inf l (!(!f)). Proof. intros. apply Contra with f; auto. apply Neg_elim. auto. Qed.
Hint Resolve Imp_trans Imp_swap Absurd Contra Neg_elim Neg_intro.

Theorem Imps_imply: forall p l c, Inf p (Imps l c) -> (forall f, In f l->Inf p f) -> Inf p c. Proof. induction l; intros. auto. simpl in H. apply IHl. apply IMp with a; auto. intros. apply H0. right; auto. Qed.
Theorem Imps_Ded: forall l p f, Inf (l++p) f <-> Inf p (Imps l f). Proof. induction l; intros. simpl. split; intros; auto. split; intros. simpl. apply Ded. apply IHl. apply Inf_incl with ((a::l)++p); auto. intros x Hx. apply in_or_app. destruct Hx. subst x. auto. apply in_app_or in H0. destruct H0; auto. simpl. apply IMp with a; auto. apply Inf_incl with (l++p); auto. apply IHl. simpl in H. clear -H. revert H. revert p. induction l; intros; auto. simpl in H. simpl. apply Ded. apply IHl. apply IMp with a0; auto. Qed.
Theorem Bi_imp: forall l f g, Inf l (f==>g) -> Inf l (!f==>g) -> Inf l g. Proof. intros. apply Contra with f; auto. apply IMp with (!g); auto. apply IMp with (!f==>(!(!g))); auto. apply Imp_trans with g; auto. apply IMp with (!g); auto. apply IMp with (!(!f)==>!(!g)); auto. apply Imp_trans with f; auto. apply Imp_trans with g; auto. Qed.
Theorem Or_intro1: forall l f g, Inf l f -> Inf l (f|^g). Proof. intros. apply Ded. apply Absurd with f; auto. Qed.
Theorem Or_intro2: forall l f g, Inf l g -> Inf l (f|^g). Proof. intros. unfold Lor. auto. Qed.
Theorem Or_elim: forall l f g h, Inf l (f==>h) -> Inf l (g==>h) -> Inf l (f|^g) -> Inf l h. Proof. intros. apply Bi_imp with f; auto. apply Imp_trans with g; auto. Qed.
Theorem And_intro: forall l f g, Inf l f -> Inf l g -> Inf l (f&^g). Proof. intros. apply Contra with g; auto. apply IMp with f; auto. Qed.
Theorem And_elim1: forall l f g, Inf l (f&^g) -> Inf l f. Proof. intros. apply Contra with (f==>!g); auto. apply Ded. apply Absurd with f; auto. Qed.
Theorem And_elim2: forall l f g, Inf l (f&^g) -> Inf l g. Proof. intros. apply Contra with (f==>!g); auto. Qed.
Hint Resolve Imps_imply Bi_imp Or_intro1 Or_intro2 Or_elim And_intro And_elim1 And_elim2.

Theorem Ui: forall l f v, Inf l (Any v f) -> forall t g, TFFSub v t f g -> Inf l g. Proof. intros. apply IMp with (Any v f); auto. apply IAx. apply PAL4 with t; auto. Qed.
Theorem Eg: forall l g, Inf l g -> forall v t f, TFFSub v t f g -> Inf l (Ex v f). Proof. intros. unfold Ex. apply Contra with g; auto. apply Ui with (!f) v t; auto. Qed.
Theorem Eg_refl: forall l f v, Inf l f -> Inf l (Ex v f). Proof. intros. apply Eg with f (#v); auto. Qed.
Theorem Ug: forall l f, Inf l f -> forall v, (forall p, In p l->~FreeVar v p) -> Inf l (Any v f). Proof. intros. apply IUg; auto. Qed.
Theorem Any_rename: forall l v f, Inf l (Any v f) -> forall v' f', TFFSub v (Var v') f f' -> ~FreeVar v' f -> Inf l (Any v' f'). Proof. intros. apply IMp with (Any v f); auto. apply Inf_incl with nil; auto. apply Ded. apply Ug; auto. apply Ui with f v (# v'); auto. intros. destruct H2. subst p. intros C. inversion C; contradiction. destruct H2. Qed.
Theorem nFV_Ei: forall v f l, ~FreeVar v f -> Inf l (Ex v f) -> Inf l f. Proof. unfold Ex. intros. apply Contra with (Any v (!f)); auto. apply Inf_incl with ((!f)::nil); auto. intros x Hx. destruct Hx. subst x; auto. destruct H1. apply IUg; auto. intros. destruct H1. subst p. contradict H; inversion H; auto. destruct H1. Qed.
Theorem Ei: forall l f v, Inf l (Ex v f) -> forall f' g, Inf l (f'==>g) -> forall v', TFFSub v (Var v') f f' -> (forall p, In p l->~FreeVar v' p) -> ~FreeVar v' f -> ~FreeVar v' g -> Inf l g. Proof. unfold Ex. intros. destruct (nat_eq_dec v' v) as [Hv|Hv]. subst v'. assert (f=f'). apply Sub_unique with v (#v) f; auto. subst f'. apply IMp with f; auto. apply nFV_Ei with v; auto.
  apply Contra with (Any v (!f)); auto. apply Any_rename with v' (!f'); auto. apply Ug; auto. apply Contra with g; auto. apply IMp with f'; auto. intros. destruct H5; auto. subst p. contradict H4; inversion H4; auto. apply Sub_nFV with (# v') (!f); auto. intros C. inversion C. contradict Hv; auto. Qed.
Theorem Ei': forall l f v g, Inf l (Ex v f) -> Inf l (f==>g) -> ~FreeVar v g -> (forall p, In p l->~FreeVar v p) -> Inf l g. Proof. unfold Ex. intros. apply Contra with (Any v (!f)); auto. apply Ug. apply IMp with (!g); auto. apply IMp with (!(!f)==>!(!g)); auto. apply Imp_trans with f; auto. apply Imp_trans with g; auto. intros. destruct H3; auto. subst p; auto. Qed.
Theorem Ui_refl: forall l f v, Inf l (Any v f) -> Inf l f. Proof. intros. apply Ui with f v (#v); auto. Qed.
Hint Resolve Ui Eg Eg_refl Ug Any_rename Ei Ei' Ui_refl.

Theorem Ex_rename: forall l v f, Inf l (Ex v f) -> forall v' f', TFFSub v (Var v') f f' -> ~FreeVar v' f -> Inf l (Ex v' f'). Proof. unfold Ex. intros. apply Contra with (Any v (! f)); auto. apply Any_rename with v' (!f'); auto. destruct (nat_eq_dec v v'). subst v'. replace f' with f; auto. apply TFFSub_unique with v (#v) f; auto. apply Sub_nFV with (#v') (!f); auto. Qed.
Theorem Any_swap: forall v v' f l, Inf l (Any v (Any v' f)) -> Inf l (Any v' (Any v f)). Proof. intros. apply IMP with (Any v (Any v' f)) nil l; auto. apply Ded. apply Ug. apply Ug. apply IMp with (Any v' f); auto. apply Ded. apply Ui_refl with v'; auto. apply Ui_refl with v; auto. intros. apply In_one in H0. subst p. auto. intros. apply In_one in H0. subst p. auto. Qed.
Theorem Ex_swap: forall v v' f l, Inf l (Ex v (Ex v' f)) -> Inf l (Ex v' (Ex v f)). Proof. intros. destruct (nat_eq_dec v' v) as [Hv|Hn]. subst v'; auto. apply IMP with (Ex v (Ex v' f)) nil l; auto. apply Ded. clear H. apply Ei' with (Ex v' f) v; auto. apply Inf_incl'. apply Ded. apply Ei' with f v'; auto. intros. apply In_one in H. subst p; auto. intros. apply In_one in H. subst p; auto. Qed.
Theorem ExAny__AnyEx: forall v u f l, Inf l (Ex v (Any u f)) -> Inf l (Any u (Ex v f)). Proof. intros. apply IMP with (Ex v (Any u f)) nil l; auto. clear H. apply Ded. apply Ei' with (Any u f) v; auto. apply Inf_incl'. apply Ded. apply Ug. apply Eg_refl. apply Ui_refl with u; auto. intros. apply In_one in H. subst p; auto. intros. apply In_one in H. subst p; auto. Qed.
Hint Resolve Ex_rename Any_swap Ex_swap ExAny__AnyEx.

Theorem AnyImp_dist: forall pre v f g, Inf pre (Any v (f==>g)) -> Inf pre (Any v f==>Any v g). Proof. intros. apply IMP with (Any v (f==>g)) nil pre; auto. clear H. apply Ded. apply Ded. apply Ug. apply IMp with f. apply Ui_refl with v; auto. apply Ui_refl with v; auto. intros. destruct H. subst p; auto. destruct H. subst p; auto. destruct H. Qed.
Theorem AnyAnd_dist1: forall pre v f g, Inf pre (Any v f &^ Any v g) -> Inf pre (Any v (f &^ g)). Proof. intros. apply IMP with (Any v f &^ Any v g) nil pre; auto. apply Ded. clear H. apply Ug. apply And_intro. apply Ui_refl with v. eapply And_elim1; eauto. apply Ui_refl with v. eapply And_elim2; eauto. intros. apply In_one in H. subst p. auto. Qed. 
Theorem AnyAnd_dist2: forall pre v f g, Inf pre (Any v (f &^ g)) -> Inf pre (Any v f &^ Any v g). Proof. intros. apply And_intro; apply IMP with (Any v (f&^g)) nil pre; auto; apply Ded; apply Ug. apply And_elim1 with g. apply Ui_refl with v; auto. intros. apply In_one in H0. subst p; auto. apply And_elim2 with f. apply Ui_refl with v; auto. intros. apply In_one in H0. subst p; auto. Qed.
Theorem AnyOr_dist1: forall pre v f g, Inf pre (Any v f |^ Any v g) -> Inf pre (Any v (f |^ g)). Proof. intros. apply IMP with (Any v f |^ Any v g) nil pre; auto. apply Ded. apply Ug. apply Or_elim with (Any v f) (Any v g); auto; apply Ded; [apply Or_intro1| apply Or_intro2]; apply Ui_refl with v; auto. intros. apply In_one in H0. subst p; auto. Qed.
Theorem ExAnd_dist1: forall pre v f g, Inf pre (Ex v (f &^g)) -> Inf pre (Ex v f &^ Ex v g). Proof. intros. apply IMP with (Ex v (f&^g)) nil pre; auto. clear H. apply Ded. apply Ei' with (f&^g) v; auto. apply Inf_incl'. apply Ded. apply And_intro. apply Eg_refl. apply And_elim1 with g; auto. apply Eg_refl. apply And_elim2 with f; auto. intros. apply In_one in H. subst p; auto. Qed.
Theorem ExOr_dist1: forall pre v f g, Inf pre (Ex v (f |^g)) -> Inf pre (Ex v f |^ Ex v g). Proof. intros. apply IMP with (Ex v (f|^g)) nil pre; auto. clear H. apply Ded. apply Ei' with (f|^g) v; auto. apply Inf_incl'. apply Ded. apply Or_elim with f g; auto. intros. apply In_one in H; subst p; auto. Qed.
Theorem ExOr_dist2: forall pre v f g, Inf pre (Ex v f |^ Ex v g) -> Inf pre (Ex v (f |^g)). Proof. intros. apply IMP with (Ex v f|^Ex v g) nil pre; auto. clear H. apply Ded. apply Or_elim with (Ex v f) (Ex v g); auto; apply Inf_incl'; apply Ded. apply Ei' with f v; auto. intros. apply In_one in H; subst p; auto. apply Ei' with g v; auto. intros. apply In_one in H; subst p; auto. Qed.
Hint Resolve AnyImp_dist AnyAnd_dist1 AnyAnd_dist2 AnyOr_dist1 ExAnd_dist1 ExOr_dist1 ExOr_dist2.

