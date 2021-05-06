Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.

Hint Resolve incl_refl lt_le_weak Nat.le_max_l Nat.le_max_r le_not_lt lt_not_le.

(* LQ *)
Inductive Term : Set :=
|Var: nat -> Term
|Const: nat -> Term
|Func: nat -> list Term -> Term
.

Inductive Formula : Set :=
|Pred: nat -> list Term -> Formula
|Neg: Formula -> Formula
|Imp: Formula -> Formula -> Formula
|Any: nat -> Formula -> Formula
.

Definition LQand (f g:Formula) := Neg (Imp f (Neg g)).
Definition LQor (f g:Formula) := Imp (Neg f) g.
Definition Ex v f := Neg (Any v (Neg f)).

(* Declare Scope LQ_scope. *)
Notation "! f" := (Neg f) (at level 80, no associativity) : LQ_scope.
Notation "f ==> g" := (Imp f g) (at level 83, right associativity) : LQ_scope.
Notation "f &^ g" := (LQand f g) (at level 81, left associativity) : LQ_scope.
Notation "f |^ g" := (LQor f g) (at level 82, left associativity) : LQ_scope.

Open Scope LQ_scope.

Inductive FreeVarTerm (v:nat) : Term -> Prop :=
|FVT_var: FreeVarTerm v (Var v)
|FVT_func: forall i t l, FreeVarTerm v t -> In t l -> FreeVarTerm v (Func i l)
.
Inductive FreeVar (v:nat) : Formula -> Prop :=
|FV_pred: forall i t l, FreeVarTerm v t -> In t l -> FreeVar v (Pred i l)
|FV_Neg: forall f, FreeVar v f -> FreeVar v (!f)
|FV_Imp1: forall f g, FreeVar v f -> FreeVar v (f==>g)
|FV_Imp2: forall f g, FreeVar v g -> FreeVar v (f==>g)
|FV_Any: forall i f, i<>v -> FreeVar v f -> FreeVar v (Any i f)
.
Inductive VarIn (v:nat) : Formula -> Prop :=
|VI_pred: forall i t l, FreeVarTerm v t -> In t l -> VarIn v (Pred i l)
|VI_Neg: forall f, VarIn v f -> VarIn v (!f)
|VI_Imp1: forall f g, VarIn v f -> VarIn v (f==>g)
|VI_Imp2: forall f g, VarIn v g -> VarIn v (f==>g)
|VI_Any1: forall i f, VarIn v f -> VarIn v (Any i f)
|VI_Any2: forall f, VarIn v (Any v f)
.

Inductive ConstInTerm (c:nat) : Term -> Prop :=
|CIT_const: ConstInTerm c (Const c)
|CIT_func: forall i t l, ConstInTerm c t -> In t l -> ConstInTerm c (Func i l)
.

Inductive ConstIn (c:nat) : Formula -> Prop :=
|CI_pred: forall i t l, ConstInTerm c t -> In t l -> ConstIn c (Pred i l)
|CI_Neg: forall f, ConstIn c f -> ConstIn c (!f)
|CI_Imp1: forall f g, ConstIn c f -> ConstIn c (f==>g)
|CI_Imp2: forall f g, ConstIn c g -> ConstIn c (f==>g)
|CI_Any: forall n f, ConstIn c f -> ConstIn c (Any n f)
.

Inductive SubTerm (v:nat) (t:Term) : relation Term :=
|ST_var1: SubTerm v t (Var v) t
|ST_var2: forall i, i<>v -> SubTerm v t (Var i) (Var i)
|ST_const: forall i, SubTerm v t (Const i) (Const i)
|ST_func1: forall i, SubTerm v t (Func i nil) (Func i nil)
|ST_func2: forall i f g l m, SubTerm v t (Func i l) (Func i m) -> SubTerm v t f g -> SubTerm v t (Func i (f::l)) (Func i (g::m))
.

Inductive Sub (v:nat) (t:Term) : relation Formula :=
|Sub_pred1: forall i, Sub v t (Pred i nil) (Pred i nil)
|Sub_pred2: forall i f g l m, SubTerm v t f g -> Sub v t (Pred i l) (Pred i m) -> Sub v t (Pred i (f::l)) (Pred i (g::m))
|Sub_neg: forall f g, Sub v t f g -> Sub v t (!f) (!g)
|Sub_imp: forall f1 f2 g1 g2, Sub v t f1 g1 -> Sub v t f2 g2 -> Sub v t (f1==>f2) (g1==>g2)
|Sub_any1: forall f, Sub v t (Any v f) (Any v f)
|Sub_any2: forall i f g, i<>v -> Sub v t f g -> Sub v t (Any i f) (Any i g)
.

Inductive BoundByRep (x y:nat) : Formula -> Prop :=
|BBR_neg: forall f, BoundByRep x y f -> BoundByRep x y (!f)
|BBR_imp1: forall f g, BoundByRep x y f -> BoundByRep x y (f==>g)
|BBR_imp2: forall f g, BoundByRep x y g -> BoundByRep x y (f==>g)
|BBR_any1: forall f, y<>x -> FreeVar x f -> BoundByRep x y (Any y f)
|BBR_any2: forall i f, i<>x -> BoundByRep x y f -> BoundByRep x y (Any i f)
.

Inductive TFFSub (v:nat) (t:Term) : relation Formula := TFFSub_intro: forall f g, Sub v t f g -> (forall i, FreeVarTerm i t -> ~BoundByRep v i f) -> TFFSub v t f g.

Inductive LQAxiom: Formula -> Prop :=
|LQA1 : forall f g, LQAxiom (f==>g==>f)
|LQA2 : forall f g h, LQAxiom ((f==>g==>h)==>(f==>g)==>f==>h)
|LQA3 : forall f g, LQAxiom ((!f==>!g)==>g==>f)
|LQA4 : forall f v t g, TFFSub v t f g -> LQAxiom (Any v f ==> g)
|LQA5 : forall v f g, ~FreeVar v f -> LQAxiom (Any v (f==>g) ==> f ==> Any v g)
.

Inductive LQTheorem : Formula -> Prop:=
|LQAx: forall f, LQAxiom f -> LQTheorem f
|LQMp: forall f g, LQTheorem (f==>g) -> LQTheorem f -> LQTheorem g
|LQUg: forall v f, LQTheorem f -> LQTheorem (Any v f)
.

Inductive LQInf (pre:list Formula): Formula -> Prop :=
|LQIAx: forall f, LQAxiom f -> LQInf pre f
|LQIPre: forall f, In f pre -> LQInf pre f
|LQIMp: forall f g p1 p2, incl p1 pre -> incl p2 pre -> LQInf p1 (f==>g) -> LQInf p2 f -> LQInf pre g
|LQIUg: forall v f, (forall p, In p pre -> ~FreeVar v p) -> LQInf pre f -> LQInf pre (Any v f)
.
Hint Constructors FreeVarTerm FreeVar VarIn ConstInTerm ConstIn SubTerm Sub BoundByRep TFFSub LQAxiom LQTheorem LQInf.

Fixpoint termDepth (t:Term) : nat := match t with |Var _ => 0 |Const _ => 0 |Func _ l => S (fold_right (fun t x=>max x (termDepth t)) 0 l) end.
Definition Term_eq_dec: forall t u:Term, {t=u}+{t<>u}. intros t. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun t=>forall u, {t=u}+{t<>u}). clear t. intros t IH u. destruct t; destruct u; try (right;discriminate). destruct (nat_eq_dec n n0); [subst n0; left|right]; auto. contradict n1; inversion n1; auto. destruct (nat_eq_dec n n0); [subst n0; left|right]; auto. contradict n1; inversion n1; auto. destruct (nat_eq_dec n n0); [subst n0|right]; auto. revert l0. induction l; intros. destruct l0; [left|right]; auto. intros C; inversion C. destruct l0. right; intros C; inversion C. destruct (IH a) with (u:=t). unfold ltof. simpl. apply le_n_S. apply Nat.le_max_r. subst t. destruct IHl with (l0:=l0). intros. apply IH. unfold ltof. unfold ltof in H. apply lt_le_trans with (termDepth (Func n l)); auto. simpl. apply le_n_S. apply Nat.le_max_l. left. inversion e; auto. right. contradict n0. inversion n0; auto. right. contradict n0. inversion n0; auto. contradict n1. inversion n1; auto. Defined.
Definition Formula_eq_dec: forall f g:Formula, {f=g}+{f<>g}. induction f; destruct g; try (right; discriminate). destruct (nat_eq_dec n n0). subst n0. destruct (list_eq_dec Term_eq_dec l l0). subst l0; left; auto. right. contradict n0. inversion n0; auto. right. contradict n1; inversion n1; auto. destruct (IHf g); [subst g;left|right]; auto. contradict n; inversion n; auto. destruct (IHf1 g1); [subst g1; destruct (IHf2 g2); [subst g2; left|right] |right]; auto; contradict n; inversion n; auto. destruct (nat_eq_dec n n0); [subst n0|right]. destruct (IHf g); [subst g; left|right]; auto. contradict n0; inversion n0; auto. contradict n1; inversion n1; auto. Defined. 
Definition freeVarsTerm: forall t, {l| forall v, In v l <-> FreeVarTerm v t}. apply (Fix (well_founded_ltof Term termDepth)). intros t IH. destruct t. exists (n::nil). intros; split; intros. destruct H. subst n; auto. destruct H. inversion H; auto. exists nil. intros; split; intros. destruct H. inversion H.
  induction l. exists nil. intros; split; intros. destruct H. inversion H. destruct H3. destruct IHl as [vl H]. intros. apply IH. unfold ltof. unfold ltof in H. apply lt_le_trans with (termDepth (Func n l)); auto. simpl. apply le_n_S. apply Nat.le_max_l.
  destruct (IH a) as [al H0]. unfold ltof. simpl. apply le_n_S. apply Nat.le_max_r. exists (al++vl). intros; split; intros. apply in_app_or in H1. destruct H1. apply FVT_func with a; auto. apply H0; auto. apply H in H1. inversion H1. subst i l0. apply FVT_func with t; auto. apply in_or_app. inversion H1. subst i l0. destruct H5. subst t; left; apply H0; auto. right; apply H. apply FVT_func with t; auto. Defined.
Definition freeVars: forall f, {l| forall v, In v l <-> FreeVar v f}. induction f. exists (flat_map (fun t=> let (vl,_) := freeVarsTerm t in vl) l). intros; split; intros. apply in_flat_map in H. destruct H as [t [H H0]]. destruct (freeVarsTerm t) as [vl H1]. apply FV_pred with t; auto. apply H1; auto. inversion H. subst i l0. apply in_flat_map. exists t. split; auto. destruct (freeVarsTerm t) as [vl H0]. apply H0; auto.
  destruct IHf as [l H]. exists l; intros; split; intros. apply H in H0; auto. inversion H0. apply H; auto. destruct IHf1 as [l1 H]. destruct IHf2 as [l2 H0]. exists (l1++l2). intros; split; intros. apply in_app_or in H1. destruct H1. apply H in H1; auto. apply H0 in H1; auto. apply in_or_app. inversion H1. apply H in H3; auto. apply H0 in H3; auto. destruct IHf as [l H]. exists (remove nat_eq_dec n l). intros; split; intros. destruct (nat_eq_dec n v). subst n. contradict H0. apply remove_In. apply FV_Any; auto. apply H. apply remove_In2 in H0; auto. inversion H0. apply H in H4. apply in_in_remove; auto. Defined. 
Definition varsIn: forall f, {l| forall v, In v l <-> VarIn v f}. induction f. exists (flat_map (fun t=> let (vl,_) := freeVarsTerm t in vl) l). intros; split; intros. apply in_flat_map in H. destruct H as [t [H H0]]. destruct (freeVarsTerm t) as [vl H1]. apply VI_pred with t; auto. apply H1; auto. inversion H. subst i l0. apply in_flat_map. exists t. split; auto. destruct (freeVarsTerm t) as [vl H0]. apply H0; auto.
  destruct IHf as [l H]. exists l; intros; split; intros. apply H in H0; auto. inversion H0. apply H; auto. destruct IHf1 as [l1 H]. destruct IHf2 as [l2 H0]. exists (l1++l2). intros; split; intros. apply in_app_or in H1. destruct H1. apply H in H1; auto. apply H0 in H1; auto. apply in_or_app. inversion H1. apply H in H3; auto. apply H0 in H3; auto. destruct IHf as [l H]. exists (n::l). intros; split; intros. destruct H0. subst n; auto. apply H in H0; auto. inversion H0; auto. right. apply H; auto. Defined.

Definition constsInTerm: forall t, {l|forall c, In c l <-> ConstInTerm c t}. apply (Fix (well_founded_ltof Term termDepth)). intros t IH. destruct t. exists nil. intros; split; intros. destruct H. inversion H. exists (n::nil). intros; split; intros. destruct H. subst n; auto. destruct H. inversion H; auto. induction l. exists nil. intros; split; intros. destruct H. inversion H. destruct H3. destruct IHl as [m H]. intros. apply IH. unfold ltof. unfold ltof in H. apply lt_le_trans with (termDepth (Func n l)); auto. simpl. apply le_n_S. apply Nat.le_max_l. destruct (IH a) as [o H0]. unfold ltof. simpl. apply le_n_S. apply Nat.le_max_r. exists (o++m). intros; split; intros. apply in_app_or in H1. destruct H1. apply H0 in H1; auto. apply CIT_func with a; auto. apply H in H1. inversion H1. apply CIT_func with t; auto. apply in_or_app. inversion H1. subst i l0. destruct H5. subst a. apply H0 in H4; auto. right. apply H. apply CIT_func with t; auto. Defined.
Definition constsIn: forall f, {l|forall c, In c l <-> ConstIn c f}. induction f. exists (flat_map (fun t=>let (m,_):= constsInTerm t in m) l). intros; split; intros. apply in_flat_map in H. destruct H as [t [H H0]]. destruct (constsInTerm t) as [m H1]. apply H1 in H0. apply CI_pred with t; auto. apply in_flat_map. inversion H. exists t. split; auto. destruct (constsInTerm t) as [m H4]. apply H4; auto. destruct IHf as [l H]. exists l. intros; split; intros. apply H in H0; auto. apply H; inversion H0; auto. destruct IHf1 as [l1 H1]. destruct IHf2 as [l2 H2]. exists (l1++l2). intros; split; intros. apply in_app_or in H. destruct H; [apply H1 in H|apply H2 in H]; auto. apply in_or_app. inversion H. left; apply H1; auto. right; apply H2; auto. destruct IHf as [l H]. exists l. intros; split; intros. apply H in H0; auto. inversion H0. apply H; auto. Defined.
Definition subTerm: forall v t u, {s|SubTerm v t u s & forall s', SubTerm v t u s' -> s'=s}. intros v t. apply (Fix (well_founded_ltof Term termDepth)). intros u IH. destruct u. destruct (nat_eq_dec n v). subst n. exists t; auto. intros. inversion H; auto. contradict H1; auto. exists (Var n); auto. intros. inversion H; [contradict n0|]; auto. exists (Const n); auto. intros. inversion H; auto. assert (forall x, In x l->ltof Term termDepth x (Func n l)). intros. unfold ltof. simpl. apply le_n_S. clear IH. induction l. destruct H. destruct H. subst x. simpl. apply Nat.le_max_r. simpl. eapply le_trans. eapply IHl; auto. apply Nat.le_max_l. remember (fun x=>match in_dec Term_eq_dec x l with |left _ H0 => let (y,_,_):=IH x (H x H0) in y |right _ _=> Var 0 end) as f. assert (Hf: forall x, In x l-> SubTerm v t x (f x) /\ forall y, SubTerm v t x y->y=f x). intros. subst f. destruct (in_dec Term_eq_dec x l). destruct (IH x (H x i)). split; auto. contradiction. clear Heqf.  exists (Func n (map f l)). clear -Hf. induction l; auto. apply ST_func2; auto. destruct (Hf a); auto. clear -Hf. induction l; intros; simpl. inversion H; auto. inversion H. f_equal. f_equal. destruct (Hf a); auto. apply IHl in H4; auto. inversion H4; auto. Defined.
Definition sub: forall v t f, {g|Sub v t f g & forall g', Sub v t f g' -> g' = g}. induction f. exists (Pred n (map (fun u=>let (s,_,_):=subTerm v t u in s) l)). induction l; auto. simpl. apply Sub_pred2; auto. destruct (subTerm v t a); auto. induction l; simpl; intros. inversion H; auto. inversion H. subst i f l0 g'. f_equal. f_equal. destruct (subTerm v t a); auto. apply IHl in H5. inversion H5. auto. destruct IHf as [g H H0]. exists (!g); auto. intros. inversion H1. f_equal; auto. destruct IHf1 as [g1 H H0]. destruct IHf2 as [g2 H1 H2]. exists (g1==>g2); auto. intros. inversion H3. subst f0 f3 g'. f_equal; auto. destruct IHf as [g H H0]. destruct (nat_eq_dec n v). subst n. exists (Any v f); auto. intros. inversion H1; auto. contradict H4; auto. exists (Any n g); auto. intros. inversion H1. contradict n0; auto. f_equal; auto. Defined.
Definition BoundByRep_dec: forall x y f, {BoundByRep x y f}+{~BoundByRep x y f}. induction f. right. intros C; inversion C. destruct IHf; [left|right]; auto. contradict n; inversion n; auto. destruct IHf1; [left|destruct IHf2; [left|right]]; auto. intros C; inversion C; contradiction. destruct (nat_eq_dec n x). subst n. right. intros C; inversion C; contradict H1; auto. destruct (nat_eq_dec n y). subst n. destruct (freeVars f) as [l H]. destruct (in_dec nat_eq_dec x l). left. apply BBR_any1; auto. apply H; auto. destruct IHf; [left| right]; auto. intros C; inversion C. contradict n; apply H; auto. contradiction. destruct IHf; [left|right]; auto. intros C; inversion C. contradict n1; auto. contradiction. Defined.
Definition tffSub: forall v t f, {g|TFFSub v t f g & forall g', TFFSub v t f g' -> g'=g}+{forall g, ~TFFSub v t f g}. intros. destruct (sub v t f) as [g H H0]. destruct (freeVarsTerm t) as [l H1]. destruct Exists_dec with (P:=fun i=>BoundByRep v i f) (l:=l). intros. apply BoundByRep_dec. right. intros g' Hg. inversion Hg. apply Exists_exists in e. destruct e as [x [H6 H7]]. contradict H7. apply H3. apply H1; auto. left. exists g. apply TFFSub_intro; auto. intros. contradict n. apply Exists_exists. exists i; split; auto. apply H1; auto. intros. apply H0. inversion H2; auto. Defined.

Theorem FV_Or1: forall v f g, FreeVar v f -> FreeVar v (f |^ g). Proof. intros. unfold LQor. auto. Qed.
Theorem FV_Or2: forall v f g, FreeVar v g -> FreeVar v (f |^ g). Proof. intros. unfold LQor. auto. Qed.
Theorem FV_And1: forall v f g, FreeVar v f -> FreeVar v (f &^ g). Proof. intros. unfold LQand. auto. Qed.
Theorem FV_And2: forall v f g, FreeVar v g -> FreeVar v (f &^ g). Proof. intros. unfold LQand. auto. Qed.
Theorem FV_Ex: forall v i f, i<>v -> FreeVar v f -> FreeVar v (Ex i f). Proof. intros. unfold Ex. auto. Qed.
Theorem FV_Neg_inv: forall v f, FreeVar v (!f) -> FreeVar v f. Proof. intros. inversion H; auto. Qed.
Theorem FV_Imp_inv: forall v f g, FreeVar v (f==>g) -> FreeVar v f \/ FreeVar v g. Proof. intros. inversion H; auto. Qed.
Theorem FV_Any_inv1: forall v i f, FreeVar v (Any i f) -> FreeVar v f. Proof. intros. inversion H; auto. Qed.
Theorem FV_Any_inv2: forall v i f, FreeVar v (Any i f) -> i<>v. Proof. intros. inversion H; auto. Qed.
Theorem FV_Or_inv: forall v f g, FreeVar v (f |^ g) -> FreeVar v f \/ FreeVar v g. Proof. intros. inversion H; auto. inversion H1; auto. Qed.
Theorem FV_And_inv: forall v f g, FreeVar v (f &^ g) -> FreeVar v f \/ FreeVar v g. Proof. intros. inversion H; auto. inversion H1; auto. inversion H3; auto. Qed.
Theorem FV_Ex_inv1: forall v i f, FreeVar v (Ex i f) -> FreeVar v f. Proof. intros. inversion H; auto. inversion H1; auto. inversion H5; auto. Qed.
Theorem FV_Ex_inv2: forall v i f, FreeVar v (Ex i f) -> i<>v. Proof. intros. inversion H; auto. inversion H1; auto. Qed.
Hint Resolve FV_Or1 FV_Or2 FV_And1 FV_And2 FV_Ex FV_Imp_inv FV_Any_inv1 FV_Any_inv2 FV_Or_inv FV_And_inv FV_Ex_inv1 FV_Ex_inv2.

Theorem SubTermSelf: forall v t, SubTerm v (Var v) t t. Proof. intros v. apply (Fix (well_founded_ltof Term termDepth)). intros t IH. destruct t; auto. destruct (nat_eq_dec n v). subst n; auto. auto. induction l; auto. apply ST_func2. apply IHl. intros. apply IH. unfold ltof. unfold ltof in H. apply lt_le_trans with (termDepth (Func n l)); auto. simpl. apply le_n_S. apply Nat.le_max_l. apply IH. unfold ltof. simpl. apply le_n_S. apply Nat.le_max_r. Qed.
Theorem SubSelf: forall v f, Sub v (Var v) f f. Proof. induction f; auto. induction l; auto. apply Sub_pred2; auto. apply SubTermSelf; auto. destruct (nat_eq_dec n v). subst n; auto. auto. Qed.
Theorem SubTerm_noFV: forall v u t, ~FreeVarTerm v t -> SubTerm v u t t. Proof. intros v u t. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun t=>~FreeVarTerm v t->SubTerm v u t t). clear t. intros t IH H. destruct t. apply ST_var2. contradict H; subst n; auto. auto. revert H. revert IH. induction l; intros; auto. apply ST_func2. apply IHl; auto. intros. apply IH; auto. unfold ltof. unfold ltof in H0. apply lt_le_trans with (termDepth (Func n l)); auto. simpl. apply le_n_S. apply Nat.le_max_l. contradict H. inversion H. apply FVT_func with t; auto. apply IH. unfold ltof. simpl. apply le_n_S. apply Nat.le_max_r. contradict H. apply FVT_func with a; auto. Qed.
Theorem Sub_noFV: forall v t f, ~FreeVar v f -> Sub v t f f. Proof. induction f; intros. revert H. induction l; intros; auto. apply Sub_pred2. apply SubTerm_noFV; auto. contradict H. apply FV_pred with a; auto. apply IHl. contradict H. inversion H. apply FV_pred with t0; auto. apply Sub_neg. apply IHf; auto. apply Sub_imp; auto. destruct (nat_eq_dec n v). subst n; auto. apply Sub_any2; auto. Qed.
Theorem TFFSub_noFV: forall v t f, ~FreeVar v f -> TFFSub v t f f. Proof. intros. apply TFFSub_intro. apply Sub_noFV; auto. intros. contradict H. clear H0. induction H; auto. Qed.
Theorem TFFSubSelf: forall v f, TFFSub v (Var v) f f. Proof. intros. apply TFFSub_intro. apply SubSelf. intros. inversion H. clear H H1. induction f; intros C. inversion C. inversion C. contradiction. inversion C; contradiction. inversion C. contradict H1; auto. contradiction. Qed.
Theorem SubTerm_noFreeVar: forall v t u s, SubTerm v t u s -> ~FreeVarTerm v t -> ~FreeVarTerm v s. Proof. intros v t u s H H0. revert H. revert s. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun u=>forall s,SubTerm v t u s->~FreeVarTerm v s). clear u. intros u IH s H. destruct u. inversion H. subst s n; auto. contradict H2; inversion H2; auto. inversion H. intros C; inversion C. inversion H. intros C; inversion C. destruct H7. subst i l s. intros C. inversion C. subst i l. destruct H6. subst t0. contradict H4. apply IH with f; auto. unfold ltof. simpl. apply le_n_S. apply Nat.le_max_r.  contradict H4. clear -IH H3 H1. revert H3. revert IH. revert l0. induction m; intros. destruct H1. inversion H3. subst i l0 a m0. destruct H1. apply IH with f0; auto. unfold ltof. simpl. apply le_n_S. apply le_trans with (max (fold_right (fun t1 x => max x (termDepth t1)) 0 l) (termDepth f0)). apply Nat.le_max_r. apply Nat.le_max_l. rewrite <- H; auto. apply IHm with l; auto. intros. apply IH with y; auto. unfold ltof. unfold ltof in H0. apply lt_le_trans with (termDepth (Func n (f::l))); auto. simpl. apply le_n_S. remember (fold_right (fun (t1 : Term) (x : nat) => Init.Nat.max x (termDepth t1)) 0 l) as x. remember (termDepth f) as z. remember (termDepth f0) as w. 
  clear -x z w. destruct (le_lt_dec x w). rewrite max_r with x w; auto. destruct (le_lt_dec w z). rewrite max_r with w z; auto. rewrite max_r; auto. apply le_trans with w; auto. rewrite max_l with w z; auto. destruct (le_lt_dec x z). rewrite max_r; auto. rewrite max_l; auto. rewrite max_l with x w; auto. Qed.
Theorem Sub_noFreeVar: forall v t f g, Sub v t f g -> ~FreeVarTerm v t -> ~FreeVar v g. Proof. intros v t f g H. induction H; intros. intros C; inversion C. destruct H3. intros C. inversion C. subst i0 l0. destruct H5. subst t0. contradict H4. apply SubTerm_noFreeVar with t f; auto. apply IHSub in H1. apply H1. clear -H4 H2. apply FV_pred with t0; auto. apply IHSub in H0. contradict H0; inversion H0; auto. intros C. inversion C; contradict H3; auto. contradict H. inversion H. contradict H2; auto. apply IHSub in H1. contradict H1. inversion H1; auto. Qed.
Theorem SubTermRev: forall v u t s, ~FreeVarTerm u t -> SubTerm v (Var u) t s -> SubTerm u (Var v) s t. Proof. intros v u t. apply (Fix (well_founded_ltof Term termDepth)) with (P:=fun t=>forall s, ~FreeVarTerm u t->SubTerm v (Var u) t s->SubTerm u (Var v) s t). clear t. intros t IH s. intros. destruct t. inversion H0; auto. subst i s. apply ST_var2. contradict H. subst u; auto. inversion H0; auto. revert H0. revert H. revert IH. revert s. induction l; intros. inversion H0; auto. inversion H0. subst i f l0 s. apply ST_func2. apply IHl; auto. intros. apply IH; auto. unfold ltof. unfold ltof in H1. apply lt_le_trans with (termDepth (Func n l)); auto. simpl. apply le_n_S. apply Nat.le_max_l. contradict H. inversion H. apply FVT_func with t; auto. apply IH; auto. unfold ltof. simpl. apply le_n_S. apply Nat.le_max_r. contradict H. apply FVT_func with a; auto. Qed.
Theorem TFFSubRev: forall v u f g, ~FreeVar u f -> TFFSub v (Var u) f g -> TFFSub u (Var v) g f. Proof. induction f; intros. inversion H0. subst f g0. clear H2 H0. revert H1. revert H. revert g. induction l; intros. inversion H1. apply TFFSub_intro; auto. intros. intros C; inversion C. inversion H1. subst i f l0 g. apply TFFSub_intro. apply Sub_pred2; auto. apply SubTermRev; auto. contradict H. apply FV_pred with a; auto. apply IHl in H6. inversion H6; auto. contradict H. inversion H. apply FV_pred with t; auto. intros. intros C. inversion C. inversion H0. subst f0 g0. inversion H1. subst f0 g. assert (TFFSub v (Var u) f g0). apply TFFSub_intro; auto. intros. apply H2 in H3. contradict H3; auto. apply IHf in H3. inversion H3. apply TFFSub_intro; auto. intros. apply H6 in H9. contradict H9; inversion H9; auto. contradict H; auto. inversion H0. subst f g0. inversion H1. subst f0 f3 g. assert (TFFSub v (Var u) f1 g1). apply TFFSub_intro; auto. intros. apply H2 in H3. contradict H3; auto. assert (TFFSub v (Var u) f2 g2). apply TFFSub_intro; auto. intros. apply H2 in H4. contradict H4; auto. apply IHf1 in H3. apply IHf2 in H4. inversion H3. inversion H4. subst f g f0 g0. apply TFFSub_intro; auto. intros. intros C. inversion C; contradict H13; auto. contradict H; auto. contradict H; auto. inversion H0. subst f0 g0. assert (~BoundByRep v u (Any n f)). apply H2; auto. clear H2 H0. inversion H1. subst n f0 g.
  destruct (nat_eq_dec u v). subst u. apply TFFSub_intro; auto. intros; intros C; inversion C; contradict H5; auto. apply TFFSub_noFV; auto. subst i f0 g. destruct (nat_eq_dec n u). subst n. destruct (freeVars f) as [fl H7]. destruct (in_dec nat_eq_dec v fl). apply H7 in i. contradict H3; auto. replace g0 with f. apply TFFSub_noFV; auto. destruct (sub v (Var u) f) as [g H8 H9]. apply H9 in H6. subst g0. apply H9. apply Sub_noFV. contradict n; apply H7; auto. assert (TFFSub v (Var u) f g0). apply TFFSub_intro; auto. intros. inversion H0. subst i. contradict H3; auto. apply IHf in H0. inversion H0. subst f0 g. apply TFFSub_intro. apply Sub_any2; auto. intros. inversion H7. subst i. intros C. inversion C. contradict H4; auto. subst i f0. inversion H0. contradict H11. apply H9; auto. contradict H; auto. Qed.
Theorem BBR_FreeVar: forall x y f, BoundByRep x y f -> FreeVar x f. Proof. intros. induction H; auto. Qed.
Theorem BBR_VarIn: forall x y f, BoundByRep x y f -> VarIn y f. Proof. intros. induction H; auto. Qed.
Theorem FreeVar_VarIn: forall x f, FreeVar x f -> VarIn x f. Proof. intros. induction H; auto. apply VI_pred with t; auto. Qed.
Hint Resolve SubTermSelf SubSelf SubTerm_noFV Sub_noFV TFFSub_noFV TFFSubSelf SubTerm_noFreeVar Sub_noFreeVar SubTermRev TFFSubRev BBR_FreeVar BBR_VarIn FreeVar_VarIn.

Theorem InfMp: forall pre f g, LQInf pre (f==>g) -> LQInf pre f -> LQInf pre g. Proof. intros. apply LQIMp with f pre pre; auto. Qed.
Theorem ImpRefl: forall pre f, LQInf pre (f==>f). Proof. intros. apply LQIMp with (f==>f==>f) pre pre; auto. apply LQIMp with (f==>(f==>f)==>f) pre pre; auto. Qed.
Theorem LQInf_incl: forall l m f, LQInf l f -> incl l m -> LQInf m f. Proof. intros. apply LQIMp with f m l; auto. apply ImpRefl. Qed.
Theorem LQInf_incl1: forall p l f, LQInf l f -> LQInf (p::l) f. Proof. intros. apply LQInf_incl with l; auto. Qed.
Theorem LQTh_LQInf': forall f, LQTheorem f -> LQInf nil f. Proof. intros. induction H; auto. apply LQIMp with f nil nil; auto. Qed.
Theorem LQTh_LQInf: forall pre f, LQTheorem f -> LQInf pre f. Proof. intros. apply LQInf_incl with nil. apply LQTh_LQInf'; auto. intros x Hx. destruct Hx. Qed.
Theorem LQInf_LQTh: forall f, LQInf nil f -> LQTheorem f. Proof. intros. remember nil as l. revert Heql. induction H; intros; auto; subst pre. destruct H. apply incl_l_nil in H0. apply incl_l_nil in H. subst p1 p2. apply LQMp with f; auto. Qed.
Theorem InfTh': forall p l f, LQInf l f -> LQInf (remove Formula_eq_dec p l) (p==>f). Proof. intros. induction H; intros. apply InfMp with f; auto. destruct (Formula_eq_dec f p). subst p. apply ImpRefl. apply InfMp with f; auto. apply InfMp with (p==>f). apply InfMp with (p==>f==>g); auto. apply LQInf_incl with (remove Formula_eq_dec p p1); auto. apply LQInf_incl with (remove Formula_eq_dec p p2); auto. destruct (in_dec Formula_eq_dec p pre). apply InfMp with (Any v (p==>f)); auto. apply LQIUg; auto. intros q Hq. apply H. apply remove_In2 in Hq; auto. apply InfMp with (Any v f); auto. rewrite remove_notIn; auto. Qed.
Theorem InfTh: forall p l m f, Add p l m -> LQInf m f -> LQInf l (p==>f). Proof. intros. apply LQInf_incl with (remove Formula_eq_dec p m). apply InfTh'; auto. intros x Hx. apply Add_in with (x:=x) in H. assert (In x m). apply remove_In2 in Hx; auto. apply H in H1. destruct H1. subst x. contradict Hx. apply remove_In. auto. Defined.
Theorem InfTh1: forall p l f, LQInf (p::l) f -> LQInf l (p==>f). Proof. intros. apply InfTh with (p::l); auto. Qed.

Hint Resolve InfMp ImpRefl LQInf_incl LQInf_incl1 LQTh_LQInf LQInf_LQTh InfTh' InfTh InfTh1.

Theorem ImpIntro: forall pre f g, LQInf pre f -> LQInf pre (g==>f). Proof. intros. apply InfMp with f; auto. Qed.
Theorem ImpTrans: forall pre f g h, LQInf pre (f==>g) -> LQInf pre (g==>h) -> LQInf pre (f==>h). Proof. intros. apply InfTh1. apply InfMp with g; auto. apply InfMp with f; auto. Qed.
Theorem Absurd: forall pre f g, LQInf pre f -> LQInf pre (!f) -> LQInf pre g. Proof. intros. apply InfMp with f; auto. apply InfMp with (!g==>!f); auto. Qed.
Theorem Contra: forall pre f g, LQInf ((!f)::pre) g -> LQInf ((!f)::pre) (!g) -> LQInf pre f. Proof. intros. apply InfMp with (f==>f); auto. apply InfMp with (!f ==> !(f==>f)); auto. apply InfTh1. apply Absurd with g; auto. Qed.
Theorem NegElim: forall pre f, LQInf pre (!(!f)) -> LQInf pre f. Proof. intros. apply InfMp with (f==>f); auto. apply InfMp with (!f ==> !(f==>f)); auto. apply InfMp with (!(!(f==>f)) ==> !(!f)); auto. Qed.
Theorem NegIntro: forall pre f, LQInf pre f -> LQInf pre (!(!f)). Proof. intros. apply Contra with f; auto. apply NegElim; auto. Qed.
Theorem DualImp: forall pre f g, LQInf pre (f==>g) -> LQInf pre (!f ==>g) -> LQInf pre g. Proof. intros. apply Contra with f. apply InfMp with (!g); auto. apply InfMp with (!f==>!(!g)); auto. apply ImpTrans with g; auto. apply InfTh1. apply NegIntro; auto. apply InfMp with (!g); auto. apply InfMp with (!(!f) ==> !(!g)); auto. apply ImpTrans with f; auto. apply InfTh1. apply NegElim; auto. apply ImpTrans with g; auto. apply InfTh1. apply NegIntro; auto. Qed.

Hint Resolve ImpIntro ImpTrans Absurd Contra NegElim NegIntro DualImp.

Theorem OrIntro1: forall pre f g, LQInf pre f -> LQInf pre (f|^g). Proof. intros. apply InfTh1. apply Absurd with f; auto. Qed.
Theorem OrIntro2: forall pre f g, LQInf pre g -> LQInf pre (f|^g). Proof. intros. apply InfTh1. auto. Qed.
Theorem OrElim: forall pre f g h, LQInf pre (f==>h) -> LQInf pre (g==>h) -> LQInf pre (f |^g) -> LQInf pre h. Proof. intros. apply DualImp with f; auto. apply ImpTrans with g; auto. Qed.
Theorem AndIntro: forall pre f g, LQInf pre f -> LQInf pre g -> LQInf pre (f&^g). Proof. intros. apply Contra with g; auto. apply InfMp with f; auto. Qed.
Theorem AndElim1: forall pre f g, LQInf pre (f&^g) -> LQInf pre f. Proof. intros. apply Contra with (f==>!g); auto. apply InfTh1. apply Absurd with f; auto. Qed.
Theorem AndElim2: forall pre f g, LQInf pre (f&^g) -> LQInf pre g. Proof. intros. apply Contra with (f==>!g); auto. Qed.

Hint Resolve OrIntro1 OrIntro2 OrElim AndIntro AndElim1 AndElim2.

Theorem LQIUi: forall pre v t f g, LQInf pre (Any v f) -> TFFSub v t f g -> LQInf pre g. Proof. intros. apply InfMp with (Any v f); auto. apply LQIAx. apply LQA4 with t; auto. Qed.
Theorem LQIEg: forall pre v t f g, TFFSub v t f g -> LQInf pre g -> LQInf pre (Ex v f). Proof. intros. unfold Ex. apply Contra with g; auto. apply LQIUi with v t (!f); auto. inversion H. apply TFFSub_intro; auto. intros. intros C. inversion C. contradict H7; auto. Qed.
Theorem Any_rename: forall pre v v' f f', ~FreeVar v' f -> TFFSub v (Var v') f f' -> LQInf pre (Any v f) -> LQInf pre (Any v' f'). Proof. intros. apply LQIMp with (Any v f) nil pre; auto. apply InfTh1. apply LQIUg. intros. destruct H2. subst p. contradict H. inversion H; auto. destruct H2. apply LQIUi with v (Var v') f; auto. Qed.
Theorem LQIEi: forall pre v v' f f' g, (forall p, In p pre -> ~FreeVar v' p) -> ~FreeVar v' f -> ~FreeVar v' g -> TFFSub v (Var v') f f' -> LQInf pre (f'==>g) -> LQInf pre (Ex v f) -> LQInf pre g. Proof. unfold Ex. intros. destruct (nat_eq_dec v' v). subst v'. apply Contra with (Any v (! f)); auto. apply LQIUg. intros. destruct H5. subst p. contradict H1; inversion H1; auto. auto. assert (f'=f). destruct (tffSub v (Var v) f) as [[f'' H5]|H5]. apply e in H2. rewrite H2. symmetry; auto. contradict H2; auto. subst f'. apply Contra with g; auto. apply InfMp with f; auto.
  apply Contra with (Any v (!f)); auto. apply Any_rename with v' (!f'); auto. apply Sub_noFreeVar with (Var v') (!f). inversion H2; auto. intros C. inversion C. contradict n; auto. apply TFFSubRev. contradict H0; inversion H0; auto. inversion H2. apply TFFSub_intro; auto. intros. apply H6 in H9. contradict H9; auto. inversion H9; auto. apply LQIUg. intros. destruct H5. subst p. contradict H1. inversion H1; auto. auto. apply Contra with g; auto. apply InfMp with f'; auto. Qed. 

Hint Resolve LQIUi LQIEg Any_rename LQIEi.

Theorem Ex_rename: forall pre v v' f f', ~FreeVar v' f -> TFFSub v (Var v') f f' -> LQInf pre (Ex v f) -> LQInf pre (Ex v' f'). Proof. intros. apply LQIMp with (Ex v f) nil pre; auto. apply InfTh1. apply LQIEi with v v' f f'; auto. intros. destruct H2. subst p. contradict H. inversion H. inversion H3. inversion H7; auto. destruct H2. intros C. inversion C. inversion H3. contradict H6; auto. apply InfTh1. apply LQIEg with (Var v') f'; auto. Qed.
Theorem Any_swap: forall pre x y f, LQInf pre (Any x (Any y f)) -> LQInf pre (Any y (Any x f)). Proof. intros. apply LQIMp with (Any x (Any y f)) nil pre; auto. apply InfTh1. apply LQIUg. intros. destruct H0. subst p. intros C. inversion C. inversion H3. contradict H6; auto. destruct H0. apply LQIUg. intros. destruct H0. subst p. intros C. inversion C. contradict H2; auto. destruct H0. apply LQIMp with (Any y f) nil (Any x (Any y f)::nil); auto. apply InfTh1. apply LQIUi with y (Var y) f; auto. apply LQIUi with x (Var x) (Any y f); auto. Qed.
Theorem ExAny_AnyEx: forall pre x y f, LQInf pre (Ex x (Any y f)) -> LQInf pre (Any y (Ex x f)). Proof. intros. apply LQIMp with (Ex x (Any y f)) nil pre; auto. apply InfTh1. apply LQIUg. intros. destruct H0. subst p. intros C. apply FV_Ex_inv1 in C. apply FV_Any_inv2 in C. contradict C; auto. destruct H0. destruct (nat_eq_dec y x). subst y. apply LQIEi with x x (Any x f) (Any x f); auto. intros. destruct H0. subst p. intros C. apply FV_Ex_inv2 in C. contradict C; auto. destruct H0. intros C. apply FV_Any_inv2 in C. contradict C; auto. intros C. apply FV_Ex_inv2 in C. contradict C; auto. apply InfTh1. apply LQIEg with (Var x) f; auto. apply LQIUi with x (Var x) f; auto.
  destruct (varsIn f) as [l H0]. destruct (ubound_sig (x::y::l)) as [z H1 H2]. assert (z<>x). intros C. subst x. absurd (z<z); auto. assert (z<>y). intros C. subst y. absurd (z<z); auto. assert (~In z l). intros C. absurd (z<z); auto. clear H1 H2. destruct (tffSub x (Var z) f) as [[f' H1 H2]|H1]. apply LQIEi with x z (Any y f) (Any y f'); auto. intros. destruct H6. subst p. intros C. apply FV_Ex_inv1 in C. apply FV_Any_inv1 in C. contradict H5; apply H0; auto. destruct H6. intros C. apply FV_Any_inv1 in C. contradict H5; apply H0; auto. intros C. contradict H5. apply H0. apply FV_Ex_inv1 in C; auto.
  inversion H1. subst f0 g. apply TFFSub_intro; auto. intros. inversion H8. subst i. intros C. apply BBR_VarIn in C. inversion C. contradict H5; apply H0; auto. contradiction. apply InfTh1. apply LQIEg with (Var z) f'; auto. apply LQIUi with y (Var y) f'; auto. destruct (sub x (Var z) f) as [g H6 H7]. absurd (TFFSub x (Var z) f g); auto. apply TFFSub_intro; auto. intros. intros C. inversion H2. subst i. apply BBR_VarIn in C. contradict H5. apply H0; auto. Qed.
Theorem AnyAnd_dist1: forall pre v f g, LQInf pre (Any v f &^ Any v g) -> LQInf pre (Any v (f &^ g)). Proof. intros. apply LQIMp with (Any v f &^ Any v g) nil pre; auto. apply InfTh1. clear H. apply LQIUg. intros. destruct H. subst p. intros C. apply FV_And_inv in C. destruct C; apply FV_Any_inv2 in H; contradict H; auto. destruct H. apply AndIntro. apply InfMp with (Any v f). apply InfTh1. apply LQIUi with v (Var v) f; auto. eapply AndElim1; eauto. apply InfMp with (Any v g); auto. apply InfTh1. apply LQIUi with v (Var v) g; auto. eapply AndElim2; eauto. Qed.
Theorem AnyAnd_dist2: forall pre v f g, LQInf pre (Any v (f &^ g)) -> LQInf pre (Any v f &^ Any v g). Proof. intros. apply AndIntro. apply LQIMp with (Any v (f&^g)) nil pre; auto. apply InfTh1. apply LQIUg. intros. destruct H0. subst p. intros C. apply FV_Any_inv2 in C. contradict C; auto. destruct H0. apply InfMp with (f &^g). apply InfTh1. eapply AndElim1; eauto. apply LQIUi with v (Var v) (f&^g); auto. apply LQIMp with (Any v (f&^g)) nil pre; auto. apply InfTh1. apply LQIUg. intros. destruct H0. subst p. intros C. inversion C. contradict H2; auto. destruct H0. apply InfMp with (f&^g). apply InfTh1. eapply AndElim2; eauto. apply LQIUi with v (Var v) (f&^g); auto. Qed.
Theorem AnyOr_dist1: forall pre v f g, LQInf pre (Any v f |^ Any v g) -> LQInf pre (Any v (f |^ g)). Proof. intros. apply LQIMp with (Any v f |^ Any v g) nil pre; auto. apply InfTh1. apply LQIUg. intros. destruct H0. subst p. intros C. apply FV_Or_inv in C. destruct C; apply FV_Any_inv2 in H0; contradict H0; auto. destruct H0. apply OrElim with (Any v f) (Any v g); auto; apply InfTh1; [apply OrIntro1|apply OrIntro2]; eapply LQIUi with (v:=v) (t:=Var v); eauto. Qed. 
Theorem ExAnd_dist1: forall pre v f g, LQInf pre (Ex v (f &^g)) -> LQInf pre (Ex v f &^ Ex v g). Proof. intros. apply LQIMp with (Ex v (f&^g)) nil pre; auto. apply InfTh1. destruct (varsIn (f&^g)) as [l H0]. destruct (ubound_sig (v::l)) as [x H1 _]. assert (Hx:~In x l). intros C. absurd (x<x); auto. destruct (tffSub v (Var x) f) as [[f' H2 _]|H2]. destruct (tffSub v (Var x) g) as [[g' H3 _]|H3]. apply LQIEi with v x (f &^g) (f' &^g'); auto. intros. destruct H4. subst p. contradict Hx. apply H0. apply FV_Ex_inv1 in Hx; auto. destruct H4. contradict Hx; apply H0; auto. contradict Hx; apply H0. apply FV_And_inv in Hx. destruct Hx; apply FV_Ex_inv1 in H4; auto.
  inversion H2. inversion H3. apply TFFSub_intro; unfold LQand; auto. intros i H12 C. inversion C. inversion H14. contradict H16; auto. inversion H16. contradict H19; auto. apply InfTh1. apply AndIntro. apply LQIEg with (Var x) f'; auto. apply AndElim1 with g'; auto. apply LQIEg with (Var x) g'; auto. apply AndElim2 with f'; auto.
  destruct (sub v (Var x) g) as [g' H4 _]. absurd (TFFSub v (Var x) g g'); auto. apply TFFSub_intro; auto. intros. intros C. inversion H5. subst i. apply BBR_VarIn in C. absurd (x<x); auto. apply H1. right. apply H0. unfold LQand; auto. destruct (sub v (Var x) f) as [f' H3 _]. absurd (TFFSub v (Var x) f f'); auto. apply TFFSub_intro; auto. intros. inversion H4. subst i. intros C. apply BBR_VarIn in C. absurd (x<x); auto. apply H1. right. apply H0. unfold LQand; auto. Qed.
Theorem ExOr_dist1: forall pre v f g, LQInf pre (Ex v f |^ Ex v g) -> LQInf pre (Ex v (f|^g)). Proof. intros. apply LQIMp with (Ex v f|^Ex v g) nil pre; auto. apply InfTh1. destruct (varsIn f) as [l1 H0]. destruct (varsIn g) as [l2 H1]. destruct (ubound_sig (v::l1++l2)) as [x H3 _]. destruct (sub v (Var x) f) as [f' H4 _]. assert (TFFSub v (Var x) f f'). apply TFFSub_intro; auto. intros. inversion H2. subst i. intros C. apply BBR_VarIn in C. absurd (x<x); auto. apply H3. right. apply in_or_app; left; apply H0; auto. destruct (sub v (Var x) g) as [g' H5 _]. assert (TFFSub v (Var x) g g'). apply TFFSub_intro; auto. intros. inversion H6. subst i. intros C. apply BBR_VarIn in C. absurd (x<x); auto. apply H3. right; apply in_or_app; right; apply H1; auto. assert (~FreeVar x (Ex v (f|^g))). intros C. inversion C. inversion H8.  inversion H12. absurd (x<x); auto. apply H3. right. apply in_or_app. inversion H14; [left|right]. apply H0. inversion H16; auto. apply H1; auto.
  apply OrElim with (Ex v f) (Ex v g); auto; apply LQInf_incl with nil; auto; apply InfTh1. apply LQIEi with v x f f'; auto. intros. destruct H8. subst p. intros C. inversion C. inversion H9. inversion H13. absurd (x<x); auto. apply H3. right. apply in_or_app. left. apply H0; auto. destruct H8. intros C. absurd (x<x); auto. apply H3. right. apply in_or_app. left. apply H0; auto. apply InfTh1. apply LQIEg with (Var x) (f' |^ g'); auto. apply TFFSub_intro; auto. apply Sub_imp; auto. intros. inversion H8. subst i. intros C. inversion C. inversion H10. inversion H2. contradict H13; auto. inversion H6. contradict H10; auto.
  apply LQIEi with v x g g'; auto. intros. destruct H8. subst p. intros C. inversion C. inversion H9. inversion H13. absurd (x<x); auto. apply H3. right; apply in_or_app; right; apply H1; auto. destruct H8. intros C. absurd (x<x); auto. apply H3. right; apply in_or_app; right; apply H1; auto. apply InfTh1. apply LQIEg with (Var x) (f' |^ g'); auto. unfold LQor. apply TFFSub_intro; auto. intros. inversion H8. subst i. intros C. inversion C. inversion H10. inversion H2. contradict H13; auto. inversion H6. contradict H10; auto. Qed.
Theorem ExOr_dist2: forall pre v f g, LQInf pre (Ex v (f|^g)) -> LQInf pre (Ex v f |^ Ex v g). Proof. intros. apply LQIMp with (Ex v (f|^g)) nil pre; auto. apply InfTh1. destruct (varsIn f) as [l1 H1]. destruct (varsIn g) as [l2 H2]. destruct (ubound_sig (v::l1++l2)) as [x H3 _]. destruct (sub v (Var x) f) as [f' H4 _]. destruct (sub v (Var x) g) as [g' H5 _]. apply LQIEi with v x (f|^g) (f'|^g'); auto. intros. destruct H0. subst p. intros C. inversion C. inversion H6. inversion H10. absurd (x<x); auto. apply H3. right. apply in_or_app. inversion H12; [left|right]. apply H1. inversion H14; auto. apply H2; auto. destruct H0. intros C. absurd (x<x); auto. apply H3. right; apply in_or_app. inversion C; [left|right]. apply H1. inversion H6; auto. apply H2; auto. intros C. absurd (x<x); auto. apply H3. right. apply in_or_app. inversion C; [left|right]. apply H1. inversion H6. inversion H9. inversion H11. inversion H15; auto. apply H2. inversion H6. inversion H9. inversion H13; auto. unfold LQor. apply TFFSub_intro; auto. intros. inversion H0. subst i. intros C. apply BBR_VarIn in C. absurd (x<x); auto. apply H3. right. apply in_or_app. inversion C; [left|right]. apply H1. inversion H7; auto. apply H2; auto.
  apply InfTh1. apply OrElim with f' g'; auto; apply InfTh1. apply OrIntro1. apply LQIEg with (Var x) f'; auto. apply TFFSub_intro; auto. intros. inversion H0. subst i. intros C. apply BBR_VarIn in C. absurd (x<x); auto. apply H3. right; apply in_or_app; left; apply H1; auto. apply OrIntro2. apply LQIEg with (Var x) g'; auto. apply TFFSub_intro; auto. intros. inversion H0. subst i. intros C. apply BBR_VarIn in C. absurd (x<x); auto. apply H3. right; apply in_or_app; right; apply H2; auto. Qed.

Hint Resolve Ex_rename Any_swap ExAny_AnyEx AnyAnd_dist1 AnyAnd_dist2 AnyOr_dist1 ExAnd_dist1 ExOr_dist1 ExOr_dist2.
