Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.

(* LP *)
Inductive Formula : Set :=
|Var: nat -> Formula
|Neg: Formula -> Formula
|Imp: Formula -> Formula -> Formula
.

Notation "# n" := (Var n) (at level 80, no associativity) : LP_scope.
Notation "! f" := (Neg f) (at level 82, no associativity) : LP_scope.
Notation "f ==> g" := (Imp f g) (at level 85, right associativity) : LP_scope.

Open Scope LP_scope.
Fixpoint interpret (f:Formula) (a:nat->bool) := match f with |# n => a n | ! g => negb (interpret g a) | g ==> h => orb (negb (interpret g a)) (interpret h a) end.

Inductive LPAxiom: Formula -> Prop :=
|LPA1 : forall f g, LPAxiom (f==>g==>f)
|LPA2 : forall f g h, LPAxiom ((f==>g==>h)==>(f==>g)==>f==>h)
|LPA3 : forall f g, LPAxiom ((!f==>!g)==>g==>f)
.
Inductive LPTheorem : Formula -> Prop:=
|LPAx: forall f, LPAxiom f -> LPTheorem f
|LPImp: forall f g, LPTheorem (f==>g) -> LPTheorem f -> LPTheorem g
.
Inductive LPInf (p:list Formula) : Formula -> Prop:=
|LPIAx : forall f, LPAxiom f -> LPInf p f
|LPIIn : forall f, In f p -> LPInf p f
|LPIImp: forall f g, LPInf p (f==>g) -> LPInf p f -> LPInf p g
.
Hint Constructors LPAxiom LPTheorem LPInf.

Theorem LPTheorem_Inf: forall p f, LPTheorem f -> LPInf p f. Proof. intros. induction H; auto. apply LPIImp with f; auto. Qed.
Theorem LPInf_Theorem: forall f, LPInf nil f -> LPTheorem f. Proof. intros. induction H; auto. inversion H. apply LPImp with f; auto. Qed.
Theorem Inf_incl: forall f l m, incl l m -> LPInf l f -> LPInf m f. Proof. intros. induction H0; auto. apply LPIImp with f; auto. Qed.
Theorem Inf_cons: forall f l p, LPInf l f -> LPInf (p::l) f. Proof. intros. apply Inf_incl with l; auto. Qed.
Theorem imp_refl: forall l f, LPInf l (f==>f). Proof. intros. apply LPIImp with (f==>f==>f); auto. apply LPIImp with (f==>(f==>f)==>f); auto. Qed.
Theorem imp_intro: forall l f g, LPInf l f -> LPInf l (g==>f). Proof. intros. apply LPIImp with f; auto. Qed.
Hint Resolve LPTheorem_Inf LPInf_Theorem Inf_incl Inf_cons imp_refl imp_intro.

Theorem InfTh': forall p l m f, Add p l m -> LPInf m f -> LPInf l (p==>f). Proof. intros. induction H0; auto. apply Add_in with (x:=f) in H. apply H in H0. destruct H0; [subst p|]; auto. apply LPIImp with (p==>f); auto. apply LPIImp with (p==>f==>g); auto. Qed.
Theorem InfTh: forall p l f, LPInf (p::l) f -> LPInf l (p==>f). Proof. intros. apply InfTh' with (p::l); auto. Qed.
Theorem LPabsurd: forall p f g, LPInf p f -> LPInf p (!f) -> LPInf p g. Proof. intros. apply LPIImp with f; auto. apply LPIImp with (!g==>!f); auto. Qed.
Theorem contra': forall l m f g, Add (!f) l m -> LPInf m g -> LPInf m (!g) -> LPInf l f. Proof. intros. apply LPIImp with (f==>f); auto. apply LPIImp with (!f==>!(f==>f)); auto. apply InfTh' with m; auto. apply LPabsurd with g; auto. Qed.
Theorem contra: forall l f g, LPInf ((!f)::l) g -> LPInf ((!f)::l) (!g) -> LPInf l f. Proof. intros. apply contra' with ((!f)::l) g; auto. Qed.
Hint Resolve InfTh' InfTh LPabsurd contra' contra.

Theorem neg_elim: forall p f, LPInf p (!(!f)) -> LPInf p f. Proof. intros. apply LPIImp with (f==>f); auto. apply LPIImp with (!f==>!(f==>f)); auto. apply LPIImp with (!(!(f==>f))==>!(!f)); auto. Qed.
Theorem neg_intro: forall p f, LPInf p f -> LPInf p (!(!f)). Proof. intros. apply contra with f; auto. apply neg_elim; auto. Qed.
Theorem imp_trans: forall p f g h, LPInf p (f==>g) -> LPInf p (g==>h) -> LPInf p (f==>h). Proof. intros. apply InfTh. apply LPIImp with g; auto. apply LPIImp with f; auto. Qed.
Hint Resolve neg_elim neg_intro imp_trans.

Theorem neg_imp: forall p f g, LPInf p (f==>g) -> LPInf p (!f==>g) -> LPInf p g. Proof. intros. apply contra with f; apply LPIImp with (!g); auto. apply LPIImp with (!f==>!(!g)); auto. apply imp_trans with g; auto. apply LPIImp with (!(!f)==>!(!(g))); auto. apply imp_trans with f; auto. apply imp_trans with g; auto. Qed.

Definition LPand (f g:Formula) := !(f==>!g).
Definition LPor (f g:Formula) := !f==>g.
Notation "f &^ g" := (LPand f g) (at level 83, left associativity) : LP_scope.
Notation "f |^ g" := (LPor f g) (at level 84, left associativity) : LP_scope.

Theorem or_intro1: forall p f g, LPInf p f -> LPInf p (f|^g). Proof. intros. apply InfTh. apply contra with f; auto. Qed.
Theorem or_intro2: forall p f g, LPInf p g -> LPInf p (f|^g). Proof. intros. apply InfTh. auto. Qed.
Theorem or_elim: forall p f g h, LPInf p (f==>h) -> LPInf p (g==>h) -> LPInf p (f|^g) -> LPInf p h. Proof. intros. apply neg_imp with f; auto. apply imp_trans with g; auto. Qed.
Theorem and_intro: forall p f g, LPInf p f -> LPInf p g -> LPInf p (f&^g). Proof. intros. apply contra with g; auto. apply LPIImp with f; auto. Qed.
Theorem and_elim1: forall p f g, LPInf p (f&^g) -> LPInf p f. Proof. intros. apply contra with (f==>!g); auto. apply InfTh. apply LPabsurd with f; auto. Qed.
Theorem and_elim2: forall p f g, LPInf p (f&^g) -> LPInf p g. Proof. intros. apply contra with (f==>!g); auto. Qed.
Hint Resolve neg_imp or_intro1 or_intro2 or_elim and_intro and_elim1 and_elim2.

Theorem deMorgan1: forall f g p, LPInf p (! f |^ ! g) -> LPInf p (!(f&^g)). Proof. intros. apply contra with f; auto. apply and_elim1 with g; auto. apply or_elim with (!f) (!g); auto. apply InfTh. apply LPabsurd with g; auto. apply and_elim2 with f; auto. Qed.
Theorem deMorgan2: forall f g p, LPInf p (!f &^ !g) -> LPInf p (!(f|^g)). Proof. intros. apply contra with f; auto. apply or_elim with f g; auto. apply InfTh. apply LPabsurd with g; auto. apply and_elim2 with (!f); auto. apply and_elim1 with (!g); auto. Qed.
Theorem deMorgan3: forall f g p, LPInf p (!(f|^g)) -> LPInf p (!f &^ !g). Proof. intros. apply and_intro; apply contra with (f|^g); auto. Qed.
Theorem deMorgan4: forall f g p, LPInf p (!(f&^g)) -> LPInf p (!f |^ !g). Proof. intros. apply contra with (f &^ g); auto. apply LPIImp with (!(!f)&^!(!g)). apply InfTh. apply and_intro; apply neg_elim. apply and_elim1 with (!(!g)); auto. apply and_elim2 with (!(!f)); auto. apply deMorgan3; auto. Qed.
Hint Resolve deMorgan1 deMorgan2 deMorgan3 deMorgan4.

Definition Tautology f: Prop := forall a, interpret f a = true.

Inductive Vars: nat-> Formula ->Prop:=
|VarV: forall n, Vars n (#n)
|VarN: forall n f, Vars n f -> Vars n (!f)
|VarI1: forall n f g, Vars n f -> Vars n (f==>g)
|VarI2: forall n f g, Vars n g -> Vars n (f==>g)
.
Hint Constructors Vars.
Definition vars' : forall f, {l| forall x, In x l<->Vars x f}. induction f. exists (n::nil). intros x; split; intros. destruct H. subst x; auto. destruct H. inversion H; auto. destruct IHf as [l H]. exists l. intros x. split; intros. apply VarN; apply H; auto. apply H. inversion H0; auto. destruct IHf1 as [l H]. destruct IHf2 as [m H1]. exists (l++m). intros. split; intros. apply in_app_or in H0. destruct H0. apply H in H0; auto. apply H1 in H0; auto. apply in_or_app. inversion H0; [left; apply H|right; apply H1]; auto. Defined.
Definition vars: forall f, {l|NoDup l & forall x, In x l<->Vars x f}. intros. destruct (vars' f) as [l H]. exists (nodup nat_eq_dec l). apply NoDup_nodup. intros. split; intros. apply nodup_In in H0. apply H; auto. apply nodup_In. apply H; auto. Defined.

Theorem interpret_equiv: forall f a b, (forall n, Vars n f -> a n = b n) -> interpret f a = interpret f b. Proof. induction f; simpl; intros; auto. f_equal. apply IHf; auto. rewrite IHf1 with a b; auto. rewrite IHf2 with a b; auto. Qed.
Fixpoint assign_prep (l:list nat):= match l with nil => (fun _=>false, nil)::nil |n::m => map (fun p=>(fun x=>if nat_eq_dec x n then true else fst p x, (#n)::snd p)) (assign_prep m) ++ map (fun p=>(fst p, (! #n)::snd p)) (assign_prep m) end.
Theorem assign_prep_spec1: forall l n p, In p (assign_prep l) -> In n l <-> In (# n) (snd p) \/ In (! #n) (snd p). Proof. induction l; simpl; intros. destruct H. destruct p. simpl. split; intros. destruct H0. inversion H. subst l. destruct H0; destruct H0. destruct H.  apply in_app_or in H. destruct H; apply in_map_iff in H; destruct H as [y [H3 H4]]; subst p; simpl; split; intros. destruct H. subst a; auto. destruct (IHl n y); auto. apply H0 in H. destruct H; auto. destruct H. destruct H. inversion H; auto. right. destruct (IHl n y); auto. destruct H. inversion H. right. destruct (IHl n y); auto. destruct H. subst a; auto. destruct (IHl n y); auto. apply H0 in H. destruct H; auto. destruct H. destruct H. inversion H. right. destruct (IHl n y); auto. destruct H. inversion H; auto. right. destruct (IHl n y); auto. Qed.
Theorem assign_prep_spec2: forall l n p, In p (assign_prep l) -> ~In n l -> fst p n=false. Proof. induction l; simpl; intros. destruct H. destruct p. destruct H. auto. destruct H. apply in_app_or in H. destruct H; apply in_map_iff in H; destruct H as [y [H1 H2]]; subst p; simpl. destruct (nat_eq_dec n a). contradict H0; auto. apply IHl; auto. apply IHl; auto. Qed.
Theorem assign_prep_spec3: forall l n p, NoDup l -> In p (assign_prep l) -> In n l -> fst p n=true <-> In (# n) (snd p). Proof. intros l n p H. revert n p. induction H; intros. destruct H0. simpl in H1. apply in_app_or in H1. destruct H1; apply in_map_iff in H1; destruct H1 as [y [H3 H4]]; subst p; destruct H2; simpl. subst x; simpl. destruct (nat_eq_dec n n). split; intros; auto. contradict n0; auto. destruct (nat_eq_dec n x). subst x. split; intros; auto. split; intros; auto. right. apply IHNoDup; auto. apply IHNoDup; auto. destruct H2; auto. contradict n0; inversion H2; auto.
  subst x. split; intros. rewrite assign_prep_spec2 with l n y in H1; auto. inversion H1. destruct H1. inversion H1. contradict H. destruct assign_prep_spec1 with l n y; auto. split; intros. right. apply IHNoDup; auto. destruct H2. inversion H2. apply IHNoDup; auto. Qed.
Theorem assign_prep_spec4: forall l n p, NoDup l -> In p (assign_prep l) -> In n l -> fst p n=false <-> In (! # n) (snd p). Proof. intros l n p H. revert n p. induction H; intros. destruct H0. simpl in H1. apply in_app_or in H1. destruct H1; apply in_map_iff in H1; destruct H1 as [y [H3 H4]]; subst p; destruct H2; simpl. subst x; simpl. destruct (nat_eq_dec n n). split; intros; auto. inversion H1. destruct H1. inversion H1. contradict H. destruct (assign_prep_spec1) with l n y; auto. contradict n0; auto. destruct (nat_eq_dec n x). subst x. split; intros; auto. inversion H2. destruct H2. inversion H2. contradict H. destruct (assign_prep_spec1) with l n y; auto. split; intros; auto. right. apply IHNoDup; auto. destruct H2. inversion H2. apply IHNoDup; auto. subst x. split; intros; auto. apply assign_prep_spec2 with l; auto. split; intros. right. apply IHNoDup; auto. destruct H2. inversion H2.  subst x; contradiction. apply IHNoDup; auto. Qed.
Theorem assign_prep_spec5: forall l a, NoDup l -> exists p, In p (assign_prep l) /\ forall n, In n l->a n=fst p n. Proof. intros. induction H; simpl; intros. exists (fun _=>false, nil). split; auto. destruct (IHNoDup) as [[b r] [H1 H2]]. simpl in H2. remember (a x) as c. destruct c. exists (fun y=>if nat_eq_dec y x then true else b y, (#x)::r). split. apply in_or_app. left. apply in_map_iff. exists (b,r); auto. intros. simpl. destruct H3. subst x. destruct (nat_eq_dec n n); auto. contradict n0; auto. destruct (nat_eq_dec n x). subst x. auto. apply H2; auto. exists (b, (! #x)::r). split. apply in_or_app. right. apply in_map_iff. exists (b,r); auto. simpl. intros. destruct H3. subst x. rewrite <- Heqc. rewrite <- assign_prep_spec2 with l n (b,r); auto. auto. Qed.

Definition Tauto_dec: forall f, {Tautology f}+{~Tautology f}. intros. destruct (vars f) as [l H1 H2]. remember (find (fun p=>negb (interpret f (fst p))) (assign_prep l)). destruct o. right. intros C. symmetry in Heqo. apply find_some in Heqo. destruct Heqo. rewrite C in H0. inversion H0. symmetry in Heqo. left. intros a. destruct (assign_prep_spec5 l a) as [p [H3 H4]]; auto. apply find_none with (x:=p) in Heqo; auto. rewrite interpret_equiv with (b:=fst p); auto. destruct (interpret f (fst p)); auto. intros. apply H4. apply H2; auto. Defined.
Theorem Theorem_Tauto: forall f, LPTheorem f -> Tautology f. Proof. intros. intros a. induction H. destruct H. simpl. destruct (interpret f a); simpl; auto. apply Bool.orb_true_r. simpl. destruct (interpret h a); destruct (interpret g a); destruct (interpret f a);simpl; auto.  simpl. destruct (interpret g a); destruct (interpret f a); simpl; auto. simpl in IHLPTheorem1. destruct (interpret g a); auto. contradict IHLPTheorem1. rewrite IHLPTheorem2. simpl. discriminate. Qed.
Theorem interpretTh: forall f (a:nat->bool) l, (forall n, Vars n f->In (if a n then (#n) else (!(#n))) l) -> LPInf l (if (interpret f a) then f else (!(f))). Proof. intros. induction f; intros. simpl. auto. simpl. destruct (interpret f a); simpl; auto. simpl. destruct (interpret f2 a). rewrite Bool.orb_true_r. auto. destruct (interpret f1 a); simpl. apply contra with f2; auto. apply LPIImp with f1; auto. apply InfTh. apply LPabsurd with f1; auto. Qed.
Theorem Tauto_Theorem: forall f, Tautology f -> LPTheorem f. Proof. intros. cut (forall m, (forall p, In p (assign_prep m) -> LPInf (snd p) f) -> LPTheorem f). intros. destruct (vars f) as [v H1 H2]. apply H0 with v. intros. replace f with (if interpret f (fst p) then f else (!f)). apply interpretTh. intros. remember (fst p n) as b. destruct b. apply assign_prep_spec3 with v; auto. apply H2; auto. apply assign_prep_spec4 with v; auto. apply H2; auto. replace (interpret f (fst p)) with true; auto.
  induction m; simpl; intros. cut (LPInf (snd (fun _:nat=>false, nil)) f); intros; auto. apply IHm. intros. apply neg_imp with (#a); apply InfTh. replace ((#a)::snd p) with (snd (fun x=>if nat_eq_dec x a then true else fst p x, (#a)::snd p)); auto. apply H0. apply in_or_app. left. apply in_map_iff. exists p; auto. replace ((! # a)::snd p) with (snd (fst p, (! # a)::snd p)); auto. apply H0. apply in_or_app. right. apply in_map_iff. exists p; auto. Qed.

Definition Theorem_dec: forall f, {LPTheorem f}+{~LPTheorem f}. intros. destruct (Tauto_dec f); [left|right]. apply Tauto_Theorem; auto. contradict n. apply Theorem_Tauto; auto. Defined.
