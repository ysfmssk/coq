Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import ModEq.
Require Import Peano_LQ.
Require Import Peano_Func.
Require Import Peano_rfunc.

(* pairing function *)
Definition pair_lt: relation (nat*nat) := fun p q => fst p+snd p<fst q+snd q \/ fst p+snd p=fst q+snd q /\ snd p<snd q.
Theorem wf_pair_lt : well_founded pair_lt. Proof. cut (forall z x y, x+y<=z -> Acc pair_lt (x,y)). intros. intros p. destruct p as [x y]. apply H with (x+y); auto. induction z; intros. inversion H. apply plus_is_O in H1. destruct H1; subst x y. apply Acc_intro. unfold pair_lt. intros. simpl in H0. destruct H0. inversion H0. destruct H0. inversion H1.
 apply le_lt_or_eq in H. destruct H; auto. revert H. revert x. induction y; intros. rewrite <- plus_n_O in H. subst x. apply Acc_intro. intros p H. destruct p as [x y]. unfold pair_lt in H. simpl in H. destruct H. rewrite <- plus_n_O in H; auto. destruct H. inversion H0. apply Acc_intro. intros p H0.
 destruct p as [x' y']. unfold pair_lt in H0. simpl in H0. destruct H0. apply IHz. apply le_S_n. rewrite <- H; auto. destruct H0. apply le_S_n in H1. apply le_lt_or_eq in H1. destruct H1. assert (Acc pair_lt (S x, y)). apply IHy. rewrite <- H. rewrite <- plus_n_Sm; auto. inversion H2. apply H3. unfold pair_lt. right. simpl. split; auto. rewrite H0. rewrite plus_n_Sm; auto. subst y'. apply IHy. rewrite H0; auto. Qed.

Inductive Pairing: nat -> nat -> nat -> Prop:=
|Pairing00: Pairing 0 0 0
|PairingX: forall y n, Pairing 0 y n -> Pairing (S y) 0 (S n)
|PairingY: forall x y n, Pairing (S x) y n -> Pairing x (S y) (S n)
.
Hint Constructors Pairing.

Lemma div'_plus_mult: forall n x y, n<>0 -> div' x n+y = div' (x+y*n) n. Proof. intros. unfold div'. destruct (divmod n x) as [[q [r [H1 H2] H3]]|H1]; [|contradiction]. destruct (divmod n (x+y*n)) as [[q' [r' [H4 H5] H6]]|H4]; [|contradiction]. destruct (H6 (q+y) r); auto. rewrite H1. rewrite plus_comm. rewrite plus_assoc. f_equal. rewrite <- mult_plus_distr_r. f_equal; auto. Qed.
Lemma div'_mult_self: forall n x, n<>0 -> div' (x*n) n = x. Proof. intros. unfold div'. destruct (divmod n (x*n)) as [[q [r [H1 H2] H3]]|H1]; [|contradiction]. destruct (H3 x 0); auto. Qed.
Lemma div'_le: forall n x y, x<=y -> div' x n<=div' y n. Proof. intros. replace y with (x+(y-x));[|rewrite <- le_plus_minus]; auto. unfold div'. destruct (divmod n x) as [[q [r [H1 H2] H3]]|H1]; destruct (divmod n (x+(y-x))) as [[s [t [H4 H5] H6]]|H4]; auto. destruct (le_lt_dec q s); auto. rewrite H1 in H4 at 1. absurd (n<=t); auto. apply plus_le_reg_l with (s*n). rewrite <- H4. apply le_trans with (q*n). replace (s*n+n) with (S s*n). apply mult_le_compat_r; auto. simpl; auto. rewrite <- plus_assoc; auto. subst n; inversion H2. Qed.
Theorem Pairing_unique: forall x y n m, Pairing x y n -> Pairing x y m -> n=m. Proof. intros x y. remember (x,y) as p. replace x with (fst p); [|subst p]; auto. replace y with (snd p); [|subst p]; auto. clear Heqp x y. apply (Fix wf_pair_lt) with (P:=fun p=>forall n m, Pairing (fst p) (snd p) n->Pairing (fst p) (snd p) m->n=m). clear p. intros p IH. destruct p as [x y]. simpl; intros. destruct y; [destruct x|]. inversion H; inversion H0; auto.
  inversion H; inversion H0. subst y y0 n m. f_equal. apply IH with (0,x); auto. unfold pair_lt; simpl. rewrite <- plus_n_O; auto. inversion H; inversion H0. subst x0 y0 x1 y1 n m. f_equal. apply IH with (S x, y); auto. unfold pair_lt; simpl. rewrite <- plus_n_Sm; auto. Qed.
Definition pairn x y: nat := div' ((x+y)*(S(x+y))) 2 + y.
Theorem pairn_spec: forall x y, Pairing x y (pairn x y). Proof. intros. remember (x,y) as p. replace x with (fst p); [|subst p]; auto. replace y with (snd p); [|subst p]; auto. clear Heqp x y. revert p. apply (Fix wf_pair_lt). intros p IH. destruct p as [x y]. simpl. destruct y; [destruct x|]; simpl; auto. replace (pairn (S x) 0) with (S (pairn 0 x)). apply PairingX. apply (IH (0,x)). unfold pair_lt; simpl. rewrite <- plus_n_O; auto.
  unfold pairn. repeat rewrite <- plus_n_O. simpl. rewrite plus_n_Sm. rewrite div'_plus_mult; auto. f_equal. simpl. rewrite plus_comm. simpl. f_equal. f_equal. rewrite <- mult_plus_distr_l. symmetry. rewrite plus_comm. rewrite mult_n_Sm. f_equal; auto. replace (pairn x (S y)) with (S(pairn (S x) y)). apply PairingY. apply (IH (S x,y)). unfold pair_lt; simpl. rewrite <- plus_n_Sm; auto. unfold pairn. rewrite <- plus_n_Sm. f_equal. f_equal. f_equal. f_equal. rewrite <- plus_n_Sm; auto. f_equal. rewrite <- plus_n_Sm; auto. Qed.
Hint Resolve Pairing_unique pairn_spec.
Theorem pairn_le: forall x y, x+y <= pairn x y. Proof. intros. unfold pairn. apply plus_le_compat_r. apply le_trans with (div' (x*2) 2). rewrite div'_mult_self; auto. apply div'_le. destruct (nat_eq_dec x 0). subst x; auto. apply le_trans with ((x+y)*2). apply mult_le_compat_r; auto. apply mult_le_compat_l. apply le_n_S. destruct x. contradict n; auto. apply le_n_S; auto. Qed.
Theorem pairn_le_x: forall x y, x <= pairn x y. Proof. intros. apply le_trans with (x+y); auto. apply pairn_le. Qed.
Theorem pairn_le_y: forall x y, y <= pairn x y. Proof. intros. apply le_trans with (x+y); auto. apply pairn_le. Qed.
Hint Resolve  pairn_le pairn_le_x pairn_le_y.

Definition unpair_p (n:nat): nat. refine (match maxP (fun m=>div' (m*S m) 2<=n) _ (n:=S n) with |inleft (exist _ p _) => p |inright _ => _ end). intros. apply le_dec. absurd (div' (0*S 0) 2<=n); auto. Defined.
Lemma unpair_p_spec: forall n, MaxP (fun m=>div' (m*S m) 2<=n) (unpair_p n). Proof. intros. unfold unpair_p. destruct (maxP (fun m=>div' (m*S m) 2<=n)) as [[m H]|H]. apply H. intros. apply lt_not_le. apply le_trans with x; auto. destruct (nat_eq_dec x 0). subst x; inversion H0. apply le_trans with (div' (x*2) 2). rewrite div'_mult_self; auto. apply div'_le. apply mult_le_compat_l. destruct x; auto. absurd (div' (0*S 0) 2<=n); auto. Qed.
Definition sndn (n:nat) := n - div' (unpair_p n*S (unpair_p n)) 2.
Definition fstn (n:nat) := unpair_p n - sndn n.
Theorem pairn_id: forall n, pairn (fstn n) (sndn n) = n. Proof. intros. assert (MaxP (fun m=>div' (m*S m) 2<=n) (unpair_p n)). apply unpair_p_spec. unfold fstn. unfold pairn. replace (unpair_p n- sndn n+sndn n) with (unpair_p n). unfold sndn. rewrite <- le_plus_minus; auto. inversion H; auto. rewrite plus_comm. rewrite <- le_plus_minus; auto.
  unfold sndn. inversion H. subst n0. clear H. destruct (le_lt_dec (n-div' (unpair_p n*S(unpair_p n)) 2) (unpair_p n)); auto. absurd (S (unpair_p n)<=unpair_p n); auto. apply H1. replace (S(unpair_p n)*S(S(unpair_p n))) with (unpair_p n*S(unpair_p n)+(S(unpair_p n))*2). rewrite <- div'_plus_mult; auto. replace n with (div' (unpair_p n*S(unpair_p n)) 2+(n-div' (unpair_p n*S(unpair_p n)) 2)) at 4. apply plus_le_compat_l; auto. rewrite <- le_plus_minus; auto. rewrite mult_comm. rewrite <- mult_plus_distr_l. f_equal. rewrite plus_comm; auto. Qed.
Theorem unpair_p_id: forall x y, unpair_p (pairn x y) = x+y. Proof. intros. unfold pairn. assert (MaxP (fun m=>div' (m*S m) 2 <= (div' ((x+y)*S(x+y)) 2 + y)) (unpair_p (div' ((x+y)*S (x+y)) 2+y))). apply unpair_p_spec. inversion H. subst n. apply le_antisym; auto. destruct (le_lt_dec (unpair_p (div' ((x+y)*S(x+y)) 2 +y)) (x+y)); auto. contradict H0. apply lt_not_le. apply lt_le_trans with (div' ((S(x+y))*S (S(x+y))) 2). replace (S (x+y)*S (S(x+y))) with ((x+y)*S(x+y)+(S(x+y))*2). rewrite <- div'_plus_mult; auto. rewrite <- plus_n_Sm. apply le_n_S. apply plus_le_compat_l; auto. rewrite mult_comm. rewrite <- mult_plus_distr_l. f_equal. rewrite plus_comm; auto. apply div'_le. apply le_trans with (unpair_p (div' ((x+y)*S(x+y)) 2 +y)*S(S(x+y))). apply mult_le_compat_r; auto. apply mult_le_compat_l; auto. Qed.
Theorem sndn_id: forall x y, sndn (pairn x y) = y. Proof. intros. unfold sndn. rewrite unpair_p_id. unfold pairn. rewrite minus_plus; auto. Qed.
Theorem fstn_id: forall x y, fstn (pairn x y) = x. Proof. intros. unfold fstn. rewrite unpair_p_id. rewrite sndn_id. rewrite plus_comm. rewrite minus_plus; auto. Qed.
Hint Resolve pairn_id unpair_p_id sndn_id fstn_id.

Theorem pairn_injective1: forall x y x' y', pairn x y = pairn x' y' -> x=x'. Proof. intros. replace x with (fstn (pairn x y)); auto. replace x' with (fstn (pairn x' y')); auto. Qed.
Theorem pairn_injective2: forall x y x' y', pairn x y = pairn x' y' -> y=y'. Proof. intros. replace y with (sndn (pairn x y)); auto. replace y' with (sndn (pairn x' y')); auto. Qed.
Hint Resolve pairn_injective1 pairn_injective2.

Theorem PR2_pairn : PR2 pairn. Proof. unfold pairn. apply PR2_Comp2 with plus (fun x y=>div' ((x+y)*S(x+y)) 2) (fun _ y=>y); auto. apply PR2_Comp2 with div' (fun x y=>(x+y)*S(x+y)) (fun _ _=>2); auto. apply PR2_Comp2 with mult plus (fun x y=>S(x+y)); auto. apply PR2_Comp1 with S plus; auto. Qed.
Theorem PR1_unpair_p: PR1 unpair_p. Proof. destruct PR2_maxP with (P:=fun m n=>div' (m*S m) 2<=n) as [f [H1 H2]]. apply PRP2_Comp2; auto. apply PR2_Comp2 with div' (fun x _=>x*S x) (fun _ _=>2); auto. apply PR2_Comp2 with mult (fun x _=>x) (fun x _=>S x); auto. apply PR2_Comp1 with S (fun x _=>x); auto. apply PR1_Comp1 with pred (fun n=> (f (S n) n)); auto. apply PR1_Comp2 with f S id; auto. intros n. destruct (H2 (S n) n) as [H3 [H4 H5]]. remember (f (S n) n) as x. destruct x. absurd (div' (0*S 0) 2 <= n); auto. simpl. destruct (H5 x); auto. assert (MaxP (fun m=>div' (m*S m) 2<=n) (unpair_p n)). apply unpair_p_spec. inversion H6. subst n0. clear H6.
  apply le_antisym; auto. apply H0; auto. apply le_n_S. replace n with (pairn (fstn n) (sndn n)); auto. rewrite unpair_p_id; auto. Qed.
Hint Resolve PR2_pairn PR1_unpair_p.
Theorem PR1_sndn: PR1 sndn. Proof. unfold sndn. apply PR1_Comp2 with minus id (fun n=>div' (unpair_p n*S(unpair_p n)) 2); auto. apply PR1_Comp2 with div' (fun n=>unpair_p n*S(unpair_p n)) (fun _=>2); auto. apply PR1_Comp2 with mult unpair_p (fun n=>S (unpair_p n)); auto. apply PR1_Comp1 with S unpair_p; auto. Qed.
Theorem PR1_fstn: PR1 fstn. Proof. unfold fstn. apply PR1_Comp2 with minus unpair_p sndn; auto. apply PR1_sndn. Qed.
Hint Resolve PR1_fstn PR1_sndn.

(* list encode : (length, (0-th element, (1-st element, (2nd element, ...)))) *)
Fixpoint list_encode' (l:list nat) : nat := match l with |nil =>0 (* dummy *) |n::l' => match l' with nil => n |_::_ => pairn n (list_encode' l') end end.
Lemma list_encode'_injective: forall l m, length l=length m -> list_encode' l=list_encode' m -> l=m. Proof. induction l; intros. destruct m; auto. inversion H. destruct m. inversion H. inversion H. simpl in H0. destruct l. destruct m. subst n; auto. inversion H2. destruct m. inversion H2. f_equal. apply pairn_injective1 in H0; auto.  apply IHl; auto. apply pairn_injective2 in H0; auto. Qed.
Definition list_encode (l:list nat) : nat := pairn (length l) (list_encode' l).
Theorem list_encode_injective: forall l m, list_encode l = list_encode m -> l=m. Proof. unfold list_encode. intros. apply list_encode'_injective. apply pairn_injective1 in H; auto. apply pairn_injective2 in H; auto. Qed.

Fixpoint list_decode' (l n:nat) : list nat := match l with |O => nil |S l' => match l' with |O => n::nil |S _=> let (x,y):=unpair n in x::list_decode' l' y end end.
Lemma list_decode'_length: forall l n, length (list_decode' l n) = l. Proof. induction l; intros; simpl; auto. destruct l; auto. destruct (unpair n). simpl. f_equal; apply IHl; auto. Qed.
Lemma list_decode'_spec: forall l n, l<>0 -> list_encode' (list_decode' l n) = n. Proof. induction l; intros. contradict H; auto. simpl. clear H. destruct l; auto. remember (unpair n) as p. destruct p as [x y]. remember (list_decode' (S l) y) as d. simpl. destruct d. absurd (0=S l); auto. replace 0 with (length (A:=nat) nil); auto. rewrite Heqd. apply list_decode'_length. rewrite <- unpair_pair_id. f_equal. rewrite <- Heqp. f_equal. rewrite Heqd. auto. Qed.
Definition list_decode_sig : forall n, {l|list_encode l=n}+{forall l, list_encode l <> n}. refine (fun n=>if nat_eq_dec (fst (unpair n)) 0 then if nat_eq_dec (snd (unpair n)) 0 then inleft (exist _ nil _) else inright _ else inleft (exist _ (list_decode' (fst (unpair n)) (snd (unpair n))) _)). unfold list_encode. simpl. rewrite <- unpair_pair_id. f_equal. destruct (unpair n). simpl in e. simpl in e0; auto.
  intros. contradict n0. unfold list_encode in n0. assert (unpair n =(length l,list_encode' l)).  rewrite <- n0. rewrite pair_unpair_id; auto. rewrite H in e. simpl in e. destruct l. rewrite H. simpl; auto. inversion e. remember (unpair n) as p. destruct p as [x y]. simpl. unfold list_encode. rewrite <- unpair_pair_id. rewrite <- Heqp. f_equal. f_equal. apply list_decode'_length. apply list_decode'_spec; auto. Defined.

(* Godel function for each type *)
Inductive Godel_f : Func -> nat -> Prop :=
|Gf_FZero: Godel_f FZero 0
|Gf_FSucc: Godel_f FSucc 1
|Gf_FProj: forall n, Godel_f (FProj n) (pairn 2 n)
|Gf_FComp: forall f n l ns, Godel_f f n -> MapR Godel_f l ns -> Godel_f (FComp f l) (pairn 3 (pairn n (list_encode ns)))
|Gf_FRecu: forall f g n m, Godel_f f n -> Godel_f g m -> Godel_f (FRecu f g) (pairn 4 (pairn n m))
.
Hint Constructors Godel_f.
Definition godel_f_sig: forall f, {n|Godel_f f n & forall g, Godel_f g n -> g=f}. apply (Fix (well_founded_ltof Func funcDepth)). intros f IH. destruct f. exists 0; auto. intros. inversion H; auto. absurd (2<=0); auto. rewrite <- H2 at 2; auto. absurd (3<=0); auto. rewrite <- H0 at 2; auto. absurd (4<=0); auto. rewrite <- H0 at 2; auto. exists 1; auto. intros. inversion H; auto. absurd (2<=1); auto. rewrite <- H2 at 2; auto. absurd (3<=1); auto. rewrite <- H0 at 2; auto. absurd (4<=1); auto. rewrite <- H0 at 2; auto.
  exists (pairn 2 n); auto. intros. inversion H. absurd (2<=0); auto. rewrite H2 at 2; auto. absurd (2<=1); auto. rewrite H2 at 2; auto. f_equal. apply pairn_injective2 in H2; auto. apply pairn_injective1 in H0. contradict H0; auto. apply pairn_injective1 in H0. contradict H0; auto. destruct (IH f) as [n H H0]. unfold ltof. simpl; auto. destruct MapR_build2 with (l:=l) (R1:=fun f n=>Godel_f f n) (R2:=fun f n=>forall g, Godel_f g n->g=f) as [ns H1]. intros. apply IH. unfold ltof. simpl. apply le_n_S. apply le_trans with (maxl (map funcDepth l)); auto. apply maxl_le. apply in_map_iff. exists x; auto.
  exists (pairn 3 (pairn n (list_encode ns))). apply Gf_FComp; auto. eapply MapR_trans; [|eapply H1]. intros. destruct H4; auto. intros. inversion H2. absurd (3<=0); auto. rewrite H5 at 2; auto. absurd (3<=1); auto. rewrite H5 at 2; auto. apply pairn_injective1 in H5. contradict H5; auto. apply pairn_injective2 in H3. assert (n0=n). apply pairn_injective1 in H3; auto. subst n0. apply pairn_injective2 in H3. f_equal; auto. apply list_encode_injective in H3. subst ns0. clear -H1 H6. revert H6. revert l0. induction H1; intros. inversion H6; auto. destruct H. inversion H6. subst l0 b0 m0. f_equal. apply H0; auto. apply IHMapR; auto. apply pairn_injective1 in H3. contradict H3; auto.
  destruct (IH f1) as [n H H0]. unfold ltof; simpl; auto. destruct (IH f2) as [m H1 H2]. unfold ltof; simpl; auto. exists (pairn 4 (pairn n m)); auto. intros. inversion H3. absurd (4<=0); auto. rewrite H6 at 2; auto. absurd (4<=1); auto. rewrite H6 at 2; auto. apply pairn_injective1 in H6. contradict H6; auto. apply pairn_injective1 in H4. contradict H4; auto. apply pairn_injective2 in H4. apply pairing_injective in H4. inversion H4. subst n0 m0. f_equal; auto. Defined.
Definition godel_f (f:Func):nat := match godel_f_sig f with exist2 _ _ n _ _ => n end.
Definition godel_f_rev: forall n, {f|Godel_f f n}+{forall f,~Godel_f f n}. intros. destruct (le_lt_dec 2 n). remember (unpair n) as p. destruct p as [x y]. destruct (nat_eq_dec x 2). subst x. replace n with (pairn 2 y). left; exists (FProj y); auto. unfold pairn. rewrite Heqp; auto. destruct (nat_eq_dec x 3). subst x. remember (unpair y) as p. destruct p as [z w].

Inductive GSource : Set :=
|GS_T: Term -> GSource
|GS_F: Formula -> GSource
|GS_LT: list Term -> GSource
|GS_LF: list Formula -> GSource
.

Variable godel_t : Term -> nat.
Variable godel_f : Formula -> nat.
Hypothesis godel_t_unique: forall s t, godel_t s = godel_t t -> s = t.
Hypothesis godel_f_unique: forall f g, godel_f f = godel_f g -> f = g.
Hypothesis godel_t_odd: forall t, ~Divide 2 (godel_t t).
Hypothesis godel_f_odd: forall f, ~Divide 2 (godel_f f).
Variable godel_l : list nat -> nat.
Hypothe

Definition godel (gs:GSource) : nat := match gs with
| GS_T t => godel_t t
| GS_F f => 2*godel_f f
| GS_LT l => 4*godel_l (map godel_t l)
| GS_LF l => 8*godel_l (map godel_f l)
end.


Definition t2g (t:Term) := godel (GS_T t).
Definition f2t (f:Formula) := godel (GS_F f).