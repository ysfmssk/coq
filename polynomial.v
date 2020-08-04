Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import ModEq.

Set Implicit Arguments.

Inductive poly: Set :=
| polyHead: nat -> poly
| polyCons: nat -> poly -> poly.

Fixpoint polyOrder f:= match f with |polyHead _ => 0 |polyCons _ p => S(polyOrder p) end.
Fixpoint polyEval f n :=match f with |polyHead c => c |polyCons c p => c+n*polyEval p n end.
Fixpoint polyPlus f g := match f with |polyHead c => match g with |polyHead d => polyHead (c+d) |polyCons d g' => polyCons (c+d) g' end
                                      |polyCons c f' => match g with |polyHead d => polyCons (c+d) f' |polyCons d g' => polyCons (c+d) (polyPlus f' g') end end.
Fixpoint polyMultC f a := match f with |polyHead c => polyHead (a*c) |polyCons c f' => polyCons (a*c) (polyMultC f' a) end.
Fixpoint polyMult f g := match f with |polyHead c => polyMultC g c |polyCons c f' => polyPlus (polyMultC g c) (polyCons 0 (polyMult f' g)) end.
Fixpoint polyTop f := match f with |polyHead c => c |polyCons _ f' => polyTop f' end.
Theorem polyEval_plus: forall f g n, polyEval (polyPlus f g) n = polyEval f n + polyEval g n. Proof. induction f; simpl; intros. destruct g; simpl; auto. destruct g; simpl; auto. repeat rewrite <- plus_assoc; auto. repeat rewrite <- plus_assoc. f_equal. symmetry. rewrite plus_comm. repeat rewrite <- plus_assoc. f_equal. rewrite <- mult_plus_distr_l. f_equal; auto. rewrite IHf;  auto. Qed.
Theorem polyEval_multc: forall f c n, polyEval (polyMultC f c) n = c*polyEval f n. Proof. induction f; simpl; intros; auto. rewrite mult_plus_distr_l. f_equal. symmetry. rewrite mult_comm. rewrite <- mult_assoc. f_equal. rewrite IHf; auto. Qed.
Theorem polyEval_mult: forall f g n, polyEval (polyMult f g) n = polyEval f n * polyEval g n. Proof. induction f; simpl; intros. rewrite polyEval_multc; auto. rewrite polyEval_plus. simpl. rewrite polyEval_multc. rewrite mult_plus_distr_r. f_equal. rewrite <- mult_assoc. f_equal. auto. Qed.
Theorem polyOrder_plus: forall f g, polyOrder (polyPlus f g) = max (polyOrder f) (polyOrder g). Proof. induction f. intros g. destruct g; simpl; auto. intros. destruct g; simpl; auto. Qed.
Theorem polyOrder_multc: forall f c, polyOrder (polyMultC f c) = polyOrder f. Proof. induction f; intros; simpl; auto. Qed.
Theorem polyOrder_mult: forall f g, polyOrder (polyMult f g) = polyOrder f + polyOrder g. Proof. induction f; intros; simpl; auto. apply polyOrder_multc. rewrite polyOrder_plus; simpl. rewrite  Nat.max_r; auto. rewrite polyOrder_multc. rewrite IHf. auto. Qed.
Theorem polyTop_mult: forall f g, polyTop (polyMult f g) = polyTop f * polyTop g. Proof. induction f; simpl; intros. revert n. induction g; simpl; intros; auto. simpl. cut (forall f g, polyOrder f < polyOrder g -> polyTop (polyPlus f g) = polyTop g). intros. rewrite H.  simpl; auto.
  rewrite polyOrder_multc. simpl. rewrite polyOrder_mult. auto. clear IHf f g. intros f g. revert g. induction f; simpl; intros. destruct g. inversion H. simpl; auto. destruct g. inversion H. simpl in H. simpl. apply IHf; auto. Qed.
Theorem polyPlus_assoc: forall  f g h, polyPlus f (polyPlus g h) = polyPlus (polyPlus f g) h. Proof. induction f; simpl; induction g; simpl; auto; destruct h; simpl; auto; try rewrite plus_assoc; auto. f_equal. auto. Qed.
Theorem polyPlus_comm: forall f g, polyPlus f g = polyPlus g f. Proof. induction f; destruct g; simpl; auto; try rewrite plus_comm; auto. f_equal; auto. Qed.

Theorem poly_ModEq: forall n a b f, ModEq n a b -> ModEq n (polyEval f a) (polyEval f b). Proof. induction f; simpl; intros; auto. Qed.

Hint Resolve polyEval_plus polyEval_multc polyEval_mult polyOrder_plus polyOrder_multc polyOrder_mult polyTop_mult polyPlus_assoc polyPlus_comm.
Inductive ModEq_poly (n:nat) : relation poly :=
|MEp_Head: forall a b, ModEq n a b -> ModEq_poly n (polyHead a) (polyHead b)
|MEp_cons: forall a b f g, ModEq n a b -> ModEq_poly n f g -> ModEq_poly n (polyCons a f) (polyCons b g)
.

Hint Constructors ModEq_poly.

Theorem ModEq_poly_refl: forall n f, ModEq_poly n f f. Proof. induction f; auto. Qed.
Theorem ModEq_poly_order: forall n f g, ModEq_poly n f g -> polyOrder f = polyOrder g. Proof. intros. induction H; simpl; auto. Qed.
Theorem ModEq_poly_top: forall n f g, ModEq_poly n f g -> ModEq n (polyTop f) (polyTop g). Proof. intros. induction H; simpl; auto. Qed.
Theorem ModEq_poly_plus: forall n f g h i, ModEq_poly n f g -> ModEq_poly n h i -> ModEq_poly n (polyPlus f h) (polyPlus g i). Proof. intros n f g h i H. revert h i. induction H; simpl; intros; auto. inversion H0; simpl; auto. inversion H1; simpl; auto. Qed.
Theorem ModEq_poly_trans: forall n f g h, ModEq_poly n f g -> ModEq_poly n g h -> ModEq_poly n f h. Proof. intros. revert h H0. induction H; simpl; intros; auto. inversion H0. cut (ModEq n a b0); auto. apply ModEq_trans with b; auto. inversion H1. apply MEp_cons; auto. apply ModEq_trans with b; auto. Qed.
Definition modNeg_sig: forall n m, {x| ModEq n (x+m) 0}+{n=0}. intros. destruct (divmod n m) as [[q [r [H1 H2] _]]|H1]; [left|right]; auto. subst. exists (n-r). rewrite plus_comm. rewrite <- plus_assoc. rewrite <- le_plus_minus; auto.  apply ModEq_sym; apply Divide_plus; auto. Defined.
Definition modNeg n (nz:n<>0) m := match modNeg_sig n m with |inleft (exist _ x _)=> x |inright _ H => False_rec nat (nz H) end.
Theorem modNeg_spec: forall n (nz:n<>0) a, Divide n (modNeg nz a+a). Proof. intros. unfold modNeg. destruct (modNeg_sig n a). destruct s; unfold Divide; auto. contradiction. Qed.
Theorem modNeg_dual: forall n (nz:n<>0) a, ModEq n a (modNeg nz (modNeg nz a)). Proof. intros. apply ModEq_minus with (modNeg nz a). apply ModEq_trans with 0. apply ModEq_sym. apply modNeg_spec. rewrite plus_comm. apply modNeg_spec. Qed.
Theorem ModEq_poly_ModEq: forall n f g x, ModEq_poly n f g -> ModEq n (polyEval f x) (polyEval g x). Proof. intros. induction H; simpl; auto. Qed.
Definition poly_div: forall n (nz:n<>0) f a,  {g| ModEq_poly n (polyPlus (polyMult (polyCons a (polyHead 1)) g) (polyHead (polyEval f (modNeg nz a)))) f & polyTop g=polyTop f}+{polyOrder f=0}. intros. revert f. apply (Fix (well_founded_ltof poly polyOrder)). intros f IH. destruct f as [c|c f]; [right|left]; auto. destruct (IH f) as [[g H H1]|H]. unfold ltof; auto. exists (polyCons (polyEval f (modNeg nz a)) g). simpl. apply MEp_cons; auto. unfold modNeg. unfold modNeg in H. destruct (modNeg_sig n a) as [[b H2]|H2]; [|contradiction]. rewrite <- plus_n_O. rewrite plus_comm. rewrite <- plus_assoc. replace c with (c+0) at 2; auto. apply ModEq_plus; auto. rewrite <- mult_plus_distr_r. replace 0 with (0*polyEval f b); auto. rewrite <-plus_n_O. simpl in H. rewrite <- polyPlus_assoc in H. simpl in H. auto. simpl; auto.
  destruct f as [d|d f]; [|inversion H]. exists (polyHead d); auto. simpl. repeat rewrite <- plus_n_O. apply MEp_cons; auto. rewrite plus_comm. rewrite <- plus_assoc. replace c with (c+0) at 2; auto. apply ModEq_plus; auto. rewrite <- mult_plus_distr_r. replace 0 with (0*d); auto. apply ModEq_mult; auto. unfold modNeg. destruct (modNeg_sig n a) as [[b H1]|H1]; auto; contradiction. Defined.
Hint Resolve ModEq_poly_refl ModEq_poly_order ModEq_poly_top ModEq_poly_plus ModEq_poly_trans modNeg_spec modNeg_dual ModEq_poly_ModEq.

Definition poly_divide: forall n (nz:n<>0) f m, ~Divide n (polyTop f) -> Divide n (polyEval f m) -> {g| ModEq_poly n (polyMult (polyCons (modNeg nz m) (polyHead 1)) g) f & polyTop g = polyTop f}. intros. destruct (poly_div nz f (modNeg nz m)) as [[g H1 H2]|H1]. exists g; auto. remember (polyMult (polyCons (modNeg nz m) (polyHead 1)) g) as h. eapply ModEq_poly_trans; [|eapply H1]. assert (Divide n (polyEval f (modNeg nz (modNeg nz m)))). apply ModEq_trans with (polyEval f m); auto. apply poly_ModEq. auto. replace h with (polyPlus h (polyHead 0)) at 1; auto. destruct h; simpl; rewrite <- plus_n_O; auto. destruct f; [|inversion H1]. simpl in H. simpl in H0. contradiction. Defined.
Theorem poly_root_num: forall p f m, Prime p -> ~Divide p (polyTop f) -> PnumN (fun x=> Divide p (polyEval f x)) p m -> m<=polyOrder f. Proof. intros p f m Hp. revert m. apply (Fix (well_founded_ltof poly polyOrder)) with (P:=fun f=>forall m, ~Divide p (polyTop f) -> PnumN (fun x=>Divide p (polyEval f x)) p m -> m<=polyOrder f). clear f. intros f IH m H H0.
  destruct (nat_eq_dec m 0) as [Hm|Hm]. subst m; auto. destruct (PnumN_ex H0). clear H2. destruct H1 as [x [H2 H3]]; auto. assert (nz:p<>0). contradict Hp; subst p; auto. apply poly_divide with p nz f x in H3; auto. destruct H3 as [g H3 Ht]. destruct pnumN with (P:=fun x=>Divide p (polyEval g x)) (n:=p) as [m' H4]; auto. intros. apply Divide_dec. assert (m'<=polyOrder g). apply IH; auto. unfold ltof. apply ModEq_poly_order in H3. rewrite <- H3. rewrite polyOrder_mult. simpl; auto. apply ModEq_poly_top in H3. rewrite polyTop_mult in H3. simpl in H3. rewrite <- plus_n_O in H3. contradict H. apply ModEq_trans with (polyTop g); auto.
  assert (polyOrder f=S (polyOrder g)). apply ModEq_poly_order in H3. rewrite polyOrder_mult in H3. simpl in H3. symmetry; auto. rewrite H5. apply le_n_S in H1. apply le_trans with (S m'); auto. cut (PnumN (fun y=>Divide p (polyEval (polyCons (modNeg nz x) (polyHead 1)) y)) p 1). intros. replace (S m') with (1+m'); auto. eapply PnumN_or. eapply H6. eapply H4. eapply PnumN_equiv; [|eapply H0]. intros y Hy. split; intros. apply Euclid_Prime; auto. rewrite <- polyEval_mult.  apply ModEq_poly_ModEq with (x:=y) in H3. apply ModEq_trans with (polyEval f y); auto. apply ModEq_poly_ModEq with (x:=y) in H3. rewrite polyEval_mult in H3. eapply ModEq_trans; [|eapply H3]. destruct H7; eapply Divide_trans. eapply H7. rewrite mult_comm; auto. eapply H7. auto.
  simpl. apply PnumN_one with (modN nz x); auto. rewrite mult_1_r. apply ModEq_trans with (modNeg nz x+x); auto. apply modNeg_spec. intros. rewrite <- modN_le_eq with p nz y; auto. apply ModEq__modN_eq. apply ModEq_minus with (modNeg nz x). rewrite mult_1_r in H7. apply ModEq_trans with 0; auto. apply modNeg_spec. Qed.





