Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import ModEq.

Set Implicit Arguments.

Theorem Willson1: forall p, Prime p -> ModEq p (fact (p-1)) (p-1). Proof. intros. destruct (le_lt_dec p 2) as [H0|H0]. replace p with 2; simpl; auto. apply le_antisym; auto. assert (Hp:p<>0). contradict H; subst p; auto. rewrite fact_fold. remember (p-1) as t. assert (Ht: p=S t). destruct p. contradict Hp; auto. simpl in Heqt. rewrite <- minus_n_O in Heqt; subst t; auto. assert (Ht1:t<p). rewrite Ht; auto. assert (Ht2:Coprime p t). destruct (Prime_Coprime_Divide t H); auto. apply Divide_le in H1. contradict Ht1; auto. contradict H. rewrite Ht. rewrite H. auto. remember (t-2) as u. assert (Hu:t=S(S u)). subst u. destruct t. subst p; contradict H0; auto. simpl. destruct t. contradict H0; subst p; auto. simpl. rewrite <- minus_n_O; auto. rewrite Hu at 1. rewrite seqS. simpl. rewrite <- plus_n_O. rewrite fold_mult_app. simpl. rewrite mult_1_r. rewrite <- Hu. replace t with (1*t) at 2; auto. apply ModEq_mult; auto.
  destruct (Rpair_list) with (l:=seq 2 u) (R:=fun x y=>ModEq p (x*y) 1) as [l [H1 H2]]; simpl; intros; auto. intros C. apply in_seq in H1. destruct H1. absurd (x=1). contradict H1; subst x; auto. rewrite <- modN_le_eq with p Hp x. rewrite <- modN_le_eq with p Hp 1; auto. apply ModEq__modN_eq. apply ModEq_div with (1+x); auto. destruct (Prime_Coprime_Divide (1+x) H); auto. simpl in H3. apply Divide_le in H3; auto. contradict H2. simpl. rewrite <- Hu. apply le_not_lt. apply le_S_n. rewrite <- Ht; auto. rewrite mult_1_r. rewrite mult_plus_distr_r. rewrite mult_1_l. rewrite plus_comm. auto. simpl in H2. rewrite <- Hu in H2. apply lt_le_trans with t; auto.
  apply in_seq in H1. destruct H1. simpl in H2. rewrite <- Hu in H2. assert (Hx:x<p). rewrite Ht; auto. assert (Hxz:x<>0). contradict H1; subst x; auto. assert (Hc:Coprime p x). destruct (Prime_Coprime_Divide x H); auto. apply Divide_le in H3; auto. contradict Hx; auto. destruct ModInv with (n:=p) (a:=x) as [y [H3 H4]]; auto. exists (modN Hp y). split. apply ModEq_trans with (x*y); auto. split. apply in_seq. split. destruct (le_lt_dec 2 (modN Hp y)); auto. inversion l. assert (ModEq p x 1). replace x with (x*modN Hp y). apply ModEq_trans with (x*y); auto. rewrite H6. rewrite mult_1_r; auto. apply ModEq__modN_eq with p Hp x 1 in H5. rewrite modN_le_eq in H5; auto. rewrite modN_le_eq in H5; auto. contradict H1; subst x; auto. inversion H6. assert (ModEq p 0 1). apply ModEq_trans with (x*y); auto. replace 0 with (x*modN Hp y); auto. rewrite H8; auto. absurd (0=1); auto. apply ModEq__modN_eq with p Hp 0 1 in H7. rewrite modN_le_eq with p Hp 1 in H7; auto. rewrite modN_le_eq with p Hp 0 in H7; auto. inversion H8. simpl. rewrite <- Hu. assert (modN Hp y<p). auto. rewrite Ht in H5. apply le_S_n in H5. destruct (le_lt_or_eq (modN Hp y) t H5); auto. contradict H2. replace x with t; auto. cut (ModEq p t x). intros. apply ModEq__modN_eq with p Hp t x in H2. rewrite modN_le_eq in H2; auto. rewrite modN_le_eq in H2; auto.
  destruct (ModInv) with (n:=p) (a:=t) as [z [H7 H8]]; auto. contradict H0. rewrite Ht. rewrite H0. auto. apply ModEq_trans with z. apply ModEq_sym; apply H8. rewrite Ht. apply ModEq_m1_sq. apply H8. rewrite <- H6. apply ModEq_trans with (y*x); auto. rewrite mult_comm; auto. intros. rewrite <- modN_le_eq with p Hp z. apply ModEq__modN_eq; auto. apply in_seq in H5. destruct H5. apply lt_le_trans with (2+u); auto. simpl. rewrite <- Hu; auto. 
 rewrite mult_comm; auto. rewrite fold_right_Perm with (m:=map fst l++map snd l); auto. clear -H2. induction l as [|[a b] l]; simpl; auto. rewrite fold_right_Perm with (m:=b::map fst l++map snd l); auto. simpl. rewrite mult_assoc. inversion H2.  replace 1 with (1*1); auto. Qed.
Theorem Willson2: forall n, 2<=n -> ModEq n (fact (n-1)) (n-1) -> Prime n. Proof. intros. destruct (primeDivide n) as [[p H1 H2]|H1]; [|contradict H; auto]. assert (p<=n). apply Divide_le; auto. contradict H; subst n; auto. destruct (le_lt_or_eq p n H3). absurd (Divide p (fact (n-1)+1)). intros C. apply Divide_minus in C. apply Divide_le in C; auto. contradict C; auto. apply fact_Divide. apply le_S_n. destruct n; simpl; auto. rewrite <- minus_n_O; auto. contradict H1; subst p; auto. apply Divide_trans with n; auto. apply ModEq_trans with n; auto. replace n with (1*n+0) at 2; auto. simpl. repeat rewrite <- plus_n_O. auto. replace n with (n-1+1) at 2; auto. destruct n; simpl; auto. rewrite <- minus_n_O. rewrite plus_comm; auto. subst p; auto. Qed.

Inductive ModOrder (n:nat): relation nat := ModOrder_intro: forall a k, Coprime n a -> MinP (fun x=>x<>0 /\ ModEq n (pow a x) 1) k -> ModOrder n a k.
Hint Constructors ModOrder.

Definition modOrder: forall n a, Coprime n a -> {k|ModOrder n a k}. intros. destruct (nat_eq_dec n 0) as [Hn|Hn]. subst n. assert (a=1). apply GCD_unique with 0 a; auto. destruct (nat_eq_dec a 0); auto. subst a; contradict H; unfold Coprime; auto. subst a. exists 1. apply ModOrder_intro; auto. apply MinP_intro; auto. intros. destruct H0. destruct m; auto.
  destruct (minP) with (P:=fun x=>x<>0/\ModEq n (pow a x) 1) (n:=S(totient n)).  intros. destruct (ModEq_dec n (pow a x) 1); [|right]. destruct (nat_eq_dec x 0); [right|left]; auto. contradict e; destruct e; auto. contradict n0; destruct n0; auto. destruct s as [m H1]. exists m. apply ModOrder_intro; auto. unfold totient in n0. destruct (totient_sig n) as [t Ht]. absurd (t<>0/\ModEq n (pow a t) 1); auto. split. apply Totient_nz with n; auto. apply Euler; auto. Defined.
Theorem ModOrder_nz: forall n a k, ModOrder n a k -> k<>0. Proof. intros. inversion H. inversion H1. destruct H4; auto. Qed.
Theorem ModOrder_unique: forall n a k j, ModOrder n a k -> ModOrder n a j -> k=j. Proof. intros. inversion H. inversion H0. inversion H2. inversion H6. apply le_antisym; auto. Qed.
Theorem ModOrder_Divide: forall n a k d, ModOrder n a k -> Divide k d <-> ModEq n (pow a d) 1. Proof. intros. split; intros. destruct (Divide_multN H0). subst d. rewrite pow_mult. clear H0. inversion H. inversion H1. destruct H4. clear -H7. induction x; simpl; auto. replace 1 with (1*1); auto. inversion H. subst a0 k0. inversion H2. subst n0. destruct H3. destruct (divmod k d) as [[q [r [H6 H7] _]]|];[|contradiction]. subst d. destruct (nat_eq_dec r 0). subst r. rewrite <- plus_n_O. auto. rewrite pow_plus in H0. rewrite pow_mult in H0.
  absurd (k<=r); auto. apply H4. split; auto. clear -H0 H1 H5. induction q. simpl in H0. rewrite <- plus_n_O in H0; auto. apply IHq. simpl in H0. apply ModEq_div with (pow a k). clear -H1. induction k; simpl; auto. rewrite mult_assoc. rewrite mult_1_r. apply ModEq_trans with 1; auto. Qed.
Theorem ModOrder_Totient: forall n a k t, ModOrder n a k -> Totient n t -> Divide k t. Proof. intros. destruct ModOrder_Divide with n a k t; auto. apply H2. apply Euler; auto. inversion H; auto. Qed.
Theorem ModOrder_pow: forall n a k, ModOrder n a k -> forall x y, ModEq n (pow a x) (pow a y) <-> ModEq k x y. Proof. intros n a k H. cut (forall x y, x<=y->ModEq n (pow a x) (pow a y) <-> ModEq k x y). intros. destruct (le_lt_dec x y); auto. split; intros. apply ModEq_sym. apply H0; auto. apply ModEq_sym. apply H0; auto. intros. replace y with (x+(y-x)); [|rewrite <- le_plus_minus]; auto. split; intros. cut (ModEq n (pow a (y-x)) 1). intros. destruct ModOrder_Divide with n a k (y-x); auto. replace x with (x+0) at 1; auto. apply ModEq_plus; auto. apply H4; auto.
  inversion H. revert H1. clear -H2. generalize (y-x). induction x; simpl; intros; auto. apply IHx. apply ModEq_div with a; auto. rewrite pow_plus. replace (pow a x) with (pow a x*1) at 1; [|apply mult_1_r]. apply ModEq_mult; auto. destruct (ModOrder_Divide) with n a k (y-x); auto. apply ModEq_sym. apply H2. apply ModEq_minus with x. rewrite <- plus_n_O; auto. Qed.
Theorem ModOrder_NoDup: forall n a k (Hn:n<>0), ModOrder n a k -> NoDup (map (fun x=>modN Hn (pow a x)) (seq 0 k)). Proof. intros. apply NoDup_map; auto. intros. apply modN_eq__ModEq in H2. destruct ModOrder_pow with n a k x y; auto. apply H3 in H2. destruct (ModEq_multN H2) as [[q H5]|[q H5]]. subst y. destruct q; auto. apply in_seq in H1. destruct H1. contradict H5; auto. simpl. rewrite <- plus_assoc. auto. subst x. destruct q; auto. apply in_seq in H0. destruct H0. contradict H5. simpl. rewrite <- plus_assoc; auto. Qed.
Theorem ModOrder_ModEq: forall n a k b, ModOrder n a k -> ModEq n a b -> ModOrder n b k. Proof. intros. inversion H. subst a0 k0. apply ModOrder_intro. apply GCD_ModEq with a; auto. inversion H2. destruct H3. apply MinP_intro; auto. split; auto. apply ModEq_trans with (pow a k); auto. clear -H0. induction k; simpl; auto. intros. destruct H7. apply H4; split; auto. apply ModEq_trans with (pow b m); auto. clear -H0. induction m; simpl; auto. Qed.
Theorem ModOrder_PnumN: forall n a k, n<>0->ModOrder n a k-> PnumN (fun x=>exists k, ModEq n (pow a k) x) n k. Proof. intros. assert (Hk:k<>0). eapply ModOrder_nz; eauto. assert (P_dec: forall x, {exists m, ModEq n (pow a m) x}+{~exists m, ModEq n (pow a m) x}).  intros. destruct minP with (n:=k) (P:=fun y=>ModEq n (pow a y) x) as [[m H1]|H1]; [|left|right]. intros. destruct (ModEq_dec n (pow a x0) x); [left|right]; auto. exists m. inversion H1; auto. intros C. destruct C. absurd (ModEq n (pow a  (modN Hk x0)) x ); auto. apply ModEq_trans with (pow a x0); auto. destruct ModOrder_pow with n a k (modN Hk x0) x0; auto. replace k with (length (filter (dec2b P_dec) (seq 0 n))). apply PnumN_filter.
  replace k with (length (map (fun x=>modN H (pow a x)) (seq 0 k))). apply Perm_length. apply NoDup_incl_each_Perm; auto. apply NoDup_map; auto. intros. apply modN_eq__ModEq in H3. apply ModOrder_pow with n a k  x y in H3; auto. replace x with (modN Hk x). replace y with (modN Hk y); auto. apply modN_le_eq. apply in_seq in H2. destruct H2; auto. apply in_seq in H1. destruct H1; auto. intros x Hx. apply filter_In in Hx. destruct Hx. apply dec2b_true in H2.  destruct H2 as [m H3]. apply in_map_iff. exists (modN Hk m). split. replace x with (modN H x). apply ModEq__modN_eq. apply ModEq_trans with (pow a m); auto. destruct ModOrder_pow with n a k (modN Hk m) m; auto. apply modN_le_eq. apply in_seq in H1. destruct H1; auto. apply in_seq. split; auto.
  intros x Hx. apply in_map_iff in Hx. destruct Hx as [y [H1 H2]]. subst x. apply filter_In. split. apply in_seq. split; auto. apply dec2b_true. exists y; auto. rewrite map_length. apply seq_length; auto. Qed.
Hint Resolve ModOrder_unique ModOrder_Divide ModOrder_Totient ModOrder_pow ModOrder_ModEq ModOrder_PnumN.

Inductive ModRoot: relation nat:= ModRoot_intro: forall n g t, Totient n t -> ModOrder n g t -> ModRoot n g.
Hint Constructors ModRoot.

Theorem ModRoot_ModEq: forall n a b, ModRoot n a -> ModEq n a b -> ModRoot n b. Proof. intros. inversion H. apply ModRoot_intro with t; auto. apply ModOrder_ModEq with a; auto. Qed.
Theorem Prime_ModRoot_map: forall p g (Hp:Prime p), ModRoot p g -> Perm (seq 1 (p-1)) (map (fun x=>modN (Prime_nz Hp) (pow g x)) (seq 1 (p-1))). Proof. intros. apply Perm_sym. apply NoDup_incl_Perm. intros y Hy. apply in_map_iff in Hy. destruct Hy as [z [H1 H2]]. subst y. apply in_seq. split. cut (modN (Prime_nz Hp) (pow g z)<>0); intros. destruct (modN (Prime_nz Hp) (pow g z)); auto. intros C. replace 0 with (modN (Prime_nz Hp) 0) in C; auto. apply modN_eq__ModEq in C. inversion H. inversion H1. clear -H5 C Hp. induction z. simpl in C. apply ModEq_le_eq in C; auto. inversion C. simpl in C. apply ModEq_sym in C. apply Euclid_Prime in C; auto. destruct C; auto. absurd (p<=1); auto. inversion H5; auto. rewrite <- le_plus_minus; auto. apply NoDup_map; auto. intros. apply modN_eq__ModEq in H2. cut (forall a b, a<b -> In a (seq 1 (p-1)) -> In b (seq 1 (p-1)) -> ~ModEq p (pow g a) (pow g b)); intros. destruct (le_lt_dec x y). destruct (le_lt_or_eq x y l); auto. contradict H2; auto. apply ModEq_sym in H2; contradict H2; auto. intros C. rewrite <- mult_1_r with (n:=pow g a) in C. rewrite le_plus_minus with a b in C; auto. rewrite pow_plus in C.
  apply ModEq_div in C. inversion H. inversion H7. inversion H11. subst n g0 a0 k n0. assert (t<=b-a). apply H15; split; auto. contradict H3. apply Nat.sub_0_le in H3; auto. replace t with (p-1) in H8. apply in_seq in H4. destruct H4. apply in_seq in H5. destruct H5. contradict H8. apply lt_not_le. apply lt_le_trans with b. destruct b. inversion H5. destruct a. inversion H4. simpl. apply le_n_S. apply le_minus. auto. apply Totient_unique  with p; auto. inversion H. inversion H7. clear -Hp H10. induction a; auto. rewrite map_length; auto. Qed.
Theorem Prime_ModRoot_root: forall p g, Prime p -> ModRoot p g -> forall n, {k|ModEq p (pow g k) n & forall k', ModEq p (pow g k') n -> ModEq (p-1) k k'}+{Divide p n}. intros. destruct (Divide_dec p n) as [Hd|Hd]; [right; auto|left]. destruct findN with (P:=fun x=>x<>0/\ModEq p (pow g x) n) (n:=p) as [[y H1]|H1]. intros. simpl. destruct (nat_eq_dec x 0); [right|]; auto. contradict e. destruct e; auto. destruct (ModEq_dec p (pow g x) n); [left|right]; auto. intros C; destruct C; contradiction. destruct H1. exists y; auto. intros. apply ModOrder_pow with (k:=p-1) (x:=y) (y:=k') (n:=p) (a:=g); auto. inversion H0. replace (p-1) with t; auto. eapply Totient_unique with p; auto. apply ModEq_trans with n; auto. absurd (In (modN (Prime_nz H) n) (seq 1 (p-1))). intros C. apply Perm_In with (m:=map (fun x=>modN (Prime_nz H) (pow g x)) (seq 1 (p-1))) in C. apply in_map_iff in C. destruct C as [x [H2 H3]]. apply in_seq in H3. destruct H3. absurd (x<>0/\ModEq p (pow g x) n). apply H1. rewrite <- le_plus_minus in H4; auto. split. destruct x; auto. inversion H3. apply modN_eq__ModEq in H2; auto. apply Prime_ModRoot_map; auto. apply in_seq. split. destruct (le_lt_dec 1 (modN (Prime_nz H) n)); auto. contradict Hd. inversion l. apply modN_eq__ModEq with (Prime_nz H). rewrite modN_le_eq; auto. inversion H3. rewrite <- le_plus_minus; auto. Defined.
Theorem ModOrder_mult: forall p a b o s, Prime p -> ModOrder p a o -> ModOrder p b s -> Coprime o s -> ModOrder p (a*b) (o*s). Proof. intros. inversion H0. inversion H4. inversion H1. inversion H11. destruct H7. destruct H14. subst a0 k n a1 k0 n0. clear H0 H1 H4 H11. apply ModOrder_intro; auto. apply MinP_intro. split. intros C. apply mult_is_O in C. destruct C; contradiction. replace 1 with (1*1); auto. rewrite pow_mult2. apply ModEq_mult. rewrite mult_comm. rewrite pow_mult. clear -H17. induction s; simpl; auto. replace 1 with (1*1); auto. rewrite pow_mult. clear -H18. induction o; simpl; auto. replace 1 with (1*1); auto. intros. destruct H0.
  cut (Divide o m); intros. cut (Divide s m); intros. destruct (Divide_multN H4) as [q H6]. subst m. rewrite mult_comm in H5. apply Euclid in H5; auto. destruct (Divide_multN H5) as [r H6]. subst q. rewrite mult_comm. rewrite <- mult_assoc. destruct r; simpl; auto. apply Euclid with o; auto. apply ModOrder_Divide with (n:=p) (a:=b) (k:=s) (d:=o*m); auto. apply ModEq_div with (pow a (o*m)); auto. rewrite <- pow_mult2. rewrite mult_1_r. replace (o*m) with (m*o) at 2; auto. repeat rewrite pow_mult. apply ModEq_trans with 1. clear -H1. induction o; simpl; auto. replace 1 with (1*1); auto. clear -H17. induction m; simpl; auto. replace 1 with (1*1); auto. apply Euclid with s; auto. apply ModOrder_Divide with (n:=p) (a:=a) (k:=o) (d:=s*m); auto. apply ModEq_div with (pow b (s*m)); auto. rewrite <- pow_mult2. rewrite mult_1_r. rewrite mult_comm. replace (s*m) with (m*s) at 2; auto. repeat rewrite pow_mult. apply ModEq_trans with 1. clear -H1. induction s; simpl; auto. replace 1 with (1*1); auto. clear -H18. induction m; simpl; auto. replace 1 with (1*1); auto. Qed.
Theorem ModOrder_fold: forall p l, Prime p -> (forall q, In q l->ModOrder p (fst q) (snd q)) -> Forall (Coprime p) (map fst l) -> ForallR Coprime (map snd l) -> ModOrder p (fold_right mult 1 (map fst l)) (fold_right mult 1 (map snd l)). Proof. induction l as [|[a o] l]; simpl; intros; auto. apply ModOrder_intro; auto. apply MinP_intro; auto. intros. destruct H3. destruct m; auto. inversion H1. inversion H2. subst x x0 l0 l1. apply ModOrder_mult; auto. apply (H0 (a,o)); auto. clear -H10. revert H10. generalize (map snd l) as m. induction m; simpl; intros; auto. Qed.

Theorem pow_m1_factorize: forall x n, x<>0 -> pow x n - 1 = (x-1)*(fold_right (fun k b=>pow x k+b) 0 (seq 0 n)). Proof. intros. assert (1<=x). destruct x; auto. induction n. simpl; auto. rewrite seqS. simpl. rewrite fold_right_app. simpl. rewrite <- plus_n_O. replace (fold_right (fun k b=>pow x k+b) (pow x n) (seq 0 n)) with (pow x n+fold_right (fun k b=>pow x k+b) 0 (seq 0 n)). rewrite mult_plus_distr_l. rewrite <- IHn. replace x with (x-1+1) at 1. rewrite mult_plus_distr_r. rewrite mult_1_l. rewrite Nat.add_sub_assoc; auto. rewrite plus_comm. rewrite <- le_plus_minus; auto. generalize (seq 0 n). generalize (pow x n). induction l; simpl; auto. rewrite plus_comm. rewrite <- plus_assoc. f_equal. rewrite plus_comm; auto. Qed.

Inductive PolyCoeff : list nat -> nat -> nat -> Prop:= PolyCoeff_intro: forall l o t, length l=o -> PolyCoeff (t::l) o t.
Hint Constructors PolyCoeff.
Fixpoint polyEval (l:list nat) (n:nat) := match l with nil => 0 |c::l' => c*pow n (length l')+polyEval l' n end.
Definition mod_minus: forall n (nz:n<>0) x, {y|Divide n (x+y) & y<n}. intros. destruct (nat_eq_dec (modN nz x) 0). exists 0; auto. apply Divide_plus; auto. apply modN_eq__ModEq with nz; auto. rewrite e. rewrite modN_le_eq; auto. exists (n-modN nz x). apply ModEq_trans with (modN nz x+(n- modN nz x)); auto. rewrite <- le_plus_minus; auto. replace n with (1*n) at 2; auto. apply multN_Divide. destruct n. absurd (0=0); auto. destruct (modN nz x). absurd (0=0); auto. simpl. apply le_n_S. apply le_minus. Defined.
Definition polyDiv: forall n (nz:n<>0) f o t a b, PolyCoeff f (S o) t -> Divide n (a+b) -> {g|PolyCoeff g o t & forall x, ModEq n (polyEval f x) ((x+a)*polyEval g x+polyEval f b)}. intros n Hn f o. revert f. induction o; intros. exists (t::nil); auto. intros. simpl. rewrite mult_1_r. rewrite <- plus_n_O. inversion H. subst f o t0. destruct l as [|c l]. inversion H1. destruct l. simpl. repeat rewrite mult_1_r. repeat rewrite <- plus_n_O. rewrite plus_assoc. apply ModEq_plus; auto. replace ((x+a)*t) with (t*(x+a)); auto. rewrite <- mult_plus_distr_l. apply ModEq_mult; auto. replace x with (x+0) at 1; auto. rewrite <- plus_assoc; auto. inversion H1.
  destruct f. exfalso; inversion H. destruct f as [|c f]. exfalso; inversion H; inversion H5. assert (n0=t). inversion H; auto. subst n0. destruct (mod_minus Hn (a*t)) as [d H1 H2]; auto. destruct (IHo (c+d::f) (c+d) a b) as [g H3 H4]; auto. inversion H; auto. exists (t::g). inversion H3. apply PolyCoeff_intro; simpl; auto. intros. assert (length f=S o). inversion H. inversion H9; auto. assert (length g=S o). inversion H3. rewrite <- H6; auto. assert (forall x, polyEval (t::c::f) x = t*pow x (o+2)+c*pow x (o+1)+polyEval f x). intros y. simpl. repeat rewrite plus_assoc. f_equal. f_equal. f_equal. rewrite H5; auto. rewrite plus_comm; auto. f_equal. f_equal. rewrite H5; rewrite plus_comm; auto. assert (forall x, polyEval (t::g) x = t*pow x (o+1)+polyEval g x). intros y. simpl. f_equal. f_equal. f_equal. rewrite plus_comm; auto. rewrite H8. rewrite mult_plus_distr_l. rewrite mult_plus_distr_r. rewrite H7. repeat rewrite <- plus_assoc. apply ModEq_plus. apply ModEq_sym. rewrite mult_comm. rewrite <- mult_assoc. apply ModEq_mult; auto. replace (o+2) with (S(o+1)). simpl. rewrite mult_comm; auto. rewrite plus_n_Sm; auto.
  apply ModEq_minus with (d*pow x (o+1)). rewrite plus_assoc. rewrite <- mult_plus_distr_r. rewrite plus_assoc. rewrite mult_assoc. rewrite <- mult_plus_distr_r. replace ((d+c)*pow x (o+1)+polyEval f x) with (0+polyEval (c+d::f) x). apply ModEq_plus. rewrite mult_comm. apply Divide_trans with (d+a*t); auto. rewrite plus_comm; auto. apply ModEq_trans with ((x+a)*polyEval g x+polyEval (c+d::f) b); auto. apply ModEq_plus; auto. simpl. repeat rewrite plus_assoc. apply ModEq_plus; auto. rewrite plus_comm. rewrite mult_plus_distr_r. apply ModEq_plus; auto. rewrite mult_assoc. apply ModEq_mult; auto. rewrite mult_comm. apply ModEq_minus with (a*t). apply ModEq_trans with 0; auto. rewrite <- mult_plus_distr_r. rewrite mult_comm. apply Divide_trans with (a+b); auto. simpl. f_equal. f_equal; auto. f_equal. rewrite plus_comm; auto. Qed.
Theorem polySolutionNum: forall p f o t c, Prime p -> PolyCoeff f o t -> ~Divide p t -> PnumN (fun x=>Divide p (polyEval f x)) p c -> c<=o. Proof. intros p f o t c Hp. revert f t c. assert (Hn:p<>0). contradict Hp; subst p; auto. induction o; intros. inversion H. destruct l. subst o t0 f. simpl in H1. replace c with 0; auto. eapply PnumN_unique; [|eapply H1]. rewrite mult_1_r. rewrite <- plus_n_O. auto. inversion H2. destruct (nat_eq_dec c 0) as [Hc|Hc]. subst c; auto. destruct (PnumN_ex H1). destruct (H2 Hc) as [d [H4 H5]]. destruct (mod_minus Hn d) as [e H6 H7]. destruct (polyDiv Hn e d H) as [g H8 H9]; auto. rewrite plus_comm; auto. apply PnumN_equiv with (Q:=fun x=>Divide p (x+e) \/ Divide p (polyEval g x)) in H1. assert (PnumN (fun x=>Divide p (x+e)) p 1). apply PnumN_one with d; auto. intros. rewrite <- modN_le_eq with p Hn y; auto. rewrite <- modN_le_eq with p Hn d; auto. apply ModEq__modN_eq. apply ModEq_minus with e; auto. rewrite plus_comm. apply ModEq_trans with 0; auto. rewrite plus_comm; auto. destruct (pnumN) with (P:=fun x=>Divide p (polyEval g x)) (n:=p) as [c' H11]. intros; apply Divide_dec. assert (c<=1+c'). eapply PnumN_or. eapply H10. eapply H11. auto. apply le_trans with (1+c'); auto. simpl. apply le_n_S. apply IHo with g t; auto. intros. split; intros. apply Euclid_Prime; auto. apply Divide_minus with (polyEval f d); auto. rewrite plus_comm. apply ModEq_trans with (polyEval f x); auto. apply ModEq_trans with ((x+e)*polyEval g x+polyEval f d); auto. apply Divide_plus; auto. destruct H11. rewrite mult_comm; apply Divide_trans with (x+e); auto. apply Divide_trans with (polyEval g x); auto. Qed.
Lemma repeat0_head: forall f x n, polyEval (repeat 0 n++f) x = polyEval f x. Proof. induction n; simpl; auto. Qed.
Lemma fold_app_length: forall {X:Type} l ll, length (fold_right (app (A:=X)) l ll) = fold_right plus (length l) (map (length (A:=X)) ll). Proof. induction ll; simpl; auto. rewrite app_length; f_equal; auto. Qed.
Theorem polyRootNum: forall p d, Prime p -> Divide d (p-1) -> PnumN (fun x=>ModEq p (pow x d) 1) p d. Proof. intros. assert (Hp:p-1<>0). contradict H. destruct p; auto. destruct p; auto. inversion H. destruct (Divide_multN H0) as [e H1]. assert (Hd:d<>0). contradict Hp. subst d. rewrite H1; auto. assert (He:e<>0). contradict Hp. subst e. rewrite H1; auto. assert (PnumN (fun x=>ModEq p (pow x (e*d)) 1) p (e*d)). rewrite <- H1. cut (forall x, 1<=x->x<=p->PnumN (fun x=>ModEq p (pow x (p-1)) 1) x (x-1)). intros. apply H2; auto. intros x Hx. induction Hx; intros. simpl. apply PnumN_NP; auto. rewrite pow0n; auto. intros C. apply Divide_le in C; auto. contradict C; auto. rewrite <- minus_Sn_m; auto. apply PnumN_P; auto. apply Fermat; auto. contradict H2. apply Divide_le in H2; auto. contradict Hx; subst m; auto. destruct (pnumN) with (P:=fun x=>ModEq p (pow x d) 1) (n:=p) as [c H3]. intros. apply ModEq_dec. replace d with c at 1; auto. apply le_antisym.
  assert (H4:PolyCoeff (1::repeat 0 (d-1)++p-1::nil) d 1). apply PolyCoeff_intro. rewrite app_length. rewrite repeat_length. simpl. rewrite plus_comm. rewrite <- le_plus_minus; auto. apply (polySolutionNum H H4). intros C. apply Divide_le in C; auto. contradict C; auto. eapply PnumN_equiv; [|eapply H3]. simpl; intros. rewrite app_length. rewrite repeat_length. rewrite <- plus_assoc. simpl. replace (d-1+1) with d. rewrite repeat0_head. simpl. rewrite mult_1_r. rewrite <- plus_n_O. split; intros. apply ModEq_trans with (1+(p-1)); auto. rewrite <- le_plus_minus; auto. apply Divide_refl. apply ModEq_minus with (p-1). rewrite plus_comm. apply ModEq_trans with 0; auto. rewrite plus_comm. rewrite <- le_plus_minus; auto. apply Divide_refl. rewrite plus_comm. apply le_plus_minus; auto.
  rewrite <- mult_1_l at 1. apply plus_le_reg_l with ((e-1)*d). rewrite <- mult_plus_distr_r. rewrite plus_comm. rewrite <- le_plus_minus; auto. destruct pnumN with (P:=fun x=>Divide p (polyEval (fold_right (app (A:=nat)) (1::nil) (repeat (1::repeat 0 (d-1)) (e-1))) x)) (n:=p) as [f H4]. intros. apply Divide_dec. assert (f<=(e-1)*d). assert (PolyCoeff (fold_right (app (A:=nat)) (1::nil) (repeat (1::repeat 0 (d-1)) (e-1))) ((e-1)*d) 1). generalize (e-1). induction n; simpl; auto. apply PolyCoeff_intro; auto. rewrite app_length. rewrite repeat_length. inversion IHn. rewrite <- H6. simpl. rewrite <- plus_n_Sm. rewrite <- plus_Sn_m. f_equal. destruct d. contradict Hd; auto. simpl. rewrite <- minus_n_O; auto. apply (polySolutionNum H H5); auto. intros C. apply Divide_le in C; auto. contradict C; auto. apply le_trans with (f+c); [|apply plus_le_compat_r]; auto. eapply PnumN_or. eapply H4. eapply H3. simpl. eapply PnumN_equiv; [|eapply H2]. intros; simpl. clear H2 H3 H4 H5 c f. assert (polyEval (fold_right (app (A:=nat)) (1::nil) (repeat (1::repeat 0 (d-1)) (e-1))) x = polyEval (fold_right (app (A:=nat)) (0::nil) (repeat (1::repeat 0 (d-1)) (e-1))) x+1). generalize (e-1). induction n; simpl; auto. repeat rewrite <- plus_assoc. f_equal. f_equal. repeat rewrite app_length. f_equal. repeat rewrite fold_app_length; auto. simpl. repeat rewrite repeat0_head; auto. assert (polyEval (fold_right (app (A:=nat)) (1::nil) (repeat (1::repeat 0 (d-1)) (e-1))) x * pow x d = polyEval (fold_right (app (A:=nat)) (0::nil) (repeat (1::repeat 0 (d-1)) (e-1))) x + pow x (e*d)). replace (e*d) with (S(e-1)*d).
  generalize (e-1). induction n; simpl; repeat rewrite <- plus_n_O; auto. rewrite mult_plus_distr_r. repeat rewrite repeat0_head; repeat rewrite app_length; repeat rewrite repeat_length; repeat rewrite fold_app_length. rewrite <- pow_plus. rewrite plus_comm. f_equal. rewrite IHn. rewrite plus_comm. f_equal. f_equal. simpl. rewrite map_repeat. simpl. rewrite repeat_length. rewrite minus_Sn_m; auto. simpl. rewrite <- minus_n_O. clear -Hd. induction n; simpl; auto. rewrite <- plus_n_O. rewrite plus_comm. apply le_plus_minus; auto. rewrite IHn. repeat rewrite plus_assoc. f_equal; auto. f_equal. rewrite map_repeat. simpl. rewrite repeat_length. rewrite minus_Sn_m; auto. simpl. rewrite <- minus_n_O. rewrite plus_comm. f_equal. clear -Hd. induction n; simpl. rewrite plus_comm. rewrite <- le_plus_minus; auto. rewrite <- IHn. repeat rewrite plus_assoc. f_equal; auto. f_equal. rewrite minus_Sn_m; auto. simpl. rewrite <- minus_n_O; auto. split; intros. destruct (Prime_Coprime_Divide (polyEval (fold_right (app (A:=nat)) (1::nil) (repeat (1::repeat 0 (d-1)) (e-1))) x)  H); auto; right. eapply ModEq_div. eapply H5. rewrite H3. rewrite mult_1_r. rewrite H2; auto. apply ModEq_minus with (polyEval (fold_right (app (A:=nat)) (0::nil) (repeat (1::repeat 0 (d-1)) (e-1))) x). rewrite <- H3. rewrite <- H2. destruct H4. apply ModEq_trans with 0; auto. rewrite mult_comm. apply ModEq_sym. eapply Divide_trans. eapply H4. auto. rewrite <- mult_1_r. auto. Qed.

Theorem Prime_ModRoot: forall p, Prime p -> exists a, ModRoot p a. Proof. intros. assert (2<=p). auto. assert (Hp:p-1<>0). contradict H0. apply le_not_lt. destruct p; auto. destruct p; auto. inversion H0. apply le_lt_or_eq in H0. destruct H0; [|subst p; exists 1]. destruct (fundamental2 (p-1)) as [[pl [H1 [H2 [H3 H4]]]]|H1]; [|contradiction]. cut (exists l, map snd l = map (fun p=>pow (fst p) (snd p)) pl /\forall q, In q l->ModOrder p (fst q) (snd q)). intros. destruct H5 as [l [H5 H6]]. exists (fold_right mult 1 (map fst l)). apply ModRoot_intro with (p-1); auto. replace (p-1) with (fold_right mult 1 (map snd l)). apply ModOrder_fold; auto. apply Forall_forall. intros q Hq. apply in_map_iff in Hq. destruct Hq as [[r s] [H7 H8]]. simpl in H7. subst r. apply H6 in H8. simpl in H8. inversion H8; auto. rewrite H5. clear -H2 H3 H4. induction pl as [|[p c] pl]; simpl; auto. inversion H2. inversion H3. inversion H4. subst x x0 x1 l l0 l1. apply ForallR_cons; auto. intros y Hy.  apply in_map_iff in Hy. destruct Hy as [[q d] [H10 H11]]. subst y. simpl. destruct (Prime_pow_Coprime_Divide (pow q d) c H1); auto. absurd (In p (map fst pl)); auto. replace p with q. apply in_map_iff. exists (q,d); auto. symmetry. apply repeat_spec with d. apply Prime_mult_In; auto. cut (Prime q). intros. clear -H0. induction d; simpl; auto. apply Forall_forall with (P:=Prime) (l:=map fst pl); auto. apply in_map_iff. exists (q,d); auto. replace (fold_right mult 1 (repeat q d)) with (pow q d); auto. clear -d. induction d; simpl; auto. rewrite H1. rewrite H5. clear -pl. induction pl; simpl; auto.
  cut (forall q, In q pl -> exists a, ModOrder p a (pow (fst q) (snd q))). intros. clear -H5. induction pl. exists nil; simpl; auto. split; auto. intros. destruct H. destruct (H5 a) as [o H6]; auto. destruct IHpl as [l [H7 H8]]. intros. apply H5; auto. exists ((o, pow (fst a) (snd a))::l). simpl. split. f_equal; auto. intros. destruct H; auto. subst q. simpl. auto. 
  intros. destruct q as [q c]. simpl. assert (c<>0). apply Forall_forall with (l:=map snd pl) (P:=fun x=>x<>0); auto. apply in_map_iff. exists (q,c); auto. assert (Prime q). apply Forall_forall with (l:=map fst pl) (P:=Prime); auto. apply in_map_iff. exists (q,c); auto. assert (Divide (pow q c) (p-1)). rewrite H1. clear -H5. induction pl. destruct H5. destruct H5. simpl. subst a. simpl; rewrite mult_comm; auto. simpl. eapply Divide_trans. eapply IHpl; auto. auto. assert (Divide (pow q (c-1)) (p-1)). apply Divide_trans with (pow q c); auto. apply pow_Prime_Divide; auto. exists (c-1); split; auto. apply le_minus. assert (PnumN (fun x=>ModEq p (pow x (pow q c)) 1) p (pow q c)). apply polyRootNum; auto. assert (PnumN (fun x=>ModEq p (pow x (pow q (c-1))) 1) p (pow q (c-1))). apply polyRootNum; auto. destruct (PnumN_lt) with (P:=fun x=>ModEq p (pow x (pow q (c-1))) 1) (Q:=fun x=>ModEq p (pow x (pow q c)) 1) (n:=p) (a:=pow q (c-1)) (b:=pow q c) as [x [Ha [Hb Hc]]]; auto. destruct c. contradict H6; auto. simpl. rewrite <- minus_n_O. remember (pow q c) as a. destruct a. symmetry in Heqa. contradict Heqa. apply pow_nz. contradict H7; subst q; auto. destruct q. contradict H7; auto. destruct q. contradict H7; auto. simpl. rewrite <- plus_n_Sm. auto.
  exists x. assert (Coprime p x). destruct (Prime_Coprime_Divide  x H); auto. contradict Ha. apply Divide_le in H12; auto. intros C; subst x. replace (pow 0 (pow q c)) with 0 in Hc. absurd (0=1); auto. apply ModEq_le_eq with p; auto. rewrite pow0n; auto. destruct (modOrder H12) as [k H13]. destruct (ModOrder_Divide (pow q c) H13). destruct (ModOrder_Divide (pow q (c-1)) H13). apply H15 in Hc. apply pow_Prime_Divide in Hc; auto. destruct Hc as [m [H18 H19]]. subst k. apply le_lt_or_eq in H19. destruct H19; [|subst m]; auto. contradict Hb. apply H16. apply pow_Prime_Divide; auto. exists m; split; auto. destruct c. contradict H6; auto. simpl. rewrite <- minus_n_O; auto. apply ModRoot_intro with (2-1); auto. simpl. apply ModOrder_intro; auto. apply MinP_intro; auto. intros. destruct m; auto. destruct H0. contradict H0; auto. Qed.
Definition modRoot: forall p, Prime p -> {a|ModRoot p a}. intros. destruct minP with (P:=fun x=>Coprime p x/\ModOrder p x (p-1)) (n:=p) as [[a H1]|H1]. intros. destruct (Coprime_dec p x); [|right]. destruct (modOrder c) as [k H1]. destruct (nat_eq_dec k (p-1)); [subst k;left|right]; auto. contradict n. destruct n. apply ModOrder_unique with p x; auto. contradict n; destruct n; auto. exists a. inversion H1. destruct H0. apply ModRoot_intro with (p-1); auto. exfalso. destruct (Prime_ModRoot H) as [a Ha]. assert (Hp:p<>0). contradict H; subst p; auto. absurd (Coprime p (modN Hp a)/\ModOrder p (modN Hp a) (p-1)); auto. apply ModRoot_ModEq with (b:=modN Hp a) in Ha; auto. inversion Ha. inversion H2. split; auto. replace (p-1) with t; auto. apply Totient_unique with p; auto. Defined.

(* Carmichael function *)
Definition Carmichael (n m:nat) := MinP (fun x=>x<>0 /\ forall y, Coprime n y-> ModEq n (pow y x) 1) m.
Definition carmichael_sig : forall n, {m|Carmichael n m}. intros. destruct (nat_eq_dec n 0) as [Hn|Hn]. subst n. exists 1. apply MinP_intro; [split|]; intros; auto. replace y with 1; auto. destruct y. contradict H; apply GCD_00; auto. apply GCD_unique with (g:=S y) in H; auto. destruct H. destruct m; auto. destruct (totient_sig n) as [t Ht]. destruct minP with (n:=S t) (P:=fun x=>x<>0/\forall y, Coprime n y->ModEq n (pow y x) 1) as [[m H]|H]. intros. destruct (nat_eq_dec x 0). subst x; right; intros C; destruct C; contradict H0; auto. destruct Forall_dec with (P:=fun y=>ModEq n (pow y x) 1) (l:=coprimeList' n) as [[y H0 H1]|H1]. intros. apply ModEq_dec. right. intros C. destruct C. contradict H1. apply H3. apply coprimeList'_In in H0. destruct H0; auto. left. split; auto. intros. apply ModEq_trans with (pow (modN Hn y) x). clear -Hn. induction x; simpl; auto. apply Forall_forall with (x:=modN Hn y) (l:=coprimeList' n); auto. apply coprimeList'_In; split; auto. apply GCD_ModEq with y; auto. exists m; auto. absurd (t<>0/\forall y, Coprime n y->ModEq n (pow y t) 1); auto. split; auto. apply Totient_nz with n; auto. Defined.
Theorem Carmichael_nz: forall n m, Carmichael n m -> m<>0. Proof. intros. inversion H. destruct H0; auto. Qed.
Theorem Carmichael0: Carmichael 0 1. Proof. intros. apply MinP_intro. split; intros; auto. destruct y. contradict H; apply GCD_00; auto. apply GCD_unique with (g:=S y) in H; auto. rewrite H; auto. intros. destruct H. destruct m; auto. Qed.
Theorem Carmichael1: Carmichael 1 1. Proof. intros. apply MinP_intro. split; intros; auto. intros. destruct H. destruct m; auto. Qed.
(*
Theorem Carmichael_mult: forall n m a b c, Coprime n m -> Carmichael n a -> Carmichael m b -> LCM c a b -> Carmichael (n*m) c.
*)

(* RSA *)
Record RSAKey : Set := mkRSAKey {
  prime1:nat; prime2:nat; modkey:nat; seckey:nat; pubkey:nat;
  isPrime1: Prime prime1;
  isPrime2: Prime prime2;
  prime_neq: prime1 <> prime2;
  modkey_mult: modkey = prime1 * prime2;
  modkey_nz: modkey <> 0;
  pubkey_coprime: Coprime (totient modkey) pubkey;
  pubkey_le: pubkey <= totient modkey;
  keyinv: ModEq (totient modkey) (seckey*pubkey) 1;
}.

Definition generateRSAKey (p q e:nat) : Prime p -> Prime q -> p<>q -> e<=(p-1)*(q-1) -> Coprime ((p-1)*(q-1)) e -> RSAKey. intros. assert (totient (p*q) = (p-1)*(q-1)). unfold totient. destruct (totient_sig (p*q)). apply Totient_unique with (p*q); auto. apply Totient_mult; auto. destruct (Prime_Coprime_Divide q H); auto. apply Prime_Divide in H4; auto. destruct H4. contradict H; subst p; auto. contradiction. destruct (invMod ((p-1)*(q-1)) e) as [[d H5]|H5]. rewrite <- H4 in H3. rewrite <- H4 in H2. rewrite <-H4 in H5. refine (mkRSAKey d  H H0 H1 _ _ H3 H2 _); auto. intros C. apply mult_is_O in C. destruct C. subst p; contradict H; auto. subst q; contradict H0; auto. replace (d*e) with (e*d); auto. contradiction. Defined.

Definition RSAencrypt (k:RSAKey) (m:nat) : nat := modN (modkey_nz k) (pow m (pubkey k)).
Definition RSAdecrypt (k:RSAKey) (m:nat) : nat := modN (modkey_nz k) (pow m (seckey k)).

Lemma ModEq_pow: forall n a b c, ModEq n a b -> ModEq n (pow a c) (pow b c). Proof. induction c; intros; simpl; auto. Qed.
Theorem RSA_spec: forall k m, Coprime (modkey k) m -> RSAdecrypt k (RSAencrypt k m) = modN (modkey_nz k) m. Proof. intros k m Hc. unfold RSAdecrypt. unfold RSAencrypt. apply ModEq__modN_eq. apply ModEq_trans with (pow (pow m (pubkey k)) (seckey k)). apply ModEq_pow; auto. rewrite <- pow_mult. destruct k; simpl. simpl in Hc. destruct (ModEq_multN keyinv0) as [[q H]|[q H]]. destruct q. simpl in H. rewrite <- H. simpl. rewrite mult_1_r; auto. simpl in H.  absurd (totient modkey0<=1). apply lt_not_le. subst modkey0. replace (totient (prime3*prime4)) with ((prime3-1)*(prime4-1)). assert (2<=prime3); auto. apply le_lt_or_eq in H0. destruct H0. apply le_trans with (prime3-1); auto. destruct prime3. contradict isPrime3; auto. simpl. rewrite <- minus_n_O. auto. destruct prime4. contradict isPrime4; auto. destruct prime4. contradict isPrime4; auto. simpl. rewrite <- mult_n_Sm; auto. subst prime3. simpl. rewrite <- plus_n_O. assert (2<=prime4); auto. apply le_lt_or_eq in H0. destruct H0. destruct prime4. inversion H0. simpl. rewrite <- minus_n_O; auto. contradiction. apply Totient_unique with (prime3*prime4); auto. apply Totient_mult; auto. destruct (Prime_Coprime_Divide prime4 isPrime3); auto. destruct (Prime_Divide isPrime4 H0). contradict isPrime3; subst prime3; auto. contradiction. unfold totient. destruct (totient_sig (prime3*prime4)); auto.
  rewrite H. rewrite <- plus_assoc; auto. rewrite H. rewrite plus_comm. simpl. replace m with (m*1) at 3; auto. apply ModEq_mult; auto. rewrite pow_mult. replace 1 with (pow 1 q); auto. apply ModEq_pow. apply Euler; auto. unfold totient. destruct (totient_sig modkey0); auto. clear -q. induction q; simpl; auto. rewrite <- plus_n_O; auto. rewrite mult_1_r; auto. Qed.

