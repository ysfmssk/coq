Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import ModEq.

Require Import combi.

Set Implicit Arguments.

Theorem Willson1: forall p, Prime p -> ModEq p (fact (p-1)) (p-1). Proof. intros. destruct (le_lt_dec p 2) as [H0|H0]. replace p with 2; simpl; auto. apply le_antisym; auto. assert (Hp:p<>0). contradict H; subst p; auto. rewrite fact_fold. remember (p-1) as t. assert (Ht: p=S t). destruct p. contradict Hp; auto. simpl in Heqt. rewrite <- minus_n_O in Heqt; subst t; auto. assert (Ht1:t<p). rewrite Ht; auto. assert (Ht2:Coprime p t). destruct (Prime_Coprime_Divide t H); auto. apply Divide_le in H1. contradict Ht1; auto. contradict H. rewrite Ht. rewrite H. auto. remember (t-2) as u. assert (Hu:t=S(S u)). subst u. destruct t. subst p; contradict H0; auto. simpl. destruct t. contradict H0; subst p; auto. simpl. rewrite <- minus_n_O; auto. rewrite Hu at 1. rewrite seqS. simpl. rewrite <- plus_n_O. rewrite fold_mult_app. simpl. rewrite mult_1_r. rewrite <- Hu. replace t with (1*t) at 2; auto. apply ModEq_mult; auto.
  destruct (Rpair_list) with (l:=seq 2 u) (R:=fun x y=>ModEq p (x*y) 1) as [l [H1 H2]]; simpl; intros; auto. intros C. apply in_seq in H1. destruct H1. absurd (x=1). contradict H1; subst x; auto. rewrite <- modN_le_eq with p Hp x. rewrite <- modN_le_eq with p Hp 1; auto. apply ModEq__modN_eq. apply ModEq_div with (1+x); auto. destruct (Prime_Coprime_Divide (1+x) H); auto. simpl in H3. apply Divide_le in H3; auto. contradict H2. simpl. rewrite <- Hu. apply le_not_lt. apply le_S_n. rewrite <- Ht; auto. rewrite mult_1_r. rewrite mult_plus_distr_r. rewrite mult_1_l. rewrite plus_comm. auto. simpl in H2. rewrite <- Hu in H2. apply lt_le_trans with t; auto.
  apply in_seq in H1. destruct H1. simpl in H2. rewrite <- Hu in H2. assert (Hx:x<p). rewrite Ht; auto. assert (Hxz:x<>0). contradict H1; subst x; auto. assert (Hc:Coprime p x). destruct (Prime_Coprime_Divide x H); auto. apply Divide_le in H3; auto. contradict Hx; auto. destruct ModInv with (n:=p) (a:=x) as [y [H3 H4]]; auto. exists (modN Hp y). split. apply ModEq_trans with (x*y); auto. split. apply in_seq. split. destruct (le_lt_dec 2 (modN Hp y)); auto. inversion l. assert (ModEq p x 1). replace x with (x*modN Hp y). apply ModEq_trans with (x*y); auto. rewrite H6. rewrite mult_1_r; auto. apply ModEq__modN_eq with p Hp x 1 in H5. rewrite modN_le_eq in H5; auto. rewrite modN_le_eq in H5; auto. contradict H1; subst x; auto. inversion H6. assert (ModEq p 0 1). apply ModEq_trans with (x*y); auto. replace 0 with (x*modN Hp y); auto. rewrite H8; auto. absurd (0=1); auto. apply ModEq__modN_eq with p Hp 0 1 in H7. rewrite modN_le_eq with p Hp 1 in H7; auto. rewrite modN_le_eq with p Hp 0 in H7; auto. inversion H8. simpl. rewrite <- Hu. assert (modN Hp y<p). auto. rewrite Ht in H5. apply le_S_n in H5. destruct (le_lt_or_eq (modN Hp y) t H5); auto. contradict H2. replace x with t; auto. cut (ModEq p t x). intros. apply ModEq__modN_eq with p Hp t x in H2. rewrite modN_le_eq in H2; auto. rewrite modN_le_eq in H2; auto.
  destruct (ModInv) with (n:=p) (a:=t) as [z [H7 H8]]; auto. contradict H0. rewrite Ht. rewrite H0. auto. apply ModEq_trans with z. apply ModEq_sym; apply H8. rewrite Ht. apply ModEq_m1_sq. apply H8. rewrite <- H6. apply ModEq_trans with (y*x); auto. rewrite mult_comm; auto. intros. rewrite <- modN_le_eq with p Hp z. apply ModEq__modN_eq; auto. apply in_seq in H5. destruct H5. apply lt_le_trans with (2+u); auto. simpl. rewrite <- Hu; auto. 
 rewrite mult_comm; auto. rewrite fold_right_Perm with (m:=map fst l++map snd l); auto. clear -H2. induction l as [|[a b] l]; simpl; auto. rewrite fold_right_Perm with (m:=b::map fst l++map snd l); auto. simpl. rewrite mult_assoc. inversion H2.  replace 1 with (1*1); auto. Qed.
Theorem Willson2: forall n, 2<=n -> ModEq n (fact (n-1)) (n-1) -> Prime n. Proof. intros. destruct (primeDivide n) as [[p H1 H2]|H1]; [|contradict H; auto]. assert (p<=n). apply Divide_le; auto. contradict H; subst n; auto. destruct (le_lt_or_eq p n H3). absurd (Divide p (fact (n-1)+1)). intros C. apply Divide_minus in C. apply Divide_le in C; auto. contradict C; auto. apply fact_Divide. apply le_S_n. destruct n; simpl; auto. rewrite <- minus_n_O; auto. contradict H1; subst p; auto. apply Divide_trans with n; auto. apply ModEq_trans with n; auto. replace n with (1*n+0) at 2; auto. simpl. repeat rewrite <- plus_n_O. auto. replace n with (n-1+1) at 2; auto. destruct n; simpl; auto. rewrite <- minus_n_O. rewrite plus_comm; auto. subst p; auto. Qed.

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
Theorem RSA_spec: forall k m, Coprime (modkey k) m -> RSAdecrypt k (RSAencrypt k m) = modN (modkey_nz k) m. Proof. intros k m Hc. unfold RSAdecrypt. unfold RSAencrypt. apply ModEq__modN_eq. apply ModEq_trans with (pow (pow m (pubkey k)) (seckey k)). apply ModEq_pow; auto. rewrite <- pow_mult. destruct k; simpl. simpl in Hc. destruct (ModEq_multN keyinv0) as [[q H]|[q H]]. destruct q. simpl in H. rewrite <- H. simpl. rewrite mult_1_r; auto. simpl in H.  absurd (totient modkey0<=1). apply lt_not_le. subst modkey0. replace (totient (prime3*prime4)) with ((prime3-1)*(prime4-1)). assert (2<=prime3); auto. apply le_lt_or_eq in H0. destruct H0. apply le_trans with (prime3-1); auto. destruct prime3. contradict isPrime3; auto. simpl. rewrite <- minus_n_O. auto. destruct prime4. contradict isPrime4; auto. destruct prime4. contradict isPrime4; auto. simpl. rewrite <- mult_n_Sm; auto. subst prime3. simpl. rewrite <- plus_n_O. assert (2<=prime4); auto. apply le_lt_or_eq in H0. destruct H0. destruct prime4. inversion H0. simpl. rewrite <- minus_n_O; auto. contradiction. apply Totient_unique with (prime3*prime4); auto. apply Totient_mult; auto. destruct (Prime_Coprime_Divide prime4 isPrime3); auto. destruct (Prime_Divide isPrime4 H0). contradict isPrime3; subst prime3; auto. contradiction. unfold totient. destruct (totient_sig (prime3*prime4)); auto.
  rewrite H. rewrite <- plus_assoc; auto. rewrite H. rewrite plus_comm. simpl. replace m with (m*1) at 3; auto. apply ModEq_mult; auto. rewrite pow_mult. replace 1 with (pow 1 q); auto. apply ModEq_pow. apply Euler; auto. unfold totient. destruct (totient_sig modkey0); auto. rewrite mult_1_r; auto. Qed.

