Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import ModEq.


Set Implicit Arguments.

Fixpoint combi (n k:nat) :=
  match k with |O => 1
               |S k'=> match n with |O => 0 |S n'=> combi n' k + combi n' k' end end.

Theorem Combi_0: forall n, combi n 0 = 1. Proof. intros. destruct n; simpl; auto. Qed.
Theorem Combi_1: forall n, combi n 1 = n. Proof. induction n; simpl; auto. rewrite IHn. rewrite Combi_0. rewrite plus_comm; auto. Qed.
Theorem Combi_lt: forall n k, n<k -> combi n k = 0. Proof. induction n; intros; auto. destruct k; auto. inversion H. destruct k. inversion H. simpl. rewrite IHn; auto. rewrite IHn; auto. Qed.
Theorem Combi_S: forall n k, combi (S n) (S k) = combi n (S k) + combi n k. Proof. intros. auto. Qed.
Theorem Combi_n_n: forall n, combi n n = 1. Proof. induction n; auto. rewrite Combi_S; auto. rewrite IHn. rewrite Combi_lt; auto. Qed.
Theorem Combi_fact: forall n k, k<=n -> combi n k * fact k * fact (n-k) = fact n. Proof. induction n; intros. inversion H; auto. destruct k. simpl. rewrite plus_n_O; auto. rewrite Combi_S. apply le_S_n in H. apply le_lt_or_eq in H. destruct H as [H|H]. replace (S n-S k) with (n-k); auto. rewrite <- mult_assoc. rewrite mult_plus_distr_r. replace (fact (n-k)) with (fact (n-S k)*(n-k)) at 1. repeat rewrite mult_assoc. rewrite IHn; auto. 
  replace (fact (S k)) with (S k*fact k); auto. replace (combi n k*(S k*fact k)*fact (n-k)) with (combi n k*fact k*fact (n-k)*S k); auto. rewrite IHn; auto. rewrite <- mult_plus_distr_l. rewrite <- plus_n_Sm. rewrite plus_comm. rewrite <- le_plus_minus; auto. rewrite mult_comm; auto. repeat rewrite <- mult_assoc. f_equal. symmetry. rewrite mult_comm. rewrite mult_assoc; auto. replace (n-k) with (S(n-S k)). rewrite mult_comm; auto. rewrite minus_Sn_m; auto. subst k. rewrite Combi_lt; auto. rewrite Combi_n_n. rewrite <- minus_n_n. rewrite mult_1_r. auto. Qed.
Theorem Combi_nz: forall n k, k<=n -> combi n k<>0. Proof. induction n; intros. inversion H. simpl; auto. destruct k. simpl; auto. rewrite Combi_S. intros C. apply plus_is_O in C. destruct C. contradict H1. apply IHn; auto. Qed.
Lemma fact_Prime: forall p n, Prime p -> n<p -> ~Divide p (fact n). Proof. induction n; intros. intros C. apply Divide_le in C; auto. contradict C; auto. rewrite fact_S. intros C. apply Euclid_Prime in C; auto. destruct C. apply Divide_le in H1; auto. contradict H1; auto. contradict H1; auto. Qed.
Theorem Combi_Prime: forall p k, Prime p -> 0<k<p -> Divide p (combi p k). Proof. intros. destruct H0. assert (combi p k*fact k*fact (p-k)=fact p). apply Combi_fact; auto. assert (Divide p (combi p k*fact k*fact (p-k))). rewrite H2; auto. apply Euclid_Prime in H3; auto. destruct H3. apply Euclid_Prime in H3; auto. destruct H3; auto. contradict H3. apply fact_Prime; auto. contradict H3. apply fact_Prime; auto. destruct k. contradict H0; auto. destruct p; auto. simpl. apply le_lt_trans with p; auto. apply le_minus. Qed.

Theorem poly_combi: forall x y n, pow (x+y) n = fold_right plus 0 (map (fun k=>combi n k*pow x (n - k)*pow y k) (seq 0 (S n))). Proof. induction n. simpl; auto. rewrite powS. rewrite seqS. rewrite map_app. replace (map (fun k=>combi (S n) k*pow x (S n-k)*pow y k) (0+S n::nil)) with (pow y (S n)::nil). rewrite fold_plus_app. rewrite IHn. rewrite mult_plus_distr_r. rewrite seqS at 2. rewrite map_app. rewrite fold_plus_app. rewrite mult_plus_distr_l. rewrite plus_assoc. f_equal. replace (seq 0 (S n)) with (0::seq 1 n). simpl. rewrite mult_plus_distr_l. rewrite <- plus_assoc. f_equal. rewrite Combi_0. repeat rewrite mult_1_r. rewrite <- plus_n_O. f_equal. rewrite <- minus_n_O; auto. rewrite mult_fold_plus. rewrite mult_fold_plus. repeat rewrite mult_0_r. rewrite map_map. rewrite map_map. replace (seq 0 n) with (map (fun x=>x-1) (seq 1 n)). rewrite map_map. rewrite fold_plus_map.
  f_equal. apply map_ext_in. clear IHn. intros a Ha. apply in_seq in Ha. destruct Ha. simpl in H0. apply le_S_n in H0. destruct a. inversion H. replace (S a -1) with a. repeat rewrite mult_plus_distr_r. f_equal. rewrite mult_assoc. f_equal. rewrite mult_comm. rewrite <- mult_assoc. f_equal. rewrite mult_comm. rewrite <- powS. f_equal. rewrite minus_Sn_m; auto. rewrite mult_comm. repeat rewrite <- mult_assoc. f_equal. f_equal. rewrite powS; auto. simpl; rewrite <- minus_n_O; auto. clear -n. induction n. simpl; auto. repeat rewrite seqS. rewrite map_app. f_equal; auto. simpl. rewrite <- minus_n_O; auto. simpl; auto.
  simpl. repeat rewrite <- plus_n_O. f_equal. rewrite Combi_n_n. rewrite <- minus_n_n. rewrite mult_1_l; auto. simpl. f_equal. rewrite Combi_n_n. rewrite Combi_lt; auto. rewrite <- minus_n_n. rewrite mult_1_l; auto. Qed.

Theorem poly2: forall x y, pow (x+y) 2 = x*x + 2*x*y + y*y. Proof. intros. rewrite poly_combi. simpl. repeat rewrite <- plus_n_O. repeat rewrite mult_1_r. rewrite <- plus_assoc; auto. Qed.

Hint Resolve Combi_0 Combi_1 Combi_lt Combi_S Combi_n_n Combi_fact Combi_nz fact_Prime Combi_Prime poly_combi poly2.