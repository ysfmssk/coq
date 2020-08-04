Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import ModEq.


Set Implicit Arguments.

Inductive Combi: nat -> relation (nat):= Combi_intro: forall n k a, k<=n -> fact n=fact k*fact (n-k)*a -> Combi n k a.
Hint Constructors Combi.
Theorem Combi_add: forall n k b c, Combi n (S k) b -> Combi n k c -> Combi (S n) (S k) (b+c). Proof. intros. inversion H. inversion H0.  clear -H1 H2 H7. apply Combi_intro; auto. replace (S n-S k) with (n-k); auto. rewrite mult_plus_distr_l. assert (forall k, fact (S k)=(S k)*fact k). simpl; auto. assert (fact (n-k)=(n-k)*fact (n-S k)). replace (n-k) with (S(n-S k)). simpl; auto. rewrite minus_Sn_m; auto. symmetry. rewrite H at 2. rewrite H0 at 1. replace (fact (S k)*((n-k)*fact (n-S k))*b) with ((n-k)*(fact (S k)*fact(n-S k)*b)). rewrite <- H2. rewrite <-  mult_assoc. rewrite <- mult_assoc. rewrite <- mult_assoc in H7. rewrite <- H7. rewrite <- mult_plus_distr_r. rewrite H. f_equal. rewrite <- plus_n_Sm. f_equal. rewrite plus_comm. rewrite <- le_plus_minus; auto. rewrite mult_comm. rewrite <- mult_assoc. rewrite <- mult_assoc. rewrite <- mult_assoc. f_equal. rewrite mult_comm. rewrite <- mult_assoc. apply mult_comm. Qed.
Theorem Combi_0: forall n, Combi n 0 1. Proof. intros. apply Combi_intro; auto. simpl. rewrite <- minus_n_O. rewrite mult_1_r. simpl. rewrite plus_comm; auto. Qed.
Theorem Combi_n: forall n, Combi n n 1. Proof. intros. apply Combi_intro; auto. rewrite mult_1_r. rewrite <- minus_n_n. simpl. rewrite mult_1_r; auto. Qed.
Theorem Combi_unique: forall n k a b, Combi n k a -> Combi n k b -> a=b. Proof. intros. inversion H. inversion H0. apply Nat.mul_cancel_l with (fact (n-k)). apply fact_nz. apply Nat.mul_cancel_l with (fact k). apply fact_nz. repeat rewrite mult_assoc. rewrite <- H2. auto. Qed.
Definition combi_sig: forall n k, {a|Combi n k a}+{n<k}. induction n; intros. destruct (nat_eq_dec k 0); [left|right]. subst k.  exists 1. apply Combi_0. destruct k; auto. destruct k. left; exists 1. apply Combi_0. destruct (le_lt_dec k n); [left|right]; auto. apply le_lt_or_eq in l. destruct (nat_eq_dec k n). exists 1. subst k; apply Combi_n. destruct (IHn (S k)) as [[a H]|H]. destruct (IHn k) as [[b H1]|H1]. exists (a+b). apply Combi_add; auto. contradict H1. destruct l; auto. contradict H. destruct l; auto. Defined.
Definition combi n k (H:k<=n): nat. refine (match combi_sig n k with inleft (exist _ a _) => a |inright _ => _ end). contradict l; auto. Defined.
