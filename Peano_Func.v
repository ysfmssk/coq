Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import Peano_LQ.

Set Implicit Arguments.

Theorem Var_Eq_sym: forall x y l, Inf l (#x==#y) -> Inf l (#y==#x). Proof. intros. apply IMp with (#x==#x); auto. apply IMp with (#x==#y); auto. apply IAx. apply PAE2 with (S(max x y)) (#S(max x y)) (#x); auto; apply nVT_SubTerm; intros C; apply VT_var in C; absurd (x<x); auto; rewrite <- C at 2; auto. Qed.
Theorem Var_Eq_trans: forall x y z l, Inf l (#x==#y) -> Inf l (#y==#z) -> Inf l (#x==#z). Proof. intros. apply IMp with (#y==#z); auto. apply IMp with (#y==#x); [|apply Var_Eq_sym]; auto. apply IAx. apply PAE2 with (S z) (#S z) (#z); auto; apply nVT_SubTerm; intros C; apply VT_var in C. Qed.
Theorem Term_Eq_refl: forall t l, Inf l (t==t). Proof. intros. apply Inf_incl with nil; auto. apply Ui with (#0==#0) 0 t; auto. Qed.
Theorem Term_Eq_sym: forall t u l, Inf l (t==u) -> Inf l (u==t). Proof. intros. destruct (varTerm u) as [vs Hv]. apply IMP with (t==u) nil l; auto. apply Ui with (#S(maxl vs)==u==>u==#S(maxl vs)) (S(maxl vs)) t; auto. apply Ug; auto. apply Ui with (#S(maxl vs)==#0==>#0==#S(maxl vs)) 0 u; auto. apply Ug; auto. apply Ded. apply Var_Eq_sym; auto. apply TFFSub_Imp; apply TFFSub_Eq; auto; apply nVT_SubTerm; intros C; apply Hv in C; apply maxl_le in C; contradict C; auto. Qed.
Theorem Var_Eq_SubTerm: forall v x y t tx ty l, Inf l (#x==#y) -> SubTerm v (#x) t tx -> SubTerm v (#y) t ty -> Inf l (tx==ty). Proof. intros. destruct (varTerm t) as [vs Hv]. remember (S (maxl (x::vs))) as z. destruct (subTerm_sig v (#z) t) as [t' H2 H3]. assert (Hz:~VarTerm z t). intros C. apply Hv in C. apply maxl_le in C. contradict C. apply lt_not_le. rewrite Heqz. simpl; auto. assert (SubTerm z (#x) t' tx). apply SubTerm_via with v t; auto. assert (SubTerm z (#y) t' ty). apply SubTerm_via with v t; auto. apply IMp with (tx==tx). apply IMp with (#x==#y); auto. apply IAx. apply PAE2 with z tx t'; auto; apply nVT_SubTerm; apply SubTerm_nVT2 with v (#x) t; auto; intros C; apply VT_var in C; subst z; absurd (x<x); auto; rewrite <-C at 2; auto. apply Term_Eq_refl. Qed.
Theorem Term_Eq_SubTerm: forall t u l v f ft fu, Inf l (t==u) -> SubTerm v t f ft -> SubTerm v u f fu -> Inf l (ft==fu). Proof. intros. apply IMP with (t==u) nil l; auto. destruct (varTerm u) as [uvs Hu]. destruct (varTerm f) as [fvs Hf]. remember (S (maxl (uvs++fvs))) as x. assert (forall i, x<=i->~VarTerm i f). intros i Hi C. apply Hf in C. absurd (x<=maxl (uvs++fvs)). apply lt_not_le. rewrite Heqx; auto. apply le_trans with i; auto. apply maxl_le; auto. apply in_or_app; auto. assert (forall i, x<=i->~VarTerm i u). intros i Hi C. apply Hu in C. absurd (x<=maxl (uvs++fvs)). apply lt_not_le. rewrite Heqx; auto. apply le_trans with i; auto. apply maxl_le. apply in_or_app; auto. apply Ui with (#x==u==>subTerm v (#x) f==fu) x t. apply Ug; auto. apply Ui with (#x==#S x==>subTerm v (#x) f==subTerm v (#S x) f) (S x) u; auto. apply Ug; auto. apply Ded. apply Var_Eq_SubTerm with v x (S x) f; auto.
  apply TFFSub_Imp; apply TFFSub_Eq; auto. apply nVT_SubTerm. apply SubTerm_nVT2 with v (#x) f; auto. intros C. apply VT_var in C. contradict C; auto. apply SubTerm_via with v f; auto. apply TFFSub_Imp; apply TFFSub_Eq; auto. apply SubTerm_via with v f; auto. apply nVT_SubTerm. apply SubTerm_nVT2 with v u f; auto. Qed.
Hint Resolve Var_Eq_sym Var_Eq_trans Term_Eq_refl Term_Eq_sym Var_Eq_SubTerm Term_Eq_SubTerm.

Theorem Term_Eq_Succ: forall t u l, Inf l (t==u) -> Inf l (Succ t==Succ u). Proof. intros. apply Term_Eq_SubTerm with t u 0 (Succ (#0)); auto; unfold Succ; apply ST_Func; auto. Qed.
Theorem Term_Eq_Succ_inv: forall t u l, Inf l (Succ t==Succ u) -> Inf l (t==u). Proof. intros. apply IMP with (Succ t==Succ u) nil l; auto. destruct (varTerm t) as [vs Hv]. apply Ui with (Succ t==Succ (#S(maxl vs))==>t==(#S(maxl vs))) (S(maxl vs)) u. apply Ug; auto. apply Ui with (Succ (#0)==Succ (#S(maxl vs))==>#0==#S(maxl vs)) 0 t; auto. apply TFFSub_Imp; apply TFFSub_Eq; auto; apply ST_Func; auto. apply TFFSub_Imp; apply TFFSub_Eq; auto. apply nVT_SubTerm; auto. intros C. inversion C. apply In_one in H4. subst t0. apply Hv in H3. absurd (S (maxl vs)<=maxl vs); auto. auto. unfold Succ; auto. apply nVT_SubTerm. intros C. apply Hv in C. absurd (S (maxl vs)<=maxl vs); auto. Qed.


