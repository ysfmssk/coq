Require Import Arith.
Require Import Relations.
Require Import List.
Require Import Orders.
Require Import Wellfounded.

Set Implicit Arguments.

Section ListType.

Variable T:Type.

Inductive Swap: relation (list T) :=
|Swap_here: forall a b l, Swap (a::b::l) (b::a::l)
|Swap_there: forall a l m, Swap l m -> Swap (a::l) (a::m)
.
Inductive Perm: relation (list T) :=
|Perm_nil: Perm nil nil
|Perm_Add: forall a l la m ma, Perm l m -> Add a l la -> Add a m ma -> Perm la ma
.
Hint Constructors Swap Perm Add.
Hint Resolve in_eq in_cons.
Definition Perm' := clos_refl_trans (list T) Swap.

Theorem Swap_sym : forall l m, Swap l m -> Swap m l. Proof. intros. induction H; auto. Qed.
Theorem Perm'_sym : forall l m, Perm' l m -> Perm' m l. Proof. intros. induction H. apply rt_step; apply Swap_sym; auto. apply rt_refl. apply rt_trans with y; auto. Qed.
Theorem Perm'_refl : forall l, Perm' l l. Proof. intros. apply rt_refl; auto. Qed.
Theorem Perm'_trans : forall l m n, Perm' l m -> Perm' m n -> Perm' l n. Proof. intros. apply rt_trans with m; auto. Qed.
Theorem Swap_Perm' : forall l m, Swap l m -> Perm' l m. Proof. intros. apply rt_step; auto. Qed.
Hint Resolve Swap_sym Perm'_sym Perm'_refl Perm'_trans Swap_Perm'.
Theorem Perm'_cons: forall a l m, Perm' l m -> Perm' (a::l) (a::m). Proof. intros. induction H; eauto. Qed.
Theorem Perm'_cons_Add: forall a l la, Add a l la -> Perm' (a::l) la. Proof. intros. induction H; auto. apply Perm'_trans with (x::a::l); auto. apply Perm'_cons; auto. Qed.
Hint Resolve Perm'_cons Perm'_cons_Add.

Theorem Perm__Perm' : forall l m, Perm l m -> Perm' l m. Proof. intros. induction H; auto. apply Perm'_trans with (a::l); auto. apply Perm'_trans with (a::m); auto. Qed.
Theorem Perm_length : forall l m, Perm l m -> length l = length m. Proof. intros. induction H; auto. apply Add_length in H0. apply Add_length in H1. rewrite H0. rewrite H1. auto. Qed.
Theorem Perm_In : forall l m a, Perm l m -> In a l -> In a m. Proof. intros. induction H; auto. apply Add_in with (x:=a) in H1. apply Add_in with (x:=a) in H2. apply H2. apply H1 in H0. destruct H0; [left|right]; auto. Qed.
Theorem Perm_refl : forall l, Perm l l. Proof. induction l; auto. apply Perm_Add with a l l; auto. Qed.
Theorem Perm_sym : forall l m, Perm l m -> Perm m l. Proof. intros. induction H; auto. apply Perm_Add with a m l; auto. Qed.
Theorem Perm_cons: forall a l m, Perm l m -> Perm (a::l) (a::m). Proof. intros. eapply Perm_Add; eauto. Qed.
Hint Resolve Perm_In Perm_length Perm__Perm' Perm_refl Perm_sym Perm_cons.
Theorem Add_insert : forall (a:T) l m, Add a (l++m) (l++a::m). Proof. induction l; simpl; intros; auto. Qed.
Theorem Add_dual : forall l (a:T) la, Add a la l -> forall b lb, Add b lb l -> a=b /\ la=lb \/ exists lc, Add a lc lb /\ Add b lc la. Proof. intros l a la H. induction H; intros. inversion H; [left|right]; auto. exists l0; auto.
  inversion H0. right. subst l0 x l'. exists l; auto. subst lb x0 l'0. destruct (IHAdd b l0 H3) as [[H4 H5]|[lc [H4 H5]]]. left; subst b l0; auto. right; exists (x::lc); auto. Qed.
Theorem Perm_Add_inv : forall a l la m ma, Add a l la -> Add a m ma -> Perm la ma -> Perm l m. Proof. intros a l la. revert l. apply (Fix (well_founded_ltof (list T) (length (A:=T)))) with (P:=fun la=>forall l m ma,Add a l la->Add a m ma->Perm la ma->Perm l m). clear la. intros la IH. intros. inversion H1 as [|b lb lb' mb mb']. subst la ma; inversion H0. subst lb' mb'.
  destruct (Add_dual H H3) as [[H5 H6]|[lc [H5 H6]]]; destruct (Add_dual H0 H4) as [[H7 H8]|[mc [H7 H8]]]. subst b lb mb; auto. subst b lb. destruct (Add_inv a l) as [lc H9]. apply Perm_In with mb; auto. apply Add_in with (x:=a) in H7; apply H7; left; auto. apply Perm_Add with a lc mc; auto. apply IH with l mb; auto. unfold ltof. apply Add_length in H3. rewrite H3; auto.
  subst b mb. destruct (Add_inv a m) as [mc H7]. apply Perm_In with lb; auto. apply Add_in with (x:=a) in H5; apply H5; left; auto. apply Perm_Add with a lc mc; auto. apply IH with lb m; auto. unfold ltof. apply Add_length in H3. rewrite H3; auto. apply Perm_Add with b lc mc; auto. apply IH with lb mb; auto. unfold ltof. apply Add_length in H3. rewrite H3; auto. Qed.
Theorem Perm_trans : forall l m n, Perm l m -> Perm m n -> Perm l n. Proof. intros l m n H. revert n. induction H; intros. inversion H; auto. destruct (Add_inv a n) as [n' H3]. apply Perm_In with ma; auto. apply Add_in with (x:=a) in H1; apply H1; left; auto. apply Perm_Add with a l n'; auto. apply IHPerm. apply Perm_Add_inv with a ma n; auto. Qed.
Theorem Perm'__Perm : forall l m, Perm' l m -> Perm l m. Proof. intros. induction H; auto. induction H; auto. apply Perm_Add with a (b::l) (b::l); auto. apply Perm_trans with y; auto. Qed.
Hint Resolve Add_dual Perm_Add_inv Perm_trans Perm'__Perm.

Theorem Perm_rev: forall l, Perm l (rev l). Proof. induction l; simpl; auto. apply Perm_Add with a l (rev l); auto. generalize (rev l) as m. induction m; simpl; auto. Qed.
Theorem app_Add: forall (a:T) l la m, Add a l la -> Add a (l++m) (la++m). Proof. intros. induction H; simpl; auto. Qed.
Theorem Perm_app_swap: forall l m, Perm (l++m) (m++l). Proof. induction l; simpl; intros. rewrite app_nil_r; auto. apply Perm_Add with a (l++m) (m++l); auto. induction m; simpl; auto. Qed.
Theorem Perm_app: forall l1 m1 l2 m2, Perm l1 m1 -> Perm l2 m2 -> Perm (l1++l2) (m1++m2). Proof. intros. induction H; simpl; auto. apply Perm_Add with a (l++l2) (m++m2); auto; apply app_Add; auto. Qed.
Theorem Perm_app_rev: forall l1 m1 l2 m2, Perm l1 m1 -> Perm (l1++l2) (m1++m2) -> Perm l2 m2. Proof. intros. induction H; simpl in H0; auto. apply IHPerm. apply Perm_Add_inv with a (la++l2) (ma++m2); auto; apply app_Add; auto. Qed.
Theorem NoDup_incl_length: forall  (l m:list T), NoDup l -> incl l m ->length l<=length m. Proof. induction l; simpl; intros. apply le_O_n. inversion H. subst x l0. destruct (Add_inv a m) as [m' H5]. apply H0; auto. rewrite Add_length with T a m' m; auto. apply le_n_S. apply IHl; auto. intros x Hx. apply Add_in with (x:=x) in H5. cut (In x m); intros. apply H5 in H1. destruct H1; auto. subst x; contradiction. apply H0; auto. Qed.
Theorem NoDup_incl_Perm : forall l m, incl l m -> NoDup l -> length m <= length l -> Perm l m. Proof. induction l; intros. destruct m; auto. contradict H1. apply lt_not_le. simpl. apply le_n_S. apply le_O_n. destruct (Add_inv a m) as [m' H2]. apply H. left; auto. apply Perm_Add with a l m'; auto. apply IHl; auto. intros y H3. apply Add_in with (x:=y) in H2. cut (In y m); intros. apply H2 in H4. destruct H4; auto. subst y. inversion H0; contradiction. apply H. right; auto. inversion H0; auto. apply Add_length in H2. rewrite H2 in H1. apply le_S_n; auto. Qed.
Theorem NoDup_incl_each_Perm: forall l m, NoDup l -> NoDup m -> incl l m -> incl m l -> Perm l m. Proof. induction l;intros; auto. destruct m; auto. absurd (In t nil); auto. inversion H. subst x l0. destruct (Add_inv a m) as [m' H3]; auto. apply (NoDup_Add H3) in H0. destruct H0. apply Perm_Add with a l m'; auto. apply IHl; auto. intros x Hx. apply Add_in with (x:=x) in H3. cut (In x m); intros. apply H3 in H7. destruct H7; auto. subst x; contradiction. auto. intros x Hx. cut (In x (a::l)); intros. destruct H7; auto. subst x; contradiction. apply H2. apply Add_in with (x:=x) in H3; auto. apply H3; auto. Qed.
Theorem NoDup_repeat: forall (a:T) n, NoDup (repeat a n) <-> n<=1. Proof. intros; split; intros. destruct n; auto. destruct n; auto. simpl in H. inversion H. contradict H2; auto. inversion H; simpl. apply NoDup_cons; auto. apply NoDup_nil. inversion H1. simpl. apply NoDup_nil. Qed.

Theorem partition_Perm: forall f l, let (la,lb) := partition f l in Perm l (la++lb). Proof. induction l; simpl; intros; auto. destruct (f a); destruct (partition f l); simpl. apply Perm_Add with a l (l0++l1); auto. apply Perm_Add with a l (l0++l1); auto. clear IHl. induction l0; simpl; auto. Qed.
Theorem filter_app_Perm: forall f l, Perm l (filter f l++filter (fun x=>negb (f x)) l). Proof. induction l; simpl; auto. destruct (f a); simpl; eapply Perm_Add with (a:=a); eauto. generalize (filter f l) as m. induction m; simpl; auto. Qed.
Theorem fold_right_Perm: forall (o:T->T->T) a l m, (forall x y z, o (o x y) z = o x (o y z)) -> (forall x y, o x y = o y x) -> Perm l m -> fold_right o a l = fold_right o a m. Proof. intros. induction H1; simpl; auto. assert (Ha:forall l la, Add a0 l la -> fold_right o a la = o a0 (fold_right o a l)). clear -H H0. intros. induction H1; simpl; auto. rewrite IHAdd. rewrite <- H. rewrite <- H. f_equal; auto. rewrite Ha with l la; auto. rewrite Ha with m ma; auto. f_equal; auto. Qed.
Theorem filter_Add1: forall (a:T) l la f, f a=true -> Add a l la -> Add a (filter f l) (filter f la). Proof. intros. induction H0; simpl. rewrite H; auto. destruct (f x); auto. Qed.
Theorem filter_Add2: forall (a:T) l la f, f a=false -> Add a l la -> filter f l = filter f la. Proof. intros. induction H0; simpl. rewrite H; auto. destruct (f x); auto; f_equal; auto. Qed.
Theorem filter_Perm: forall l m, Perm l m -> forall f, Perm (filter f l) (filter f m). Proof. intros. induction H; simpl; auto. remember (f a) as b. destruct b. apply Perm_Add with a (filter f l) (filter f m); auto; apply filter_Add1; auto. rewrite <- filter_Add2 with (a:=a) (l:=l) (la:=la); auto. rewrite <- filter_Add2 with (a:=a) (l:=m) (la:=ma); auto. Qed.
Theorem filter_Forall: forall f (l:list T), (forall x, In x l->f x=true) -> filter f l = l. Proof. induction l; simpl; intros; auto. remember (f a) as b. destruct b; auto. f_equal; auto. absurd (false = true); auto. rewrite Heqb. auto. Qed.
Theorem filter_None: forall f (l:list T), (forall x, In x l -> f x=false) -> filter f l = nil. Proof. induction l; simpl; intros; auto. remember (f a) as b. destruct b; auto. absurd (true=false); auto. discriminate. rewrite Heqb. auto. Qed.
Theorem filter_ord: forall f g (l:list T), filter f (filter g l) = filter g (filter f l). Proof. induction l; simpl; auto. remember (f a) as b. remember (g a) as c. destruct b; destruct c; simpl; auto. rewrite <- Heqb. rewrite <- Heqc. f_equal; auto. rewrite <- Heqc; auto. rewrite <- Heqb; auto. Qed.
Theorem filter_and: forall f g (l:list T), filter (fun x=>andb (f x) (g x)) l = filter f (filter g l). Proof. induction l; simpl; auto. remember (f a) as b. remember (g a) as c. destruct b; destruct c; simpl; auto. rewrite <- Heqb; auto. f_equal; auto. rewrite <- Heqb; auto. Qed.
Theorem filter_app: forall f (l m:list T), filter f (l++m) = filter f l++filter f m. Proof. induction l; intros; simpl; auto. destruct (f a); simpl; auto. f_equal; auto. Qed.
Theorem filter_NoDup: forall f (l:list T), NoDup l -> NoDup (filter f l). Proof. induction l; simpl; intros; auto. inversion H. destruct (f a); auto. apply NoDup_cons; auto. contradict H2. apply filter_In in H2. destruct H2; auto. Qed.
Theorem filter_equiv: forall (f g:T->bool) l, (forall x, In x l ->f x=g x) -> filter f l = filter g l. Proof. induction l; simpl; intros; auto. remember (f a) as b. remember (g a) as c. destruct b; destruct c; auto. f_equal; auto. absurd (true=false); auto. discriminate. rewrite Heqb. rewrite Heqc. apply H; auto. absurd (false=true). discriminate. rewrite Heqb. rewrite Heqc; auto. Qed.
Definition dec2b {P:T->Prop} (P_dec:forall x,{P x}+{~P x}): T->bool := fun x=>if P_dec x then true else false.
Theorem dec2b_true: forall P P_dec x, dec2b (P:=P) P_dec x = true <-> P x. Proof. intros. unfold dec2b. destruct (P_dec x). split; auto. split; intros. inversion H. contradiction. Qed.
Theorem dec2b_false: forall P P_dec x, dec2b (P:=P) P_dec x = false <-> ~P x. Proof. intros. unfold dec2b. destruct (P_dec x). split; intros. inversion H. contradiction. split; intros; auto. Qed.

Definition Forall_dec: forall (P:T->Prop) l (P_dec:forall x, In x l->{P x}+{~P x}), {x|In x l & ~P x}+{Forall P l}. induction l; intros. right; auto. destruct IHl as  [[x H]|H]. intros. apply P_dec; auto. left; exists x; auto. destruct (P_dec a); auto. left; exists a; auto. Defined.
Definition Exists_dec: forall (P:T->Prop) l (P_dec:forall x, In x l->{P x}+{~P x}), {Exists P l}+{~Exists P l}. induction l; intros. right; intros C. inversion C. destruct (P_dec a); auto. destruct IHl; auto. right. intros C. inversion C; contradiction. Defined.
Definition findP : forall (P:T->Prop) (l:list T) (P_dec:forall x, In x l->{P x}+{~P x}), {x|In x l & P x}+{forall x, In x l ->~P x}. induction l; intros. right. intros. destruct H. destruct (P_dec a); auto. left; auto. exists a; auto. destruct IHl as [[x H]|H]; [|left; exists x|right]; auto. intros. destruct H0; auto. subst a; auto. Defined.

Theorem Rpair_list: forall (R:relation T) l, NoDup l -> (forall x, In x l->~R x x) -> (forall x, In x l->exists y, R x y/\In y l/\forall z,In z l->R x z->z=y) -> (forall x y, In x l->In y l->R x y->R y x) -> exists m, Perm l (map fst m++map snd m) /\ Forall (fun p=>R (fst p) (snd p)) m. Proof. intros R l. apply (Fix (well_founded_ltof (list T) (length (A:=T)))) with (P:=fun l=>NoDup l ->(forall x, In x l -> ~ R x x) ->(forall x, In x l -> exists y : T, R x y /\ In y l/\forall z,In z l->R x z->z=y) ->(forall x y, In x l -> In y l -> R x y -> R y x) -> exists m, Perm l (map fst m ++ map snd m) /\ Forall (fun p : T * T => R (fst p) (snd p)) m). clear l. intros l IH. intros. destruct l as [|a l]. exists nil; simpl; auto. destruct (H1 a) as [b [H4 [H5 H6]]]; auto. destruct H5. subst b; absurd (R a a); auto. destruct (Add_inv b l H3) as [l' H5]. inversion H. subst x l0.
  destruct (IH l') as [m [H11 H12]]; intros; auto. unfold ltof. apply Add_length in H5. simpl. rewrite H5; auto. apply NoDup_Add in H5. apply H5 in H10. destruct H10; auto. apply H0. right. apply Add_in with (x:=x) in H5. apply H5; auto. assert (In x l). apply (Add_in) with (x:=x) in H5. apply H5; auto.  destruct (H1 x) as [y [H11 [H12 H13]]]; auto. exists y; split; [|split]; auto. destruct H12. subst y. absurd (In b l'). apply NoDup_Add in H5. apply H5 in H10. destruct H10; auto. replace b with x; auto. apply Add_in with (x:=y) in H5. apply H5 in H12. destruct H12; auto. subst y. contradict H9. replace a with x; auto. destruct (H1 b) as [z [Ha [Hb Hc]]]; auto. rewrite Hc; auto. intros; apply H13; auto. right. apply Add_in with (x:=z) in H5. apply H5; auto. apply H2; auto; right. apply Add_in with (x:=x) in H5. apply H5; auto. apply Add_in with (x:=y) in H5. apply H5; auto. 
  exists ((a,b)::m). split; auto. apply Perm_Add with a l (map fst m++b::map snd m); simpl; auto. apply Perm_Add with b l' (map fst m++map snd m); auto. generalize (map fst m) as n. induction n; simpl; auto. Qed.

Variable T_eq_dec: forall x y:T, {x=y}+{x<>y}.

Definition add_inv: forall (a:T) l, {m|Add a m l}+{~In a l}. induction l. right; auto. destruct (T_eq_dec a0 a). left. subst a0. exists l; auto. destruct IHl as [[m H]|H]. left. exists (a0::m); auto. right. intros C. destruct C; contradiction. Defined.
Definition Perm_dec: forall l m, {Perm l m}+{~Perm l m}. induction l; intros. destruct m; [left|right]; auto. intros C. absurd (In t nil); auto. apply Perm_In with (t::m); auto. destruct (add_inv a m) as [[m' H]|H]. destruct (IHl m') as [H1|H1]; [left|right]; auto. apply Perm_Add with a l m'; auto. contradict H1. apply Perm_Add_inv with a (a::l) m; auto. right; contradict H. apply Perm_In with (a::l); auto; left; auto. Defined.

Theorem count_occ_Add_eq: forall (a:T) l la, Add a l la -> count_occ T_eq_dec la a = S(count_occ T_eq_dec l a). Proof. intros. induction H; simpl. destruct (T_eq_dec a a); auto. contradict n; auto. destruct (T_eq_dec x a); auto. Qed.
Theorem count_occ_Add_neq: forall a b l la, Add a l la -> b<>a -> count_occ T_eq_dec la b = count_occ T_eq_dec l b. Proof. intros. induction H; simpl. destruct (T_eq_dec a b); auto. contradict H0; auto. destruct (T_eq_dec x b); auto. Qed.
Theorem Perm__count_occ: forall l m, Perm l m -> forall x:T, count_occ T_eq_dec l x= count_occ T_eq_dec m x. Proof. intros. induction H; simpl; auto. destruct (T_eq_dec x a). subst x. rewrite count_occ_Add_eq with a l la; auto. rewrite count_occ_Add_eq with a m ma; auto. rewrite count_occ_Add_neq with a x l la; auto. rewrite count_occ_Add_neq with a x m ma; auto. Qed.
Theorem count_occ__Perm: forall l m, (forall x, count_occ T_eq_dec l x=count_occ T_eq_dec m x) -> Perm l m. Proof. induction l; intros. destruct m; auto. absurd (count_occ T_eq_dec (t::m) t = 0). simpl. destruct (T_eq_dec t t). discriminate. contradict n; auto. rewrite <- H. auto. destruct (add_inv a m) as [[m' H1]|H1]. apply Perm_Add with a l m'; auto. apply IHl. intros. destruct (T_eq_dec x a). subst x. cut (S(count_occ T_eq_dec l a)=S(count_occ T_eq_dec m' a)). intros. inversion H0; auto.
  rewrite <- count_occ_Add_eq with a m' m; auto. rewrite <- H. symmetry. apply count_occ_Add_eq; auto. rewrite <- count_occ_Add_neq with a x m' m; auto. rewrite <- count_occ_Add_neq with a x l (a::l); auto. contradict H1. destruct count_occ_In with (eq_dec:=T_eq_dec) (x:=a) (l:=m). apply H1. rewrite <- H. simpl. destruct (T_eq_dec a a); auto. apply le_n_S. apply le_O_n. contradict n; auto. Qed.
Theorem nodup_Add1: forall a l la, Add a l la -> ~In a l -> Add a (nodup T_eq_dec l) (nodup T_eq_dec la). Proof. intros. induction H; simpl. destruct (in_dec T_eq_dec a l); auto; contradiction. destruct (in_dec T_eq_dec x l); destruct (in_dec T_eq_dec x l'); auto. contradict n. apply Add_in with (x:=x) in H; apply H; auto. apply Add_in with (x:=x) in H. apply H in i. destruct i. subst x; contradict H0; auto. contradiction. apply Add_cons. apply IHAdd. contradict H0; auto. Qed.
Theorem nodup_Add2: forall a l la, Add a l la -> In a l -> Perm (nodup T_eq_dec l) (nodup T_eq_dec la). Proof. intros. induction H. simpl. destruct (in_dec T_eq_dec a l); auto; contradiction. simpl. destruct (in_dec T_eq_dec x l); destruct (in_dec T_eq_dec x l'). destruct H0; auto. subst x; auto. contradict n. apply Add_in with (x:=x) in H. apply H; auto. apply Perm_Add with x (nodup T_eq_dec l) (nodup T_eq_dec l); auto. apply nodup_Add1; auto. destruct H0. subst a; auto. apply Add_in with (x:=x) in H. apply H in i. destruct i; [subst x|]; contradiction.
  destruct H0. subst x. contradict n0. apply Add_in with (x:=a) in H. apply H; auto. apply Perm_Add with x (nodup T_eq_dec l) (nodup T_eq_dec l'); auto. Qed.
Theorem nodup_Perm: forall l m, Perm l m -> Perm (nodup T_eq_dec l) (nodup T_eq_dec m). Proof. intros. induction H; simpl; auto. destruct (in_dec T_eq_dec a l) as [H2|H2]. apply Perm_trans with (nodup T_eq_dec m). apply Perm_trans with (nodup T_eq_dec l); auto. apply Perm_sym. apply nodup_Add2 with a; auto. apply nodup_Add2 with a; auto. apply Perm_In with l; auto. apply Perm_Add with a (nodup T_eq_dec l) (nodup T_eq_dec m); auto; apply nodup_Add1; auto. contradict H2. apply Perm_In with m; auto. Qed.
Theorem nodup_incl_min: forall l m, incl l m -> length (nodup T_eq_dec l) <= length m. Proof. induction l; simpl; intros; auto. apply le_O_n. destruct (in_dec T_eq_dec a l). apply IHl. intros y H0. apply H; auto. destruct (add_inv a m) as [[m' H1]|H1]. rewrite Add_length with T a m' m; auto.  simpl. apply le_n_S. apply IHl. intros y Hy. apply Add_in with (x:=y) in H1. cut (In y m). intros. apply H1 in H0. destruct H0; auto. subst y; contradiction. apply H. auto. contradict H1. apply H; auto. Qed.

Theorem remove_length: forall l a, length (remove T_eq_dec a l)<=length l. Proof. induction l; simpl; intros; auto. destruct (T_eq_dec a0 a); auto. simpl. apply le_n_S; auto. Qed.
Theorem remove_notIn: forall l a, ~In a l -> remove T_eq_dec a l=l. Proof. induction l; simpl; intros; auto. destruct (T_eq_dec a0 a); auto. contradict H; subst a0; auto. f_equal. apply IHl. contradict H; auto. Qed.
Theorem remove_Add: forall a l m, Add a l m ->remove T_eq_dec a l = remove T_eq_dec a m. Proof. intros. induction H; simpl. destruct (T_eq_dec a a); auto. contradict n; auto. destruct (T_eq_dec a x); auto; f_equal; auto. Qed.
Definition count_list: forall l, {pl| Perm l (fold_right (fun p=>app (repeat (fst p) (snd p))) nil pl) /\ NoDup (map fst pl) /\ Forall (fun x=>x<>0) (map snd pl)}. apply (Fix (well_founded_ltof (list T) (length (A:=T)))). intros l IH. destruct l. exists nil; simpl; auto. split; auto. split; auto. apply NoDup_nil. destruct (IH (remove T_eq_dec t l)) as [m [H1 [H2 H3]]]. unfold ltof. simpl. apply le_n_S. apply remove_length. exists ((t, S(count_occ T_eq_dec l t))::m). simpl. split. apply Perm_cons. remember (count_occ T_eq_dec l t) as c. revert H1 Heqc. clear -l. revert l. induction c; simpl; intros. rewrite remove_notIn in H1. apply H1. destruct count_occ_not_In with (eq_dec:=T_eq_dec) (l:=l) (x:=t). apply H0; auto.
  destruct (add_inv t l) as [[l' H2]|H2]. apply Perm_Add with t l' (repeat t c++fold_right (fun p=>app (repeat (fst p) (snd p))) nil m); auto. apply IHc. rewrite remove_Add with t l' l; auto. rewrite count_occ_Add_eq with t l' l in Heqc; auto. contradict H2. destruct (count_occ_In T_eq_dec l t). apply H0. rewrite <- Heqc; auto. apply le_n_S. apply le_0_n. split. apply NoDup_cons. assert (~In t (remove T_eq_dec t l)). apply remove_In.
  contradict H. eapply Perm_In. apply Perm_sym. eapply H1. apply in_map_iff in H. destruct H as [[n c] [H4 H5]]. simpl in H4. subst n. clear -H3 H5. induction m. destruct H5. simpl. apply in_or_app. destruct H5; [left|right]. subst a. simpl. destruct c; simpl; auto. inversion H3. auto. apply IHm. inversion H3; auto. auto. auto. apply Forall_cons; auto. Defined.

Inductive ForallR (R: relation T): list T->Prop:=
|ForallR_nil: ForallR R nil
|ForallR_cons: forall x l, ForallR R l -> (forall y, In y l->R x y) -> ForallR R (x::l)
.
Inductive NoRDup (R:relation T): list T->Prop:=
|NoRDup_nil: NoRDup R nil
|NoRDup_cons: forall x l, NoRDup R l-> (forall y, In y l->~R x y) -> NoRDup R (x::l)
.
Hint Constructors ForallR NoRDup.
Theorem ForallR_Add_rev: forall (R:relation T) a l m, (forall x y, R x y->R y x) -> Add a l m -> ForallR R m -> ForallR R l /\ forall x, In x l -> R a  x. Proof. intros. induction H0; auto. inversion H1. subst x l0. split; auto. inversion H1. subst x0 l0. destruct (IHAdd H4). split; auto. apply ForallR_cons; auto. intros. apply Add_in with (x:=y) in H0. apply H5. apply H0; auto. intros y Hy. destruct Hy. subst y. apply H. apply H5. apply Add_in with (x:=a) in H0; apply H0; auto. apply H3; auto. Qed.
Theorem ForallR_Add: forall (R:relation T) a l m, (forall x y, R x y->R y x) -> Add a l m -> ForallR R l -> (forall x, In x l->R a x) -> ForallR R m. Proof. intros. induction H0; auto. apply ForallR_cons; auto. apply IHAdd; auto. inversion H1; auto. intros. apply Add_in with (x:=y) in H0. apply H0 in H3. destruct H3; auto. subst y. apply H. auto. inversion H1. auto. Qed.
Theorem ForallR_Perm: forall (R:relation T) l m, (forall x y, R x y->R y x) -> Perm l m -> ForallR R l -> ForallR R m. Proof. intros. revert H1. induction H0; intros; auto. destruct ForallR_Add_rev with R a l la; auto. apply ForallR_Add with a m; auto. intros. apply H5. apply Perm_In with m; auto. Qed.
Theorem NoRDup_Add_rev: forall (R:relation T) a l m, (forall x y, R x y->R y x) -> Add a l m -> NoRDup R m -> NoRDup R l /\ forall x, In x l -> ~R a x. Proof. intros. induction H0. inversion H1; auto. inversion H1. subst x0 l0. destruct (IHAdd H4). split. apply NoRDup_cons; auto. intros. apply Add_in with (x:=y) in H0; auto. apply H5. apply H0; auto. intros y Hy. destruct Hy. subst y. intros C. apply H in C. contradict C. apply H5. apply Add_in with (x:=a) in H0. apply H0; auto. auto. Qed.
Theorem NoRDup_Add: forall (R:relation T) a l m, (forall x y, R x y->R y x) -> Add a l m -> NoRDup R l -> (forall x, In x l->~R a x) -> NoRDup R m. Proof. intros. induction H0; auto. apply NoRDup_cons; auto. apply IHAdd; auto. inversion H1; auto. intros. apply Add_in with (x:=y) in H0. apply H0 in H3. destruct H3; auto. subst y. intros C. apply H in C. contradict C. auto. inversion H1. auto. Qed.
Theorem NoRDup_Perm: forall (R:relation T) l m, (forall x y, R x y->R y x) -> Perm l m -> NoRDup R l -> NoRDup R m. Proof. intros. revert H1. induction H0; intros; auto. destruct NoRDup_Add_rev with R a l la; auto. apply NoRDup_Add with a m; auto. intros. apply H5. apply Perm_In with m; auto. Qed.


(* Sort *)
Variable R: relation T.
Variable R_ord: order T R.
Variable R_fullord: forall x y, R x y \/ R y x.
Variable R_dec: forall x y, {R x y}+{~R x y}.

Inductive Sorted: list T -> Prop :=
|Sorted_nil: Sorted nil
|Sorted_one: forall a, Sorted (a::nil)
|Sorted_cons: forall a b l, R a b -> Sorted (b::l) -> Sorted (a::b::l)
.
Hint Constructors Sorted.

Definition Sorted_dec: forall l, {Sorted l}+{~Sorted l}. induction l. left; auto. destruct l as [|b l]. left; auto. destruct IHl; [destruct (R_dec a b); [left|right]|right]; auto; contradict n; inversion n; auto. Defined.
Theorem Sorted_cons_rev: forall a l, Sorted (a::l) -> Sorted l. Proof. intros. inversion H; auto. Qed.
Theorem Sorted_min_cons: forall a l, Sorted l -> (forall x, In x l -> R a x) -> Sorted (a::l). Proof. intros. induction H; auto. Qed.
Theorem Sorted_min: forall a l, Sorted (a::l) -> forall x, In x (a::l) -> R a x. Proof. destruct R_ord. induction l; simpl; intros. destruct H0; [subst x|]; auto. destruct H0. destruct H0. subst x; auto. destruct H0. subst x. inversion H; auto. apply IHl; auto. inversion H. subst a1 a0 l0. inversion H5; auto. apply Sorted_cons; auto. apply ord_trans with b; auto. Qed.
Theorem Sorted_Perm_uniq: forall l m, Sorted l -> Sorted m -> Perm l m -> l=m. Proof. induction l; simpl; intros. destruct m; auto. absurd (In t nil); auto. apply Perm_In with (t::m); auto. destruct m as [|b m]. absurd (In a nil); auto. apply Perm_In with (a::l); auto. cut (a=b); intros. subst b. f_equal. apply IHl; try apply Sorted_cons_rev with a; auto. apply Perm_Add_inv with a (a::l) (a::m); auto. destruct R_ord. apply ord_antisym. apply Sorted_min with l; auto. apply Perm_In with (b::m); auto. apply Sorted_min with m; auto. apply Perm_In with (a::l); auto. Qed.
Theorem Sorted_app: forall l a m, Sorted l -> Sorted (a::m) -> (forall x, In x l ->R x a) -> Sorted (l++a::m). Proof. intros l a m H. induction H; simpl; intros; auto. Qed.
Definition insert_one: forall a l,  Sorted l -> {m|Add a l m & Sorted m}. induction l; intros. exists (a::nil); auto. destruct R_ord. destruct (R_dec a a0). exists (a::a0::l); auto. destruct IHl as [m H1 H2]. apply Sorted_cons_rev with a0; auto. exists (a0::m); auto. apply Sorted_min_cons; auto. intros. apply Add_in with (x:=x) in H1. apply H1 in H0. destruct H0. subst x. destruct (R_fullord a0 a); auto; contradiction. apply Sorted_min with l; auto. Defined.
Definition insert_sort: forall l, {m|Sorted m & Perm l m}. induction l. exists nil; auto. destruct IHl as [m H1 H2]. destruct (insert_one a H1) as [m' H3 H4]; auto. exists m'; auto. apply Perm_Add with a l m; auto. Defined.
Definition quick_sort: forall l, {m|Sorted m & Perm l m}. apply (Fix (well_founded_ltof (list T) (length (A:=T)))). intros l IH. destruct l as [|a l]. exists nil; auto. assert (Perm l (filter (fun x=>if R_dec x a then true else false) l++filter (fun x=>negb (if R_dec x a then true else false)) l)). apply filter_app_Perm. destruct (IH (filter (fun x=>if R_dec x a then true else false) l)) as [ma H1 H2]. unfold ltof. simpl. apply le_n_S. apply Perm_length in H. rewrite H. rewrite app_length. apply le_plus_l. destruct (IH (filter (fun x=>negb (if R_dec x a then true else false)) l)) as [mb H3 H4]. unfold ltof. simpl. apply le_n_S. apply Perm_length in H. rewrite H. rewrite app_length. apply le_plus_r.
  exists (ma++a::mb). apply Sorted_app; auto. apply Sorted_min_cons; auto. intros. apply Perm_sym in H4. apply Perm_In with (a:=x) in H4; auto. apply filter_In in H4. destruct H4. destruct (R_dec x a). inversion H5. destruct (R_fullord x a); auto; contradiction. intros. apply Perm_sym in H2. apply Perm_In with (a:=x) in H2; auto. apply filter_In in H2. destruct H2. destruct (R_dec x a); auto. inversion H5. apply Perm_Add with a l (ma++mb); auto. eapply Perm_trans. eapply H. apply Perm_app; auto. clear -ma. induction ma; simpl; auto. Defined.
Definition nat_eq_dec: forall x y:nat, {x=y}+{x<>y}. induction x; intros. destruct y; [left|right]; auto. destruct y. right; auto. destruct (IHx y); [left|right]; auto. Defined.
Definition half_split: forall l, {la:list T & {lb|Perm l (la++lb) & length la = length lb \/ length la=S (length lb)}}. induction l. exists nil; exists nil; simpl; auto. destruct IHl as [la [lb H1 H2]]. destruct (nat_eq_dec (length la) (length lb)). exists (a::la); exists lb; simpl. apply Perm_Add with a l (la++lb); auto. right; auto. exists la; exists (a::lb). apply Perm_Add with a l (la++lb); auto. clear -la; induction la; simpl; auto. destruct H2. contradiction. left. rewrite H; auto. Defined.
Definition merge': forall p, Sorted (fst p)->Sorted (snd p)->{n|Sorted n & Perm n (fst p++snd p)}. intros p. apply (Fix (well_founded_ltof (list T*list T) (fun p=>length (fst p)+length (snd p)))) with (P:=fun p=>Sorted (fst p)->Sorted (snd p)->{n|Sorted n & Perm n (fst p++snd p)}). clear p. intros p IH. destruct p as [la lb]. simpl. intros. destruct la as [|a la]. exists lb; auto. destruct lb as [|b lb]. rewrite app_nil_r. exists (a::la); auto. destruct (R_dec a b). destruct (IH (la,b::lb)) as [m H1 H2]. unfold ltof. simpl. auto. simpl; apply Sorted_cons_rev with a; auto. simpl; auto. exists (a::m). apply Sorted_min_cons; auto. intros. apply Perm_In with (a:=x) in H2; auto. apply in_app_or in H2. destruct H2. apply Sorted_min with la; auto. destruct R_ord. apply ord_trans with b; auto. apply Sorted_min with lb; auto.
  simpl. apply Perm_Add with a m (la++b::lb); auto. destruct R_ord. destruct (IH (a::la, lb)) as [m H1 H2]; auto. unfold ltof. simpl. rewrite <- plus_n_Sm; auto. apply Sorted_cons_rev with b; auto. exists (b::m). destruct (R_fullord a b). contradiction. apply Sorted_min_cons; auto. intros. apply Perm_In with (a:=x) in H2; auto. apply in_app_or in H2. destruct H2. apply ord_trans with a; auto. apply Sorted_min with la; auto. apply Sorted_min with lb; auto. apply Perm_Add with b m ((a::la)++lb); auto. generalize (a::la) as l. induction l; simpl; auto. Defined.
Definition merge: forall l m, Sorted l -> Sorted m -> {n|Sorted n & Perm n (l++m)}. intros. destruct (merge' (l,m)) as [n H1 H2]; auto. exists n; auto. Defined.
Definition merge_sort: forall l, {m|Sorted m & Perm l m}. apply (Fix (well_founded_ltof (list T) (length (A:=T)))). intros l IH. destruct (half_split l) as [la [lb H1 H2]]. destruct lb as [|b lb]. exists la. destruct la; auto. destruct la; auto. simpl in H2. destruct H2; inversion H. rewrite app_nil_r in H1; auto. destruct (IH la) as [ma H3 H4]. unfold ltof. apply Perm_length in H1. rewrite H1. rewrite app_length. simpl. rewrite <- plus_n_Sm. apply le_n_S. apply le_plus_l. destruct (IH (b::lb)) as [mb H5 H6]. unfold ltof. apply Perm_length in H1. rewrite H1. rewrite app_length. destruct la. simpl in H2. destruct H2; inversion H. simpl. apply le_n_S. apply le_plus_r. destruct (merge H3 H5) as [m H7 H8]. exists m; auto. apply Perm_trans with (la++b::lb); auto. apply Perm_trans with (ma++mb); auto. apply Perm_app; auto. Defined.

End ListType.

Section ListType2.
Variable T U V:Type.

Hint Constructors NoDup Perm Add.
Theorem NoDup_map_inv: forall (f:T->U) l, NoDup (map f l) -> NoDup l. Proof. induction l; simpl; intros; auto. inversion H. apply NoDup_cons; auto. contradict H2. apply in_map_iff. exists a; auto.  Qed.
Theorem NoDup_map: forall (f:T->U) l, NoDup l -> (forall x y, In x l -> In y l -> f x=f y -> x=y) -> NoDup (map f l). Proof. induction l; simpl; intros; auto. inversion H. apply NoDup_cons; auto. contradict H3. apply in_map_iff in H3. subst x l0. destruct H3 as [x [H6 H5]]. replace a with x; auto. Qed.
Theorem NoDup_flat_map: forall (f:T->list U) l, NoDup l -> (forall x, In x l->NoDup (f x)) -> (forall x y z, In x l->In y l->In z (f x)->In z (f y)->x=y) -> NoDup (flat_map f l). Proof. induction l; intros; simpl; auto. inversion H. subst x l0. assert (NoDup (f a)). apply H0; left; auto. remember (f a) as m. assert (forall y, In y m->~In y (flat_map f l)). intros. intros C. apply in_flat_map in C. destruct C as [x [H6 H7]]. subst m. assert (a=x). apply H1 with y; auto. left; auto. right; auto. subst a. contradiction. assert (NoDup (flat_map f l)). apply IHl; auto. intros. apply H0. right; auto. intros. apply H1 with z; auto; right; auto. clear -H2 H3 H6. induction m; simpl; auto. apply NoDup_cons. intros C. apply in_app_or in C. destruct C. inversion H2; contradiction. contradict H; apply H3; left; auto. apply IHm. inversion H2; auto. intros. apply H3; right; auto. Qed.
Theorem map_Add: forall (f:T->U) l a la, Add a l la -> Add (f a) (map f l) (map f la). Proof. intros. induction H; simpl; auto. Qed.
Hint Resolve map_Add.
Theorem Perm_map: forall (f:T->U) l m, Perm l m -> Perm (map f l) (map f m). Proof. intros. induction H; simpl; auto. apply Perm_Add with (f a) (map f l) (map f m); auto. Qed.
Theorem Perm_map_inv: forall (f:T->U) l m, (forall x y, f x=f y -> x=y) -> Perm (map f l) (map f m) -> Perm l m. Proof. induction l; simpl; intros. destruct m; auto. simpl in H0. absurd (In (f t) nil); auto. apply Perm_In with (f t::map f m); auto. apply Perm_sym; auto. left; auto. destruct Add_inv with (a:=a) (l:=m) as [m' H1]. cut (In (f a) (map f m)); intros. apply in_map_iff in H1. destruct H1 as [y [H2 H3]]. replace a with y; auto. apply Perm_In with (f a::map f l); auto. left; auto. apply Perm_Add with a l m'; auto. apply IHl; auto. apply Perm_Add_inv with (f a) (f a::map f l) (map f m); auto. Qed.
Theorem filter_map: forall (m:T->U) (f:U->bool) l, filter f (map m l) = map m (filter (fun x=>f (m x)) l). Proof. induction l; simpl; auto. destruct (f (m a)); simpl; auto. f_equal; auto. Qed.
Theorem flat_map_app: forall (f:T->list U) l m, flat_map f (l++m) = flat_map f l ++flat_map f m. Proof. induction l; intros; simpl; auto. rewrite <- app_assoc. f_equal; auto. Qed.
Theorem Perm_flat_map: forall (f:T->list U) l m, Perm l m -> Perm (flat_map f l) (flat_map f m). Proof. induction l; intros. destruct m; simpl; auto. absurd (In t nil); auto. apply Perm_In with (t::m). apply Perm_sym; auto. left; auto. simpl. destruct (Add_inv a m) as [m' H1]. apply Perm_In with (a::l); auto. left; auto. destruct (Add_split H1) as [m1 [m2 [H2 H3]]]. subst m m'. rewrite flat_map_app. simpl. apply Perm_trans with (f a++flat_map f m1++flat_map f m2). apply Perm_app; auto. apply Perm_refl. rewrite <- flat_map_app. apply IHl. apply Perm_Add_inv with a (a::l) (m1++a::m2); auto. repeat rewrite app_assoc. apply Perm_app; auto. apply Perm_app_swap. apply Perm_refl. Qed.
Theorem map_repeat: forall (f:T->U) a n, map f (repeat a n) = repeat (f a) n. Proof. induction n; simpl; auto. f_equal; auto. Qed.

Definition all_pair (f:T->U->V) l m : list V := fold_right (fun x=>app (map (f x) m)) nil l.
Theorem all_pair_spec1: forall f l m x y, In x l -> In y m -> In (f x y) (all_pair f l m). Proof. induction l; simpl; intros; auto. apply in_or_app. destruct H; [left|right]; auto. subst x. apply in_map_iff. exists y; auto. Qed.
Theorem all_pair_spec2: forall f l m z, In z (all_pair f l m) -> exists x y, In x l /\ In y m /\ z=f x y. Proof. induction l; simpl; intros. destruct H. apply in_app_or in H. destruct H. apply in_map_iff in H. destruct H as [y [H1 H2]]. subst z. exists a. exists y; auto. destruct (IHl m z H) as [x [y [H1 [H2 H3]]]]. subst z. exists x. exists y; auto. Qed.
Definition maxf: forall (f:T->nat) l, {x|In x l & forall y, In y l->f y<=f x}+{l=nil}. induction l; [right|left]; auto. destruct IHl as [[x H1 H2]|H1]. destruct (le_lt_dec (f a) (f x)). exists x; auto. right; auto. intros. destruct H; auto. subst y; auto. exists a. left; auto. intros. destruct H; auto. subst y; auto. apply le_trans with (f x); auto. apply lt_le_weak; auto. subst l. exists a. left; auto. intros. destruct H. subst a; auto. destruct H. Defined.
Definition minf: forall (f:T->nat) l, {x|In x l & forall y, In y l->f x<=f y}+{l=nil}. induction l; [right|left]; auto. destruct IHl as [[x H1 H2]|H1]. destruct (le_lt_dec (f a) (f x)). exists a; auto. left; auto. intros. destruct H; auto. subst y; auto. apply le_trans with (f x); auto. exists x.  right; auto. intros. destruct H; auto. subst y; auto. apply lt_le_weak; auto. subst l. exists a. left; auto. intros. destruct H. subst a; auto. destruct H. Defined.
 
End ListType2.

Definition splits: forall {T:Type} (l: list T), {pl| forall p, l=fst p++snd p <-> In p pl & NoDup pl}. induction l as [|a l]. exists ((nil,nil)::nil). intros; split; intros. destruct p. simpl in H. destruct l. destruct l0. left; auto. inversion H. inversion H. destruct H. subst p. auto. destruct H. apply NoDup_cons; auto. apply NoDup_nil. destruct IHl as [pl H1 Hn]. exists ((nil, a::l)::map (fun p=> (a::fst p, snd p)) pl). intros; split; intros. destruct p as [t u]. simpl in H. destruct t. left. simpl in H. subst u. auto. inversion H. subst a l. right. apply in_map_iff. exists (t0,u). split; auto. apply H1; auto. destruct H. subst p. auto. apply in_map_iff in H. destruct H as [[t u] [H2 H3]]. subst p. simpl. f_equal. apply H1 in H3. subst l; auto. apply NoDup_cons. intros C. apply in_map_iff in C. destruct C as [[x y] [H2 H3]]. inversion H2. apply NoDup_map; auto. intros. destruct x. destruct y. simpl in H2. inversion H2. auto. Defined.

Hint Constructors Swap Perm Add Sorted ForallR NoRDup.
Hint Resolve in_eq in_cons Swap_sym Perm'_sym Perm'_refl Perm'_trans Swap_Perm'.
Hint Resolve Perm'_cons Perm'_cons_Add.
Hint Resolve Perm_In Perm_length Perm__Perm' Perm_refl Perm_sym Perm_cons.
Hint Resolve Add_insert Add_dual Perm_Add_inv Perm_trans Perm'__Perm.
Hint Resolve Perm_rev app_Add Perm_app_swap Perm_app Perm_app_rev NoDup_incl_Perm NoDup_incl_each_Perm count_occ_Add_eq count_occ_Add_neq Perm__count_occ count_occ__Perm.
Hint Resolve partition_Perm filter_app_Perm fold_right_Perm filter_Add1 filter_Add2 filter_Perm filter_Forall filter_None filter_ord filter_and.
Hint Resolve filter_app filter_NoDup filter_equiv dec2b_true dec2b_false Rpair_list.
Hint Resolve NoDup_incl_length NoDup_map_inv NoDup_map NoDup_flat_map NoDup_repeat map_Add Perm_map Perm_map_inv filter_map flat_map_app Perm_flat_map map_repeat.
Hint Resolve count_occ_Add_eq count_occ_Add_neq Perm__count_occ count_occ__Perm nodup_Add1 nodup_Add2 nodup_Perm nodup_incl_min ForallR_Add_rev ForallR_Add ForallR_Perm NoRDup_Add_rev NoRDup_Add NoRDup_Perm.
Hint Resolve Sorted_cons_rev Sorted_min_cons Sorted_Perm_uniq Sorted_app.
Hint Resolve all_pair_spec1 all_pair_spec2.

