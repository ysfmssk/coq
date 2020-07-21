Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.

Set Implicit Arguments.

Hint Resolve le_plus_r le_plus_l le_n_S le_S_n.

Section CharType.

Variable C: Set.
Variable C_eq_dec: forall x y:C, {x=y}+{x<>y}.

Inductive RegExp: Set:=
| Rnil: RegExp
| Rchar: C -> RegExp
| Rcons: RegExp -> RegExp -> RegExp
| Ror: RegExp -> RegExp -> RegExp
| Rstar: RegExp -> RegExp
.

Inductive Racc: RegExp -> list C -> Prop:=
|RAchar : forall c, Racc (Rchar c) (c::nil)
|RAcons : forall l m r s, Racc r l -> Racc s m -> Racc (Rcons r s) (l++m)
|RAor1  : forall l r s, Racc r l -> Racc (Ror r s) l
|RAor2  : forall l r s, Racc s l -> Racc (Ror r s) l
|RAstar1: forall r, Racc (Rstar r) nil
|RAstar2: forall r l m, l<>nil -> Racc r l -> Racc (Rstar r) m -> Racc (Rstar r) (l++m)
.
Hint Constructors Racc.

Definition Remp:=Rstar Rnil.
Theorem Remp_spec: forall w, Racc Remp w<-> w=nil. Proof. unfold Remp. intros; split; intros. inversion H; auto. inversion H2. subst w; auto. Qed.
Theorem Rnil_spec: forall w, ~Racc Rnil w. Proof. intros w D. inversion D. Qed.
Theorem Rchar_spec: forall w c, Racc (Rchar c) w <-> w=c::nil. Proof. intros; split; intros. inversion H; auto. subst w; auto. Qed.
Definition Rword w:=fold_right (fun c r=>Rcons (Rchar c) r) Remp w.
Theorem Rword_spec: forall w s, Racc (Rword w) s <-> s=w. Proof. induction w; intros; simpl; split; intros. apply Remp_spec; auto. apply Remp_spec; auto. inversion H. inversion H2. simpl. f_equal. apply IHw; auto. subst s. replace (a::w) with ((a::nil)++w); auto. apply RAcons; auto. apply IHw; auto. Qed.

Definition Racc_dec: forall r l, {Racc r l}+{~Racc r l}. intros r l. revert r. apply (Fix (well_founded_ltof (list C) (length (A:=C)))) with (P:=fun l=>forall r, {Racc r l}+{~Racc r l}). clear l. intros l IH r. assert (forall r, {Racc r nil}+{~Racc r nil}). clear r. intros. induction r. right. intros D; inversion D. right. intros D; inversion D. destruct IHr1; [destruct IHr2; [left|right]| right]; auto. replace nil with (nil (A:=C)++nil); auto. contradict n. inversion n. destruct l0. destruct m; auto. inversion H1. contradict n. inversion n. destruct l0. destruct m; auto. inversion H1. inversion H1. destruct IHr1; [left|destruct IHr2; [left|right]]; auto. intros D. inversion D; contradiction. left; auto.
  induction r. right. intros D; inversion D. destruct l. right. intros D; inversion D. destruct l. destruct (C_eq_dec c0 c); [left|right]. subst c0; auto. contradict n; inversion n; auto. right. intros D; inversion D.
  destruct (splits l) as [pl H0]. destruct (findP (fun p=>Racc r1 (fst p)/\Racc r2 (snd p)) pl). intros. apply H0 in H1. destruct x as [t u]. simpl in H1. subst l. simpl. destruct t. destruct (H r1); [|right]. destruct IHr2; [left|right]; auto. contradict n; destruct n; auto. contradict n; destruct n; auto. destruct u. destruct (H r2); [|right]. rewrite app_nil_r in IHr1. destruct IHr1; [left|right]; auto. contradict n; destruct n; auto. contradict n; destruct n; auto. destruct (IH (c::t)) with (r:=r1); [| |right]. unfold ltof. rewrite app_length. simpl. rewrite <- plus_n_Sm; auto. destruct (IH (c0::u)) with (r:=r2); [|left|right]; auto. unfold ltof. rewrite app_length. simpl. rewrite <- plus_n_Sm; auto. contradict n; destruct n; auto. contradict n; destruct n; auto.
  destruct s as [x H1 [H2 H3]]. left. apply H0 in H1. subst l. auto. right. intros D. inversion D. subst r1 r2 l. absurd (Racc r l0/\Racc s m); auto. replace l0 with (fst (l0,m)); auto. replace m with (snd (l0,m)); auto. apply n; auto. apply H0. simpl; auto.
  destruct IHr1; [left|destruct IHr2; [left|right]]; auto. intros D; inversion D; contradiction.
  destruct (splits l) as [pl H0]. destruct (findP (fun p=>fst p<>nil/\Racc r (fst p)/\Racc (Rstar r) (snd p)) pl) as [[x H1 H2]|H1]; [|left|]. intros. apply H0 in H1. destruct x as [t u]. simpl in H1. subst. simpl. destruct t. right. intros D. destruct D. contradict H1; auto. destruct u. rewrite app_nil_r in IHr. destruct IHr; [left|right]; auto. split; auto. intros D; inversion D. contradict n. destruct n. destruct H2; auto. destruct (IH (c::t)) with (r:=r); [| |right]. unfold ltof. rewrite app_length. simpl. rewrite <- plus_n_Sm; auto. destruct (IH (c0::u)) with (r:=Rstar r); [|left|right]; auto. unfold ltof. rewrite app_length. simpl. rewrite <- plus_n_Sm; auto. split; auto. intros D; inversion D. contradict n. destruct n. destruct H2; auto. contradict n. destruct n. destruct H2; auto.
  apply H0 in H1. destruct x as [t u]. simpl in H1. subst l. simpl in H2. destruct H2. destruct H2. auto. destruct l; [left|right]; auto. intros D. inversion D. subst r0. absurd (l0<>nil/\Racc r l0/\Racc (Rstar r) m); auto. replace l0 with (fst (l0,m)); auto. replace m with (snd (l0,m)); auto. apply H1. apply H0. rewrite <- H3; auto. Defined.

Definition Rincl: relation RegExp:= fun r s=>forall w, Racc r w -> Racc s w.
Definition Req: relation RegExp:= fun r s=> Rincl r s /\ Rincl s r.

Theorem Rstar_app: forall r l m, Racc (Rstar r) l -> Racc (Rstar r) m -> Racc (Rstar r) (l++m). Proof. intros r l. apply (Fix (well_founded_ltof (list C) (length (A:=C)))) with (P:=fun l=>forall m, Racc (Rstar r) l->Racc (Rstar r) m ->Racc (Rstar r) (l++m)). clear l. intros l IH m H H0. inversion H; auto. rewrite <- app_assoc. apply RAstar2; auto. apply IH; auto. unfold ltof. subst l. rewrite app_length. destruct l0. contradict H2; auto. simpl; auto. Qed.
Theorem Rstar_one: forall r w, Racc r w -> Racc (Rstar r) w. Proof. intros. destruct w; auto. rewrite <- app_nil_r; apply RAstar2; auto. intros D; inversion D. Qed.
Theorem Rstar_incl: forall r s, Rincl r s -> Rincl (Rstar r) (Rstar s). Proof. intros. intros w. apply (Fix (well_founded_ltof (list C) (length (A:=C)))) with (P:=fun w=>Racc (Rstar r) w ->Racc (Rstar s) w). clear w. intros w IH H0. inversion H0; auto. apply RAstar2; auto. apply IH; auto. unfold ltof. subst w. rewrite app_length. destruct l. contradict H2;auto. simpl; auto. Qed.
Hint Resolve Rstar_app Rstar_one Rstar_incl.

Theorem Rstar_dual: forall r, Req (Rstar r) (Rstar (Rstar r)). Proof. intros. split; intros w H. auto. revert H. apply (Fix (well_founded_ltof (list C) (length (A:=C)))) with (P:=fun w=>Racc(Rstar(Rstar r)) w->Racc(Rstar r) w). clear w. intros w IH H. inversion H; auto. subst w r0. inversion H2. contradict H1; subst l; auto. rewrite <- app_assoc. apply RAstar2; auto. apply Rstar_app; auto. apply IH; auto. unfold ltof. rewrite app_length. destruct l. destruct l0. contradict H4; auto. inversion H7. simpl. auto. Qed.
Theorem Rstar_dual2: forall r, Req (Rstar r) (Rcons (Rstar r) (Rstar r)). Proof. intros; split; intros w H. rewrite <- app_nil_r; auto. inversion H. apply Rstar_app; auto. Qed.
Theorem Rstar_or: forall r s, Req (Rstar (Ror r s)) (Rstar (Rcons (Rstar r) (Rstar s))). Proof. intros. split; intros w H; revert H. apply (Fix (well_founded_ltof (list C) (length (A:=C)))) with (P:=fun w=>Racc (Rstar (Ror r s)) w -> Racc (Rstar (Rcons (Rstar r) (Rstar s))) w). clear w. intros w IH H. inversion H; auto. subst w r0. apply RAstar2; auto. inversion H2. rewrite <- app_nil_r. apply RAcons; auto. rewrite <- app_nil_l; auto. apply IH; auto. unfold ltof. rewrite app_length. destruct l. contradict H1; auto. simpl; auto.
  apply (Fix (well_founded_ltof (list C) (length (A:=C)))) with (P:=fun w=>Racc (Rstar (Rcons (Rstar r) (Rstar s))) w->Racc (Rstar (Ror r s)) w). clear w. intros w IH H. inversion H; auto. subst w r0. apply Rstar_app. inversion H2. subst r0 s0 l. apply Rstar_app. revert H5. apply Rstar_incl. intros w Hw. auto. revert H7. apply Rstar_incl. intros w Hw. auto. apply IH; auto. unfold ltof. destruct l. contradict H1; auto. rewrite app_length. simpl. auto. Qed.

End CharType.
