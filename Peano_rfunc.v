Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Wellfounded.
Require Import list_util.
Require Import ModEq.
Require Import Peano_LQ.
Require Import Peano_Func.

Set Implicit Arguments.

(* Primitive recursive functions *)
Inductive PRfunc: nat -> (list nat->nat) -> Prop :=
|PRZero : PRfunc 0 (fun _ => 0)
|PRSucc : PRfunc 1 (fun l => match l with |nil => 0 (* dummy *) |a::_ => S a end)
|PRProj : forall i n, i<n -> PRfunc n (fun l => nth i l 0)
|PRComp : forall f gs n, PRfunc (length gs) f -> (forall x, In x gs->PRfunc n x) -> PRfunc n (fun a=>f (map (fun g=>g a) gs))
|PRRecu : forall n f g, PRfunc n f -> PRfunc (S (S n)) g -> PRfunc (S n) (fun l=> match l with |nil=>0 (*dummy*) |i::l'=> (fix rec (n:nat) := match n with |0=>f l' |S n'=>g (rec n'::n'::l') end) i end)
.
Hint Constructors PRfunc.
(*
Definition PRfunc_Func: forall f n, PRfunc n f -> {F:Func|WFFunc n F & forall ns p, n=length ns -> Inf p (FuncT F (map n2t ns) == n2t (f ns))}. intros f n H. induction H.
  exists FZero; auto. intros. destruct ns; auto. inversion H. exists (FSucc); auto. intros. destruct ns. inversion H. destruct ns; auto. inversion H. exists (FProj i); auto. intros. apply FProj_spec. rewrite map_length; subst n; auto. replace Zero with (n2t 0); auto. apply map_nth.
  destruct IHPRfunc as [F H1 H2]. destruct MapR_build2 with (l:=gs) (R1:=fun (_:list nat->nat) F=>WFFunc n F) (R2:=fun f F=>forall ns p,n=length ns->Inf p (FuncT F (map n2t ns)==n2t (f ns))) as [Gs H3]. intros; auto. assert (WFFunc n (FComp F Gs)). apply WFF_Comp. replace (length Gs) with (length gs); auto. apply MapR_length in H3; auto.
  apply Forall_forall. intros g H4. apply in_MapR_2 with (x:=g) in H3; auto. destruct H3 as [y [[H5 H6] H7]]. auto.  exists (FComp F Gs); auto.  intros. apply Term_Eq_trans with (FuncT F (map (fun g=>n2t (g ns)) gs)). apply FComp_spec with n; auto. rewrite map_length; auto. apply MapR_sym. replace Gs with (map id Gs). apply MapR_map2. eapply MapR_trans; [|eapply H3].
  intros. replace (id y) with y; auto. destruct H8; auto. rewrite map_id; auto. rewrite <- map_map. apply H2. rewrite map_length; auto.
  destruct IHPRfunc1 as [F H1 H2]. destruct IHPRfunc2 as [G H3 H4]. exists (FRecu F G); auto. intros. destruct ns as [|i ns]. inversion H5. inversion H5. clear H5. subst n. induction i. simpl. apply Term_Eq_trans with (FuncT F (map n2t ns)). apply FRecu_Zero_spec; auto. rewrite map_length. auto. apply H2; auto. simpl. remember ((fix rec (n:nat):=match n with|O=>f ns|S n'=>g (rec n'::n'::ns) end) i) as t.
  apply Term_Eq_trans with (FuncT G (n2t t::n2t i::map n2t ns)). apply FRecu_Succ_spec; auto. rewrite map_length; auto. replace (n2t t::n2t i::map n2t ns) with (map n2t (t::i::ns)); auto. Defined.
*)

Definition MapR_build': forall {T U:Type} (R:T->U->Prop) (l:list T), (forall x, In x l->exists y, R x y) -> exists m, MapR R l m. Proof. induction l; intros. exists nil; auto. destruct IHl as [m H0]. intros; auto. destruct (H a) as [b H1]; auto. exists (b::m); auto. Qed.

Theorem PRfunc_Func: forall f n, PRfunc n f -> exists F:Func, WFFunc n F /\ forall ns p, n=length ns -> Inf p (FuncT F (map n2t ns) == n2t (f ns)). Proof. intros f n H. induction H.
  exists FZero; split; auto. intros. destruct ns; auto. inversion H. exists (FSucc); split; auto. intros. destruct ns. inversion H. destruct ns; auto. inversion H. exists (FProj i); split; auto. intros. apply FProj_spec. rewrite map_length; subst n; auto. replace Zero with (n2t 0); auto. apply map_nth.
  destruct IHPRfunc as [F [H2 H3]]. destruct (MapR_build' (T:=list nat->nat) (U:=Func)) with (l:=gs) (R:=fun f F=>WFFunc n F /\ forall ns p,n=length ns->Inf p (FuncT F (map n2t ns)==n2t (f ns))) as [Gs H4]. intros; auto. assert (WFFunc n (FComp F Gs)). apply WFF_Comp. replace (length Gs) with (length gs); auto. apply MapR_length in H4; auto.
  apply Forall_forall. intros g H5. apply in_MapR_2 with (x:=g) in H4; auto. destruct H4 as [y [[H6 H7] H8]]. auto.  exists (FComp F Gs); split; auto. intros. apply Term_Eq_trans with (FuncT F (map (fun g=>n2t (g ns)) gs)). apply FComp_spec with n; auto. rewrite map_length; auto. apply MapR_sym. replace Gs with (map id Gs). apply MapR_map2. eapply MapR_trans; [|eapply H4].
  intros. replace (id y) with y; auto. destruct H9; auto. rewrite map_id; auto. rewrite <- map_map. apply H3. rewrite map_length; auto.
  destruct IHPRfunc1 as [F [H1 H2]]. destruct IHPRfunc2 as [G [H3 H4]]. exists (FRecu F G); split; auto. intros. destruct ns as [|i ns]. inversion H5. inversion H5. clear H5. subst n. induction i. simpl. apply Term_Eq_trans with (FuncT F (map n2t ns)). apply FRecu_Zero_spec; auto. rewrite map_length. auto. apply H2; auto. simpl. remember ((fix rec (n:nat):=match n with|O=>f ns|S n'=>g (rec n'::n'::ns) end) i) as t.
  apply Term_Eq_trans with (FuncT G (n2t t::n2t i::map n2t ns)). apply FRecu_Succ_spec; auto. rewrite map_length; auto. replace (n2t t::n2t i::map n2t ns) with (map n2t (t::i::ns)); auto. Qed.

Inductive PR0 (f:nat) : Prop := PR0_intro: forall pf, PRfunc 0 pf -> f = pf nil -> PR0 f.
Inductive PR1 (f:nat->nat) : Prop := PR1_intro: forall pf, PRfunc 1 pf -> (forall x, f x = pf (x::nil)) -> PR1 f.
Inductive PR2 (f:nat->nat->nat) : Prop := PR2_intro: forall pf, PRfunc 2 pf -> (forall x y, f x y = pf (x::y::nil)) -> PR2 f.
Inductive PR3 (f:nat->nat->nat->nat) : Prop := PR3_intro: forall pf, PRfunc 3 pf -> (forall x y z, f x y z = pf (x::y::z::nil)) -> PR3 f.
Inductive PR4 (f:nat->nat->nat->nat->nat) : Prop := PR4_intro: forall pf, PRfunc 4 pf -> (forall x y z w, f x y z w = pf (x::y::z::w::nil)) -> PR4 f.
Hint Constructors PR0 PR1 PR2 PR3 PR4.

Theorem PR0_Func: forall f, PR0 f -> exists F:Func, WFFunc 0 F /\ forall p, Inf p (FuncT F (nil) == n2t f). Proof. intros. destruct H. destruct (PRfunc_Func H) as [F [H1 H2]]. exists F; split; auto. intros. replace nil with (map n2t nil) at 1; auto. subst f; auto. Qed.
Theorem PR1_Func: forall f, PR1 f -> exists F:Func, WFFunc 1 F /\ forall n p, Inf p (FuncT F (n2t n::nil) == n2t (f n)). Proof. intros. destruct H. destruct (PRfunc_Func H) as [F [H1 H2]]. exists F; split; auto. intros. replace (f n) with (pf (n::nil)); auto. replace (n2t n::nil) with (map n2t (n::nil)); auto. Qed.
Theorem PR2_Func: forall f, PR2 f -> exists F:Func, WFFunc 2 F /\ forall x y p, Inf p (FuncT F (n2t x::n2t y::nil) == n2t (f x y)). Proof. intros. destruct H. destruct (PRfunc_Func H) as [F [H1 H2]]. exists F; split; auto. intros. replace (f x y) with (pf (x::y::nil)); auto. replace (n2t x::n2t y::nil) with (map n2t (x::y::nil)); auto. Qed.
Theorem PR3_Func: forall f, PR3 f -> exists F:Func, WFFunc 3 F /\ forall x y z p, Inf p (FuncT F (n2t x::n2t y::n2t z::nil) == n2t (f x y z)). Proof. intros. destruct H. destruct (PRfunc_Func H) as [F [H1 H2]]. exists F; split; auto. intros. replace (f x y z) with (pf (x::y::z::nil)); auto. replace (n2t x::n2t y::n2t z::nil) with (map n2t (x::y::z::nil)); auto. Qed.
Theorem PR4_Func: forall f, PR4 f -> exists F:Func, WFFunc 4 F /\ forall x y z w p, Inf p (FuncT F (n2t x::n2t y::n2t z::n2t w::nil) == n2t (f x y z w)). Proof. intros. destruct H. destruct (PRfunc_Func H) as [F [H1 H2]]. exists F; split; auto. intros. replace (f x y z w) with (pf (x::y::z::w::nil)); auto. replace (n2t x::n2t y::n2t z::n2t w::nil) with (map n2t (x::y::z::w::nil)); auto. Qed.

Theorem PR0_0: PR0 0. Proof. apply PR0_intro with (fun _=>0); auto. Qed.
Theorem PR1_S: PR1 S. Proof. apply PR1_intro with (fun l=>match l with |nil=>0 |a::_ => S a end); auto. Qed.
Theorem PR1_Proj0: PR1 (fun x=>x). Proof. apply PR1_intro with (fun l=>nth 0 l 0); auto. Qed.
Theorem PR2_Proj0: PR2 (fun x y=>x). Proof. apply PR2_intro with (fun l=>nth 0 l 0); auto. Qed. 
Theorem PR2_Proj1: PR2 (fun x y=>y). Proof. apply PR2_intro with (fun l=>nth 1 l 0); auto. Qed.
Theorem PR3_Proj0: PR3 (fun x y z=>x). Proof. apply PR3_intro with (fun l=>nth 0 l 0); auto. Qed. 
Theorem PR3_Proj1: PR3 (fun x y z=>y). Proof. apply PR3_intro with (fun l=>nth 1 l 0); auto. Qed.
Theorem PR3_Proj2: PR3 (fun x y z=>z). Proof. apply PR3_intro with (fun l=>nth 2 l 0); auto. Qed.
Theorem PR4_Proj0: PR4 (fun x y z w=>x). Proof. apply PR4_intro with (fun l=>nth 0 l 0); auto. Qed. 
Theorem PR4_Proj1: PR4 (fun x y z w=>y). Proof. apply PR4_intro with (fun l=>nth 1 l 0); auto. Qed. 
Theorem PR4_Proj2: PR4 (fun x y z w=>z). Proof. apply PR4_intro with (fun l=>nth 2 l 0); auto. Qed. 
Theorem PR4_Proj3: PR4 (fun x y z w=>w). Proof. apply PR4_intro with (fun l=>nth 3 l 0); auto. Qed. 
Hint Resolve PR0_0 PR1_S PR1_Proj0 PR2_Proj0 PR2_Proj1 PR3_Proj0 PR3_Proj1 PR3_Proj2 PR4_Proj0 PR4_Proj1 PR4_Proj2 PR4_Proj3.

Theorem PR0_Comp0: forall c f, PR0 f -> c = f -> PR0 c. Proof. intros. subst c; auto. Qed.
Theorem PR0_Comp1: forall c f g, PR1 f -> PR0 g -> c = f g -> PR0 c. Proof. intros. destruct H. destruct H0. apply PR0_intro with (fun a=>pf (map (fun g=>g a) (pf0::nil))). apply PRComp; auto. intros. apply In_one in H4; subst x; auto. intros. simpl. rewrite H1. rewrite <- H2; auto. Qed.
Theorem PR0_Comp2: forall c f g h, PR2 f -> PR0 g -> PR0 h -> c = f g h -> PR0 c. Proof. intros. destruct H. destruct H0. destruct H1. apply PR0_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::nil))). apply PRComp; auto. intros. destruct H6. subst x; auto. destruct H6. subst x; auto. destruct H6. intros. simpl. rewrite H2. rewrite H3. repeat f_equal; auto. Qed.
Theorem PR0_Comp3: forall c f g h i, PR3 f -> PR0 g -> PR0 h -> PR0 i -> c = f g h i -> PR0 c. Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. apply PR0_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::pf2::nil))). apply PRComp; auto. intros. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. intros. simpl. rewrite H3. rewrite H4. repeat f_equal; auto. Qed.
Theorem PR1_Comp0: forall c f, PR0 f -> (forall x, c x= f) -> PR1 c. Proof. intros. destruct H. apply PR1_intro with (fun a=>pf (map (fun g=>g a) nil)). apply PRComp; auto. intros. destruct H2. intros. simpl. rewrite H0; auto. Qed.
Theorem PR1_Comp1: forall c f g, PR1 f -> PR1 g -> (forall x, c x= f (g x)) -> PR1 c. Proof. intros. destruct H. destruct H0. apply PR1_intro with (fun a=>pf (map (fun g=>g a) (pf0::nil))). apply PRComp; auto. intros. apply In_one in H4; subst x; auto. intros. simpl. rewrite H1. rewrite <- H2; auto. Qed.
Theorem PR1_Comp2: forall c f g h, PR2 f -> PR1 g -> PR1 h -> (forall x, c x = f (g x) (h x)) -> PR1 c. Proof. intros. destruct H. destruct H0. destruct H1. apply PR1_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::nil))). apply PRComp; auto. intros. destruct H6. subst x; auto. destruct H6. subst x; auto. destruct H6. intros. simpl. rewrite H2. rewrite H3. repeat f_equal; auto. Qed.
Theorem PR1_Comp3: forall c f g h i, PR3 f -> PR1 g -> PR1 h -> PR1 i -> (forall x, c x= f (g x) (h x) (i x)) -> PR1 c. Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. apply PR1_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::pf2::nil))). apply PRComp; auto. intros. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. intros. simpl. rewrite H3. rewrite H4. repeat f_equal; auto. Qed.
Theorem PR2_Comp0: forall c f, PR0 f -> (forall x y, c x y= f) -> PR2 c. Proof. intros. destruct H. apply PR2_intro with (fun a=>pf (map (fun g=>g a) nil)). apply PRComp; auto. intros. destruct H2. intros. simpl. rewrite H0; auto. Qed.
Theorem PR2_Comp1: forall c f g, PR1 f -> PR2 g -> (forall x y, c x y= f (g x y)) -> PR2 c. Proof. intros. destruct H. destruct H0. apply PR2_intro with (fun a=>pf (map (fun g=>g a) (pf0::nil))). apply PRComp; auto. intros. apply In_one in H4; subst x; auto. intros. simpl. rewrite H1. rewrite <- H2; auto. Qed.
Theorem PR2_Comp2: forall c f g h, PR2 f -> PR2 g -> PR2 h -> (forall x y, c x y = f (g x y) (h x y)) -> PR2 c. Proof. intros. destruct H. destruct H0. destruct H1. apply PR2_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::nil))). apply PRComp; auto. intros. destruct H6. subst x; auto. destruct H6. subst x; auto. destruct H6. intros. simpl. rewrite H2. rewrite H3. repeat f_equal; auto. Qed.
Theorem PR2_Comp3: forall c f g h i, PR3 f -> PR2 g -> PR2 h -> PR2 i -> (forall x y, c x y= f (g x y) (h x y) (i x y)) -> PR2 c. Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. apply PR2_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::pf2::nil))). apply PRComp; auto. intros. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. intros. simpl. rewrite H3. rewrite H4. repeat f_equal; auto. Qed.
Theorem PR3_Comp0: forall c f, PR0 f -> (forall x y z, c x y z= f) -> PR3 c. Proof. intros. destruct H. apply PR3_intro with (fun a=>pf (map (fun g=>g a) nil)). apply PRComp; auto. intros. destruct H2. intros. simpl. rewrite H0; auto. Qed.
Theorem PR3_Comp1: forall c f g, PR1 f -> PR3 g -> (forall x y z, c x y z= f (g x y z)) -> PR3 c. Proof. intros. destruct H. destruct H0. apply PR3_intro with (fun a=>pf (map (fun g=>g a) (pf0::nil))). apply PRComp; auto. intros. apply In_one in H4; subst x; auto. intros. simpl. rewrite H1. rewrite <- H2; auto. Qed.
Theorem PR3_Comp2: forall c f g h, PR2 f -> PR3 g -> PR3 h -> (forall x y z, c x y z= f (g x y z) (h x y z)) -> PR3 c. Proof. intros. destruct H. destruct H0. destruct H1. apply PR3_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::nil))). apply PRComp; auto. intros. destruct H6. subst x; auto. destruct H6. subst x; auto. destruct H6. intros. simpl. rewrite H2. rewrite H3. repeat f_equal; auto. Qed.
Theorem PR3_Comp3: forall c f g h i, PR3 f -> PR3 g -> PR3 h -> PR3 i -> (forall x y z, c x y z= f (g x y z) (h x y z) (i x y z)) -> PR3 c. Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. apply PR3_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::pf2::nil))). apply PRComp; auto. intros. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. intros. simpl. rewrite H3. rewrite H4. repeat f_equal; auto. Qed.
Theorem PR4_Comp0: forall c f, PR0 f -> (forall x y z w, c x y z w= f) -> PR4 c. Proof. intros. destruct H. apply PR4_intro with (fun a=>pf (map (fun g=>g a) nil)). apply PRComp; auto. intros. destruct H2. intros. simpl. rewrite H0; auto. Qed.
Theorem PR4_Comp1: forall c f g, PR1 f -> PR4 g -> (forall x y z w, c x y z w= f (g x y z w)) -> PR4 c. Proof. intros. destruct H. destruct H0. apply PR4_intro with (fun a=>pf (map (fun g=>g a) (pf0::nil))). apply PRComp; auto. intros. apply In_one in H4; subst x; auto. intros. simpl. rewrite H1. rewrite <- H2; auto. Qed.
Theorem PR4_Comp2: forall c f g h, PR2 f -> PR4 g -> PR4 h -> (forall x y z w, c x y z w= f (g x y z w) (h x y z w)) -> PR4 c. Proof. intros. destruct H. destruct H0. destruct H1. apply PR4_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::nil))). apply PRComp; auto. intros. destruct H6. subst x; auto. destruct H6. subst x; auto. destruct H6. intros. simpl. rewrite H2. rewrite H3. repeat f_equal; auto. Qed.
Theorem PR4_Comp3: forall c f g h i, PR3 f -> PR4 g -> PR4 h -> PR4 i -> (forall x y z w, c x y z w= f (g x y z w) (h x y z w) (i x y z w)) -> PR4 c. Proof. intros. destruct H. destruct H0. destruct H1. destruct H2. apply PR4_intro with (fun a=>pf (map (fun g=>g a) (pf0::pf1::pf2::nil))). apply PRComp; auto. intros. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. subst x; auto. destruct H8. intros. simpl. rewrite H3. rewrite H4. repeat f_equal; auto. Qed.
Hint Resolve PR0_Comp0 PR0_Comp1 PR0_Comp2 PR0_Comp3 PR1_Comp0 PR1_Comp1 PR1_Comp2 PR1_Comp3 PR2_Comp0 PR2_Comp1 PR2_Comp2 PR2_Comp3 PR3_Comp0 PR3_Comp1 PR3_Comp2 PR3_Comp3 PR4_Comp0 PR4_Comp1 PR4_Comp2 PR4_Comp3.

Theorem PR1_Recu: forall r f g, PR0 f -> PR2 g -> (forall x, r x= (fix rec i := match i with 0=>f |S i'=> g (rec i') i' end) x) -> PR1 r. Proof. intros. destruct H. destruct H0. apply PR1_intro with (fun l=> match l with |nil=>0 |i::l'=> (fix rec (n:nat) := match n with |0=>pf l' |S n'=>pf0 (rec n'::n'::l') end) i end). apply PRRecu; auto. intros. rewrite H1. clear H1. induction x; auto. rewrite IHx. rewrite <- H3. auto. Qed.
Theorem PR2_Recu: forall r f g, PR1 f -> PR3 g -> (forall x y, r x y = (fix rec i y:= match i with 0=>f y|S i'=> g (rec i' y) i' y end) x y) -> PR2 r. Proof. intros. destruct H. destruct H0. apply PR2_intro with (fun l=> match l with |nil=>0 |i::l'=> (fix rec (n:nat) := match n with |0=>pf l' |S n'=>pf0 (rec n'::n'::l') end) i end). apply PRRecu; auto. intros. rewrite H1. clear H1. induction x; auto. rewrite IHx. rewrite <- H3. auto. Qed.
Theorem PR3_Recu: forall r f g, PR2 f -> PR4 g -> (forall x y z, r x y z = (fix rec i y z:= match i with 0=>f y z|S i'=> g (rec i' y z) i' y z end) x y z) -> PR3 r. Proof. intros. destruct H. destruct H0. apply PR3_intro with (fun l=> match l with |nil=>0 |i::l'=> (fix rec (n:nat) := match n with |0=>pf l' |S n'=>pf0 (rec n'::n'::l') end) i end). apply PRRecu; auto. intros. rewrite H1. clear H1. induction x; auto. rewrite IHx. rewrite <- H3. auto. Qed.
Hint Resolve PR1_Recu PR2_Recu PR3_Recu.

Theorem PR0_const: forall n, PR0 n. Proof. induction n; auto. apply PR0_Comp1 with S n; auto. Qed.
Theorem PR1_const: forall n, PR1 (fun _:nat=>n). Proof. induction n. apply PR1_Comp0 with 0; auto. apply PR1_Comp1 with S (fun _=>n); auto. Qed.
Theorem PR2_const: forall n, PR2 (fun _ _:nat=>n). Proof. induction n. apply PR2_Comp0 with 0; auto. apply PR2_Comp1 with S (fun _ _=>n); auto. Qed.
Theorem PR2_plus: PR2 plus. Proof. apply PR2_Recu with (fun y=>y) (fun r i y=>S r); auto. apply PR3_Comp1 with S (fun x y z=>x); auto. Qed.
Theorem PR2_mult: PR2 mult. Proof. apply PR2_Recu with (fun y=>0) (fun r i y=>r+y); auto. apply PR1_const. apply PR3_Comp2 with plus (fun x y z=>x) (fun x y z=>z); auto. apply PR2_plus. intros. induction x; simpl; auto. rewrite <- IHx. auto. Qed.
Theorem PR2_pow: PR2 pow. Proof. cut (PR2 (fun x y=>pow y x)). intros. apply PR2_Comp2 with (fun x y=>pow y x) (fun x y=>y) (fun x y=>x); auto. apply PR2_Recu with (fun y=>1) (fun r i y=>r*y); auto. apply PR1_const. apply PR3_Comp2 with mult (fun x y z=>x) (fun x y z=>z); auto. apply PR2_mult. intros. induction x; simpl; auto. rewrite <- IHx. auto. Qed.
Theorem PR1_pred: PR1 pred. Proof. apply PR1_Recu with 0 (fun r i =>i); auto. induction x; auto. Qed.
Theorem PR2_minus: PR2 minus. Proof. cut (PR2 (fun x y=>minus y x)). intros. apply PR2_Comp2 with (fun x y=>y-x) (fun x y=>y) (fun x y=>x); auto. apply PR2_Recu with (fun y=>y) (fun r i y=>pred r); auto. apply PR3_Comp1 with pred (fun x y z=>x); auto. apply PR1_pred. induction x; intros. rewrite <- minus_n_O; auto. rewrite <- IHx. clear IHx. destruct (le_lt_dec y x). replace (y-x) with 0. replace (y-S x) with 0; auto. symmetry; apply Nat.sub_0_le; auto. symmetry; apply Nat.sub_0_le; auto. destruct y. inversion l. replace (S y-x) with (S(y-x)). simpl; auto. rewrite <- minus_Sn_m; auto. Qed.
Theorem PR2_max: PR2 max. Proof. apply PR2_Comp2 with plus minus (fun x y=>y); auto. apply PR2_plus. apply PR2_minus. intros. destruct (le_lt_dec x y). rewrite max_r; auto. replace (x-y) with 0; auto. apply Nat.sub_0_le in l. auto. rewrite max_l; auto. rewrite plus_comm. rewrite <- le_plus_minus; auto. Qed.
Theorem PR2_min: PR2 min. Proof. apply PR2_Comp2 with minus (fun x y=>x) minus; auto. apply PR2_minus. apply PR2_minus. intros. destruct (le_lt_dec x y). rewrite min_l; auto. apply Nat.sub_0_le in l. rewrite l. rewrite <- minus_n_O; auto. rewrite min_r; auto. replace (x-(x-y)) with (y+(x-y)-(x-y)). rewrite plus_comm. rewrite minus_plus; auto. f_equal. rewrite <- le_plus_minus with y x; auto. Qed.
Hint Resolve PR0_const PR1_const PR2_const PR2_plus PR2_mult PR2_pow PR1_pred PR2_minus PR2_max PR2_min.

Definition abs n m:nat := if le_lt_dec n m then m-n else n-m.
Definition sign n:nat := match n with |0=>0 |S _=>1 end.
Definition nsign n:nat := match n with |0=>1 |S _=>0 end.

Theorem PR2_abs: PR2 abs. Proof. apply PR2_Comp2 with plus minus (fun x y=>y-x); auto. apply PR2_Comp2 with minus (fun x y=>y) (fun x y=>x); auto. intros. unfold abs. destruct (le_lt_dec x y). apply Nat.sub_0_le in l. rewrite l. auto. apply lt_le_weak in l. apply Nat.sub_0_le in l. rewrite l. auto. Qed.
Theorem PR1_sign: PR1 sign. Proof. apply PR1_Recu with 0 (fun _ _=>1); auto. destruct x; auto. Qed.
Theorem PR1_nsign: PR1 nsign. Proof. apply PR1_Recu with 1 (fun _ _=>0); auto. destruct x; auto. Qed.
Hint Resolve PR2_abs PR1_sign PR1_nsign.

(* Predicates *)
Inductive PRP1 (P:nat->Prop) : Prop := PRP1_intro: forall f, PR1 f-> (forall x, f x = 0 -> P x) -> (forall x, f x<>0 -> ~P x) -> PRP1 P.
Inductive PRP2 (P:nat->nat->Prop) : Prop := PRP2_intro: forall f, PR2 f-> (forall x y, f x y = 0 -> P x y) -> (forall x y, f x y<>0 -> ~P x y) -> PRP2 P.
Inductive PRP3 (P:nat->nat->nat->Prop) : Prop := PRP3_intro: forall f, PR3 f-> (forall x y z, f x y z= 0 -> P x y z) -> (forall x y z, f x y z<>0 -> ~P x y z) -> PRP3 P.
Hint Constructors PRP1 PRP2 PRP3.

Theorem PRP1_Func: forall P p v, PRP1 P -> exists (F:Formula), forall x, (P x -> Inf ((#v==n2t x)::p) F) /\ (~P x -> Inf ((#v==n2t x)::p) (!F)). Proof. intros. destruct H. apply PR1_Func in H as [G [H2 H3]]. exists (FuncT G ((#v)::nil) == n2t 0). intros; split; intros. apply Term_Eq_trans with (FuncT G (n2t x::nil)). apply Term_Eq_args; auto. replace 0 with (f x); auto. destruct (nat_eq_dec (f x) 0); auto. contradict H; auto.
  apply Contra with (n2t (f x)==n2t 0). apply Term_Eq_trans with (FuncT G ((#v)::nil)); auto. apply Term_Eq_trans with (FuncT G (n2t x::nil)); auto. apply Term_Eq_args; auto. apply n2t_neq. destruct (nat_eq_dec (f x) 0); auto; contradiction. Qed.
Theorem PRP2_Func: forall P p v u, PRP2 P -> exists (F:Formula), forall x y, (P x y -> Inf ((#v==n2t x)::(#u==n2t y)::p) F) /\ (~P x y-> Inf ((#v==n2t x)::(#u==n2t y)::p) (!F)). Proof. intros. destruct H. apply PR2_Func in H as [G [H2 H3]]. exists (FuncT G ((#v)::(#u)::nil) == n2t 0). intros; split; intros. apply Term_Eq_trans with (FuncT G (n2t x::n2t y::nil)). apply Term_Eq_args; auto. replace 0 with (f x y); auto. destruct (nat_eq_dec (f x y) 0); auto. contradict H; auto.
  apply Contra with (n2t (f x y)==n2t 0). apply Term_Eq_trans with (FuncT G ((#v)::(#u)::nil)); auto. apply Term_Eq_trans with (FuncT G (n2t x::n2t y::nil)); auto. apply Term_Eq_args; auto. apply MapR_cons; auto. apply MapR_cons; auto. apply n2t_neq. destruct (nat_eq_dec (f x y) 0); auto; contradiction. Qed.
Theorem PRP3_Func: forall P p v u w, PRP3 P -> exists (F:Formula), forall x y z, (P x y z-> Inf ((#v==n2t x)::(#u==n2t y)::(#w==n2t z)::p) F) /\ (~P x y z-> Inf ((#v==n2t x)::(#u==n2t y)::(#w==n2t z)::p) (!F)). Proof. intros. destruct H. apply PR3_Func in H as [G [H2 H3]]. exists (FuncT G ((#v)::(#u)::(#w)::nil) == n2t 0). intros; split; intros. apply Term_Eq_trans with (FuncT G (n2t x::n2t y::n2t z::nil)). apply Term_Eq_args; auto. apply MapR_cons; auto. apply MapR_cons; auto. replace 0 with (f x y z); auto. destruct (nat_eq_dec (f x y z) 0); auto. contradict H; auto.
  apply Contra with (n2t (f x y z)==n2t 0). apply Term_Eq_trans with (FuncT G ((#v)::(#u)::(#w)::nil)); auto. apply Term_Eq_trans with (FuncT G (n2t x::n2t y::n2t z::nil)); auto. apply Term_Eq_args; auto. apply MapR_cons; auto. apply MapR_cons; auto. apply MapR_cons; auto. apply Inf_incl'; auto. apply n2t_neq. destruct (nat_eq_dec (f x y z) 0); auto; contradiction. Qed.

Theorem PRP1_equiv: forall P Q, PRP1 P -> (forall x, P x<->Q x) -> PRP1 Q. Proof. intros. destruct H. apply PRP1_intro with f; intros; auto. apply H0; auto. intros C; apply H0 in C; contradict C; auto. Qed.
Theorem PRP2_equiv: forall P Q, PRP2 P -> (forall x y, P x y<->Q x y) -> PRP2 Q. Proof. intros. destruct H. apply PRP2_intro with f; intros; auto. apply H0; auto. intros C; apply H0 in C; contradict C; auto. Qed.
Theorem PRP3_equiv: forall P Q, PRP3 P -> (forall x y z, P x y z<->Q x y z) -> PRP3 Q. Proof. intros. destruct H. apply PRP3_intro with f; intros; auto. apply H0; auto. intros C; apply H0 in C; contradict C; auto. Qed.

Theorem PRP1_Neg: forall P, PRP1 P -> PRP1 (fun x=>~P x). Proof. intros. destruct H. apply PRP1_intro with (fun x=>nsign (f x)); auto. apply PR1_Comp1 with nsign f; auto. intros. apply H1. destruct (f x); auto. inversion H2. intros. intros C. apply C. apply H0. destruct (f x); auto. contradict H2; auto. Qed.
Theorem PRP2_Neg: forall P, PRP2 P -> PRP2 (fun x y=>~P x y). Proof. intros. destruct H. apply PRP2_intro with (fun x y=>nsign (f x y)); auto. apply PR2_Comp1 with nsign f; auto. intros. apply H1. destruct (f x y); auto. inversion H2. intros. intros C. apply C. apply H0. destruct (f x y); auto. contradict H2; auto. Qed.
Theorem PRP3_Neg: forall P, PRP3 P -> PRP3 (fun x y z=>~P x y z). Proof. intros. destruct H. apply PRP3_intro with (fun x y z=>nsign (f x y z)); auto. apply PR3_Comp1 with nsign f; auto. intros. apply H1. destruct (f x y z); auto. inversion H2. intros. intros C. apply C. apply H0. destruct (f x y z); auto. contradict H2; auto. Qed.

Theorem PRP1_Land: forall P Q, PRP1 P -> PRP1 Q -> PRP1 (fun x=>P x /\ Q x). Proof. intros. destruct H. destruct H0. apply PRP1_intro with (fun x=>plus (f x) (f0 x)); intros; auto. apply PR1_Comp2 with plus f f0; auto. split. apply H1. destruct (f x); auto. inversion H5. apply H3. destruct (f0 x); auto. rewrite <- plus_n_Sm in H5. inversion H5. contradict H5. destruct H5. destruct (nat_eq_dec (f x) 0); destruct (nat_eq_dec (f0 x) 0). rewrite e; rewrite e0; auto. contradict H6; auto. contradict H5; auto. contradict H5; auto. Qed.
Theorem PRP2_Land: forall P Q, PRP2 P -> PRP2 Q -> PRP2 (fun x y=>P x y/\ Q x y). Proof. intros. destruct H. destruct H0. apply PRP2_intro with (fun x y=>plus (f x y) (f0 x y)); intros; auto. apply PR2_Comp2 with plus f f0; auto. split. apply H1. destruct (f x y); auto. inversion H5. apply H3. destruct (f0 x y); auto. rewrite <- plus_n_Sm in H5. inversion H5. contradict H5. destruct H5. destruct (nat_eq_dec (f x y) 0); destruct (nat_eq_dec (f0 x y) 0). rewrite e; rewrite e0; auto. contradict H6; auto. contradict H5; auto. contradict H5; auto. Qed.
Theorem PRP3_Land: forall P Q, PRP3 P -> PRP3 Q -> PRP3 (fun x y z=>P x y z/\ Q x y z). Proof. intros. destruct H. destruct H0. apply PRP3_intro with (fun x y z=>plus (f x y z) (f0 x y z)); intros; auto. apply PR3_Comp2 with plus f f0; auto. split. apply H1. destruct (f x y z); auto. inversion H5. apply H3. destruct (f0 x y z); auto. rewrite <- plus_n_Sm in H5. inversion H5. contradict H5. destruct H5. destruct (nat_eq_dec (f x y z) 0); destruct (nat_eq_dec (f0 x y z) 0). rewrite e; rewrite e0; auto. contradict H6; auto. contradict H5; auto. contradict H5; auto. Qed.

Theorem PRP1_Lor: forall P Q, PRP1 P -> PRP1 Q -> PRP1 (fun x=>P x \/ Q x). Proof. intros. destruct H. destruct H0. apply PRP1_intro with (fun x=>mult (f x) (f0 x)); intros; auto. apply PR1_Comp2 with mult f f0; auto. apply mult_is_O in H5. destruct H5; auto. contradict H5. destruct H5. destruct (nat_eq_dec (f x) 0). rewrite e; auto. contradict H5; auto. destruct (nat_eq_dec (f0 x) 0). rewrite e; auto. contradict H5; auto. Qed.
Theorem PRP2_Lor: forall P Q, PRP2 P -> PRP2 Q -> PRP2 (fun x y=>P x y\/ Q x y). Proof. intros. destruct H. destruct H0. apply PRP2_intro with (fun x y=>mult (f x y) (f0 x y)); intros; auto. apply PR2_Comp2 with mult f f0; auto. apply mult_is_O in H5. destruct H5; auto. contradict H5. destruct H5. destruct (nat_eq_dec (f x y) 0). rewrite e; auto. contradict H5; auto. destruct (nat_eq_dec (f0 x y) 0). rewrite e; auto. contradict H5; auto. Qed.
Theorem PRP3_Lor: forall P Q, PRP3 P -> PRP3 Q -> PRP3 (fun x y z=>P x y z\/ Q x y z). Proof. intros. destruct H. destruct H0. apply PRP3_intro with (fun x y z=>mult (f x y z) (f0 x y z)); intros; auto. apply PR3_Comp2 with mult f f0; auto. apply mult_is_O in H5. destruct H5; auto. contradict H5. destruct H5. destruct (nat_eq_dec (f x y z) 0). rewrite e; auto. contradict H5; auto. destruct (nat_eq_dec (f0 x y z) 0). rewrite e; auto. contradict H5; auto. Qed.
Hint Resolve PRP1_equiv PRP2_equiv PRP3_equiv PRP1_Neg PRP2_Neg PRP3_Neg PRP1_Land PRP2_Land PRP3_Land PRP1_Lor PRP2_Lor PRP3_Lor.

Theorem PRP2_Eq: PRP2 (fun x y:nat =>x=y). Proof. apply PRP2_intro with abs; auto; intros; unfold abs in H; destruct (le_lt_dec x y). apply le_antisym; auto. apply Nat.sub_0_le in H; auto. contradict l. apply Nat.sub_0_le in H; auto. contradict H; subst y. rewrite <- minus_n_n; auto. contradict H. subst y; rewrite <- minus_n_n; auto. Qed.
Theorem PRP2_le: PRP2 le. Proof. apply PRP2_intro with minus; auto; intros. apply Nat.sub_0_le; auto. contradict H. apply Nat.sub_0_le; auto. Qed.
Theorem PRP2_Neq: PRP2 (fun x y:nat =>x<>y). Proof. apply PRP2_Neg. apply PRP2_Eq. Qed.
Theorem PRP2_lt: PRP2 lt. Proof. apply PRP2_equiv with (fun x y=>x<=y /\ x<>y). apply PRP2_Land. apply PRP2_le. apply PRP2_Neq. intros; split; intros. destruct H. apply le_lt_or_eq in H. destruct H; auto; contradiction. split. auto. contradict H; subst y; auto. Qed.

Theorem PRP1_Ex: forall P, PRP1 P -> PRP1 (fun x=>exists n, n<x /\ P n). Proof. intros. destruct H. apply PRP1_intro with (fix rec x := match x with |0=>1 |S x'=>rec x' * f x' end). apply PR1_Recu with 1 (fun r x=>r*f x); auto. apply PR2_Comp2 with mult (fun r x=>r) (fun r x=>f x); auto. apply PR2_Comp1 with f (fun _ x=>x); auto. intros. induction x. inversion H2. apply mult_is_O in H2. destruct H2. apply IHx in H2. destruct H2 as [n [H3 H4]]. exists n; auto. exists x; auto. intros. induction x. intros C. destruct C as [n [H3 H4]]. inversion H3. intros C. destruct C as [n [H3 H4]].
 apply le_S_n in H3. apply le_lt_or_eq in H3. destruct H3. apply IHx. contradict H2. rewrite H2; auto. exists n; auto. subst n. apply H2. destruct (nat_eq_dec (f x) 0). rewrite e; auto. contradict H4; auto. Qed.
Theorem PRP2_Ex: forall P, PRP2 P -> PRP2 (fun x y=>exists n, n<x /\ P n y). Proof. intros. destruct H. apply PRP2_intro with (fix rec x y:= match x with |0=>1 |S x'=>rec x' y* f x' y end). apply PR2_Recu with (fun _=>1) (fun r x y=>r*f x y); auto. apply PR3_Comp2 with mult (fun r x y=>r) (fun r x y=>f x y); auto. apply PR3_Comp2 with f (fun _ x y=>x) (fun _ x y=>y); auto. intros. induction x. inversion H2. apply mult_is_O in H2. destruct H2. apply IHx in H2. destruct H2 as [n [H3 H4]]. exists n; auto. exists x; auto. intros. induction x. intros C. destruct C as [n [H3 H4]]. inversion H3. intros C. destruct C as [n [H3 H4]].
 apply le_S_n in H3. apply le_lt_or_eq in H3. destruct H3. apply IHx. contradict H2. rewrite H2; auto. exists n; auto. subst n. apply H2. destruct (nat_eq_dec (f x y) 0). rewrite e; auto. contradict H4; auto. Qed.
Theorem PRP3_Ex: forall P, PRP3 P -> PRP3 (fun x y z=>exists n, n<x /\ P n y z). Proof. intros. destruct H. apply PRP3_intro with (fix rec x y z:= match x with |0=>1 |S x'=>rec x' y z* f x' y z end). apply PR3_Recu with (fun _ _=>1) (fun r x y z=>r*f x y z); auto. apply PR4_Comp2 with mult (fun r x y z=>r) (fun r x y z=>f x y z); auto. apply PR4_Comp3 with f (fun _ x y z=>x) (fun _ x y z=>y) (fun _ x y z=>z); auto. intros. induction x. inversion H2. apply mult_is_O in H2. destruct H2. apply IHx in H2. destruct H2 as [n [H3 H4]]. exists n; auto. exists x; auto. intros. induction x. intros C. destruct C as [n [H3 H4]]. inversion H3. intros C. destruct C as [n [H3 H4]].
 apply le_S_n in H3. apply le_lt_or_eq in H3. destruct H3. apply IHx. contradict H2. rewrite H2; auto. exists n; auto. subst n. apply H2. destruct (nat_eq_dec (f x y z) 0). rewrite e; auto. contradict H4; auto. Qed.
Hint Resolve PRP2_Eq PRP2_le PRP2_Neq PRP2_lt PRP1_Ex PRP2_Ex PRP3_Ex.