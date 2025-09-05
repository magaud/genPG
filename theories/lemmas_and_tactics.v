Require Import ssreflect ssrfun  ssrbool.
Require Import List.
Import ListNotations.

(* basic boolean lemmas *)

Lemma degen_bool : forall P, is_true false -> P.
Proof.
  intros; discriminate.
Qed.

Lemma and_bool_lr : forall a b, a && b -> a /\ b.
Proof.
  intros a b; case a; case b; intros H; inversion H; split; assumption.
Qed.

Lemma and_bool : forall a b, a && b <-> a /\ b.
Proof.
  intros a b; split.
  apply and_bool_lr.
  case a;case b; intros (ha,hb); solve [inversion ha | inversion hb | reflexivity].
Qed.

Lemma circ3: forall A B C: bool, B && C && A -> A && B &&C.
Proof.
  intros a b c; case a; case b; case c; intros; assumption.
Qed.

Lemma comm12L: forall A B C:bool, B && A && C -> A && B && C.
Proof.
   intros a b c; case a; case b; case c; intros; assumption.
 Qed.

Lemma comm12P: forall A B C D E F :bool,
       B && A && C && D &&E && F -> A && B && C && D && E && F.
Proof.
  intros a b c d e f; case a; case b; case c; case d; case e; case f; intros; assumption.
Qed.

Lemma circ6: forall A B C D E F : bool,
       B && C && D && E &&F && A -> A && B && C && D && E && F.
Proof.
  intros a b c d e f; case a; case b; case c; case d; case e; case f; intros; assumption.
Qed.

Lemma circ2 : forall a b, a&&b -> b&&a.
Proof.
  intros a b; destruct a; destruct b; intros H;inversion H; assumption.
Qed.

(* advanced lemmas *)

Lemma exchL: forall line, forall eql, forall (eql_sym: forall x y:line, eql x y = eql y x), forall x y B C, ~~eql y x && B &&C-> ~~eql x y && B && C.
Proof.
  intros line eql eql_sym x y b c H.
  apply and_bool in H.      
  destruct H as [Hx Hy].
  apply and_bool in Hx.
  destruct Hx.
  apply and_bool; split.
  apply and_bool; split.
  rewrite eql_sym.
  assumption.
  assumption.
  assumption.
Qed.

Lemma exchP: forall point, forall eqp, forall (eqp_sym: forall x y:point, eqp x y = eqp y x),forall x y B C D E F,
    ~~eqp y x && B &&C &&D &&E &&F-> ~~eqp x y && B && C && D && E &&F.
Proof.
  intros point eqp eqp_sym x y b c d e f H.
  apply and_bool in H.
  destruct H as [Ha Hf]; apply and_bool in Ha;
    destruct Ha as [Ha He]; apply and_bool in Ha;
      destruct Ha as [Ha Hd]; apply and_bool in Ha;
        destruct Ha as [Ha Hc]; apply and_bool in Ha;
          destruct Ha as [Ha Hb].
  apply and_bool; split.
  apply and_bool; split.
  apply and_bool; split.
  apply and_bool; split.
  apply and_bool; split.
  rewrite eqp_sym.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma wrapABC : forall S:Type, forall A B C:S,
      forall le:S->S->bool, forall le_total:(forall x y:S, le x y || le y x),
          forall P:S->S->S->Type,
            forall Pwlog: (forall x y z : S, le x y && le y z -> P x y z),
      (forall x y z : S, P x z y -> P x y z) ->
      (forall x y z : S, P y x z -> P x y z) ->
      (forall x y z : S, P y z x -> P x y z) ->
      (forall x y z : S, P z x y -> P x y z) ->
      (forall x y z : S, P z y x -> P x y z) ->
      P A B C.
Proof.
  intros S A B C le le_total P Pwlog Psym1 Psym2 Psym3 Psym4 Psym5;
    destruct (Bool.orb_true_elim _ _ (le_total A B)) as [i | i];
    destruct (Bool.orb_true_elim _ _ (le_total A C)) as [j | j];
    destruct (Bool.orb_true_elim _ _ (le_total B C)) as [k | k];
    [
      apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym1; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym4; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym2; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym2; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym3; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym5; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    ].
Qed.

Lemma wrapperAB : forall S:Type, forall A B:S,forall le:S->S->bool, forall le_total:(forall x y:S, le x y || le y x), forall P:S-> S -> Type, forall Pwlog:(forall x y:S, le x y -> P x y), forall Psym:(forall x y:S,  
P y x -> P x y),  P A B.
Proof.
    intros S A B le le_total P Pwlog Psym; 
      destruct (Bool.orb_true_elim _ _ (le_total A B)) as [i | i];
    [exact (Pwlog _ _ i) | exact  (Psym _ _ (Pwlog _ _ i))].
Qed. (*Defined.*)


(* tactics *)

Ltac prove_a1_exists l_from_points :=
  let A:=fresh in
  let B:=fresh in
  intros A B;  pose (l:=(l_from_points A B));
  revert l;case A; case B; intros l; exists l; exact (erefl true).

Ltac exists_p3 t u v :=
  exact (existT _ t
                (existT _  u 
                        (exist _   v (erefl true)))).

Ltac prove_a3_1 points_from_l P0 := let l := fresh "l" in
                   let x := fresh "x" in
                   intros l; pose (x:= points_from_l l); revert x;
                   case l; intros x;
                   exists_p3 (hd P0 x) (hd P0 (tl x)) (hd P0 (tl (tl x))).

Ltac handle incid eqp points_line x :=
  match goal with Ht  : is_true (incid ?T x),
                        Hz  : is_true (incid ?Z x),
                              Htz : ((@eqp ?T ?Z) = false)  |- _ =>
                  let HP := fresh in pose proof (points_line T Z x Ht Hz Htz) as HP;
                                     clear Ht Hz; rewrite HP(*; subst*)  end.

Ltac prove_a1_unique incid eqp points_line :=
  let A:=fresh in
  let B:= fresh in
  let HAB' := fresh in 
  let l1:=fresh in
  let l2:=fresh in
  let HAB:=fresh in
  let HAl1:=fresh in
  let HBl1:= fresh in
  let HAl2 := fresh in
  let HBl2 := fresh in
  intros A B l1 l2 HAB HAl1 HBl1 HAl2 HBl2;
  destruct A; destruct B; solve [discriminate |  
                                  handle incid eqp points_line l1;handle incid eqp points_line l2; exact (@erefl _ _)].

Ltac prove_uniqueness incid eqp points_line :=
  let P:= fresh in
  let Q:= fresh in
  let hypP := fresh in
  let HPQdiff := fresh in 
  let hypQ := fresh in
  let HPQ := fresh in 
  let l := fresh in
  let m := fresh in
  let Hl := fresh in
  let Hl' := fresh in
  let Hm := fresh in
  let Hm' := fresh in
   intros P Q l m Hl Hl' Hm Hm';case_eq (eqp P Q);
    [ intros; apply orTb | 
  destruct P; destruct Q; solve [discriminate |
  intros Hneq; handle incid eqp points_line l; handle incid eqp points_line m; rewrite Bool.orb_false_l; exact (erefl true)]].

Ltac solve_a3_2 := let p:= fresh in
                   intros p; case p;
                   let hypp:=fresh in let t := fresh in intros hypp t; discriminate.

Ltac exists_lppp point line l t u v :=
  exact (@ex_intro line _ l 
                   (@ex_intro point _ t
                              (@ex_intro point _ u 
                                 (@ex_intro point _ v  (erefl true))))).

Ltac wlog3 vA vB vC vle vle_total tac_sym tac_wlog :=
  let X:= fresh "A" in
  let Y:= fresh "B" in
  let Z:= fresh "C" in
  let Xsym := fresh "Xsym" in
  let Xsym1 := fresh "Xsym1" in
  let Xsym2 := fresh "Xsym2" in
  let Xle := fresh "Xle" in
  pattern vA,vB,vC; 
  match goal with vA:?ty |- (?P vA vB vC) =>
                  cbv beta;
                  revert vA vB vC;
                  assert (Xle:forall A B C:ty, vle A B && vle B C -> P A B C) ;
                  [ tac_wlog |
                    intros X Y Z; apply (wrapABC _ X Y Z vle vle_total _ Xle);clear Xle; tac_sym]
  end.

Ltac wlog2 vA vB vle vle_total tac_sym tac_wlog:=
  let X:= fresh "X" in
  let Y:= fresh "Y" in
  let Xsym := fresh "Xsym" in
  let Xle := fresh "Xle" in
  pattern vA,vB; 
  match goal with vA:?ty |- (?P vA vB) =>
                  cbv beta;
                  revert vA vB; 
                  assert (Xle:forall x y:ty, vle x y -> P x y);
                  [first [tac_wlog | idtac "You have to prove " Xle "."] |
                   assert (Xsym:forall x y:ty, P y x -> P x y);
                   [first [tac_sym |  idtac "You have to prove " Xsym "."] |
                    intros X Y; apply (wrapperAB  _ X Y vle vle_total _ Xle Xsym)
                  ]]
  end.

