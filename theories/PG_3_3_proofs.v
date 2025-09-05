Require Import ssreflect ssrfun ssrbool.

Require Import PG.lemmas_and_tactics.
Require Import  PG.PG_3_3.

(** a1_exists : existence of a line generated from 2 points *)

Lemma a1_exists : forall A B : point,
    {l : line | incid A l && incid B l}.
Proof.
  idtac "-> proving a1_exists".
  time (prove_a1_exists l_from_points).
  Time Qed.
Check a1_exists.

(** a3_1 : every line has at least three distinct points *)

Definition dist_3p  (A B C :point) : bool := (negb (eqp A B)) && (negb (eqp A C)) && (negb (eqp B C)).

Lemma a3_1 : 
  forall l:line,{A:point &{B:point &{ C:point| 
                                      dist_3p A B C && (incid A l && incid B l && incid C l)}}}.
Proof.
  idtac "-> proving a3_1".
  time (prove_a3_1 points_from_l P0).
Qed. 
Check a3_1.

(** a1_unique : unicity of the line generated from 2 points *)
(** l_from_points is actually a1_exists *)

Lemma points_line : forall T Z:point, forall x:line,
      incid T x -> incid Z x -> (eqp T Z)= false -> x = (l_from_points T Z).
Proof.
  idtac "-> proving points_line".
  time (intros T Z x;
        case x; case T; intros HTx;
        first [ discriminate | 
                case Z; intros HZx HTZ;
                solve  [ discriminate |  exact (@erefl line _) | apply False_rect; auto ] ]).
Time Qed.
Check points_line.

Lemma a1_unique:forall (A B :point)(l1 l2:line),
    eqp A B = false ->
    incid A l1 -> incid B l1 -> incid A l2 -> incid B l2 -> l1=l2.
Proof.
  idtac "-> proving a1_unique".
  time(prove_a1_unique incid eqp points_line).
Time Qed.
Check a1_unique.

Lemma point_dec : forall T U:point, {T=U}+{~T=U}.
Proof.
  intros T U; case T; case U;
    solve [left; exact (@erefl point _) | right; discriminate].
Defined.

Lemma uniqueness : forall (A B :point)(l1 l2:line),
    incid A l1 -> incid B l1  -> incid A l2 -> incid B l2 ->
    (eqp A B) || (eql l1 l2).
Proof.
  idtac "-> proving uniqueness".
  time(prove_uniqueness incid eqp points_line).
  Time Qed.
Check uniqueness.

(** a3_2 : there exists 2 lines which do not intersect, i.e. dim >= 3  *)

Lemma a3_2 : exists l1:line, exists l2:line, forall p:point, ~(incid p l1 && incid p l2). 
Proof.
  idtac "-> proving a3_2".
  exists L0; exists L29;intros p; case p; 
    let hypp:=fresh in let t := fresh in intros t; discriminate.
  (*Time (prove_a3_2).*) 
  Time Qed.
Check a3_2.

(* a3_3 : given 3 lines, there exists a line which intersects these 3 lines *)

Definition Intersect_In (l1 l2 :line) (P:point) := incid P l1 && incid P l2.

Definition dist_3l (A B C :line) : bool :=
  (negb (eql A B)) && (negb (eql A C)) && (negb (eql B C)).

Lemma a3_3_simple :
  forall v1 v2 v3:line,
    lel v1 v2-> lel v2 v3 ->
    dist_3l v1 v2 v3 ->
    exists v4 :line, exists T1:point, exists T2:point, exists T3:point,
            (Intersect_In v1 v4 T1) && (Intersect_In v2 v4 T2) && (Intersect_In v3 v4 T3).
Proof.
  idtac "-> proving a3_3_simple".
   unfold dist_3l; intros v1 v2 v3 Hv1v2 Hv2v3 Hd;
    pose (t:=f_a3_3 v1 v2 v3); revert Hv1v2 Hv2v3 Hd t.
  case v1;
    
    abstract (time (case v2; intros hp1p2; first [exact (degen_bool _ hp1p2) | 
                                                  
                                                  (case v3;
                                                   intros hp1p3 hdist x;
                                                   solve [ (exact (degen_bool _ hp1p3)) | (exact (degen_bool _ hdist)) |
                                                           exists_lppp point line (fst x) (fst (fst (snd x))) (snd (fst (snd x))) (snd (snd x))
         ])])).
Time Qed.
Check a3_3_simple.

Lemma eql_sym : forall x y:line, eql x y = eql y x.
Proof.
  idtac "proving eqL_sym".
  time (intros; apply PeanoNat.Nat.eqb_sym). 
  Time Qed.
Check eql_sym.

Lemma eqp_sym : forall x y:point, eqp x y = eqp y x.
Proof. 
  idtac "proving eqP_sym".
  time (intros;apply PeanoNat.Nat.eqb_sym).
  Time Qed.
Check eqp_sym.

Require Import Arith.

Lemma lel_total : forall A B, lel A B || lel B A.
Proof.
intros A B; apply Bool.orb_true_iff;
destruct (le_ge_dec (l2nat A) (l2nat B));
  [left; apply leb_correct; assumption |
right; apply leb_correct; unfold ge in *; assumption].
Qed.

Lemma a3_3 : forall v1 v2 v3:line,
    dist_3l v1 v2 v3 -> exists v4 :line,  exists T1:point, exists T2:point, exists T3:point,
            (Intersect_In v1 v4 T1) && (Intersect_In v2 v4 T2) && (Intersect_In v3 v4 T3).
Proof.
  idtac "-> proving a3_3".
  intros v1 v2 v3.
  wlog3 v1 v2 v3 lel lel_total idtac idtac.
  
  intros; apply a3_3_simple.
  destruct (and_bool_lr _ _  H) as [Ha1 Ha2]; exact Ha1.
  destruct (and_bool_lr _ _  H) as [Ha1 Ha2]; exact Ha2.
  assumption.

  intros.
  assert (Hd: dist_3l x z y).
  unfold dist_3l in *;
    apply circ3;apply circ3; apply (exchL _ _ eql_sym); apply circ3; apply comm12L; assumption.
  destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
  exists v4; exists t1; exists t3; exists t2.
  apply circ3; apply circ3; apply comm12L; assumption.
  
  intros.
  assert (Hd: dist_3l y x z).
  unfold dist_3l in *; apply (exchL _ _ eql_sym); apply circ3; apply circ3; apply comm12L; assumption.
  destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
  exists v4; exists t2; exists t1; exists t3.
  apply comm12L; assumption.
  
  intros.
  assert (Hd: dist_3l y z x).
  unfold dist_3l in *.
  apply circ3; apply (exchL _ _ eql_sym); apply circ3; apply (exchL _ _ eql_sym); apply circ3; apply circ3; assumption.
  destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
  exists v4; exists t3; exists t1; exists t2.
  apply circ3; assumption.
  
  intros.
  assert (Hd: dist_3l z x y).
  unfold dist_3l in *.
  apply (exchL _ _ eql_sym); apply circ3; apply (exchL _ _ eql_sym); apply circ3; assumption.
  destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
  exists v4; exists t2; exists t3; exists t1.
  apply circ3; apply circ3; assumption.
  
  intros.
  assert (Hd: dist_3l z y x).
  unfold dist_3l in *.
   apply (exchL _ _ eql_sym); apply circ3; apply (exchL _ _ eql_sym); apply circ3; apply (exchL _ _ eql_sym); 
    apply circ3; apply circ3; apply comm12L; assumption.
  destruct  (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
  exists v4; exists t3; exists t2; exists t1.
  apply comm12L; apply circ3;apply circ3; assumption. 
  Time Qed.

(** a2 : Pasch's axiom *)

Definition dist_4p  (A B C D:point) : bool :=
  (negb (eqp A B)) && (negb (eqp A C)) && (negb (eqp A D))
  && (negb (eqp B C)) && (negb (eqp B D)) && (negb (eqp C D)).

Ltac findp' := match goal with
                 |-  (@ex point (fun J:point => 
                                   is_true (andb (incid J ?m) 
                                                 (incid J ?p))))
                     /\ (@ex point (fun K:point => 
                                      is_true (andb (incid K ?q) 
                                                    (incid K ?r))))=> 
                 exact (conj (ex_intro _  (f_a2 m p) (erefl true))
                             (ex_intro _  (f_a2 q r) (erefl true)))
               end.

Lemma a2_conj_specific :
  forall A B C D:point, lep A B -> lep C D ->
                        let lAB := l_from_points A B in
                        let lCD := l_from_points C D in
                        let lAC := l_from_points A C in
                        let lBD := l_from_points B D in
                        let lAD := l_from_points A D in
                        let lBC := l_from_points B C in 
                        
                        dist_4p A B C D -> 
                        incid A lAB && incid B lAB ->  
                        incid C lCD && incid D lCD -> 
                        incid A lAC && incid C lAC -> 
                        incid B lBD && incid D lBD ->
                        incid A lAD && incid D lAD ->
                        incid B lBC && incid C lBC ->
                        
                        (exists I:point, incid I lAB && incid I lCD) ->
                        (exists J:point, (incid J lAC && incid J lBD)) /\
                        (exists K:point, (incid K lAD && incid K lBC)).
Proof.
  idtac "-> proving a2_conj_specific".
  intros A B C D HleAB HleCD lAB lCD lAC lBD lAD lBC Hdist HlAB HlCD HlAC HlBD HlAD HlBC Hex;
    destruct (and_bool_lr _ _ Hdist) as [Hdist1 HCD]; clear Hdist;
      destruct (and_bool_lr _ _ Hdist1) as [Hdist2 HBD]; clear Hdist1;
           destruct (and_bool_lr _ _ Hdist2) as [Hdist3 HBC]; clear Hdist2;
             destruct (and_bool_lr _ _ Hdist3) as [Hdist4 HAD]; clear Hdist3;
               destruct (and_bool_lr _ _ Hdist4) as [HAB HAC]; clear Hdist4;
        revert A B HleAB HAB lAB HlAB C HBC HAC lBC HlBC lAC HlAC D HleCD HAD HBD HCD lAD HlAD lBD HlBD lCD HlCD Hex.

     time (intros A B; case A; case B; intros HlePAB HAB lAB HlAB). 
     par: abstract (time (first [exact (degen_bool _ HlePAB) |exact (degen_bool _ HAB) | exact (degen_bool _ HlAB)| 



      (intros C; case C; intros HBC HAC lBC HlBC lAC HlAC; 
           first [  exact (degen_bool _ HBC) | exact (degen_bool _ HAC)
                        |
           
                        (intros D; case D; intros HleCD HAD HBD HCD lAD HlAD lBD HlBD lCD HlCD Hex;

                         first [ exact (degen_bool _ HleCD) | exact (degen_bool _ HAD)
                                 | exact (degen_bool _ HBD) | exact (degen_bool _ HCD)
                                 
                                 | case Hex; intros t; case t; intros Ht;
                                 first [exact (degen_bool _ Ht) | findp'] ])])])).
  Qed.
  Check a2_conj_specific.
  
  Lemma l_from_points_sym : forall x y:point, l_from_points x y = l_from_points y x.
  Proof.
    intros x y; case x; case y; apply erefl.
  Qed.

Require Import Arith.

Lemma lep_total : forall A B, lep A B || lep B A.
Proof.
intros A B; apply Bool.orb_true_iff;
destruct (le_ge_dec (p2nat A) (p2nat B));
  [left; apply leb_correct; assumption |
right; apply leb_correct; unfold ge in *; assumption].
Qed.

Lemma a2_conj :
    forall A B C D:point, dist_4p A B C D -> 
         let lAB := l_from_points A B in
         let lCD := l_from_points C D in
         let lAC := l_from_points A C in
         let lBD := l_from_points B D in
         let lAD := l_from_points A D in
         let lBC := l_from_points B C in 
         
         incid A lAB && incid B lAB ->  
         incid C lCD && incid D lCD -> 
         incid A lAC && incid C lAC -> 
         incid B lBD && incid D lBD ->
         incid A lAD && incid D lAD ->
         incid B lBC && incid C lBC ->
         
         (exists I:point, incid I lAB && incid I lCD) ->
         (exists J:point, (incid J lAC && incid J lBD)) /\
         (exists J:point, (incid J lAD && incid J lBC)).
  Proof.
    intros A B.
    wlog2 A B lep lep_total idtac idtac.
    intros A B HleAB.
    intros C D.
    wlog2 C D lep lep_total idtac ltac:(intros; apply a2_conj_specific; assumption || exact I).
    (* other cases *)

    intros C D Hr.

    intros lAB lCD lAC lBD lAD lBC Hdist HlAB HlCD HlAC HlBD HlAD HlBC Hex.
    assert (Hd' : dist_4p A B D C).
    unfold dist_4p in *.
    apply circ6; apply comm12P; apply circ6; apply circ6 ; apply comm12P; apply circ6;
    apply circ6; apply (exchP _ _ eqp_sym); apply circ6; assumption.

    assert (HlDC:(incid D (l_from_points D C) && incid C (l_from_points D C))).
    apply circ2; rewrite l_from_points_sym; assumption. 
    assert (Hex': (exists I : point, incid I (l_from_points A B) && incid I (l_from_points D C))).
    rewrite (l_from_points_sym D C); assumption.
    generalize (Hr Hd' HlAB HlDC HlAD HlBC HlAC HlBD Hex').
    solve [intuition].

    intros A B Hr C D.
    intros Hd lAB lCD lAC lBD lAD lBC HlAB HlCD HlAC HlBD HlAD HlBC Hex.
    assert (Hd':  dist_4p B A C D).
    unfold dist_4p in *.
    apply (exchP _ _ eqp_sym); apply circ6; apply circ6; apply comm12P; apply circ6; apply comm12P;
      apply circ6; apply circ6; apply circ6; apply circ6; apply comm12P; apply circ6;
        apply comm12P; apply circ6; apply circ6; apply circ6; apply circ6; assumption.

    assert (HlBA:incid B (l_from_points B A) && incid A (l_from_points B A)).
    apply circ2; rewrite l_from_points_sym; assumption.
    assert (HlDB:(incid D (l_from_points D B) && incid B (l_from_points D B))).
    apply circ2; rewrite l_from_points_sym; assumption.
    assert (Hex':(exists I : point, incid I (l_from_points B A) && incid I (l_from_points C D))).
    rewrite (l_from_points_sym B A); assumption.

    generalize (Hr C D Hd' HlBA HlCD HlBC HlAD HlBD HlAC Hex').
    intros (He1,He2).
    split.
    destruct He2 as [e2 He2]; apply circ2 in He2; exists e2; assumption.
    destruct He1 as [e1 He1]; apply circ2 in He1; exists e1; assumption.
  Qed.

  Check a2_conj.

  Lemma points_line' : forall T Z:point, forall x:line,
        incid T x -> incid Z x -> ~~ eqp T Z -> x = (l_from_points T Z).
  Proof.
    idtac "-> proving points_line".
    time (intros T Z x;
           case x ; 
           case T; intros  HTx;
           first [ discriminate | 
                   case Z; intros  HZx HTZ;
                   solve [discriminate | apply False_rect; auto | exact (@erefl line _)]]).
    Time Qed.

  Ltac handle' x :=
    match goal with Ht  : is_true (incid ?T x),
                          Hz  : is_true (incid ?Z x),
                                Htz : is_true (negb (eqp ?T ?Z)) |- _ =>
                    let HP := fresh in pose proof (points_line' T Z x Ht Hz Htz) as HP;
                                       clear Ht Hz; rewrite HP(*; subst*)  end.

  
  Ltac handle_eff l P Q HlAB:= assert (l=l_from_points P Q);[
                                 assert (incid P l) by ( solve [intuition]);
                                 assert (incid Q l) by ( solve [intuition]);
                                 handle' l; apply erefl | idtac].

  Lemma incid_l_from_point1 : forall x y, incid x (l_from_points x y).
  Proof.
    intros x y; case x; case y; trivial.
  Qed.

  Lemma incid_l_from_point2 : forall x y, incid y (l_from_points x y).
  Proof.
    intros x y; case x; case y; trivial.
  Qed.

  Lemma a2 : forall A B C D:point, forall lAB lCD lAC lBD :line,
        dist_4p A B C D -> 
        incid A lAB && incid B lAB ->
        incid C lCD && incid D lCD ->
        incid A lAC && incid C lAC ->
        incid B lBD && incid D lBD ->
        (exists I:point, incid I lAB && incid I lCD) ->
        exists J:point, incid J lAC && incid J lBD.
  Proof.
    idtac "-> proving a2".
    intros A B C D lAB lCD lAC lBD Hdist HlAB HlCD HlAC HlBD Hex.
    destruct (and_bool_lr _ _ HlAB) as [HlAB1 HlAB2]; 
      destruct (and_bool_lr _ _ HlCD) as [HlCD1 HlCD2]; 
      destruct (and_bool_lr _ _ HlAC) as [HlAC1 HlAC2]; 
      destruct (and_bool_lr _ _ HlBD) as [HlBD1 HlBD2]; 
      destruct (and_bool_lr _ _ Hdist) as [Hdist1 HCD]; 
      destruct (and_bool_lr _ _ Hdist1) as [Hdist2 HBD]; 
      destruct (and_bool_lr _ _ Hdist2) as [Hdist3 HBC]; 
      destruct (and_bool_lr _ _ Hdist3) as [Hdist4 HAD]; 
      destruct (and_bool_lr _ _ Hdist4) as [HAB HAC].
    
    handle_eff lAB A B HlAB.
    handle_eff lCD C D HlCD.
    handle_eff lAC A C HlAC.
    handle_eff lBD B D HlBD.
    rewrite H in HlAB.
    rewrite H0 in HlCD.
    rewrite H1 in HlAC.
    rewrite H2 in HlBD.
    rewrite H in Hex.
    rewrite H0 in Hex.
    assert (HlAD:(incid A (l_from_points A D) && incid D (l_from_points A D))).
    apply Bool.andb_true_iff; split;
      [apply incid_l_from_point1 | apply incid_l_from_point2].
    
    assert (HlBC: (incid B (l_from_points B C) && incid C (l_from_points B C))).
    apply Bool.andb_true_iff; split;
      [apply incid_l_from_point1 | apply incid_l_from_point2].
    
    rewrite H1.
    rewrite H2.
    elim (a2_conj A B C D Hdist HlAB HlCD HlAC HlBD HlAD HlBC Hex).
    intros; assumption.
  Time Qed.
  Check a2.
(*
Module PS : ProjectiveSpace.

  Definition point := pg32_inductive.point.
  Definition line := pg32_inductive.line.

  Definition incid := incid. 
  Definition eqP := eqP.
  Definition eqL := eqL.

  Lemma a1_exists : forall A B : point,
      {l : line | incid A l && incid B l}.
  Proof.
    exact a1_exists.  
  Qed.

  Lemma uniqueness : forall (A B :point)(l1 l2:line),
      incid A l1 -> incid B l1  -> incid A l2 -> incid B l2 -> eqP A B || eqL l1 l2.
  Proof.
    exact uniqueness.
  Qed.

  Definition dist_4p := dist_4p.

    Lemma a2 : forall A B C D:point, forall lAB lCD lAC lBD :line,
        dist_4p A B C D -> 
        incid A lAB && incid B lAB ->
        incid C lCD && incid D lCD ->
        incid A lAC && incid C lAC ->
        incid B lBD && incid D lBD ->
        (exists I:point, incid I lAB && incid I lCD) ->
        exists J:point, incid J lAC && incid J lBD.
    Proof.
      exact a2.
    Qed.

    Definition dist_3p := dist_3p.

    Lemma a3_1 : forall l:line,
        {A:point &{B:point &{ C:point| 
                              dist_3p A B C && (incid A l && incid B l && incid C l)}}}.
    Proof.
      exact a3_1.
    Qed.

    Lemma a3_2 : exists l1:line, exists l2:line, forall p:point, ~(incid p l1 && incid p l2). 
    Proof.
      exact a3_2.
    Qed.

    Definition Intersect_In := Intersect_In.
    Definition dist_3l := dist_3l.

    Lemma a3_3 : forall v1 v2 v3:line,
      dist_3l v1 v2 v3 -> exists v4 :line,  exists T1:point, exists T2:point, exists T3:point,
             (Intersect_In v1 v4 T1) && (Intersect_In v2 v4 T2) && (Intersect_In v3 v4 T3).
  Proof.
    exact a3_3.
  Qed.

End PS.
*)
