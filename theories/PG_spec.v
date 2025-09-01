Class IncidenceStructure := {
    Point : Set;
    Line : Set;
    Incid : Point -> Line -> Prop;

    incid_dec : forall (A : Point)(l : Line), {Incid A l} + {~Incid A l}
  }.

Class PreProjectiveSpace `(IS : IncidenceStructure) := {

    a1 (* a1_exist*) : forall (A B : Point) , {l : Line | Incid A l /\ Incid B l};
    a3 (*uniqueness*) : forall (A B : Point)(l1 l2 : Line),
      Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A = B \/ l1 = l2;
    a4 (*three_points*) : forall l : Line,
      {A : Point & {B : Point & {C : Point |
           (~ A = B /\ ~ A = C /\ ~ B = C /\ Incid A l /\ Incid B l /\ Incid C l)}}}
  }.


Class ProjectivePlane `(PP : PreProjectiveSpace) := {
    a2 (*a2_exist*) : forall (l1 l2 : Line), {A : Point | Incid A l1 /\ Incid A l2};
    a5 (*lower_dimension*) : {l1 : Line & {l2 : Line | l1 <> l2}}; 

  }.

Class ProjectiveSpace3Dplus `(PP : PreProjectiveSpace) := {
    a2_pasch (*pasch*) : forall A B C D : Point, forall lAB lCD lAC lBD : Line,
  ~ A = B /\ ~ A = C /\ ~ A = D /\ ~ B = C /\ ~ B = D /\ ~ C = D ->
  Incid A lAB /\ Incid B lAB ->
  Incid C lCD /\ Incid D lCD ->
  Incid A lAC /\ Incid C lAC ->
  Incid B lBD /\ Incid D lBD ->
  (exists I : Point, (Incid I lAB /\ Incid I lCD)) -> exists J : Point, (Incid J lAC /\ Incid J lBD);
    lower_dimension : {l1 : Line & {l2 : Line | forall p : Point, ~(Incid p l1 /\ Incid p l2)}}
  }.

(* how to fix the dimensions of a projective space >=3 *)

