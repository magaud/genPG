(* formal description of points, lines and their incident relation for PG(3,2) *)

Require Import PG.PG_spec.

Inductive point : Set := | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11 | P12 | P13 | P14.

Inductive line : Set := | L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | L12 | L13 | L14 | L15 | L16 | L17 | L18 | L19 | L20 | L21 | L22 | L23 | L24 | L25 | L26 | L27 | L28 | L29 | L30 | L31 | L32 | L33 | L34.

Definition incid (p:point) (l:line) : bool := 
   match l with 
| L0 => match p with  | P0 | P1 | P2 => true | _ => false end
| L1 => match p with  | P0 | P3 | P4 => true | _ => false end
| L2 => match p with  | P2 | P4 | P5 => true | _ => false end
| L3 => match p with  | P1 | P3 | P5 => true | _ => false end
| L4 => match p with  | P2 | P3 | P6 => true | _ => false end
| L5 => match p with  | P1 | P4 | P6 => true | _ => false end
| L6 => match p with  | P0 | P5 | P6 => true | _ => false end
| L7 => match p with  | P0 | P7 | P8 => true | _ => false end
| L8 => match p with  | P2 | P8 | P9 => true | _ => false end
| L9 => match p with  | P1 | P7 | P9 => true | _ => false end
| L10 => match p with  | P2 | P7 | P10 => true | _ => false end
| L11 => match p with  | P1 | P8 | P10 => true | _ => false end
| L12 => match p with  | P0 | P9 | P10 => true | _ => false end
| L13 => match p with  | P6 | P10 | P11 => true | _ => false end
| L14 => match p with  | P5 | P9 | P11 => true | _ => false end
| L15 => match p with  | P4 | P8 | P11 => true | _ => false end
| L16 => match p with  | P3 | P7 | P11 => true | _ => false end
| L17 => match p with  | P6 | P9 | P12 => true | _ => false end
| L18 => match p with  | P5 | P10 | P12 => true | _ => false end
| L19 => match p with  | P4 | P7 | P12 => true | _ => false end
| L20 => match p with  | P3 | P8 | P12 => true | _ => false end
| L21 => match p with  | P0 | P11 | P12 => true | _ => false end
| L22 => match p with  | P6 | P8 | P13 => true | _ => false end
| L23 => match p with  | P5 | P7 | P13 => true | _ => false end
| L24 => match p with  | P4 | P10 | P13 => true | _ => false end
| L25 => match p with  | P3 | P9 | P13 => true | _ => false end
| L26 => match p with  | P2 | P12 | P13 => true | _ => false end
| L27 => match p with  | P1 | P11 | P13 => true | _ => false end
| L28 => match p with  | P6 | P7 | P14 => true | _ => false end
| L29 => match p with  | P5 | P8 | P14 => true | _ => false end
| L30 => match p with  | P4 | P9 | P14 => true | _ => false end
| L31 => match p with  | P3 | P10 | P14 => true | _ => false end
| L32 => match p with  | P2 | P11 | P14 => true | _ => false end
| L33 => match p with  | P1 | P12 | P14 => true | _ => false end
| L34 => match p with  | P0 | P13 | P14 => true | _ => false end
   end.

(*Definition l_from_points (x:point) (y:point) : line :=*)
