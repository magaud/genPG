open Array
open String
open List

(* computes the points and lines of PG(dim, rk) from GF(rk)^(dim+1) *)
(* it works successfully for (dim=3 and rk=23)  or (dim=7 and rk=3) *)
(* (but fails for dim=3 and rk=29 so far) *)

exception Arguments_wrong

let enumerate max =
  let rec enum n =
if (max = n) then [] else if (max=0) then [0] else n::enum (n+1) in enum 0;;

let rec all_vectors max size =
  if (size=1) then List.map (function x -> [x]) (enumerate max)
  else List.concat_map (function x -> (List.map (function y -> x::y) (all_vectors max (size-1)))) (enumerate max)

let all_vectors_non_zeros max size = List.tl (all_vectors max size)

let rec first_non_zero_is_one l =
  match l with [] -> false
             | 0::xs -> first_non_zero_is_one xs
             | 1::_ -> true
             | n::xs -> false

let rec first_non_zero l =
  match l with [] -> failwith "first_non_zero"
             | 0::xs -> first_non_zero xs
             | n::xs -> n

let rec scalar_mul k l max =
  match l with [] -> [] | x::xs ->  ((k*x) mod max)::(scalar_mul k xs max)

let rec add p q max =
  match p with [] -> [] | x::xs -> match q with [] -> [] | y::ys -> ((x+y) mod max)::add xs ys max

let rec multiplicative_inverse x max =
List.hd (List.filter (fun t -> x*t mod max = 1) (List.tl (enumerate max)))

let normalize t max =
  let f = first_non_zero t in
  let m = multiplicative_inverse f max in 
  scalar_mul m t max

let rec points n q =
  List.filter first_non_zero_is_one (all_vectors_non_zeros q (n+1));;

let rec smaller_int p q =
  match (p,q) with
    ([],[]) -> 0
  | ([],_) | (_,[]) -> failwith "not the same size"
  | (x::xs,y::ys) -> if (x>y) then 1 else if (x=y) then smaller_int xs ys else -1

let rec remove_dups l =
  match l with
    [] -> []
  | x::xs -> if List.mem x xs then remove_dups xs else x::remove_dups xs

let make_normalized_line x y rk =
  if (rk<2)
  then failwith "rk"
  else
    let new_points = List.map (fun t -> (normalize (add x (scalar_mul t y rk) rk)) rk) (List.tl (enumerate rk)) in
    List.sort smaller_int (x::y::new_points)

let rec given_one_point p1 l max acc =
  match l with [] -> acc
             | p2::xs ->
                if (p1<>p2)
                then
                  let new_line = make_normalized_line p1 p2 max in
                  if (List.mem new_line acc)
                  then given_one_point p1 xs max acc
                  else given_one_point p1 xs max (new_line::acc)
                else given_one_point p1 xs max acc

let rec all_lines l max =
  List.concat_map (function t -> given_one_point t l max []) l

let rec lines dim rk =
  remove_dups (all_lines (points dim rk) rk)


let arguments args =
  try
    let nb_args = Array.length Sys.argv - 1 in
    let n = int_of_string Sys.argv.(1) in
    let q = int_of_string Sys.argv.(2) in
    let _ = if ((nb_args = 3) || (nb_args >=5)) then raise Arguments_wrong in 
    let filename =
      if ((nb_args = 4)&&(Sys.argv.(3)="-o"))
      then Sys.argv.(4)
      else "defaultPG_" ^ Sys.argv.(1) ^  "_" ^ Sys.argv.(2) ^ ".v"
    in ((n,q),filename)
  with _ ->  let _ = print_string ("usage: " ^ Sys.argv.(0)^  " n q [ -o <output.v> ]\n") in exit(1)

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n ->
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let nb_points n q = (pow q (n+1) - 1) / (q - 1)
let nb_lines n q = ((pow q (n+1)-1)*((pow q (n+1)) -q)) / ((q*q-1)*(q*q-q))
let nb_points_per_line n q = q+1
let nb_lines_per_spread n q = nb_points n q / nb_points_per_line n q
let nb_spreads_per_packing n q = nb_lines n q / nb_lines_per_spread n q

let find_some_index pred li = match find_index pred li with Some t -> t | None -> failwith "find_some_index"

let l_from_points x y p l = find_some_index (fun t -> (List.mem (nth p x) t) && (List.mem (nth p y) t)) l

let list_elements c n = List.fold_right (fun x y -> (" | " ^ c ^ (string_of_int x) ^ y)) (enumerate n) ".\n";;

let list_incid p l =
  let indices li = List.fold_right
                     (fun x y -> (" | P" ^ (string_of_int x) ^ y))
                     (List.map (fun x -> match (List.find_index ((=) x) p) with Some t -> t | None -> failwith "find_index") li) "" in
  List.fold_right
    (fun x y -> ("| L" ^ (string_of_int x) ^ " => match p with " ^ (indices (List.nth l x)) ^ " => true | _ => false end\n" ^ y))
    (enumerate (List.length l)) "   end.\n";;

let list_lfp p l =
  List.fold_right
    (fun x y -> (" | P" ^  (string_of_int x) ^ " => match y with \n" ^
                   (List.fold_right (fun t u -> (" | P" ^ (string_of_int t) ^  " => L" ^ (string_of_int (l_from_points x t p l)) ^ u))
                      (enumerate (List.length p)) " end\n") ^ y))
    (enumerate (List.length p)) "end.\n"

let inter x t p l = let l1 = List.nth l x in
                    let l2 = List.nth l t in
                    let r = List.filter (fun x -> List.mem x l1) l2 in
                    try find_some_index (fun x -> x=(List.hd r)) p with _ -> 14

let inter_bool x t p l = let l1 = List.nth l x in
                           let l2 = List.nth l t in
                           let r = List.filter (fun x -> List.mem x l1) l2 in
                           try let _ = find_some_index (fun x -> x=(List.hd r)) p in true with _ -> false

let list_a2 p l =
  List.fold_right
    (fun x y -> (" | L" ^ (string_of_int x) ^ " => match m with \n" ^
                   (List.fold_right
                      (fun t u -> " | L" ^ (string_of_int t) ^ " => P" ^ (string_of_int (inter x t p l)) ^ u)
                      (enumerate (List.length l)) " end\n") ^ y))
    (enumerate (List.length l))
    "end.\n"

let list_pfl p l = List.fold_right
                     (fun x y -> "\n | L" ^ (string_of_int x) ^  " => [" ^  (String.concat ";" (List.map (fun t -> "P" ^ (string_of_int (find_some_index ((=) t) p))) (nth l x)) ^ "]" ^ y)) (enumerate (List.length l)) " end.\n"

let traversal l1 l2 l3 p l = try List.hd (List.filter (fun x -> (inter_bool x l1 p l)&&(inter_bool x l2 p l)&&(inter_bool x l3 p l)) (enumerate (List.length l))) with _ -> failwith "traversal: should not happen"

let list_a3_3 p l =
  let el = enumerate (List.length l) in 
  List.fold_right
    (fun l1 y ->
      " | L" ^ (string_of_int l1) ^ " => match l2 with \n" ^
        (List.fold_right
           (fun l2 u ->
             " | L" ^ (string_of_int l2) ^ " => match l1 with \n" ^
               (List.fold_right
                  (fun l3 b ->
                    let trav = (traversal l1 l2 l3 p l) in
                    " | L" ^ (string_of_int l3) ^ " =>  (L" ^ (string_of_int trav) ^ ", (P" ^ (string_of_int (inter l3 trav p l )) ^ ", P" ^ (string_of_int (inter l2 trav p l)) ^ ", P" ^ (string_of_int (inter l1 trav p l)) ^ "))" ^ b) el " end\n") ^ u) el " end\n") ^ y) el "end.\n"


let infos_pg n q =
  let _ = print_string ("#points = " ^ (string_of_int (nb_points n q)) ^ "\n") in
  let _ = print_string ("#lines = "  ^ (string_of_int (nb_lines n q)) ^ "\n") in
  let _ = print_string ("#points_per_line = " ^ (string_of_int (nb_points_per_line n q)) ^ "\n") in
  let _ = print_string ("#lines_per_spread = " ^  (string_of_int (nb_lines_per_spread n q)) ^ "\n") in
  let _ = print_string ("#spreads_per_packing = " ^ (string_of_int (nb_spreads_per_packing n q)) ^ "\n") in
  ()

let nl f = output_string f "\n"

let main () =
  let _ = print_string "This is genPG, a Rocq specification generator for finite projective spaces of the shape PG(n,q).\n" in
  let _ = print_string "(c) 2025 - Nicolas Magaud, ICube UMR 7357 CNRS Université de Strasbourg\n" in
  let ((n,q),filename) = arguments Sys.argv in
  let _ =
    print_string ("-*- generating PG(" ^ Sys.argv.(1) ^ "," ^ Sys.argv.(2) ^ ") in the file " ^ filename ^ ". -*-\n") in
  let _ = infos_pg n q in

  let p = points n q in
  let l = lines n q in
  let _ = print_string ("List.length (points " ^ (string_of_int n) ^ " " ^ (string_of_int q) ^ ") = " ^ (string_of_int(List.length p)) ^ "\n") in
  let _ = print_string ("List.length (lines " ^ (string_of_int n) ^ " " ^ (string_of_int q) ^ ") = " ^ (string_of_int(List.length l)) ^ "\n") in

  let f = open_out filename in
  let str_n = string_of_int n in
  let str_q = string_of_int q in

  let str_Proof = "Proof.\n" in
  let str_Qed = "Qed.\n" in

  let comment = "(* formal description of points, lines and their incident relation for PG(" ^ str_n ^ "," ^ str_q ^ ") *)\n" in

  let str_Require = "Require Import List.\nImport ListNotations.\nRequire Import PG.PG_spec.\n" in

  let str_points = "Inductive point : Set :=" ^ (list_elements "P" (nb_points n q)) in

  let str_lines = "Inductive line : Set :="  ^ (list_elements "L" (nb_lines n q)) in

  let str_incid = "Definition incid (p:point) (l:line) : bool := \n   match l with \n" ^ (list_incid p l) in

  (*  let str_incid_dec = "Lemma incid_dec : forall (A : point)(l : line), {incid A l} + {~incid A l}.\n" in *)
  let str_p2nat =
    "Definition p2nat (l:point) := match l with " ^
      (List.fold_right (fun t v -> "| P" ^ (string_of_int t) ^ "=> " ^ (string_of_int t) ^ "%nat " ^ v) (enumerate (List.length p)) "end.\n ") in

  let str_l2nat =
    "Definition l2nat (l:line) := match l with " ^
      (List.fold_right (fun t v -> "| L" ^ (string_of_int t) ^ "=> " ^ (string_of_int t) ^ "%nat " ^ v) (enumerate (List.length l)) "end.\n ") in


  let str_l_from_points = "Definition l_from_points (x:point) (y:point) : line := match x with \n" ^ (list_lfp p l) in

  let str_points_from_l = "Definition points_from_l (l:line) :=  match l with" ^ (list_pfl p l) in

  let str_def_eqp = "Definition eqp (x y: point) : bool := Nat.eqb (p2nat x) (p2nat y).\n" in
  let str_def_lep = "Definition lep (x y: point) : bool := Nat.leb (p2nat x) (p2nat y).\n" in

  let str_def_eql = "Definition eql (x y: line) : bool := Nat.eqb (l2nat x) (l2nat y).\n" in
  let str_def_lel = "Definition lel (x y: line) : bool := Nat.leb (l2nat x) (l2nat y).\n" in

  let str_a2 = "Definition f_a2 (l:line) (m:line) := match l with \n" ^ (list_a2 p l) in 

  let str_a3_3 = "Definition f_a3_3 (l1:line) (l2:line) (l3:line) :=  match l3 with\n" ^ (list_a3_3 p l) in 

  let _ = output_string f comment in
  let _ = nl f in
  let _ = output_string f str_Require in
  let _ = nl f in
  let _ = output_string f str_points in
  let _ = nl f in
  let _ = output_string f str_lines in
  let _ = nl f in
  let _ = output_string f str_incid in
  let _ = nl f in
  (*let _ = output_string f str_incid_dec in
  let _ = output_string f str_Proof in
  let _ = output_string f str_Qed in
  let _ = nl f in*)
  let _ = output_string f str_l_from_points in
  let _ = nl f in
  let _ = output_string f str_points_from_l in
  let _ = nl f in
  let _ = output_string f str_p2nat in
  let _ = nl f in
  let _ = output_string f str_def_eqp in
  let _ = nl f in
  let _ = output_string f str_def_lep in
  let _ = nl f in
  let _ = output_string f str_l2nat in
  let _ = nl f in
  let _ = output_string f str_def_eql in
  let _ = nl f in
  let _ = output_string f str_def_lel in
  let _ = nl f in
  let _ = output_string f str_a2 in
  let _ = nl f in

  let _ = output_string f str_a3_3 in
  let _ = nl f in

  let _ = close_out f in
  print_string "-*- end of program -*-\n"
;;

main ();;
