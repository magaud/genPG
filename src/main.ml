open Array
open String
open List

(* computes the points and lines from GF(rk)^(dim+1) for dim=3 and rk=23 *)
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

(*let rec mul p q max =
  match p with [] -> [] | x::xs -> match q with [] -> [] | y::ys -> ((x*y) mod max)::mul xs ys max*)

let rec multiplicative_inverse x max =
List.hd (List.filter (fun t -> x*t mod max = 1) (List.tl (enumerate max)))

let normalize t max =
  let f = first_non_zero t in
  let m = multiplicative_inverse f max in 
  scalar_mul m t max

let rec points n q =
  List.filter first_non_zero_is_one (all_vectors_non_zeros q (n+1));;

(*let rec smaller p q =
  match x with [] -> false
             | x::xs -> match q with [] -> true | y::ys -> x<y || ((x=y) && (smaller xs ys))*)

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
  (*let third = (add x y max) in
  if first_non_zero_is_one third
  then List.sort smaller_int [x; y; third]
  else
    if first_non_zero_is_one (add third third max)
    then List.sort smaller_int [x; y; (add third third max)]
    else failwith "cc"*)

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
      else cat "defaultPG_" (cat Sys.argv.(1) (cat "_" (cat Sys.argv.(2) ".v")))
    in ((n,q),filename)
  with _ ->  let _ = print_string (cat "usage: " (cat Sys.argv.(0) " n q [ -o <output.v> ]\n")) in exit(1)

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


let list_elements c n = List.fold_right (fun x y -> (cat (cat (cat " | " c) (string_of_int x)) y)) (enumerate n) ".\n";;
let list_incid p l =
let indices li = List.fold_right (fun x y -> cat (cat " | P" (string_of_int x)) y) (List.map (fun x -> match (List.find_index ((=) x) p) with Some t -> t | None -> failwith "find_index") li) "" in
  List.fold_right (fun x y -> (cat "| L" (cat (string_of_int x) (cat (" => match p with ") (cat (indices (List.nth l x)) (cat " => true | _ => false end\n" y)))))) (enumerate (List.length l)) "   end.\n";;

let list_lfp p l = List.fold_right (fun x y -> (cat " | P" (cat (string_of_int x) (cat " => match y with \n" (cat (List.fold_right (fun t u -> (cat " | P" (cat (string_of_int t) (cat " => L" (cat (string_of_int (l_from_points x t p l)) u))))) (enumerate (List.length p)) " end\n") y))))) (enumerate (List.length p)) "end.\n"

(*let common l1 l2 = match l1 with [] -> failwith "error_common" | x::xs -> match l2 with [] -> failwith "error_common" | y::ys -> if (x=y) return x else *)

let inter x t p l = let l1 = List.nth l x in
                    let l2 = List.nth l t in
                    let r = List.filter (fun x -> List.mem x l1) l2 in
                    try find_some_index (fun x -> x=(List.hd r)) p with _ -> 14

let list_a2 p l = List.fold_right (fun x y -> (cat " | L" (cat (string_of_int x) (cat " => match m with \n" (cat (List.fold_right (fun t u -> (cat " | L" (cat (string_of_int t) (cat " => P" (cat (string_of_int (inter x t p l)) u))))) (enumerate (List.length l)) " end\n") y))))) (enumerate (List.length l)) "end.\n"


  (*(List.fold_right (fun a b -> cat (cat "P" (string_of_int a)) (cat ";" b)) (List.map (fun t -> find_some_index ((=) t) p) (nth l x)) "] "*)

(*     List.fold_right (fun a b -> cat (string_of_int a) (cat ";" b)) (List.map (fun t -> find_index ((=) t) p) (nth l x)) "] "*)
let list_pfl p l = List.fold_right (fun x y -> cat "\n | L" (cat (string_of_int x) (cat " => [" (cat (String.concat ";" (List.map (fun t -> cat "P" (string_of_int (find_some_index ((=) t) p))) (nth l x))) (cat "]" y))))) (enumerate (List.length l)) " end.\n"

let infos_pg n q =
  let _ = print_string (cat "#points = " (cat (string_of_int (nb_points n q)) "\n")) in
  let _ = print_string (cat "#lines = "  (cat (string_of_int (nb_lines n q)) "\n")) in
  let _ = print_string (cat "#points_per_line = " (cat (string_of_int (nb_points_per_line n q)) "\n")) in
  let _ = print_string (cat "#lines_per_spread = " (cat (string_of_int (nb_lines_per_spread n q)) "\n")) in
  let _ = print_string (cat "#spreads_per_packing = " (cat (string_of_int (nb_spreads_per_packing n q)) "\n")) in
                                                                   ()
let nl f = output_string f "\n"

let main () =
  let _ = print_string "This is genPG, a Rocq specification generator for finite projective spaces of the shape PG(n,q).\n" in
  let _ = print_string "(c) 2025 - Nicolas Magaud, ICube UMR 7357 CNRS Université de Strasbourg\n" in
  let ((n,q),filename) = arguments Sys.argv in
  let _ =
    print_string (cat "-*- generating PG(" (cat Sys.argv.(1) (cat "," (cat Sys.argv.(2) (cat ") in the file " (cat filename ". -*-\n")))))) in
  let _ = infos_pg n q in

  let p = points n q in
  let l = lines n q in
  let _ = print_string (cat "List.length (points " (cat (string_of_int n) (cat " " (cat (string_of_int q) (cat ") = " (cat (string_of_int(List.length p)) "\n")))))) in
  let _ = print_string (cat "List.length (lines " (cat (string_of_int n) (cat " " (cat (string_of_int q) (cat ") = " (cat (string_of_int(List.length l)) "\n")))))) in

  let f = open_out filename in
  let str_n = string_of_int n in
  let str_q = string_of_int q in

  let str_Proof = "Proof.\n" in
  let str_Qed = "Qed.\n" in

  let comment =
    cat "(* formal description of points, lines and their incident relation for PG(" (cat str_n (cat "," (cat str_q ") *)\n"))) in

  let str_Require = "Require Import List.\nImport ListNotations.\nRequire Import PG.PG_spec.\n" in

  let str_points = cat "Inductive point : Set :=" (list_elements "P" (nb_points n q)) in

  let str_lines = cat "Inductive line : Set :="  (list_elements "L" (nb_lines n q)) in

  let str_incid = cat "Definition incid (p:point) (l:line) : bool := \n   match l with \n" (list_incid p l) in

  (*  let str_incid_dec = "Lemma incid_dec : forall (A : point)(l : line), {incid A l} + {~incid A l}.\n" in *)
  let str_p2nat =
    cat "Definition p2nat (l:point) := match l with " (List.fold_right (fun t v -> cat "| P" (cat (string_of_int t) (cat "=> " (cat (string_of_int t) (cat "%nat " v))))) (enumerate (List.length p)) "end.\n ") in

  let str_l2nat =
    cat "Definition l2nat (l:line) := match l with " (List.fold_right (fun t v -> cat "| L" (cat (string_of_int t) (cat "=> " (cat (string_of_int t) (cat "%nat " v))))) (enumerate (List.length l)) "end.\n ") in


  let str_l_from_points = cat "Definition l_from_points (x:point) (y:point) : line := match x with \n" (list_lfp p l) in

  let str_points_from_l = cat "Definition points_from_l (l:line) :=  match l with" (list_pfl p l) in

  let str_def_eqp = "Definition eqp (x y: point) : bool := Nat.eqb (p2nat x) (p2nat y).\n" in
  let str_def_lep = "Definition lep (x y: point) : bool := Nat.leb (p2nat x) (p2nat y).\n" in

  let str_def_eql = "Definition eql (x y: line) : bool := Nat.eqb (l2nat x) (l2nat y).\n" in
  let str_def_lel = "Definition lel (x y: line) : bool := Nat.leb (l2nat x) (l2nat y).\n" in

  let str_a2 = cat "Definition f_a2 (l:line) (m:line) := match l with \n" (list_a2 p l) in 


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
  
  let _ = close_out f in
  print_string "-*- end of program -*-\n"
;;

main ();;
