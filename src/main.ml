open Array
open String
open List

(* computes the points and lines from GF(rk)^(dim+1) for dim=3 and rk=13 *)
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

let infos_pg n q =
  let _ = print_string (cat "#points = " (cat (string_of_int (nb_points n q)) "\n")) in
  let _ = print_string (cat "#lines = "  (cat (string_of_int (nb_lines n q)) "\n")) in
  let _ = print_string (cat "#points_per_line = " (cat (string_of_int (nb_points_per_line n q)) "\n")) in
  let _ = print_string (cat "#lines_per_spread = " (cat (string_of_int (nb_lines_per_spread n q)) "\n")) in 
  let _ = print_string (cat "#spreads_per_packing = " (cat (string_of_int (nb_spreads_per_packing n q)) "\n")) in
                                                                   ()


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
  print_string "-*- end of program -*-\n"
;;

main ();;
