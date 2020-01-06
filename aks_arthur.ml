(**
Usage:

  ocamlopt -o test aks_arthur.ml
	./test 20


Throughout this file, "log" describes logarithm in base 2.

Assume the type "int" to implemented as "Z" (i.e., bignums).
The operations on "int" have the following costs:
  - constant literal     O(1)
  - n = m                O(min (log n) (log m))
  - n <= m               O(min (log n) (log m))
  - n + m                O(log n + log m)
  - n / 2                O(log n)  (or O(1) in certain implem)
  - 2 * 2                O(log n)
  - n * m                O(log n * log m)  (naive)
  - pow n m              O(?)    (see code below)
  - n mod m              O(?)
  - n mod 2              O(log n)  (or O(1) in certain implem)
*)

(*-----------------------------------*)
(* Log, power, and roots *)

(* round below of log in base 2 *)
let rec log2_floor n =
  if n <= 1 then 0 else 1 + log2_floor (n / 2)

(* round up of log in base 2 (simpler and faster than proposed log2) *)
let rec log2_ceil n =
  log2_floor (2 * n - 1)

(* Question: in maths paper on AKS, I see mostly rounding below,
   is it really needed to round up here? *)
let log2 n =
  log2_ceil n

(* Is fast exponentiation really needed? for "int"? for polynomials? *)
let rec pow a n =
  if n = 0 then 1 else
  if n = 1 then a else
    let b = pow a (n / 2) in
    let b2 = b * b in
    if n mod 2 = 0
      then b2
      else b2 * a

(* TEMPORARY Naive power, in case it is sufficient *)
let rec pow_naive a n =
  if n = 0 then 1 else a * pow_naive a (n-1)

(* kth root of n *)
let root k n =
  let rec aux r =
    if r = 0 then 0 else
    let v = 2 * (aux (r / (pow 2 k))) in
    if pow (1 + v) k <= r then v + 1 else v
    in
  if k = 0 then 0 else aux n

(* to be an exact root *)
let is_root k n =
  (n = pow (root k n) k)

(* square root -- is there an optimized version for this one? maybe it's not needed?*)
let sqrt =
  root 2

(*-----------------------------------*)
(* Prime numbers *)


(* test if m and n are coprime *)
 
(* TEMPORARY variant for coprime, assuming nonnegative arguments *)
let rec coprime m n =
  if m < n then coprime n m else
  (* assuming n <= m *)
  if n = 0 || n = m
    then (m = 1)
    else coprime n (m mod n)

(* the order of n in Z_m *)
let order_mod m n =
  let rec aux m n r i k =
    let r1 = (r * n) mod m in
    if r1 = 1 then i
    else if 1 <= k then aux m n r1 (i + 1) (k - 1)
    else i in
  if coprime n m && 1 < m
    then aux m n 1 1 m
    else 0

(* totient function *)
let totient n =
  let rec aux acc d =
    if d < n then
      aux (if coprime n d then acc + 1 else acc) (d + 1)
    else acc
  in
  if n = 1 then 1 else aux 0 1

(* TEMPORARY totient function with iteration going downwards, without
   the tailrec optimization (which could be set up automatically by a compiler) *)
let totient n =
  let rec aux d =
    if d = 0 then 0 else
      (aux (d-1))
    + (if coprime n d then 1 else 0)
    in
  if n = 1 then 1 else aux (n-1)

(*-----------------------------------*)
(* Functions on List *)

(* [unlast l] returns a pair (v,t) such that [l = t++v::nil] *)
let rec unlast l =
  match l with
  | [] -> assert false
  | [x] -> (x, [])
  | x::l1 -> let (v,t1) = unlast l1 in (v,x::t1)

(* [replace i v l] returns a modified version of [l] where the
   item at index [i] is replaced with [v]. Assumes [i >= 0]. *)
let rec replace i v l =
  match l with
  | [] -> [] (* or "assert false" ? *)
  | x::t -> if i = 0 then v::t else x::(replace (i-1) v t)

(*-----------------------------------*)
(* Modular polynomials of degree [k-1], working modulo [n],
   represented as lists of length [k],
   with the coefficient of X^0 to the front, and X^(k-1) to the tail. *)

(* null polynomial, returns [0:: ... ::0] *)
let pzero k =
  List.init k (fun _ -> 0)

(* constant polynomial [x], returns [(x mod k)::0:: ... ::0] *)
let pconst n k x =
  replace 0 (x mod n) (pzero k)

(* X^n, returns the list [0::0 ... 0::1::0... 0::0] with
   the 1 at index [i mod k]. *)
let pXn n k i =
  replace (i mod k) 1 (pzero k)

(* multiplication by X, turns a list [t++x::nil] into [x::t]
   (argument n is not technically needed) *)
let pmulX n k v =
  let (x,t) = unlast v in
  x::t

(* Addition (argument k is not actually needed),
   returns the pointwise addition of two lists *)
let rec padd n k v1 v2 =
  match v1, v2 with
  | [], [] -> assert (k = 0); []
  | x1::t1, x2::t2 -> ((x1 + x2) mod n)::(padd n (k-1) t1 t2)
  | _ -> assert false

(* Multiplication by a scalar [a]
   (argument k is not actually needed) *)
let rec pscale n k a v =
  match v with
  | [] -> assert (k = 0); []
  | x::t -> ((a * x) mod n)::(pscale n (k-1) a t)

(* Multiplication of a polynomial [v1] with a polynomial [v2]
   (both lists of length [k]). *)
let rec pmul n k v1 v2 =
  let rec aux k2 v2 = (* [k2] is not actually needed *)
    match v2 with
    | [] -> assert (k2 = 0); pzero k
    | x::t2 -> padd n k (pscale n k x v1)
                        (pmulX n k (aux (k2-1) t2))
    in
  aux k v2

(* Power [p], using fast exponentiation *)
let rec ppow n k p v =
  if p = 0 then pconst n k 1 else
  if p = 1 then v else
    let r = ppow n k (p / 2) v in
    let r2 = pmul n k r r in
    if (p mod 2 = 0) then r2 else pmul n k v r2

(* Equality test (argument k is not actually needed) *)
let rec peq n k v1 v2 =
  match v1, v2 with
  | [], [] -> assert (k = 0); true
  | x1::t1, x2::t2 ->    ((x1 mod n) = (x2 mod n))
                      && (peq n (k-1) t1 t2)
  | _ -> assert false

(*-----------------------------------*)
(* The AKS algorithm *)

(* Phase 1 : n cannot be written as m ^ e with 2 <= e <= l *)
let power_free n l =
  let rec aux e =
    (e <= 1) || (not (is_root e n) && aux (e-1)) in
  1 < n && aux l

(* Phase 2 : search for a parameter *)

type aks_param_res = Nice of int | Bad | Good of int

let rec aks_param_search n a k c =
  if c < 1 then Bad
  else if (n mod k = 0) then Nice k
  else if (a <= k) && (a <= order_mod k n) then Good k
  else aks_param_search n a (k + 1) (c - 1)

let aks_param n l =
  let a = l * l in
  let k = 2 in
  let c = (l * (a * a)) / 2  in
  if l <= 1 then Nice n else aks_param_search n a k c

(* Phase 3 : introspection with modular polynomial *)
(* TEMPORARY is the test [1 <= r] equivalent to [r < 1] and thus to [r = 0] ? *)
(* TEMPORARY add a comment to help read the formula computed for [xncc] *)

let fpoly_intro_range n k l =
  let rec aux n k c r =
    if r < 1 then true else
      let cc = pconst n k c in
      let x = pXn n k 1 in
      let xcc = padd n k x cc in
      let xve = ppow n k n xcc in
      let xn = pXn n k n in
      let xncc = padd n k xn cc in
         peq n k xve xncc
      && aux n k (c + 1) (r - 1)
      in
  aux n k 1 (sqrt (totient k) * l)

(* Main algo *)

let aks n =
  let l = log2 n in
     power_free n l
  && (match aks_param n l with
      | Nice k -> (n = k)
      | Good k -> fpoly_intro_range n k l
      | Bad -> false)

(* Demo *)

let _ =
  let nmax = int_of_string Sys.argv.(1) in
  List.iter (fun n -> if aks n then Printf.printf "%d%! " n)
            (List.init nmax (fun i -> i));
  print_newline()

