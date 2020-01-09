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
  if n ^<= one then zero else one ^+ log2_floor (div2 n)

(* round up of log in base 2 (simpler and faster than proposed log2) *)
let rec log2_ceil n =
  log2_floor (pred (mul2 n))

(* Question: in maths paper on AKS, I see mostly rounding below,
   is it really needed to round up here? *)
let log2 n =
  log2_ceil n


(* kth root of n *)
let root k n =
  let rec aux r =
    if r ^= zero then zero else
    let v = mul2 (aux (shiftr r k)) in
    if ((succ v) ^^ k) ^<= r then succ v else v
    in
  if k ^= zero then zero else aux n

(* to be an exact root *)
let is_root k n =
  (n ^= ((root k n) ^^ k))

(* square root -- is there an optimized version for this one? maybe it's not needed?*)
let sqrt =
  root two

(*-----------------------------------*)
(* Prime numbers *)


(* test if m and n are coprime *)
 
(* the order of n in Z_m *)
let order_mod m n =
  let rec aux m n r i k =
    let r1 = (r ^* n) ^% m in
    if r1 ^= one then i
    else if one ^<= k then aux m n r1 (succ i) (pred k)
    else i in
  if coprime n m && one ^< m
    then aux m n one one m
    else zero

(* totient function *)
let totient n =
  let rec aux acc d =
    if d < n then
      aux (if coprime n d then succ acc else acc) (succ d)
    else acc
  in
  if n ^= one then one else aux zero one

(* TEMPORARY totient function with iteration going downwards, without
   the tailrec optimization (which could be set up automatically by a compiler) *)
let totient n =
  let rec aux d =
    if d ^= zero then zero else
      (aux (pred d))
    ^+ (if coprime n d then one else zero)
    in
  if n ^= one then one else aux (pred n)

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
  | x::t -> if i ^= zero then v::t else x::(replace (pred i) v t)

(*-----------------------------------*)
(* Modular polynomials of degree [k-1], working modulo [n],
   represented as lists of length [k],
   with the coefficient of X^0 to the front, and X^(k-1) to the tail. *)

(* null polynomial, returns [0:: ... ::0] *)
let rec pzero k =
  if k ^= zero then [] else zero :: (pzero (pred k))

(* constant polynomial [x], returns [(x mod k)::0:: ... ::0] *)
let pconst n k x =
  replace zero (x ^% n) (pzero k)

(* X^n, returns the list [0::0 ... 0::1::0... 0::0] with
   the 1 at index [i mod k]. *)
let pXn n k i =
  replace (i ^% k) one (pzero k)

(* multiplication by X, turns a list [t++x::nil] into [x::t]
   (argument n is not technically needed) *)
let pmulX n k v =
  let (x,t) = unlast v in
  x::t

(* Addition (argument k is not actually needed),
   returns the pointwise addition of two lists *)
let rec padd n k v1 v2 =
  match v1, v2 with
  | [], [] -> assert (k ^= zero); []
  | x1::t1, x2::t2 -> ((x1 ^+ x2) ^% n)::(padd n (pred k) t1 t2)
  | _ -> assert false

(* Multiplication by a scalar [a]
   (argument k is not actually needed) *)
let rec pscale n k a v =
  match v with
  | [] -> assert (k ^= zero); []
  | x::t -> ((a ^* x) ^% n)::(pscale n (pred k) a t)

(* Multiplication of a polynomial [v1] with a polynomial [v2]
   (both lists of length [k]). *)
let rec pmul n k v1 v2 =
  let rec aux k2 v2 = (* [k2] is not actually needed *)
    match v2 with
    | [] -> assert (k2 ^= zero); pzero k
    | x::t2 -> padd n k (pscale n k x v1)
                        (pmulX n k (aux (pred k2) t2))
    in
  aux k v2

(* Power [p], using fast exponentiation *)
let rec ppow n k p v =
  if p ^= zero then pconst n k one else
  if p ^= one then v else
    let r = ppow n k (div2 p) v in
    let r2 = pmul n k r r in
    if even p then r2 else pmul n k v r2

(* Equality test (argument k is not actually needed) *)
let rec peq n k v1 v2 =
  match v1, v2 with
  | [], [] -> assert (k ^= zero); true
  | x1::t1, x2::t2 ->    ((x1 ^% n) = (x2 ^% n))
                      && (peq n (pred k) t1 t2)
  | _ -> assert false

(*-----------------------------------*)
(* The AKS algorithm *)

(* Phase 1 : n cannot be written as m ^ e with 2 <= e <= l *)
let power_free n l =
  let rec aux e =
    (e ^<= one) || (not (is_root e n) && aux (pred e)) in
  one ^< n && aux l

(* Phase 2 : search for a parameter *)

type aks_param_res = Nice of bit list | Bad | Good of bit list

let rec aks_param_search n a k c =
  if c ^< one then Bad
  else if ((n ^% k) ^= zero) then Nice k
  else if (a ^<= k) && (a ^<= order_mod k n) then Good k
  else aks_param_search n a (succ k) (pred c)

let aks_param n l =
  let a = l ^* l in
  let k = two in
  let c = div2 (l ^* (a ^* a)) in
  if l ^<= one then Nice n else aks_param_search n a k c

(* Phase 3 : introspection with modular polynomial *)
(* TEMPORARY is the test [1 <= r] equivalent to [r < 1] and thus to [r = 0] ? *)
(* TEMPORARY add a comment to help read the formula computed for [xncc] *)

let fpoly_intro_range n k l =
  let rec aux n k c r =
    if r ^< one then true else
      let cc = pconst n k c in
      let x = pXn n k one in
      let xcc = padd n k x cc in
      let xve = ppow n k n xcc in
      let xn = pXn n k n in
      let xncc = padd n k xn cc in
         peq n k xve xncc
      && aux n k (succ c) (pred r)
      in
  aux n k one (sqrt (totient k) ^* l)

(* Main algo *)

let aks n =
  let l = log2 n in
     power_free n l
  && (match aks_param n l with
      | Nice k -> (n ^= k)
      | Good k -> fpoly_intro_range n k l
      | Bad -> false)

let test n = 
  let rec aux m n = 
       if aks m then Printf.printf "%d %!" (bnat_to_nat m);
       if 0 < n then aux (succ m) (n - 1) in
  aux zero n

(* Demo *)

let _ =
  let nmax = int_of_string Sys.argv.(1) in test nmax
  

