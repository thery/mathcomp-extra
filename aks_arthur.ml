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
   is it really needed to round up here? 
   answer: the formal proof mostly uses log2n because it gives the 
   simple bound n <= 2 ^ (log2n n)
   rather than having to use n < 2 ^ (log2_floor n + 1)
   if needed I could change the formal proof to use log2_floor
   *)
let log2 n =
  log2_ceil n

(* Is fast exponentiation really needed? for "int"? for polynomials? 
  answer : I think that for int naive is enough, since pow is only
  needed in power_free and we know in this case that the exponent is always
  smaller than log2 n, for polynomials I am afraid it is needed as we do
  (X + c) ^ n, if we are not doing with fast exponential we are not
  P(log2 n) anymore 
  *)
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

(* square root -- is there an optimized version for this one? 
   maybe it's not needed?
   answer : I think it is not needed*)
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

(* the order of n in Z_m : find the smallest r such that n ^ r = 1 mod m *)
let order_mod m n =
  let rec aux m n r i k =
    let r1 = (r * n) mod m in
    if r1 = 1 then i
    else if 1 <= k then aux m n r1 (i + 1) (k - 1)
    else i in
  if coprime n m && 1 < m
    then aux m n 1 1 m
    else 0

(* totient function : number of elements smaller than n that are coprime with n
   if this function is hard to prove we can avoid while being still polynomial
   see  fpoly_intro_range
*)
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
(* Modular polynomials of degree [k-1], working with coefficient modulo [n]
   and modulo the polynomial (X ^ k - 1) represented as lists of length [k],
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
   (argument n is not technically needed) 
   X * (\sum_(i < k) a_i X^ i)  modulo (X^k - 1) =
        a_k-1 + (\sum_(1 <= i < k) a_(i - 1) X^ i)  
*)
let pmulX n k v =
  let (x,t) = unlast v in
  x::t

(* Addition (argument k is not actually needed),
   returns the pointwise addition of two lists 
   (x1 + X * t1) + (x2 + X * t2) = (x1 + x2) + X * (t1 + t2)
   *)
let rec padd n k v1 v2 =
  match v1, v2 with
  | [], [] -> assert (k = 0); []
  | x1::t1, x2::t2 -> ((x1 + x2) mod n)::(padd n (k-1) t1 t2)
  | _ -> assert false

(* Multiplication by a scalar [a]
   (argument k is not actually needed)
   a * (x + X * t) = (a* x) + X * (a * t)
*)
  
let rec pscale n k a v =
  match v with
  | [] -> assert (k = 0); []
  | x::t -> ((a * x) mod n)::(pscale n (k-1) a t)

(* Multiplication of a polynomial [v1] with a polynomial [v2]
   (both lists of length [k]).
   v1 * (x + X * t2) = x * v1 + X * (v1 * t2)   
*)

  
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

(* Equality test (argument k is not actually needed)
   (x1 + X * t1) = (x2 + X * t2)  iff
   (x1 = x2) and (t1 = t2)
*)
let rec peq n k v1 v2 =
  match v1, v2 with
  | [], [] -> assert (k = 0); true
  | x1::t1, x2::t2 ->    ((x1 mod n) = (x2 mod n))
                      && (peq n (k-1) t1 t2)
  | _ -> assert false

(*-----------------------------------*)
(* The AKS algorithm *)

(* NB : in order to avoid computing log2 n again and again, 
  in most functions, there is a companion argument to n 
  (the number we try to assert its primality) that is l
  l is meant to be initially set to log2 n *)

(* Phase 1 : n cannot be written as m ^ e with 2 <= e <= l
   since 2 <= m, the largest possible value for e with n = m ^ e
   is log2 n since n <= 2 ^ (log2 n)
 *)
let power_free n l =
  let rec aux e =
    (e <= 1) || (not (is_root e n) && aux (e-1)) in
  1 < n && aux l

(* Phase 2 : search for a parameter *)

type aks_param_res = Nice of int | Bad | Good of int

(* this is the recursive part of the search. 
   we try to find an h (k <= h < k + c) such that it is greater of a (a <= h)
   and its order in Z_n is also greater than a (a <= order_mod k n)
   If we find such h, we return it (Good h)
   If during the search, it occurs that the candidate h is in fact
   a divisor of n, we return the witness that n is not prime (Nice h)
   If we find no such h we return Bad *)

let rec aks_param_search n a k c =
  if c < 1 then Bad
  else if (n mod k = 0) then Nice k
  else if (a <= k) && (a <= order_mod k n) then Good k
  else aks_param_search n a (k + 1) (c - 1)

(* run the search with some carefully choosen values: 
   - n is the number whose primality is checked 
   - l is meant to have value log2 n
   - the bound parameter of the search is set to  (log2 n) ^ 2 
   the range for the search is 2 <= h < (log2 n) ^ 5 /2 + 2
   with this setting the search will always be positive 
  (Bad will never been returned) 
  anyway when an h is returned (Good h or Nice h) it will always
  be smaller than (log2 n) ^ 5) /2 + 1 *)
  
let aks_param n l =
  let a = l * l in
  let k = 2 in
  let c = (l * (a * a)) / 2  in
  if l <= 1 then Nice n else aks_param_search n a k c

(* Phase 3 : introspection with modular polynomial *)
(*  n is the prime we want to check
    k is the result of the search (so k <= (log2 n) ^ 5 /2 + 1)
    l has value (log2 n)
    we work with polynomials with coef in Z_n and modulo X^k - 1 (so their
    degree is strictly less than k)
    and we check that a consequence of Fermat's little theorem, i.e
      (X + c) ^ n = X^n + c (modulo X^k - 1)
    holds for 1 <= c <= sqrt (totient k) * log2 n
    since (totient k) <= k, we are still polynomial in log2 n
  this is the key mathemical part of the algorithm, only checking this little 
  sample is enough to assert the primality
*)

let fpoly_intro_range n k l =
  let rec aux n k c r =
    if r = 0 then true else
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
  (* we can avoid using totient by replacing sqrt (totient k) * l with k *)

(* Main algo *)

(* we check if n is power_free, find the parameter k and check
   if the polynomial equalities hold *)
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

