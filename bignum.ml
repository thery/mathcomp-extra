(** Representation for bnat:
   - list of bits
   - lower bits are at the head of the list
   - leading bit must be B1 for a non-zero number
*)

type bit = B0 | B1

type bnat = bit list


(*****************************************************************************)
(** * Auxiliary functions *)

(** Smart constructor, ensuring normalization of [B0] to [] *)

let bcons b n = (* returns b+2*n *)
  match b, n with
  | B0, [] -> []
  | _ -> b::n

(** Auxiliary functions for addition and subtraction *)

let two_bits_repr n = (* requires n <= 3 *)
  (* returns (b0,b1) such that n=2*b1+b0 *)
  match n with
  | [] -> (B0,B0)
  | [B1] -> (B1,B0)
  | [b0;b1] -> (b0,b1)
  | _ -> assert false

(** Conversion of a bit to a (nonnegative) primitive integers *)

let bit_to_nat b =
  match b with
  | B0 -> 0
  | B1 -> 1

(** Conversion of a bnat to a (nonnegative) primitive integers *)

let rec bnat_to_nat n =
  match n with
  | [] -> 0
  | b::n' -> bit_to_nat b + 2 * (bnat_to_nat n')

(** Conversion of a bit to a bnat *)

let bit_to_bnat b =
  match b with
  | B0 -> []
  | B1 -> [B1]

(** Conversion of a bit its opposite bit *)

let bit_flip b = (* returns 1-b *)
  match b with
  | B0 -> B1
  | B1 -> B0


(*****************************************************************************)
(** * Constants and comparisons *)

(** Constants *)

let zero = []

let one = [B1]

let two = [B0;B1]

(** Comparison algorithm,
    returns -1, 0 or 1, according to sign(n1-n2).
    Complexity: O(min(log n1, log n2)) *)

let rec cmp n1 n2 =
  match n1, n2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | b1::n1', b2::n2' ->
      let c = cmp n1' n2' in
      if c <> 0 then c
      else if b1 = b2 then 0
      else if b1 = B0 then -1
      else 1

(** Basic comparisons *)

let (^=) n1 n2 =
  cmp n1 n2 = 0

let (^<=) n1 n2 =
  cmp n1 n2 <= 0

let (^<) n1 n2 =
  cmp n1 n2 < 0

(** Symmetric comparisons *)

let (^<>) n1 n2 =
  not (n1 ^= n2)

let (^>=) n1 n2 =
  n2 ^<= n1

let (^>) n1 n2 =
  n2 ^< n1


(*****************************************************************************)
(** * Addition and subtraction *)

(** Multiplication by 2
    Complexity: O(1) *)

let mul2 n =
  bcons B0 n

(** Successor
    Complexity: O(log n) *)

let rec succ n = (* returns n+1 *)
  match n with
  | [] -> [B1]
  | B0::n' -> B1::n'
  | B1::n' -> B0::(succ n')

(** Addition of a bit to a bnat *)

let add_bit b n = (* returns n+b *)
  if b = B0
    then n
    else succ n

(** Addition
    Complexity: O(max(log n1, log n2)) *)

let (^+) n1 n2 =
  let rec aux n1 n2 b = (* b is the carry bit *)
    match n1, n2 with
    | [], _ -> add_bit b n2
    | _, [] -> add_bit b n1
    | b1::n1', b2::n2' ->
        let r = add_bit b (add_bit b1 (bit_to_bnat b2)) in
        let (b3,b') = two_bits_repr r in
        b3 :: (aux n1' n2' b')
    in
  aux n1 n2 B0

(** Predecessor *)

let rec pred n = (* returns max(n-1,0) *)
  match n with
  | [] -> []
  | B1::[] -> []
  | B1::n' -> bcons B0 n'
  | B0::n' -> B1::(pred n')

(** Subtraction of a bit to a bnat *)

let sub_bit b n = (* returns n-b *)
  if b = B0
    then n
    else pred n

(* Subtraction
   Complexity: O(log n1) *)

let (^-) n1 n2 = (* requires n1 >= n2 *)
  let rec aux n1 n2 b = (* b is the carry bit *)
    match n1, n2 with
    | [], [] -> if b = B0 then [] else assert false
    | [], _ -> assert false
    | _, [] -> sub_bit b n1
    | b1::n1', b2::n2' ->
        (* b1-b2-b = b3-2b', thus 2+b1-b2-b = b3+2*(1-b') *)
        let r = sub_bit b (sub_bit b2 (add_bit b1 two)) in
        let (b3,bneg') = two_bits_repr r in
        let b' = bit_flip bneg' in
        bcons b3 (aux n1' n2' b')
    in
  aux n1 n2 B0


(*****************************************************************************)
(** * Multiplication and exponentiation *)

(** Multiplication (naive)
    Complexity: O(log n1 * log n2) *)

let rec (^*) n1 n2 =
  match n1 with
  | [] -> zero
  | b::n1' ->
     let r = mul2 (n1' ^* n2) in
     if b = B0 then r else r ^+ n2

(** Power (naive)
    Complexity: O(log n1 * n2 ^ 2)  (?) *)

let rec (^^) n1 n2 =
  if n2 ^= zero
    then one
    else n1 ^* n1 ^^ (n2 ^- one)


(*****************************************************************************)
(** * Division, modulo and co-primality *)

(** Even test
    Complexity O(1) *)

let even n =
  match n with
  | [] -> true
  | B0::n' -> true
  | _ -> false

(** Division by 2
    Complexity O(1) *)

let div2 n =
  match n with
  | [] -> []
  | b::n' -> n'

(** Modulo
    Complexity O(log n1 * log n2) *)

let rec (^%) n1 n2 = (* requires n2 > 0 *)
  match n1 with
  | [] -> zero
  | b::n1' ->
     let r = add_bit b (mul2 (n1' ^% n2)) in
     if n2 ^<= r then r ^- n2 else r

(** Coprime
    Complexity O(log n1 + log n2)^2) *)

let rec coprime n1 n2 =
   let c = cmp n1 n2 in
   if c < 0 then
      coprime n2 n1 (* swap to ensure n1 >= n2 in the code below *)
   else if n2 ^= zero then
      n1 ^= one (* zero is only coprime with one *)
   else if c = 0 then
      n1 ^= one (* a non-zero number is coprime with itself only if it is one *)
   else
      let simpl n = (* half a number if it is even *)
        if even n then div2 n else n in
      if even n1 || even n2
        then coprime (simpl n1) (simpl n2)
        else coprime (div2 (n1 ^- n2)) n2


(* alternative 1:

     match even n1, even n2 with
     | true, true  -> coprime (div2 n1) (div2 n2)
     | true, false -> coprime (div2 n1) n2
     | false, true -> coprime n1 (div2 n2)
     | false, false -> coprime (n1 ^- n2) n2
*)

(* alternative 2:

   if even n1 && even n2 then
      coprime (div2 n1) (div2 n2)
   else if even n1 then
      coprime (div2 n1) n2
   else if even n2 then
      coprime n1 (div2 n2)
   else
      coprime (n1 ^- n2) n2
*)