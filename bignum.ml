(** Representation for bnat:
   - list of bits
   - lower bits are at the head of the list
   - leading bit must be B1
*)

type bit = B0 | B1

type bnat = bit list

(** smart constructor **)

let bcons b l =
  match b, l with
  | B0, [] -> []
  | _ ->  b :: l

(** Conversion to (nonnegative) primitive integers *)

let bit_to_nat b =
  match b with
  | B0 -> 0
  | B1 -> 1

(** Comparisons *)

let rec cmp n1 n2 = (* returns -1, 0 or 1, according to sign(n1-n2) *)
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

let (^=) n1 n2 =
  cmp n1 n2 = 0

let (^<=) n1 n2 =
  cmp n1 n2 <= 0

let (^<) n1 n2 =
  cmp n1 n2 < 0

let rec bnat_to_nat n =
  match n with
  | [] -> 0
  | b::n' -> bit_to_nat b + 2 * (bnat_to_nat n')

(** Conversion of a bit to a bnat, or to its opposite bit *)

let bit_to_bnat b =
  match b with
  | B0 -> []
  | B1 -> [B1]

let bit_flip b =
  match b with
  | B0 -> B1
  | B1 -> B0

(** Constants *)

let zero = []

let one = [B1]

let two = [B0;B1]

(** Derived comparisons *)

let (^<>) n1 n2 =
  not (n1 ^= n2)

let (^>=) n1 n2 =
  n2 ^<= n1

let (^>) n1 n2 =
  n2 ^< n1

(** Even, multiplication and division by 2*)

let even n =
  match n with
  | [] -> true
  | B0::n' -> true
  | _ -> false

let mul2 n =
  bcons B0 n

let div2 n =
  match n with
  | [] -> []
  | b::n' -> n'

(** Successor, addition *)

let rec succ n =
  match n with
  | [] -> [B1]
  | B0::n' -> B1::n'
  | B1::n' -> B0::(succ n')

let add_bit b n =
  if b = B0
    then n
    else succ n

let two_bits_repr n = (* assumes n <= 3 *)
  match n with
  | [] -> (B0,B0)
  | [B1] -> (B1,B0)
  | [b0;b1] -> (b0,b1)
  | _ -> assert false

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

(** Predecessor, subtraction *)

let rec pred n =
  match n with
  | [] -> [] (* negative goes to zero *)
  | B1::[] -> [] (* 1-1 is zero *)
  | B1::n' -> bcons B0 n'
  | B0::n' -> B1::(pred n')

let sub_bit b n =
  if b = B0
    then n
    else pred n

(* substraction WARNING only valid if n1 >= n2 *)
let (^-) n1 n2 =
  let rec aux n1 n2 b = (* b is the carry bit *)
    match n1, n2 with
    | [], _ -> [] (* negative goes to zero *)
    | _, [] -> sub_bit b n1
    | b1::n1', b2::n2' ->
        (* b1-b2-b = b3-2b', thus 2+b1-b2-b = b3+2*(1-b') *)
        let r = sub_bit b (sub_bit b2 (add_bit b1 two)) in
        let (b3,bneg') = two_bits_repr r in
        let b' = bit_flip bneg' in
        bcons b3 (aux n1' n2' b')
    in
  aux n1 n2 B0

(** Multiplication (naive) *)

let rec (^*) n1 n2 =
  match n1 with
  | [] -> zero
  | b::n1' ->
     let r = mul2 (n1' ^* n2) in
     if b = B0 then r else r ^+ n2

(** Power (naive) *)

let rec (^^) a n =
  if n ^= zero
    then one
    else a ^* a ^^ (n ^- one)

(** Coprime *)

let rec coprime n1 n2 =
   if n1 ^= zero then n2 ^= one else
   if n2 ^= zero then n1 ^= one else
   let c = cmp n1 n2 in
   if c = 0 then
      n1 ^= one
   else if even n1 && even n2 then
      coprime (div2 n1) (div2 n2)
   else if even n1 then
      coprime (div2 n1) n2
   else if even n2 then
      coprime n1 (div2 n2)
   else if c > 0 then
      coprime (n1 ^- n2) n2
   else
      coprime n1 (n2 ^- n1)

(** Modulo WARNING we assume n2 > 0*)

let rec (^%) n1 n2 =
  match n1 with
  | [] -> zero
  | b::n1' ->
     let r = add_bit b (mul2 (n1' ^% n2)) in
     if n2 ^<= r then r ^- n2 else r
