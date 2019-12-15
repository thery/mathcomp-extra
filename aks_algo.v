From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*  This is a direct transcription of  AKS algorithm as given for HOL4        *)
(*  by Hing Lun Chan in his PhD thesis                                        *) 
(*                                                                            *)
(******************************************************************************)

(******************************************************************************)
(*     Base 2 logarithm                                                       *)
(******************************************************************************)

Definition log2n n := 
  let v := trunc_log 2 n in if n <= 2 ^ v then v else v.+1.

(******************************************************************************)
(*  Fancy nth root algorithm due to Yves Bertot, we could move to a           *)
(*  more naïve implementation without changing the complexity                 *)
(******************************************************************************)

Fixpoint seq_pol_add (s1 s2 : seq nat) :=
  if s1 is a :: s3 then
  if s2 is b :: s4 then a + b :: seq_pol_add s3 s4
  else s1 else s2.
 
Fixpoint seq_pol_mul (s1 s2 : seq nat) :=
  if s1 is a :: s3 then 
     seq_pol_add [seq a * i | i <- s2] (seq_pol_mul s3 (0 :: s2))
  else [::].

Fixpoint seq_pol_exp (s : seq nat) n := iter n (seq_pol_mul s) [:: 1].

Definition seq_2Xp1_exp_n (n : nat) := seq_pol_exp [:: 1; 2] n.

Fixpoint seq_pol_eval (s : seq nat) (x : nat) :=
  if s is a :: s1 then a + x * seq_pol_eval s1 x else 0.

Fixpoint pre_rootn l n (fuel i : nat) :=
  if fuel is fuel1.+1 then
    if i == 0 then 
      (0, 0)
    else
      let i' := i %/ n in
      let k' := i %% n in
      let (r, k2) := pre_rootn l n fuel1 i' in
        let remainder := seq_pol_eval l r in
        if remainder <=  n * k2 + k' then
           (r.*2.+1, n * k2 + k'- remainder)
        else
           (r.*2, n * k2 + k')
  else (0, 0).

Definition rootn (n i : nat) := 
  (pre_rootn ((take n (seq_2Xp1_exp_n n))) (2 ^ n) i i).1.

Definition is_rootn (n i : nat) :=
  (pre_rootn ((take n (seq_2Xp1_exp_n n))) (2 ^ n) i i).2  == 0.

Definition sqrtn := rootn 2.


(******************************************************************************)
(*    Power Free                                                              *)
(******************************************************************************)

Fixpoint power_free (n : nat) k :=
  if k is k1.+1 then 
    if k1 is _.+1 then 
      if is_rootn k n then false
      else power_free n k1
    else (1 < n) 
  else (1 < n).

Compute (fun n => power_free n (log2n n)) 128.

(******************************************************************************)
(*    Order on an element n in Z_m                                            *)
(******************************************************************************)

Fixpoint order_modn_rec m n r i k :=
  let r1 := ((r * n) %% m)%nat in
  if r1 == 1%N then i else 
  if k is k1.+1 then order_modn_rec m n r1 i.+1 k1 else i%nat.

Definition order_modn m n := 
  if coprime n m && (1 < m) then order_modn_rec m n 1 1 m
  else 0%nat.

(******************************************************************************)
(*    aks_param search                                                        *)
(******************************************************************************)

Inductive aks_param_res := nice of nat | bad | good of nat.

Fixpoint aks_param_search n a k c := 
  if c is c1.+1 then
    if (k %| n)%nat then nice k
    else if (a <= k) && (a <= order_modn k n) then good k
    else aks_param_search n a k.+1 c1
  else bad.

Definition aks_param n l := 
  let a := l ^ 2 in
  let k := 2 in
  let c := (l * (a ^ 2))./2  in
  if l <= 1 then nice n else aks_param_search n a k c.


(******************************************************************************)
(*    Polynomial modulo X^k - 1 with coefficient in Z_n                       *)
(******************************************************************************)


(******************************************************************************)
(*    Polynomial modulo : constant                                            *)
(******************************************************************************)

Definition modnp_const (n k v : nat) := (v %% n)%N :: nseq k.-1 0%N.

(******************************************************************************)
(*    Polynomial modulo : X^n                                                 *)
(******************************************************************************)

Definition modnp_Xn (n k v : nat) := 
    nseq (v %% k) 0%N ++ (1%N :: nseq (k.-1 - (v %% k)) 0%N).

(******************************************************************************)
(*    Polynomial modulo : multiplication by X                                 *)
(******************************************************************************)

Definition modnp_mulX (n k : nat) (v : list nat) :=  belast (last 0%N v) v.
  

Compute (modnp_mulX 4 10 (modnp_Xn 4 10 9)).

(******************************************************************************)
(*    Polynomial modulo : addition                                            *)
(******************************************************************************)

Fixpoint modnp_add (n k : nat) (v1 v2 : seq nat) :=
  if k is k1.+1 then 
    ((head 0%N v1 + head 0%N v2) %% n)%N :: 
    modnp_add n k1 (behead v1) (behead v2)
  else [::].


Compute (modnp_add 4 10 (modnp_Xn 4 10 9) (modnp_Xn 4 10 1)).

(******************************************************************************)
(*    Polynomial modulo : multiplication by a constant                        *)
(******************************************************************************)

Fixpoint modnp_scale (n k a : nat) (v : seq nat) :=
  if k is k1.+1 then 
    ((a * head 0%N v) %% n)%N :: modnp_scale n k1 a (behead v)
  else [::].

(******************************************************************************)
(*    Polynomial modulo : multiplication                                      *)
(******************************************************************************)

Fixpoint modnp_mul (n k : nat) (v1 v2 : seq nat) :=
  if v2 is a :: v3 then
    modnp_add n k (modnp_scale n k a v1) (modnp_mulX n k (modnp_mul n k v1 v3))
  else modnp_const n k 0.


Compute (modnp_mul 4 10 (modnp_Xn 4 10 9) (modnp_Xn 4 10 1)).

(******************************************************************************)
(*    Polynomial modulo : exponentiation                                      *)
(******************************************************************************)

Import BinPos.

Fixpoint modnp_pow (n k : nat) (p : positive) (v : seq nat) :=
  if p is xO p1 then let r := modnp_pow n k p1 v in
                     modnp_mul n k r r
  else if p is xI p1 then let r := modnp_pow n k p1 v in
                          modnp_mul n k v (modnp_mul n k r r)
  else v.


Compute (modnp_pow 4 10 (Pos.of_nat 4) (modnp_Xn 4 10 1)).

(******************************************************************************)
(*    Polynomial modulo : equality test                                       *)
(******************************************************************************)

Fixpoint modnp_eq (n k : nat) (v1 v2 : seq nat) : bool :=
  if k is k1.+1 then 
    ((head O v1) == (head O v2) %[mod n]) && 
    modnp_eq n k1 (behead v1) (behead v2)
  else true.

Compute modnp_eq 4 10 (modnp_Xn 4 10 1) (modnp_Xn 4 10 11).

(******************************************************************************)
(*    introspection check                                                     *)
(******************************************************************************)

Fixpoint poly_intro_range_aux n pn k c r := 
  if r is r1.+1 then
    let cc := modnp_const n k c in
    let x := modnp_Xn n k 1 in
    let xcc := modnp_add n k x cc in
    let xve := modnp_pow n k pn xcc in
    let xn := modnp_Xn n k n in
    let xncc := modnp_add n k xn cc in
    if modnp_eq n k xve xncc then poly_intro_range_aux n pn k c.+1 r1
    else false
  else true.


Definition fpoly_intro_range n k l := 
  let r := (sqrtn (totient k) * l)%nat in
  poly_intro_range_aux n (Pos.of_nat n) k 1 r.


(******************************************************************************)
(*    Aks algorithmm                                                          *)
(******************************************************************************)

Definition aks n := 
  let l := log2n n in
  if power_free n l then
    let v := aks_param n l in
    if v is nice k then n == k else
    if v is good k then fpoly_intro_range n k l else false
  else false.

Compute filter aks (iota 2 50).

