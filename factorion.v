From Stdlib Require Import String NArith.
From mathcomp Require Import all_ssreflect.
Require Import digitn.


(******************************************************************************)
(*                                                                            *)
(* factorion n   ==  n is equal to the sum of the factorial of its digits in  *)
(*                   base 10                                                  *)
(* This file shows that there is only 4 of these 1, 2, 145, 40585             *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Factorion.

Let v40585 := Eval vm_compute in 4058 * 10 + 5.
Let v5040 := Eval vm_compute in 504 * 10.
Let v40320 := Eval vm_compute in 4032 * 10.
Let v362880 := Eval vm_compute in 80 + 100 * 3628.

Definition factorion (n : nat) := 
  n == \sum_(i < ndigits 10 n) (digitn 10 n i) `!.

Lemma factorion0 : ~ factorion 0.
Proof. by rewrite /factorion !big_ord_recr /= big_ord0. Qed.

Lemma factorion1 : factorion 1.
Proof. by rewrite /factorion !big_ord_recr /= big_ord0. Qed.

Lemma factorion2 : factorion 2.
Proof. by rewrite /factorion !big_ord_recr /= big_ord0. Qed.

Lemma factorion145 : factorion 145.
Proof. by rewrite /factorion -[ndigits 10 145]/3 !big_ord_recr big_ord0. Qed.

Lemma factorion40585 : factorion v40585.
Proof. by rewrite /factorion -[ndigits 10 v40585]/5 !big_ord_recr big_ord0. Qed.

Lemma factorion_bound n : factorion n -> n <= ndigits 10 n * 9 `!.
Proof.
move/eqP => {1}->.
rewrite -{6}[ndigits _ _]subn0 -[X in _ <= X]sum_nat_const_nat big_mkord.
elim: ndigits => [|k IH]; first by rewrite !big_ord0.
rewrite !big_ord_recr /= leq_add //.
case: digitn (ltn_pdigit n k (isT : 0 < 10))=> // l Hl.
by rewrite leq_pfact.
Qed.

Lemma factorion_upperbound n : factorion n -> ndigits 10 n <= 8.
Proof.
case: n => // n nF.
have : 10 ^ (ndigits 10 n.+1).-1 <= ndigits 10 n.+1 * 9`!.
  by apply: leq_trans (ndigits_leq _ _) (factorion_bound nF).
case: ndigits => //=; do 7 case => //; move=> k.
rewrite leqNgt => /negP[].
have -> : 10 ^ k.+3.+4 = 10^k.+1 * 10^6 by rewrite mulnC -expnD; congr (_ ^ _).
apply: leq_trans (_ : k.+4.+4 * 10 ^ 6 <= _); first by rewrite ltn_mul2l.
rewrite leq_pmul2r //.
by elim: k => // k IH; rewrite (leq_ltn_trans IH _) // ltn_exp2l.
Qed.

Fixpoint get_factorion1 (k : nat) (n p : N) (l : seq nat) : seq nat := 
  if k is k1.+1 then
    let n1 := (10 * n)%num in 
    let l1 := get_factorion1 k1 n1 (1 + p)%num l in
    let l2 := get_factorion1 k1 (1 + n1)%num (1 + p)%num l1 in
    let l3 := get_factorion1 k1 (2 + n1)%num (2 + p)%num l2 in
    let l4 := get_factorion1 k1 (3 + n1)%num (6 + p)%num l3 in
    let l5 := get_factorion1 k1 (4 + n1)%num (24 + p)%num l4 in
    let l6 := get_factorion1 k1 (5 + n1)%num (120 + p)%num l5 in
    let l7 := get_factorion1 k1 (6 + n1)%num (720 + p)%num l6 in
    let l8 := get_factorion1 k1 (7 + n1)%num (5040 + p)%num l7 in
    let l9 := get_factorion1 k1 (8 + n1)%num (40320 + p)%num l8 in
    get_factorion1 k1 (9 + n1)%num (362880 + p)%num l9 
  else if (n =? p)%num then (N.to_nat n) :: l else l.

Lemma get_factorion1S k n p l :
  get_factorion1 k.+1 n p l =
    let n1 := (10 * n)%num in 
    let l1 := get_factorion1 k n1 (1 + p)%num l in
    let l2 := get_factorion1 k (1 + n1)%num (1 + p)%num l1 in
    let l3 := get_factorion1 k (2 + n1)%num (2 + p)%num l2 in
    let l4 := get_factorion1 k (3 + n1)%num (6 + p)%num l3 in
    let l5 := get_factorion1 k (4 + n1)%num (24 + p)%num l4 in
    let l6 := get_factorion1 k (5 + n1)%num (120 + p)%num l5 in
    let l7 := get_factorion1 k (6 + n1)%num (720 + p)%num l6 in
    let l8 := get_factorion1 k (7 + n1)%num (5040 + p)%num l7 in
    let l9 := get_factorion1 k (8 + n1)%num (40320 + p)%num l8 in
    get_factorion1 k (9 + n1)%num (362880 + p)%num l9.
Proof. by []. Qed.

Lemma mem_get_factorion1 k n p (l : seq nat) :
   {subset l <= (get_factorion1 k n p l)}.
Proof.
elim: k n p l => [n p l | k IH n p l] i iIl.
  by rewrite /=; case: N.eqb; rewrite ?in_cons // iIl orbT.
by do 10 apply: (IH).
Qed.

Lemma get_factorion1_spec k n p m l : 
 let n1 := N.to_nat n in 
 let p1 := N.to_nat p in 
  0 < n1 ->
  m %/ 10 ^ k = n1 ->
  p1 = \sum_(i < ndigits 10 n1) (digitn 10 n1 i) `! -> 
  factorion m -> m \in get_factorion1 k n p l.
Proof.
elim: k n p m l => [n p m l| k IH n p m l] n1 p1 n1_pos mE p1E mF.
have mF1 := (eqP mF).
  rewrite divn1 in mE.
  rewrite -mE -mF1 mE in p1E.
  by rewrite (N2Nat.inj _ _ p1E) /= mE N.eqb_refl in_cons eqxx.
pose d1 := digitn 10 m k.
rewrite get_factorion1S.
have : m = (m %/ 10 ^ k.+1 * 10 + d1) * 10 ^ k + m %% 10 ^ k.
  rewrite [LHS](divn_eq _ (10 ^ k)); congr (_ * _ + _).
  rewrite [LHS](divn_eq _ 10);  congr (_ * _ + _).
  by rewrite expnS mulnC divnMA.
case E : d1 => [|d].
  move=> mE1.
  do 9 apply: mem_get_factorion1.
  have nE : N.to_nat (10 * n) = 10 * n1 by rewrite N2Nat.inj_mul.
  apply: IH => //; first by rewrite nE muln_gt0.
    rewrite nE mE1 addn0 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mul //.
  have -> : N.to_nat (1 + p) = p1.+1 by rewrite N2Nat.inj_add.
  rewrite p1E -add1n big_ord_recl; congr (_ + _).
    by rewrite digitn0 modnMr.
  apply: eq_bigr => /= i _.
  by rewrite -[10 * n1]addn0 digitn_mulD //.
case: d E => [d1E|].
  move=> mE1.
  do 8 apply: mem_get_factorion1.
  have nE : N.to_nat (1 + 10 * n) = 10 * n1 + 1.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE addn1.
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (1 + p) = p1.+1 by rewrite N2Nat.inj_add.
  rewrite p1E -add1n big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d2E|].
  move=> mE1.
  do 7 apply: mem_get_factorion1.
  have nE : N.to_nat (2 + 10 * n) = 10 * n1 + 2.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (2 + p) = 2 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d3E|].
  move=> mE1.
  do 6 apply: mem_get_factorion1.
  have nE : N.to_nat (3 + 10 * n) = 10 * n1 + 3.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (6 + p) = 6 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d4E|].
  move=> mE1.
  do 5 apply: mem_get_factorion1.
  have nE : N.to_nat (4 + 10 * n) = 10 * n1 + 4.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (24 + p) = 24 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d5E|].
  move=> mE1.
  do 4 apply: mem_get_factorion1.
  have nE : N.to_nat (5 + 10 * n) = 10 * n1 + 5.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (120 + p) = 120 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d6E|].
  move=> mE1.
  do 3 apply: mem_get_factorion1.
  have nE : N.to_nat (6 + 10 * n) = 10 * n1 + 6.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (720 + p) = 720 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d7E|].
  move=> mE1.
  do 2 apply: mem_get_factorion1.
  have nE : N.to_nat (7 + 10 * n) = 10 * n1 + 7.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (5040 + p) = v5040 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d8E|].
  move=> mE1.
  apply: mem_get_factorion1.
  have nE : N.to_nat (8 + 10 * n) = 10 * n1 + 8.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (40320 + p) = v40320 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
case=> [d9E|].
  move=> mE1.
  have nE : N.to_nat (9 + 10 * n) = 10 * n1 + 9.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  rewrite nE ndigits_mulD //.
  have -> : N.to_nat (362880 + p) = v362880 + p1 by rewrite N2Nat.inj_add.
  rewrite p1E big_ord_recl; congr (_ + _).
    by rewrite digitn0 mulnC modnMDl modn_small.
  apply: eq_bigr => /= i _.
  by rewrite digitn_mulD //.
move=> d d1E.
suff : d1 < 10 by rewrite d1E.
by apply: ltn_pdigit.
Qed.

Definition get_factorion k : seq nat := 
  let l1 := get_factorion1 k 1%num 1%num [::] in  
  let l2 := get_factorion1 k 2%num 2%num l1 in  
  let l3 := get_factorion1 k 3%num 6%num l2 in  
  let l4 := get_factorion1 k 4%num 24%num l3 in  
  let l5 := get_factorion1 k 5%num 120%num l4 in  
  let l6 := get_factorion1 k 6%num 720%num l5 in  
  let l7 := get_factorion1 k 7%num 5040%num l6 in 
  let l8 := get_factorion1 k 8%num 40320%num l7 in  
  get_factorion1 k 9%num 362880%num l8.

Lemma get_factorion_spec m :
  factorion m -> m \in get_factorion (ndigits 10 m).-1.
Proof.
move=> mF.
pose d1 := digitn 10 m (ndigits 10 m).-1.
rewrite /get_factorion.
have : m %/ 10 ^ (ndigits 10 m).-1 = d1.
  rewrite /d1 /digitn modn_small //.
  rewrite ltn_divLR ?expn_gt0 //.
  by rewrite -expnS prednK ?ndigits_gt0 // ndigitsP.
case E : d1 => [|d].
  move=> mE.
  case Em : (m) => [|m1]; first by case: factorion0; rewrite -Em.
  have m_pos : 0 < m by rewrite Em.
  have := ndigits_leq (isT : 1 < 10) m_pos.
  rewrite leqNgt => /negP[].
  rewrite {1}(divn_eq m (10 ^ (ndigits 10 m).-1)) mE add0n.
  by rewrite ltn_mod expn_gt0. 
case: d E => [d1E mE|].
  do 8 apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d2E mE|].
  do 7 apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d3E mE|].
  do 6 apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d4E mE|].
  do 5 apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d5E mE|].
  do 4 apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d6E mE|].
  do 3 apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d7E mE|].
  do 2 apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d8E mE|].
  apply: mem_get_factorion1.
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d9E mE|].
  apply: get_factorion1_spec => //.
  by rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
move=> d d1E.
suff : d1 < 10 by rewrite d1E.
by apply: ltn_pdigit.
Qed.

Lemma factorionE m : factorion m = (m \in [::1; 2; 145; v40585]).
Proof.
apply/idP/idP; last first.
  rewrite !inE; case/or4P => /eqP->.
  - by exact: factorion1.
  - by exact: factorion2.
  - by exact: factorion145.
  by exact: factorion40585.
move=> mF.
have := factorion_upperbound mF.
have := ndigits_gt0 m (isT : 1 < 10).
have := get_factorion_spec mF.
case: ndigits => //.
case.
  have -> : get_factorion 1.-1 = [::2; 1].
    by vm_cast_no_check (refl_equal [::2; 1]).
  by rewrite !inE; case/orP => /eqP->; rewrite eqxx.
case.
  have -> : get_factorion 2.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq nat)).
  by rewrite !in_nil.
case.
  have -> : get_factorion 3.-1 = [::145].
    by vm_cast_no_check (refl_equal [::145]).
  by rewrite !inE=> /eqP->; rewrite eqxx.
case.
  have -> : get_factorion 4.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq nat)).
  by rewrite !in_nil.
case.
  have -> : get_factorion 5.-1 = [::v40585].
    by vm_cast_no_check (refl_equal [::v40585]).
  by rewrite !inE=> /eqP->; rewrite eqxx.
case.
  have -> : get_factorion 6.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq nat)).
  by rewrite !in_nil.
case.
  have -> : get_factorion 7.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq nat)).
  by rewrite !in_nil.
case.
  have -> : get_factorion 8.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq nat)).
  by rewrite !in_nil.
by [].
Time Qed.

End Factorion.

Check factorionE.