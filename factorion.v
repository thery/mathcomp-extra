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

Let v40585 := Eval vm_compute in 5 + 10 * 4058.

Definition sum_fact b (n : nat) := \sum_(i < ndigits b n) (digitn b n i) `!.

Lemma sum_factMD b n d :
  0 < n -> 1 < b -> d < b -> sum_fact b (b * n + d) = d `! + sum_fact b n.
Proof.
move=> n_pos b_gt1 d_digit.
rewrite /sum_fact ndigitsMD // big_ord_recl; congr (_ + _).
  by rewrite digitn0 mulnC modnMDl modn_small.
apply: eq_bigr => /= i _.
by rewrite digitn_mulD // ltnW.
Qed.

Lemma sum_factM b n :
  0 < n -> 1 < b -> sum_fact b (b * n) = (sum_fact b n).+1.
Proof. by move=> ? ?; rewrite -[b * n]addn0 sum_factMD // ltnW. Qed.

Definition factorion (n : nat) := sum_fact 10 n == n.

Lemma factorion0 : ~ factorion 0.
Proof. by rewrite /factorion /sum_fact !big_ord_recr /= big_ord0. Qed.

Lemma factorion1 : factorion 1.
Proof. by rewrite /factorion /sum_fact !big_ord_recr /= big_ord0. Qed.

Lemma factorion2 : factorion 2.
Proof. by rewrite /factorion /sum_fact !big_ord_recr /= big_ord0. Qed.

Lemma factorion145 : factorion 145.
Proof. 
by rewrite /factorion /sum_fact -[ndigits 10 145]/3 !big_ord_recr big_ord0. 
Qed.

Lemma factorion40585 : factorion v40585.
Proof. 
by rewrite /factorion /sum_fact -[ndigits 10 v40585]/5 !big_ord_recr big_ord0.
Qed.

Lemma sum_fact_bound b n : 1 < b -> sum_fact b n <= ndigits b n * b.-1 `!.
Proof.
move=> b_pos; rewrite /sum_fact.
rewrite -[X in _ <= X * _]subn0 -[X in _ <= X]sum_nat_const_nat big_mkord.
elim: ndigits => [|k IH]; first by rewrite !big_ord0.
rewrite !big_ord_recr /= leq_add //.
case: (b) b_pos => // [] [|b1] // _.
case: digitn (ltn_pdigit n k (isT : 0 < b1.+2))=> [_ |d dLb] //.
  by rewrite -[0 `!]/(1 `!) leq_pfact.
by rewrite leq_pfact.
Qed.

Lemma sum_fact10_increasing n : 7 < ndigits 10 n -> sum_fact 10 n < n.
Proof.
move=> nL7.
have n_pos : 0 < n by case: n nL7.
apply : leq_ltn_trans (sum_fact_bound _ _) _ => //.
apply: leq_trans (ndigits_leq (isT : 1 < 10) n_pos).
set u := ndigits _ _ in nL7 |- *.
have u_pos : 0 < u  by case: u nL7.
have -> : 10 ^ u.-1 = 10^(u - 7) * 10^6.
  rewrite mulnC -expnD; congr (_ ^ _).
  rewrite -[u in RHS](prednK u_pos) subSS addnC subnK //.
  by case: (u) nL7 => // [] [|[|[|[|[|[|]]]]]].
apply: leq_trans (_ : u * 10 ^ 6 <= _); first by rewrite ltn_mul2l u_pos.
rewrite leq_pmul2r // -subSS subSn // -[X in X <= _](subnK nL7).
by elim: (_ - _) => // k IH; rewrite (leq_ltn_trans IH _) // ltn_exp2l.
Qed.

Lemma factorion_upperbound n : factorion n -> ndigits 10 n <= 7.
Proof.
by move=> Hf; case: leqP => // /sum_fact10_increasing; rewrite (eqP Hf) ltnn.
Qed.

Fixpoint fact_look_up1 (r : rel N) (k : nat) (n p : N) (l : seq N) : seq N := 
  if k is k1.+1 then
    let n1 := (10 * n)%num in 
    let l1 := fact_look_up1 r k1 n1 (1 + p)%num l in
    let l2 := fact_look_up1 r k1 (1 + n1)%num (1 + p)%num l1 in
    let l3 := fact_look_up1 r k1 (2 + n1)%num (2 + p)%num l2 in
    let l4 := fact_look_up1 r k1 (3 + n1)%num (6 + p)%num l3 in
    let l5 := fact_look_up1 r k1 (4 + n1)%num (24 + p)%num l4 in
    let l6 := fact_look_up1 r k1 (5 + n1)%num (120 + p)%num l5 in
    let l7 := fact_look_up1 r k1 (6 + n1)%num (720 + p)%num l6 in
    let l8 := fact_look_up1 r k1 (7 + n1)%num (5040 + p)%num l7 in
    let l9 := fact_look_up1 r k1 (8 + n1)%num (40320 + p)%num l8 in
    fact_look_up1 r k1 (9 + n1)%num (362880 + p)%num l9 
  else if (r n p)%num then n :: l else l.

Lemma fact_look_up1S r k n p l :
  fact_look_up1 r k.+1 n p l =
    let n1 := (10 * n)%num in 
    let l1 := fact_look_up1 r k n1 (1 + p)%num l in
    let l2 := fact_look_up1 r k (1 + n1)%num (1 + p)%num l1 in
    let l3 := fact_look_up1 r k (2 + n1)%num (2 + p)%num l2 in
    let l4 := fact_look_up1 r k (3 + n1)%num (6 + p)%num l3 in
    let l5 := fact_look_up1 r k (4 + n1)%num (24 + p)%num l4 in
    let l6 := fact_look_up1 r k (5 + n1)%num (120 + p)%num l5 in
    let l7 := fact_look_up1 r k (6 + n1)%num (720 + p)%num l6 in
    let l8 := fact_look_up1 r k (7 + n1)%num (5040 + p)%num l7 in
    let l9 := fact_look_up1 r k (8 + n1)%num (40320 + p)%num l8 in
    fact_look_up1 r k (9 + n1)%num (362880 + p)%num l9.
Proof. by []. Qed.

Lemma mem_fact_look_up1 r k n p (l : seq N) :
   {subset l <= (fact_look_up1 r k n p l)}.
Proof.
elim: k n p l => [n p l | k IH n p l] i iIl.
  by rewrite /=; case: r; rewrite ?in_cons // iIl orbT.
by do 10 apply: (IH).
Qed.

Lemma fact_look_up1_spec (r : rel N) k n p m l : 
 let n1 := N.to_nat n in 
 let p1 := N.to_nat p in 
  0 < n1 -> m %/ 10 ^ k = n1 -> p1 = sum_fact 10 n1 -> 
  r (N.of_nat m) (N.of_nat (sum_fact 10 m)) -> 
  N.of_nat m \in fact_look_up1 r k n p l.
Proof.
elim: k n p m l => [n p m l| k IH n p m l] n1 p1 n1_pos mE p1E mF.
  rewrite divn1 in mE.
  rewrite /fact_look_up1 mE N2Nat.id.
  rewrite -mE in p1E.
  rewrite -p1E mE !N2Nat.id in mF.
  by rewrite mF inE eqxx.
pose d1 := digitn 10 m k.
rewrite fact_look_up1S.
have : m = (m %/ 10 ^ k.+1 * 10 + d1) * 10 ^ k + m %% 10 ^ k.
  rewrite [LHS](divn_eq _ (10 ^ k)); congr (_ * _ + _).
  rewrite [LHS](divn_eq _ 10);  congr (_ * _ + _).
  by rewrite expnS mulnC divnMA.
case E : d1 => [|d].
  move=> mE1.
  do 9 apply: mem_fact_look_up1.
  have nE : N.to_nat (10 * n) = 10 * n1 by rewrite N2Nat.inj_mul.
  apply: IH => //; first by rewrite nE muln_gt0.
    rewrite nE mE1 addn0 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factM // -p1E N2Nat.inj_add.
case: d E => [d1E|].
  move=> mE1.
  do 8 apply: mem_fact_look_up1.
  have nE : N.to_nat (1 + 10 * n) = 10 * n1 + 1.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE addn1.
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d2E|].
  move=> mE1.
  do 7 apply: mem_fact_look_up1.
  have nE : N.to_nat (2 + 10 * n) = 10 * n1 + 2.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d3E|].
  move=> mE1.
  do 6 apply: mem_fact_look_up1.
  have nE : N.to_nat (3 + 10 * n) = 10 * n1 + 3.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d4E|].
  move=> mE1.
  do 5 apply: mem_fact_look_up1.
  have nE : N.to_nat (4 + 10 * n) = 10 * n1 + 4.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d5E|].
  move=> mE1.
  do 4 apply: mem_fact_look_up1.
  have nE : N.to_nat (5 + 10 * n) = 10 * n1 + 5.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d6E|].
  move=> mE1.
  do 3 apply: mem_fact_look_up1.
  have nE : N.to_nat (6 + 10 * n) = 10 * n1 + 6.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d7E|].
  move=> mE1.
  do 2 apply: mem_fact_look_up1.
  have nE : N.to_nat (7 + 10 * n) = 10 * n1 + 7.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d8E|].
  move=> mE1.
  apply: mem_fact_look_up1.
  have nE : N.to_nat (8 + 10 * n) = 10 * n1 + 8.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
case=> [d9E|].
  move=> mE1.
  have nE : N.to_nat (9 + 10 * n) = 10 * n1 + 9.
    by  rewrite N2Nat.inj_add N2Nat.inj_mul addnC.
  apply: IH => //; first by rewrite nE (leq_trans _ (leq_addl _ _)).
    rewrite nE mE1 divnMDl ?expn_gt0 //.
    rewrite mE divn_small; last by rewrite ltn_mod expn_gt0.
    by rewrite addn0 mulnC.
  by rewrite nE sum_factMD // -p1E N2Nat.inj_add.
move=> d d1E.
suff : d1 < 10 by rewrite d1E.
by apply: ltn_pdigit.
Qed.

Definition fact_look_up r k : seq N := 
  let l1 := fact_look_up1 r k 1%num 1%num [::] in  
  let l2 := fact_look_up1 r k 2%num 2%num l1 in  
  let l3 := fact_look_up1 r k 3%num 6%num l2 in  
  let l4 := fact_look_up1 r k 4%num 24%num l3 in  
  let l5 := fact_look_up1 r k 5%num 120%num l4 in  
  let l6 := fact_look_up1 r k 6%num 720%num l5 in  
  let l7 := fact_look_up1 r k 7%num 5040%num l6 in 
  let l8 := fact_look_up1 r k 8%num 40320%num l7 in  
  fact_look_up1 r k 9%num 362880%num l8.

Lemma fact_look_up_spec (r : rel N) m :
  0 < m ->
  r (N.of_nat m) (N.of_nat (sum_fact 10 m)) -> 
  N.of_nat m \in fact_look_up r (ndigits 10 m).-1.
Proof.
move=> m_pos mF.
pose d1 := digitn 10 m (ndigits 10 m).-1.
rewrite /fact_look_up.
have : m %/ 10 ^ (ndigits 10 m).-1 = d1.
  rewrite /d1 /digitn modn_small //.
  rewrite ltn_divLR ?expn_gt0 //.
  by rewrite -expnS prednK ?ndigits_gt0 // ndigitsP.
case E : d1 => [|d].
  move=> mE.
  have := ndigits_leq (isT : 1 < 10) m_pos.
  rewrite leqNgt => /negP[].
  rewrite {1}(divn_eq m (10 ^ (ndigits 10 m).-1)) mE add0n.
  by rewrite ltn_mod expn_gt0. 
case: d E => [d1E mE|].
  do 8 apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d2E mE|].
  do 7 apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d3E mE|].
  do 6 apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d4E mE|].
  do 5 apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d5E mE|].
  do 4 apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d6E mE|].
  do 3 apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d7E mE|].
  do 2 apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d8E mE|].
  apply: mem_fact_look_up1.
  apply: fact_look_up1_spec => //.
  by rewrite /sum_fact -[ndigits _ _]/1 big_ord_recr big_ord0.
case => [d9E mE|].
  apply: fact_look_up1_spec => //.
  rewrite /sum_fact.
  have -> : N.to_nat (362880) = N.to_nat (9 * (8 * (7 * (720)))).
    by congr N.to_nat.
  rewrite [N.to_nat (9 * _)]N2Nat.inj_mul.
  rewrite [N.to_nat (8 * _)]N2Nat.inj_mul.
  rewrite -[ndigits _ _]/1 big_ord_recr big_ord0.
  rewrite [digitn _ _ _]/= [RHS]add0n 2!factS.
  by congr (_ * (_ * _)%coq_nat)%coq_nat.
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
move=> mF; apply/or4P.
rewrite -[m]Nat2N.id.
suff : N.of_nat m \in [:: 1; 2; 145; 40585]%num.
  rewrite !inE => /or4P[] /eqP->.
  - by apply: Or41.
  - by apply: Or42.
  - by apply: Or43.
  apply: Or44.
  have -> : (40585 = 5 + 10 * 4058)%num by [].
  by rewrite N2Nat.inj_add N2Nat.inj_mul.
have := factorion_upperbound mF.
have := ndigits_gt0 m (isT : 1 < 10).
pose get_factorion d := fact_look_up [rel m n | (m =? n)%num] d.
have : N.of_nat m \in get_factorion (ndigits 10 m).-1.
  apply: fact_look_up_spec => /=.
    by case: (m) mF factorion0 => // [].
  by rewrite (eqP mF); case: N.eqb_spec.
case: ndigits => //.
case.
  have -> : get_factorion 1.-1 = [::2; 1]%num.
    by vm_cast_no_check (refl_equal [::2; 1]%num).
  by rewrite !inE; case/orP => /eqP->; rewrite eqxx.
case.
  have -> : get_factorion 2.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq N)).
  by rewrite !in_nil.
case.
  have -> : get_factorion 3.-1 = [::145]%num.
    by vm_cast_no_check (refl_equal [::145]%num).
  by rewrite !inE=> /eqP->; rewrite eqxx.
case.
  have -> : get_factorion 4.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq N)).
  by rewrite !in_nil.
case.
  have -> : get_factorion 5.-1 = [::40585]%num.
    by vm_cast_no_check (refl_equal [::40585]%num).
  by rewrite !inE=> /eqP->; rewrite eqxx.
case.
  have -> : get_factorion 6.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq N)).
  by rewrite !in_nil.
case.
  have -> : get_factorion 7.-1 = [::].
    by vm_cast_no_check (refl_equal ([::] : seq N)).
  by rewrite !in_nil.
by [].
Time Qed.

End Factorion.

Check factorionE.