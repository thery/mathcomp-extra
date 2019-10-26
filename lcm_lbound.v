(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*       'L(n,m) <=>                                                          *)
(*             the entry at row n, colum m of Leibniz’s Denominator Triangle. *)
(*       primes m == the sorted list of prime divisors of m > 1, else [::].   *)
(*      \lcm_ ( i < n ) F i  <=> the lcm of all the F i                       *)
(*                                                                            *)
(* It proves a lower bound for \lcm_ ( i < n ) i                              *)
(* following [Chan and Norrish]                                               *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Definition leibnizn m n := m.+1 *  'C(m, n).

Notation "''L' ( n , m )" := (leibnizn n m)
  (at level 8, format "''L' ( n ,  m )") : nat_scope.

Lemma leibn0 n : 'L(n, 0) = n.+1.
Proof. by rewrite /leibnizn bin0 muln1. Qed.

Lemma leibnn n : 'L(n, n) = n.+1.
Proof. by rewrite /leibnizn binn muln1. Qed.

Lemma leibn_small m n : m < n -> 'L(m, n) = 0.
Proof. by move=> Hmn; rewrite /leibnizn bin_small ?muln0. Qed.

Lemma leibn_sub m n :  n <= m -> 'L(m, m - n) = 'L(m, n).
Proof. by move=> Lnm; rewrite /leibnizn bin_sub. Qed.

Lemma leibn_gt0 m n : n <= m -> 0 < 'L(m, n).
Proof. by move=> Lnm; rewrite /leibnizn muln_gt0 bin_gt0. Qed.

Lemma bin_up1 m n : m.+1 * 'C(m, n) = (m.+1 - n) * 'C(m.+1, n).
Proof. by have := mul_bin_down m.+1 n. Qed. 

Lemma leibn_up m n : m.+2 * 'L(m, n) = (m.+1 - n) * 'L(m.+1, n).
Proof. by rewrite /leibnizn mul_bin_down mulnCA. Qed.

Lemma leibn_right m n : n.+1 * 'L(m.+1, n.+1) = (m.+1 - n) * 'L(m.+1, n).
Proof. by rewrite /leibnizn mulnCA mul_bin_left mulnCA. Qed.

Lemma leibnS m n : 
  'L(m.+1, n.+1) * 'L(m.+1, n) = 'L(m, n) * ('L(m.+1, n.+1) + 'L(m.+1, n)).
Proof.
case: (leqP n m.+1) => H; last first.
  by rewrite leibn_small 1?ltnW // leibn_small // !muln0.
apply/eqP.
have /eqn_pmul2l<- : m.+2 * n.+1 > 0 by [].
apply/eqP.
rewrite -[_.+2 * _ * _]mulnA [n.+1 * _]mulnA.
rewrite [in RHS]mulnCA -[_.+2 * _ * _ in RHS]mulnA.
rewrite mulnDr leibn_right.
rewrite mulnDr [m.+2 * (_.+1 * _) in RHS] mulnCA.
rewrite -{1}leibn_up [in RHS]mulnC mulnDl.
rewrite -mulnA ['L(_,_) * _]mulnC 2!mulnA.
rewrite -mulnDl; congr (_ * _).
rewrite [X in _ = X + _]mulnA [X in _ = _ + X]mulnA.
rewrite -mulnDl; congr (_ * _).
by rewrite [_ * _.+2 in RHS]mulnC -mulnDr addnS subnK.
Qed.

Lemma lcmn_swap a b c :
    a * c = b * (a + c) -> lcmn b c = lcmn a c.
Proof.
case: a => [|a].
  by move/eqP; rewrite add0n eq_sym muln_eq0=> /orP[] /eqP->; rewrite !(lcm0n,lcmn0).
case: b => [|b].
  by move/eqP; rewrite muln_eq0=> /orP[] /eqP->; rewrite !(lcm0n,lcmn0).
case: c => [|c H].
  by move/eqP; rewrite addn0 eq_sym muln0 muln_eq0=> /orP[] /eqP->; 
     rewrite !(lcm0n,lcmn0).
apply/eqP.
have /eqn_pmul2r<- : a.+1 * gcdn b.+1 c.+1 > 0 by rewrite muln_gt0 gcdn_gt0.
  rewrite {2}muln_gcdr H [b.+1 * _]mulnC mulnDl gcdnDl.
  by rewrite mulnCA muln_lcm_gcd -muln_gcdl !mulnA muln_lcm_gcd [X in _ == X]mulnAC.
Qed.

Lemma leibn_lcm_swap m n :
   lcmn 'L(m.+1, n) 'L(m, n) = lcmn 'L(m.+1, n) 'L(m.+1, n.+1).
Proof.
rewrite ![lcmn 'L(m.+1, n) _]lcmnC.
by apply/lcmn_swap/leibnS.
Qed.

Notation "\lcm_ ( i < n ) F" :=
 (\big[lcmn/1%N]_(i < n ) F%N) 
  (at level 41, F at level 41, i, n at level 50,
           format "'[' \lcm_ ( i  <  n  ) '/  '  F ']'") : nat_scope.

Lemma leib_line n i k : lcmn 'L(n.+1, i) (\lcm_(j < k) 'L(n, i + j)) = 
                   \lcm_(j < k.+1) 'L(n.+1, i + j).
Proof.
elim: k i => [i|k1 IH i].
  by rewrite big_ord_recr !big_ord0 /= lcmn1 lcm1n addn0.
rewrite big_ord_recl /= addn0.
rewrite lcmnA leibn_lcm_swap.
rewrite (eq_bigr (fun j : 'I_k1 => 'L(n, i.+1 + j))).
rewrite -lcmnA.
rewrite IH.
rewrite [RHS]big_ord_recl.
rewrite addn0; congr (lcmn _ _).
by apply: eq_bigr => j _; rewrite addnS.
move=> j _.
by rewrite addnS.
Qed.

Lemma leib_corner n : \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) 'L(n, i).
Proof.
elim: n => [|n IH]; first by rewrite !big_ord_recr !big_ord0 /=.
rewrite big_ord_recr /= IH lcmnC.
rewrite (eq_bigr (fun i : 'I_n.+1 => 'L(n, 0 + i))) //.
by rewrite leib_line.
Qed.

Lemma main_result n : 2^n.-1 <= \lcm_(i < n) i.+1.
Proof.
case: n => [|n /=]; first by rewrite big_ord0.
have <-: \lcm_(i < n.+1) 'L(i, 0) = \lcm_(i < n.+1) i.+1.
  by apply: eq_bigr => i _; rewrite leibn0.
rewrite leib_corner.
have -> : forall j,  \lcm_(i < j.+1) 'L(n, i) = n.+1 *  \lcm_(i < j.+1) 'C(n, i).
  elim=> [|j IH]; first by rewrite !big_ord_recr !big_ord0 /= !lcm1n.
  by rewrite big_ord_recr [in RHS]big_ord_recr /= IH muln_lcmr.
rewrite (expnDn 1 1) /=  (eq_bigr (fun i : 'I_n.+1 => 'C(n, i))) => 
       [|i _]; last by rewrite !exp1n !muln1.
have <- : forall n m,  \sum_(i < n) m = n * m.
  by move=> m1 n1; rewrite sum_nat_const card_ord.
apply: leq_sum => i _.
apply: dvdn_leq; last by rewrite (bigD1 i) //= dvdn_lcml.
apply big_ind => // [x y Hx Hy|x H]; first by rewrite lcmn_gt0 Hx.
by rewrite bin_gt0 -ltnS.
Qed.
