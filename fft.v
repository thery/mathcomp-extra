From mathcomp Require Import all_ssreflect all_algebra.

(******************************************************************************)
(*                                                                            *)
(*             Proof of the Fast Fourier Transform                            *)
(*              inspired by the paper of V. Capretta                          *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section FFT.

Local Open Scope ring_scope.


(* Arbitrary ring *)
Variable R : ringType.

Implicit Type p : {poly R}.

(* Even part of a polynomial *)
Definition even_poly p : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.

Lemma size_even_poly p : (size (even_poly p) <= uphalf (size p))%nat.
Proof. by apply: size_poly. Qed.

Lemma coef_even_poly p i : (even_poly p)`_ i = p `_ i.*2.
Proof.
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)).
move: L; rewrite uphalf_half.
case: odd; first by rewrite !add1n ltn_double.
by rewrite leq_double.
Qed.

(* Odd part of a polynomial *)
Definition odd_poly p : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.+1.

Lemma size_odd_poly p : (size (odd_poly p) <= uphalf (size p))%nat.
Proof. by apply: size_poly. Qed.

Lemma coef_odd_poly p i : (odd_poly p)`_ i = p `_ i.*2.+1.
Proof.
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)).
move: L; rewrite uphalf_half.
case: odd; first by rewrite !add1n ltnS leq_double => /ltnW.
by rewrite -leq_double => /leq_trans->.
Qed.

(* Auxillary lemmas for _ \Po X'X^n *)
Lemma comp_polyXn (p : {poly R}) n :
  (0 < n)%nat -> 
  p \Po 'X^n = \poly_(i < size p * n) (if (n %| i)%nat then p`_(i %/ n) else 0).
Proof.
move=> nP.
apply/polyP=> i.
rewrite coef_comp_poly coef_poly.
under [LHS] eq_bigr do rewrite -exprM coefXn.
have [/dvdnP[j ->]|NiDn] := boolP (n %| i)%nat; last first.
  rewrite if_same big1 // => j _; case: eqP; rewrite (mulr0, mulr1) // => iE.
  by case/negP: NiDn; rewrite iE dvdn_mulr.
rewrite mulnK //.
have [sLj|jLs] := leqP (size p) j.
  rewrite nth_default // if_same big1 // => l _.
  rewrite mulnC eqn_mul2l (negPf (lt0n_neq0 nP)) /=.
  case: eqP=> [jE|_]; rewrite (mulr0, mulr1) //.
  by have := ltn_ord l; rewrite -jE ltnNge sLj.
rewrite ifT; last by rewrite ltn_mul2r nP.
rewrite (bigD1 (Ordinal jLs)) //= mulnC eqxx mulr1.
rewrite big1 ?addr0 // => /= [] [l /= lLs] /eqP/val_eqP/= lDj.
by rewrite eqn_mul2l (negPf (lt0n_neq0 nP)) eq_sym (negPf lDj) mulr0.
Qed.

Lemma coef_comp_polyXn (p : {poly R}) n i :
  (0 < n)%nat -> (p \Po 'X^n)`_i = if (n %| i)%nat then p`_(i %/ n) else 0.
Proof.
move=> nP.
rewrite comp_polyXn // coef_poly; case: leqP => // sLi.
by rewrite nth_default ?if_same // leq_divRL.
Qed.

Lemma hornerMXn (p : {poly R}) n (x : R):
  (p * 'X^n).[x] = p.[x] * x ^+ n.
Proof.
elim/poly_ind: p n => [n|p c IH n]; first by rewrite !(mul0r, horner0).
rewrite mulrDl hornerD hornerCM hornerXn.
by rewrite -mulrA -exprS IH hornerMXaddC mulrDl -mulrA -exprS.
Qed.

Lemma horner_comp_polyXn (p : {poly R}) n (x : R):
  (p \Po 'X^n).[x] = p.[x ^+ n].
Proof.
elim/poly_ind: p => [|p c IH]; first by rewrite horner0 comp_poly0 horner0.
by rewrite comp_poly_MXaddC !hornerD !hornerC hornerMX hornerMXn IH.
Qed.

(* Decomposiiton in odd and even part *)
Lemma odd_even_polyE p :
  p = (even_poly p \Po 'X^2) + (odd_poly p \Po 'X^2) * 'X.
Proof.
apply/polyP=> i.
rewrite coefD coefMX !coef_comp_polyXn // coef_even_poly coef_odd_poly.
rewrite !divn2 !dvdn2 -(odd_double_half i).
case: (odd i); rewrite !(add1n, add0n, oddS, odd_double, doubleK, add0r) //=.
by case: i => [|[|i]]; rewrite ?addr0 //= odd_double /= addr0.
Qed.

Fixpoint fft n w p : {poly R} := 
  if n is n1.+1 then
  let ev := fft n1 (w * w) (even_poly p) in
  let ov := fft n1 (w * w) (odd_poly p) in
  \poly_(i < 2 ^ n1.+2)
    let j := (i %% 2^n1.+1)%nat in ev`_j + ov`_ j * w ^+ i 
  else \poly_(i < 2) (if i == 0%nat :> nat then p.[1] else p.[w]).

Lemma uphalf_leq m n : (m <= n -> uphalf m <= uphalf n)%nat.
Proof.
move/subnK <-; rewrite !uphalf_half oddD halfD !addnA.
by do 2 case: odd => //=; apply: leq_addl.
Qed.

Lemma size_fft  n (w : R) p : (size (fft n w p) <= 2 ^ n.+1)%nat.
Proof. by case: n => [|n]; apply: size_poly. Qed.

Lemma fft_correct n (w : R) p i : 
   (i < 2 ^ n.+1)%nat ->
   (size p <= 2 ^ n.+1)%nat -> w ^+ (2 ^ n) = -1 -> 
   (fft n w p)`_ i = p.[w ^+ i].
Proof.
elim: n w p i =>  [w p [|[]] //=|n IH w p i iL sL wE /=]; rewrite coef_poly //.
have imL : (i %% 2 ^ n.+1 < 2 ^ n.+1)%N by apply/ltn_pmod/expn_gt0.
have n2P : (0 < 2 ^ n.+2)%nat by rewrite expn_gt0.
have n2P_halfE : (2 ^ n.+1 = uphalf (2 ^ n.+2))%nat.
  by rewrite uphalf_half !expnS !mul2n doubleK odd_double add0n.
rewrite iL !IH ?coef_poly //.
- rewrite [p in RHS]odd_even_polyE.
  rewrite !(hornerD, horner_comp_polyXn, hornerMX, hornerX).
  suff -> : (w * w) ^+ (i %% 2 ^ n.+1) = w ^+ i * w ^+ i by [].
  rewrite -!expr2 -!exprM.
  have [iLm|mLi] := leqP (2 ^ n.+1) i; last by rewrite modn_small // mulnC.
  have -> : (i %% 2 ^ n.+1 = i - 2 ^ n.+1)%nat.
    rewrite -[in LHS](subnK iLm) modnDr modn_small //.
    by rewrite ltn_psubLR ?expn_gt0 // addnn -mul2n -expnS.
  have -> : (i * 2 = 2 * (i - 2 ^ n.+1) + 2 ^ n.+2)%nat.
    by rewrite mulnC mulnBr -expnS subnK // expnS leq_mul2l.
  rewrite exprD.
  suff -> : w ^+ (2 ^ n.+2) = 1 by rewrite mulr1.
  by rewrite expnS mulnC exprM wE expr2 mulrN1 opprK.
- apply: leq_trans (size_odd_poly _) _.
  by rewrite n2P_halfE uphalf_leq.
- by rewrite -expr2 -exprM -expnS.
- apply: leq_trans (size_even_poly _) _.
  by rewrite n2P_halfE uphalf_leq.
by rewrite -expr2 -exprM -expnS.
Qed.

End FFT.
