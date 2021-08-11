From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Section OddEven.

Local Open Scope ring_scope.

Variable R : ringType.
Variable p : {poly R}.
Definition even_poly : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.
Definition odd_poly : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.+1.

Lemma comp_polyXn (q : {poly R}) n :
  (0 < n)%nat -> 
  q \Po 'X^n = \poly_(i < size q * n) (if (n %| i)%nat then q`_(i %/ n) else 0).
Proof.
move=> nP.
apply/polyP=> i.
rewrite coef_comp_poly coef_poly.
under [LHS] eq_bigr do rewrite -exprM coefXn.
have [/dvdnP[j ->]|NiDn] := boolP (n %| i)%nat; last first.
  rewrite if_same big1 // => j _; case: eqP; rewrite (mulr0, mulr1) // => iE.
  by case/negP: NiDn; rewrite iE dvdn_mulr.
rewrite mulnK //.
have [sLj|jLs] := leqP (size q) j.
  rewrite nth_default // if_same big1 // => l _.
  rewrite mulnC eqn_mul2l (negPf (lt0n_neq0 nP)) /=.
  case: eqP=> [jE|_]; rewrite (mulr0, mulr1) //.
  by have := ltn_ord l; rewrite -jE ltnNge sLj.
rewrite ifT; last by rewrite ltn_mul2r nP.
rewrite (bigD1 (Ordinal jLs)) //= mulnC eqxx mulr1.
rewrite big1 ?addr0 // => /= [] [l /= lLs] /eqP/val_eqP/= lDj.
by rewrite eqn_mul2l (negPf (lt0n_neq0 nP)) eq_sym (negPf lDj) mulr0.
Qed.

Lemma coef_even_poly i : even_poly `_ i = p `_ i.*2.
Proof.
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)).
move: L; rewrite uphalf_half.
case: odd; first by rewrite !add1n ltn_double.
by rewrite leq_double.
Qed.

Lemma size_even_poly : (size even_poly <= uphalf (size p))%nat.
Proof. by apply: size_poly. Qed.

Lemma coef_odd_poly i : odd_poly `_ i = p `_ i.*2.+1.
Proof.
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)).
move: L; rewrite uphalf_half.
case: odd; first by rewrite !add1n ltnS leq_double => /ltnW.
by rewrite -leq_double => /leq_trans->.
Qed.

Lemma size_odd_poly : (size odd_poly <= uphalf (size p))%nat.
Proof. by apply: size_poly. Qed.

Lemma odd_even_polyE : p = (even_poly \Po 'X^2) + 'X * (odd_poly \Po 'X^2).
Proof.
rewrite comp_polyXn.
apply/polyP=> i; rewrite coefD coefXM !coef_comp_poly.
rewrite -(odd_double_half i); case: odd; rewrite !(add1n, add0n) /=.
rewrite add1.

rewrite coefD coefXM !coef_comp_poly.

 admit.

 /=.
case (
  odd i); rewrite ?add1n /=.
  rewrite big1 ?add0r => [|j _]; last first.
    rewrite -exprM coefXn mul2n; case: eqP => E; rewrite ?mulr0 //.
    have : ~~ odd j.*2 by rewrite odd_double.
    by rewrite -E /= odd_double.
    Search (_.*2) (_.+1).
   case: eqP E => [->|]; rewrite ?(oddM, mulr0).

Search odd (_ + _)%N.
  by rewrite mulr0.

  Search _ ('X^_) inside poly.
  rewrite coefXn.
  rewrite add0r.
Check coef_sum.

rewrite !comp_polyE.
Search (_ \Po _).



Print