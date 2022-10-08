From mathcomp Require Import all_ssreflect all_algebra.


(******************************************************************************)
(*                                                                            *)
(*          Polynomial decomposition                                          *)
(*                                                                            *)
(*   odd_poly p    =  polynomial composed of the odd terms of p               *)
(*   even_poly p   =  polynomial composed of the odd terms of p               *)
(*   take_poly n p =  polynomial composed of taking the first n term of p     *)
(*   drop_poly n p =  polynomial composed of droping the first n terms of p   *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(* This is not in matchcomp yet *)

Lemma uphalfE n : uphalf n = n.+1./2.
Proof. by []. Qed.

Lemma leq_half_double m n : (m./2 <= n) = (m <= n.*2.+1).
Proof.
apply/idP/idP => [m2Ln|mLnn]; last first.
  by rewrite -[n](half_bit_double _ true) half_leq.
rewrite -[m](odd_double_half) -add1n.
by apply: leq_add; [case: odd|rewrite leq_double].
Qed.

Lemma gtn_half_double m n : (n < m./2) = (n.*2.+1 < m).
Proof. by rewrite ltnNge leq_half_double -ltnNge. Qed.

Lemma ltn_half_double m n : (m./2 < n) = (m < n.*2).
Proof. by rewrite ltnNge geq_half_double -ltnNge. Qed.

Lemma geq_uphalf_double m n : (m <= uphalf n) = (m.*2 <= n.+1).
Proof. by rewrite uphalfE geq_half_double. Qed.

Lemma gtn_uphalf_double m n : (n < uphalf m) = (n.*2 < m).
Proof. by rewrite uphalfE gtn_half_double. Qed.

Lemma ltn_uphalf m n : (uphalf m < n) = (m.+1 < n.*2).
Proof. by rewrite uphalfE ltn_half_double. Qed.

Lemma half_gtnn n : (n./2 < n) = (n != 0).
Proof.
case: n => // [] [|n] //.
rewrite eqn_leq [n.+2 <= _]leqNgt -[X in _ < X]odd_double_half -addnn addnA.
by rewrite /= [~~ _ + _]addnS addSn !ltnS leq_addl.
Qed.

Section Poly.

Local Open Scope ring_scope.

Variable R : ringType.

Implicit Type p : {poly R}.


(* Even part of a polynomial                                                  *)

Definition even_poly p : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.

Lemma even_polyE s (p : {poly R}) :
  (size p <= s.*2)%N -> even_poly p = \poly_(i < s) p`_i.*2.
Proof.
move=> pLs2; apply/polyP => i.
rewrite !coef_poly gtn_uphalf_double.
have [pLi2|i2Lp] := leqP; last by rewrite -ltn_double (leq_trans i2Lp).
by have [//|sLi] := leqP; have /leq_sizeP->// := pLi2.
Qed.

Lemma size_even_poly p : (size (even_poly p) <= uphalf (size p))%N.
Proof. by apply: size_poly. Qed.

Lemma coef_even_poly p i : (even_poly p)`_ i = p `_ i.*2.
Proof.
rewrite coef_poly gtn_uphalf_double; case: leqP => L //.
by rewrite nth_default // -(odd_double_half (size p)) .
Qed.

Lemma even_polyZ k p : even_poly (k *: p) = k *: even_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_even_poly). Qed.

Lemma even_polyD p q : even_poly (p + q) = even_poly p + even_poly q.
Proof. by apply/polyP => i; rewrite !(coef_even_poly, coefD). Qed.

Fact even_poly_is_linear : linear even_poly.
Proof. by move=> k p q; rewrite even_polyD even_polyZ. Qed.

Canonical even_poly_additive := Additive even_poly_is_linear.
Canonical even_poly_linear := Linear even_poly_is_linear.

Lemma even_polyC (c : R) : even_poly c%:P = c%:P.
Proof. by apply/polyP => i; rewrite coef_even_poly !coefC; case: i. Qed.

(* Odd part of a polynomial                                                   *)

Definition odd_poly p : {poly R} := \poly_(i < (size p)./2) p`_i.*2.+1.

Lemma size_odd_poly p : (size (odd_poly p) <= (size p)./2)%N.
Proof. exact: size_poly. Qed.

Lemma coef_odd_poly p i : (odd_poly p)`_ i = p `_ i.*2.+1.
Proof.
by rewrite coef_poly gtn_half_double; case: leqP => L; rewrite // nth_default.
Qed.

Lemma odd_polyC (c : R) : odd_poly c%:P = 0.
Proof. by apply/polyP => i; rewrite coef_odd_poly !coefC; case: i. Qed.

Lemma odd_polyE s (p : {poly R}) :
  (size p <= s.*2.+1)%N -> odd_poly p = \poly_(i < s) p`_i.*2.+1.
Proof.
move=> pLs2; apply/polyP => i; rewrite !coef_poly gtn_half_double.
have [pLi2|i2Lp] := leqP; have [sLi|iLs] := leqP; rewrite // nth_default //.
by apply: leq_trans pLs2 _; rewrite ltnS leq_double.
Qed.

Lemma odd_polyZ k p : odd_poly (k *: p) = k *: odd_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_odd_poly). Qed.

Lemma odd_polyD p q : odd_poly (p + q) = odd_poly p + odd_poly q.
Proof. by apply/polyP => i; rewrite !(coef_odd_poly, coefD). Qed.

Fact odd_poly_is_linear : linear odd_poly.
Proof. by move=> k p q; rewrite odd_polyD odd_polyZ. Qed.

Canonical odd_poly_additive := Additive odd_poly_is_linear.
Canonical odd_poly_linear := Linear odd_poly_is_linear.

Lemma odd_polyX p : odd_poly (p * 'X) = even_poly p.
Proof.
have [->|/eqP p_neq0] := p =P 0; first by rewrite mul0r even_polyC odd_polyC.
apply/polyP => i.
by rewrite !coef_poly size_mulX // -[_./2]/(uphalf _) coefMX.
Qed.

Lemma even_polyX p : even_poly (p * 'X) = odd_poly p * 'X.
Proof.
have [->|/eqP p_neq0] := p =P 0.
  by rewrite mul0r even_polyC odd_polyC mul0r.
by apply/polyP => [] [|i]; rewrite !(coefMX, coef_poly, if_same, size_mulX).
Qed.

Lemma comp_polyXn (p : {poly R}) n : 'X^n \Po p = p ^+ n.
Proof.
apply/polyP=> i.
rewrite coef_comp_poly size_polyXn.
rewrite (bigD1 (Ordinal (leqnn n.+1))) //= coefXn eqxx big1 ?addr0 ?mul1r //.
by move=> j /eqP/val_eqP/= jDn; rewrite coefXn (negPf jDn) mul0r.
Qed.

Lemma coef_comp_polyXnr (p : {poly R}) n i :
  (0 < n)%N -> (p \Po 'X^n)`_i = if (n %| i)%N then p`_(i %/ n) else 0.
Proof.
move=> nP.
rewrite coef_comp_poly.
under eq_bigr do rewrite -exprM coefXn mulr_natr mulrb.
rewrite -big_mkcond /=.
case: (boolP (_ %| _)%N) => [/dvdnP[j ->]|n_div]; last first.
  rewrite big_pred0 // => j; apply: contraNF n_div => /eqP->.
  exact: dvdn_mulr.
under eq_bigl do rewrite mulnC eqn_mul2l gtn_eqF //= eq_sym.
rewrite mulnK //.
case: (leqP (size p) j) => [j_big|j_small]; last first.
  by rewrite (big_pred1_eq _ (Ordinal _)).
rewrite big_pred0 ?nth_default // => k.
by apply: contra_leqF j_big => /eqP<-.
Qed.

Lemma comp_polyXnr (p : {poly R}) n :
  (0 < n)%N -> 
  p \Po 'X^n = \poly_(i < size p * n) (if (n %| i)%N then p`_(i %/ n) else 0).
Proof.
move=> nP.
apply/polyP=> i.
rewrite coef_comp_polyXnr // coef_poly.
case: dvdnP=> [[k ->]|]; last by rewrite if_same.
rewrite mulnK // ltn_mul2r nP.
by case: ltnP => ? //; rewrite nth_default.
Qed.


(* Decomposition in odd and even part                                         *)
Lemma odd_even_polyE p :
  p = (even_poly p \Po 'X^2) + (odd_poly p \Po 'X^2) * 'X.
Proof.
apply/polyP=> i.
rewrite coefD coefMX !coef_comp_polyXnr // coef_even_poly coef_odd_poly.
rewrite !divn2 !dvdn2 -(odd_double_half i).
case: (odd i); rewrite !(add1n, add0n, oddS, odd_double, doubleK, add0r) //=.
by case: i => [|[|i]]; rewrite ?addr0 //= odd_double /= addr0.
Qed.

(* take and drop for polynomials                                              *)

Definition take_poly m (p : {poly R}) := \poly_(i < m) p`_i.
Definition drop_poly m (p : {poly R}) := \poly_(i < size p - m) p`_(i + m).

Lemma size_take_poly m p : (size (take_poly m p) <= m)%N.
Proof. by exact: size_poly. Qed.

Lemma size_drop_poly m p : (size (drop_poly m p) <= size p - m)%N.
Proof. by exact: size_poly. Qed.

Lemma coef_drop_poly m p i : (drop_poly m p)`_ i = p`_ (i + m).
Proof.
by rewrite coef_poly ltn_subRL addnC; case: leqP => // /(nth_default _).
Qed.

Lemma coef_take_poly m p i : 
  (take_poly m p)`_ i = if (i < m)%N then p`_ i else 0.
Proof. by rewrite coef_poly. Qed.

Lemma take_poly_id m p : (size p <= m)%N -> take_poly m p = p.
Proof.
move=> Hs; apply/polyP => i.
rewrite coef_poly; case: leqP => // Hs1.
by apply/sym_equal/nth_default/(leq_trans Hs).
Qed.

Lemma take_polyD m (p q : {poly R}) :
  take_poly m (p + q) = take_poly m p + take_poly m q.
Proof.
apply/polyP => i; rewrite !(coefD, coef_poly).
by case: leqP; rewrite ?add0r.
Qed.

Lemma take_polyZ k m p : take_poly m (k *: p) = k *: take_poly m p.
Proof.
apply/polyP => i; rewrite !(coefZ, coef_take_poly); case: leqP => //.
by rewrite mulr0.
Qed.

Fact take_poly_is_linear m : linear (take_poly m).
Proof. by move=> k p q; rewrite take_polyD take_polyZ. Qed.

Canonical take_poly_additive m := Additive (take_poly_is_linear m).
Canonical take_poly_linear m := Linear (take_poly_is_linear m).

Lemma take_poly0l p : take_poly 0 p = 0.
Proof.
by apply/eqP; rewrite -size_poly_leq0 (leq_trans (size_take_poly _ _)).
Qed.

Lemma take_poly0r m : take_poly m 0 = 0.
Proof. by rewrite linear0. Qed.

Lemma take_poly_sum m n (p : 'I_n -> {poly R}) P :
  take_poly m (\sum_(i < n | P i) p i) = \sum_(i < n| P i) (take_poly m (p i)).
Proof. by rewrite linear_sum. Qed.

Lemma take_polyMXn m n p :
  take_poly m (p * 'X^ n) = take_poly (m - n) p * 'X^n.
Proof.
have [->|/eqP p_neq0] := p =P 0; first by rewrite !(mul0r, take_poly0r).
apply/polyP => i.
rewrite !(coef_take_poly, coefMXn).
by case: (leqP n) => iLn; rewrite ?if_same // ltn_subRL addnC subnK.
Qed.

Lemma drop_poly_eq0 m p : (size p <= m)%N -> drop_poly m p = 0.
Proof.
move=> sLm; apply/polyP => i.
rewrite coef_poly coef0; case: leqP => // Hs1.
apply: nth_default.
by apply: leq_trans sLm (leq_addl _ _).
Qed.

Lemma drop_polyZ k m p : drop_poly m (k *: p) = k *: drop_poly m p.
Proof. by apply/polyP => i; rewrite coefZ !coef_drop_poly coefZ. Qed.

Lemma drop_polyD m (p q : {poly R}) :
  drop_poly m (p + q) = drop_poly m p + drop_poly m q.
Proof. by apply/polyP => i; rewrite coefD !coef_drop_poly coefD. Qed.

Fact drop_poly_is_linear m : linear (drop_poly m).
Proof. by move=> k p q; rewrite drop_polyD drop_polyZ. Qed.

Canonical drop_poly_additive m := Additive (drop_poly_is_linear m).
Canonical drop_poly_linear m := Linear (drop_poly_is_linear m).

Lemma drop_poly0l p : drop_poly 0 p = p.
Proof.
apply/polyP => i; rewrite coef_poly subn0 addn0.
by case: leqP => // /(nth_default _)->.
Qed.

Lemma drop_poly0r m : drop_poly m 0 = 0.
Proof. by rewrite linear0. Qed.

Lemma drop_poly_sum m n (p : 'I_n -> {poly R}) P :
  drop_poly m (\sum_(i < n | P i) p i) = \sum_(i < n | P i) (drop_poly m (p i)).
Proof. by rewrite linear_sum. Qed.

Lemma size_mulXn n p : p != 0 -> size (p * 'X^n) = (n + size p)%N.
Proof.
elim: n p => [p p_neq0| n IH p p_neq0]; first by rewrite mulr1.
by rewrite exprS mulrA IH -?size_poly_eq0 size_mulX // addnS.
Qed.

Lemma drop_polyMXn m n p :
  drop_poly m (p * 'X^ n) = drop_poly (m - n) p * 'X^ (n - m).
Proof.
have [->|/eqP p_neq0] := p =P 0; first by rewrite mul0r !drop_poly0r mul0r.
apply/polyP => i.
have [mLn|/ltnW nLm]:= leqP m n. 
  have -> : (m - n = 0)%N by apply/eqP; rewrite subn_eq0.
  rewrite drop_poly0l coef_drop_poly !coefMXn !ltn_subRL.
  by rewrite [(m + i)%N]addnC //= ?subnBA.
have -> : (n - m = 0)%N by apply/eqP; rewrite subn_eq0.
rewrite mulr1 !coef_drop_poly coefMXn addnBA // ifN // -leqNgt.
by apply: leq_trans (leq_addl _ _).
Qed.

Lemma take_drop_polyE m p : p = take_poly m p + drop_poly m p * 'X^m.
Proof.
apply/polyP => i.
rewrite coefD coefMXn !coef_poly.
case: leqP => HlP; last by rewrite addr0.
case: leqP => H1lP; last by rewrite subnK ?add0r.
by rewrite add0r nth_default // -(subnK HlP) addnC -leq_subLR.
Qed.

End Poly.

