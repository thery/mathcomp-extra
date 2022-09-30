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
Proof. by apply: size_poly. Qed.

Lemma coef_odd_poly p i : (odd_poly p)`_ i = p `_ i.*2.+1.
Proof.
by rewrite coef_poly gtn_half_double; case: leqP => L; rewrite // nth_default.
Qed.

Lemma odd_polyC (c : R) : odd_poly c%:P = 0.
Proof. by apply/polyP => i; rewrite coef_odd_poly !coefC; case: i. Qed.

Lemma odd_polyE s (p : {poly R}) :
  ((size p) <= s.*2.+1)%N -> odd_poly p = \poly_(i < s) p`_i.*2.+1.
Proof.
move=> pLs2; apply/polyP => i; rewrite !coef_poly gtn_half_double.
have [pLi2|i2Lp] := leqP; have [sLi|iLs] := leqP; rewrite // nth_default //.
by apply: leq_trans pLs2 _; rewrite ltnS leq_double.
Qed.

Lemma odd_polyZ k p : odd_poly (k *: p) = k *: odd_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_odd_poly). Qed.

Lemma odd_polyD p q : odd_poly (p + q) = odd_poly p + odd_poly q.
Proof.
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

Lemma comp_polyXn (p : {poly R}) n :
  (0 < n)%N -> 
  p \Po 'X^n = \poly_(i < size p * n) (if (n %| i)%N then p`_(i %/ n) else 0).
Proof.
move=> nP.
apply/polyP=> i.
rewrite coef_comp_poly coef_poly.
under [LHS] eq_bigr do rewrite -exprM coefXn.
have [/dvdnP[j ->]|NiDn] := boolP (n %| i)%N; last first.
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
  (0 < n)%N -> (p \Po 'X^n)`_i = if (n %| i)%N then p`_(i %/ n) else 0.
Proof.
move=> nP; rewrite comp_polyXn // coef_poly.
case: (_ %| _)%N; last by rewrite if_same.
by case: leqP => snLi; rewrite // nth_default // leq_divRL.
Qed.

(* Decomposiiton in odd and even part                                         *)
Lemma odd_even_polyE p :
  p = (even_poly p \Po 'X^2) + (odd_poly p \Po 'X^2) * 'X.
Proof.
apply/polyP=> i.
rewrite coefD coefMX !coef_comp_polyXn // coef_even_poly coef_odd_poly.
rewrite !divn2 !dvdn2 -(odd_double_half i).
case: (odd i); rewrite !(add1n, add0n, oddS, odd_double, doubleK, add0r) //=.
by case: i => [|[|i]]; rewrite ?addr0 //= odd_double /= addr0.
Qed.

Definition take_poly m (p : {poly R}) := \poly_(i < m) p`_i.
Definition drop_poly m (p : {poly R}) := \poly_(i < m) p`_(i + m).

Lemma coef_take_poly m p i : 
  (take_poly m p)`_ i = if (i < m)%N then p`_ i else 0.
Proof. by rewrite coef_poly. Qed.

Lemma coef_drop_poly m p i : 
  (drop_poly m p)`_ i = if (i < m)%N then p`_ (i + m) else 0.
Proof. by rewrite coef_poly. Qed.

Lemma take_poly_id m p : (size p <= m)%N -> take_poly m p = p.
Proof.
move=> Hs; apply/polyP => i.
rewrite coef_poly; case: leqP => // Hs1.
by apply/sym_equal/nth_default/(leq_trans Hs).
Qed.

Lemma take_polyMXn m p : take_poly m ('X^ m * p) = 0.
Proof.
apply/polyP => i.
rewrite -[_ * p]commr_polyXn coef_poly coefMXn coef0.
by case: leqP.
Qed.

Lemma take_poly_add m (p q : {poly R}) :
  take_poly m (p + q) = take_poly m p + take_poly m q.
Proof.
apply/polyP => i; rewrite !(coefD, coef_poly).
by case: leqP; rewrite ?add0r.
Qed.

Lemma take_poly0 m : take_poly m 0 = 0.
Proof. by apply/polyP => i; rewrite coef_poly coef0 if_same. Qed.

Lemma take_poly_sum m n (p : 'I_n -> {poly R}) :
  take_poly m (\sum_(i < n) p i) = \sum_(i < n) (take_poly m (p i)).
Proof.
have F (q : nat -> _) : 
       take_poly m (\sum_(i < n) q i) = \sum_(i < n) (take_poly m (q i)).
  elim: n {p}q => [|n IH] q; first by rewrite !big_ord0 take_poly0.
  by rewrite !big_ord_recr /= take_poly_add IH.
case: n p F => [|n] p F; first by rewrite !big_ord0 take_poly0.
have := F (fun x => p (inord x)).
under eq_bigr do rewrite inord_val.
by under [X in _ = X -> _]eq_bigr do rewrite inord_val.
Qed.

Lemma drop_poly_size_0 m p : (size p <= m)%N -> drop_poly m p = 0.
Proof.
move=> Hs; apply/polyP => i.
rewrite coef_poly coef0; case: leqP => // Hs1.
apply: nth_default.
by apply: leq_trans Hs (leq_addl _ _).
Qed.

Lemma drop_polyMXn m p : (size p <= m)%N -> drop_poly m ('X^ m * p) = p.
Proof.
move=> Hs; apply/polyP => i.
rewrite -[_ * p]commr_polyXn coef_poly coefMXn addnK.
rewrite [(_ + _ < _)%N]ltnNge leq_addl /=.
case: leqP => // mLi.
by apply/sym_equal/nth_default/(leq_trans _ mLi).
Qed.

Lemma drop_poly_add m (p q : {poly R}) :
  drop_poly m (p + q) = drop_poly m p + drop_poly m q.
Proof.
apply/polyP => i; rewrite !(coefD, coef_poly).
by case: leqP; rewrite ?add0r.
Qed.

Lemma drop_poly0 m : drop_poly m 0 = 0.
Proof. by apply/polyP => i; rewrite coef_poly !coef0 if_same. Qed.

Lemma drop_poly_sum m n (p : 'I_n -> {poly R}) :
  drop_poly m (\sum_(i < n) p i) = \sum_(i < n) (drop_poly m (p i)).
Proof.
have F (q : nat -> _) : 
       drop_poly m (\sum_(i < n) q i) = \sum_(i < n) (drop_poly m (q i)).
  elim: n {p}q => [|n IH] q; first by rewrite !big_ord0 drop_poly0.
  by rewrite !big_ord_recr /= drop_poly_add IH.
case: n p F => [|n] p F; first by rewrite !big_ord0 drop_poly0.
have := F (fun x => p (inord x)).
under eq_bigr do rewrite inord_val.
by under [X in _ = X -> _]eq_bigr do rewrite inord_val.
Qed.

Lemma left_drop_polyE m p :
  (size p <= m.*2)%N -> p = take_poly m p + drop_poly m p * 'X^m.
Proof.
move=> sL2m; apply/polyP => i.
rewrite coefD coefMXn !coef_poly.
case: leqP => HlP; last by rewrite addr0.
case: leqP => H1lP; last by rewrite subnK ?add0r.
rewrite add0r nth_default //.
apply: leq_trans sL2m _.
by rewrite -addnn -leq_subRL.
Qed.

End Poly.
