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

Lemma if_nth (A : eqType) (x0 : A) s b n : b || (size s <= n) ->
  (if b then nth x0 s n else x0) = nth x0 s n.
Proof. by case: leqP; case: ifP => //= *; rewrite nth_default. Qed.


Lemma if_and b1 b2 T (x y : T) :
  (if b1 && b2 then x else y) = (if b1 then if b2 then x else y else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_or b1 b2 T (x y : T) :
  (if b1 || b2 then x else y) = (if b1 then x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implyb b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b1 then if b2 then x else y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_implybC b1 b2 T (x y : T) :
  (if b1 ==> b2 then x else y) = (if b2 then x else if b1 then y else x).
Proof. by case: b1 b2 => [] []. Qed.

Lemma if_add b1 b2 T (x y : T) :
  (if b1 (+) b2 then x else y) = (if b1 then if b2 then y else x else if b2 then x else y).
Proof. by case: b1 b2 => [] []. Qed.

Lemma leqVgt m n : (m <= n) || (n < m). Proof. by rewrite leqNgt orNb. Qed.

Lemma leq_sub2rE p m n : p <= n -> (m - p <= n - p) = (m <= n).
Proof. by move=> pn; rewrite leq_subLR subnKC. Qed.

Lemma leq_sub2lE m n p : n <= m -> (m - p <= m - n) = (n <= p).
Proof. by move=> nm; rewrite leq_subCl subKn. Qed.

Lemma ltn_sub2rE p m n : p <= m -> (m - p < n - p) = (m < n).
Proof. by move=> pn; rewrite ltn_subRL addnC subnK. Qed.

Lemma ltn_sub2lE m n p : p <= m -> (m - p < m - n) = (n < p).
Proof. by move=> pm; rewrite ltn_subCr subKn. Qed.

Section Poly.

Local Open Scope ring_scope.

Variable R : ringType.

Implicit Type p q : {poly R}.

(* Even part of a polynomial                                                  *)

Definition even_poly p : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.

Lemma size_even_poly p : (size (even_poly p) <= uphalf (size p))%N.
Proof. exact: size_poly. Qed.

Lemma coef_even_poly p i : (even_poly p)`_i = p`_i.*2.
Proof. by rewrite coef_poly gtn_uphalf_double if_nth ?leqVgt. Qed.

Lemma even_polyE s p : (size p <= s.*2)%N -> even_poly p = \poly_(i < s) p`_i.*2.
Proof.
move=> pLs2; apply/polyP => i; rewrite coef_even_poly !coef_poly if_nth //.
by case: ltnP => //= ?; rewrite (leq_trans pLs2) ?leq_double.
Qed.

Lemma even_polyD p q : even_poly (p + q) = even_poly p + even_poly q.
Proof. by apply/polyP => i; rewrite !(coef_even_poly, coefD). Qed.

Lemma even_polyZ k p : even_poly (k *: p) = k *: even_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_even_poly). Qed.

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

Lemma coef_odd_poly p i : (odd_poly p)`_i = p`_i.*2.+1.
Proof. by rewrite coef_poly gtn_half_double if_nth ?leqVgt. Qed.

Lemma odd_polyE s p :
  (size p <= s.*2.+1)%N -> odd_poly p = \poly_(i < s) p`_i.*2.+1.
Proof.
move=> pLs2; apply/polyP => i; rewrite coef_odd_poly !coef_poly if_nth //.
by case: ltnP => //= ?; rewrite (leq_trans pLs2) ?ltnS ?leq_double.
Qed.

Lemma odd_polyC (c : R) : odd_poly c%:P = 0.
Proof. by apply/polyP => i; rewrite coef_odd_poly !coefC; case: i. Qed.

Lemma odd_polyD p q : odd_poly (p + q) = odd_poly p + odd_poly q.
Proof. by apply/polyP => i; rewrite !(coef_odd_poly, coefD). Qed.

Lemma odd_polyZ k p : odd_poly (k *: p) = k *: odd_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_odd_poly). Qed.

Fact odd_poly_is_linear : linear odd_poly.
Proof. by move=> k p q; rewrite odd_polyD odd_polyZ. Qed.

Canonical odd_poly_additive := Additive odd_poly_is_linear.
Canonical odd_poly_linear := Linear odd_poly_is_linear.

Lemma odd_polyMX p : odd_poly (p * 'X) = even_poly p.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite mul0r even_polyC odd_polyC.
by apply/polyP => i; rewrite !coef_poly size_mulX // coefMX.
Qed.

Lemma even_polyMX p : even_poly (p * 'X) = odd_poly p * 'X.
Proof.
have [->|pN0] := eqVneq p 0; first by rewrite mul0r even_polyC odd_polyC mul0r.
by apply/polyP => -[|i]; rewrite !(coefMX, coef_poly, if_same, size_mulX).
Qed.

Lemma comp_Xn_poly p n : 'X^n \Po p = p ^+ n.
Proof.
apply/polyP => i; rewrite coef_comp_poly size_polyXn.
rewrite (bigD1 (Ordinal (leqnn n.+1))) //= coefXn eqxx big1 ?addr0 ?mul1r //.
by move=> j /eqP/val_eqP/= jDn; rewrite coefXn (negPf jDn) mul0r.
Qed.

Lemma coef_sumMXn I (r : seq I) (P : pred I) (p : I -> R) (n : I -> nat) k :
  (\sum_(i <- r | P i) p i *: 'X^(n i))`_k =
    \sum_(i <- r | P i && (n i == k)) p i.
Proof.
rewrite coef_sum big_mkcondr; apply: eq_bigr => i Pi.
by rewrite coefZ coefXn mulr_natr mulrb eq_sym.
Qed.

Lemma big_ord1_eq (A : Type) (idx : A) (op : Monoid.law idx)  (F : nat -> A) i n :
  \big[op/idx]_(j < n | j == i :> nat) F j = if (i < n)%N then F i else idx.
Proof.
case: ltnP => [i_lt|i_ge]; first by rewrite (big_pred1_eq op (Ordinal _)).
by rewrite big_pred0// => j; apply: contra_leqF i_ge => /eqP <-.
Qed.

Lemma big_ord1_cond_eq (A : Type) (idx : A) (op : Monoid.law idx) (F : nat -> A) (P : pred nat) i n :
  \big[op/idx]_(j < n | P j && (j == i :> nat)) F j =
    if (i < n)%N && P i then F i else idx.
Proof.
by rewrite big_mkcondl if_and (big_ord1_eq op (fun j => if P j then F j else _)).
Qed.

Lemma coef_comp_poly_Xn p n i : (0 < n)%N ->
  (p \Po 'X^n)`_i = if (n %| i)%N then p`_(i %/ n) else 0.
Proof.
move=> n_gt0; rewrite comp_polyE; under eq_bigr do rewrite -exprM mulnC.
rewrite coef_sumMXn/=; case: dvdnP => [[j ->]|nD]; last first.
   by rewrite big1// => j /eqP ?; case: nD; exists j.
under eq_bigl do rewrite eqn_mul2r gtn_eqF//.
by rewrite big_ord1_eq if_nth ?leqVgt ?mulnK.
Qed.

Lemma comp_poly_Xn p n : (0 < n)%N ->
  p \Po 'X^n = \poly_(i < size p * n) if (n %| i)%N then p`_(i %/ n) else 0.
Proof.
move=> n_gt0; apply/polyP => i; rewrite coef_comp_poly_Xn // coef_poly.
case: dvdnP => [[k ->]|]; last by rewrite if_same.
by rewrite mulnK // ltn_mul2r n_gt0 if_nth ?leqVgt.
Qed.

Lemma sum_even_poly p :
  \sum_(i < size p | ~~ odd i) p`_i *: 'X^i = even_poly p \Po 'X^2.
Proof.
apply/polyP => i; rewrite coef_comp_poly_Xn// coef_sumMXn coef_even_poly.
rewrite (big_ord1_cond_eq _ _ (negb \o _))/= -dvdn2 andbC -muln2.
by case: dvdnP => //= -[k ->]; rewrite mulnK// if_nth ?leqVgt.
Qed.

Lemma sum_odd_poly p :
  \sum_(i < size p | odd i) p`_i *: 'X^i = (odd_poly p \Po 'X^2) * 'X.
Proof.
apply/polyP => i; rewrite coefMX coef_comp_poly_Xn// coef_sumMXn coef_odd_poly/=.
case: i => [|i]//=; first by rewrite big_andbC big1// => -[[|j]//].
rewrite big_ord1_cond_eq/= -dvdn2 andbC -muln2.
by case: dvdnP => //= -[k ->]; rewrite mulnK// if_nth ?leqVgt.
Qed.

(* Decomposition in odd and even part                                         *)
Lemma poly_even_odd p : even_poly p \Po 'X^2 + (odd_poly p \Po 'X^2) * 'X = p.
Proof.
rewrite -sum_even_poly -sum_odd_poly addrC -(bigID _ xpredT).
by rewrite -[RHS]coefK poly_def.
Qed.

(* take and drop for polynomials                                              *)

Definition take_poly m p := \poly_(i < m) p`_i.

Lemma size_take_poly m p : (size (take_poly m p) <= m)%N.
Proof. exact: size_poly. Qed.

Lemma coef_take_poly m p i : (take_poly m p)`_i = if (i < m)%N then p`_i else 0.
Proof. exact: coef_poly. Qed.

Lemma take_poly_id m p : (size p <= m)%N -> take_poly m p = p.
Proof.
move=> /leq_trans gep; apply/polyP => i; rewrite coef_poly if_nth//=.
by case: ltnP => // /gep->.
Qed.

Lemma take_polyD m p q : take_poly m (p + q) = take_poly m p + take_poly m q.
Proof.
by apply/polyP => i; rewrite !(coefD, coef_poly); case: leqP; rewrite ?add0r.
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

Lemma take_poly_sum m I r P (p : I -> {poly R}) :
  take_poly m (\sum_(i <- r | P i) p i) = \sum_(i <- r| P i) take_poly m (p i).
Proof. exact: linear_sum. Qed.

Lemma take_poly0l p : take_poly 0 p = 0.
Proof. exact/size_poly_leq0P/size_take_poly. Qed.

Lemma take_poly0r m : take_poly m 0 = 0.
Proof. exact: linear0. Qed.

Lemma take_polyMXn m n p :
  take_poly m (p * 'X^n) = take_poly (m - n) p * 'X^n.
Proof.
have [->|/eqP p_neq0] := p =P 0; first by rewrite !(mul0r, take_poly0r).
apply/polyP => i; rewrite !(coef_take_poly, coefMXn).
by have [iLn|nLi] := leqP n i; rewrite ?if_same// ltn_sub2rE.
Qed.

Lemma take_polyMXn_0 n p : take_poly n (p * 'X^n) = 0.
Proof. by rewrite take_polyMXn subnn take_poly0l mul0r. Qed.

Lemma take_polyDMXn n p q : (size p <= n)%N -> take_poly n (p + q * 'X^n) = p.
Proof. by move=> ?; rewrite take_polyD take_poly_id// take_polyMXn_0 addr0. Qed.

Definition drop_poly m p := \poly_(i < size p - m) p`_(i + m).

Lemma coef_drop_poly m p i : (drop_poly m p)`_i = p`_(i + m).
Proof. by rewrite coef_poly ltn_subRL addnC if_nth ?leqVgt. Qed.

Lemma drop_poly_eq0 m p : (size p <= m)%N -> drop_poly m p = 0.
Proof.
move=> sLm; apply/polyP => i; rewrite coef_poly coef0 ltn_subRL addnC.
by rewrite if_nth ?leqVgt// nth_default// (leq_trans _ (leq_addl _ _)).
Qed.

Lemma size_drop_poly n p : size (drop_poly n p) = (size p - n)%N.
Proof.
have [pLn|nLp] := leqP (size p) n.
  by rewrite (eqP pLn) drop_poly_eq0 ?size_poly0.
have sp_gt0 : (0 < size p)%N by rewrite (leq_trans _ nLp).
rewrite size_poly_eq// predn_sub subnK; last by rewrite -ltnS prednK.
by rewrite -lead_coefE lead_coef_eq0 -size_poly_gt0.
Qed.

Lemma drop_polyD m p q : drop_poly m (p + q) = drop_poly m p + drop_poly m q.
Proof. by apply/polyP => i; rewrite coefD !coef_drop_poly coefD. Qed.

Lemma drop_polyZ k m p : drop_poly m (k *: p) = k *: drop_poly m p.
Proof. by apply/polyP => i; rewrite coefZ !coef_drop_poly coefZ. Qed.

Fact drop_poly_is_linear m : linear (drop_poly m).
Proof. by move=> k p q; rewrite drop_polyD drop_polyZ. Qed.

Canonical drop_poly_additive m := Additive (drop_poly_is_linear m).
Canonical drop_poly_linear m := Linear (drop_poly_is_linear m).

Lemma drop_poly_sum m I r P (p : I -> {poly R}) :
  drop_poly m (\sum_(i <- r | P i) p i) = \sum_(i <- r | P i) drop_poly m (p i).
Proof. exact: linear_sum. Qed.

Lemma drop_poly0l p : drop_poly 0 p = p.
Proof. by apply/polyP => i; rewrite coef_poly subn0 addn0 if_nth ?leqVgt. Qed.

Lemma drop_poly0r m : drop_poly m 0 = 0. Proof. exact: linear0. Qed.

Lemma drop_polyMXn m n p :
  drop_poly m (p * 'X^n) = drop_poly (m - n) p * 'X^(n - m).
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite mul0r !drop_poly0r mul0r.
apply/polyP => i; rewrite !(coefMXn, coef_drop_poly) ltn_subRL [(m + i)%N]addnC.
have [i_small|i_big]// := ltnP; congr nth.
by have [mn|/ltnW mn] := leqP m n;
   rewrite (eqP mn) (addn0, subn0) (subnBA, addnBA).
Qed.

Lemma drop_polyMXn_id n p : drop_poly n (p * 'X^ n) = p.
Proof. by rewrite drop_polyMXn subnn drop_poly0l expr0 mulr1. Qed.

Lemma drop_polyDMXn n p q : (size p <= n)%N -> drop_poly n (p + q * 'X^n) = q.
Proof. by move=> ?; rewrite drop_polyD drop_poly_eq0// drop_polyMXn_id add0r. Qed.

Lemma poly_take_drop n p : take_poly n p + drop_poly n p * 'X^n = p.
Proof.
apply/polyP => i; rewrite coefD coefMXn coef_take_poly coef_drop_poly.
by case: ltnP => ni; rewrite ?addr0 ?add0r//= subnK.
Qed.

Lemma eqp_take_drop n p q :
  take_poly n p = take_poly n q -> drop_poly n p = drop_poly n q -> p = q.
Proof.
by move=> tpq dpq; rewrite -[p](poly_take_drop n) -[q](poly_take_drop n) tpq dpq.
Qed.

End Poly.

