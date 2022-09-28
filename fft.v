From mathcomp Require Import all_ssreflect all_algebra ssrnum.
Require Import digitn.

(******************************************************************************)
(*                                                                            *)
(*             Proof of the Fast Fourier Transform                            *)
(*              inspired by a paper by V. Capretta                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.POrderTheory Num.ExtraDef Num.

Section FFT.

Local Open Scope ring_scope.

(* Arbitary idomain                                                           *)
(* In fact  it works for an arbitray ring. We ask for idomain in order to use *)
(* primitive-root and sqr_eqf1                                                *)
Variable R : idomainType.

Implicit Type p : {poly R}.

Lemma prim_exp2nS n (w : R) : (2 ^ n.+1).-primitive_root w -> w ^+ (2 ^ n) = -1.
Proof.
move=> Hp; have /prim_expr_order/eqP := Hp.
rewrite expnS mulnC exprM sqrf_eq1 => /orP[]/eqP // /eqP.
by rewrite -(prim_order_dvd Hp) dvdn_Pexp2l // ltnn.
Qed.

Lemma prim_sqr n (w : R) :
  (2 ^ n.+1).-primitive_root w -> (2 ^ n).-primitive_root (w * w).
Proof.
move=> Hp.
rewrite -expr2.
have -> : (2 ^ n = 2 ^ n.+1 %/ (gcdn 2 (2 ^ n.+1)))%N.
  by rewrite -(expn_min _ 1) (minn_idPl _) // expnS mulKn.
by rewrite exp_prim_root.
Qed.

Lemma leq_uphalf m n : (uphalf m <= n)%N = (m <= n.*2)%N.
Proof.
rewrite -[X in (X <= _.*2)%N]odd_double_half uphalf_half.
by case: odd ; [rewrite !add1n ltn_double | rewrite leq_double].
Qed.

(* Even part of a polynomial                                                  *)

Definition even_poly p : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.

Lemma even_polyE s (p : {poly R}) :
  (size p <= s.*2)%N -> even_poly p = \poly_(i < s) p`_i.*2.
Proof.
move=> pLs2; apply/polyP => i.
rewrite !coef_poly ltnNge leq_uphalf_double -ltnNge.
have [pLi2|i2Lp] := leqP; last by rewrite -ltn_double (leq_trans i2Lp).
by have [//|sLi] := leqP; have /leq_sizeP->// := pLi2.
Qed.

Lemma size_even_poly p : (size (even_poly p) <= uphalf (size p))%N.
Proof. by apply: size_poly. Qed.

Lemma coef_even_poly p i : (even_poly p)`_ i = p `_ i.*2.
Proof.
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)) .
move: L; rewrite uphalf_half.
by case: odd; [rewrite !add1n ltn_double | rewrite leq_double].
Qed.

Lemma even_polyZ k p : even_poly (k *: p) = k *: even_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_even_poly). Qed.

Lemma even_polyD p q : even_poly (p + q) = even_poly p + even_poly q.
Proof.
apply/polyP => i.
pose s := uphalf (maxn (size p) (size q)).
have pLs2 : (size p <= s.*2)%N.
  by rewrite -leq_uphalf_double uphalf_leq // leq_maxl.
have qLs2 : (size q <= s.*2)%N.
  by rewrite -leq_uphalf_double uphalf_leq // leq_maxr.
have pqLs2 : (size (p + q)%R <= s.*2)%N.
  by rewrite (leq_trans (size_add _ _)) // -leq_uphalf_double.
rewrite (even_polyE pqLs2) (even_polyE pLs2) (even_polyE qLs2).
by rewrite coefD !coef_poly; case: leqP; [rewrite add0r | rewrite coefD].
Qed.

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
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)) -add1n.
by apply: leq_add; [case: odd | rewrite leq_double].
Qed.

Lemma odd_polyC (c : R) : odd_poly c%:P = 0.
Proof. by apply/polyP => i; rewrite coef_odd_poly !coefC; case: i. Qed.

Lemma leq_half m n : ((m./2 <= n) = (m <= n.*2.+1))%N.
Proof.
apply/idP/idP => [m2Ln|mLnn]; last first.
  by rewrite -[n](half_bit_double _ true) half_leq.
rewrite -[m](odd_double_half) -add1n.
by apply: leq_add; [case: odd|rewrite leq_double].
Qed.

Lemma odd_polyE s (p : {poly R}) :
  ((size p) <= s.*2.+1)%N -> odd_poly p = \poly_(i < s) p`_i.*2.+1.
Proof.
move=> pLs2; apply/polyP => i; rewrite !coef_poly.
have [pLi2|i2Lp] := leqP; have [sLi|iLs] := leqP;
    rewrite // nth_default // -[size _]odd_double_half -add1n;
    (apply: leq_add; [case: odd => // | rewrite leq_double //]).
rewrite leq_half.
apply: leq_trans pLs2 _.
by rewrite ltnS leq_double.
Qed.

Lemma odd_polyZ k p : odd_poly (k *: p) = k *: odd_poly p.
Proof. by apply/polyP => i; rewrite !(coefZ, coef_odd_poly). Qed.

Lemma odd_polyD p q : odd_poly (p + q) = odd_poly p + odd_poly q.
Proof.
apply/polyP => i; pose s := (maxn (size p) (size q))./2.
have pLs2 : (size p <= s.*2.+1)%N.
  by rewrite -leq_half half_leq // leq_maxl.
have qLs2 : (size q <= s.*2.+1)%N.
  by rewrite -leq_half half_leq // leq_maxr.
have pqLs2 : (size (p + q)%R <= s.*2.+1)%N.
  by rewrite (leq_trans (size_add _ _)) //  geq_max pLs2.
rewrite (odd_polyE pqLs2) (odd_polyE pLs2) (odd_polyE qLs2).
by rewrite coefD !coef_poly; case: leqP; [rewrite add0r | rewrite coefD].
Qed.

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

(* Auxillary lemmas for _ \Po X'X^n                                           *)

Lemma coef_comp_polyXn (p : {poly R}) n i :
  (0 < n)%N -> (p \Po 'X^n)`_i = if (n %| i)%N then p`_(i %/ n) else 0.
Proof.
move=> nP; rewrite coef_comp_poly.
under eq_bigr do rewrite -exprM coefXn.
have [sLi|iLs] := leqP (size p) (i %/n).
  rewrite nth_default // if_same big1 // => j _.
  case: eqP =>[iE |]; last by rewrite mulr0.
  by rewrite iE mulKn // leqNgt ltn_ord in sLi.
rewrite (bigD1 (Ordinal iLs)) //= big1 => [|j].
  rewrite addr0 dvdn_eq [(n * _)%N]mulnC eq_sym.
  by case: eqP => []; rewrite !(mulr1, mulr0).
case: (i =P _) => [iE /eqP[]|]; last by rewrite mulr0.
by apply/val_eqP; rewrite /= iE mulKn.
Qed.

Lemma comp_polyXn (p : {poly R}) n :
  (0 < n)%N -> 
  p \Po 'X^n = \poly_(i < size p * n) (if (n %| i)%N then p`_(i %/ n) else 0).
Proof.
move=> nP; apply/polyP=> i.
rewrite coef_comp_polyXn // coef_poly.
by case: leqP => // sLi; rewrite nth_default ?if_same // leq_divRL.
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
 
(* The recursive algorithm                                                    *)
Fixpoint fft (n : nat) (w : R) (p : {poly R}) : {poly R} := 
  if n is n1.+1 then
    let ev := fft n1 (w * w) (even_poly p) in
    let ov := fft n1 (w * w) (odd_poly p) in
    \poly_(i < 2 ^ n1.+1) let j := (i %% 2 ^ n1)%N in ev`_j + ov`_ j * w ^+ i 
  else (p`_0)%:P.

Lemma size_fft n w p : (size (fft n w p) <= 2 ^ n)%N.
Proof. 
by case: n => [|n] /=; [rewrite size_polyC; case: eqP | apply: size_poly].
Qed.

Fact half_exp2n n : (uphalf (2 ^ n.+1) = 2 ^ n)%N.
Proof.
by rewrite uphalf_half !expnS !mul2n doubleK odd_double add0n.
Qed.

Fact size_odd_poly_exp2n n p : 
  (size p <= 2 ^ n.+1 -> size (odd_poly p) <= 2 ^ n)%N.
Proof.
move=> Hs; apply: leq_trans (size_odd_poly _) _.
by rewrite leq_half (leq_trans Hs) // -mul2n -expnS.
Qed.

Fact size_even_poly_exp2n n p : 
  (size p <= 2 ^ n.+1 -> size (even_poly p) <= 2 ^ n)%N.
Proof.
move=> Hs; apply: leq_trans (size_even_poly _) _.
by rewrite -half_exp2n uphalf_leq.
Qed.

Lemma poly_size1 p : (size p <= 1)%N -> p = (p`_0)%:P.
Proof.
move=> sL.
rewrite -[LHS]coefK poly_def; case E : size sL => [|[]]// _.
  by rewrite big_ord0 -[p]coefK E poly_def big_ord0 !coefC.
by rewrite big_ord1 alg_polyC.
Qed.

Lemma poly_size2 p : (size p <= 2)%N -> p = (p`_0)%:P + (p`_1)%:P * 'X.
Proof.
rewrite leq_eqVlt => /orP[/eqP spE|/poly_size1->]; last first.
  by rewrite !coefC /= mul0r addr0.
by rewrite -[LHS]coefK poly_def spE big_ord_recr /= 
           big_ord1 alg_polyC mul_polyC.
Qed.

(* Its correctness                                                            *)
Lemma fftE n (w : R) p : 
  (size p <= 2 ^ n)%N -> (2 ^ n).-primitive_root w ->
  fft n w p = \poly_(i < 2 ^ n) p.[w ^+ i].
Proof.
elim: n w p => [/= w p sL _ |n IH w p sL wE /=].
  by rewrite poly_def big_ord1 expr0 [p]poly_size1 // !hornerE alg_polyC coefC.
apply/polyP => i; rewrite !coef_poly; case: leqP => // iL.
have imL : (i %% 2 ^ n < 2 ^ n)%N by apply/ltn_pmod/expn_gt0.
have n2P : (0 < 2 ^ n.+1)%N by rewrite expn_gt0.
have wwE := prim_sqr wE.
rewrite !IH ?coef_poly ?imL ?size_even_poly_exp2n ?size_odd_poly_exp2n //.
rewrite [p in RHS]odd_even_polyE.
rewrite !(hornerD, horner_comp, hornerMX, hornerX).
suff -> : (w * w) ^+ (i %% 2 ^ n) = w ^+ i * w ^+ i by [].
rewrite -!expr2 -!exprM.
have [iLm|mLi] := leqP (2 ^ n) i; last by rewrite modn_small // mulnC.
have -> : (i %% 2 ^ n = i - 2 ^ n)%N.
  rewrite -[in LHS](subnK iLm) modnDr modn_small //.
  by rewrite ltn_psubLR ?expn_gt0 // addnn -mul2n -expnS.
have -> : (i * 2 = 2 * (i - 2 ^ n) + 2 ^ n.+1)%N.
  by rewrite mulnC mulnBr -expnS subnK // expnS leq_mul2l.
rewrite exprD.
suff -> : w ^+ (2 ^ n.+1) = 1 by rewrite mulr1.
by rewrite expnS exprM expr2 (prim_expr_order wwE).
Qed.

(* The algorithm with explicitely the butterfly                               *)
Fixpoint fft1 n w p : {poly R} := 
  if n is n1.+1 then
  let ev := fft1 n1 (w * w) (even_poly p) in
  let ov := fft1 n1 (w * w) (odd_poly p) in
  \sum_(j < 2 ^ n1)
    ((ev`_j + ov`_ j * w ^+ j) *: 'X^j +
     (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + 2 ^ n1)) 
  else (p`_0)%:P.

Lemma fft1S n w p : 
  fft1 n.+1 w p = 
  let ev := fft1 n (w * w) (even_poly p) in
  let ov := fft1 n (w * w) (odd_poly p) in
  \sum_(j < 2 ^ n)
    ((ev`_j + ov`_ j * w ^+ j) *: 'X^j +
     (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + 2 ^ n)).
Proof. by []. Qed. 

Lemma fft1E n (w : R) p : 
  (size p <= 2 ^ n)%N -> (2 ^ n).-primitive_root w -> 
  fft n w p = fft1 n w p.
Proof.
elim: n w p => [// |n IH w p sL wE /=].
have wwE := prim_sqr wE.
rewrite poly_def -(@big_mkord _ (0 : {poly R}) +%R (2 ^ n.+1) xpredT
   (fun (i : nat) => 
      ((fft n (w * w) (even_poly p))`_(i %% 2 ^ n) +
    (fft n (w * w) (odd_poly p))`_(i %% 2 ^ n) * w ^+ i) *: 'X^i)).
have F : (2 ^ n <= 2 ^ n.+1)%N by rewrite leq_exp2l.
rewrite (big_cat_nat _ _ _ _ F) //=.
rewrite big_nat; under eq_bigr do rewrite modn_small // ; rewrite -big_nat /=.
rewrite -(add0n (2 ^ n)%N) big_addn add0n.
rewrite [(2 ^ n.+1)%N]expnS mul2n -addnn addnK.
rewrite big_split /= big_mkord; congr (_ + _).
  by apply: eq_bigr => i _;
      rewrite !IH ?size_even_poly_exp2n ?size_odd_poly_exp2n //.
rewrite big_nat; under eq_bigr do
    rewrite modnDr modn_small // exprD (prim_exp2nS wE) mulrN1 mulrN;
    rewrite -big_nat /=.
rewrite big_mkord; apply: eq_bigr => i _.
by rewrite !IH ?size_even_poly_exp2n ?size_odd_poly_exp2n.
Qed.

Definition left_poly m (p : {poly R}) := \poly_(i < m) p`_i.
Definition right_poly m (p : {poly R}) := \poly_(i < m) p`_(i + m).

Lemma coef_left_poly m p i : 
  (left_poly m p)`_ i = if (i < m)%N then p`_ i else 0.
Proof. by rewrite coef_poly. Qed.

Lemma coef_right_poly m p i : 
  (right_poly m p)`_ i = if (i < m)%N then p`_ (i + m) else 0.
Proof. by rewrite coef_poly. Qed.

Lemma left_poly_id m p : (size p <= m)%N -> left_poly m p = p.
Proof.
move=> Hs; apply/polyP => i.
rewrite coef_poly; case: leqP => // Hs1.
by apply/sym_equal/nth_default/(leq_trans Hs).
Qed.

Lemma left_polyMXn m p : left_poly m ('X^ m * p) = 0.
Proof.
apply/polyP => i.
rewrite -[_ * p]commr_polyXn coef_poly coefMXn coef0.
by case: leqP.
Qed.

Lemma left_poly_add m (p q : {poly R}) :
  left_poly m (p + q) = left_poly m p + left_poly m q.
Proof.
apply/polyP => i; rewrite !(coefD, coef_poly).
by case: leqP; rewrite ?add0r.
Qed.

Lemma left_poly0 m : left_poly m 0 = 0.
Proof. by apply/polyP => i; rewrite coef_poly coef0 if_same. Qed.

Lemma left_poly_sum m n (p : 'I_n -> {poly R}) :
  left_poly m (\sum_(i < n) p i) = \sum_(i < n) (left_poly m (p i)).
Proof.
have F (q : nat -> _) : 
       left_poly m (\sum_(i < n) q i) = \sum_(i < n) (left_poly m (q i)).
  elim: n {p}q => [|n IH] q; first by rewrite !big_ord0 left_poly0.
  by rewrite !big_ord_recr /= left_poly_add IH.
case: n p F => [|n] p F; first by rewrite !big_ord0 left_poly0.
have := F (fun x => p (inord x)).
under eq_bigr do rewrite inord_val.
by under [X in _ = X -> _]eq_bigr do rewrite inord_val.
Qed.

Lemma right_poly_size_0 m p : (size p <= m)%N -> right_poly m p = 0.
Proof.
move=> Hs; apply/polyP => i.
rewrite coef_poly coef0; case: leqP => // Hs1.
apply: nth_default.
by apply: leq_trans Hs (leq_addl _ _).
Qed.

Lemma right_polyMXn m p : (size p <= m)%N -> right_poly m ('X^ m * p) = p.
Proof.
move=> Hs; apply/polyP => i.
rewrite -[_ * p]commr_polyXn coef_poly coefMXn addnK.
rewrite [(_ + _ < _)%N]ltnNge leq_addl /=.
case: leqP => // mLi.
by apply/sym_equal/nth_default/(leq_trans _ mLi).
Qed.

Lemma right_poly_add m (p q : {poly R}) :
  right_poly m (p + q) = right_poly m p + right_poly m q.
Proof.
apply/polyP => i; rewrite !(coefD, coef_poly).
by case: leqP; rewrite ?add0r.
Qed.

Lemma right_poly0 m : right_poly m 0 = 0.
Proof. by apply/polyP => i; rewrite coef_poly !coef0 if_same. Qed.

Lemma right_poly_sum m n (p : 'I_n -> {poly R}) :
  right_poly m (\sum_(i < n) p i) = \sum_(i < n) (right_poly m (p i)).
Proof.
have F (q : nat -> _) : 
       right_poly m (\sum_(i < n) q i) = \sum_(i < n) (right_poly m (q i)).
  elim: n {p}q => [|n IH] q; first by rewrite !big_ord0 right_poly0.
  by rewrite !big_ord_recr /= right_poly_add IH.
case: n p F => [|n] p F; first by rewrite !big_ord0 right_poly0.
have := F (fun x => p (inord x)).
under eq_bigr do rewrite inord_val.
by under [X in _ = X -> _]eq_bigr do rewrite inord_val.
Qed.

Lemma left_right_polyE m p :
  (size p <= m.*2)%N -> p = left_poly m p + right_poly m p * 'X^m.
Proof.
move=> sL2m; apply/polyP => i.
rewrite coefD coefMXn !coef_poly.
case: leqP => HlP; last by rewrite addr0.
case: leqP => H1lP; last by rewrite subnK ?add0r.
rewrite add0r nth_default //.
apply: leq_trans sL2m _.
by rewrite -addnn -leq_subRL.
Qed.

Definition step m n w (p : {poly R}) :=
  \sum_(l < 2 ^ m)
  let ev := \poly_(i < 2 ^ n) p`_(i + l * 2 ^ n.+1) in
  let ov := \poly_(i < 2 ^ n) p`_(i + l * 2 ^ n.+1 + 2 ^ n) in
    \sum_(j < 2 ^ n)
      ((ev`_j + ov`_ j * w ^+ j) *: 'X^(j + l * 2 ^ n.+1) +
       (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + l * 2 ^ n.+1 + 2 ^ n)).

Lemma stepE m n w (p : {poly R}) :
  step m n w p =
  \sum_(l < 2 ^ m)
  let ev := \poly_(i < 2 ^ n) p`_(i + l * 2 ^ n.+1) in
  let ov := \poly_(i < 2 ^ n) p`_(i + l * 2 ^ n.+1 + 2 ^ n) in
    (\sum_(j < 2 ^ n)
      ((ev`_j + ov`_ j * w ^+ j) *: 'X^j +
       (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + 2 ^ n))) * 
    'X^ (l * 2 ^ n.+1).
Proof.
apply: eq_bigr => i _ /=.
rewrite [RHS]mulr_suml.
apply: eq_bigr => j _ /=.
rewrite mulrDl; congr (_ + _); rewrite -scalerAl -exprD //.
by rewrite addnAC.
Qed.

Lemma size_step m n w p : (size (step m n w p) <= (2 ^ (m + n).+1))%N.
Proof.
apply: leq_trans (size_sum _ _ _) _.
apply/bigmax_leqP_seq => i _ _.
apply: leq_trans (size_sum _ _ _) _.
apply/bigmax_leqP_seq => j _ _.
apply: leq_trans (size_add _ _) _.
rewrite geq_max; apply/andP; split; 
    apply: leq_trans (size_scale_leq _ _) _; rewrite size_polyXn.
  apply: leq_trans (_ : 2  ^ n + i *2 ^ n.+1 <= _ )%N.
    by rewrite ltn_add2r.
  apply: leq_trans (_ : (2 ^ m.+1).-1 *2 ^ n <= _ )%N; last first.
    by rewrite -addSn expnD leq_mul2r leq_pred expn_eq0 orbT.
  rewrite expnS mulnA -mulSn leq_mul2r expn_eq0 /=.
  by rewrite -subn1 ltn_subRL add1n muln2 -doubleS expnS mul2n leq_double.
rewrite addnAC.
apply: leq_trans (_ : 2 ^ n + 2 ^ n + i *2 ^ n.+1 <= _ )%N.
  by rewrite -!addnA ltn_add2r.
by rewrite addnn -mul2n -expnS -mulSn -addnS expnD leq_mul2r expn_eq0 /=.
Qed.

Lemma left_step m n w (p : {poly R}) :
  (size p <= 2 ^ (m + n).+2)%N ->
  left_poly (2 ^ (m + n).+1) (step m.+1 n w p) =
  step m n w (left_poly (2 ^ (m + n).+1) p).
Proof.
move=> pLmn; rewrite stepE.
apply/polyP=> i; rewrite coef_left_poly.
case: leqP => [mnLi|iLmn].
  rewrite nth_default //.
  by apply: leq_trans (size_step _ _ _ _) _.
rewrite stepE !coef_sum expnS mul2n -addnn big_split_ord /=.
rewrite [X in _ + X = _]big1 ?addr0 => [|j _]; last first.
  by rewrite coefMXn ifT // (leq_trans iLmn) // mulnDl -expnD addnS leq_addr.
apply: eq_bigr => j _.
congr (((_ * _) : {poly R}) `_ _).
apply: eq_bigr => k _.
have F : (k + j * 2 ^ n.+1 < 2 ^ (m + n).+1)%N.
  apply: leq_trans (_ : 2 ^ n + j * 2 ^ n.+1 <= _ )%N.
    by rewrite ltn_add2r.
  rewrite -addSn expnS mulnA muln2 -mulSn expnD leq_mul2r.
  by rewrite expnS mul2n ltn_double ltn_ord orbT.
have F1 : (k + j * 2 ^ n.+1 + 2 ^ n < 2 ^ (m + n).+1)%N.
  rewrite addnAC.
  apply: leq_trans (_ : 2 ^ n + 2 ^ n + j * 2 ^ n.+1 <= _ )%N.
    by rewrite -!addnA ltn_add2r.
  by rewrite addnn -mul2n -expnS -mulSn -addnS expnD leq_mul2r ltn_ord orbT.
by rewrite !coef_poly F F1.
Qed.

Lemma right_step m n w (p : {poly R}) :
  (size p <= 2 ^ (m + n).+2)%N ->
  right_poly (2 ^ (m + n).+1) (step m.+1 n w p) =
  step m n w (right_poly (2 ^ (m + n).+1) p).
Proof.
move=> pLmn.
apply/polyP=> i; rewrite coef_right_poly.
case: leqP => [mnLi|iLmn].
  rewrite nth_default //.
  by apply: leq_trans (size_step _ _ _ _) _.
rewrite !stepE !coef_sum expnS mul2n -addnn big_split_ord /=.
rewrite [X in X + _ = _]big1 ?add0r => [|j _]; last first.
  rewrite coefMXn ifN; last first.
    rewrite -leqNgt (leq_trans _ (leq_addl _ _)) //.
    by rewrite -addnS expnD leq_mul2r // ltnW ?orbT.
  rewrite nth_default //.
  apply: leq_trans (_ : 2 ^ n.+1 <= _)%N.
    apply: leq_trans (size_sum _ _ _) _.
    apply/bigmax_leqP => k _.
    apply: leq_trans (size_add _ _) _.
    rewrite geq_max; apply/andP; split; apply: leq_trans (size_scale_leq _ _) _.
      rewrite size_polyXn.
      by apply: leq_trans (ltn_ord _) _; rewrite leq_exp2l.
    by rewrite size_polyXn expnS mul2n -addnn ltn_add2r.
  rewrite leq_subRL (leq_trans _ (leq_addl _ _)) //.
    by rewrite addnC -mulSn -addnS expnD leq_mul2r ltn_ord orbT.
  by rewrite -addnS expnD leq_mul2r ltnW ?orbT // ltn_ord.
apply: eq_bigr => j _.
rewrite !coefMXn addnC mulnDl -expnD addnS ltn_add2l.
case: leqP => // jLi; rewrite subnDl.
congr ((_ : {poly R}) `_ _).
apply: eq_bigr => k _.
have F : (k + j * 2 ^ n.+1 < 2 ^ (m + n).+1)%N.
  apply: leq_trans (_ : 2 ^ n + j * 2 ^ n.+1 <= _ )%N.
    by rewrite ltn_add2r.
  rewrite -addSn expnS mulnA muln2 -mulSn expnD leq_mul2r.
  by rewrite expnS mul2n ltn_double ltn_ord orbT.
have F1 : (k + j * 2 ^ n.+1 + 2 ^ n < 2 ^ (m + n).+1)%N.
  rewrite addnAC.
  apply: leq_trans (_ : 2 ^ n + 2 ^ n + j * 2 ^ n.+1 <= _ )%N.
    by rewrite -!addnA ltn_add2r.
  by rewrite addnn -mul2n -expnS -mulSn -addnS expnD leq_mul2r ltn_ord orbT.
have F2 : (k + (2 ^ (m + n).+1 + j * 2 ^ n.+1) = 
              k + j * 2 ^ n.+1 + 2 ^ (m + n).+1)%N by rewrite addnAC addnA. 
have F3 : (k + j * 2 ^ n.+1 + 2 ^ (m + n).+1 + 2 ^ n =
           k + j * 2 ^ n.+1 + 2 ^ n + 2 ^ (m + n).+1)%N.
     by rewrite -!addnA [(_ + 2 ^ n)%N]addnC.
by rewrite !coef_poly F F1 F2 F3.
Qed.

Definition reverse_poly n (p : {poly R}) :=
  \poly_(i < 2 ^ n) p`_(rdigitn 2 n i).

Lemma size_reverse_poly  n p : (size (reverse_poly n p) <= 2 ^ n)%N.
Proof. by rewrite size_poly. Qed.

Lemma reverse_poly0 p : reverse_poly 0 p = (p`_0)%:P.
Proof. by apply/polyP => [] [|i]; rewrite coef_poly coefC. Qed.

Lemma reverse_polyS n p : 
  reverse_poly n.+1 p = 
  reverse_poly n (even_poly p) + reverse_poly n (odd_poly p) * 'X^(2 ^ n).
Proof.
rewrite /reverse_poly /even_poly /odd_poly.
under [X in X + _]eq_poly do rewrite coef_poly.
under [X in _ + X * _]eq_poly do rewrite coef_poly.
apply/polyP => i.
rewrite coefD coefMXn !coef_poly.
have [tnLi|iLtn] := leqP (2 ^ n) i.
  rewrite ltn_subLR // addnn -mul2n -expnS add0r.
  case: leqP => [//|iLtSn].
  suff Hf : (rdigitn 2 n.+1 i) = (rdigitn 2 n (i - 2 ^ n)).*2.+1.
    case: leqP => [iLn|nLi]; last by rewrite Hf.
    suff/leq_sizeP-> : (size p <= rdigitn 2 n.+1 i)%N by [].
    rewrite Hf.
    by rewrite leq_half in iLn.
  rewrite !rdigitnE big_ord_recl /= subn0 muln1 /bump /= .
  rewrite {1}/digitn -{1}(subnK tnLi).
  rewrite divnDr ?dvdnn // divnn expn_gt0 /= divn_small ?add1n; last first.
    by rewrite ltn_subLR // addnn -mul2n -expnS.
  under eq_bigr do rewrite add1n; congr (_.+1).
  under eq_bigr do rewrite expnS mulnCA.
  rewrite -big_distrr /= mul2n; congr (_.*2).
  apply: eq_bigr => j _; congr (_ * _)%N.
  have ->: (n.-1 - j = n - j.+1)%N.
    rewrite subnS.
    by case: (n) j => //= n1 j; rewrite subSn // -ltnS.
  rewrite /digitn -{1}(subnK tnLi) -[X in (_ + 2 ^ X)%N](subnK (ltn_ord j)).
  rewrite expnD mulnC divnDMl ?expn_gt0 //.
  by rewrite -modnDm // expnS modnMr addn0 modn_mod.
rewrite addr0 ifT; last by rewrite (leq_trans iLtn) // leq_exp2l.
suff Hf : (rdigitn 2 n.+1 i) = (rdigitn 2 n i).*2.
  case: leqP => [iLn|nLi]; last by rewrite Hf.
  suff/leq_sizeP-> : (size p <= rdigitn 2 n.+1 i)%N by [].
  rewrite leq_uphalf_double in iLn.
  by rewrite (leq_trans iLn) // Hf.
rewrite !rdigitnE big_ord_recl /= subn0 muln1 /bump /= .
rewrite {1}/digitn divn_small // add0n.
under eq_bigr do rewrite add1n expnS mulnCA.
rewrite -big_distrr /= mul2n; congr (_.*2).
apply: eq_bigr => j _; congr (_ _ _ * _)%N.
rewrite subnS.
by case: (n) j => //= n1 j; rewrite subSn // -ltnS.
Qed.


Fixpoint invariant_fft1 n m w p q :=
  if n is n1.+1 then 
  invariant_fft1 n1 m w (even_poly p) (left_poly (2 ^ (m + n1)) q) /\ 
  invariant_fft1 n1 m w (odd_poly p) (right_poly (2 ^ (m + n1)) q) 
  else q = fft1 m w p.

Lemma invariantS_fft1 n m w p q :
  invariant_fft1 n.+1 m w p q <->
  invariant_fft1 n m w (even_poly p) (left_poly (2 ^ (m + n)) q) /\ 
  invariant_fft1 n m w (odd_poly p) (right_poly (2 ^ (m + n)) q).
Proof. by []. Qed.

Lemma invariant_fft1_reverse_poly p n w :
  (size p <= 2 ^ n)%N -> invariant_fft1 n 0 w p (reverse_poly n p).
Proof.
elim: n p => /= [p spL1|n IH p spLb].
  by rewrite reverse_poly0 -poly_size1.
split.
  rewrite /left_poly reverse_polyS poly_def.
  under eq_bigr do rewrite coefD coefMXn ifT // addr0.
  rewrite -poly_def.
  have -> : \poly_(i < 2 ^ n) (reverse_poly n (even_poly p))`_i = 
            \poly_(i < size (reverse_poly n (even_poly p)))
                       (reverse_poly n (even_poly p))`_i.
    apply/polyP => i; rewrite coef_poly [RHS]coef_poly.
    case: leqP => [n2Li|iLn2].
      by rewrite ifN // -leqNgt (leq_trans _ n2Li) // size_reverse_poly.
    case: leqP => [epLi|iLep] => //.
    by suff /leq_sizeP-> : (size (reverse_poly n (even_poly p)) <= i)%N by [].
  rewrite coefK.
  apply: IH.
  by rewrite size_even_poly_exp2n.
rewrite /right_poly reverse_polyS poly_def.
under eq_bigr do rewrite coefD coefMXn ltnNge leq_addl /= addnK scalerDl.
rewrite big_split /= big1 ?add0r => [|i _]; last first.
  suff /leq_sizeP-> : (size (reverse_poly n (even_poly p)) <= i + 2 ^ n)%N.
  - by rewrite scale0r.
  - by [].
  by apply: leq_trans (size_reverse_poly _ _) (leq_addl _ _).
rewrite -poly_def.
have -> : \poly_(i < 2 ^ n) (reverse_poly n (odd_poly p))`_i = 
          \poly_(i < size (reverse_poly n (odd_poly p)))
                      (reverse_poly n (odd_poly p))`_i.
  apply/polyP => i; rewrite coef_poly [RHS]coef_poly.
  case: leqP => [n2Li|iLn2].
    by rewrite ifN // -leqNgt (leq_trans _ n2Li) // size_reverse_poly.
  case: leqP => [epLi|iLep] => //.
  by suff /leq_sizeP-> : (size (reverse_poly n (odd_poly p)) <= i)%N by [].
rewrite coefK.
apply: IH.
by rewrite size_odd_poly_exp2n.
Qed.

Lemma poly1 (s : nat -> R) : \poly_(i < 1) s i = (s 0%N)%:P.
Proof. by apply/polyP => i; rewrite coef_poly coefC; case: i. Qed.

Lemma invariant_fft1_step m n w p p1 :
  (size p <= 2 ^ (m + n).+1)%N ->
  (size p1 <= 2 ^ (m + n).+1)%N ->
  invariant_fft1 m.+1 n (w * w) p p1 ->
  invariant_fft1 m n.+1 w p (step m n w p1).
Proof.
elim: m n w p p1; last first.
  move=> m IH n w p p1 Hsp Hsp1/invariantS_fft1[H2 H3].
  apply/invariantS_fft1; split.
    rewrite [(_ + m)%N]addnC addnS left_step //.
    apply: IH => //.
    - by apply: size_even_poly_exp2n.
    - by rewrite size_poly.
    by rewrite [(m + _)%N]addnC -addnS.
  rewrite addnC addnS right_step //.
  apply: IH => //.
  - by apply: size_odd_poly_exp2n.
  - by rewrite size_poly.
  by rewrite [(m + _)%N]addnC -addnS.
move=> n p w p1; rewrite add0n => Hp Hp1 [H1 H2].
rewrite /= -H1 -H2.
rewrite /step big_ord1 mul0n !addn0.
apply: eq_bigr => /= i _.
by rewrite !coef_poly !addn0.
Qed.

Fixpoint istep_aux m n w p :=
  if m is m1.+1 then istep_aux m1 n.+1 w (step m1 n (w ^+ (2 ^ m1)) p) else p.

Definition istep n w p := istep_aux n 0 w (reverse_poly n p).

Lemma istep_fft1 n p w : (size p <= 2 ^ n)%N -> istep n w p = fft1 n w p.
Proof.
move=> Hs.
suff /(_ n 0%N): forall m1 n1 (p1 q1 : {poly R}), 
    (size p1 <= 2 ^ (m1 + n1))%N ->
    (size q1 <= 2 ^ (m1 + n1))%N ->
    invariant_fft1 m1 n1 (w ^+ (2 ^ m1)) p1 q1 -> 
    invariant_fft1 0 (m1 + n1) w p1 (istep_aux m1 n1 w q1).
  rewrite addn0 /=.
   apply => //; first by apply: size_reverse_poly.
  by apply: invariant_fft1_reverse_poly.
elim => [//| m1 IH] n1 p1 q1 Hs1 Hs2 H1.
rewrite /istep_aux -/istep_aux addSnnS.
apply: IH; first by rewrite addnS.
  rewrite addnS.
  by apply: size_step.
apply: invariant_fft1_step => //.
by rewrite -exprD addnn -mul2n -expnS.
Qed.

End FFT.

Section iFFT.

Local Open Scope ring_scope.

(* Arbitrary field                                                            *)
Variable F : fieldType.

Lemma unity_rootJ n (w : F) : n.-unity_root w^-1 = n.-unity_root w.
Proof.
apply/unity_rootP/unity_rootP; rewrite exprVn => /eqP.
  by rewrite invr_eq1 => /eqP.
by move=> H; apply/eqP; rewrite invr_eq1.
Qed. 

Lemma primJ n (w : F) : n.-primitive_root w -> n.-primitive_root (w^-1).
Proof.
move/andP=> [nP /forallP H]; apply/andP; split => //.
apply/forallP => i; apply/eqP; rewrite -(eqP (H i)).
by apply: unity_rootJ.
Qed.

Implicit Type p : {poly F}.

(* The inverse algorithm                                                      *)
Definition ifft n w p : {poly F} := (2^ n)%:R^-1%:P * (fft n w^-1 p).

(* Its correctness                                                            *)
Lemma fftK n (w : F) p : 
  2%:R != 0 :> F -> (size p <= 2 ^ n)%N -> (2 ^ n).-primitive_root w ->
  ifft n w (fft n w p) = p.
Proof.
move=> char2 sL wE.
have wE1 : w ^+ (2 ^ n) = 1 by apply: prim_expr_order.
have wNZ : w != 0.
  apply/eqP=> wZ; move/eqP: wE1.
  by rewrite eq_sym wZ expr0n expn_eq0 /= oner_eq0.
have wVE := primJ wE.
have wIE : w^-1 = w ^+ (2 ^ n).-1.
  by apply: (mulfI wNZ); rewrite mulfV // -exprS prednK ?expn_gt0.
rewrite /ifft !fftE ?size_poly //.
apply/polyP => i; rewrite coefCM coef_poly /=.
case: leqP => iL; first by rewrite nth_default ?mulr0 // (leq_trans _ iL).
rewrite horner_poly.
have pE : p = \poly_(j <  2 ^ n) p`_j.
  apply/polyP => j; rewrite coef_poly; case: leqP => // jL.
  by rewrite nth_default // (leq_trans _ jL).
under [X in _ * X = _]eq_bigr => j H do
  rewrite {1}pE horner_poly /= mulr_suml (bigD1 (Ordinal iL)) //=
          -!exprM mulnC -mulrA -exprMn ?(divff, expr1n, mulr1, addr0) //.
rewrite big_split /=.
rewrite sumr_const card_ord mulrDr.
rewrite -[X in _ * X + _ = _]mulr_natl mulrA mulVf ?mul1r; last first.
  by rewrite natrX expf_eq0 (negPf char2) andbF.
rewrite exchange_big /= big1 ?(mulr0, addr0) //= => k /eqP /val_eqP /= kDi.
under [LHS] eq_bigr do 
  rewrite -mulrA -exprM mulnC !exprM -exprMn wIE -!exprM -exprD.
set x := w ^+ _; rewrite -mulr_sumr.
suff xDone : x - 1 != 0.
  suff -> : (\sum_(i0 < 2 ^ n) x ^+ i0) = 0 by rewrite mulr0.
  apply: (mulfI xDone).
  by rewrite -subrX1 mulr0 -exprM mulnC exprM wE1 expr1n subrr.
(* There should be a simpler way to prove this *)
rewrite subr_eq0 -(prim_order_dvd wE).
case: {x}i iL kDi => [|i] iL xDi.
  rewrite muln0 addn0; apply/negP=> /dvdn_leq.
  by rewrite lt0n leqNgt ltn_ord => /(_ xDi).
rewrite -subn1 mulnBl mul1n mulnS addnC [(_ ^ _ + _)%N]addnC.
rewrite -addnBA ?(leq_trans _ iL) //.
rewrite /dvdn mulnC -addnA modnMDl; apply/negP => /dvdnP[q /eqP qE].
suff : (q < 2)%N.
  case: q qE => [|[|]] //.
    by rewrite mul0n; rewrite addn_eq0 subn_eq0 leqNgt iL.
  by rewrite mul1n -(eqn_add2r (i.+1)) addnAC subnK 
             ?(eqn_add2l, negPf xDi) // ltnW.
rewrite -(ltn_pmul2r (_ : 0 < 2 ^ n)%N) ?expn_gt0 //.
rewrite -(eqP qE) mul2n -addnn.
apply: (leq_trans (_ : _ <= 2 ^ n - i.+1 + 2 ^ n)%N).
  by rewrite ltn_add2l.
by rewrite leq_add2r leq_subr.
Qed.

End iFFT.