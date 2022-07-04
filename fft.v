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

(* Arbitrary ring *)
Variable R : ringType.

Implicit Type p : {poly R}.

Lemma leq_uphalf_double m n : (uphalf m <= n)%N = (m <= n.*2)%N.
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
have [pLi2|i2Lp] := leqP.
  have [//|sLi] := leqP.
  by have /leq_sizeP->// := pLi2.
by rewrite -ltn_double (leq_trans i2Lp).
Qed.

Lemma size_even_poly p : (size (even_poly p) <= uphalf (size p))%N.
Proof. by apply: size_poly. Qed.

Lemma coef_even_poly p i : (even_poly p)`_ i = p `_ i.*2.
Proof.
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)).
move: L; rewrite uphalf_half.
case: odd; first by rewrite !add1n ltn_double.
by rewrite leq_double.
Qed.

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

Lemma even_polyC (c : R) : even_poly c%:P = c%:P.
Proof.
by apply/polyP => i; rewrite coef_even_poly !coefC; case: i.
Qed.

(* Odd part of a polynomial                                                   *)

Definition odd_poly p : {poly R} := \poly_(i < uphalf (size p)) p`_i.*2.+1.

Lemma size_odd_poly p : (size (odd_poly p) <= uphalf (size p))%N.
Proof. by apply: size_poly. Qed.

Lemma coef_odd_poly p i : (odd_poly p)`_ i = p `_ i.*2.+1.
Proof.
rewrite coef_poly; case: leqP => L //.
rewrite nth_default // -(odd_double_half (size p)).
move: L; rewrite uphalf_half.
case: odd; first by rewrite !add1n ltnS leq_double => /ltnW.
by rewrite -leq_double => /leq_trans->.
Qed.

Lemma odd_polyC (c : R) : odd_poly c%:P = 0.
Proof.
by apply/polyP => i; rewrite coef_odd_poly !coefC; case: i.
Qed.

Lemma odd_polyE s (p : {poly R}) :
  (size p <= s.*2)%N -> odd_poly p = \poly_(i < s) p`_i.*2.+1.
Proof.
move=> pLs2; apply/polyP => i.
rewrite !coef_poly ltnNge leq_uphalf_double -ltnNge.
have [pLi2|i2Lp] := leqP.
  have [//|sLi] := leqP.
  by have /leq_sizeP->// := pLi2.
by rewrite -ltn_double (leq_trans i2Lp).
Qed.

Lemma odd_polyD p q : odd_poly (p + q) = odd_poly p + odd_poly q.
Proof.
apply/polyP => i.
pose s := uphalf (maxn (size p) (size q)).
have pLs2 : (size p <= s.*2)%N.
  by rewrite -leq_uphalf_double uphalf_leq // leq_maxl.
have qLs2 : (size q <= s.*2)%N.
  by rewrite -leq_uphalf_double uphalf_leq // leq_maxr.
have pqLs2 : (size (p + q)%R <= s.*2)%N.
  by rewrite (leq_trans (size_add _ _)) // -leq_uphalf_double.
rewrite (odd_polyE pqLs2) (odd_polyE pLs2) (odd_polyE qLs2).
by rewrite coefD !coef_poly; case: leqP; [rewrite add0r | rewrite coefD].
Qed.

Lemma odd_polyX p : odd_poly (p * 'X) = even_poly p.
Proof.
have [->|/eqP p_neq0] := p =P 0; first by rewrite mul0r even_polyC odd_polyC.
apply/polyP => i.
have pLpX : (size p <= (uphalf (size (p * 'X)%R)).*2)%N.
  by rewrite -leq_uphalf_double uphalf_leq // size_mulX.
by rewrite /odd_poly (even_polyE pLpX) !coef_poly coefMX.
Qed.

Lemma even_polyX p : even_poly (p * 'X) = odd_poly p * 'X.
Proof.
have [->|/eqP p_neq0] := p =P 0.
  by rewrite mul0r even_polyC odd_polyC mul0r.
apply/polyP => i.
have pLpX : (size p < (uphalf (size (p * 'X)%R)).*2)%N.
  by rewrite -leq_uphalf_double uphalf_leq // size_mulX.
rewrite (odd_polyE (ltnW pLpX)) coefMX !coef_poly coefMX.
case: i => [|i] /=; first by rewrite if_same.
have [pXLi|] := leqP (uphalf (size (p * 'X)%R)) i.
  by rewrite ifN // -leqNgt (leq_trans pXLi).
rewrite leq_eqVlt => /orP[/eqP E|->//].
rewrite E ltnn.
suff /leq_sizeP-> : (size p <= i.*2.+1)%N by [].
by rewrite -ltnS -doubleS E.
Qed.

(* Auxillary lemmas for _ \Po X'X^n                                           *)
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
Fixpoint fft n w p : {poly R} := 
  if n is n1.+1 then
  let ev := fft n1 (w * w) (even_poly p) in
  let ov := fft n1 (w * w) (odd_poly p) in
  \poly_(i < 2 ^ n)
    let j := (i %% 2 ^  n1)%N in ev`_j + ov`_ j * w ^+ i 
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
by rewrite -half_exp2n uphalf_leq.
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
  (size p <= 2 ^ n)%N -> ((0 < n)%N -> w ^+ (2 ^ n.-1) = -1) ->
  fft n w p = \poly_(i < 2 ^ n) p.[w ^+ i].
Proof.
elim: n w p => [/= w p sL _ |n IH w p sL wE /=].
  by rewrite poly_def big_ord1 expr0 [p]poly_size1 // !hornerE alg_polyC coefC.
apply/polyP => i; rewrite !coef_poly; case: leqP => // iL.
have imL : (i %% 2 ^ n < 2 ^ n)%N by apply/ltn_pmod/expn_gt0.
have n2P : (0 < 2 ^ n.+1)%N by rewrite expn_gt0.
have wwE : (0 < n)%N -> (w * w) ^+ (2 ^ n.-1) = -1.
  move=> nP.
  by rewrite -expr2 -exprM -expnS prednK // wE.
rewrite !IH ?coef_poly ?imL ?size_even_poly_exp2n ?size_odd_poly_exp2n //.
rewrite [p in RHS]odd_even_polyE.
rewrite !(hornerD, horner_comp_polyXn, hornerMX, hornerX).
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
by rewrite expnS mulnC exprM wE // expr2 mulrN1 opprK.
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

Lemma fft1E n (w : R) p : 
  (size p <= 2 ^ n)%N -> ((0 < n)%N -> w ^+ (2 ^ n.-1) = -1) -> 
  fft n w p = fft1 n w p.
Proof.
elim: n w p => [// |n IH w p sL wE /=].
have wwE : (0 < n)%N -> (w * w) ^+ (2 ^ n.-1) = -1.
  by move=> n_gt0; rewrite -expr2 -exprM -expnS prednK // wE.
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
    rewrite modnDr modn_small // exprD wE // mulrN1 mulrN; rewrite -big_nat /=.
rewrite big_mkord; apply: eq_bigr => i _.
by rewrite !IH ?size_even_poly_exp2n ?size_odd_poly_exp2n.
Qed.

(* The algorithm with explicitely the butterfly                               *)
Fixpoint fft2 n w p : {poly R} := 
  if n is n1.+1 then
  let ev := fft2 n1 (w * w) (even_poly p) in
  let ov := fft2 n1 (w * w) (odd_poly p) in
  \sum_(j < 2 ^ n1)
    ((ev`_j + ov`_ j * w ^+ j) *: 'X^j +
     (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + 2 ^ n1)) 
  else (p`_0)%:P.

Lemma fft2S n w (p : {poly R}) :
  fft2 n.+1 w p =  
  let ev := fft2 n (w * w) (even_poly p) in
  let ov := fft2 n (w * w) (odd_poly p) in
  \sum_(j < 2 ^ n)
    ((ev`_j + ov`_ j * w ^+ j) *: 'X^j +
     (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + 2 ^ n)).
Proof. by []. Qed.


Lemma fft2E n (w : R) p : 
  (size p <= 2 ^ n)%N -> ((0 < n)%N -> w ^+ (2 ^ n.-1) = -1) -> 
  fft2 n w p = fft1 n w p.
Proof.
elim: n w p => [// |/= n IH w p sL wE].
have wwE : (0 < n)%N -> (w * w) ^+ (2 ^ n.-1) = -1.
  by move=> n_gt0; rewrite -expr2 -exprM -expnS prednK // wE.
apply: eq_bigr => i _.
by rewrite !IH ?size_even_poly_exp2n ?size_odd_poly_exp2n.
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
    rewrite leq_uphalf_double in iLn.
    by rewrite (leq_trans iLn) // Hf.
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

End FFT.

Section iFFT.

Local Open Scope ring_scope.

(* Arbitrary field                                                            *)
Variable F : fieldType.

Implicit Type p : {poly F}.

(* The inverse algorithm                                                      *)
Definition ifft n w p : {poly F} := (2^ n)%:R^-1%:P * (fft n w^-1 p).

(* Its correctness                                                            *)
Lemma fftK n (w : F) p : 
  2%:R != 0 :> F -> (size p <= 2 ^ n)%N -> (2 ^ n).-primitive_root w ->
  ifft n w (fft n w p) = p.
Proof.
move=> char2 sL wP.
have wE1 : w ^+ (2 ^ n) = 1 by apply: prim_expr_order.
have wE : (0 < n)%N -> w ^+ (2 ^ n.-1) = -1.
  case: n {sL}wE1 wP => // n wE1 wP.
  have /eqP := wE1; rewrite expnS mulnC exprM -subr_eq0 subr_sqr_1.
  rewrite mulf_eq0 => /orP[]; last first.
    by rewrite -[1]opprK subr_eq0 opprK => /eqP.
  by rewrite subr_eq0 -(prim_order_dvd wP) dvdn_Pexp2l // ltnn.
have wNZ : w != 0.
  apply/eqP=> wZ; move/eqP: wE1.
  by rewrite eq_sym wZ expr0n expn_eq0 /= oner_eq0.
have wVE : (0 < n)%N -> w^-1 ^+ (2 ^ n.-1) = -1.
  move=> n_gt0; by rewrite exprVn wE // invrN invr1.
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
rewrite subr_eq0 -(prim_order_dvd wP).
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