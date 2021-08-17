From mathcomp Require Import all_ssreflect all_algebra.

(******************************************************************************)
(*                                                                            *)
(*             Proof of the Fast Fourier Transform                            *)
(*              inspired by a paper by V. Capretta                            *)
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

Lemma uphalf_leq m n : (m <= n -> uphalf m <= uphalf n)%N.
Proof.
move/subnK <-; rewrite !uphalf_half oddD halfD !addnA.
by do 2 case: odd => //=; apply: leq_addl.
Qed.

(* Odd part of a polynomial *)
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

(* Auxillary lemmas for _ \Po X'X^n *)
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

(* The algorithm *)
Fixpoint fft n w p : {poly R} := 
  if n is n1.+1 then
  let ev := fft n1 (w * w) (even_poly p) in
  let ov := fft n1 (w * w) (odd_poly p) in
  \poly_(i < 2 ^ n1.+2)
    let j := (i %% 2^n1.+1)%N in ev`_j + ov`_ j * w ^+ i 
  else \poly_(i < 2) p.[w ^+ i].

(* Its correctness *)
Lemma fftE n (w : R) p : 
  (size p <= 2 ^ n.+1)%N -> w ^+ (2 ^ n) = -1 ->
  (fft n w p) = \poly_(i < 2 ^ n.+1) p.[w ^+ i].
Proof.
elim: n w p => [// |n IH w p sL wE /=].
apply/polyP => i; rewrite !coef_poly; case: leqP => // iL.
have imL : (i %% 2 ^ n.+1 < 2 ^ n.+1)%N by apply/ltn_pmod/expn_gt0.
have n2P : (0 < 2 ^ n.+2)%N by rewrite expn_gt0.
have n2P_halfE : (2 ^ n.+1 = uphalf (2 ^ n.+2))%N.
  by rewrite uphalf_half !expnS !mul2n doubleK odd_double add0n.
rewrite !IH ?coef_poly ?imL //.
- rewrite [p in RHS]odd_even_polyE.
  rewrite !(hornerD, horner_comp_polyXn, hornerMX, hornerX).
  suff -> : (w * w) ^+ (i %% 2 ^ n.+1) = w ^+ i * w ^+ i by [].
  rewrite -!expr2 -!exprM.
  have [iLm|mLi] := leqP (2 ^ n.+1) i; last by rewrite modn_small // mulnC.
  have -> : (i %% 2 ^ n.+1 = i - 2 ^ n.+1)%N.
    rewrite -[in LHS](subnK iLm) modnDr modn_small //.
    by rewrite ltn_psubLR ?expn_gt0 // addnn -mul2n -expnS.
  have -> : (i * 2 = 2 * (i - 2 ^ n.+1) + 2 ^ n.+2)%N.
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

Section iFFT.

Local Open Scope ring_scope.

(* Arbitrary field *)
Variable F : fieldType.

Implicit Type p : {poly F}.

(* The inverse algorithm  *)
Definition ifft n w p : {poly F} := (2^ n.+1)%:R^-1%:P * (fft n w^-1 p).

(* Its correctness *)
Lemma fftK n (w : F) p : 
  2%:R != 0 :> F -> (size p <= 2 ^ n.+1)%N -> (2 ^ n.+1).-primitive_root w ->
  ifft n w (fft n w p) = p.
Proof.
move=> char2 sL wP.
have wE1 : w^+ (2 ^ n.+1) = 1 by apply: prim_expr_order.
have wE : w ^+ (2 ^ n) = -1.
  have /eqP := wE1; rewrite expnS mulnC exprM -subr_eq0 subr_sqr_1.
  rewrite mulf_eq0 => /orP[]; last first.
    by rewrite -[1]opprK subr_eq0 opprK => /eqP.
  by rewrite subr_eq0 -(prim_order_dvd wP) dvdn_Pexp2l // ltnn.
have wNZ : w != 0.
  apply/eqP=> wZ; move/eqP: wE.
  by rewrite eq_sym wZ expr0n expn_eq0 /= oppr_eq0 oner_eq0.
have wVE : w^-1 ^+ (2 ^ n) = -1 by rewrite exprVn wE invrN invr1.
have wIE : w^-1 = w^(2^n.+1).-1.
  by apply: (mulfI wNZ); rewrite mulfV // -exprS prednK ?expn_gt0.
rewrite /ifft !fftE ?size_poly //.
apply/polyP => i; rewrite coefCM coef_poly /=.
case: leqP => iL; first by rewrite nth_default ?mulr0 // (leq_trans _ iL).
rewrite horner_poly.
have pE : p = \poly_(j <  2 ^ n.+1) p`_j.
  apply/polyP => j; rewrite coef_poly; case: leqP => // jL.
  by rewrite nth_default // (leq_trans _ jL).
under [X in _ * X = _]eq_bigr => j H do
  rewrite {1}pE horner_poly /= mulr_suml (bigD1 (Ordinal iL)) //=
          -!exprM mulnC -mulrA -exprMn ?(divff, expr1n, mulr1, addr0) //.
rewrite big_split /=.
rewrite sumr_const card_ord mulrDr.
rewrite -[X in _ * X + _ = _]mulr_natl mulrA mulVf ?mul1r; last first.
  by rewrite natrX expf_eq0.
rewrite exchange_big /= big1 ?(mulr0, addr0) //= => k /eqP /val_eqP /= kDi.
under [LHS] eq_bigr do 
  rewrite -mulrA -exprM mulnC !exprM -exprMn wIE -!exprM -exprD.
set x := w ^+ _; rewrite -mulr_sumr.
suff xDone : x - 1 != 0.
  suff -> : (\sum_(i0 < 2 ^ n.+1) x ^+ i0) = 0 by rewrite mulr0.
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
rewrite -(ltn_pmul2r (_ : 0 < 2 ^ n.+1)%N) ?expn_gt0 //.
rewrite -(eqP qE) mul2n -addnn.
apply: (leq_trans (_ : _ <= 2 ^ n.+1 - i.+1 + 2 ^ n.+1 )%N).
  by rewrite ltn_add2l.
by rewrite leq_add2r leq_subr.
Qed.

End iFFT.