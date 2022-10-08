From mathcomp Require Import all_ssreflect all_algebra ssrnum.
Require Import digitn splitpoly.

(******************************************************************************)
(*                                                                            *)
(*             Proof of the Fast Fourier Transform                            *)
(*              inspired by a paper by V. Capretta                            *)
(******************************************************************************)

(******************************************************************************)
(*                                                                            *)
(* fft n w p    = naive algorithn that returns the polynomial                 *)
(*                p[1] + p[w] * 'X + ... + p[w^(2^n - 1)] * 'X^(2^n - 1)      *)
(* fft1 n w p   = returns the polynomial                                      *)
(*                p[1] + p[w] * 'X + ... + p[w^(2^n - 1)] * 'X^(2^n - 1)      *)
(* istep n w p  = naive iterative algorithn that returns the polynomial       *)
(*                p[1] + p[w] * 'X + ... + p[w^(2^n - 1)] * 'X^(2^n - 1)      *)
(* istep1 n w p = iterative algorithm that returns the polynomial             *)
(*                p[1] + p[w] * 'X + ... + p[w^(2^n - 1)] * 'X^(2^n - 1)      *)
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
  (2 ^ n.+1).-primitive_root w -> (2 ^ n).-primitive_root (w ^+ 2).
Proof.
move=> Hp.
have -> : (2 ^ n = 2 ^ n.+1 %/ (gcdn 2 (2 ^ n.+1)))%N.
  by rewrite -(expn_min _ 1) (minn_idPl _) // expnS mulKn.
by rewrite exp_prim_root.
Qed.
 
(* The recursive algorithm                                                    *)
Fixpoint fft (n : nat) (w : R) (p : {poly R}) : {poly R} := 
  if n is n1.+1 then
    let ev := fft n1 (w ^+ 2) (even_poly p) in
    let ov := fft n1 (w ^+ 2) (odd_poly p) in
    \poly_(i < 2 ^ n1.+1) let j := (i %% 2 ^ n1)%N in ev`_j + ov`_ j * w ^+ i 
  else (p`_0)%:P.

Lemma size_fft n w p : (size (fft n w p) <= 2 ^ n)%N.
Proof. 
by case: n => [|n] /=; [rewrite size_polyC; case: eqP | apply: size_poly].
Qed.

Fact size_odd_poly_exp2n n p : 
  (size p <= 2 ^ n.+1 -> size (odd_poly p) <= 2 ^ n)%N.
Proof.
move=> Hs; apply: leq_trans (size_odd_poly _) _.
by rewrite leq_half_double (leq_trans Hs) // -mul2n -expnS.
Qed.

Fact half_exp2n n : (uphalf (2 ^ n.+1) = 2 ^ n)%N.
Proof.
by rewrite uphalf_half !expnS !mul2n doubleK odd_double add0n.
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
suff -> : (w ^+ 2) ^+ (i %% 2 ^ n) = w ^+ i * w ^+ i by [].
rewrite -!expr2 -!exprM.
have [iLm|mLi] := leqP (2 ^ n) i; last by rewrite modn_small // mulnC.
have -> : (i %% 2 ^ n = i - 2 ^ n)%N.
  rewrite -[in LHS](subnK iLm) modnDr modn_small //.
  by rewrite ltn_psubLR ?expn_gt0 // addnn -mul2n -expnS.
have -> : (i * 2 = 2 * (i - 2 ^ n) + 2 ^ n.+1)%N.
  by rewrite mulnC mulnBr -expnS subnK // expnS leq_mul2l.
rewrite exprD.
suff -> : w ^+ (2 ^ n.+1) = 1 by rewrite mulr1.
by rewrite expnS exprM (prim_expr_order wwE).
Qed.

(* The algorithm with explicitely the butterfly                               *)
Fixpoint fft1 n w p : {poly R} := 
  if n is n1.+1 then
  let ev := fft1 n1 (w ^+ 2) (even_poly p) in
  let ov := fft1 n1 (w ^+ 2) (odd_poly p) in
  \sum_(j < 2 ^ n1)
    ((ev`_j + ov`_ j * w ^+ j) *: 'X^j +
     (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + 2 ^ n1)) 
  else (p`_0)%:P.

Lemma fft1S n w p : 
  fft1 n.+1 w p = 
  let ev := fft1 n (w ^+ 2) (even_poly p) in
  let ov := fft1 n (w ^+ 2) (odd_poly p) in
  \sum_(j < 2 ^ n)
    ((ev`_j + ov`_ j * w ^+ j) *: 'X^j +
     (ev`_j - ov`_ j * w ^+ j) *: 'X^(j + 2 ^ n)).
Proof. by []. Qed. 

Lemma fft1E n (w : R) p : (2 ^ n).-primitive_root w -> fft1 n w p = fft n w p.
Proof.
elim: n w p => [// |n IH w p wE /=].
have wwE := prim_sqr wE.
rewrite poly_def -(@big_mkord _ (0 : {poly R}) +%R (2 ^ n.+1) xpredT
   (fun (i : nat) => 
      ((fft n (w ^+ 2) (even_poly p))`_(i %% 2 ^ n) +
    (fft n (w ^+ 2) (odd_poly p))`_(i %% 2 ^ n) * w ^+ i) *: 'X^i)).
have F : (2 ^ n <= 2 ^ n.+1)%N by rewrite leq_exp2l.
apply: sym_equal.
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

Fact bound_step m n i j : 
  (i < 2 ^ m -> j < 2 ^ n -> 
   j + i * 2 ^ n.+1 + 2 ^ n < 2 ^ (m + n).+1)%N.
Proof.
move=> Hi Hj.
rewrite addnAC.
apply: leq_trans (_ : 2 ^ n + 2 ^ n + i *2 ^ n.+1 <= _ )%N.
  by rewrite -!addnA ltn_add2r.
by rewrite addnn -mul2n -expnS -mulSn -addnS expnD leq_mul2r expn_eq0 /=.
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
  apply: leq_trans (bound_step (ltn_ord i) (ltn_ord j)).
  by rewrite ltnS leq_addr.
by apply: bound_step.
Qed.

Lemma take_step m n w (p : {poly R}) :
  (size p <= 2 ^ (m + n).+2)%N ->
  take_poly (2 ^ (m + n).+1) (step m.+1 n w p) =
  step m n w (take_poly (2 ^ (m + n).+1) p).
Proof.
move=> pLmn; rewrite stepE.
apply/polyP=> i; rewrite coef_take_poly.
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
  apply: leq_trans (bound_step (ltn_ord j) (ltn_ord k)).
  by rewrite ltnS leq_addr.
have F1 : (k + j * 2 ^ n.+1 + 2 ^ n < 2 ^ (m + n).+1)%N.
  by apply: bound_step.
by rewrite !coef_poly F F1.
Qed.

Lemma drop_step m n w (p : {poly R}) :
  (size p <= 2 ^ (m + n).+2)%N ->
  drop_poly (2 ^ (m + n).+1) (step m.+1 n w p) =
  step m n w (drop_poly (2 ^ (m + n).+1) p).
Proof.
move=> pLmn.
apply/polyP=> i; rewrite coef_drop_poly.
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
have F : (k + j * 2 ^ n.+1 + 2 ^ (m + n).+1 = 
          k + (2 ^ (m + n).+1 + j * 2 ^ n.+1))%N.
  by rewrite addnAC addnA.
have F1 : 
  ((k + j * 2 ^ n.+1 + 2 ^ n + 2 ^ (m + n).+1) =
    (k + (2 ^ (m + n).+1 + j * 2 ^ n.+1) + 2 ^ n))%N.
  by rewrite !addnA [(k + _ + _)%N in RHS]addnAC [(_ + 2 ^ n)%N in RHS]addnAC. 
by rewrite !(coef_drop_poly, coef_poly) ltn_ord // F F1.
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
    by rewrite leq_half_double in iLn.
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
  invariant_fft1 n1 m w (even_poly p) (take_poly (2 ^ (m + n1)) q) /\ 
  invariant_fft1 n1 m w (odd_poly p) (drop_poly (2 ^ (m + n1)) q) 
  else q = fft1 m w p.

Lemma invariantS_fft1 n m w p q :
  invariant_fft1 n.+1 m w p q <->
  invariant_fft1 n m w (even_poly p) (take_poly (2 ^ (m + n)) q) /\ 
  invariant_fft1 n m w (odd_poly p) (drop_poly (2 ^ (m + n)) q).
Proof. by []. Qed.

Lemma invariant_fft1_reverse_poly p n w :
  (size p <= 2 ^ n)%N -> invariant_fft1 n 0 w p (reverse_poly n p).
Proof.
elim: n p => /= [p spL1|n IH p spLb].
  by rewrite reverse_poly0 -poly_size1.
split.
  rewrite /take_poly reverse_polyS poly_def.
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
rewrite add0n.
have -> : drop_poly (2 ^ n) (reverse_poly n.+1 p) =
         \poly_(i < 2 ^ n) (reverse_poly n.+1 p)`_(i + 2 ^ n).
  apply/polyP=> i; rewrite coef_drop_poly coef_poly.
  case: leqP => // nLn; rewrite nth_default //.
  apply: leq_trans (size_reverse_poly _ _) _.
  by rewrite expnS mul2n -addnn leq_add2r.
rewrite reverse_polyS poly_def.
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
  invariant_fft1 m.+1 n (w ^+ 2) p p1 ->
  invariant_fft1 m n.+1 w p (step m n w p1).
Proof.
elim: m n w p p1; last first.
  move=> m IH n w p p1 Hsp Hsp1/invariantS_fft1[H2 H3].
  apply/invariantS_fft1; split.
    rewrite [(_ + m)%N]addnC addnS take_step //.
    apply: IH => //.
    - by apply: size_even_poly_exp2n.
    - by rewrite size_poly.
    by rewrite [(m + _)%N]addnC -addnS.
  rewrite addnC addnS drop_step //.
  apply: IH => //.
  - by apply: size_odd_poly_exp2n.
  - apply: leq_trans (size_drop_poly _ _) _.
    by rewrite leq_subLR addnn -mul2n -expnS.
  by rewrite [(m + _)%N]addnC -addnS.
move=> n p w p1; rewrite add0n => Hp Hp1 [H1 H2].
rewrite /= -H1 -H2.
rewrite /step big_ord1 mul0n !addn0.
apply: eq_bigr => /= i _.
by rewrite !coef_drop_poly !coef_poly !addn0 ltn_ord.
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
by rewrite -exprM mulnC -expnS.
Qed.

(* Refined version of step 1                                                  *)
Definition step1 m n w (p : {poly R}) :=
  \poly_(i < 2 ^ (m + n).+1)
    let j := (i %% 2 ^ n.+1)%N in
    if (j < 2 ^ n)%N then 
      p`_i + p`_(i + 2 ^ n) * w ^+ j
    else 
      p`_(i - 2 ^ n) - p`_i * w ^+ (j - 2 ^ n).

Lemma step1E m n w p : step1 m n w p = step m n w p.
Proof.
apply/polyP => i.
rewrite coef_poly coef_sum.
have [mnLi|iLmn] := leqP.
  rewrite big1 // => j _; rewrite coef_sum /=.
  rewrite big1 // => k _; rewrite !coef_poly !(coefD, coefZ, coefXn).
  rewrite !gtn_eqF ?mulr0 ?addr0 // (leq_trans _ mnLi) //.
    by apply: bound_step.
  apply: leq_trans (bound_step (ltn_ord j) (ltn_ord k)).
  by rewrite ltnS leq_addr.
set l := (i %/ 2 ^ n.+1)%N.
have l_ltn : (l < 2 ^ m)%N.
  by rewrite ltn_divLR ?expn_gt0 // -expnD addnS.
rewrite (bigD1 (Ordinal l_ltn)) //= [X in _ = _ + X]big1; last first.
  move=> i1 /eqP/val_eqP /= i1Dl.
  rewrite coef_sum big1 // => i2 _.
  rewrite coefD !coefZ !coefXn.
  case: (ltngtP i1 l) i1Dl => // i1Dl _.
    rewrite leq_divRL ?expn_gt0 // in i1Dl.
    rewrite !gtn_eqF ?mulr0 ?addr0 //; apply: leq_trans i1Dl.
      by rewrite addnAC mulSn -!addSn leq_add // expnS mul2n -addnn leq_add2r.
    rewrite mulSn -!addSn leq_add // (leq_trans (ltn_ord _)) //.
    by rewrite expnS mul2n -addnn leq_addr.
  rewrite ltn_divLR ?expn_gt0 // in i1Dl.
  rewrite !ltn_eqF ?mulr0 ?addr0 //; apply: leq_trans i1Dl _.
    by rewrite addnAC leq_addl.
  by rewrite leq_addl.
rewrite addr0.
have F : (i %% 2 ^ n.+1 + l * 2 ^ n.+1 = i)%N by rewrite addnC -divn_eq.
rewrite coef_sum.
case: leqP => H.
  have Fi : (2 ^ n <= i)%N by apply: leq_trans H (leq_mod _ _).
  have F1 : (i %% 2 ^ n.+1 - 2 ^ n < 2 ^ n)%N.
    by rewrite ltn_subLR // addnn -mul2n -expnS ltn_pmod ?expn_gt0.
  have F2 : ((i %% 2 ^ n.+1) %% 2 ^ n = i %% 2 ^ n.+1 - 2 ^ n)%N.
    by rewrite -[in LHS](subnK H) modnDr modn_small.
  rewrite (bigD1 (Ordinal F1)) //= ?big1.
    rewrite addr0 coefD !coefZ !coefXn.
    rewrite addnBAC // F subnK // eqxx mulr1 gtn_eqF; last first.
      by rewrite ltn_subLR // (ltn_add2r _ 0) expn_gt0.
    rewrite mulr0 add0r !coef_poly F1.
    by rewrite addnBAC // F subnK // eqxx mulr1 gtn_eqF.
  move=> i1 /eqP/val_eqP/= Hi1.
  rewrite !coef_poly ltn_ord coefD !coefZ !coefXn.
  rewrite -F addnAC !eqn_add2r gtn_eqF ?mulr0 ?add0r; last first.
    by apply: leq_trans H.
  by rewrite -(subnK H) eqn_add2r eq_sym (negPf Hi1) mulr0.
rewrite (bigD1 (Ordinal H)) //= ?big1.
  rewrite addr0 coefD !coefZ !coefXn F.
  rewrite eqxx mulr1 ltn_eqF ?mulr0 ?addr0 // ?(ltn_add2l _ 0) ?expn_gt0 //.
    by rewrite !coef_poly F H.
  by rewrite addnC (ltn_add2r _ 0) expn_gt0.
move=> i1 /eqP/val_eqP/= Hi1.
rewrite !coef_poly ltn_ord coefD !coefZ !coefXn.
rewrite -F eqn_add2r eq_sym (negPf Hi1) mulr0 add0r.
rewrite addnAC eqn_add2r ltn_eqF ?mulr0 //.
by apply: leq_trans H (leq_addl _ _).
Qed.    

Fixpoint istep1_aux m n w p :=
  if m is m1.+1 then istep1_aux m1 n.+1 w (step1 m1 n (w ^+ (2 ^ m1)) p) else p.

Definition istep1 n w p := istep1_aux n 0 w (reverse_poly n p).

Lemma istep1_fft1 n p w : (size p <= 2 ^ n)%N -> istep1 n w p = fft1 n w p.
Proof.
move=> Hs; rewrite -istep_fft1 // /istep1 /istep.
elim: n {Hs}(size_reverse_poly n p) 0%N w (reverse_poly _ _) => 
    //= n IH pLn n1 w p1.
rewrite step1E.
apply: IH.
by apply: size_reverse_poly.
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