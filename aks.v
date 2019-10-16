From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section AKS.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.

Definition introspective {R : ringType} n k (p : {poly R}) :=
  rmodp (p ^+ n) ('X^k - 1)  == rmodp (p \Po 'X^n) ('X^k - 1).

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").

Lemma fin_little_fermat (F : finFieldType) (n c : nat) :
  n \in [char F] -> c%:R ^+ n = c%:R :> F.
Proof.
move=> nC.
have Pp : prime n by apply: charf_prime nC.
have Cn : [char F].-nat n by rewrite pnatE.
elim: c => [|c IH]; first by rewrite -natrX exp0n ?prime_gt0.
by rewrite -addn1 natrD exprDn_char // IH -natrX exp1n.
Qed.

Lemma poly_geom (R : comRingType) n (p : {poly R}) : 
  p ^+ n.+1 - 1 = (p - 1) * \sum_(i < n.+1) p ^+ i.
Proof.
rewrite mulrBl mul1r {1}big_ord_recr big_ord_recl /=.
rewrite [_ + p^+_]addrC mulrDr -exprS expr0 addrAC opprD addrA mulr_sumr.
rewrite (eq_bigr (fun i : 'I_n => p * p ^+ i)) ?subrK // => i _.
by rewrite exprS.
Qed.

Lemma dvdp_geom (R : comRingType) n (p : {poly R}) : p - 1 \is monic -> rdvdp (p - 1) (p ^+ n.+1 - 1).
Proof. move=> pM; rewrite poly_geom mulrC rdvdp_mull //. Qed.

(* 98 *)
Lemma introspec_char (F : finFieldType) (k n c : nat) :
  n \in [char F] -> n ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> nC; apply/eqP; congr (rmodp _  _).
have Pp : prime n by apply: charf_prime nC.
have Cn : [char F].-nat n by rewrite pnatE.
rewrite comp_polyD comp_polyC comp_polyX.
rewrite exprDn_char; first by rewrite -polyC_exp fin_little_fermat.
by rewrite pnatE // (rmorph_char (polyC_rmorphism _)).
Qed.

Lemma comp_polyX (R : comRingType) n (p q : {poly R}) : 
  (p \Po q) ^+ n = (p ^+ n) \Po q.
Proof.
elim: n => [|n IH]; first by rewrite !expr0 comp_polyC.
by rewrite !exprS IH comp_polyM.
Qed.

Lemma comp_polyXn (R : ringType) n (p : {poly R}) : 
  'X^n \Po p = p ^+ n.
Proof.
rewrite comp_polyE size_polyXn.
rewrite (bigD1 ord_max) //= coefXn eqxx scale1r big1 ?addr0 //.
by move=> i /eqP/val_eqP /= iDn; rewrite coefXn (negPf iDn) scale0r.
Qed.

Lemma modp_exp (R : comRingType) n (p d : {poly R}) :
  d \is monic -> rmodp ((rmodp p d) ^+ n) d = (rmodp (p ^+ n) d).
Proof.
move=> lCd; elim: n => [|n IH]; first by rewrite !expr0.
rewrite !exprS.
by rewrite -rmodp_mulmr // IH rmodp_mulmr // mulrC rmodp_mulmr // mulrC.
Qed.

Lemma rmodp_sub (R : ringType) (d p q : {poly R}) : 
  d \is monic -> rmodp (p - q) d = rmodp p d - rmodp q d.
Proof.
move=> dM.
rewrite {1}(rdivp_eq dM p) {1}(rdivp_eq dM q).
rewrite opprD addrCA 2!addrA -mulNr -mulrDl (addrC (- rdivp q d)) -addrA.
rewrite rmodp_addl_mul_small //; apply: (leq_ltn_trans (size_add _ _)).
by rewrite gtn_max size_opp !ltn_rmodp // monic_neq0.
Qed.

Lemma rdvdp_trans (R : ringType) (p q r : {poly R}) : 
  p \is monic -> q \is monic -> rdvdp p q -> rdvdp q r -> rdvdp p r.
Proof.
move=> pM qM /rdvdpP => /(_ pM) [qq1 qq1E] /rdvdpP => /(_ qM) [qq2 qq2E].
by apply/rdvdpP => //; exists (qq2 * qq1); rewrite qq2E qq1E mulrA.
Qed.

Lemma coef_comp_poly {R : ringType} (p q : {poly R}) n :
  (p \Po q)`_n = \sum_(i < size p) p`_i * (q ^+ i)`_n.
Proof. by rewrite comp_polyE coef_sum; apply: eq_bigr => i; rewrite coefZ. Qed.

Lemma size_exp_monic (R : ringType) (p: {poly R}) n :
  p \is monic -> size (p ^+ n) = ((size p).-1 * n).+1.
Proof.
move=> pM; elim: n => // [|n IH]; first by rewrite !expr0 muln0 size_polyC oner_eq0.
rewrite exprS size_proper_mul ?IH; last first.
  by rewrite (eqP pM) (eqP (monic_exp n pM)) mul1r oner_neq0.
have : (0 < size p)%nat.
  by have := monic_neq0 pM; rewrite -size_poly_eq0; case: size.
by case: size => // k _; rewrite addSn addnS -mulnS.
Qed.

Lemma monic_comp_poly (R : ringType) (p q : {poly R}) :
  p \is monic -> q \is monic -> q != 1 -> p \Po q \is monic.
Proof.
move=> pM qM qD1.
have cp0q : (p \Po q)`_((size p).-1 * (size q).-1) == 1.
  rewrite comp_polyE coef_sum.
  have := (pM); rewrite monicE /lead_coef.
  have : (0 < size p)%nat.
    by have := monic_neq0 pM; rewrite -size_poly_eq0; case: size.
  case: size => //= k _ pkE.
  rewrite big_ord_recr /= (eqP pkE) scale1r big1 ?add0r.
  by have := monic_exp k qM; rewrite qualifE /lead_coef size_exp_monic //= mulnC.
  move=> i _; rewrite coefZ [_`_(k * _)]nth_default ?mulr0 //.
  rewrite size_exp_monic // mulnC.
  suff : (1 < size q)%nat.
    by case: size => // [] [|v] //_ ; rewrite ltn_mul2r ltn_ord.
  case E : size => [|[|v]] //.
    have /eqP := E; rewrite size_poly_eq0 => /eqP qE0.
    by move: qM; rewrite qualifE qE0 lead_coefC eq_sym oner_eq0.
  have /eqP/size_poly1P[c cD0 qE] := E.
  by case/eqP: qD1; move: qM; rewrite qE qualifE lead_coefC => /eqP->.
have := size_comp_poly_leq p q.
rewrite qualifE /lead_coef leq_eqVlt => /orP[/eqP-> //|].
rewrite ltnS => sLp; move: cp0q.
by rewrite nth_default // eq_sym oner_eq0.
Qed.

Lemma rdvdp_comp_poly (R : comRingType) (r p q : {poly R}) : 
 p \is monic -> r \is monic -> r != 1 -> rdvdp p q -> rdvdp (p \Po r) (q \Po r).
Proof.
move=> pM rM rD1 /rdvdpP => /(_ pM) [qq qqE].
apply/rdvdpP; first by apply: monic_comp_poly.
by exists (qq \Po r); rewrite qqE comp_polyM.
Qed.
  
(* 99 *)
Lemma introspecMl (R : comRingType) (k m n : nat) (p : {poly R}) :
  m ⋈[k] p -> n ⋈[k] p -> m * n ⋈[k] p.
Proof.
case: m => // m.
have XmD1 : 'X^m.+1 != 1 :> {poly R}.
  apply/eqP => /(congr1 (size : {poly R} -> _)).
  by rewrite size_polyXn size_polyC oner_eq0.
case: k => [|k mIp nIp].
  rewrite /introspective !subrr !rmodp0 exprM => /eqP->.
  rewrite comp_polyX => /eqP->.
  by rewrite -comp_polyA comp_polyXn -exprM.
have XM : ('X^k.+1 - 1 : {poly R}) \is monic.
  rewrite qualifE lead_coefDl ?lead_coefXn ?unitr1 //.
  by rewrite size_polyXn size_opp size_polyC oner_neq0.
rewrite /introspective exprM -modp_exp // (eqP mIp) modp_exp //.
rewrite exprM -['X^m.+1 ^+_]comp_polyXn comp_polyX comp_polyA.
rewrite -subr_eq0 -rmodp_sub // -comp_polyB.
apply: rdvdp_trans (_ : rdvdp (('X^k.+1 -1) \Po 'X^m.+1) _) => //.
- by apply: monic_comp_poly => //; rewrite qualifE lead_coefXn.
- rewrite comp_polyB comp_polyXn comp_polyC -exprM mulnC exprM.
  by apply: dvdp_geom.
apply: rdvdp_comp_poly => //; first by rewrite qualifE lead_coefXn.
by rewrite /rdvdp rmodp_sub // subr_eq0.
Qed.

(* 100 *)
Lemma introspecMr (R : comRingType) (k n : nat) (p q : {poly R}) :
  n ⋈[k] p -> n ⋈[k] q -> n ⋈[k] (p * q).
Proof.
case: k => [|k nIp nIq].
  rewrite /introspective !subrr !rmodp0.
  by rewrite comp_polyM exprMn => /eqP-> /eqP->.
have Xlf := monic_Xn_sub_1 R (isT : (0 < k.+1)%N).
rewrite /introspective exprMn -rmodp_mulmr // (eqP nIq).
rewrite rmodp_mulmr // mulrC.
rewrite -rmodp_mulmr // (eqP nIp) rmodp_mulmr //.
by rewrite mulrC comp_polyM.
Qed.

End AKS.

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").
