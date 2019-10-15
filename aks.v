From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section AKS.

Definition introspective {R : idomainType} n k (p : {poly R}) :=
  p ^+ n %% ('X^k - 1) == (p \Po 'X^n) %% ('X^k - 1).

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

Lemma dvdp_geom (R : idomainType) n (p : {poly R}) : p - 1 %| p ^+ n.+1 - 1.
Proof. by rewrite poly_geom dvdp_mulIl. Qed.

(* 98 *)
Lemma introspec_char (F : finFieldType) (k n c : nat) :
  n \in [char F] -> n ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> nC; apply/eqP; congr ( _ %%  _).
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

Lemma modp_exp (R : idomainType) n (p d : {poly R}) :
  lead_coef d \is a GRing.unit -> ((p %% d) ^+ n) %% d = (p ^+ n) %% d.
Proof.
move=> lCd; elim: n => [|n IH]; first by rewrite !expr0.
rewrite !exprS -Pdiv.IdomainUnit.modp_mul // -IH Pdiv.IdomainUnit.modp_mul //.
by rewrite mulrC Pdiv.IdomainUnit.modp_mul // mulrC.
Qed.

(* 99 *)
Lemma introspecMl (R : idomainType) (k m n : nat) (p : {poly R}) :
  m ⋈[k] p -> n ⋈[k] p -> m * n ⋈[k] p.
Proof.
case: k => [|k mIp nIp].
  rewrite /introspective !subrr !modp0 exprM => /eqP->.
  rewrite comp_polyX => /eqP->.
  by rewrite -comp_polyA comp_polyXn -exprM.
have Xlf : lead_coef ('X^k.+1 - 1 : {poly R}) \is a GRing.unit.
  rewrite lead_coefDl ?lead_coefXn ?unitr1 //.
  by rewrite size_polyXn size_opp size_polyC oner_neq0.
rewrite /introspective exprM -modp_exp // (eqP mIp) modp_exp //.
rewrite exprM -['X^m ^+_]comp_polyXn comp_polyX comp_polyA.
rewrite -subr_eq0 -Pdiv.IdomainUnit.modp_opp // -Pdiv.IdomainUnit.modp_add //.
rewrite -comp_polyB.
apply: dvdp_trans (_ : ('X^k.+1 -1) \Po 'X^m %| _).
  rewrite comp_polyB comp_polyXn comp_polyC -exprM mulnC exprM.
  case: (m) => [|m1]; first by rewrite subrr dvdp0.
  by apply: dvdp_geom.
apply: Pdiv.Idomain.dvdp_comp_poly.
rewrite /dvdp Pdiv.IdomainUnit.modp_add //.
by rewrite Pdiv.IdomainUnit.modp_opp // subr_eq0.
Qed.

(* 99 *)
Lemma introspecMr (R : idomainType) (k n : nat) (p q : {poly R}) :
  n ⋈[k] p -> n ⋈[k] q -> n ⋈[k] (p * q).
Proof.
case: k => [|k nIp nIq].
  rewrite /introspective !subrr !modp0.
  by rewrite comp_polyM exprMn => /eqP-> /eqP->.
have Xlf : lead_coef ('X^k.+1 - 1 : {poly R}) \is a GRing.unit.
  rewrite lead_coefDl ?lead_coefXn ?unitr1 //.
  by rewrite size_polyXn size_opp size_polyC oner_neq0.
rewrite /introspective exprMn -Pdiv.IdomainUnit.modp_mul // (eqP nIq).
rewrite Pdiv.IdomainUnit.modp_mul // mulrC.
rewrite -Pdiv.IdomainUnit.modp_mul // (eqP nIp) Pdiv.IdomainUnit.modp_mul //.
by rewrite mulrC comp_polyM.
Qed.

End AKS.