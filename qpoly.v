From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype tuple.
From mathcomp
Require Import bigop binomial finset finfun ssralg countalg finalg poly polydiv.
From mathcomp
Require Import perm fingroup matrix mxalgebra mxpoly vector countalg.
Require Import more_thm.

(******************************************************************************)
(* This file minic the zmod file for polynomial                               *)
(* First, it defines polynomials of bounded size (equivalent of 'I_n),        *)
(* gives it a structure of choice, finite and countable ring, ..., and        *)
(* lmodule, when possible.                                                    *)
(* Internally, the construction uses poly_rV and rVpoly, but they should not  *)
(* be exposed.                                                                *)
(* We provide two bases: the 'X^i and the lagrange polynomials.               *)
(*     {poly_n R} == the type of polynomial of size at most n                 *)
(* irreducibleb p == boolean decision procedure for irreducibility            *)
(*                   of a bounded size polynomial over a finite idomain       *)
(* Considering {poly_n F} over a field F, it is a vectType and                *)
(*          'nX^i == 'X^i as an element of {poly_n R}                         *)
(*         polynX == [tuple 'X^0, ..., 'X^(n - 1)], basis of {poly_n R}       *)
(*    x.-lagrange == lagrange basis of {poly_n R} wrt x : nat -> F            *)
(* x.-lagrange_ i == the ith lagrange polynomial wrt the sampling points x    *)
(* Second, it defines polynomials quotiented by a poly (equivalent of 'Z_p),  *)
(* as bounded polynomial. As we are aiming to build a ring structure we need  *)
(* the polynomial to be monic and of size greater than one. If it is not the  *)
(* case we quotient by 'X                                                     *)
(*     mk_qpoly p == the actual polynomial on which we quotient               *)
(*                   if p is monic ans of size> 1 it is p otherwise 'X        *)
(*      {qpoly p} == defined as {poly_(size (mk_poly p)).-1 R} on which       *)
(*                   there is a ring structure                                *)
(*     in_qpoly p == turn the polynomial p into an element of {qpoly p} by    *)
(*                   taking a modulo                                          *)
(*            'qX == in_qpoly 'X                         *)
(* Third, it defines polynomials quotiented by a poly  (equivalent of 'F_p),  *)
(* as {qpoly p}. As we are aiming to build a field structure we need          *)
(* the polynomial to be monic and irreducible. As irreducible is not          *)
(* decidable in general, this is done by giving a proof.                      *)
(*      monic_irreducible_poly p == proof that p is monic is irreducible      *)
(*     {qfpoly mi} == defined as {qpoly p} if mi proves that                  *)
(*                    monic_irreducible_poly p                                *)
(* Finally, it constructs the discrete logarithm with a primitive polynomial  *)
(* on a final field                                                           *)
(*    primitive_poly p == p is a primitive polynome                           *)
(*     qlog sp_gt2' q == is the discrete log of q where q is an element of    *)
(*                       the quotient field with respect to a primitive       *)
(*                       polynomial p, sp_gt2 is a proof that the size of p   *)
(*                       is greater than                                      *)
(*     plog p q == is the discrete log of q with respect to p in {poly F}     *)
(*                 this makes only sense if p is a primitive polynomial of    *)
(*                 size > 2                                                   *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.
Import Pdiv.Field.
Import FinRing.Theory.
Local Open Scope ring_scope.

Section poly_of_size_zmod.
Context {R : ringType}.
Implicit Types (phR : phant R) (n : nat).

Section poly_of_size.
Variable (n : nat).

Definition poly_of_size :=
  [qualify a p | size (p : {poly R}) <= n].
Fact poly_of_size_key : pred_key poly_of_size. Proof. by []. Qed.
Canonical poly_of_size_keyd := KeyedQualifier poly_of_size_key.

Lemma npoly_submod_closed : submod_closed poly_of_size.
Proof.
split=> [|x p q sp sq]; rewrite qualifE ?size_polyC ?eqxx//.
rewrite (leq_trans (size_add _ _)) // geq_max.
by rewrite (leq_trans (size_scale_leq _ _)).
Qed.

Canonical npoly_opprPred := OpprPred npoly_submod_closed.
Canonical npoly_addrPred := AddrPred npoly_submod_closed.
Canonical npoly_zmodPred := ZmodPred npoly_submod_closed.
Canonical npoly_submodPred := SubmodPred npoly_submod_closed.

End poly_of_size.

Section npoly.

Record npoly_of phR n : predArgType := NPoly_of {
  polyn :> {poly R};
  _ : polyn \is a poly_of_size n
}.

Variable (n : nat).

Local Notation npolyR := (@npoly_of (Phant R) n).

Canonical npoly_subType := [subType for @polyn (Phant R) n].

Lemma npoly_is_a_poly_of_size (p : npolyR) : val p \is a poly_of_size n.
Proof. by case: p. Qed.
Hint Resolve npoly_is_a_poly_of_size : core.

Lemma size_npoly (p : npolyR) : size p <= n.
Proof. exact: npoly_is_a_poly_of_size. Qed.
Hint Resolve size_npoly : core.

Definition npoly_eqMixin := [eqMixin of npolyR by <:].
Canonical npoly_eqType := EqType npolyR npoly_eqMixin.
Definition npoly_choiceMixin := [choiceMixin of npolyR by <:].
Canonical npoly_choiceType := ChoiceType npolyR npoly_choiceMixin.
Definition npoly_zmodMixin := [zmodMixin of npolyR by <:].
Canonical npoly_zmodType := ZmodType npolyR npoly_zmodMixin.
Definition npoly_lmodMixin := [lmodMixin of npolyR by <:].
Canonical npoly_lmodType := LmodType R npolyR npoly_lmodMixin.

Definition npoly_rV : npolyR -> 'rV[R]_n := poly_rV \o val.
Definition rVnpoly : 'rV[R]_n -> npolyR := insubd (0 : npolyR) \o rVpoly.
Arguments rVnpoly /.
Arguments npoly_rV /.

Lemma npoly_rV_K : cancel npoly_rV rVnpoly.
Proof.
move=> p /=; apply/val_inj.
by rewrite val_insubd [_ \is a _]size_poly ?poly_rV_K.
Qed.
Lemma rVnpolyK : cancel rVnpoly npoly_rV.
Proof. by move=> p /=; rewrite val_insubd [_ \is a _]size_poly rVpolyK. Qed.
Hint Resolve npoly_rV_K rVnpolyK : core.

Lemma npoly_vect_axiom : Vector.axiom n npolyR.
Proof. by exists npoly_rV; [move=> ???; exact: linearP|exists rVnpoly]. Qed.

Definition npoly_vect_mixin := VectMixin npoly_vect_axiom.
Canonical npoly_vect_type := VectType R npolyR npoly_vect_mixin.

End npoly.
End poly_of_size_zmod.

Notation "'{poly_' n R }" := (npoly_of (Phant R) n)
  (at level 0, n at level 2, format "'{poly_' n  R }").
Notation NPoly := (NPoly_of (Phant _)).
#[global]
Hint Resolve size_npoly npoly_is_a_poly_of_size : core.

Definition npoly_countMixin (R : countRingType) n :=
  [countMixin of {poly_n R} by <:].
Canonical npoly_countType (R : countRingType) n :=
  CountType {poly_n R} (@npoly_countMixin R n).
Canonical npoly_subCountType (R : countRingType) n :=
  [subCountType of {poly_n R}].

Section npoly_fin.
Variable (R : finRingType) (n : nat).

Definition npoly_finMixin (R : finRingType) (n : nat) :=
  CanFinMixin (@npoly_rV_K [ringType of R] n).
Canonical npoly_finType (R : finRingType) n :=
  FinType {poly_n R} (@npoly_finMixin R n).
Canonical npoly_subFinType := [subFinType of {poly_n R}].
End npoly_fin.

Section npoly_theory.
Context (R : ringType) {n : nat}.

Lemma polyn_is_linear : linear (@polyn _ _ _ : {poly_n R} -> _).
Proof. by []. Qed.
Canonical polyn_additive := Additive polyn_is_linear.
Canonical polyn_linear := Linear polyn_is_linear.

Canonical npoly (E : nat -> R) : {poly_n R} :=
   @NPoly_of _ (Phant R) _ (\poly_(i < n) E i) (size_poly _ _).

Fact size_npoly0 : size (0 : {poly R}) <= n.
Proof. by rewrite size_poly0. Qed.

Definition npoly0 := NPoly (size_npoly0).

Fact npolyp_key : unit. Proof. exact: tt. Qed.
Definition npolyp : {poly R} -> {poly_n R} :=
  locked_with npolyp_key (npoly \o (nth 0)).

Definition npoly_of_seq := npolyp \o Poly.

Lemma npolyP (p q : {poly_n R}) : nth 0 p =1 nth 0 q <-> p = q.
Proof. by split => [/polyP/val_inj|->]. Qed.

Lemma coef_npolyp (p : {poly R}) i : (npolyp p)`_i = if i < n then p`_i else 0.
Proof. by rewrite /npolyp unlock /= coef_poly. Qed.

Lemma big_coef_npoly (p : {poly_n R}) i : n <= i -> p`_i = 0.
Proof.
by move=> i_big; rewrite nth_default // (leq_trans _ i_big) ?size_npoly.
Qed.

Lemma npolypK (p : {poly R}) : size p <= n -> npolyp p = p :> {poly R}.
Proof.
move=> spn; apply/polyP=> i; rewrite coef_npolyp.
by have [i_big|i_small] // := ltnP; rewrite nth_default ?(leq_trans spn).
Qed.

Lemma coefn_sum (I : Type) (r : seq I) (P : pred I)
  (F : I -> {poly_n R}) (k : nat) :
  (\sum_(i <- r | P i) F i)`_k = \sum_(i <- r | P i) (F i)`_k.
Proof. by rewrite !raddf_sum //= coef_sum. Qed.

End npoly_theory.
Arguments npoly {R} n E.
Arguments npolyp {R} n p.

Section fin_npoly.

Variable R : finRingType.
Variable n : nat.
Implicit Types p q : {poly_n R}.

Definition npoly_enum : seq {poly_n R} :=
  if n isn't n.+1 then [:: npoly0 _] else
  pmap insub [seq \poly_(i < n.+1) c (inord i) | c : (R ^ n.+1)%type].

Lemma npoly_enum_uniq : uniq npoly_enum.
Proof.
rewrite /npoly_enum; case: n=> [|k] //.
rewrite pmap_sub_uniq // map_inj_uniq => [|f g eqfg]; rewrite ?enum_uniq //.
apply/ffunP => /= i; have /(congr1 (fun p : {poly _} => p`_i)) := eqfg.
by rewrite !coef_poly ltn_ord inord_val.
Qed.

Lemma mem_npoly_enum p : p \in npoly_enum.
Proof.
rewrite /npoly_enum; case: n => [|k] // in p *.
  case: p => [p sp] /=.
  by rewrite in_cons -val_eqE /= -size_poly_leq0 [size _ <= _]sp.
rewrite mem_pmap_sub; apply/mapP.
eexists [ffun i : 'I__ => p`_i]; first by rewrite mem_enum.
apply/polyP => i; rewrite coef_poly.
have [i_small|i_big] := ltnP; first by rewrite ffunE /= inordK.
by rewrite nth_default // 1?(leq_trans _ i_big) // size_npoly.
Qed.

Lemma card_npoly : #|{poly_n R}| = (#|R| ^ n)%N.
Proof.
rewrite -(card_imset _ (can_inj (@npoly_rV_K _ _))) eq_cardT.
  by rewrite -cardT /= card_mx mul1n.
by move=> v; apply/imsetP; exists (rVnpoly v); rewrite ?rVnpolyK //.
Qed.

End fin_npoly.

Section Irreducible.

Variable R : finIdomainType.
Variable p : {poly R}.

Definition irreducibleb :=
  ((1 < size p) &&
  [forall q : {poly_((size p).-1) R},
    (Pdiv.Ring.rdvdp q p)%R ==> (size q <= 1)])%N.

Lemma irreducibleP : reflect (irreducible_poly p) irreducibleb.
Proof.
rewrite /irreducibleb /irreducible_poly.
apply: (iffP idP) => [/andP[sp /'forall_implyP /= Fp]|[sp Fpoly]].
  have sp_gt0 : size p > 0 by case: size sp.
  have p_neq0 : p != 0 by rewrite -size_poly_eq0; case: size sp.
  split => // q sq_neq1 dvd_qp; rewrite -dvdp_size_eqp // eqn_leq dvdp_leq //=.
  apply: contraNT sq_neq1; rewrite -ltnNge => sq_lt_sp.
  have q_small: (size q <= (size p).-1)%N by rewrite -ltnS prednK.
  rewrite Pdiv.Idomain.dvdpE in dvd_qp.
  have /= := Fp (NPoly q_small) dvd_qp.
  rewrite leq_eqVlt ltnS => /orP[//|]; rewrite size_poly_leq0 => /eqP q_eq0.
  by rewrite -Pdiv.Idomain.dvdpE q_eq0 dvd0p (negPf p_neq0) in dvd_qp.
have sp_gt0 : size p > 0 by case: size sp.
rewrite sp /=; apply/'forall_implyP => /= q.
rewrite -Pdiv.Idomain.dvdpE=> dvd_qp.
have [/eqP->//|/Fpoly/(_ dvd_qp)/eqp_size sq_eq_sp] := boolP (size q == 1%N).
by have := size_npoly q; rewrite sq_eq_sp -ltnS prednK ?ltnn.
Qed.

End Irreducible.

Section Vspace.

Variable (K : fieldType) (n : nat).

Lemma dim_polyn : \dim (fullv : {vspace {poly_n K}}) = n.
Proof. by rewrite [LHS]mxrank_gen mxrank1. Qed.

Definition npolyX : n.-tuple {poly_n K} := [tuple npolyp n 'X^i | i < n].
Notation "''nX^' i" := (tnth npolyX i)
  (at level 3, i at level 2, format "''nX^' i").

Lemma npolyXE (i : 'I_n) : 'nX^i = 'X^i :> {poly _}.
Proof. by rewrite tnth_map tnth_ord_tuple npolypK // size_polyXn. Qed.

Lemma nth_npolyX (i : 'I_n) : npolyX`_i = 'nX^i.
Proof. by rewrite -tnth_nth. Qed.

Lemma npolyX_free : free npolyX.
Proof.
apply/freeP=> u /= sum_uX_eq0 i; have /npolyP /(_ i) := sum_uX_eq0.
rewrite (@big_morph _ _ _ 0%R +%R) // coef_sum coef0.
rewrite (bigD1 i) ?big1 /= ?addr0 ?coefZ ?(nth_map 0%N) ?size_iota //.
  by rewrite nth_npolyX npolyXE coefXn eqxx mulr1.
move=> j; rewrite -val_eqE /= => neq_ji.
by rewrite nth_npolyX npolyXE coefZ coefXn eq_sym (negPf neq_ji) mulr0.
Qed.

Lemma npolyX_full : basis_of fullv npolyX.
Proof.
by rewrite basisEfree npolyX_free subvf size_map size_enum_ord dim_polyn /=.
Qed.

Lemma npolyX_coords (p : {poly_n K}) i : coord npolyX i p = p`_i.
Proof.
rewrite [p in RHS](coord_basis npolyX_full) ?memvf // coefn_sum.
rewrite (bigD1 i) //= coefZ nth_npolyX npolyXE coefXn eqxx mulr1 big1 ?addr0//.
move=> j; rewrite -val_eqE => /= neq_ji.
by rewrite coefZ nth_npolyX npolyXE coefXn eq_sym (negPf neq_ji) mulr0.
Qed.

Lemma npolyX_gen (p : {poly K}) : (size p <= n)%N ->
  p = \sum_(i < n) p`_i *: 'nX^i.
Proof.
move=> sp; rewrite -[p](@npolypK _ n) //.
rewrite [npolyp _ _ in LHS](coord_basis npolyX_full) ?memvf //.
rewrite (@big_morph _ _ _ 0%R +%R) // !raddf_sum.
by apply: eq_bigr=> i _; rewrite npolyX_coords //= nth_npolyX npolyXE.
Qed.

Section lagrange.

Variables (x : nat -> K).

Notation lagrange_def := (fun i :'I_n =>
  let k := i in let p := \prod_(j < n | j != k) ('X - (x j)%:P)
  in (p.[x k]^-1)%:P * p).

Fact lagrange_key : unit. Proof. exact: tt. Qed.

Definition lagrange := locked_with lagrange_key
  [tuple npolyp n (lagrange_def i) | i < n].
Notation lagrange_ := (tnth lagrange).

Hypothesis n_gt0 : (0 < n)%N.
Hypothesis x_inj : injective x.

Let lagrange_def_sample (i j : 'I_n) : (lagrange_def i).[x j] = (i == j)%:R.
Proof using x_inj.
rewrite hornerM hornerC; set p := (\prod_(_ < _ | _) _).
have [<-|neq_ij] /= := altP eqP.
  rewrite mulVf // horner_prod; apply/prodf_neq0 => k neq_ki.
  by rewrite hornerXsubC subr_eq0 inj_eq // eq_sym.
rewrite [X in _ * X]horner_prod (bigD1 j) 1?eq_sym //=.
by rewrite hornerXsubC subrr mul0r mulr0.
Qed.

Let size_lagrange_def i : size (lagrange_def i) = n.
Proof using n_gt0 x_inj.
rewrite size_Cmul; last first.
  suff : (lagrange_def i).[x i] != 0.
    by rewrite hornerE mulf_eq0 => /norP [].
  by rewrite lagrange_def_sample ?eqxx ?oner_eq0.
rewrite size_prod /=; last first.
  by move=> j neq_ji; rewrite polyXsubC_eq0.
rewrite (eq_bigr (fun=> (2 * 1)%N)); last first.
  by move=> j neq_ji; rewrite size_XsubC.
rewrite -big_distrr /= sum1_card cardC1 card_ord /=.
by case: (n) {i} n_gt0 => ?; rewrite mul2n -addnn -addSn addnK.
Qed.

Lemma lagrangeE i : lagrange_ i = lagrange_def i :> {poly _}.
Proof.
rewrite [lagrange]unlock tnth_map.
by rewrite [val _]npolypK tnth_ord_tuple // size_lagrange_def.
Qed.

Lemma nth_lagrange (i : 'I_n) : lagrange`_i = lagrange_ i.
Proof. by rewrite -tnth_nth. Qed.

Lemma size_lagrange_ i : size (lagrange_ i) = n.
Proof. by rewrite lagrangeE size_lagrange_def. Qed.

Lemma size_lagrange : size lagrange = n.
Proof. by rewrite size_tuple. Qed.

Lemma lagrange_sample (i j : 'I_n) : (lagrange_ i).[x j] = (i == j)%:R.
Proof. by rewrite lagrangeE lagrange_def_sample. Qed.

Lemma lagrange_free : free lagrange.
Proof.
apply/freeP=> lambda eq_l i.
have /(congr1 (fun p : {poly__ _} => p.[x i])) := eq_l.
rewrite (@big_morph _ _ _ 0%R +%R) // horner_sum horner0.
rewrite (bigD1 i) // big1 => [|j /= /negPf ji] /=;
by rewrite ?hornerE nth_lagrange lagrange_sample ?eqxx ?ji ?mulr1 ?mulr0.
Qed.

Lemma lagrange_full : basis_of fullv lagrange.
Proof.
by rewrite basisEfree lagrange_free subvf size_lagrange dim_polyn /=.
Qed.

Lemma lagrange_coords (p : {poly_n K}) i : coord lagrange i p = p.[x i].
Proof.
rewrite [p in RHS](coord_basis lagrange_full) ?memvf //.
rewrite (@big_morph _ _ _ 0%R +%R) // horner_sum.
rewrite (bigD1 i) // big1 => [|j /= /negPf ji] /=;
by rewrite ?hornerE nth_lagrange lagrange_sample ?eqxx ?ji ?mulr1 ?mulr0.
Qed.

Lemma lagrange_gen (p : {poly K}) : (size p <= n)%N ->
  p = \sum_(i < n) p.[x i]%:P * lagrange_ i.
Proof.
move=> sp; rewrite -[p](@npolypK _ n) //.
rewrite [npolyp _ _ in LHS](coord_basis lagrange_full) ?memvf //.
rewrite (@big_morph _ _ _ 0%R +%R) //; apply: eq_bigr=> i _.
by rewrite lagrange_coords mul_polyC nth_lagrange.
Qed.

End lagrange.

End Vspace.

Notation "''nX^' i" := (tnth (npolyX _) i)
  (at level 3, i at level 2, format "''nX^' i").
Notation "x .-lagrange" := (lagrange x)
  (at level 2, format "x .-lagrange") : ring_scope.
Notation "x .-lagrange_" := (tnth x.-lagrange)
  (at level 2, format "x .-lagrange_") : ring_scope.

Section Qpoly.

Variable R : ringType.
Variable h : {poly R}.

Definition mk_qpoly := 
  if (1 < size h)%N && (h \is monic) then h else 'X.

Definition qpoly := {poly_(size mk_qpoly).-1 R}.

Local Notation "{qpoly}" := qpoly.

Lemma monic_mk_qpoly : mk_qpoly \is monic.
Proof.
rewrite /mk_qpoly; case: leqP=> [_|/=]; first by apply: monicX.
by case E : (h \is monic) => [->//|] => _; apply: monicX.
Qed. 

Lemma size_mk_qpoly_gt1 : (1 < size mk_qpoly)%N.
Proof. 
by rewrite !fun_if size_polyX; case: leqP => //=; rewrite if_same.
Qed.

Lemma size_mk_qpoly_gt0 : (0 < size mk_qpoly)%N.
Proof. by rewrite (leq_trans _ size_mk_qpoly_gt1). Qed.

Lemma mk_qpoly_neq0 : mk_qpoly != 0.
Proof. by rewrite -size_poly_gt0 size_mk_qpoly_gt0. Qed.

Lemma size_mk_qpoly (p : {qpoly}) : size p < size mk_qpoly.
Proof.
have: (p : {poly R}) \is a poly_of_size (size mk_qpoly).-1 by case: p.
by rewrite qualifE -ltnS prednK // size_mk_qpoly_gt0.
Qed.

(* standard inject *)
Lemma poly_of_size_mod p :
  (rmodp p mk_qpoly) \is a poly_of_size (size mk_qpoly).-1.
Proof.
rewrite qualifE -ltnS prednK ?size_mk_qpoly_gt0 //.
by apply: ltn_rmodpN0; rewrite mk_qpoly_neq0.
Qed.

Definition in_qpoly p : {qpoly} := NPoly_of _ (poly_of_size_mod p).

Lemma in_qpoly_small (p : {poly R}) : 
  size p < size mk_qpoly -> in_qpoly p = p :> {poly R}.
Proof. exact: rmodp_small. Qed.

Lemma qpoly_const_proof k : 
  (k%:P : {poly R}) \is a poly_of_size (size mk_qpoly).-1.
Proof.
rewrite qualifE -ltnS size_polyC prednK ?size_mk_qpoly_gt0 //.
by rewrite (leq_ltn_trans _ size_mk_qpoly_gt1) //; case: eqP.
Qed.

Definition qpoly_const k : {qpoly} :=  NPoly_of _ (qpoly_const_proof k).

Lemma qpoly_constE k : qpoly_const k = k%:P :> {poly R}.
Proof. by []. Qed.

Lemma qpoly_const0 : qpoly_const 0 = 0.
Proof. by apply/val_eqP/eqP. Qed.

Definition qpoly1 := qpoly_const 1.

Definition qpoly_mul (q1 q2 : {qpoly}) : {qpoly} := 
  in_qpoly ((q1 : {poly R}) * q2).

Lemma qpoly_mul1z : left_id qpoly1 qpoly_mul.
Proof.
by move=> x; apply: val_inj; rewrite /= mul1r rmodp_small // size_mk_qpoly.
Qed. 

Lemma qpoly_mulz1 : right_id qpoly1 qpoly_mul.
Proof.
by move=> x; apply: val_inj; rewrite /= mulr1 rmodp_small // size_mk_qpoly.
Qed.

Lemma qpoly_nontrivial : qpoly1 != 0.
Proof. by apply/eqP/val_eqP; rewrite /= oner_eq0. Qed.

Definition qpolyX := in_qpoly 'X.
Notation "'qX" := qpolyX.

Lemma qpolyXE : 2 < size h -> h \is monic -> 'qX = 'X :> {poly R}.
Proof.
move=> sh_gt2 h_mo.
by rewrite in_qpoly_small // size_polyX /mk_qpoly ifT // (ltn_trans _ sh_gt2).
Qed.

End Qpoly.

Notation "'qX" := (qpolyX _).
Notation "{qpoly  p }" := (qpoly p).

Lemma mk_qpoly_X (R : ringType) : mk_qpoly 'X = 'X :> {poly R}.
Proof. by rewrite /mk_qpoly size_polyX monicX. Qed.

Lemma mk_qpoly_Xn (R : ringType) n : mk_qpoly 'X^n = 'X^n.-1.+1 :> {poly R}.
Proof. by case: n => [|n]; rewrite /mk_qpoly size_polyXn monicXn /= ?expr1. Qed.

Lemma card_qpoly (R : finRingType) (h : {poly R}):
   #|{qpoly h}| = #|R| ^ (size (mk_qpoly h)).-1.
Proof. by rewrite card_npoly. Qed.

Section QRing.

Variable A : comRingType.
Variable h : {poly A}.

(* Ring operations *)

Lemma qpoly_mulC : commutative (@qpoly_mul A h).
Proof. by move=> p q; apply: val_inj; rewrite /= mulrC. Qed.

Lemma qpoly_mulA : associative (@qpoly_mul A h).
Proof.
have rPM := monic_mk_qpoly h; move=> p q r; apply: val_inj.
by rewrite /= rmodp_mulml // rmodp_mulmr // mulrA.
Qed.

Lemma qpoly_mul_addr : right_distributive (@qpoly_mul A h) +%R.
Proof.
have rPM := monic_mk_qpoly h; move=> p q r; apply: val_inj.
by rewrite /= !(mulrDr, rmodp_mulmr, rmodpD).
Qed.

Lemma qpoly_mul_addl : left_distributive (@qpoly_mul A h) +%R.
Proof. by move=> p q r; rewrite -!(qpoly_mulC r) qpoly_mul_addr. Qed.

Definition qpoly_ringMixin :=
  ComRingMixin qpoly_mulA qpoly_mulC (@qpoly_mul1z _ h) qpoly_mul_addl
               (@qpoly_nontrivial _ h).

Canonical qpoly_ringType := Eval hnf in RingType {qpoly h} qpoly_ringMixin.
Canonical npoly_ringType := Eval hnf in RingType {poly_ _ A} qpoly_ringMixin.
Canonical qpoly_comRingType := Eval hnf in ComRingType {qpoly h} qpoly_mulC.
Canonical npoly_comRingType := Eval hnf in ComRingType {poly_ _ A} qpoly_mulC.


Lemma poly_of_qpoly_sum I (r : seq I) (P1 : pred I) (F : I -> {qpoly h}) :
  ((\sum_(i <- r | P1 i) F i) =
    \sum_(p <- r | P1 p) ((F p) : {poly A}) :> {poly A})%R.
Proof. by elim/big_rec2: _ => // i p q IH <-. Qed.

Lemma poly_of_qpolyD (p q : {qpoly h}) : 
  p + q= (p : {poly A}) + q :> {poly A}.
Proof. by []. Qed.

Lemma qpoly_natmul p : (p%:R : {qpoly h}) = p%:R :> {poly A}.
Proof.  by elim: p => //= p IH; rewrite !mulrS poly_of_qpolyD IH. Qed.

Lemma char_qpoly : [char {qpoly h}] =i [char A].
Proof.
move=> p; rewrite !inE; congr (_ && _).
apply/eqP/eqP=> [/(congr1 val) /=|pE]; last first.
  by apply: val_inj => //=; rewrite qpoly_natmul /= -poly_natmul pE.
rewrite !qpoly_natmul -!poly_natmul=> /(congr1 val) /=.
by rewrite polyseqC polyseq0; case: eqP.
Qed.

Lemma poly_of_qpolyM (p q : {qpoly h}) : 
  p * q = rmodp ((p : {poly A}) * q) (mk_qpoly h) :> {poly A}.
Proof. by []. Qed.

Lemma poly_of_qpolyX (p : {qpoly h}) n : 
  p ^+ n = rmodp ((p : {poly A}) ^+ n) (mk_qpoly h) :> {poly A}.
Proof.
have HhQ := monic_mk_qpoly h.
elim: n => //= [|n IH].
  rewrite rmodp_small // size_polyC ?(leq_ltn_trans _ (size_mk_qpoly_gt1 _)) //.
  by case: eqP.
by rewrite exprS /= IH // rmodp_mulmr // -exprS.
Qed.

Lemma qpoly_constN (a : A) : qpoly_const h (- a) = -(qpoly_const h a).
Proof. apply: val_inj; rewrite /= raddfN //= raddfN. Qed.

Lemma qpoly_constD : {morph (qpoly_const h) : a b / a + b >-> a + b}%R.
Proof. by move=> a b; apply/val_eqP/eqP=> /=; rewrite -!raddfD. Qed.

Lemma qpoly_constM : {morph (qpoly_const h) : a b / a * b >-> a * b}%R.
Proof.
move=> a b; apply/val_eqP/eqP=> /=; rewrite -polyCM rmodp_small //=.
have := qpoly_const_proof h (a * b).
by rewrite qualifE -ltnS prednK // size_mk_qpoly_gt0.
Qed.

Lemma qpoly_const_is_rmorphism : rmorphism (qpoly_const h).
Proof.
do ?split; move=> // x y /=; first by rewrite qpoly_constD qpoly_constN.
by rewrite qpoly_constM.
Qed.

Canonical qpoly_const_rmorphism := RMorphism qpoly_const_is_rmorphism.

Definition qpoly_scale k (p : {qpoly h}) := (k *: p)%R.

Fact qpoly_scaleA a b p :
  qpoly_scale a (qpoly_scale b p) = qpoly_scale (a * b) p.
Proof.  by apply/val_eqP; rewrite /= scalerA. Qed.

Fact qpoly_scale1l : left_id 1%R qpoly_scale.
Proof. by move=> p; apply/val_eqP; rewrite /= scale1r. Qed.

Fact qpoly_scaleDr a : {morph qpoly_scale a : p q / (p + q)%R}.
Proof. by move=> p q; apply/val_eqP; rewrite /= scalerDr. Qed.

Fact qpoly_scaleDl p : {morph qpoly_scale^~ p : a b / a + b}%R.
Proof. by move=> a b; apply/val_eqP; rewrite /= scalerDl. Qed.

Fact qpoly_scaleAl a p q : qpoly_scale a (p * q) = (qpoly_scale a p * q).
Proof. by apply/val_eqP; rewrite /= -scalerAl rmodpZ // monic_mk_qpoly. Qed.

Fact qpoly_scaleAr a p q : qpoly_scale a (p * q) = p * (qpoly_scale a q).
Proof. by apply/val_eqP; rewrite /= -scalerAr rmodpZ // monic_mk_qpoly. Qed.

Canonical qpoly_lalgType :=
  Eval hnf in LalgType A ({qpoly h}) qpoly_scaleAl.
Canonical npoly_lalgType :=
  Eval hnf in LalgType A ({poly_ _ _}) qpoly_scaleAl.

Canonical qpoly_algType := AlgType A {qpoly h} qpoly_scaleAr.
Canonical npoly_algType := AlgType A {poly_ _ _} qpoly_scaleAr.

Lemma poly_of_qpolyZ (p : {qpoly h}) a :
  a *: p = a *: (p : {poly A})  :> {poly A}.
Proof. by []. Qed.

End QRing.

Section iDomain.

Variable R : idomainType.
Variable h : {poly R}.
         
Definition monic_irreducible_poly  (p : {poly R}) := 
  ((irreducible_poly p) * (p \is monic))%type.
Hypothesis hI : monic_irreducible_poly h.

Definition qfpoly : monic_irreducible_poly h -> Type := fun=> {qpoly h}.
Notation "{qfpoly}" := (qfpoly hI).

Canonical qfpoly_eqType := [eqType of {qfpoly}].
Canonical qfpoly_choiceType := [choiceType of {qfpoly}].
Canonical qfpoly_zmodType := [zmodType of {qfpoly}].
Canonical qfpoly_ringType := [ringType of {qfpoly}].

End iDomain.

Notation "{qfpoly  p }" := (qfpoly p).

Section finIDomain.

Variable R : finIdomainType.
Variable h : {poly R}.
Hypothesis hI : monic_irreducible_poly h.

Canonical qfpoly_finZmodType := [finZmodType of {qfpoly hI}].
Canonical qfpoly_finRingType := [finRingType of {qfpoly hI}].

End finIDomain.

Section Field.

Variable R : fieldType.
Variable h : {poly R}.

Notation hQ := (mk_qpoly h).

Definition qpoly_inv (p : {qpoly h}) := 
  if coprimep hQ p then let v : {qpoly h} := in_qpoly h (egcdp hQ p).2 in 
                        ((lead_coef (v * p)) ^-1 *: v) else p.

(* Ugly *)
Lemma qpoly_mulVz (p : {qpoly h}) : coprimep hQ p -> (qpoly_inv p * p = 1)%R.
Proof.
have hQM := monic_mk_qpoly h.
move=> hCp; apply: val_inj; rewrite /qpoly_inv /in_qpoly hCp /=.
have p_neq0 : p != 0%R.
  apply/eqP=> pZ; move: hCp; rewrite pZ.
  rewrite coprimep0 -size_poly_eq1.
  by case: size (size_mk_qpoly_gt1 h) => [|[]].
have F : (egcdp hQ p).1 * hQ + (egcdp hQ p).2 * p %= 1.
  apply: eqp_trans _ (_ : gcdp hQ p %= _).
    rewrite eqp_sym.
    by case: (egcdpP (mk_qpoly_neq0 h) p_neq0).
  by rewrite -size_poly_eq1.
rewrite rmodp_mulml // -scalerAl rmodpZ // rmodp_mulml //.
rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE //.
have := eqp_modpl hQ F.
rewrite modpD // modp_mull add0r // .
rewrite [(1 %% _)%R]modp_small => // [egcdE|]; last first.
  by rewrite size_polyC oner_eq0 size_mk_qpoly_gt1.
rewrite {2}(eqpfP egcdE) lead_coefC divr1 alg_polyC scale_polyC mulVf //.
rewrite lead_coef_eq0.
apply/eqP => egcdZ.
by move: egcdE; rewrite -size_poly_eq1 egcdZ size_polyC eq_sym  eqxx.
Qed.

Lemma qpoly_mulzV (p : {qpoly h}) :
  coprimep hQ p -> (p * (qpoly_inv p) = 1)%R.
Proof. by move=> hCp; rewrite /= mulrC qpoly_mulVz. Qed.

Lemma qpoly_intro_unit (p q : {qpoly h}) : (q * p = 1)%R -> coprimep hQ p.
Proof.
have hQM := monic_mk_qpoly h.
case; rewrite -[rmodp]/Pdiv.Ring.rmodp -!Pdiv.IdomainMonic.modpE // => qp1.
have:= coprimep1 hQ.
rewrite -coprimep_modr -[1%R]qp1 !coprimep_modr coprimepMr; by case/andP.
Qed.

Lemma qpoly_inv_out (p : {qpoly h}) : ~~ coprimep hQ p -> qpoly_inv p = p.
Proof. by rewrite /qpoly_inv => /negPf->. Qed.

Definition qpoly_unitRingMixin :=
  ComUnitRingMixin qpoly_mulVz qpoly_intro_unit qpoly_inv_out.
Canonical qpoly_unitRingType :=
  Eval hnf in UnitRingType {qpoly h} qpoly_unitRingMixin.
Canonical npoly_unitRingType :=
  Eval hnf in UnitRingType {poly_ _ _} qpoly_unitRingMixin.
Canonical qpoly_comUnitRingType :=
  Eval hnf in [comUnitRingType of {qpoly h}].

Hypothesis hI : monic_irreducible_poly h.

Canonical qfpoly_unitRingType := [unitRingType of {qfpoly hI}].
Canonical qfpoly_comRingType := [comRingType of {qfpoly hI}].
Canonical qfpoly_comUnitRingType := [comUnitRingType of {qfpoly hI}].

Lemma mk_qpolyE : mk_qpoly h = h.
Proof. by rewrite /mk_qpoly !hI. Qed.

Lemma irreducible_poly_coprime (A : idomainType) (p q : {poly A}) :
  irreducible_poly p -> coprimep p q = ~~(p %| q)%R.
Proof.
case => H1 H2; apply/coprimepP/negP.
  move=> sPq H.
  by have := sPq p (dvdpp _) H; rewrite -size_poly_eq1; case: size H1 => [|[]].
move=> pNDq d dDp dPq.
rewrite -size_poly_eq1; case: eqP => // /eqP /(H2 _) => /(_ dDp) dEp.
by case: pNDq; rewrite -(eqp_dvdl _ dEp).
Qed.

Lemma coprimep_unit (p : {qpoly h}) : p != 0%R -> coprimep hQ p.
Proof.
move=> pNZ.
rewrite irreducible_poly_coprime //; last first.
  by case: hI; rewrite mk_qpolyE.
apply: contra pNZ => H; case: eqP => // /eqP /dvdp_leq /(_ H).
by rewrite leqNgt size_mk_qpoly.
Qed.

Lemma qpoly_mulVp (p : {qpoly h}) : p != 0%R -> (qpoly_inv p * p = 1)%R.
Proof. by move=> pNZ; apply/qpoly_mulVz/coprimep_unit. Qed.

Lemma qpoly_inv0 : qpoly_inv 0%R = 0%R :> {qpoly h}.
Proof.
rewrite /qpoly_inv /= coprimep0 -size_poly_eq1.
rewrite [in X in X == _]mk_qpolyE.
by have [[]] := hI; case: size => [|[]].
Qed.

Definition qpoly_fieldUnitMixin := FieldUnitMixin qpoly_mulVp qpoly_inv0.

Lemma qpoly_fieldMixin : GRing.Field.mixin_of [unitRingType of {qpoly h}].
Proof. by apply: coprimep_unit. Qed.

Definition qpoly_fieldIdomainMixin := FieldIdomainMixin qpoly_fieldMixin.

Canonical qpoly_idomainType :=
  Eval hnf in IdomainType {qfpoly hI} qpoly_fieldIdomainMixin.
Canonical qpoly_fieldType :=
  Eval hnf in FieldType {qfpoly hI} qpoly_fieldMixin.

End Field.

Section FinField.

Variable R : finFieldType.
Variable h : {poly R}.
Notation hQ := (mk_qpoly h).

Canonical qpoly_finUnitRingType :=
  Eval hnf in [finUnitRingType of {qpoly h}].
Canonical qpoly_finComUnitRingType :=
  Eval hnf in [finComUnitRingType of {qpoly h}].

Hypothesis hI : monic_irreducible_poly h.

Canonical qfpoly_finUnitRingType := 
  Eval hnf in [finUnitRingType of {qfpoly hI}].
Canonical qfpoly_finComRingType := 
  Eval hnf in [comRingType of {qfpoly hI}].
Canonical qfpoly_finComUnitRingType :=
  Eval hnf in [comUnitRingType of {qfpoly hI}].
Canonical qpoly_finIdomainType :=
  Eval hnf in [finIdomainType of {qfpoly hI}].
Canonical qpoly_finFieldType :=
  Eval hnf in [finFieldType of {qfpoly hI}].

End FinField.

Section inPoly.

Variable R : comRingType.
Variable h : {poly R}.

Lemma in_qpoly_comp_horner (p q : {poly R}) :
 in_qpoly h (p \Po q) =
     (map_poly (qpoly_const h) p).[in_qpoly h q].
Proof.
have hQM := monic_mk_qpoly h.
rewrite comp_polyE /map_poly poly_def horner_sum /=.
apply: val_inj.
rewrite /= rmodp_sum // poly_of_qpoly_sum.
apply: eq_bigr => i  _.
rewrite !hornerE /in_qpoly /=.
rewrite mul_polyC // !rmodpZ //=.
by rewrite poly_of_qpolyX rmodp_mod // rmodpX // rmodp_mod.
Qed.

Lemma map_poly_div_inj : injective (map_poly (qpoly_const h)).
Proof.
apply: map_inj_poly => [x y /val_eqP /eqP /polyC_inj //|].
by rewrite qpoly_const0.
Qed.

End inPoly.

Section finPoly.

(* Unfortunately we need some duplications so inference 
   propagate qfpoly :-( )*)
Definition qfpoly_const (R : idomainType) (h : {poly R})
   (hMI : monic_irreducible_poly h) : R -> {qfpoly hMI} := qpoly_const h.

Lemma map_fpoly_div_inj
	  (R : idomainType) (h : {poly R}) (hMI : monic_irreducible_poly h) : 
       injective (map_poly (qfpoly_const hMI)).
Proof. by apply: (@map_poly_div_inj R h). Qed.

End finPoly.

Section PrimitivePoly.

Variable F : finFieldType.
Variable h : {poly F}.
Hypothesis sh_gt2 : 2 < size h.
Let sh_gt1 : 1 < size h.
Proof. by apply: leq_ltn_trans sh_gt2. Qed.

Definition primitive_poly (p: {poly F}) := 
  let v := (#|F|^(size p).-1).-1 in 
  [&& p \is monic,
      irreducibleb p,
      p %| 'X^v - 1 &
      [forall n : 'I_v, (p %| 'X^n - 1) ==> (n == 0%N :> nat)]].

Lemma primitive_polyP (p : {poly F}) :
  reflect 
    (let v := (#|F|^(size p).-1).-1 in 
      [/\ monic_irreducible_poly p,
          p %| 'X^v - 1 &
          forall n, 0 < n < v -> ~~ (p %| 'X^n - 1)])
    (primitive_poly p).
Proof.
apply: (iffP and4P) => [[H1 H2 H3 /forallP H4] v|[[H1 H2] H3 H4]]; split => //.
- by split => //; apply/irreducibleP.
- move=> n /andP[n_gt0 nLv]; apply/negP => /(implyP (H4 (Ordinal nLv))) /=.
  by rewrite eqn0Ngt n_gt0.
- by apply/irreducibleP.
apply/forallP=> [] [[|n] Hn] /=; apply/implyP => pDX //.
by case/negP: (H4 n.+1 Hn).
Qed.

Hypothesis Hh : primitive_poly h.

Lemma primitive_mi : monic_irreducible_poly h.
Proof. by case/primitive_polyP: Hh. Qed.

Lemma qX_ni_unit :  ('qX : {qfpoly primitive_mi}) \in GRing.unit.
Proof.
rewrite unitfE /=.
apply/eqP => /val_eqP/=.
rewrite [rmodp _ _]qpolyXE ?polyX_eq0 //.
by case: primitive_mi.
Qed.

Definition gX := FinRing.unit {qfpoly primitive_mi} qX_ni_unit.

Lemma dvdp_order n : (h %| 'X^n - 1) = (gX ^+ n == 1)%g.
Proof.
have [hM hI] := primitive_mi.
have eqr_add2r (r : ringType) (a b c : r) : (a + c == b + c) = (a == b).
  by apply/eqP/eqP => [H|->//]; rewrite -(addrK c a) H addrK.
rewrite -val_eqE /= val_unitX /= -val_eqE /=.
rewrite (poly_of_qpolyX) qpolyXE // mk_qpolyE //.
rewrite -[in RHS](subrK 1 'X^n) rmodpD //.
rewrite [rmodp 1 h]rmodp_small ?size_poly1 //.
rewrite -[1%:P]add0r polyC1 /= eqr_add2r.
by rewrite dvdpE /=; apply/rmodp_eq0P/eqP.
Qed.

Lemma card_finField_gt0 : 0 < (#|F|^(size h).-1).-1.
Proof.
have cF : 1 < #|F|.
  by rewrite (cardD1 0) inE ltnS (cardD1 1) !inE oner_eq0.
rewrite -ltnS prednK ?expn_gt0 ?(leq_ltn_trans _ cF) //.
rewrite -[1%N](exp1n (size h).-1) ltn_exp2r //.
by rewrite  -ltnS prednK // (leq_ltn_trans _ sh_gt2).
Qed.

Lemma gX_order : #[gX]%g  = (#|F|^(size h).-1).-1.
Proof.
have /primitive_polyP[Hp1 Hp2 Hp3] := Hh.
set n := _.-1 in Hp2 Hp3 *.
have [hM hI] := primitive_mi.
have gX_neq1 : gX != 1%g.
  apply/eqP/val_eqP/eqP/val_eqP=> /=.
  rewrite [X in X != _]qpolyXE /= //.
  by apply/eqP=> Hx1; have := @size_polyX F; rewrite Hx1 size_poly1.
have Hx : (gX ^+ n)%g = 1%g by apply/eqP; rewrite -dvdp_order.
have Hf i : 0 < i < n -> (gX ^+ i != 1)%g by rewrite -dvdp_order => /Hp3.
have o_gt0 : 0 < #[gX]%g by rewrite order_gt0.
have : n <= #[gX]%g.
  rewrite leqNgt; apply/negP=> oLx.
  have /Hf/eqP[] : 0 < #[gX]%g < n by rewrite o_gt0.
  by rewrite expg_order.
case: ltngtP => nLo _ //.
have: uniq (path.traject (mulg gX) 1%g #[gX]%g).
  by apply/card_uniqP; rewrite path.size_traject -(eq_card (cycle_traject gX)).
case: #[gX]%g o_gt0 nLo => //= n1 _ nLn1 /andP[/negP[]].
apply/path.trajectP; exists n.-1; first by rewrite prednK ?card_finField_gt0.
rewrite -iterSr prednK ?card_finField_gt0 // -[LHS]Hx.
by elim: (n) => //= n2 <-; rewrite expgS.
Qed.

Lemma card_finField_unit : #|[set: {unit F}]| = #|F|.-1.
by rewrite -(cardC1 0) cardsT card_sub; apply: eq_card => x; rewrite unitfE.
Qed.

Lemma gX_all : <[gX]>%g = [set: {unit {qfpoly primitive_mi}}]%G.
Proof.
apply/eqP; rewrite eqEcard; apply/andP; split.
  by apply/subsetP=> i; rewrite inE.
rewrite leq_eqVlt; apply/orP; left; apply/eqP.
rewrite -orderE gX_order -[in RHS](mk_qpolyE primitive_mi).
rewrite -card_qpoly -(cardC1 (0 : {qfpoly primitive_mi})) cardsT card_sub.
by apply: eq_card => x; rewrite unitfE.
Qed.

Definition qlog (p : {qfpoly primitive_mi}) : nat := 
  odflt (Ordinal card_finField_gt0) 
        (pick [pred i in 'I_(#|F|^(size h).-1).-1 | 'qX ^+ i == p]). 

Lemma qlog_lt p : qlog p < (#|F|^(size h).-1).-1.
Proof. by rewrite /qlog; case: pickP. Qed.

Lemma qlog_eq (p : {qfpoly primitive_mi}) : p != 0 -> 'qX ^+ (qlog p) = p.
Proof.
move=> p_neq0.
have Up : p \in GRing.unit by rewrite unitfE.
pose gp : {unit {qfpoly primitive_mi}}:= FinRing.unit _ Up.
have /cyclePmin[i iLc iX] : gp \in <[gX]>%g by rewrite gX_all inE.
rewrite gX_order in iLc.
rewrite /qlog; case: pickP => [j /eqP//|/(_ (Ordinal iLc))] /eqP[].
by have /val_eqP/eqP/= := iX; rewrite FinRing.val_unitX.
Qed. 

End PrimitivePoly.

Section PLog.

Variable F : finFieldType.

Definition plog (p q : {poly F}) :=
  if boolP (2 < size p) is AltTrue sp_gt2 then 
    if boolP (primitive_poly p) is AltTrue Hh then 
       qlog sp_gt2 ((in_qpoly p q) : {qfpoly primitive_mi Hh})
    else 0%N
  else 0%N.

Lemma plog_lt (p q : {poly F}) :
  2 < size p -> plog p q < (#|F|^(size p).-1).-1.
Proof.
move=> sp_gt2.
have cF := card_finField_gt0 sp_gt2.
rewrite /plog.
case (boolP (2 < size p)) => // sp_gt2'.
case (boolP (primitive_poly p)) => // Hh.
by apply: qlog_lt.
Qed.

Lemma plog_eq (p q : {poly F}) :
  2 < size p -> primitive_poly p -> ~~ (p %| q) -> p %| q - 'X ^+ plog p q.
Proof.
move=> sp_gt2 Hh pNDq.
have cF := card_finField_gt0 sp_gt2.
rewrite /plog.
case (boolP (2 < size p)) => // sp_gt2'; last by case/negP: sp_gt2'.
case (boolP (primitive_poly p)) => // Hh'; last by case/negP: Hh'.
have pM : p \is monic by case/and4P: Hh'.
have pMi : monic_irreducible_poly p by apply: primitive_mi.
set q' : {qfpoly primitive_mi Hh'} := in_qpoly p q.
apply/modp_eq0P; rewrite modpD modpN; apply/eqP; rewrite subr_eq0; apply/eqP.
rewrite !Pdiv.IdomainMonic.modpE //=.
suff /val_eqP/eqP/= : 'qX ^+ qlog sp_gt2' q' = q'.
  rewrite /= [X in rmodp _ X]mk_qpolyE // => <-.
  by rewrite poly_of_qpolyX /= mk_qpolyE // [rmodp 'X p]rmodp_small ?size_polyX.
apply: qlog_eq.
apply/eqP=> /val_eqP/eqP.
rewrite /= mk_qpolyE // => /rmodp_eq0P; rewrite -dvdpE => pDq.
by case/negP: pNDq.
Qed.

End PLog.

