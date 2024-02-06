From mathcomp Require Import all_ssreflect all_fingroup all_field.
From mathcomp Require Import ssralg finalg poly polydiv zmodp vector qpoly.
From mathcomp Require cyclic.
Require Import more_thm rootn lcm_lbound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(******************************************************************************)
(*                                                                            *)
(*  This is a direct transcription of the correctness proof of the            *)
(*  AKS algorithm as given for HOL4 by Hing Lun Chan in his PhD thesis        *) 
(*                                                                            *)
(******************************************************************************)

Section AKS.
Import Pdiv.CommonRing.
Import Pdiv.RingMonic.

Definition introspective {R : ringType} n k (p : {poly R}) :=
  rmodp (p ^+ n) ('X^k - 1)  == rmodp (p \Po 'X^n) ('X^k - 1).

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").

Lemma introspective1l (R : ringType) k (p : {poly R}) : 1 ⋈[k] p.
Proof. by rewrite /introspective expr1 comp_polyXr. Qed.

Lemma introspective1r (R : ringType) n k : n ⋈[k] (1 : {poly R}).
Proof. by rewrite /introspective expr1n comp_polyC polyC1. Qed.

Lemma introspectiveX (R : ringType) k n : n ⋈[k] ('X : {poly R}).
Proof. by rewrite /introspective comp_polyX. Qed.


(* 98 *)
Lemma introspec_char (F : finFieldType) (k p c : nat) :
  p \in [char F] -> p ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> pC; apply/eqP; congr (rmodp _  _).
have Pp : prime p by apply: charf_prime pC.
have Cn : [char F].-nat p by rewrite pnatE.
rewrite comp_polyD comp_polyC comp_polyX.
rewrite exprDn_char; first by rewrite -polyC_exp fin_little_fermat.
by rewrite pnatE // (rmorph_char (GRing.RMorphism.clone _ _ _ polyC)).
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
  rewrite comp_poly_exp => /eqP->.
  by rewrite -comp_polyA comp_Xn_poly -exprM.
have XM : ('X^k.+1 - 1 : {poly R}) \is monic.
  rewrite qualifE /= lead_coefDl ?lead_coefXn ?unitr1 //.
  by rewrite size_polyXn size_opp size_polyC oner_neq0.
rewrite /introspective exprM -rmodpX // (eqP mIp) rmodpX //.
rewrite exprM -['X^m.+1 ^+_]comp_Xn_poly comp_poly_exp comp_polyA.
rewrite -subr_eq0 -rmodpB // -comp_polyB.
apply: rdvdp_trans (_ : rdvdp (('X^k.+1 -1) \Po 'X^m.+1) _) => //.
- by apply: monic_comp_poly => //; rewrite qualifE /= lead_coefXn.
- rewrite comp_polyB comp_Xn_poly comp_polyC -exprM mulnC exprM.
  by apply: dvdp_geom.
apply: rdvdp_comp_poly => //; first by rewrite qualifE /= lead_coefXn.
by rewrite /rdvdp rmodpB // subr_eq0.
Qed.

(* 100 *)
Lemma introspecMr (R : comRingType) (k n : nat) (p q : {poly R}) :
  n ⋈[k] p -> n ⋈[k] q -> n ⋈[k] (p * q).
Proof.
case: k => [|k nIp nIq].
  rewrite /introspective !subrr !rmodp0.
  by rewrite comp_polyM exprMn => /eqP-> /eqP->.
have Xlf := monic_Xn_sub_1 R (isT : 0 < k.+1).
rewrite /introspective exprMn -rmodp_mulmr // (eqP nIq).
rewrite rmodp_mulmr // mulrC.
rewrite -rmodp_mulmr // (eqP nIp) rmodp_mulmr //.
by rewrite mulrC comp_polyM.
Qed.

(* 102 *)
Lemma introspec_fin_div (F : finFieldType) k n p (c : nat) :
  coprime k n -> p \in [char F] -> (p %| n)%N ->
  n ⋈[k] ('X + c%:R%:P : {poly F}) -> (n %/ p) ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> kCn pC pDn nIkX.
have pP : prime p by case/andP: pC.
have k_gt0 : 0 < k.
  case: k {nIkX}kCn pDn pP => //.
  rewrite /coprime gcd0n => /eqP->.
  by rewrite dvdn1 => /eqP->.
  rewrite /introspective -!Pdiv.IdomainMonic.modpE ?monic_Xn_sub_1 //.
have kNZ : k%:R != 0 :> F.
  rewrite -(dvdn_charf pC); apply/negP => pDk.
  move: pP.
  have : (p %| 1)%N by rewrite -(eqP kCn) dvdn_gcd pDk.
  by rewrite dvdn1 => /eqP->.
have pCF : [char {poly F}].-nat p.
  rewrite /pnat prime_gt0 //=; apply/allP => q.
  rewrite primes_prime //= inE => /eqP->.
  rewrite inE pP -polyC_natr polyC_eq0 /=.
  by case/andP : pC.
rewrite -subr_eq0 -modpN -modpD -[_ == 0]/(_ %| _).
rewrite -(separable_exp _ (separable_polyXnsub1 _) (prime_gt0 pP)) //.
rewrite exprDn_char // exprNn_char // -exprM divnK //.
rewrite comp_polyD comp_polyC [_ ^+ p]exprDn_char //.
rewrite comp_poly_exp comp_Xn_poly -exprM divnK //.
rewrite -polyC_exp fin_little_fermat //.
rewrite /dvdp modpD modpN subr_eq0 //.
move: nIkX.
rewrite /introspective -!Pdiv.IdomainMonic.modpE ?monic_Xn_sub_1 //.
by rewrite comp_polyD comp_polyC comp_polyX.
Qed.

(* I've departed from Chan thesis as it is not easy 
   to build non-constructive sets in Coq. So I turn 
   them into properties. Trying to sort things out 
   when doing the proof by contradiction 
 *)

(* This 𝒩 as a predicate *)
Definition is_iexp (R : ringType) (k s m : nat) := 
   coprime m k /\ forall c, 0 < c <= s -> m ⋈[k] ('X + c%:R%:P : {poly R}).

Lemma is_iexp1 (R : ringType) k s : is_iexp R k s 1.
Proof.
split=> [|c cR]; first by rewrite /coprime gcd1n.
by apply: introspective1l.
Qed.

Lemma is_iexp_mul (R : comRingType) k s m1 m2 : 
  is_iexp R k s m1 -> is_iexp R k s m2 -> is_iexp R k s (m1 * m2).
Proof.
move=> [m1Ck Hm1] [m2Ck Hm2]; split; first by rewrite coprimeMl m1Ck.
by move=> c Hc; apply: introspecMl; [apply: Hm1 | apply: Hm2].
Qed.

Lemma is_iexp_X (R : comRingType) k s m n : 
  is_iexp R k s m -> is_iexp R k s (m ^ n).
Proof.
move=> mI; elim: n => [|n IH]; first by apply: is_iexp1.
by rewrite expnS; apply: is_iexp_mul.
Qed.

(* 103 *)
Lemma is_iexp_fin_char (F : finFieldType) k s p :  
  p \in [char F] -> coprime p k -> is_iexp F k s p.
Proof. by move=> pC pCk; split => // c _; apply:  introspec_char. Qed.

Lemma is_iexp_fin_div (F : finFieldType) k s n p :  
  p \in [char F] -> coprime p k -> (p %| n)%N -> 
  is_iexp F k s n -> is_iexp F k s (n %/ p).
Proof. 
move=> pC pCk pDn[nCk nI]; split => [|c cB].
  by have := nCk; rewrite -{1}(divnK pDn) coprimeMl => /andP[].
apply: introspec_fin_div => //; first by rewrite coprime_sym.
by apply: nI.
Qed.

(* This is 𝒫 *)
Definition is_ipoly (R : ringType) (k s : nat) (p : {poly R}):= 
  forall m, is_iexp R k s m -> m ⋈[k] p.

Lemma is_ipoly1 (R : ringType) k s :  is_ipoly k s (1 : {poly R}).
Proof. by move=> m _; apply: introspective1r. Qed.

Lemma is_ipoly_Xaddc (R : ringType) k s c : 
   0 <= c <= s -> is_ipoly k s ('X + c%:R%:P : {poly R}).
Proof.
rewrite leq_eqVlt; case: eqP => /= [<- _ m _|_ cB m [_]]; last by apply.
by rewrite addr0; apply: introspectiveX.
Qed.

(* This is 𝓜_k *)
Definition is_iexpm (R : ringType) (k s mk : nat) :=
   exists2 m, mk = (m %% k)%N & is_iexp R k s m.

Inductive is_iexpm_spec 
     (R : ringType) (k s : nat) (mk : 'Z_k) : bool -> Prop :=
   is_iexpm_spec_true : 
    forall (m : nat),  (mk = m %% k :> nat)%N -> is_iexp R k s m -> 
      @is_iexpm_spec R k s mk true
 | is_iexpm_spec_false :
    (forall (m : nat), is_iexp R k s m -> (mk != m %% k :> nat)%N) -> 
      @is_iexpm_spec R k s mk false.

(* I've put Mk in {set 'Z_k} but its natural ambient is units_Zp! *)
Definition Mk_spec R s k (M : {set 'Z_k}) :=
  (forall x, @is_iexpm_spec R k s x (x \in M)).

Lemma Mk_Cexists R k s :
  classically (exists M : {set 'Z_k}, Mk_spec R s M).
Proof.
rewrite /Mk_spec.
suff : classically (exists M : {set 'Z_k}, 
      forall x : 'Z_k, x \in (enum 'Z_k) -> uniq (enum 'Z_k) -> 
            is_iexpm_spec R s x (x \in M)).
  apply: classic_bind => [[M HM]].
  apply/classicP=> [] []; exists M => x.
  apply: HM => //; first by rewrite mem_enum inE.
  by apply: enum_uniq.
elim: (enum _) => [|a l] //.
  by apply/classicP=> [] []; exists setT=> x; rewrite inE.
apply: classic_bind => [[M HM]].
have /classic_bind := @classic_pick nat
 (fun m => (a = m %% k :> nat)%N /\ is_iexp R k s m).
apply => [] [[ma [maE maI]]|Ha].
  apply/classicP => [] []; exists (a |: M) => x.
  rewrite !inE => /orP[/eqP-> /= /andP[aNIi Ul]|xIl /= /andP[aNIl Ul]].
    by rewrite eqxx; apply: is_iexpm_spec_true maI.
  case: eqP => [xE|_ /=]; first by case/negP: aNIl; rewrite -xE.
  by apply: HM.
apply/classicP => [] []; exists (M :\ a) => x.
rewrite !inE => /orP[/eqP-> /= /andP[aNIi Ul]|xIl /= /andP[aNIl Ul]].
  rewrite eqxx; apply: is_iexpm_spec_false=> m Hm.
  by apply/eqP=> eE; case: (Ha m).
rewrite (_ : x != a); first by by apply: HM.
by apply: contra aNIl => /eqP<-.
Qed.

Lemma is_iexpm1 (R : comRingType) k s (M : {set 'Z_k}) : 
  1 < k -> Mk_spec R s M -> 1 \in M.
Proof.
move=> k_gt1 MS; case: MS => // /(_ 1%N (is_iexp1 _ _ _)).
by rewrite modn_small ?eqxx.
Qed.

Lemma is_iexpm_mul (R : comRingType) k s (M : {set 'Z_k}) x y : 
  1 < k -> Mk_spec R s M -> x \in M -> y \in M -> (x * y) \in M. 
Proof.
move=> k_gt1 MS.
(do 3 case: (MS) => //) => Hm m1 yE m1I m xE mI _ _.
have /eqP[] := Hm _ (is_iexp_mul mI m1I).
by rewrite -modnMml -xE -modnMmr -yE /= {3}Zp_cast.
Qed.

Lemma is_iexpm_X (R : comRingType) k s (M : {set 'Z_k}) x n : 
  1 < k -> Mk_spec R s M -> x \in M -> (x ^+ n) \in M. 
Proof.
move=> k_gt1 MS xM.
elim: n => [|n IH]; first by apply: is_iexpm1.
by rewrite exprS; apply: is_iexpm_mul.
Qed.

(* 104 *)
Lemma is_iexpm_totient R k s (M : {set 'Z_k}) :
  1 < k -> Mk_spec R s M -> #|M| <= totient k.
Proof.
move:M; case: k => [|[|k /= M _ HM]] //.
suff <-: #|[set i in 'I_k.+2 | coprime i k.+2]| = totient k.+2.
  apply/subset_leq_card/subsetP=> x; rewrite !inE; case: HM => // m -> [].
  by rewrite coprime_modl.
rewrite -sum1_card big_mkcond /=.
rewrite totient_count_coprime big_mkord.
by apply: eq_bigr => i _; rewrite inE coprime_sym.
Qed.


(* 104 *)
Lemma is_iexpm_order (R : comRingType) k s (M : {set 'Z_k}) n :
  1 < k -> Mk_spec R s M -> is_iexp R k s n -> order_modn k n <= #|M|.
Proof.
move=> k_gt1 HMk nIN.
have kCn : coprime k n by case: nIN; rewrite coprime_sym.
rewrite order_modnE //; case: insubP => //=  u nE uE.
rewrite -[#[_]%g](card_imset _ val_inj).
apply/subset_leq_card/subsetP => y /imsetP[z /cycleP[i ->] ->].
rewrite FinRing.val_unitX /= uE.
apply: is_iexpm_X (HMk) _ => //.
case: HMk => // /(_ _ nIN) /eqP[] /=.
by rewrite -val_Zp_nat.
Qed.

(* 105 *)
Lemma rmodn_trans {R : ringType} (p q h z : {poly R}) :
  h \is monic -> z \is monic -> rdvdp h z -> 
  rmodp p z = rmodp q z -> rmodp p h  = rmodp q h.
Proof.
move=> hM zM /(rdvdp_trans hM zM) => /(_ (p - q)).
rewrite /rdvdp !rmodpB // !subr_eq0 => H /eqP H1; apply/eqP.
by apply: H.
Qed.

(* 106  we reformulate it because we can't have order for poly directly *)
Lemma poly_order_rmod_inj (R : ringType) (h : {poly R}) k m n :
  h \is monic -> 1 < size h -> 0 < k -> rdvdp h ('X^k - 1) -> 
  m < poly_order h 'X k -> n < poly_order h 'X k ->
  rmodp 'X^m h = rmodp 'X^n h-> m = n.
Proof.
move=> hM hS k_gt0 hDxk.
wlog : m n / m <= n => [Hw |mLn] mLp nLp xmExn.
  case: (leqP m n) => [/Hw|nLm]; first by apply.
  by apply/sym_equal/Hw => //; apply: ltnW.
move: mLn; rewrite leq_eqVlt => /orP[/eqP//|mLn].
have xkE1 :  rmodp 'X^k h = 1.
  move: hDxk; rewrite /rdvdp rmodpB // [rmodp 1 _]rmodp_small.
    by rewrite subr_eq0 => /eqP.
  by rewrite size_polyC oner_neq0.
have [|o_gt0] := leqP (poly_order h 'X k) 0.
  have kB : 0 < k <= k by rewrite k_gt0 leqnn.
  by rewrite leqn0 => /eqP/poly_order_eq0_rmodp /(_ kB) /eqP[].
pose v := (poly_order h 'X k - n + m)%N.
have /poly_order_lt/eqP[] :
     (0 < poly_order h 'X k - n + m < poly_order h 'X k )%nat.
  rewrite (leq_trans _ (_ : 0 + m < _)) //; last first.
    by rewrite ltn_add2r subn_gt0.
  rewrite -{2}[poly_order _ _ _](@subnK m); last by apply: ltnW.
  by rewrite ltn_add2r ltn_sub2l //.
rewrite exprD -rmodp_mulmr // xmExn rmodp_mulmr // -exprD subnK //.
  by apply/eqP/poly_order_gt0_rmodp.
by apply/ltnW.
Qed.

(* 107 *)
Lemma Mk_root_Mk (R : comRingType) (h : {poly R}) k s 
         (M : {set 'Z_k})  (p q : {poly R}) n  :
  Mk_spec R s M ->
  h \is monic -> 1 < size h -> 0 < k -> rdvdp h ('X^k - 1) -> 
  is_ipoly k s p -> is_ipoly k s q -> rmodp p h = rmodp q h ->
  n \in M -> rmodp ((p - q) \Po 'X^n) h = 0.
Proof.
move=> HM hM hS k_gt0 hDxk pI qI phEqh nIM; apply/eqP.
case: HM nIM => // m nE mI _.
have xkM := monic_Xn_sub_1 R k_gt0.
have F : rmodp 'X^n ('X^k - 1) = rmodp 'X^m ('X^k - 1) :> {poly R}.
  have F1 : rmodp 'X^k ('X^k - 1) = 1 :> {poly R}.
    rewrite -{1}['X^k](subrK (1 : {poly R})) addrC rmodpD // rmodpp //.
    by rewrite addr0 rmodp_small // size_polyC oner_eq0 /= size_Xn_sub_1.
    rewrite (divn_eq m k) exprD mulnC exprM.
    rewrite mulrC -rmodp_mulmr // -[in RHS]rmodpX // F1 expr1n.
    by rewrite rmodp_mulmr // mulr1 nE.
rewrite comp_polyB rmodpB // subr_eq0; apply/eqP.
apply: etrans (_ : rmodp (p^+m) h = _).
  apply: rmodn_trans hDxk _ => //.
  rewrite -rmodp_compr // F rmodp_compr //.
  by apply/esym/eqP/pI.
apply: etrans (_ : rmodp (q^+m) h = _).
  by rewrite -rmodpX // phEqh rmodpX.
apply: esym.
apply: rmodn_trans hDxk _ => //.
rewrite -rmodp_compr // F rmodp_compr //.
by apply/esym/eqP/qI.
Qed.

(*108*)
Lemma Mk_rmodp_inj (R : fieldType) (h : {poly R}) k s 
         (M : {set 'Z_k})  (p q : {poly R})  :
  Mk_spec R s M ->
  monic_irreducible_poly h -> 0 < k -> rdvdp h ('X^k - 1) -> 
  poly_order h 'X k = k -> size p <= #|M| -> size q <= #|M| ->
  is_ipoly k s p -> is_ipoly k s q -> rmodp p h = rmodp q h -> p = q.
Proof.
have [|M_gt0] := leqP #|M| 0.
  rewrite leqn0 => /eqP->; rewrite !leqn0 !size_poly_eq0.
  by move=> ? ? ? ? ? /eqP-> /eqP->.
move=> HMk hMI k_gt0 hDxk XoE pS qS pI qI /eqP.
have hS : 1 < size h by case: hMI; case.
have hI : irreducible_poly h by case: hMI.
have hM : h \is monic by case: hMI.
have hQE : mk_monic h = h by rewrite /mk_monic hS hM.
pose l : seq  {poly %/ h with hMI} := 
  map (fun i : 'I_ _ => (in_qpoly h 'X^i)) (enum M).
have Ul : uniq l.
  apply/(uniqP 0) => i j; rewrite !inE size_map -cardE => Hi1 Hj1.
  rewrite  !(nth_map ord0) -?cardE // => /val_eqP /eqP /= HH.
  suff : nth ord0 (enum M) i = nth ord0 (enum M) j.
    by have /(uniqP ord0) := enum_uniq (pred_of_set M); apply=> //; 
       rewrite inE -cardE.
  apply/val_inj => /=; move: HH.
  apply: (poly_order_rmod_inj _ _ k_gt0); rewrite hQE ?XoE //.
  - have: nth ord0 (enum M) i \in M by rewrite -mem_enum mem_nth // -cardE.
    by case: HMk => // m -> _; rewrite ltn_mod //.
  have: nth ord0 (enum M) j \in M by rewrite -mem_enum mem_nth // -cardE.
  by case: HMk => // m -> _; rewrite ltn_mod.
rewrite -subr_eq0 -rmodpB // => /eqP => u.
apply/eqP; rewrite -subr_eq0; apply/eqP/(@map_fpoly_div_inj _ h).
rewrite map_poly0.
apply: roots_geq_poly_eq0 Ul _ => //; last first.
  rewrite (@size_map_poly _ _ (GRing.RMorphism.clone _ _ _ (qfpoly_const hMI))).
  rewrite size_map (leq_trans (size_add _ _)) //=  size_opp.
  by rewrite geq_max -cardE pS.
apply/allP=> i /mapP[j jI ->]; apply/eqP.
rewrite -in_qpoly_comp_horner //.
apply/val_inj => /=.
rewrite hQE //.
apply: Mk_root_Mk => //.
  by apply/eqP; rewrite -subr_eq0 -rmodpB //; apply/eqP.
by rewrite -mem_enum.
Qed.

(* This is 𝒬_h *)
Definition is_iexph (R : ringType) (k s: nat) h ph :=
  exists2 p : {poly R}, ph = in_qpoly h p & is_ipoly k s p.

Inductive is_iexph_spec 
     (R : ringType) (k s : nat) (h : {poly R}) ph : bool -> Prop :=
   is_iexph_spec_true : 
    forall p, ph = in_qpoly h p -> is_ipoly k s p -> 
      @is_iexph_spec R k s h ph true
 | is_iexph_spec_false :
    (forall p, is_ipoly k s p -> ph != in_qpoly h p) -> 
      @is_iexph_spec R k s h ph false.

Definition Qh_spec (R : finRingType) k s (h :{poly R}) 
                   (M : {set {poly %/ h}}) :=
  (forall x, @is_iexph_spec R k s h x (x \in M)).

Lemma Qh_Cexists (R : finRingType) k s (h : {poly R}) :
  classically (exists M : {set {poly %/ h}}, Qh_spec k s M).
Proof.
rewrite /Qh_spec.
suff : classically (exists M : {set {poly %/ h}}, 
      forall x : {poly %/ h}, x \in (enum {poly %/ h}) -> 
            uniq (enum {poly %/ h}) -> 
            is_iexph_spec k s x (x \in M)).
  apply: classic_bind => [[M HM]].
  apply/classicP=> [] []; exists M => x.
  apply: HM; first by rewrite mem_enum inE.
  by apply: enum_uniq.
elim: (enum _) => [|a l] //.
  by apply/classicP=> [] []; exists setT=> x; rewrite inE.
apply: classic_bind => [[M HM]].
have /classic_bind := @classic_pick _
 (fun p : {poly R} => a = in_qpoly h p /\ is_ipoly k s p).
apply => [] [[ma [maE maI]]|Ha].
  apply/classicP => [] []; exists (a |: M) => x.
  rewrite !inE => /orP[/eqP-> /= /andP[aNIi Ul]|xIl /= /andP[aNIl Ul]].
    by rewrite eqxx; apply: is_iexph_spec_true maI.
  case: eqP => [xE|_ /=]; first by case/negP: aNIl; rewrite -xE.
  by apply: HM.
apply/classicP => [] []; exists (M :\ a) => x.
rewrite !inE => /orP[/eqP-> /= /andP[aNIi Ul]|xIl /= /andP[aNIl Ul]].
  rewrite eqxx; apply: is_iexph_spec_false=> m Hm.
  by apply/eqP=> eE; case: (Ha m).
rewrite (_ : x != a); first by by apply: HM.
by apply: contra aNIl => /eqP<-.
Qed.

(*109*)
Lemma lower_bound_card_Qh (F : finFieldType) (h : {poly F}) k s p
         (M : {set 'Z_k}) (Q : {set {poly %/ h}})   :
  Mk_spec F s M -> Qh_spec k s Q -> p \in [char F] -> 1 < order_modn k p ->
  coprime k p -> monic_irreducible_poly h -> 1 < k -> rdvdp h ('X^k - 1) -> 
  poly_order h 'X k = k -> 0 < s < p ->
  2 ^ minn s #|M| <= #|Q|.
Proof.
move=> HMk HQh pC pO_gt1 kCp hMI k_gt1 hDxk XoE sB.
have hQE : mk_monic h = h by rewrite /mk_monic !hMI.
rewrite -/{poly %/ h with hMI} in Q HQh *.
set t := minn _ _.
have Mk_gt1 : 1 < #|M|.
  apply: leq_trans pO_gt1 _.
  apply: is_iexpm_order (HMk) _  => //.
  by apply: is_iexp_fin_char; rewrite // coprime_sym.
have t_gt0 : 0 < t.
  by rewrite leq_min; case/andP: sB => -> _; rewrite ltnW.
have F1 (b : bool) c : 
   c <= s -> is_ipoly k s (('X + (c%:R)%:P :{poly F}) ^+ b).
  case: b => cD; first by rewrite expr1; apply: is_ipoly_Xaddc.
  by rewrite expr0; apply: is_ipoly1.
have F2 (b : bool) c : 
   c <= s -> size (('X + (c%:R)%:P : {poly F})%R ^+ b) <= 2.
  case: b => cD; last by rewrite expr0 size_polyC oner_eq0.
  rewrite (_ : 2%N = maxn(size ('X : {poly F})) (size ((c%:R)%:P : {poly F}))).
    by rewrite expr1 size_add.
  by rewrite size_polyX size_polyC; case: eqP.
pose m := ([ffun i : 'I_t.+1 => i == ord0] |:
           [set i | (i : {ffun 'I_t.+1 -> bool}) ord0 == false]) :\
           [ffun i : 'I_t.+1 => i != ord0].
have mTrue1 x : x \in m -> exists (i : 'I_t.+1), x i == false.
  rewrite !inE => /andP[H /orP[/eqP->|xE]].
    case: (t) t_gt0 x H => // t1  _ x H.
    by exists (inZp 1); rewrite !ffunE /=; case: eqP.
  by exists ord0.
have mTrue2 x : 1 < t -> x \in m -> exists (i : 'I_t.+1), 
     exists j, [/\ j != i, x i = false & x j = false].
  rewrite /m; case: (t) t_gt0 x => // [] [|t1] // _ x _.
  rewrite !inE => /andP[H /orP[/eqP->|/eqP xE]].
    by exists (inZp 1); exists (inZp 2); rewrite !ffunE.
  have [/existsP[i /andP[iE /eqP xiE]]|] :=
      boolP [exists i, (i != ord0) && (x i == false)].
    by exists ord0; exists i.
  rewrite negb_exists => /forallP Hf.
  case/eqP: H; apply/ffunP=> i; rewrite !ffunE.
  case: eqP => [->|/eqP H] //.
  case E : (x i) => //.
  by case/negP: (Hf i); rewrite H // E.
have <- : #|m| = 2 ^ t.
  rewrite cardsDS; last first.
    by apply/subsetP=> j; rewrite !inE => /eqP->; rewrite ffunE eqxx orbT.
  rewrite cardsU !cards1.
  set u := #|_ :&: _|.
  have /eqP->: u  == 0%N.
    rewrite cards_eq0; apply/eqP/setP=> i; rewrite !inE.
    by apply/idP => /andP[/eqP->]; rewrite ffunE eqxx.
  rewrite subn0 addnC addnK.
  have <- : [set [ffun i => if unlift ord0 i is Some v then f v else false]
                | f : {ffun 'I_t -> bool}] = 
            [set i | (i : {ffun 'I_t.+1 -> bool}) ord0 == false].
    apply/setP=> f; rewrite !inE; apply/imsetP/idP=>[[g _ ->]|/eqP fE].
      by rewrite ffunE unlift_none.
    exists [ffun i => f (fintype.lift ord0 i)]; first by rewrite inE.
    apply/ffunP=> j; rewrite ffunE; case: unliftP => [v ->|->] //.
    by rewrite ffunE.
  rewrite card_imset; first by rewrite card_ffun card_bool card_ord.
  move=> f g H; apply/ffunP=> i.
  have := (congr1 (fun f : {ffun _ -> _} => f (fintype.lift ord0 i)) H).
  by rewrite !ffunE liftK.
pose f := fun (b : {ffun 'I_t.+1 -> bool}) (i : 'I_t.+1) =>
        ('X + (i%:R)%:P : {poly F}) ^+ b i.
pose g b : {poly %/ h}:= in_qpoly h (\prod_(i < t.+1) f b i).
have F3 b : b \in m -> size (\prod_(i < t.+1) f b i)%R <= #|M|.
  have vE i : #|((fun i0 : 'I_t.+1 => i0 != i) : pred _)| = t.
    set v := #|_|; rewrite -[t]/(t.+1.-1) -[t.+1]card_ord.
    rewrite -cardsT [in RHS](cardsD1 i) inE /=.
    by apply: eq_card => j; rewrite !inE andbT.
  move: t_gt0; rewrite leq_eqVlt => /orP[/eqP tE1 /mTrue1 [i /eqP iE]| t_gt].
    rewrite (bigD1 i) //= {1}/f; rewrite iE expr0 mul1r.
    apply: leq_trans (size_prod_leq _ _) _ => /=.
    rewrite vE leq_subLR.
  rewrite (leq_ltn_trans _ (_ : (\sum_(j < t.+1 | j != i) 2)  < _)) //.
    apply: leq_sum => j _; apply: F2.
      rewrite -ltnS; apply: leq_trans (ltn_ord j) _.
      by rewrite ltnS geq_minl.
    by rewrite sum_nat_const [#|_|]vE muln2 -addnn ltn_add2l -tE1.
  move=> bM; have [i [j [jDi biE bjE]]] := mTrue2 _ t_gt bM.
  rewrite (bigD1 i) //= {1}/f; rewrite biE expr0 mul1r.
  rewrite (bigD1 j) //=  {1}/f; rewrite bjE expr0 mul1r.
  apply: leq_trans (size_prod_leq _ _) _ => /=.
  set v := #|_|.
  have vE1 : v = t.-1.
    rewrite -[t]/(t.+1.-1) -[t.+1]card_ord.
    rewrite -cardsT [in RHS](cardsD1 i) inE /=.
    rewrite [in RHS](cardsD1 j) !inE /= jDi /=.
    by apply: eq_card => l; rewrite !inE /= andbT andbC.
  rewrite vE1 leq_subLR.
  rewrite (leq_ltn_trans _ (_ : (\sum_(l < t.+1 | (l != i) && (l != j)) 2) 
                                    < _)) //.
    apply: leq_sum => l _; apply: F2.
    rewrite -ltnS; apply: leq_trans (ltn_ord l) _.
    by rewrite ltnS geq_minl.
  rewrite sum_nat_const [#|_|]vE1 muln2 -addnn ltn_add2l.
  by rewrite prednK ?geq_minr // ltnW.
have F4 b : b \in m -> is_ipoly k s (\prod_(i < t.+1) f b i).
  move=> bIm m1 Hm1.
  elim/big_rec: _ => [|i x _ xI]; first by apply: introspective1r.
  apply: introspecMr => //.
  rewrite /f; case: (b i); last by rewrite expr0; apply: introspective1r.
  rewrite expr1; case: (i : nat) (ltn_ord i) => [_|i1].
    by rewrite addr0; apply: introspectiveX.
  rewrite ltnS => i1Lt.
  case: Hm1=> _; apply=> /=; apply: leq_trans i1Lt _.
  by rewrite geq_minl.
suff /card_in_imset<- : {in m &, injective g}.
  rewrite subset_leqif_cards //; apply/subsetP => i /imsetP[/= b bIm ->].
  by case: HQh => // /(_ (\prod_(i < t.+1) f b i) (F4 _ bIm)) /eqP[].
move=> m1 m2 m1I m2I /val_eqP/eqP/= H.
have F5 b (x : 'I_ _) : b \in m -> 
      (\prod_(i < t.+1) f b i).[-(x%:R)] == 0 = (b x).
  move=> bIm; rewrite horner_prod. 
  apply/GRing.prodf_eq0/idP=> /= [[j _]|bxE]; last first.
    by exists x=> //; rewrite /f bxE expr1 !hornerE addrC subrr.
  rewrite /f horner_exp !hornerE; case: (boolP (b j)) => bjE; last first.
    by rewrite expr0 oner_eq0.
  rewrite expr1 addrC.
   rewrite {2}/is_true -{}bjE.
  wlog: x j / x <= j => [Hw|].
    case: (leqP x j)=> [xLj|jLx]; first by apply: Hw.
    rewrite -oppr_eq0 opprB => xjE0.
    by apply/esym/Hw => //; apply: ltnW.
  rewrite leq_eqVlt => /orP[/val_eqP->//|xLhj].
  rewrite -natrB 1?ltnW // -(dvdn_charf pC).
  rewrite gtnNdvd //; first by rewrite subn_gt0.
  apply: leq_ltn_trans (leq_subr _ _) _.
  apply: leq_trans (ltn_ord _) _.
  apply: leq_ltn_trans (geq_minl _ _) _.
  by case/andP: sB.
suff : \prod_(i < t.+1) f m1 i = \prod_(i < t.+1) f m2 i.
  by move=> Hprod; apply/ffunP=> i; rewrite -F5 // Hprod F5.
apply: Mk_rmodp_inj (F3 _ m1I) (F3 _ m2I) (F4 _ m1I) (F4 _ m2I) H => //.
- by rewrite hQE.
- by rewrite ltnW.
- by rewrite hQE.
by rewrite hQE.
Qed.

(* 110 *)
Lemma exp_Mk_upper_bound (R : comRingType) k s n a (M : {set 'Z_k}) :
   Mk_spec R s M -> 1 < #|M| ->
  1 < k -> 1 < n -> isnot_2power n ->
  a = up_log 2 n ^ 2 -> a <= order_modn k n ->
  s = (sqrtn (totient k) * (up_log 2 n))%N ->   
  is_iexp R k s n ->
   n ^ (sqrtn #|M|) < 2 ^ (minn s #|M|).
Proof.
move=> HMk Mk_gt1 k_gt1 m_g1 nNP aE aLo sE nIN.
set j := order_modn k n in aLo.
set m := up_log 2 n in aE sE.
have F1 : j <= #|M| by apply: is_iexpm_order.
have F2 : #|M| <= totient k by apply: is_iexpm_totient.
have F3 : m ^ 2 <= j by  move: aLo; rewrite aE.
apply: leq_trans (_ : (2 ^ m) ^ sqrtn (#|M|) <= _).
  rewrite ltn_exp2r; last first.
    by rewrite sqrtn_gt0 (leq_trans _ (_ : 2 <= _)).
  by have := up_logP n (isT : 1 < 2); rewrite leq_eqVlt (negPf nNP).
case: (leqP s #|M|) => [sLM|MLs].
  by rewrite -expnM leq_exp2l // sE mulnC leq_mul2r // orbC leq_sqrtn.
rewrite -expnM leq_exp2l //.
apply: leq_trans (_ : (sqrtn #|M|) ^ 2 <= _); last first.
  by have /andP[] := sqrtn_bound #|M|.
rewrite expnS expn1 leq_mul2r // orbC.
rewrite (leq_trans _ (_ : sqrtn j <= _)) //; last by apply: leq_sqrtn.
by rewrite -[m]sqrnK leq_sqrtn .
Qed.

Definition Nbar (p q m : nat) :  {set 'I_((p * q) ^ m).+1} := 
  [set inZp (p ^ ij.1 * q ^ ij.2) | ij: 'I_m.+1 * 'I_m.+1].

(* 111 *)
(** As Nbar is defined slightly differently, this is the dual version of     **)
(** 111 for our version                                                      **)
Lemma NbarP (p q m : nat) (x : 'I_ _) :
  1 < p -> 1 < q ->
  reflect (exists (ij : 'I_m.+1 * 'I_m.+1) , x = (p ^ ij.1 * q ^ ij.2)%N :> nat) 
          (x \in Nbar p q m).
Proof.
move=> p_gt1 q_gt1.
apply(iffP imsetP) => [[[i j _ -> /=]]|[[i j ijE]]].
  by exists (i, j); 
     rewrite modn_small // ltnS expnMn leq_mul // leq_exp2l // -ltnS.
exists (i, j) => //; apply/val_inj => /=. 
by rewrite modn_small // ltnS expnMn leq_mul // leq_exp2l // -ltnS.
Qed.

(* 112 *)
Lemma is_iexp_root (F : fieldType) (h : {poly F}) k s m n p :
  0 < k -> monic_irreducible_poly h -> rdvdp h ('X^k - 1) -> 
  is_iexp F k s m -> is_iexp F k s n -> n = m %[mod k] ->
  is_ipoly k s p -> in_qpoly h (('X^n - 'X^m) \Po p) = 0.  
Proof.
move=> k_gt0 hMI hDxk1 mI nI mMn pP.
apply/val_inj; rewrite /= /mk_monic !hMI //= -[RHS](rmod0p h).
pose z : {poly F}:= 'X^k - 1.
have zM : z \is monic by apply: monic_Xn_sub_1.
apply: rmodn_trans hDxk1 _; rewrite ?hMI -/z // rmod0p.
rewrite comp_polyB !comp_Xn_poly rmodpB //.
apply/eqP; rewrite subr_eq0; apply/eqP.
have F0 : rmodp 'X^k z = 1.
  rewrite -['X^k](subrK 1) rmodpD // rmodpp // add0r rmodp_small //.
  by rewrite size_polyC size_Xn_sub_1 ?oner_eq0.
have F1 : rmodp 'X^n z = rmodp 'X^m z.
  rewrite (divn_eq n k) (divn_eq m k) !exprD mMn.
  rewrite ![(_ * k)%N]mulnC !exprM ![_ * 'X^(_ %% _)]mulrC.
  rewrite -rmodp_mulmr // -rmodpX // F0 expr1n rmodp_mulmr // mulr1.
  rewrite -rmodp_mulmr // -[in RHS] rmodpX //.
  by rewrite F0 expr1n rmodp_mulmr // mulr1.
have F2 : rmodp (p ^+ n) z = rmodp (p \Po 'X^n) z by apply/eqP/pP.
have F3 : rmodp (p ^+ m) z = rmodp (p \Po 'X^m) z by apply/eqP/pP.
have F4 : rmodp (p \Po 'X^m) z = rmodp (p \Po 'X^n) z.
  by rewrite -rmodp_compr // -F1  rmodp_compr.
by rewrite F2 -F4 -F3.
Qed.

(* 113 *)
(* in order to be able to talk about Qh I need to limit this theorem to 
   finField *)
Lemma is_iexp_inj (F : finFieldType) (h : {poly F}) k s
     (M : {set 'Z_k}) (Q : {set {poly %/ h}}) p q :
   Mk_spec F s M -> Qh_spec k s Q -> 
  1 < k -> monic_irreducible_poly h -> rdvdp h ('X^k - 1) ->
  1 < p -> is_iexp F k s p -> (1 < q) -> is_iexp F k s q ->
  (p * q) ^ sqrtn #|M| < #|Q| -> 
  {in Nbar p q (sqrtn #|M|) &, injective (fun i : 'I_ _ => inZp i : 'Z_k)}.
Proof.
move=> hMK hQh k_gt1 hMI hDxk1 p_gt1 pIN q_gt1 qIN pqLqh i j iIN jIN.
move=> /(congr1 val); rewrite /= [X in  _ = _ %[mod X]]Zp_cast // => imEjm.
have k_gt0 : 0 < k by rewrite -ltnS ltnW.
pose r := map_poly (qfpoly_const hMI) ('X^i - 'X^j).
suff : r == 0.
  rewrite /r rmorphB /= subr_eq0 => /eqP/map_poly_div_inj.
  move=> /(congr1 (size : {poly F} -> nat)).
  by rewrite !size_polyXn => [] [] /eqP /val_eqP.
apply/eqP/(@roots_geq_poly_eq0
      (GRing.IntegralDomain.clone _ {poly %/ h with hMI}) _ (enum Q)).
- apply/allP => /= x.
  rewrite mem_enum; case: hQh => // p1 -> p1I _.
  apply/eqP; rewrite -in_qpoly_comp_horner.
  apply: is_iexp_root p1I => //.
    case/imsetP: jIN => [[i1 j1] _ -> /=].
    rewrite modn_small.
      by apply: is_iexp_mul; apply: is_iexp_X.
    by rewrite ltnS expnMn leq_mul // leq_exp2l // -ltnS.
  case/imsetP: iIN => [[i1 j1] _ -> /=].
  rewrite modn_small.
    by apply: is_iexp_mul; apply: is_iexp_X.
  by rewrite ltnS expnMn leq_mul // leq_exp2l // -ltnS.
- by apply: enum_uniq.
rewrite -cardE.
apply: leq_trans pqLqh.
rewrite /r rmorphB /= !map_polyXn.
apply: leq_trans (size_add _ _) _.
by rewrite size_opp !size_polyXn geq_max !ltn_ord.
Qed.

Definition poly_intro_range (R : ringType) k n s :=
  forall c, 0 < c <= s-> 
  rmodp (('X + c%:R%:P)^+n) ('X^k - 1 : {poly R}) = 
  rmodp ('X^n + c%:R%:P) ('X^k - 1).
  
Definition aks_criteria (R : ringType) n k :=
 [/\ 0 < n, 0 < k, 
  (forall p, p \in [char R] -> [/\ 1 < order_modn k p, (p %| n)%N & k < p]),
    up_log 2 n ^ 2 <= order_modn k n &
   poly_intro_range R k n (sqrtn (totient k) * up_log 2 n)
 ].

Lemma card_Nbar p q m : prime p -> 1 < q -> ~ is_power q p -> 
   #|Nbar p q m| = m.+1 ^ 2.
Proof.
move=> pP q_gt1 pCq.
have p_gt1 := prime_gt1 pP.
rewrite card_imset=> [|/= [i1 j1] [i2 j2] /(congr1 val)].
  by rewrite card_prod card_ord expnS expn1.
rewrite /= !modn_small //; last 2 first.
- by rewrite ltnS expnMn leq_mul // leq_exp2l // -ltnS.
- by rewrite ltnS expnMn leq_mul // leq_exp2l // -ltnS.
wlog i1Li2 : i1 i2 j1 j2 / i1 <= i2 => H.
  case: (leqP i1 i2) =>  [i1Li2|i2Li1]; first by apply H.
  by move=> Hi; apply/sym_equal/H; rewrite 1?ltnW.
suff [H1 H2] : (i1 : nat, j1 : nat) = (i2 : nat, j2 : nat).
  by congr (_, _); apply: val_inj.
move: (i1Li2) H; rewrite leq_eqVlt => /orP[/eqP<-|i1LEi2 /eqP].
  move/eqP; rewrite eqn_pmul2l; last by rewrite expn_gt0 ltnW.
  by rewrite eqn_exp2l => // /eqP<-.
rewrite -{1}(subnK i1Li2) addnC expnD -mulnA eqn_pmul2l; last first.
  by rewrite expn_gt0 prime_gt0.
case: (leqP j2 j1) => [j1Lj2|j2Lj1].
  rewrite -{1}(subnK j1Lj2) expnD eqn_pmul2r; last by rewrite expn_gt0 ltnW.
  move: j1Lj2; rewrite leq_eqVlt => /orP[/eqP<-|].
    rewrite subnn expn0 eq_sym.
    move: i1LEi2; rewrite -subn_gt0; case: (_ - _)%N=> // k _.
    by rewrite expnS muln_eq1; case: (p) p_gt1 => // [] [].
  rewrite -subn_gt0 => j1j2_gt0 /eqP qE.
  case: pCq; apply: prime_is_power_exp j1j2_gt0 _ => //.
  by rewrite qE is_power_exp.
have j1LEj2 : j1 <= j2 by rewrite ltnW.
rewrite -[_ ^ _]mul1n -{1}(subnK j1LEj2) expnD mulnA.
rewrite eqn_pmul2r; last by rewrite expn_gt0 ltnW.
move: i1LEi2; rewrite -subn_gt0; case: (_ - _)%N => // k _.
by rewrite expnS -mulnA eq_sym muln_eq1; case: (p) p_gt1 => // [] [].
Qed.

(* 96 *)
Lemma cyclotomic_special_order k p :
 (prime p -> 0 < k -> 1 < order_modn k p -> 
   exists h : {poly 'F_p}, [/\ monic_irreducible_poly h, (h %| 'X^k - 1)%R, 
                            size h = (order_modn k p).+1 & poly_order h 'X k = k] 
  )%N.
Proof.
set d := order_modn _ _.
move=> pP k_gt0 d_gt1.
have p_gt1 := prime_gt1 pP.
have k_gt1 :=  order_modn_gt1 d_gt1.
have kCp := order_modn_coprime d_gt1.
have d_gt0 : 0 < d by apply: leq_trans d_gt1.
have /= [L LC] := Fp_splittingField pP d_gt0.
set m := p ^ d in LC.
have m_gt1: m > 1 by rewrite (ltn_exp2l 0) ?prime_gt1.
have m_gt0 := ltnW m_gt1; have m1_gt0: m.-1 > 0 by rewrite -ltnS prednK.
pose Fm := FinFieldExtType L.
have /hasP[x _ xE] :
    has (m.-1).-primitive_root [seq val i | i <-
             enum (Finite.clone _ {unit Fm})].
  apply: cyclic.has_prim_root => //.
  - apply/allP => i /mapP[/= x _ -> /=].
    apply/unity_rootP => /=.
    rewrite -FinRing.val_unitX -(_ : #|[set : {unit Fm}]%g| = m.-1).
      by rewrite cyclic.expg_cardG ?inE.
    by rewrite card_finField_unit LC.
  - rewrite map_inj_uniq; first by apply: enum_uniq.
    by apply: val_inj. 
  by rewrite size_map -cardE -cardsT card_finField_unit LC.
have kDm1 : (k %| m.-1)%N by rewrite -subn1 -eqn_mod_dvd // order_modn_exp.
have mkDm1 : (m.-1 %/ k %| m.-1)%N.
  by apply/dvdnP; exists k; rewrite mulnC divnK.
pose z :=  x ^+ (m.-1 %/ k).
have kPr : k.-primitive_root z.
  rewrite {1}(_ : k = m.-1 %/ gcdn (m.-1 %/ k) m.-1)%N //.
    by apply: exp_prim_root.
  by rewrite (gcdn_idPl mkDm1) divnA // mulnC mulnK.
have /polyOver1P[h hE] := minPolyOver 1 z.
have g1L : galois 1%AS {: L}%AS.
  by apply: finField_galois (sub1v _).
pose g := ('Gal({: L}%AS /<<1; z>>))%G.
pose E := <<1; z>>%VS.
pose e := \dim E.
have dE : d = \dim {: L}.
  have /eqP := @card_vspace _ Fm _ {:L}.
  by rewrite card_vspacef LC card_Fp // eqn_exp2l // => /eqP.
have eDd : (e %| d)%N.
  by rewrite dE; apply/field_dimS/subvf.
have kDpe : (k %| (p ^ e).-1)%N.
  rewrite (prim_order_dvd kPr) -subn1 expfB ?expr1; last first.
    by rewrite -(exp1n e) ltn_exp2r ?prime_gt1 // adim_gt0.
  have: z \in E by apply: memv_adjoin.
  rewrite Fermat's_little_theorem -/E card_Fp -/e // => /eqP->.
  rewrite divff //.
  apply/eqP=> zE0; have /eqP := prim_expr_order kPr.
  by rewrite zE0 expr0n eqn0Ngt k_gt0 eq_sym oner_eq0.
have peE1 : p ^ e = 1 %[mod k].
  rewrite -[_ ^ _]prednK ?expn_gt0 ?prime_gt0 //.
  by rewrite -addn1 -modnDm (eqP kDpe) add0n modn_mod.
have hS : size h = d.+1.
  have := size_minPoly 1%AS z.
  rewrite /adjoin_degree dimv1 divn1 -/E -/e.
  rewrite hE size_map_poly prednK ?adim_gt0 // => ->.
  congr (_.+1); apply/eqP; rewrite eqn_dvd.
  apply/andP; split.
    by rewrite dE; apply/field_dimS/subvf.
  rewrite /d order_modnE //; case: insubP => [u|/negP[]]; rewrite !unitZpE //=.
  move=> _ uE.
  rewrite cyclic.order_dvdn.
  apply/eqP/val_eqP.
  rewrite FinRing.val_unitX /= uE.
  rewrite -natrX.
  by rewrite -(Zp_nat_mod k_gt1) peE1 modn_small //.
have minD : minPoly 1%AS z %| 'X^k - 1.
  apply: minPoly_dvdp.
    Time by rewrite !rpredB //= ?rpredX //= ?polyOverX //= ?rpred1 //=.
    (* by rewrite !(rpredB, rpredX, polyOverX, rpred1). *)
  rewrite rootE !hornerE -exprM divnK //.
  by rewrite prim_expr_order // subrr.
have hD : h %| 'X^k - 1.
  move: minD.
  have ->: 'X^k - 1 = map_poly (in_alg L) ('X^k - 1).
    by rewrite raddfB /= rmorphXn /= map_polyX /= rmorph1.
  by rewrite hE dvdp_map.
have hM : h \is monic.
  have := monic_minPoly 1 z.
  by rewrite hE map_monic.
exists h; split => //.
- split => //.
  split=> [|p1 Sp1 p1Dh]; first by rewrite hS.
  pose fp1 := map_poly (in_alg L) p1.
  have /(minPoly_irr (alg_polyOver _ _))/orP[] : 
      fp1 %| minPoly 1%AS z by rewrite hE dvdp_map.
    by rewrite hE eqp_map.
  rewrite  -(_ : map_poly (in_alg L) 1 = 1).
    by rewrite eqp_map -size_poly_eq1 (negPf Sp1).
  by rewrite map_polyC /= scale1r.
apply: poly_orderE=> [||k1 k1_gt0 /eqP]; first by rewrite k_gt0 leqnn.
  apply/eqP; rewrite -[1](@rmodp_small _ _ h) ?size_poly1 ?hS //.
  rewrite -subr_eq0 -rmodpB //.
  by rewrite -[_ == 0]/(rdvdp h ('X^k - 1)) -dvdpE.
rewrite -[1](@rmodp_small _ _ h) ?size_poly1 ?hS //.
rewrite -subr_eq0 -rmodpB //.
rewrite -[_ == 0]/(rdvdp h ('X^k1 - 1)) -dvdpE => hDk1.
apply: dvdn_leq => //.
suff: minPoly 1%AS z %| 'X^k1 - 1.
  move=> Hk1.
  rewrite (prim_order_dvd kPr).
  have : ('X^k1 - 1).[z] == 0.
    by case/dvdpP: Hk1 => r ->; rewrite hornerE minPolyxx mulr0.
  by rewrite !hornerE subr_eq0.
rewrite hE.
have ->: 'X^k1 - 1 = map_poly (in_alg L) ('X^k1 - 1).
  by rewrite raddfB /= rmorphXn /= map_polyX /= rmorph1.
by rewrite dvdp_map.
Time Qed.

(*115 *)
Lemma main_aks p n k (F := (FinRing.Ring.clone _ 'F_p)) :
  prime p -> aks_criteria F n k -> is_power n p.
Proof.
move=> pP; have p_gt1 := prime_gt1 pP.
have pC : p \in [char F] by apply: char_Fp.
pose a := (up_log 2 n) ^ 2; pose s := (sqrtn (totient k) * up_log 2 n)%N.
move => [n_gt0 k_gt0 /(_ p pC) [pO_gt1 pDn kLp lnLnO Hr]].
have k_gt1 : 1 < k by apply: order_modn_gt1 pO_gt1.
have := dvdn_leq n_gt0 pDn.
rewrite leq_eqVlt => /orP[/eqP<-|pLn]; first by rewrite is_power_id.
have [/eqP nE|/negP nis2p] := boolP (is_2power n).
  move: pDn; rewrite nE.
  rewrite Euclid_dvdX // => /andP[/prime_nt_dvdP->] //.
    by move=> _; apply: is_power_exp.
  by case: (p) pP => // [] // [].
have n_gt1 : 1 < n.
  apply: leq_trans (prime_gt1 pP) _.
  by apply: dvdn_leq.
have n_gt2 : 2 < n by case: (n) n_gt1 nis2p => [|[|[|]]].
have kCn : coprime k n.
  apply: order_modn_coprime.
  apply: leq_trans lnLnO.
  rewrite (@ltn_exp2r 1 _ 2) //.
  by apply: (@leq_up_log 2 3).
have kCp : coprime k p by apply: order_modn_coprime.
have nI : is_iexp (GRing.Ring.clone _ 'F_p) k s n.
  split => [|c cB]; first by rewrite coprime_sym.
  apply/eqP.
  rewrite comp_polyD comp_polyC comp_polyX.
  by apply: Hr.
have [h [hMI hDxk1 jS hO]]:= cyclotomic_special_order pP k_gt0 pO_gt1.
have [//|/negP nP] := boolP (is_power n p).
have /classicP[] := @Mk_Cexists F k s.
move=> [M hMk].
have /classicP[] := @Qh_Cexists F k s h.
move=> [Q hQh].
pose t := #|M|.
have t_gt1 : 1 < t.
  apply: leq_trans pO_gt1 _.
  apply: is_iexpm_order (hMk) _ => //.
  apply: is_iexp_fin_char; first by apply: char_Fp.
  by rewrite coprime_sym.
have nLst : n ^ sqrtn t < 2 ^ minn s t.
  apply: exp_Mk_upper_bound hMk _ _ _ _ _ _ _  _ => //.
  by apply/negP.
have stLQ : 2 ^ minn s t <= #|Q|.
  apply: (@lower_bound_card_Qh _ _ _ _ p) => //; first by rewrite -dvdpE.
  rewrite muln_gt0 sqrtn_gt0 totient_gt0 k_gt0.
  rewrite (@leq_up_log 2 2) //=.
  apply: leq_trans (kLp).
  rewrite ltnS.
  apply: leq_trans (totient_leq _).
  have /andP[/(leq_trans _)->//] := sqrtn_bound (totient k).
  rewrite expnS expn1 leq_mul2l -(sqrnK (up_log 2 n)).
  rewrite leq_sqrtn ?orbT //.
  by apply: leq_trans (leq_order_totient n _).
pose q := (n %/ p)%N.
have nE : n = (q * p)%N.
  by rewrite [n](divn_eq _ p) (eqP pDn) addn0.
have q_gt1 : 1 < q.
  case: leqP => //.
  move: n_gt1 nP; rewrite nE.
  by case: (q) => [|[|]] // _ []; rewrite mul1n is_power_id.
have pI : is_iexp F k s p by apply: is_iexp_fin_char; rewrite 1? coprime_sym.
have qI : is_iexp F k s q by apply: is_iexp_fin_div; rewrite 1? coprime_sym.
pose N1 := Nbar p q (sqrtn t).
pose f := fun i : 'I_((p * q) ^ sqrtn t).+1 => inZp i : 'Z_k.
have : #|f @: N1| <= t.
  apply/subset_leq_card/subsetP => x /imsetP[y /imsetP[/= [i1 j1 _]-> -> /=]].
  set m := (_ ^ _ * _)%N.
  have mI : is_iexp F k s m.
    by apply: is_iexp_mul; apply: is_iexp_X.
  case: hMk => //= /(_ _ mI)/eqP[].
  rewrite /= Zp_cast // [(m %% _)%N]modn_small //.
  by rewrite ltnS expnMn leq_mul // leq_exp2l // -ltnS.
rewrite leqNgt=> /negP[].
rewrite card_in_imset; last first.
  apply: (is_iexp_inj hMk hQh) => //; first by rewrite -dvdpE.
  rewrite mulnC -nE.
  by apply: leq_trans stLQ.
rewrite card_Nbar //; last first.
  move=> H; case: nP.
  by rewrite nE (eqP H) -expnSr is_power_exp.
by have /andP[] := sqrtn_bound t.
Qed.

(******************************************************************************)
(* Now that we have the main theorem we can start building the algorithm      *)
(******************************************************************************)


(******************************************************************************)
(*    Power Free                                                              *)
(******************************************************************************)

Fixpoint power_free (n : nat) k :=
  if k is k1.+1 then 
    if k1 is _.+1 then 
      if is_rootn k n then false
      else power_free n k1
    else (1 < n) 
  else (1 < n).

Lemma power_freeSS n k : 
  power_free n k.+2 = if is_rootn k.+2 n then false else power_free n k.+1.
Proof. by []. Qed.

Compute (fun n => power_free n (up_log 2 n)) 128%N.

Lemma power_freePn n :
  ~~ power_free n (up_log 2 n) -> 
  exists m, exists2 k, 1 < k & n = m ^ k.
Proof.
elim: up_log => [|[|k] IH].
- case: n => [|[|n]] //= _; first by exists 0%N; exists 2%N.
  by exists 1%N; exists 2%N.
- case: {IH}n => [|[|n]] //= _; first by exists 0%N; exists 2%N.
  by exists 1%N; exists 2%N.
rewrite power_freeSS is_rootnE //.
case: (n =P rootn k.+2 n ^ k.+2) => [-> _|_].
  by exists (rootn k.+2 n); exists k.+2.
by case: k IH.
Qed.

Lemma power_freeP n m k :
  power_free n (up_log 2 n) -> n = m ^ k -> k = 1%N.
Proof.
move=> pH nE.
have: k <= up_log 2 n.
  case: m pH nE => [|[|m]] //.
  - by case: k => // k; rewrite exp0n; case: n.
  - by rewrite exp1n; case: n => [|[|]].
  move=> pH nE.
  have m_gt1 : 1 < m.+2 by [].
  rewrite -(leq_exp2l _ _ m_gt1).
  rewrite -nE.
  apply: leq_trans (up_logP _ (isT : 1 < 2)) _.
  rewrite leq_exp2r // up_log_gt0.
  by case: (n) pH => [|[|]].
elim: up_log pH => [|[|k1] IH].
- by case: k nE => //=; case: n => [|[|]].
- by case: {IH}k nE => [|[|k]] //=; case: n => [|[|]].
rewrite power_freeSS; case E: is_rootn => // pH.
rewrite leq_eqVlt => /orP[/eqP kE |kLk1]; last by apply: IH.
move: E; rewrite is_rootnE // [in rootn _ _]nE kE.
by rewrite expnK // -kE -nE eqxx.
Qed.

(******************************************************************************)
(*    aks_param search                                                        *)
(******************************************************************************)

Inductive aks_param_res := nice of nat | bad | good of nat.

Fixpoint aks_param_search n a k c := 
  if c is c1.+1 then
    if (k %| n)%nat then nice k
    else if (a <= k) && (a <= order_modn k n) then good k
    else aks_param_search n a k.+1 c1
  else bad.

Lemma aks_param_search_goodP (n a k c r : nat) :
  aks_param_search n a k c = good r ->
  [/\  a <= r < k + c, a <= order_modn r n &
       forall j, k <= j <= r -> ~~ (j %| n)%nat].
Proof.
elim: c k => //= c IH k.
have [//|ND] := boolP (_ %| _)%N.
have [/andP[aLk aLo]|aLko] := boolP (_ && _).
  case => <-; split => // [| j].
    by rewrite aLk addnS ltnS leq_addr.
  by rewrite -eqn_leq => /eqP<-.
have {IH} := IH k.+1.
case: aks_param_search => // r1 IH Hi.
have := IH Hi; rewrite addnS => [] [H1 H2 H3].
split=> // j /andP[].
rewrite leq_eqVlt => /orP[/eqP<-//| kLj jLn1].
by apply: H3; rewrite kLj.
Qed.

Lemma aks_param_search_niceP (n a k c r : nat) :
  aks_param_search n a k c = nice r ->
  [/\  k <= r < k + c, (r %| n)%nat &
       forall j, k <= j < r -> ~~ (j %| n)%nat].
Proof.
elim: c k => //= c IH k.
have [kDn [<-]|ND] := boolP (_ %| _)%N.
  split=> [||j] //; first by rewrite leqnn addnS ltnS leq_addr.
  by case: ltnP.
have [//|aLko] := boolP (_ && _).
have {IH} := IH k.+1.
case: aks_param_search => // r1 IH Hi.
have := IH Hi; rewrite addnS => [] [/andP[H1 H2] H3 H4].
split=> [||j /andP[]] //; first by rewrite ltnW.
rewrite leq_eqVlt => /orP[/eqP<-//| kLj jLn1].
by apply: H4; rewrite kLj.
Qed.

Lemma aks_param_search_badP (n a k c : nat) :
  aks_param_search n a k c = bad ->
  (forall j , k <= j < k + c -> ~~(j %| n)%nat /\ order_modn j n < a).
Proof.
elim: c k => /= [k _ j|c IH k]; first by rewrite addn0; case: ltnP.
have [//|ND] := boolP (_ %| _)%N.
case: (leqP a k) => /= [aLk|kLa Hs j /andP[]] //.
  case: leqP => /= [aLo|oLa Hs j /andP[]] //.
  rewrite addnS leq_eqVlt => /orP[/eqP<- _|kLj jLkc]; first by split.
  by apply: (IH k.+1); rewrite // kLj.
rewrite addnS leq_eqVlt => /orP[/eqP<- _|kLj jLkc].
  split=> //.
  case: (k) kLa => [|k1 k1La].
    by rewrite /order_modn andbF.
  apply: leq_trans k1La.
  apply: leq_trans (leq_order_totient _ _) _ => //.
  by apply: totient_leq.
by apply: (IH k.+1); rewrite ?kLj.
Qed.

Definition aks_param n l := 
  let a := l ^ 2 in
  let k := 2%N in
  let c := (l * (a ^ 2))./2  in
  if l <= 1 then nice n else aks_param_search n a k c.

(* This summarizes 63 64 66 *)
Lemma aks_paramP n :
  if aks_param n (up_log 2 n) is good k then
  [/\ 1 < k < n,
      forall j, 1 < j <= k -> ~~ (j %| n)%nat,
      k <= (up_log 2 n * (up_log 2 n ^ 2) ^ 2)./2.+1,
      coprime k n & (up_log 2 n) ^ 2 <= order_modn k n]
  else if aks_param n (up_log 2 n) is nice k then
  1 < n ->
  [/\ 1 < k, if n == 2%N then k == 2%N 
             else k <= (up_log 2 n * (up_log 2 n ^ 2) ^ 2)./2.+1,
      (k %| n)%N & forall j, 1 < j < k -> ~~ (j %| n)%N]
  else False.
Proof.
rewrite /aks_param; case: (leqP (up_log 2 n) 1) => [l_gt1 | l_gt1].
  rewrite leq_eqVlt => /orP[/eqP<-|n_gt2].
    by split => // [] [|[|]].
  move: l_gt1; rewrite leqNgt => /negP[].
  rewrite  -[2%N]/(up_log 2 3).
  by apply: leq_up_log.
have n_gt1 : 1 < n by case: n l_gt1 => [|[|]].
set a := up_log 2 n ^ 2.
have a_gt1 : 1 < a by rewrite (ltn_sqr 1).
case E : aks_param_search => [k||k] //.
- move=> _.
  have [/andP[H1 H2] H3 H4]:= aks_param_search_niceP E.
  split => //.
  case: eqP => [nE|_].
    have : k <= n.
      by apply: dvdn_leq => //; rewrite ltnW.
    move: H1 H3; rewrite nE.
    by case: (k) => [|[|[|]]].
  move: H2.
  by rewrite addSn ltnS add1n.
- pose k := (up_log 2 n * (a ^ 2))./2.+1.
  have k_gt1 : 1 < k.
    rewrite ltnS half_gt0 -[1%N]/(1 * 1)%N.
    apply: ltn_mul => //.
    by rewrite -[1%N]/(1 ^ 2)%N ltn_sqr.
  have H := aks_param_search_badP E.
  rewrite addSn add1n -/k in H.
  have lcmLprod : 2 ^ k.-1 <= \prod_(1 <= i < a) (n ^ i).-1.
    apply: leq_trans (lcm_lbound k) _.
    apply: dvdn_leq.
      rewrite big_nat.
      apply: prodn_cond_gt0 => [] [|i] //= _ .
      suff ni_gt1 : 1 < n ^ i.+1 
        by rewrite -ltnS prednK // (leq_trans _ ni_gt1).
      apply: leq_trans (n_gt1) _.
      by rewrite -[X in X <= _]expn1 leq_exp2l.
    apply/dvdn_biglcmP => i /= _.
    have iLk : i < k by apply: ltn_ord.
    have [|i_gt0] := leqP i 0; first by rewrite leqn0 => /eqP->; apply: dvd1n.
    have oLl : order_modn i.+1 n < a.
      suff /H[] : 1 < i.+1 < k.+1 by [].
      by rewrite ltnS i_gt0 /= ltnS ltn_ord.
    have i1_gt1 : 1 < i.+1 by rewrite ltnS.
    have i1Cn : coprime i.+1 n.
      have : 0 < gcdn i.+1 n by rewrite gcdn_gt0.
      rewrite leq_eqVlt => /orP[|g_gt1]; first by rewrite eq_sym.
      suff /H[/negP[]] : 1 <  gcdn i.+1 n < k.+1 by apply: dvdn_gcdr.
      rewrite g_gt1.
      have /leq_ltn_trans->// : gcdn i.+1 n <= i.+1.
      by rewrite dvdn_leq // dvdn_gcdl.
    rewrite (bigD1_seq (order_modn i.+1 n)) ?iota_uniq //=; last first.
      rewrite mem_index_iota oLl.
      by have [] := (order_modnP i1_gt1 i1Cn); case: order_modn.
    by apply/dvdn_mulr/order_modn_dvd.
  have prodLprod : \prod_(1 <= i < a) (n ^ i).-1 < 2 ^ (up_log 2 n * 'C(a,2)).
    rewrite expnM; apply: leq_trans (_ : n ^ 'C(a, 2) <= _); last first.
      rewrite leq_exp2r; first by apply: up_logP.
      by rewrite bin_gt0.
    rewrite -textbook_triangular_sum. 
    elim: (a) a_gt1 => // a1 IH.
    rewrite ltnS leq_eqVlt => /orP[/eqP<-|a1_gt1].
      rewrite big_nat_recl // big_geq //.
      rewrite big_nat_recl // big_nat_recl // big_geq // expn1 !muln1.
      by rewrite prednK // (leq_trans _ n_gt1).
    rewrite !big_nat_recr ?(leq_trans _ a1_gt1) //= expnD ltn_mul //.
      by apply: IH.
    by rewrite prednK // expn_gt0  (leq_trans _ n_gt1).
  have := leq_ltn_trans lcmLprod prodLprod.
  rewrite ltn_exp2l // /k /= bin2 ltnNge => /negP[].
  rewrite -!divn2  leq_divRL // -mulnA leq_mul2l.
   rewrite orbC (leq_trans (leq_trunc_div _ _)) //.
  by rewrite leq_mul2l leq_pred orbT.
have [/andP[H1 H2] H3 H4]:= aks_param_search_goodP E.
rewrite addSn ltnS add1n in H2.
split => //.
  rewrite (leq_trans a_gt1) //.
  case: leqP => // nLk.
  have /H4/negP[] : 1 < n <= k by rewrite n_gt1.
  by apply: dvdnn.
have : 0 < gcdn k n by rewrite gcdn_gt0 orbC ltnW.
rewrite /coprime leq_eqVlt=> /orP[/eqP<-|g_gt1] //.
suff /H4/negP[] : 1 < gcdn k n <= k.
  by apply: dvdn_gcdr.
rewrite g_gt1 // dvdn_leq //.
  rewrite (leq_trans _ H1) //.
  by apply: ltnW.
by apply: dvdn_gcdl.
Qed.

(******************************************************************************)
(*    Polynomial modulo X^k - 1 with coefficient in Z_n                       *)
(******************************************************************************)

Definition PolyZ n k (l : seq nat) : {poly 'Z_n} := Poly (map inZp (take k l)).

Lemma size_PolyZ n k l : size (PolyZ n k l) <= k.
Proof.
apply: leq_trans (size_Poly _) _.
by rewrite size_map size_take; case: leqP.
Qed.

Lemma PolyZE n k l : 
  PolyZ n k l = \sum_(i < k) (inZp (nth 0%N l i)) *: 'X^i.
Proof.
apply/polyP=> i; rewrite coef_sum.
case (leqP k i) => [kLi|iLk].
  rewrite nth_default; last first.
    apply: leq_trans (size_Poly _) _.
    rewrite size_map size_take.
    by case: leqP => // /leq_trans->.
  rewrite big1 // => j _.
  rewrite coefZ coefXn.
  by case: ltngtP (leq_trans (ltn_ord j) kLi); rewrite ?mulr0.
rewrite coef_Poly (bigD1 (Ordinal iLk)) //= big1 => 
    [|j /eqP /val_eqP /= jDi]; last first.
  by rewrite coefZ coefXn eq_sym (negPf jDi) mulr0.
rewrite addr0 coefZ coefXn eqxx mulr1.
case: (leqP (size (take k l)) i) => [stLk|kLst]; last first.
  by rewrite (nth_map 0%N) // nth_take.
rewrite nth_default ?size_map //.
move: stLk; rewrite size_take; case: leqP => [_ slLi|].
  by rewrite nth_default // inZp0.
by case: ltngtP iLk.
Qed.

Lemma PolyZ_nil n k : PolyZ n k [::] = 0.
Proof. by rewrite PolyZE big1 // => i _; rewrite nth_nil inZp0 scale0r. Qed.

Lemma PolyZ_cons n k a v : 0 < k -> 1 < n -> size v < k -> 
  PolyZ n k (a :: v) = a%:R + 'X * PolyZ n k v :> {poly 'Z_n}.
Proof.
move=> k_gt0 n_gt1 svE; rewrite !PolyZE.
rewrite -(prednK k_gt0) big_ord_recl /=; congr (_ + _).
  by rewrite expr0 /= -Zp_nat scaler_nat.
rewrite [in RHS]big_ord_recr /= nth_default ?svE; last first.
  by rewrite -ltnS prednK.
rewrite inZp0 scale0r addr0.
rewrite mulr_sumr; apply: eq_bigr => i _.
by rewrite -scalerAr exprS.
Qed.

(******************************************************************************)
(*    Polynomial modulo : constant                                            *)
(******************************************************************************)

Definition modnp_const (n k v : nat) := (v %% n)%N :: nseq k.-1 0%N.

Lemma size_modnp_const n k v : 0 < k -> size (modnp_const n k v) = k.
Proof. by move=> k_gt0; rewrite /= size_nseq prednK. Qed.

Lemma poly_modnp_const n k v : 0 < k -> 1 < n ->
  PolyZ n k (modnp_const n k v) = v%:R%:P.
Proof.
rewrite Zp_nat.
move=> k_gt0 n_gt1; apply/polyP => i.
rewrite coefC /PolyZ -[in take _](prednK k_gt0) /= coef_cons; case: eqP => iE.
  by apply/val_eqP; rewrite /= Zp_cast // modn_mod.
rewrite take_nseq //.
case: (leqP k i) => iLk.
  have k1Li1 : k.-1 <= i.-1 by rewrite -ltnS !prednK //; case: (i) iE.
  by rewrite nth_default //= (leq_trans (size_Poly _)) // size_map size_nseq.
have i1Lk1 : i.-1 < k.-1 by rewrite -ltnS !prednK //; case: (i) iE.
by rewrite coef_Poly (nth_map 0%N) ?size_nseq // nth_nseq i1Lk1 // inZp0.
Qed.

(******************************************************************************)
(*    Polynomial modulo : X^n                                                 *)
(******************************************************************************)

Definition modnp_Xn (n k v : nat) := 
    nseq (v %% k) 0%N ++ (1%N :: nseq (k.-1 - (v %% k)) 0%N).

Lemma size_modnp_Xn n k v : 0 < k -> size (modnp_Xn n k v) = k.
Proof. 
move=> k_gt0; rewrite /= size_cat size_nseq /= size_nseq.
by rewrite addnC addSn subnK ?prednK // -ltnS prednK // ltn_mod.
Qed.

Lemma rmodp_Xn_sub1 (R : comRingType) k n : 
  0 < k -> rmodp ('X^(k * n) - 1) ('X^k - 1) = 0 :> {poly R}.
Proof.
move=> k_gt0; elim: n => [|n IH]; first by rewrite muln0 subrr rmod0p.
rewrite mulnS exprD -{1}['X^k](subrK 1) mulrDl mul1r.
rewrite -addrA rmodpD ?monic_Xn_sub_1 // IH addr0.
by rewrite mulrC rmodp_mull ?monic_Xn_sub_1.
Qed.

Lemma poly_modnp_Xn n k v : 0 < k -> 1 < n ->
  PolyZ n k (modnp_Xn n k v) = rmodp 'X^v ('X^k - 1).
Proof.
move=> k_gt0 n_gt1.
have XnM:= monic_Xn_sub_1 [ringType of 'Z_n] k_gt0.
rewrite [in 'X^ _](divn_eq v k) exprD mulnC.
rewrite -{1}['X^(_ * _)](subrK 1) mulrDl.
rewrite rmodpD // mul1r -rmodp_mulml // rmodp_Xn_sub1 //.
rewrite mul0r rmod0p add0r rmodp_small; last first.
  by rewrite size_polyXn size_Xn_sub_1 // ltnS ltn_mod.
apply/polyP => i.
rewrite /PolyZ coef_Poly coefXn.
case: (leqP k i) => iLk.
  have k1Li1 : k.-1 <= i.-1 by rewrite -ltnS !prednK // (leq_trans k_gt0).
  rewrite nth_default; last by rewrite size_map size_take size_modnp_Xn // ltnn.
  by case: eqP => // iE; move: iLk; rewrite iE leqNgt ltn_mod k_gt0.
rewrite (nth_map 0%N); last by rewrite size_take size_modnp_Xn // ltnn.
rewrite nth_take // nth_cat size_nseq nth_nseq if_same.
case: ltngtP => iLv; first by rewrite inZp0.
  rewrite -cat1s nth_cat /= ifF.
    by rewrite nth_nseq if_same inZp0.
  by rewrite ltnNge -(subnn (v %% k)%N) ltn_sub2r.
by rewrite iLv subnn.
Qed.

(******************************************************************************)
(*    Polynomial modulo : multiplication by X                                 *)
(******************************************************************************)

Definition modnp_mulX (n k : nat) (v : list nat) :=  belast (last 0%N v) v.
  
Lemma size_modnp_mulX n k v : 0 < k -> 
  size v = k -> size (modnp_mulX n k v) = k.
Proof. by move=> k_gt0 vsEk; rewrite size_belast. Qed.

Lemma nth_belast_0 (I : eqType ) (l : seq I) i j :
   0 < size l -> nth i (belast j l) 0 = j.
Proof. by case: l. Qed.

Lemma nth_belast_max (I : eqType ) (l : seq I) i j n :
 n.+1 < size l -> nth i (belast j l) n.+1 = nth i l n.
Proof.
elim: l n j => [n j /=|a l IH n j /=]; first by rewrite nth_nil.
by case: n => [|n /IH-> //]; case: (l).
Qed.

Lemma poly_modnp_mulX n k v : 0 < k -> 1 < n ->
  size v = k ->
  PolyZ n k (modnp_mulX n k v) = rmodp ('X * PolyZ n k v) ('X^k - 1).
Proof.
move=> k_gt0 n_gt1 vsE; rewrite !PolyZE.
have xnM := monic_Xn_sub_1 [ringType of 'Z_n] k_gt0.
rewrite mulr_sumr rmodp_sum  //= -[k]prednK // big_ord_recl big_ord_recr addrC.
congr (_ + _); last first.
  rewrite expr0 alg_polyC -scalerAr -exprS rmodpZ ?prednK //.
  rewrite [in 'X^_]prednK // [in modnp_mulX _ _]prednK //.
  rewrite -{1}['X^k](subrK 1) // rmodpD // rmodpp // add0r.
  rewrite rmodp_small; last by rewrite size_poly1 size_Xn_sub_1.
  rewrite alg_polyC; congr (_%:P).
  apply/val_eqP; rewrite /= Zp_cast // /modnp_mulX.
  case: v vsE => [|a v1 <- /=]; first by rewrite nth_nil.
  by rewrite (last_nth 0%N).
apply: eq_bigr => j _.
rewrite -scalerAr -exprS rmodpZ ?prednK //.
congr (inZp _ *: _); last first.
  rewrite rmodp_small //= prednK // size_Xn_sub_1 //.
  by rewrite  size_polyXn !ltnS -{2}[k]prednK // ltnS ltn_ord.
rewrite /modnp_mulX [in RHS]/= nth_belast_max //=.
by rewrite vsE -[X in _ < X]prednK // ltnS.
Qed.

Compute (modnp_mulX 4 10 (modnp_Xn 4 10 9)).

(******************************************************************************)
(*    Polynomial modulo : addition                                            *)
(******************************************************************************)

Fixpoint modnp_add (n k : nat) (v1 v2 : seq nat) :=
  if k is k1.+1 then 
    ((head 0%N v1 + head 0%N v2) %% n)%N :: 
    modnp_add n k1 (behead v1) (behead v2)
  else [::].

Lemma size_modnp_add n k v1 v2 : size (modnp_add n k v1 v2) = k.
Proof. by elim: k v1 v2 => //= k IH v1 v2; rewrite IH. Qed. 

Lemma poly_modnp_add n k v1 v2 : 0 < k -> 1 < n ->
  PolyZ n k (modnp_add n k v1 v2) = PolyZ n k v1 + PolyZ n k v2.
Proof.
move=> k_gt0 n_gt1; rewrite !PolyZE -big_split /=.
apply: eq_bigr => i _.
rewrite -scalerDl; congr (_ *: _).
elim: (k) (val i) (ltn_ord i) v1 v2 => //= k1 IH [_ v1 v2|n1]; last first.
  rewrite ltnS => /IH HE v1 v2; rewrite [in inZp _]/= HE.
  by case: v1 => /=; case: v2 => /=; rewrite ?nth_nil.
case: v1 => [|x _] /=; (case: v2 => [|y _] /=); 
  rewrite ?(nth_nil, inZp0, add0r, addr0, add0n, addn0, mod0n) //=.
- by apply/val_eqP; rewrite /= Zp_cast // modn_mod.
- by apply/val_eqP; rewrite /= Zp_cast // modn_mod.
by apply/val_eqP; rewrite /= Zp_cast // modn_mod modnDm.
Qed.

Compute (modnp_add 4 10 (modnp_Xn 4 10 9) (modnp_Xn 4 10 1)).

(******************************************************************************)
(*    Polynomial modulo : multiplication by a constant                        *)
(******************************************************************************)

Fixpoint modnp_scale (n k a : nat) (v : seq nat) :=
  if k is k1.+1 then 
    ((a * head 0%N v) %% n)%N :: modnp_scale n k1 a (behead v)
  else [::].

Lemma size_modnp_scale n k a v : size (modnp_scale n k a v) = k.
Proof. by elim: k a v => //= k IH b v; rewrite IH. Qed.

Lemma poly_modnp_scale n k a v : 0 < k -> 1 < n ->
  PolyZ n k (modnp_scale n k a v) = inZp a *: PolyZ n k v.
Proof.
move=> k_gt0 n_gt1; rewrite !PolyZE /= scaler_sumr.
apply: eq_bigr => i _.
rewrite scalerA; congr (_ *: _).
elim: (k) (val i) (ltn_ord i) v => //= k1 IH [_ v|n1]; last first.
  rewrite ltnS => /IH HE v; rewrite [in inZp _]/= HE.
  by case: v => /=; rewrite ?nth_nil.
case: v => [|x _] /=; 
  rewrite ?(nth_nil, inZp0, add0r, addr0, add0n, addn0, mod0n) //=.
  by apply/val_eqP; rewrite /= Zp_cast // !muln0 !mod0n.
by apply/val_eqP; rewrite /= Zp_cast // modn_mod modnMm.
Qed.

(******************************************************************************)
(*    Polynomial modulo : multiplication                                      *)
(******************************************************************************)

Fixpoint modnp_mul (n k : nat) (v1 v2 : seq nat) :=
  if v2 is a :: v3 then
    modnp_add n k (modnp_scale n k a v1) (modnp_mulX n k (modnp_mul n k v1 v3))
  else modnp_const n k 0.

Lemma size_modnp_mul n k v1 v2 : 0 < k -> size (modnp_mul n k v1 v2) = k.
Proof.
move=> k_gt0.
case: v2 => [|a v4 /=]; first by rewrite size_modnp_const.
by rewrite size_modnp_add.
Qed.

Lemma poly_modnp_mul n k v1 v2 : 0 < k -> 1 < n ->
  size v2 = k ->
  PolyZ n k (modnp_mul n k v1 v2) = 
    rmodp (PolyZ n k v1 * PolyZ n k v2) ('X^k - 1).
Proof.
move=> k_gt0 n_gt1 sv2E.
have : size v2 <= k by rewrite sv2E.
have xnM := monic_Xn_sub_1 [ringType of 'Z_n] k_gt0.
elim: {sv2E}v2 => /= [|a v4 IH sv4E].
  by rewrite poly_modnp_const // PolyZ_nil mulr0 rmod0p Zp_nat inZp0.
rewrite poly_modnp_add // poly_modnp_scale //.
rewrite poly_modnp_mulX ?size_modnp_mul // IH; last by apply: ltnW.
rewrite PolyZ_cons // mulrDr rmodpD // rmodp_mulmr // mulrCA.
congr (_ + _).
rewrite -mulr_algr -Zp_nat scaler_nat.
rewrite rmodp_small // size_Xn_sub_1 //.
apply: leq_trans (size_mul_leq _ _) _.
rewrite -polyC_natr size_polyC.
apply: leq_trans (size_PolyZ n k v1).
case: eqP=> _; first by rewrite addn0 leq_pred.
by rewrite addn1.
Qed.

Compute (modnp_mul 4 10 (modnp_Xn 4 10 9) (modnp_Xn 4 10 1)).

(******************************************************************************)
(*    Polynomial modulo : exponentiation                                      *)
(******************************************************************************)

Import BinPos.

Fixpoint modnp_pow (n k : nat) (p : positive) (v : seq nat) :=
  if p is xO p1 then let r := modnp_pow n k p1 v in
                     modnp_mul n k r r
  else if p is xI p1 then let r := modnp_pow n k p1 v in
                          modnp_mul n k v (modnp_mul n k r r)
  else v.

Lemma size_modnp_pow n k p v :
  0 < k -> size v = k -> size (modnp_pow n k p v) = k.
Proof.
move=> k_gt0 svE.
elim: p => //= p spE; first by rewrite !size_modnp_mul.
by rewrite size_modnp_mul.
Qed.

Lemma poly_modnp_pow n k p v : 0 < k -> 1 < n ->
  size v = k ->
  PolyZ n k (modnp_pow n k p v) = 
    rmodp (PolyZ n k v ^+ Pos.to_nat p) ('X^k - 1).
Proof.
move=> k_gt0 n_gt1 sv2E.
have xnM := monic_Xn_sub_1 (GRing.Ring.clone _ 'Z_n) k_gt0.
elim: p => [p1 IH|p1 IH|] /=; last first.
- by rewrite expr1 rmodp_small // size_Xn_sub_1 // ltnS size_PolyZ.
- rewrite poly_modnp_mul ?size_modnp_pow //= IH.
  rewrite rmodp_mulmr // rmodp_mulml // -exprD.
  by rewrite Pnat.Pos2Nat.inj_xO addnn -muln2 mulnC.
rewrite !poly_modnp_mul ?(size_modnp_pow, size_modnp_mul) //= IH.
rewrite rmodp_mulmr // mulrA rmodp_mulmr // mulrAC rmodp_mulmr //.
by rewrite Pnat.Pos2Nat.inj_xI /= exprS !exprD expr0 mulr1 !mulrA.
Qed.

Compute (modnp_pow 4 10 (Pos.of_nat 4) (modnp_Xn 4 10 1)).

(******************************************************************************)
(*    Polynomial modulo : equality test                                       *)
(******************************************************************************)

Fixpoint modnp_eq (n k : nat) (v1 v2 : seq nat) : bool :=
  if k is k1.+1 then 
    ((head O v1) == (head O v2) %[mod n]) && 
    modnp_eq n k1 (behead v1) (behead v2)
  else true.

Lemma poly_modnp_eq n k v1 v2 : 0 < k -> 1 < n ->
  (modnp_eq n k v1 v2) = (PolyZ n k v1 == PolyZ n k v2).
Proof.
move=> k_gt0 n_gt1; rewrite !PolyZE.
elim: (k) v1 v2 => [|k1 IH] v1 v2; first by rewrite !big1 ?eqxx // => [[]|[]].
rewrite /= IH -!(poly_def _ (fun i => inZp (nth 0%nat _ i))).
apply/andP/eqP=> [[/eqP hE /eqP/polyP pE]| /polyP pE].
  apply/polyP=> i; rewrite !coef_poly; case: leqP => //.
  case: i => [_|i].
    by (case: (v1) hE; case: (v2)) => //= [a _ aE|a _ aE|a _ b _ aE];
        apply/val_eqP/eqP; rewrite /= Zp_cast.
  rewrite ltnS => iLk1.
  have := pE i; rewrite !coef_poly iLk1.
  by (case: (v1); case: (v2)) => //= [_ l <-|_ l ->]; rewrite nth_nil.
split; apply/eqP.
  have := pE 0%nat; rewrite !coef_poly ltnS leq0n.
  by (case: (v1); case: (v2)) => //= [a _ |a _|a _ b _] /val_eqP/eqP/=;
     rewrite Zp_cast.
apply/polyP=> i; rewrite !coef_poly; case: leqP => // iLk1.
have := pE i.+1; rewrite !coef_poly ltnS iLk1.
by (case: (v1); case: (v2)) => //= [_ l|_ l]; rewrite nth_nil.
Qed.

Compute modnp_eq 4 10 (modnp_Xn 4 10 1) (modnp_Xn 4 10 11).

(******************************************************************************)
(*    introspection check                                                     *)
(******************************************************************************)

Fixpoint poly_intro_range_aux n pn k c r := 
  if r is r1.+1 then
    let cc := modnp_const n k c in
    let x := modnp_Xn n k 1 in
    let xcc := modnp_add n k x cc in
    let xve := modnp_pow n k pn xcc in
    let xn := modnp_Xn n k n in
    let xncc := modnp_add n k xn cc in
    if modnp_eq n k xve xncc then poly_intro_range_aux n pn k c.+1 r1
    else false
  else true.

Section inZp_morph.

Variable n p : nat.
Hypothesis n_gt1 : 1 < n.
Hypothesis pP : prime p.
Hypothesis pDn : (p %| n)%nat.

Fact inZpm_is_semi_additive : semi_additive (inZp : 'Z_n -> 'F_p).
Proof.
have p_gt1 : 1 < p by apply: prime_gt1.
split=> [//|x y]; first by apply/val_eqP=> /=; rewrite mod0n.
apply/val_eqP/eqP => /=.
set x' := nat_of_ord _; set y' := nat_of_ord _.
rewrite !Zp_cast /= ?pdiv_id //.
by rewrite modnDm modn_dvdm.
Qed.

Fact inZpm_is_additive : additive (inZp : 'Z_n -> 'F_p).
Proof.
have p_gt1 : 1 < p by apply: prime_gt1.
move=> /= x y; apply/val_eqP/eqP => /=.
set x' := nat_of_ord _; set y' := nat_of_ord _.
rewrite !Zp_cast /= ?pdiv_id //.
rewrite modnDm modnDmr modn_dvdm //.
rewrite -modnDmr modnB //; last 2 first.
- by apply: leq_trans p_gt1.
- apply: ltnW.
  by have := ltn_ord y; rewrite [X in _ < X -> _]Zp_cast.
have -> : modn n p = O%N.
  by have /dvdnP[k ->] := pDn; rewrite modnMl.
rewrite addn0.
case: (modn y' p)%N => //= [|xx]; last by rewrite mul1n.
by rewrite mul0n !subn0 addn0 modnDr.
Qed.

Fact inZpm_is_multiplicative : multiplicative (inZp : 'Z_n -> 'F_p).
Proof.
have p_gt1 : 1 < p by apply: prime_gt1.
split=> [x y| //]; apply/val_eqP/eqP => /=.
set x' := nat_of_ord _; set y' := nat_of_ord _.
by rewrite !Zp_cast /= ?pdiv_id // modnMm modn_dvdm.
Qed.
      
Definition inZpm : {rmorphism 'Z_n -> 'F_p} :=
  GRing.RMorphism.Pack
    (GRing.RMorphism.Class
       (GRing.isSemiAdditive.Build _ _ _ inZpm_is_semi_additive)
       (GRing.isMultiplicative.Build _ _ _ inZpm_is_multiplicative)).


Lemma eqp_rmodp_dvd (R : ringType) (p1 q r  :  {poly R}) :
  p1 \is monic ->  (rmodp q p1 == rmodp r p1) = (rdvdp p1 (q - r)).
Proof. by move=> pM; rewrite -subr_eq0 -rmodpB. Qed.

Lemma inZpm_poly_intro_range k s : 0 < k ->
  poly_intro_range (GRing.Ring.clone _ 'Z_n) k n s -> 
  poly_intro_range (GRing.Ring.clone _ 'F_p) k n s.
Proof.
move=> k_gt0.
have xnZM := monic_Xn_sub_1 (GRing.Ring.clone _ 'Z_n) k_gt0.
have xnFM := monic_Xn_sub_1 (GRing.Ring.clone _ 'F_p) k_gt0.
have p_gt1 : 1 < pdiv n by apply/prime_gt1/pdiv_prime.
move=> Hr c cB; apply/eqP; rewrite eqp_rmodp_dvd //.
have /eqP := Hr c cB; rewrite eqp_rmodp_dvd //.
case /(rdvdpP xnZM) => /= p1 pE; apply/(rdvdpP xnFM).
exists (map_poly inZpm p1).
rewrite (_ : 'X^k - 1 = map_poly inZpm ('X^k - 1)); last first.
  by rewrite rmorphB rmorph1 /= (map_polyXn inZpm).
have cE : inZp (c%:R : 'Z_n) = c%:R :> 'F_p.
  by apply/val_eqP; 
     rewrite /= !Zp_nat /= Fp_cast // Zp_cast // modn_dvdm // pDn.
rewrite -rmorphM -pE !(rmorphB, rmorphXn, rmorphD) /=.
by rewrite (map_polyX inZpm) (map_polyC inZpm) /= cE.
Qed.

End inZp_morph.

Lemma poly_intro_range_auxP n pn k c r :
  1 < k -> 1 < n -> pn = Pos.of_nat n -> 
  if poly_intro_range_aux n pn k c r then 
  forall c1, c <= c1 < c + r ->
   rmodp (('X + (c1%:R)%:P) ^+ n) ('X^k - 1) =
   rmodp ('X^n + (c1%:R)%:P) ('X^k - 1) :> {poly 'Z_n}
  else ~ prime n.
Proof.
move=> k_gt1 n_gt1 pnE.
have k_gt0 : 0 < k by apply: leq_trans k_gt1.
elim: r c => /= [c c1|r IH c]; first by rewrite addn0; case: ltngtP.
rewrite poly_modnp_eq // poly_modnp_pow ?size_modnp_add //.
rewrite !poly_modnp_add // !poly_modnp_Xn // poly_modnp_const // pnE.
rewrite Pnat.Nat2Pos.id_max max_r; last by apply/leP/ltnW.
rewrite expr1 [rmodp 'X _]rmodp_small; last first.
  by rewrite size_polyX size_Xn_sub_1.
case: eqP  => mE; last first.
  move=> nP; case: mE.
  have xnM := monic_Xn_sub_1 (GRing.Ring.clone _ 'Z_n) k_gt0.
  rewrite exprDn_char /=; last first.
    rewrite pnatE // char_poly /= inE nP /=.
    apply/eqP/val_eqP=> /=.
    by rewrite val_Zp_nat // modnn.
  rewrite rmodpD //; congr (_ + _).
  rewrite rmodp_small //; last first.
    apply: leq_ltn_trans (size_exp_leq _ _) _.
    rewrite size_polyC size_Xn_sub_1 //.
    by case: (_ != _).
  rewrite -rmorphXn; congr (_ %:P).
  pose i := inZpm n_gt1 nP (dvdnn n).
  suff : i (c%:R ^+ n) = i c%:R.
    move/val_eqP/eqP=> /=; rewrite Fp_cast //.
    rewrite !modn_small //; try by rewrite -[n]Zp_cast ?prime_gt1.
    by move=> H; apply/val_eqP/eqP.
  rewrite rmorphXn rmorph_nat.
  by apply: fin_little_fermat c (char_Fp nP).
rewrite -pnE.
case: poly_intro_range_aux (IH c.+1) => // H c1.
rewrite addnS ltnS [c <= _]leq_eqVlt => /andP[/orP[/eqP<-//|cLc1] c1Lcr].
  rewrite rmodpD ?monic_Xn_sub_1 //.
  rewrite [X in _ = _ + X]rmodp_small // size_Xn_sub_1 // size_polyC.
  by case: eqP.
by apply: H; rewrite cLc1.
Qed.

Definition fpoly_intro_range n k l := 
  let r := (sqrtn (totient k) * l)%nat in
  poly_intro_range_aux n (Pos.of_nat n) k 1 r.

Lemma fpoly_intro_rangeP n k l :
  1 < k -> 1 < n -> 
  if fpoly_intro_range n k l then 
  poly_intro_range (GRing.Ring.clone _ 'Z_n) k n (sqrtn (totient k) * l)
  else ~ prime n.
Proof.
move=> k_gt1 n_gt1; rewrite /fpoly_intro_range.
by apply: poly_intro_range_auxP.
Qed.

(******************************************************************************)
(*    Aks algorithmm                                                          *)
(******************************************************************************)

Definition aks n := 
  let l := up_log 2 n in
  if power_free n l then
    let v := aks_param n l in
    if v is nice k then n == k else
    if v is good k then fpoly_intro_range n k l else false
  else false.

Lemma aksP n : aks n = prime n.
Proof.
case: n => //; case => // m.
have : 1 < m.+2 by []; move: m.+2 => {m}n n_gt1; 
rewrite /aks; set l := up_log 2 n.
case: power_free (@power_freeP n) (@power_freePn n)
      => [H _ | _ /(_ isT) [m [k k_gt1 ->]]]; last first.
  have k_gt0 : 0 < k by apply: ltnW.
  apply/sym_equal/idP => /primePn[].
  case: m => [|[|m]]; first by left; rewrite exp0n.
    by left; rewrite exp1n.
  right; exists m.+2; first by rewrite /= -{1}[m.+2]expn1 ltn_exp2l.
  by apply: dvdn_exp.
case: aks_param (aks_paramP n) => // 
   [m /(_ n_gt1) [m_gt1 _ mDn nP]|k [kB nP kLl kCm lLo]].
  move: nP; case: eqP => [->|HD] nP; apply/sym_equal/idP.
    apply/primeP; split => // [] [|[|d]] //.
      by rewrite dvd0n; case: (m) m_gt1.
    move=> dDm /=; case: eqP => // d2Dm.
    suff /nP/negP[]/= : 1 < d.+2 < m by [].
    by have := dvdn_leq (ltnW m_gt1) dDm; rewrite leq_eqVlt => /orP[/eqP|].
  apply/negP/primePn; right; exists m => //.
  rewrite m_gt1 /=.
  have := dvdn_leq (ltnW n_gt1) mDn; rewrite leq_eqVlt => /orP[/eqP|] // mEn.
  by case: HD.
have k_gt1 : 1 < k by case/andP: kB.
case: fpoly_intro_range (fpoly_intro_rangeP l k_gt1 n_gt1); last first.
  by case: prime.
case: (boolP (prime n)) => // /negP nNP.
have pkn_gt1 : 1 < order_modn k n.
  apply: leq_trans lLo.
  apply: leq_trans (_ : up_log 2 4 ^ 2 <= _) => //.
  rewrite leq_exp2r // leq_up_log //.
  by case: (n) n_gt1 nNP => // [] [|[|[|]]].
have [p [pDn pP pO]] := order_gt1_prime n_gt1 pkn_gt1. 
move/(inZpm_poly_intro_range n_gt1 pP pDn (ltnW k_gt1)) => Hp.
suff : is_power n p.
  move/eqP => nE.
  by case: nNP; rewrite nE (H _ _ isT nE) expn1.
apply: (@main_aks p n k) => //.
split => //=; try by apply: ltnW.
move=> p1; rewrite inE => /andP[p1P].
rewrite -(dvdn_charf (char_Fp _)) // dvdn_prime2 ?pdiv_prime // => /eqP<-.
split=> //.
case: leqP => // pLk.
by have /nP/negP[] : 1 < p <= k by rewrite prime_gt1.
Qed.

Compute filter aks (iota 2 50).
Check aksP.

End AKS.

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").
