From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
Require Import more_thm divpoly.

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

Lemma introspective1l (R : ringType) k (p : {poly R}) : 1 ⋈[k] p.
Proof. by rewrite /introspective expr1 comp_polyXr. Qed.

Lemma introspective1r (R : ringType) n k : n ⋈[k] (1 : {poly R}).
Proof. by rewrite /introspective expr1n comp_polyC polyC1. Qed.

Lemma introspectiveX (R : ringType) k n : n ⋈[k] ('X : {poly R}).
Proof. by rewrite /introspective comp_polyX. Qed.

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

Lemma dvdp_geom (R : comRingType) n (p : {poly R}) :
  p - 1 \is monic -> rdvdp (p - 1) (p ^+ n.+1 - 1).
Proof. move=> pM; rewrite poly_geom mulrC rdvdp_mull //. Qed.

(* 98 *)
Lemma introspec_char (F : finFieldType) (k p c : nat) :
  p \in [char F] -> p ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> pC; apply/eqP; congr (rmodp _  _).
have Pp : prime p by apply: charf_prime pC.
have Cn : [char F].-nat p by rewrite pnatE.
rewrite comp_polyD comp_polyC comp_polyX.
rewrite exprDn_char; first by rewrite -polyC_exp fin_little_fermat.
by rewrite pnatE // (rmorph_char (polyC_rmorphism _)).
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
  by rewrite -comp_polyA comp_polyXn -exprM.
have XM : ('X^k.+1 - 1 : {poly R}) \is monic.
  rewrite qualifE lead_coefDl ?lead_coefXn ?unitr1 //.
  by rewrite size_polyXn size_opp size_polyC oner_neq0.
rewrite /introspective exprM -rmodp_exp // (eqP mIp) rmodp_exp //.
rewrite exprM -['X^m.+1 ^+_]comp_polyXn comp_poly_exp comp_polyA.
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

(* 102 *)
Lemma introspec_fin_div (F : finFieldType) k n p (c : nat) :
  coprime k n -> p \in [char F] -> (p %| n)%N ->
  n ⋈[k] ('X + c%:R%:P : {poly F}) -> (n %/ p) ⋈[k] ('X + c%:R%:P : {poly F}).
Proof.
move=> kCn pC pDn nIkX.
have pP : prime p by case/andP: pC.
have k_gt0 : (0 < k)%N.
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
  rewrite inE pP -poly_natmul polyC_eq0 /=.
  by case/andP : pC.
rewrite -subr_eq0 -modp_opp -modp_add -[_ == 0]/(_ %| _).
rewrite -(separable_exp _ (separable_polyXnsub1 _) (prime_gt0 pP)) //.
rewrite exprDn_char // exprNn_char // -exprM divnK //.
rewrite comp_polyD comp_polyC [_ ^+ p]exprDn_char //.
rewrite comp_poly_exp comp_polyXn -exprM divnK //.
rewrite -polyC_exp fin_little_fermat //.
rewrite /dvdp modp_add modp_opp subr_eq0 //.
move: nIkX.
rewrite /introspective -!Pdiv.IdomainMonic.modpE ?monic_Xn_sub_1 //.
by rewrite comp_polyD comp_polyC comp_polyX.
Qed.

(* I've departed from Chan thesis as it is not easy 
   to build non-constructive sets in Coq. So I turn 
   them into properties. Trying to sort things out 
   went doing the proof by contradiction 
 *)

(* This 𝒩 as a predicate *)
Definition is_iexp (R : ringType) (k s m : nat) := 
   coprime m k /\ forall c, (0 < c <= s)%N -> m ⋈[k] ('X + c%:R%:P : {poly R}).

Lemma is_iexp1 (R : ringType) k s : is_iexp R k s 1%N.
Proof.
split=> [|c cR]; first by rewrite /coprime gcd1n.
by apply: introspective1l.
Qed.

Lemma is_iexp_mul (R : comRingType) k s m1 m2 : 
  is_iexp R k s m1 -> is_iexp R k s m2 -> is_iexp R k s (m1 * m2)%N.
Proof.
move=> [m1Ck Hm1] [m2Ck Hm2]; split; first by rewrite coprime_mull m1Ck.
by move=> c Hc; apply: introspecMl; [apply: Hm1 | apply: Hm2].
Qed.

Lemma is_iexp_X (R : comRingType) k s m n : 
  is_iexp R k s m -> is_iexp R k s (m ^ n)%N.
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
  by have := nCk; rewrite -{1}(divnK pDn) coprime_mull => /andP[].
apply: introspec_fin_div => //; first by rewrite coprime_sym.
by apply: nI.
Qed.

(* This is 𝒫 *)
Definition is_ipoly (R : ringType) (k s : nat) (p : {poly R}):= 
  forall m, is_iexp R k s m -> m ⋈[k] p.

Lemma is_ipoly1 (R : ringType) k s :  is_ipoly k s (1 : {poly R}).
Proof. by move=> m _; apply: introspective1r. Qed.

Lemma is_ipoly_Xaddc (R : ringType) k s c : 
   (0 <= c <= s)%N -> is_ipoly k s ('X + c%:R%:P : {poly R}).
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
  (1 < k)%N -> Mk_spec R s M -> 1 \in M.
Proof.
move=> k_gt1 MS; case: MS => // /(_ 1%N (is_iexp1 _ _ _)).
by rewrite modn_small ?eqxx.
Qed.

Lemma is_iexpm_mul (R : comRingType) k s (M : {set 'Z_k}) x y : 
  (1 < k)%N -> Mk_spec R s M -> x \in M -> y \in M -> (x * y) \in M. 
Proof.
move=> k_gt1 MS.
(do 3 case: (MS) => //) => Hm m1 yE m1I m xE mI _ _.
have /eqP[] := Hm _ (is_iexp_mul mI m1I).
by rewrite -modnMml -xE -modnMmr -yE /= {3}Zp_cast.
Qed.

Lemma is_iexpm_X (R : comRingType) k s (M : {set 'Z_k}) x n : 
  (1 < k)%N -> Mk_spec R s M -> x \in M -> (x ^+ n) \in M. 
Proof.
move=> k_gt1 MS xM.
elim: n => [|n IH]; first by apply: is_iexpm1.
by rewrite exprS; apply: is_iexpm_mul.
Qed.

(* 104 *)
Lemma is_iexpm_totient R k s (M : {set 'Z_k}) :
  (1 < k)%N -> Mk_spec R s M -> (#|M| <= totient k)%N.
Proof.
move:M; case: k => [|[|k /= M _ HM]] //.
suff <-: #|[set i in 'I_k.+2 | coprime i k.+2]| = totient k.+2.
  apply/subset_leq_card/subsetP=> x; rewrite !inE; case: HM => // m -> [].
  by rewrite coprime_modl.
rewrite -sum1_card big_mkcond /=.
rewrite totient_count_coprime big_mkord.
by apply: eq_bigr => i _; rewrite inE coprime_sym.
Qed.

Lemma mk_Zp_unit_proof k m : 
  (if (1 < k)%N && (coprime k m) then (m%:R : 'Z_k) else 1) \is a GRing.unit.
Proof.
case: leqP =>  [_|k_gt1]; first by apply: unitr1.
by case: coprime (unitZpE m k_gt1) => [//|_]; apply: unitr1.
Qed.

Definition mk_Zp_unit (k m : nat) :=
  FinRing.unit 'Z_k (mk_Zp_unit_proof k m).

Lemma val_mk_Zp_unit k m :
  (1 < k)%N -> coprime k m -> val (mk_Zp_unit k m) = (m %% k)%N :> nat.
Proof.
by move=> k_gt1 kCm; rewrite /= k_gt1 kCm val_Zp_nat.
Qed.

Lemma val_mk_Zp_unit_Zp k (m : 'Z_k) :
  (1 < k)%N -> coprime k m -> val (mk_Zp_unit k m) = m.
Proof.
move=> k_gt1 kCm; apply/val_eqP/eqP; rewrite /= k_gt1 kCm val_Zp_nat //=.
by rewrite modn_small //; move: (m); rewrite Zp_cast.
Qed.

Definition ordern k m := 
  if (1 < k)%N && (coprime k m) then #[mk_Zp_unit k m]%g else 0%N.

Lemma ordern_mod k m : (1 < k)%N -> ordern k (m %% k) = ordern k m.
Proof.
move=> k_gt1.
rewrite /ordern coprime_modr; case: andb => //.
congr (#[_]%g).
apply/val_inj; rewrite /= coprime_modr.
congr (if _ then _ else _).
by apply/val_inj; rewrite !Zp_nat /= Zp_cast // modn_mod.
Qed.

(* k > 1 not necessary *)
Lemma ordern_exp k m :
  (1 < k)%N -> coprime k m -> m ^ ordern k m = 1 %[mod k].
Proof.
move=> k_gt1 kCm.
have /(congr1 val) /(congr1 val) := expg_order (mk_Zp_unit k m).
rewrite FinRing.val_unitX /ordern /= k_gt1 kCm /=.
by rewrite -natrX val_Zp_nat // Zp_cast.
Qed.


(* 104 *)
Lemma is_iexpm_order (R : comRingType) k s (M : {set 'Z_k}) n :
  (1 < k)%N -> Mk_spec R s M -> is_iexp R k s n -> (ordern k n <= #|M|)%N.
Proof.
move=> k_gt1 HMk nIN.
have kCn : coprime k n by case: nIN; rewrite coprime_sym.
pose x : 'Z_k := inZp n.
have kCx : coprime k x by rewrite /=  Zp_cast // coprime_modr.
suff <-: #|[set val x | x in <[mk_Zp_unit k x]>%g]| = ordern k n.
  apply/subset_leq_card/subsetP => y /imsetP[z /cycleP[i ->] ->].
  rewrite FinRing.val_unitX val_mk_Zp_unit_Zp //=.
   apply: is_iexpm_X (HMk) _ => //.
   by case: HMk => // /(_ _ nIN) /eqP[] /=; rewrite Zp_cast.
have -> : ordern k n = ordern k x.
  by rewrite -ordern_mod // -{2}[k]Zp_cast.
rewrite /ordern k_gt1 kCx /mk_Zp_unit.
by apply/eqP/imset_injP=> y z H1 H2 U; apply/val_eqP/eqP.
Qed.

(* 105 *)
Lemma rmodn_trans {R : ringType} (p q h z : {poly R}) :
  h \is monic -> z \is monic -> rdvdp h z -> 
  rmodp p z = rmodp q z -> rmodp p h  = rmodp q h.
Proof.
move=> hM zM /(rdvdp_trans hM zM) => /(_ (p - q)).
rewrite /rdvdp !rmodp_sub // !subr_eq0 => H /eqP H1; apply/eqP.
by apply: H.
Qed.


Definition poly_order {R : ringType} (h p :  {poly R}) (n : nat) : nat := 
  if [pick i | rmodp (p^+ (i : 'I_n.+1).-1.+1) h == 1] is Some v then
      [arg min_(i < v | (rmodp (p^+ i.-1.+1) h == 1)) i].-1.+1 else 0%N.

Lemma poly_order_leq (R : ringType) (h p : {poly R}) n :
  (0 < n -> poly_order h p n <= n)%N.
Proof.
by rewrite /poly_order; case: pickP => // x Hx; case: arg_minP => // [] [[|m]].
Qed.

Lemma poly_order_gt0_rmodp (R : ringType) (h p : {poly R}) n :
  (0 < poly_order h p n)%N ->  rmodp (p^+ poly_order h p n) h == 1.
Proof.
by rewrite /poly_order; case: pickP => // x Hx _; case: arg_minP.
Qed.

Lemma poly_order_eq0_rmodp (R : ringType) (h p : {poly R}) m n :
  (poly_order h p n = 0)%N -> (0 < m <= n)%N -> rmodp (p^+ m) h != 1.
Proof.
rewrite -[(_ <= n)%N]ltnS /poly_order; case: pickP => // HM _ /andP[m_gt0 mLn].
by have /= := HM (Ordinal mLn); case: (m) m_gt0 => //= k _ /idP/negP.
Qed.

Lemma poly_order_lt (R : ringType) (h p : {poly R}) m n :
  (0 < m < poly_order h p n)%N -> rmodp (p^+ m) h != 1.
Proof.
rewrite /poly_order; case: pickP=> [x Hx|]; last by rewrite ltn0 andbF.
case: arg_minP => // i Hi Hmin /andP[m_gt0 mLi].
have mLn : (m < n.+1)%N.
  by rewrite (leq_trans mLi) // (leq_trans _ (ltn_ord i)) //; case: (i : nat).
apply/negP; rewrite -[m]prednK // => /(Hmin (Ordinal mLn)) /=.
rewrite leqNgt; case: (i : nat) mLi  => [/=|j ->//].
by case: (m) m_gt0.
Qed.

(* 106  we reformulate it because we can't have order for poly directly *)
Lemma poly_order_rmod_inj (R : ringType) (h : {poly R}) k m n :
  h \is monic -> (1 < size h)%N -> (0 < k)%N -> rdvdp h ('X^k - 1) -> 
  (m < poly_order h 'X k)%N -> (n < poly_order h 'X k)%N ->
  rmodp 'X^m h = rmodp 'X^n h-> m = n.
Proof.
move=> hM hS k_gt0 hDxk.
wlog : m n / (m <= n)%N => [Hw |mLn] mLp nLp xmExn.
  case: (leqP m n) => [/Hw|nLm]; first by apply.
  by apply/sym_equal/Hw => //; apply: ltnW.
move: mLn; rewrite leq_eqVlt => /orP[/eqP//|mLn].
have xkE1 :  rmodp 'X^k h = 1.
  move: hDxk; rewrite /rdvdp rmodp_sub // [rmodp 1 _]rmodp_small.
    by rewrite subr_eq0 => /eqP.
  by rewrite size_polyC oner_neq0.
have [|o_gt0] := leqP (poly_order h 'X k) 0.
  have kB : (0 < k <= k)%N by rewrite k_gt0 leqnn.
  by rewrite leqn0 => /eqP/poly_order_eq0_rmodp /(_ kB) /eqP[].
pose v := (poly_order h 'X k - n + m)%N.
have /poly_order_lt/eqP[] :
     (0 < poly_order h 'X k - n + m < poly_order h 'X k )%nat.
  rewrite (leq_trans _ (_ : 0 + m < _)%N) //; last first.
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
  h \is monic -> (1 < size h)%N -> (0 < k)%N -> rdvdp h ('X^k - 1) -> 
  is_ipoly k s p -> is_ipoly k s q -> rmodp p h = rmodp q h ->
  n \in M -> rmodp ((p - q) \Po 'X^n) h = 0.
Proof.
move=> HM hM hS k_gt0 hDxk pI qI phEqh nIM; apply/eqP.
case: HM nIM => // m nE mI _.
have xkM := monic_Xn_sub_1 R k_gt0.
have F : rmodp 'X^n ('X^k - 1) = rmodp 'X^m ('X^k - 1) :> {poly R}.
  have F1 : rmodp 'X^k ('X^k - 1) = 1 :> {poly R}.
    rewrite -{1}['X^k](subrK (1 : {poly R})) addrC rmodp_add // rmodpp //.
    by rewrite addr0 rmodp_small // size_polyC oner_eq0 /= size_Xn_sub_1.
    rewrite (divn_eq m k) exprD mulnC exprM.
    rewrite mulrC -rmodp_mulmr // -[in RHS]rmodp_exp // F1 expr1n.
    by rewrite rmodp_mulmr // mulr1 nE.
rewrite comp_polyB rmodp_sub // subr_eq0; apply/eqP.
apply: etrans (_ : rmodp (p^+m) h = _).
  apply: rmodn_trans hDxk _ => //.
  rewrite -rmodp_compr // F rmodp_compr //.
  by apply/esym/eqP/pI.
apply: etrans (_ : rmodp (q^+m) h = _).
  by rewrite -rmodp_exp // phEqh rmodp_exp.
apply: esym.
apply: rmodn_trans hDxk _ => //.
rewrite -rmodp_compr // F rmodp_compr //.
by apply/esym/eqP/qI.
Qed.

(*108*)
Lemma Mk_rmodp_inj (R : fieldType) (h : {poly R}) k s 
         (M : {set 'Z_k})  (p q : {poly R})  :
  Mk_spec R s M ->
  monic_irreducible_poly h -> (0 < k)%N -> rdvdp h ('X^k - 1) -> 
  poly_order h 'X k = k -> (size p <= #|M|)%N -> (size q <= #|M|)%N ->
  is_ipoly k s p -> is_ipoly k s q -> rmodp p h = rmodp q h -> p = q.
Proof.
have [|M_gt0] := leqP #|M| 0%N.
  rewrite leqn0 => /eqP->; rewrite !leqn0 !size_poly_eq0.
  by move=> ? ? ? ? ? /eqP-> /eqP->.
move=> HMk hMI k_gt0 hDxk XoE pS qS pI qI /eqP.
have hS : (1 < size h)%N by case: hMI; case.
have hI : irreducible_poly h by case: hMI.
have hM : h \is monic by case: hMI.
have hQE : divpoly_quotient h = h by rewrite /divpoly_quotient hS hM.
pose l : seq (fdivpoly hMI) := 
  map (fun i : 'I_ _ => (inDivPoly h 'X^i)) (enum M).
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
rewrite -subr_eq0 -rmodp_sub // => /eqP => u.
apply/eqP; rewrite -subr_eq0; apply/eqP/(@map_fpoly_div_inj _ h).
rewrite map_poly0.
apply: roots_geq_poly_eq0 Ul _ => //; last first.
  rewrite (@size_map_poly _ _ (divpoly_const_rmorphism h)) /=.
  rewrite size_map (leq_trans (size_add _ _)) //=  size_opp.
  by rewrite geq_max -cardE pS.
apply/allP=> i /mapP[j jI ->]; apply/eqP.
rewrite -inDivPoly_comp_horner //.
apply/val_inj => /=.
rewrite polyC0 hQE //.
apply: Mk_root_Mk => //.
  by apply/eqP; rewrite -subr_eq0 -rmodp_sub //; apply/eqP.
by rewrite -mem_enum.
Qed.

(* This is 𝒬_h *)
Definition is_iexph (R : ringType) (k s: nat) h ph :=
  exists2 p : {poly R}, ph = inDivPoly h p & is_ipoly k s p.

Inductive is_iexph_spec 
     (R : ringType) (k s : nat) (h : {poly R}) ph : bool -> Prop :=
   is_iexph_spec_true : 
    forall p, ph = inDivPoly h p -> is_ipoly k s p -> 
      @is_iexph_spec R k s h ph true
 | is_iexph_spec_false :
    (forall p, is_ipoly k s p -> ph != inDivPoly h p) -> 
      @is_iexph_spec R k s h ph false.

Definition Qh_spec (R : finRingType) k s (h :{poly R}) 
                   (M : {set {divpoly h}}) :=
  (forall x, @is_iexph_spec R k s h x (x \in M)).

Lemma Qh_Cexists (R : finRingType) k s (h : {poly R}) :
  classically (exists M : {set {divpoly h}}, Qh_spec k s M).
Proof.
rewrite /Qh_spec.
suff : classically (exists M : {set {divpoly h}}, 
      forall x : {divpoly h}, x \in (enum {divpoly h}) -> 
            uniq (enum {divpoly h}) -> 
            is_iexph_spec k s x (x \in M)).
  apply: classic_bind => [[M HM]].
  apply/classicP=> [] []; exists M => x.
  apply: HM; first by rewrite mem_enum inE.
  by apply: enum_uniq.
elim: (enum _) => [|a l] //.
  by apply/classicP=> [] []; exists setT=> x; rewrite inE.
apply: classic_bind => [[M HM]].
have /classic_bind := @classic_pick _
 (fun p : {poly R} => a = inDivPoly h p /\ is_ipoly k s p).
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
         (M : {set 'Z_k}) (Q : {set {divpoly h}})   :
  Mk_spec F s M -> Qh_spec k s Q -> p \in [char F] -> (1 < ordern k p)%N ->
  coprime k p -> monic_irreducible_poly h -> (1 < k)%N -> rdvdp h ('X^k - 1) -> 
  poly_order h 'X k = k -> (0 < s < p)%N ->
  (2 ^ minn s #|M| <= #|Q|)%N.
Proof.
move=> HMk HQh pC pO_gt1 kCp hMI k_gt1 hDxk XoE sB.
have hQE : divpoly_quotient h = h.
  by rewrite /divpoly_quotient !hMI.
rewrite -/(fdivpoly hMI) in Q HQh *.
set t := minn _ _.
have Mk_gt1 : (1 < #|M|)%N.
  apply: leq_trans pO_gt1 _.
  apply: is_iexpm_order (HMk) _  => //.
  by apply: is_iexp_fin_char; rewrite // coprime_sym.
have t_gt0 : (0 < t)%N.
  by rewrite leq_min; case/andP: sB => -> _; rewrite ltnW.
have F1 (b : bool) c : 
   (c <= s)%N -> is_ipoly k s (('X + (c%:R)%:P :{poly F}) ^+ b).
  case: b => cD; first by rewrite expr1; apply: is_ipoly_Xaddc.
  by rewrite expr0; apply: is_ipoly1.
have F2 (b : bool) c : 
   (c <= s)%N -> (size (('X + (c%:R)%:P : {poly F})%R ^+ b) <= 2)%N.
  case: b => cD; last by rewrite expr0 size_polyC oner_eq0.
  rewrite (_ : 2 = maxn(size ('X : {poly F})) (size ((c%:R)%:P : {poly F}))).
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
have mTrue2 x : (1 < t)%N -> x \in m -> exists (i : 'I_t.+1), 
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
have <- : #|m| = (2 ^ t)%N.
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
pose g b : {divpoly h}:= inDivPoly h (\prod_(i < t.+1) f b i).
have F3 b : b \in m -> (size (\prod_(i < t.+1) f b i)%R <= #|M|)%N.
  have vE i : #|((fun i0 : 'I_t.+1 => i0 != i) : pred _)| = t.
    set v := #|_|; rewrite -[t]/(t.+1.-1) -[t.+1]card_ord.
    rewrite -cardsT [in RHS](cardsD1 i) inE /=.
    by apply: eq_card => j; rewrite !inE andbT.
  move: t_gt0; rewrite leq_eqVlt => /orP[/eqP tE1 /mTrue1 [i /eqP iE]| t_gt].
    rewrite (bigD1 i) //= {1}/f; rewrite iE expr0 mul1r.
    apply: leq_trans (size_prod_leq _ _) _ => /=.
    rewrite vE leq_subLR.
  rewrite (leq_ltn_trans _ (_ : (\sum_(j < t.+1 | j != i) 2)  < _)%N) //.
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
                                    < _)%N) //.
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
  wlog: x j / (x <= j)%N => [Hw|].
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

Definition is_2power n := (n == 2 ^ log2n n)%N.
Definition isnot_2power n := (n != 2 ^ log2n n)%N.

Lemma sqrtn_gt0 n : ((0 < sqrtn n) = (0 < n))%N.
Proof.
by case: n => [|n]; rewrite // -[1%N]/(sqrtn 1) // leq_sqrtn.
Qed.

Lemma exp_Mk_upper_bound (R : comRingType) k s n a (M : {set 'Z_k}) :
   Mk_spec R s M ->  (1 < #|M|)%N ->
  (1 < k -> 1 < n -> isnot_2power n ->
  a = (log2n n) ^ 2 -> a <= ordern k n ->
  s = sqrtn (totient k) * log2n n ->   
  is_iexp R k s n ->
   n ^ (sqrtn #|M|) < 2 ^ (minn s #|M|))%N.
Proof.
move=> HMk Mk_gt1 k_gt1 m_g1 nNP aE aLo sE nIN.
set j := ordern k n in aLo.
set m := log2n n in aE sE.
have F1 : (j <= #|M|)%N by apply: is_iexpm_order.
have F2 : (#|M| <= totient k)%N by apply: is_iexpm_totient.
have F3 : (m ^ 2 <= j)%N by  move: aLo; rewrite aE.
apply: leq_trans (_ : (2 ^ m) ^ sqrtn (#|M|) <= _)%N.
  rewrite ltn_exp2r; last first.
    by rewrite sqrtn_gt0 (leq_trans _ (_ : 2 <= _))%N.
  by have := log2nP n; rewrite leq_eqVlt (negPf nNP).
case: (leqP s #|M|) => [sLM|MLs].
  case/minn_idPl : sLM => ->.
  by rewrite -expnM leq_exp2l // sE mulnC leq_mul2r // orbC leq_sqrtn.
case/ltnW/minn_idPr : MLs => ->.
rewrite -expnM leq_exp2l //.
apply: leq_trans (_ : (sqrtn #|M|) ^ 2 <= _)%N; last first.
  by have /andP[] := sqrtn_bound #|M|.
rewrite expnS expn1 leq_mul2r // orbC.
rewrite (leq_trans _ (_ : sqrtn j <= _))%N //; first by rewrite -[m]sqrnK leq_sqrtn .
by apply: leq_sqrtn.
Qed.

Definition Nbar (p q m : nat) :  {set 'I_((p * q) ^ m).+1} := 
  [set inZp (p ^ ij.1 * q ^ ij.2) | ij: 'I_m.+1 * 'I_m.+1].

(* 111 *)
(** As Nbar is defined slightly differently, this is the dual version of     **)
(** 111 for our version                                                      **)
Lemma NbarP (p q m : nat) (x : 'I_ _) :
  (1 < p)%N -> (1 < q)%N ->
  reflect (exists (ij : 'I_m.+1 * 'I_m.+1) , x = p ^ ij.1 * q ^ ij.2 :> nat)%N 
          (x \in Nbar p q m).
Proof.
move=> p_gt1 q_gt1.
apply(iffP imsetP) => [[[i j _ -> /=]]|[[i j ijE]]].
  by exists (i, j); 
     rewrite modn_small // ltnS expnMn leq_mul // leq_exp2l // -ltnS.
exists (i, j) => //; apply/val_inj => /=. 
by rewrite modn_small // ltnS expnMn leq_mul // leq_exp2l // -ltnS.
Qed.

Lemma card_Nbard p q m : (1 < p)%N -> (1 < q)%N -> coprime p q -> 
   #|Nbar p q m| = (m.+1 ^2)%N.
Proof.
move=> p_gt1 q_gt1 pCq.
rewrite card_imset=> [|/= [i1 j1] [i2 j2] /(congr1 val)].
  by rewrite card_prod card_ord expnS expn1.
rewrite /= !modn_small //; last 2 first.
- by rewrite ltnS expnMn leq_mul // leq_exp2l // -ltnS.
- by rewrite ltnS expnMn leq_mul // leq_exp2l // -ltnS.
move=> HH; congr (_,_); apply/val_eqP; rewrite /= eqn_leq.
  rewrite -(dvdn_Pexp2l _ _ p_gt1) //.
  rewrite -(dvdn_Pexp2l _ _ p_gt1) //.
  rewrite -(@Gauss_dvdl _ _ (q ^ j2)); last first.
    by apply/coprime_expl/coprime_expr.
  rewrite -HH dvdn_mulr //=.
  rewrite -(@Gauss_dvdl _ _(q ^ j1)); last first.
    by apply/coprime_expl/coprime_expr.
  by rewrite HH dvdn_mulr.
rewrite -(dvdn_Pexp2l _ _ q_gt1) //.
rewrite -(dvdn_Pexp2l _ _ q_gt1) //.
rewrite -(@Gauss_dvdr _ (p ^ i2)); last first.
  by apply/coprime_expl/coprime_expr; rewrite coprime_sym.
rewrite -HH dvdn_mull //=.
rewrite -(@Gauss_dvdr _ (p ^ i1)); last first.
  by apply/coprime_expl/coprime_expr; rewrite coprime_sym.
by rewrite HH dvdn_mull.
Qed.

End AKS.

Notation " n '⋈[' k ] p" := (introspective n k p) 
  (at level 40, format "n  '⋈[' k ]  p").
