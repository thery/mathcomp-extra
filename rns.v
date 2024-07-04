From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*                      Formalisation of Residue Number System                *)
(*                                                                            *)
(******************************************************************************)

Section RNS.

Record rns := { 
    rM : nat ;
    rl : list nat ;
    rco: [&& rM == foldr muln 1 rl, uniq rl, 0 \notin rl &
            all (fun i : nat => 
            all (fun j : nat => (i != j) ==> coprime i j) rl) rl]
  }.

Lemma rl_uniq r : uniq (rl r).
Proof. by case: r => ? ? /= /and4P[]. Qed.

Lemma rM_gt0 r : 0 < rM r.
Proof.
case: r => /= [] [|//] l /and4P[Hf _ /negP[]]; rewrite eq_sym in Hf.
elim: l Hf => //= a l IH; rewrite muln_eq0 => /orP[/eqP->//|/IH Hf].
by rewrite inE Hf orbT.
Qed.

Lemma rME r : rM r = \prod_(i <- rl r) i.
Proof. by case: r => M l /= /and4P[/eqP]; rewrite -foldrE. Qed.

Lemma rM_dvd r (i : nat) : i \in rl r -> i %| rM r.
Proof.
case: r => M l /= /and4P[/eqP-> _ _ _].
elim: l i => //= a l IH i.
rewrite inE => /orP[/eqP->|/IH//]; first by apply: dvdn_mulr.
by apply: dvdn_mull.
Qed.

Lemma rM_dvd_div r (i j : nat) : 
  i != j -> i \in rl r -> j \in rl r -> i %| (rM r %/ j).
Proof.
move=> iDj iI jI; rewrite dvdn_divRL; last by apply: rM_dvd.
have rU := rl_uniq r.
rewrite rME (bigD1_seq j) //= big_mkcond_idem //= (bigD1_seq i) //= iDj.
by rewrite mulnA [j * _]mulnC; apply: dvdn_mulr.
Qed.

Lemma coprime_prod (i : nat) (P : pred nat) l :
  (forall j, P j -> j \in l -> coprime i j) -> 
  coprime i (\prod_(j <- l | P j) j).
Proof.
elim: l => [|a l IH] Hj /=; first by rewrite big_nil coprimen1.
have Hj' : forall j : nat, P j -> j \in l -> coprime i j.
  by move=> ? ? jI; apply: Hj => //; rewrite inE jI orbT.
rewrite big_cons; case E: P; last by apply: IH.
by rewrite coprimeMr IH ?andbT ?Hj ?inE ?eqxx.
Qed.

Lemma rl_coprime r (i j : nat) :
   i \in rl r -> j \in rl r -> i != j -> coprime i j.
Proof.
case: r => /= M l /and4P[_ _ _] /allP /= Hi iI jI iDj.
by have /allP/(_ _ jI) := Hi _ iI; rewrite iDj.
Qed.

Lemma coprime_rM_div r (i : nat) : i \in rl r -> coprime (rM r %/ i) i.
Proof.
move=> iI.
rewrite rME (bigD1_seq i) //=; last by apply: rl_uniq.
rewrite mulKn; last by case: i iI; case: r => ? ? /= /and4P[]; case: (_ \in _).
rewrite coprime_sym; apply: coprime_prod => j jDi jI.
by apply: rl_coprime iI jI _; rewrite eq_sym.
Qed.

Definition rnorm r l := all2 (fun i j => j < i) (rl r) l.

Lemma size_rnorm r l : rnorm r l -> size l = size (rl r).
Proof. by rewrite /rnorm all2E => /andP [/eqP]. Qed.

Definition rn_rl (r : rns) n := [seq (n %% i) | i <- rl r].

Lemma rnorm_rn_rl r n : rnorm r (rn_rl r n).
Proof.
rewrite /rnorm all2E size_map eqxx /=.
apply/allP =>/= [] [x y] /(nthP (0, 0)) [i].
rewrite size_zip size_map minnn nth_zip ?size_map // => iLs [<- <-] /=.
rewrite (nth_map 0) // ltn_mod.
by case: nth (mem_nth 0 iLs) => //; case: {iLs}r => M l /= /and4P[]; 
   case: in_mem.
Qed.

Definition rl_rn (r : rns) l := 
  (foldr addn 0 [seq (let a := rM r %/ j.1 in 
                     let b := (egcdn a j.1).1 in 
                     (a * ((b %% j.1 * j.2) %% j.1))) | 
                      j <- zip (rl r) l]) %% rM r.

Lemma rl_rnE r l : rl_rn r l = (\sum_(i <- zip (rl r) l) 
                       let a := rM r %/ i.1 in 
                       let b := (egcdn a i.1).1 in 
                       (a * ((b %% i.1 * i.2) %% i.1))) %% rM r.
Proof.
congr (_ %% _); rewrite unlock /reducebig /=.
by elim: zip => //= a l1 ->.
Qed.

Lemma ltn_rl_rn r l : rl_rn r l < rM r.
Proof. by rewrite ltn_mod; apply: rM_gt0. Qed.

Lemma size_rn_rl r n : size (rn_rl r n) = size (rl r).
Proof. by rewrite size_map. Qed.

Lemma zip_uniql (S T : eqType) (s : seq S) (t : seq T) : 
  uniq s -> uniq (zip s t).
Proof.
case: s t => [|s0 s] [|t0 t] //; apply: contraTT => /(uniqPn (s0, t0)) [i [j]].
case=> o z; rewrite !nth_zip_cond !ifT ?js ?(ltn_trans o)// => -[n _].
by apply/(uniqPn s0); exists i, j; rewrite o n (leq_trans z) ?size_zip?geq_minl.
Qed.

Lemma zip_uniqr (S T : eqType) (s : seq S) (t : seq T) : 
  uniq t -> uniq (zip s t).
Proof.
case: s t => [|s0 s] [|t0 t] //; apply: contraTT => /(uniqPn (s0, t0)) [i [j]].
case=> o z; rewrite !nth_zip_cond !ifT ?js ?(ltn_trans o)// => -[_ n].
by apply/(uniqPn t0); exists i, j; rewrite o n (leq_trans z) ?size_zip?geq_minr.
Qed.

Lemma mem_zip (S T : eqType) (s : seq S) (t : seq T) a : 
  a \in zip s t -> a.1 \in s /\ a.2 \in t.
Proof.
elim: s t => [|b s IH] [|c t]; rewrite //= !inE => /orP[/eqP->/=|/IH[-> ->]].
  by rewrite !eqxx.
by rewrite !orbT.
Qed.

Lemma index_uniq_zipl (S T : eqType) (s : seq S) (t : seq T) a : 
  uniq s -> a \in zip s t -> index a (zip s t) = index a.1 s.
Proof.
case: a => a b /=; elim: s t => [|c s IH] [|d t]; rewrite //= ?inE.
rewrite eq_sym.
case: eqP => /=; first by case => -> _; rewrite !eqxx.
move=> cdDab /andP[cNIs sU] abI.
rewrite ifN; first by congr (_.+1); apply: IH.
by apply: contra cNIs => /eqP->; have [] := mem_zip abI.
Qed.

Lemma neq_uniq_zipl (S T : eqType) (s : seq S) (t : seq T) a b : 
  uniq s -> a \in zip s t -> b \in zip s t -> (a != b) -> a.1 != b.1.
Proof.
case: a => a1 a2; case: b => b1 b2 /=.
elim: s t => [|c s IH] [|d t]; rewrite //= ?inE.
case: eqP => /=.
  case=> <- <- /andP[a1I sU] _.
  case: eqP => /=; first by case=> <- <-; rewrite eqxx.
  by move=> _ /mem_zip[/= ? _] _; apply: contra a1I => /eqP->.
move=> _ /andP[cI sU] a1a2I.
case: eqP => /=; last by move=> _ /(IH _ sU a1a2I).
case=> -> -> _ _; apply: contra cI => /eqP<-.
by have [] := mem_zip a1a2I.
Qed.

Lemma rl_rnK r l : rnorm r l -> rn_rl r (rl_rn r l) = l.
Proof.
move=> Hr; apply: (@eq_from_nth _ 0) => [|i].
  by rewrite size_map -(size_rnorm Hr).
have Hs : size (zip (rl r) l) = size (rl r).
  by rewrite size_zip (size_rnorm Hr) minnn.
rewrite size_rn_rl => iLs.
rewrite (nth_map 0) // rl_rnE (bigD1_seq (nth (0,0) (zip (rl r) l) i)) //=; 
  last 2 first.
- by apply: mem_nth; rewrite Hs.
- by apply/zip_uniql/rl_uniq.
rewrite (nth_zip 0 0) /=; last by rewrite (size_rnorm Hr).
set a := nth _ _ _; set b := nth _ _ _.
have abE : (a, b) = nth (0, 0) (zip (rl r) l) i.
  by rewrite nth_zip //; apply/sym_equal/size_rnorm.
have aI : a \in rl r by apply/mem_nth.
rewrite modn_dvdm; last by apply/rM_dvd/mem_nth.
rewrite -modnDmr -modn_summ modnDmr.
rewrite big_mkcond_idem //=.
rewrite big_seq big1 /=; last first.
  case => i1 j1 i1j1I /=; case: eqP => //= /eqP i1j1D.
  have i1Da : i1 != a.
    apply: neq_uniq_zipl i1j1I _ i1j1D; first by apply: rl_uniq.
    by rewrite abE; apply: mem_nth; rewrite Hs.
  have /= [i1E j1E] := mem_zip i1j1I.
  rewrite -modnMml.
  suff -> : (rM r %/ i1)  %% a = 0 by rewrite mul0n mod0n.
  by apply/eqP/rM_dvd_div => //; rewrite eq_sym.
rewrite addn0 modnMml modnMmr.
case: egcdnP => [|km kl kmlE _]//=.
  rewrite divn_gt0; last first.
    by case: a {abE}aI; case: {Hr Hs iLs}r => /= ? ? /and4P[]; case: (_ \in _).
  apply: dvdn_leq; first by apply: rM_gt0.
  by apply: rM_dvd.
rewrite mulnCA mulnA kmlE -modnMml modnMDl modnMml.
have /eqP-> : coprime (rM r %/ a) a by apply: coprime_rM_div.
rewrite mul1n modn_small //.
rewrite /rnorm all2E in Hr.
have /andP[/eqP Hs1 /allP/(_ (a, b)) /=] := Hr.
apply; rewrite -nth_zip //.
by apply: mem_nth; rewrite Hs.
Qed.

Lemma rn_rl_inj r m1 m2 :
  m1 < rM r -> m2 < rM r -> rn_rl r m1 = rn_rl r m2 -> m1 = m2.
Proof.
wlog : m1 m2 / m1 <= m2 => [Hr m1L m2L rnE|m1Lm2 m1L m2L rnE].
  case: (leqP m1 m2)=> m1Lm2; first by apply: Hr.
  by apply/sym_equal/Hr => //; apply: ltnW.
suff : m2 - m1 = 0 by move/eqP=> H; apply/eqP; rewrite eqn_leq m1Lm2.
suff: rM r %| m2 - m1.
  have : m2 - m1 < rM r.
    by apply: leq_ltn_trans (leq_subr _ _) m2L.
  case: (_ - _) => // u Hlt Hd.
  have := dvdn_leq (isT : 0 < u.+1) Hd.
  by rewrite leqNgt Hlt.
suff : forall i : nat, i \in rl r -> i %| m2 - m1.
  rewrite rME.
  have :  forall i j : nat, i \in rl r -> j \in rl r -> i != j -> coprime i j.
    move=> i j iI jI iDj.
    case : {m1L m2L rnE}r iI jI => /= ? ? /and4P[_ _ _ /allP HH] iI jI.
    by have /allP/(_ _ jI) := HH _ iI; rewrite iDj.
  elim: rl (rl_uniq r) => /= [|a rl IH /andP[aNI Hu] Hc Hi].
    by rewrite big_nil dvd1n.
  rewrite big_cons Gauss_dvd; last first.
    apply: coprime_prod => i _ iI; apply: Hc; rewrite ?inE ?eqxx ?iI ?orbT //.
    by apply: contra aNI => /eqP->.
  rewrite Hi ?inE ?eqxx //= IH // => [i j Hi1 Hj1|i Hi1].
    by apply: Hc; rewrite inE ?Hi1 ?Hj1 orbT.
  by rewrite Hi // inE Hi1 orbT.
move=> i iI.
suff /eqP : m1 = m2 %[mod i].
  by rewrite -{1}[m1]add0n -{1}(subnK m1Lm2) eqn_modDr mod0n eq_sym.
have : m1 %% i = nth 0 (rn_rl r m1) (index i (rl r)).
  by rewrite (nth_map 0) ?index_mem ?nth_index.
by rewrite rnE (nth_map 0) ?index_mem ?nth_index.
Qed.

Lemma rn_rlK r m : m < rM r -> rl_rn r (rn_rl r m) = m.
Proof.
move=> mLM.
apply: (@rn_rl_inj r) => //; first by rewrite ltn_mod; apply: rM_gt0.
by apply/rl_rnK/rnorm_rn_rl.
Qed.

Definition r_ex := {|rM := 5187; rl := [::3; 7; 13; 19]; rco := isT|}.

Compute (rl_rn r_ex (rn_rl r_ex  121)). 

Compute rn_rl r_ex 147.
Compute rl_rn r_ex [::0; 0; 4; 14].

Definition rN_op (r : rns) (f : nat -> nat -> nat) l1 l2 := 
 [seq (f i.1.1 i.1.2) %% i.2 | i <- zip (zip l1 l2) (rl r)].

Lemma rnorm_rN_op r f l1 l2 : 
  rnorm r l1 -> rnorm r l2 -> rnorm r (rN_op r f l1 l2).
Proof.
rewrite /rnorm !all2E => [] /andP[/eqP Hs1 Ha1] /andP[/eqP Hs2 Ha2].
rewrite size_map !size_zip -Hs1 -Hs2 !minnn eqxx /=.
apply/allP => /= i.
rewrite /rN_op.
have : 0 \notin rl r by case: (r) => ? ? /= /and4P[].
elim: rl l1 l2 {Ha1 Ha2}Hs1 Hs2 => /= [|a l IH [|b l1] [|c l2] /= H1 H2 H3] //.
  by do 2 case=> //.
rewrite !inE => /orP[/eqP->/=|].
  by rewrite ltn_mod //; case: (a) H3; rewrite ?inE.
rewrite inE negb_or in H3; have /andP[H4 H5] := H3.
by apply: IH => //; [case: H1 | case: H2].
Qed.

Definition rN_add r := rN_op r addn.

Lemma rnorm_rN_add r l1 l2 : 
  rnorm r l1 -> rnorm r l2 -> rnorm r (rN_add r l1 l2).
Proof. by apply: rnorm_rN_op. Qed.

Lemma rN_add_rn_rl r m n : 
  rN_add r (rn_rl r m) (rn_rl r n) = rn_rl r ((m + n) %% rM r).
Proof.
rewrite /rn_rl /rN_add /rN_op.
elim: rl (@rM_dvd r) => //= a l IH Hd.
rewrite IH; last by move => i Hi; apply: Hd; rewrite inE Hi orbT.
by rewrite modnDml modnDmr modn_dvdm // Hd // inE eqxx.
Qed.

Lemma rN_add_rl_rn r l1 l2 : 
  rnorm r l1 -> rnorm r l2 -> 
  rl_rn r (rN_add r l1 l2) = rl_rn r l1 + rl_rn r l2 %[mod (rM r)].
Proof.
move=> Hl1 Hl2.
rewrite -[in LHS](rl_rnK Hl1) -[in LHS](rl_rnK Hl2).
by rewrite rN_add_rn_rl rn_rlK ?modn_mod // ltn_mod // rM_gt0.
Qed.

Definition rN_mul r := rN_op r muln.

Lemma rnorm_rN_mul r l1 l2 : 
  rnorm r l1 -> rnorm r l2 -> rnorm r (rN_mul r l1 l2).
Proof. by apply: rnorm_rN_op. Qed.

Lemma rN_mul_rn_rl r m n : 
  rN_mul r (rn_rl r m) (rn_rl r n) = rn_rl r ((m * n) %% rM r).
Proof.
rewrite /rn_rl /rN_mul /rN_op.
elim: rl (@rM_dvd r) => //= a l IH Hd.
rewrite IH; last by move => i Hi; apply: Hd; rewrite inE Hi orbT.
by rewrite modnMml modnMmr modn_dvdm // Hd // inE eqxx.
Qed.

Lemma rN_mul_rl_rn r l1 l2 : 
  rnorm r l1 -> rnorm r l2 -> 
  rl_rn r (rN_mul r l1 l2) = rl_rn r l1 * rl_rn r l2 %[mod (rM r)].
Proof.
move=> Hl1 Hl2.
rewrite -[in LHS](rl_rnK Hl1) -[in LHS](rl_rnK Hl2).
by rewrite rN_mul_rn_rl rn_rlK ?modn_mod // ltn_mod // rM_gt0.
Qed.

Definition rN_inv (r : rns) l := 
 [seq (egcdn i.1 i.2).1 %% i.2 | i <- zip l (rl r)].

Lemma zip_nill (S T : eqType) l : zip [::] l = [::] :> seq (S * T).
Proof. by case: l. Qed.

Lemma zip_nilr (S T : eqType) l : zip [::] l = [::] :> seq (S * T).
Proof. by case: l. Qed.

Lemma rnorm_rN_inv r l : rnorm r l -> rnorm r (rN_inv r l).
Proof.
rewrite /rnorm /rN_inv !all2E => [] /andP[/eqP Hs Ha].
rewrite size_map size_zip Hs minnn eqxx /=.
apply/allP => /= i.
have : 0 \notin rl r by case: (r) => ? ? /= /and4P[].
elim: rl l {Ha}Hs => /= [|a rl IH [|b l] /= H1 H2] //; first by case=> //.
rewrite !inE => /orP[/eqP->/=|].
  by rewrite ltn_mod //; case: (a) H2; rewrite ?inE.
rewrite inE negb_or in H2; have /andP[H3 H4] := H2.
by apply: IH => //; case: H1.
Qed.

Lemma rN_inv_rn_rl r m : 
  coprime m (rM r) ->
  rN_mul r (rn_rl r m) (rN_inv r (rn_rl r m)) = rn_rl r 1.
Proof.
rewrite /rN_inv /rN_mul /rN_op /rn_rl => Hc.
elim: rl (@rM_dvd r) => //= a l IH Hd.
congr (_ :: _); last by apply: IH => i Hi; apply: Hd; rewrite inE Hi orbT.
have aD : a %| rM r by apply: Hd; rewrite inE eqxx.
have aC : coprime (m %% a) a by rewrite coprime_modl; apply: coprime_dvdr aD _.
rewrite modnMml modnMmr.
case E: (a %| m).
  suff ->: a = 1 by rewrite modn1.
  have : a %| gcdn (rM r) m by rewrite dvdn_gcd aD.
  by rewrite gcdnC (eqP Hc) dvdn1 => /eqP.
case: egcdnP => [|km kl kmlE _]//=.
  by move: E; rewrite /dvdn; case: (m %% a).
by rewrite -modnMml mulnC kmlE (eqP aC) modnMDl.
Qed.

Definition XRNS := [:: 0; 0; 4; 14].
Definition YRNS := [:: 1; 3; 5; 12].
Definition ZRNS := [:: 1; 5; 7; 10].

Compute rN_add r_ex XRNS YRNS.
Compute rl_rn r_ex (rN_add r_ex XRNS YRNS).

Compute rN_mul r_ex XRNS YRNS.
Compute rl_rn r_ex (rN_mul r_ex XRNS YRNS).

Compute rN_mul r_ex ZRNS (rN_inv r_ex YRNS).
Compute rl_rn r_ex (rN_mul r_ex ZRNS (rN_inv r_ex YRNS)).

End RNS.
