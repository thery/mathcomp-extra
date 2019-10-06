From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Matroid                                                                    *)
(*   M : Matroid  == M is a matroid whose elements are x : M                  *)
(*   msets M      == the set of set associated to the matroid                 *)
(*   mrank s      == the rank of a set                                        *)
(* is_rset s1 s2  == s1 is a set that realizes the rank of s2                 *)
(*   mclosure s   == the closure of a set                                     *)
(*   mflats M     == the set of flats                                         *)
(* mcover s1 s2   == s1 is smallest flats that is a proper superset of s2    *)
(******************************************************************************)

Record Matroid : Type := 
{ msort :> finType; 
  msets : {set {set msort}};
  wf_msets : [&& set0 \in msets,
   [forall s1 : {set msort}, forall s2 : {set msort}, 
     ((s1 \subset s2) && (s2 \in msets)) ==> (s1 \in msets)] &
   [forall s1, forall s2, [&& s1 \in msets, s2 \in msets & #|s1| < #|s2|] ==> 
     [exists x, (x \in s2 :\: s1) && ((x |: s1) \in msets) ]]
             
         
  ] }.

Section Matroid.

Variable M : Matroid.
Implicit Type s : {set M}.

(* P1I *)
Lemma msets0 : set0 \in msets M.
Proof. by have /and3P[] := wf_msets M. Qed.

(* P2I *)
Lemma msets_sub s1 s2 : 
  s1 \subset s2 -> s2 \in msets M -> s1 \in msets M.
Proof.
move=> s1Ss2 s2IM.
have /and3P[_ /forallP/(_ s1)/forallP/(_ s2) H _] := wf_msets M.
by have /implyP->// := H; rewrite s1Ss2.
Qed.

(* P3I *)
Lemma msets_card s1 s2 : 
  s1 \in msets M -> s2 \in msets M -> #|s1| < #|s2| -> 
  exists2 x, x \in s2 :\: s1 & (x |: s1) \in msets M.
Proof.
move=> s1IM s2IM s1Ls2.
have /and3P[_ _ /forallP/(_ s1)/forallP/(_ s2) H] := wf_msets M.
have /implyP := H.
rewrite s1IM s2IM => /(_ s1Ls2) /existsP[x /andP[Hx1 Hx2]].
by exists x.
Qed.

Definition mrank s := \max_(i in msets M | i \subset s) #|i|.

Notation " 'rk' s " := (mrank s) (at level 40).

Definition is_rset s1 s2 :=
  [/\ #|s1| = mrank s2, s1 \in msets M & s1 \subset s2].


Lemma leq_mrank (s1 s2 : {set M}) :
  s1 \in msets M -> s1 \subset s2 -> #|s1| <= mrank s2.
Proof.
by move=> s1IM s1Ss2; apply: leq_bigmax_cond; rewrite s1IM.
Qed.

Lemma mrankE s : exists s1 : {set M}, is_rset s1 s.
Proof.
pose f (i : {set M}) := if i \subset s then #|i| else 0.
have /eq_bigmax_cond :  0 < #|msets M|.
  by apply/card_gt0P; exists set0; exact: msets0.
move=> /(_ f)[rs]; rewrite -big_mkcondr => rsIM rsE.
have [rsSs|NrsSs] := boolP (rs \subset s).
  have rS : mrank s = #|rs| by rewrite /mrank rsE /f rsSs.
  by exists rs; split.
exists set0; split; first by rewrite /mrank rsE /f (negPf NrsSs) cards0.
  by apply: msets0.
by apply: sub0set.
Qed.

(* P1R *)
Lemma mrank_card s : mrank s <= #|s|.
Proof.
by apply/bigmax_leqP => s1 /andP[_ /subset_leq_card].
Qed.

Lemma mrank_set0 : mrank set0 = 0.
Proof.
by apply/eqP; rewrite -leqn0 -(@cards0 M) mrank_card.
Qed.

Lemma mrank_set1 a : mrank [set a] <= 1.
Proof. by rewrite -(cards1 a) mrank_card. Qed.

(* P2R *)
Lemma mrank_subset s1 s2 : s1 \subset s2 -> mrank s1 <= mrank s2.
Proof.
move=> s1Ss2; apply/bigmax_leqP => e /andP[Hs1 Hs2].
by apply: leq_bigmax_cond; rewrite Hs1 (subset_trans Hs2).
Qed.

Lemma mrank_compl s1 s2 : 
  s1 \in msets M ->  s1 \subset s2 -> 
  exists2 s3 : {set M}, s1 \subset s3 & is_rset s3 s2.
Proof.
elim: {s1}_.+1 {-2}s1 (ltnSn (#|s2 :\: s1|)) => //
    n IH s1 s1Ds2 s1IM s1Ss2.
have [s3 [Rs3 s3IM s3Ss2]] := mrankE s2.
have := leq_mrank s1IM s1Ss2.
rewrite -Rs3 leq_eqVlt => /orP[/eqP s1Es3|s1Ls3].
  by exists s1 => //; split => //; rewrite s1Es3.
have [x xIs3s1 xs1IM] := msets_card s1IM s3IM s1Ls3.
case: (IH (x |: s1)) => // [||s4 s4IM s4rS].
- move: xIs3s1; rewrite in_setD => /andP[xNIs1 xIs3].
  move : s1Ds2; rewrite (cardsD1 x) setDDl setUC in_setD xNIs1 /=.
  by rewrite (subsetP s3Ss2) //= ltnS.
- rewrite subUset s1Ss2 andbT sub1set.
  apply: (subsetP (_ : s3 :\: s1 \subset s2)) => //.
  by apply: subset_trans (subsetDl _ _) _.
exists s4 => //.
by apply: subset_trans (subsetUr _ _) s4IM.
Qed.

(* P3R *)
Lemma mrank_mod s1 s2 : mrank (s1 :|: s2) + mrank (s1 :&: s2) <= mrank s1 + mrank s2.
Proof.
have [s3 [rS3 s3IM s3Ss1Is2]] := mrankE (s1 :&: s2).
have s3Ss1Us2 : s3 \subset s1 :|: s2.
  apply: subset_trans s3Ss1Is2 _.
  by apply/subsetP => i; rewrite in_setI in_setU => /andP[->].
have [s4 s3Ss4 [<- s4IM s4Ss1Us2]] := mrank_compl s3IM s3Ss1Us2.
pose s5 := s4 :&: s1; pose s6 := s4 :&: s2.
have -> : s4 = s5 :|: s6 by rewrite -setIUr; apply/sym_equal/setIidPl.
have /eqP-> : mrank (s1 :&: s2) == #|s5 :&: s6|.
  rewrite eqn_leq; apply/andP; split; last first.
    apply: leq_mrank.
      by apply: msets_sub s4IM; rewrite -setIA subsetIl.
    by apply: setISS; apply: subsetIr.
  rewrite -rS3; apply: subset_leq_card.
  by rewrite -setIIr subsetI s3Ss4.
rewrite cardsUI.
apply: leq_add.
  apply: leq_mrank => //; first by apply: msets_sub (subsetIl _ _) _.
  by apply: subsetIr.
apply: leq_mrank => //; first by apply: msets_sub (subsetIl _ _) _.
by apply: subsetIr.
Qed.

Definition mclosure s := [set x | mrank (x |: s) == mrank s].

Notation " 'cl' s " := (mclosure s) (at level 40).

Lemma mclosure_setT : mclosure [set: M] = [set: M].
Proof.
by apply/setP=> x; rewrite !inE (_ : _ :|: _ = [set: M]) ?setUT ?eqxx.
Qed.

(* P1P *)
Lemma mclosure_sub s : s \subset mclosure s.
Proof.
apply/subsetP=> x; rewrite !inE => xIs.
rewrite (_ : _ |: _ = s) //.
by apply/setUidPr/subsetP=> y; rewrite inE => /eqP->.
Qed.

Lemma mclosure_mrank s : mrank (mclosure s) = mrank s.
Proof.
have := mrank_subset (mclosure_sub s).
rewrite leq_eqVlt => /orP[/eqP<-//|sLcls].
have [s1 [rs1E s1IM s1Ss]] := mrankE s.
have [s2 [rs2E s2IM s2Ss]] := mrankE (cl s).
case: (msets_card s1IM s2IM); first by rewrite rs1E rs2E.
move=> x; rewrite inE => /andP[xNIs1 xIs2] xs1IM.
have /(leq_mrank xs1IM) : x |: s1 \subset x |: s by apply: setUS.
rewrite cardsU1 xNIs1.
have: x \in mclosure s by apply: (subsetP s2Ss).
by rewrite inE => /eqP->; rewrite add1n -rs1E ltnn.
Qed.

(* P2P *)
Lemma mclosure_invo s : mclosure (mclosure s) = mclosure s.
Proof.
apply/eqP; rewrite eqEsubset mclosure_sub andbT.
apply/subsetP=> x; rewrite !inE mclosure_mrank => /eqP rkxsE.
rewrite eqn_leq -{1}rkxsE !mrank_subset //; first by apply: subsetUr.
by apply/setUS/mclosure_sub.
Qed.

(* P3P *)
Lemma mclosure_subset s1 s2 : s1 \subset s2 -> mclosure s1 \subset mclosure s2.
Proof.
move=> s1Ss2; apply/subsetP=> x; rewrite !inE => /eqP rxs1E.
rewrite eqn_leq [_ <= mrank (_ |: _)]mrank_subset ?andbT; last by apply: subsetUr.
have->: x |: s2 = (x |: s1) :|: s2.
  rewrite -setUA; congr (_ |: _).
  by apply/sym_equal/setUidPr.
rewrite -(leq_add2r (mrank ((x |: s1) :&: s2))) (addnC (mrank s2)).
suff {2}->: mrank ((x |: s1) :&: s2) = mrank (x |: s1) by apply: mrank_mod.
have [xIs2|xNIs2] := boolP (x \in s2).
  congr mrank; apply/setIidPl.
  by rewrite subUset /= sub1set xIs2.
rewrite rxs1E setIUl (_ : _ :&: _ = set0) ?set0U.
  by congr mrank; apply/setIidPl.
apply/setP=> y; rewrite !inE; case: eqP => [->|] //.
by rewrite (negPf xNIs2).
Qed.

Lemma mclosureU1 a s : a \in mclosure s -> mclosure (a |: s) = mclosure s.
Proof.
rewrite inE => /eqP aIs; apply/eqP; rewrite eqEsubset andbC mclosure_subset ?subsetUr //=.
apply/subsetP=> b; rewrite !inE => /eqP bIas.
rewrite eqn_leq andbC mrank_subset ?subsetUr //=.
by rewrite -aIs -bIas mrank_subset // setUCA subsetUr.
Qed.

Lemma mrank_setU1 a s : a \notin mclosure s -> mrank (a |: s) = (mrank s).+1.
Proof.
rewrite inE => aIs; have := mrank_mod [set a] s.
have-> :[set a] :&: s = set0.
  apply/setP=> y; rewrite !inE; case: eqP => // -> /=.
  apply/idP => Ha; case/eqP: aIs.
  by congr mrank; apply/setUidPr; rewrite sub1set.
rewrite mrank_set0 addn0.
case: mrank (mrank_set1 a) => [_ asLs|[_|]//].
  case/negP: aIs.
  by rewrite eqn_leq andbC mrank_subset ?subsetUr.
rewrite leq_eqVlt => /orP[/eqP//|asLs].
case/negP: aIs.
by rewrite eqn_leq andbC mrank_subset ?subsetUr.
Qed.

(* P4P *)
Lemma mclosure_ex a b s : 
  b \in (mclosure (a |: s) :\: mclosure s) -> 
  a \in (mclosure (b |: s) :\: mclosure s).
Proof.
rewrite inE => /andP[bNIs bIas].
have [/mclosureU1 asE|aNIs] := boolP (a \in mclosure s).
  by case/negP: bNIs; rewrite -asE.
rewrite inE aNIs /=.
move: bIas; rewrite !inE setUCA => /eqP->.
by rewrite !mrank_setU1.
Qed.

Definition mflats : {set {set M}} := [set s | mclosure s == s].

(* P1P *)
Lemma mflats_setT : [set: M] \in mflats.
Proof. by rewrite inE mclosure_setT eqxx. Qed.

(* P2P *)
Lemma mflats_setI s1 s2 : s1 \in mflats -> s2 \in mflats -> s1 :&: s2 \in mflats.
Proof.
rewrite !inE => s1F s2F.
rewrite eqEsubset mclosure_sub andbT subsetI.
by rewrite  -{2}(eqP s1F) -{3}(eqP s2F) !mclosure_subset ?subsetIr ?subsetIl.
Qed.

Lemma mclosure_mflats s : mclosure s \in mflats.
Proof. by rewrite inE mclosure_invo. Qed.

Lemma mflats_mclosure s : s \in mflats -> mclosure s = s.
Proof. by rewrite inE => /eqP. Qed.

Definition mcover (s1 s2 : {set M}) := 
  [&& s1 \in mflats, s2 \in mflats, s2 \proper s1 &
      [forall s, [&& s \in mflats, s2 \subset s & s \subset s1]
                                  ==> ((s == s1) || (s == s2))]].

Lemma mcoverP s1 s2 :
  reflect 
    [/\ s1 \in mflats, s2 \in mflats, s2 \proper s1 &
        forall s, s \in mflats -> s2 \subset s -> s \subset s1 ->
                                    (s = s1) \/ (s = s2)]
      (mcover s1 s2).
Proof.
apply: (iffP and4P) => [] [H1 H2 H3 H4]; split => //.
  move=> s V1 V2 V3.
  have /forallP/(_ s)/implyP H5 := H4.
  have [] := orP (H5 _) => [|/eqP->|/eqP->] //.
  - by rewrite V1 V2.
  - by left.
  by right.
apply/forallP=> s; apply/implyP => /and3P[V1 V2 V3].
by case: (H4 _ V1 V2 V3) => ->; rewrite eqxx // orbT.
Qed.

Lemma mcoverE s1 s2 : 
   mcover s1 s2 ->
   exists2 a, a \notin s2 & s1 = mclosure (a |: s2).
Proof.
move=> /mcoverP[s1F s2F s2Ps1 HS].
have /properP[s2Ss1 [a aIs1 aNIs2]] := s2Ps1.
exists a => //.
case (HS (mclosure (a |: s2))) => //.
- by apply: mclosure_mflats.
- apply: subset_trans (subsetUr _ _) (mclosure_sub _).
- rewrite -(mflats_mclosure s1F).
  apply: mclosure_subset.
  by rewrite subUset sub1set aIs1.
move=> /setP/(_ a).
by rewrite (subsetP (mclosure_sub _)) ?(negPf aNIs2) // !inE eqxx.
Qed.

Lemma mcover_sub_ex s1 s2 : 
  s1 \in mflats -> s2 \in mflats -> s1 \proper s2 -> 
  exists2 s, mcover s s1 & s \subset s2.
Proof.
move=> s1F.
elim: {s2}_.+1 {-2}s2 (ltnSn #|s2|) => // n IH s2 s2Ln s2F s1Ps2.
have [s2Cs1|] := boolP (mcover s2 s1).
  by exists s2 => //; case/andP: s1Ps2.
rewrite {1}/mcover s1F s2F s1Ps2 negb_forall => /existsP[s3].
rewrite negb_imply negb_or => /and3P[/and3P[s3F s1Ss3 s3Ss2] s3Ds2 s3Ds1].
have [|||s sCs1 sSs3] := IH s3 => //.
- have /proper_card/leq_trans->// : s3 \proper s2 by rewrite properEneq s3Ds2.
- by rewrite properEneq eq_sym s3Ds1.
by exists s => //; apply: subset_trans sSs3 _.
Qed.

(* Maybe not the shortest proof ... *)
Lemma mcover_mclosure a s1 : 
  s1 \in mflats -> a \notin s1 -> mcover (mclosure (a |: s1)) s1.
Proof.
move=> s1F aNIs1.
have [|s sCs1 s1Sas1] := mcover_sub_ex s1F (mclosure_mflats (a |: s1)).
  rewrite properE (subset_trans _ (mclosure_sub _)) ?subsetUr //=.
  apply/negP=> /subsetP/(_ a).
  rewrite (negPf aNIs1) (subsetP (mclosure_sub _)).
    by move=> /(_ isT).
  by rewrite !inE eqxx.
have [b bNIs1 sE] := mcoverE sCs1.
suff/eqP->: cl(a |: s1) == cl(b |: s1) by rewrite -sE.
rewrite eqEsubset; apply/andP; split; last first.
  by rewrite -sE (subset_trans _ s1Sas1).
rewrite -(mclosure_invo (b |: _)) mclosure_subset //.
rewrite subUset sub1set -{2}(mflats_mclosure s1F) mclosure_subset ?andbT ?subsetUr //.
suff : a \in (mclosure (b |: s1) :\: mclosure s1) by rewrite inE => /andP[].
apply: mclosure_ex.
rewrite inE mflats_mclosure // bNIs1 (subsetP s1Sas1) // sE.
by rewrite (subsetP (mclosure_sub _)) // !inE eqxx.
Qed.

Lemma mcoverPU s1 s2 : 
   s2 \in mflats ->
   reflect 
     (exists2 a, a \notin s2 & s1 = mclosure (a |: s2))
     (mcover s1 s2).
Proof.
move=> s2F.
apply: (iffP idP)=> [|[a aNIs2->]]; first by apply: mcoverE.
by apply: mcover_mclosure.
Qed.

Lemma mcoverI s s1 s2 : 
  mcover s1 s -> mcover s2 s -> s1 != s2 -> s1 :&: s2 = s.
Proof.
move=> /mcoverP[s1F sF sPs1 s1Min] /mcoverP[s2F _ sPs2 s2Min] s1Ds2.
have s1s2F : s1 :&: s2 \in mflats by apply: mflats_setI.
case: (s1Min _ s1s2F)=> // [||s1s2E1]; first by rewrite subsetI !proper_sub.
  by apply: subsetIl.
case: (s2Min _ s1s2F)=> // [||s1s2E2]; first by rewrite subsetI !proper_sub.
  by apply: subsetIr.
by case/eqP: s1Ds2; rewrite -s1s2E1.
Qed.
 
(* P3P *)
Lemma mflats_partition s : 
  s \in mflats -> partition [set (s1 :\: s) | s1 in {set M} & mcover s1 s] (~: s).
Proof.
move=> sF.
apply/and3P; split.
- apply/eqP/setP => x; rewrite inE.
  have [xIs/= |xNIs/=] := boolP (x \in s); apply/idP.
    move=> /bigcupP/= [s1] /imsetP/= [s2 _ ->].
    by rewrite inE xIs.
  apply/bigcupP; exists (mclosure (x |: s) :\:s).
    apply/imsetP; exists (mclosure (x |: s)) => //.
    by rewrite inE mcover_mclosure.
  by rewrite inE xNIs (subsetP (mclosure_sub _)) // !inE eqxx.
- apply/trivIsetP=> /= s1 s2 /imsetP/= [s3].
  rewrite inE => s3Cs -> /imsetP/= [s4].
  rewrite inE => s4Cs -> s3Ds4.
  rewrite -setI_eq0 -setDIl (mcoverI s3Cs) ?setDv //.
  by apply: contra s3Ds4 => /eqP->.
apply/imsetP=> /= [] [s1].
rewrite inE => /and4P[_ _ sPs1 _] /eqP.
rewrite eq_sym setD_eq0 => s1Ss.
case/negP : (proper_neq sPs1).
by rewrite eqEsubset s1Ss proper_sub.
Qed.

End Matroid.
