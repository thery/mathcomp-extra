From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Matroid                                                                    *)
(*   M : Matroid  == M is a matroid whose elements are x : M                  *)
(*   msets M      == the set of set associated to the matroid                 *)
(*    rank s      == the rank of a set                                        *)
(* is_rset s1 s2  == s1 is a set that realizes the rank of s2                 *)
(* closure s      == the closure of a set                                     *)
(*   flats M      == the set of flats                                         *)
(* mcover s1 s2   == s1 is smallest flats that is a proper superset of s2     *)
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

Definition rank s := \max_(i in msets M | i \subset s) #|i|.

Notation " 'rk' s " := (rank s) (at level 40).

Definition is_rset s1 s2 :=
  [/\ #|s1| = rank s2, s1 \in msets M & s1 \subset s2].


Lemma leq_rank (s1 s2 : {set M}) :
  s1 \in msets M -> s1 \subset s2 -> #|s1| <= rank s2.
Proof.
by move=> s1IM s1Ss2; apply: leq_bigmax_cond; rewrite s1IM.
Qed.

Lemma rankE s : exists s1 : {set M}, is_rset s1 s.
Proof.
pose f (i : {set M}) := if i \subset s then #|i| else 0.
have /eq_bigmax_cond :  0 < #|msets M|.
  by apply/card_gt0P; exists set0; exact: msets0.
move=> /(_ f)[rs]; rewrite -big_mkcondr => rsIM rsE.
have [rsSs|NrsSs] := boolP (rs \subset s).
  have rS : rank s = #|rs| by rewrite /rank rsE /f rsSs.
  by exists rs; split.
exists set0; split; first by rewrite /rank rsE /f (negPf NrsSs) cards0.
  by apply: msets0.
by apply: sub0set.
Qed.

(* P1R *)
Lemma rank_card s : rank s <= #|s|.
Proof.
by apply/bigmax_leqP => s1 /andP[_ /subset_leq_card].
Qed.

Lemma rank_set0 : rank set0 = 0.
Proof.
by apply/eqP; rewrite -leqn0 -(@cards0 M) rank_card.
Qed.

Lemma rank_set1 a : rank [set a] <= 1.
Proof. by rewrite -(cards1 a) rank_card. Qed.

(* P2R *)
Lemma rank_subset s1 s2 : s1 \subset s2 -> rank s1 <= rank s2.
Proof.
move=> s1Ss2; apply/bigmax_leqP => e /andP[Hs1 Hs2].
by apply: leq_bigmax_cond; rewrite Hs1 (subset_trans Hs2).
Qed.

Lemma rank_compl s1 s2 : 
  s1 \in msets M ->  s1 \subset s2 -> 
  exists2 s3 : {set M}, s1 \subset s3 & is_rset s3 s2.
Proof.
elim: {s1}_.+1 {-2}s1 (ltnSn (#|s2 :\: s1|)) => //
    n IH s1 s1Ds2 s1IM s1Ss2.
have [s3 [Rs3 s3IM s3Ss2]] := rankE s2.
have := leq_rank s1IM s1Ss2.
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
Lemma rank_mod s1 s2 : rank (s1 :|: s2) + rank (s1 :&: s2) <= rank s1 + rank s2.
Proof.
have [s3 [rS3 s3IM s3Ss1Is2]] := rankE (s1 :&: s2).
have s3Ss1Us2 : s3 \subset s1 :|: s2.
  apply: subset_trans s3Ss1Is2 _.
  by apply/subsetP => i; rewrite in_setI in_setU => /andP[->].
have [s4 s3Ss4 [<- s4IM s4Ss1Us2]] := rank_compl s3IM s3Ss1Us2.
pose s5 := s4 :&: s1; pose s6 := s4 :&: s2.
have -> : s4 = s5 :|: s6 by rewrite -setIUr; apply/sym_equal/setIidPl.
have /eqP-> : rank (s1 :&: s2) == #|s5 :&: s6|.
  rewrite eqn_leq; apply/andP; split; last first.
    apply: leq_rank.
      by apply: msets_sub s4IM; rewrite -setIA subsetIl.
    by apply: setISS; apply: subsetIr.
  rewrite -rS3; apply: subset_leq_card.
  by rewrite -setIIr subsetI s3Ss4.
rewrite cardsUI.
apply: leq_add.
  apply: leq_rank => //; first by apply: msets_sub (subsetIl _ _) _.
  by apply: subsetIr.
apply: leq_rank => //; first by apply: msets_sub (subsetIl _ _) _.
by apply: subsetIr.
Qed.

Definition closure s := [set x | rank (x |: s) == rank s].

Notation " 'cl' s " := (closure s) (at level 40).

Lemma closure_setT : closure [set: M] = [set: M].
Proof.
by apply/setP=> x; rewrite !inE (_ : _ :|: _ = [set: M]) ?setUT ?eqxx.
Qed.

(* P1P *)
Lemma closure_sub s : s \subset closure s.
Proof.
apply/subsetP=> x; rewrite !inE => xIs.
rewrite (_ : _ |: _ = s) //.
by apply/setUidPr/subsetP=> y; rewrite inE => /eqP->.
Qed.

Lemma closure_rank s : rank (closure s) = rank s.
Proof.
have := rank_subset (closure_sub s).
rewrite leq_eqVlt => /orP[/eqP<-//|sLcls].
have [s1 [rs1E s1IM s1Ss]] := rankE s.
have [s2 [rs2E s2IM s2Ss]] := rankE (cl s).
case: (msets_card s1IM s2IM); first by rewrite rs1E rs2E.
move=> x; rewrite inE => /andP[xNIs1 xIs2] xs1IM.
have /(leq_rank xs1IM) : x |: s1 \subset x |: s by apply: setUS.
rewrite cardsU1 xNIs1.
have: x \in closure s by apply: (subsetP s2Ss).
by rewrite inE => /eqP->; rewrite add1n -rs1E ltnn.
Qed.

(* P2P *)
Lemma closure_invo s : closure (closure s) = closure s.
Proof.
apply/eqP; rewrite eqEsubset closure_sub andbT.
apply/subsetP=> x; rewrite !inE closure_rank => /eqP rkxsE.
rewrite eqn_leq -{1}rkxsE !rank_subset //; first by apply: subsetUr.
by apply/setUS/closure_sub.
Qed.

(* P3P *)
Lemma closure_subset s1 s2 : s1 \subset s2 -> closure s1 \subset closure s2.
Proof.
move=> s1Ss2; apply/subsetP=> x; rewrite !inE => /eqP rxs1E.
rewrite eqn_leq [_ <= rank (_ |: _)]rank_subset ?andbT; last by apply: subsetUr.
have->: x |: s2 = (x |: s1) :|: s2.
  rewrite -setUA; congr (_ |: _).
  by apply/sym_equal/setUidPr.
rewrite -(leq_add2r (rank ((x |: s1) :&: s2))) (addnC (rank s2)).
suff {2}->: rank ((x |: s1) :&: s2) = rank (x |: s1) by apply: rank_mod.
have [xIs2|xNIs2] := boolP (x \in s2).
  congr rank; apply/setIidPl.
  by rewrite subUset /= sub1set xIs2.
rewrite rxs1E setIUl (_ : _ :&: _ = set0) ?set0U.
  by congr rank; apply/setIidPl.
apply/setP=> y; rewrite !inE; case: eqP => [->|] //.
by rewrite (negPf xNIs2).
Qed.

Lemma closureU1 a s : a \in closure s -> closure (a |: s) = closure s.
Proof.
rewrite inE => /eqP aIs; apply/eqP; rewrite eqEsubset andbC closure_subset ?subsetUr //=.
apply/subsetP=> b; rewrite !inE => /eqP bIas.
rewrite eqn_leq andbC rank_subset ?subsetUr //=.
by rewrite -aIs -bIas rank_subset // setUCA subsetUr.
Qed.

Lemma rank_setU1 a s : a \notin closure s -> rank (a |: s) = (rank s).+1.
Proof.
rewrite inE => aIs; have := rank_mod [set a] s.
have-> :[set a] :&: s = set0.
  apply/setP=> y; rewrite !inE; case: eqP => // -> /=.
  apply/idP => Ha; case/eqP: aIs.
  by congr rank; apply/setUidPr; rewrite sub1set.
rewrite rank_set0 addn0.
case: rank (rank_set1 a) => [_ asLs|[_|]//].
  case/negP: aIs.
  by rewrite eqn_leq andbC rank_subset ?subsetUr.
rewrite leq_eqVlt => /orP[/eqP//|asLs].
case/negP: aIs.
by rewrite eqn_leq andbC rank_subset ?subsetUr.
Qed.

(* P4P *)
Lemma closure_ex a b s : 
  b \in (closure (a |: s) :\: closure s) -> 
  a \in (closure (b |: s) :\: closure s).
Proof.
rewrite inE => /andP[bNIs bIas].
have [/closureU1 asE|aNIs] := boolP (a \in closure s).
  by case/negP: bNIs; rewrite -asE.
rewrite inE aNIs /=.
move: bIas; rewrite !inE setUCA => /eqP->.
by rewrite !rank_setU1.
Qed.

Definition flats : {set {set M}} := [set s | closure s == s].

(* P1P *)
Lemma flats_setT : [set: M] \in flats.
Proof. by rewrite inE closure_setT eqxx. Qed.

(* P2P *)
Lemma flats_setI s1 s2 : s1 \in flats -> s2 \in flats -> s1 :&: s2 \in flats.
Proof.
rewrite !inE => s1F s2F.
rewrite eqEsubset closure_sub andbT subsetI.
by rewrite  -{2}(eqP s1F) -{3}(eqP s2F) !closure_subset ?subsetIr ?subsetIl.
Qed.

Lemma closure_flats s : closure s \in flats.
Proof. by rewrite inE closure_invo. Qed.

Lemma flats_closure s : s \in flats -> closure s = s.
Proof. by rewrite inE => /eqP. Qed.

Definition mcover (s1 s2 : {set M}) := 
  [&& s1 \in flats, s2 \in flats, s2 \proper s1 &
      [forall s, [&& s \in flats, s2 \subset s & s \subset s1]
                                  ==> ((s == s1) || (s == s2))]].

Lemma mcoverP s1 s2 :
  reflect 
    [/\ s1 \in flats, s2 \in flats, s2 \proper s1 &
        forall s, s \in flats -> s2 \subset s -> s \subset s1 ->
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
   exists2 a, a \notin s2 & s1 = closure (a |: s2).
Proof.
move=> /mcoverP[s1F s2F s2Ps1 HS].
have /properP[s2Ss1 [a aIs1 aNIs2]] := s2Ps1.
exists a => //.
case (HS (closure (a |: s2))) => //.
- by apply: closure_flats.
- apply: subset_trans (subsetUr _ _) (closure_sub _).
- rewrite -(flats_closure s1F).
  apply: closure_subset.
  by rewrite subUset sub1set aIs1.
move=> /setP/(_ a).
by rewrite (subsetP (closure_sub _)) ?(negPf aNIs2) // !inE eqxx.
Qed.

Lemma mcover_sub_ex s1 s2 : 
  s1 \in flats -> s2 \in flats -> s1 \proper s2 -> 
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
Lemma mcover_closure a s1 : 
  s1 \in flats -> a \notin s1 -> mcover (closure (a |: s1)) s1.
Proof.
move=> s1F aNIs1.
have [|s sCs1 s1Sas1] := mcover_sub_ex s1F (closure_flats (a |: s1)).
  rewrite properE (subset_trans _ (closure_sub _)) ?subsetUr //=.
  apply/negP=> /subsetP/(_ a).
  rewrite (negPf aNIs1) (subsetP (closure_sub _)).
    by move=> /(_ isT).
  by rewrite !inE eqxx.
have [b bNIs1 sE] := mcoverE sCs1.
suff/eqP->: cl(a |: s1) == cl(b |: s1) by rewrite -sE.
rewrite eqEsubset; apply/andP; split; last first.
  by rewrite -sE (subset_trans _ s1Sas1).
rewrite -(closure_invo (b |: _)) closure_subset //.
rewrite subUset sub1set -{2}(flats_closure s1F) closure_subset ?andbT ?subsetUr //.
suff : a \in (closure (b |: s1) :\: closure s1) by rewrite inE => /andP[].
apply: closure_ex.
rewrite inE flats_closure // bNIs1 (subsetP s1Sas1) // sE.
by rewrite (subsetP (closure_sub _)) // !inE eqxx.
Qed.

Lemma mcoverPU s1 s2 : 
   s2 \in flats ->
   reflect 
     (exists2 a, a \notin s2 & s1 = closure (a |: s2))
     (mcover s1 s2).
Proof.
move=> s2F.
apply: (iffP idP)=> [|[a aNIs2->]]; first by apply: mcoverE.
by apply: mcover_closure.
Qed.

Lemma mcoverI s s1 s2 : 
  mcover s1 s -> mcover s2 s -> s1 != s2 -> s1 :&: s2 = s.
Proof.
move=> /mcoverP[s1F sF sPs1 s1Min] /mcoverP[s2F _ sPs2 s2Min] s1Ds2.
have s1s2F : s1 :&: s2 \in flats by apply: flats_setI.
case: (s1Min _ s1s2F)=> // [||s1s2E1]; first by rewrite subsetI !proper_sub.
  by apply: subsetIl.
case: (s2Min _ s1s2F)=> // [||s1s2E2]; first by rewrite subsetI !proper_sub.
  by apply: subsetIr.
by case/eqP: s1Ds2; rewrite -s1s2E1.
Qed.
 
(* P3P *)
Lemma flats_partition s : 
  s \in flats -> partition [set (s1 :\: s) | s1 in {set M} & mcover s1 s] (~: s).
Proof.
move=> sF.
apply/and3P; split.
- apply/eqP/setP => x; rewrite inE.
  have [xIs/= |xNIs/=] := boolP (x \in s); apply/idP.
    move=> /bigcupP/= [s1] /imsetP/= [s2 _ ->].
    by rewrite inE xIs.
  apply/bigcupP; exists (closure (x |: s) :\:s).
    apply/imsetP; exists (closure (x |: s)) => //.
    by rewrite inE mcover_closure.
  by rewrite inE xNIs (subsetP (closure_sub _)) // !inE eqxx.
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
