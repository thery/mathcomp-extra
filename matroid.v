From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* Matroid                                                                    *)
(*   Matroid  == the type of Matroid (x : M) x is an element of the matroid   *)
(*   msets M  == the set of set associated to the matroid                     *)
(*    rank s  == the rank of a set                                            *)
(* is_rset s1 s2  ==  s1 is a set that realizes the rank of s2                *)
(* closure s  == the closure of a set                                         *)
(*   flats M  == the set of flats                                             *)
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

(* P3P *)
Lemma flats_partition s : 
  s \in flats -> partition [set (s1 :\: s) | s1 in flats & (s :&: s1 != set0)] (~: s).
Proof.
Admitted.

End Matroid.
