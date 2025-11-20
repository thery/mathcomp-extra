From mathcomp Require Import all_boot order perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of the bitonic sorting algorithm                               *)
(*                                                                            *)
(* l \is bitonic == a sequence is bitonic if one of its rotation is increasing*)
(*                  then decreasing                                           *)
(*  half_cleaner == an (m + m) connector where wire i is linked to wire i + m *)
(* rhalf_cleaner == an (m + m) connector where wire i is linked to wire 2m-i  *)
(*                  the duplication of a half_cleaner_rec                     *)
(*    half_cleaner_rec m                                                      *)
(*               == the (`2^ m) network composed of a rhalf_cleaner and then  *)
(*                  the duplication via recursion                             *)
(*   rhalf_cleaner_rec m                                                      *)
(*               == the (`2^ m) network composed of a rhalf_cleaner and then  *)
(*                  the duplication of a half_cleaner_rec                     *)
(*       bsort m == the (`2^ m) network that implements the bitonic sort      *)
(*      bfsort m == the (`2^ m) network that implements the bitonic sort with *)
(*                  flip                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Bitonic.

Variable d : disp_t.
Variable A : orderType d.

Definition bitonic := [qualify s | 
 [exists r : 'I_(size (s : seq A)).+1, 
  exists n : 'I_(size (s : seq A)).+1,
  let s1 := rot r s in sorted (<=%O) (take n s1) && sorted (>=%O) (drop n s1)]].

Lemma bitonic_sorted (s : seq A) : sorted <=%O s -> s \is bitonic.
Proof.
move=> sS; apply/existsP; exists (inord 0); rewrite !inordK //= rot0.
apply/existsP; exists (inord (size s)); rewrite !inordK //.
by rewrite take_size sS /= drop_size.
Qed.

Lemma bitonic_r_sorted (s : seq A) : sorted >=%O s -> s \is bitonic.
Proof.
move=> sS; apply/existsP; exists (inord 0); rewrite !inordK //= rot0.
by apply/existsP; exists (inord 0); rewrite !inordK // take0 drop0.
Qed.

Lemma bitonic_cat (s1 s2 : seq A) :  
  sorted <=%O s1 -> sorted >=%O s2 -> (s1 ++ s2) \is bitonic.
Proof.
move=> s1S s2S.
apply/existsP; exists (inord 0); rewrite inordK ?rot0 //=.
apply/existsP; rewrite size_cat /=.
have sLs : size s1 < (size s1 + size s2).+1 by rewrite ltnS leq_addr.
exists (Ordinal sLs) => /=.
rewrite take_cat ltnn subnn take0 cats0 s1S /=.
by rewrite drop_cat ltnn subnn drop0.
Qed.

Lemma bitonic_catr (s1 s2 : seq A) :  
  sorted >=%O s1 -> sorted <=%O s2 -> (s1 ++ s2) \is bitonic.
Proof.
move=> s1S s2S.
apply/existsP; exists (inord (size s1)); rewrite inordK; last first.
  by rewrite ltnS size_cat leq_addr.
apply/existsP; rewrite size_cat /=.
have sLs : size s2 < (size s1 + size s2).+1 by rewrite ltnS leq_addl.
exists (Ordinal sLs) => /=.
rewrite rot_size_cat.
rewrite take_cat ltnn subnn take0 cats0 s2S /=.
by rewrite drop_cat ltnn subnn drop0.
Qed.

Lemma bitonic_rev (s : seq A) : (rev s \is  bitonic) = (s \is bitonic).
Proof.
suff {s}Hi (s : seq A) : s \is  bitonic -> rev s \is  bitonic.
  apply/idP/idP=> [H|]; last by apply: Hi.
  by rewrite -[s]revK; apply: Hi.
move=> /existsP[/= r /existsP[n /andP[tS dS]]].
apply/existsP; rewrite size_rev.
have xO : size s - r < (size s).+1 by rewrite ltnS leq_subr.
exists (Ordinal xO) => /=.
have yO : size s - n < (size s).+1 by rewrite ltnS leq_subr.
apply/existsP; exists (Ordinal yO) => /=.
rewrite -rev_rotr take_rev drop_rev !rev_sorted size_rotr /rotr.
by rewrite !subnA ?subnn -1?ltnS // dS.
Qed.

End Bitonic.

Arguments bitonic {d A}.


Section HalfCleaner.

Variable d : disp_t.
Variable A : orderType d.

Definition clink_half_cleaner m : {ffun 'I_(m + m) -> 'I_(m + m)} :=
  [ffun i =>
    match split i with 
    | inl x => rshift _ x
    | inr x => lshift _ x
    end].

Lemma clink_half_cleaner_proof m : 
  [forall i : 'I_(m + m), clink_half_cleaner _ (clink_half_cleaner _ i) == i].
Proof.
apply/forallP => i; rewrite !ffunE; case: (splitP i) => [j iE|k iE].
  by rewrite split_rshift; apply/eqP/val_eqP/eqP.
by rewrite split_lshift; apply/eqP/val_eqP/eqP.
Qed.
  
Definition half_cleaner b m :=
  connector_of (clink_half_cleaner_proof m) (cflip_default _ b).

Lemma cfun_half_cleaner b m (t : (m + m).-tuple A) : 
  cfun (half_cleaner b m) t = 
  [tuple
    match split i with 
    | inl x => (if b then max else min) (tnth t i) (tnth t (rshift m x))
    | inr x => (if b then min else max) (tnth t i) (tnth t (lshift m x))
    end | i < m + m].
Proof.
apply: eq_from_tnth => i /=.
rewrite /half_cleaner /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple !ffunE.
case: splitP => /= [j iE|k iE]; first by rewrite iE leq_addl; case: b.
rewrite ifN; first by case: b.
by rewrite -ltnNge (leq_trans (ltn_ord _) _) // iE leq_addr.
Qed.

Fixpoint half_cleaner_rec b m : network (`2^ m) :=
  if m is m1.+1 then half_cleaner b (`2^ m1) :: ndup (half_cleaner_rec b m1)
  else [::].

Lemma size_half_cleaner_rec b m : size (half_cleaner_rec b m) = m.
Proof.
elim: m => //= m IH.
by rewrite /ndup /= size_map size_zip IH minnn.
Qed.

End HalfCleaner.

Lemma bitonic_boolP (s : seq bool) :
  reflect (exists t,
            let: (b,i,j,k) := t in s = nseq i b ++ nseq j (~~ b) ++ nseq k b)
          (s \is bitonic).
Proof.
apply: (iffP existsP) => /= [[x /existsP[n /andP[isort dsort]]]|
                             [[[[b i] j] k] ->]]; last first.
  rewrite !size_cat !size_nseq.
  case: b => /=.
    have iL : i < (i + (j + k)).+1 by lia.
    have jL : j  < (i + (j + k)).+1 by lia.
    exists (Ordinal iL); apply/existsP; exists (Ordinal jL) => /=.
    rewrite -[X in rot X](size_nseq i true) rot_size_cat.
    rewrite -catA take_cat size_nseq ltnn subnn take0 cats0.
    rewrite isorted_bool_nseq /= drop_cat size_nseq ltnn subnn drop0.
    by rewrite -nseqD dsorted_bool_nseq.
  have iL : i < (i + (j + k)).+1 by lia.
  exists (Ordinal iL); apply/existsP; exists ord0 => /=.
  rewrite take0 drop0 /= -[X in rot X](size_nseq i false) rot_size_cat.
  by rewrite -catA -nseqD; apply/dsorted_boolP; exists (j, k + i).
have /isorted_boolP[[j1 k1] Hirot] := isort.
have /dsorted_boolP[[j2 k2] Hdrot] := dsort.
have -> : s = rotr x (nseq j1 false ++ nseq (k1 + j2) true ++ nseq k2 false).
  apply: (@rot_inj x); rewrite rotrK.
  by rewrite -[LHS](cat_take_drop n) Hirot Hdrot nseqD !catA.
rewrite /rotr !size_cat !size_nseq.
set i1 := j1 + (k1 + j2 +  k2) - x.
have [i1Lj1|j1Li1] := leqP i1 j1.
  rewrite -(subnK i1Lj1) addnC nseqD -catA.
  rewrite -{1}[i1](size_nseq i1 false) rot_size_cat.
  by exists (false, j1 - i1, k1 + j2, k2 + i1); rewrite !nseqD !catA.
have [i1j1Lk1j2|k1j2Li1j1] := leqP (i1 - j1) (k1 + j2).
  rewrite -(subnK i1j1Lk1j2) addnC !nseqD -!catA catA.
  have {1}-> : i1 = size (nseq j1 false ++ nseq (i1 - j1) true).
    by rewrite size_cat !size_nseq addnC subnK // ltnW.
  rewrite rot_size_cat.
  by exists (true, k1 + j2 - (i1 - j1), k2 + j1, i1 - j1); rewrite nseqD !catA.
have [i1j1k1j2Lk2|k2Li1j1k1j2] := leqP (i1 - j1 - (k1 + j2)) k2.
  rewrite -(subnK i1j1k1j2Lk2) [k2 - _ + _]addnC !nseqD -nseqD.
  have {1}-> : i1 = size (nseq j1 false ++ nseq (j2 + k1) true ++
                            nseq (i1 - j1 - (j2 + k1)) false).
    rewrite !size_cat !size_nseq [j2 + k1 + _]addnC subnK 1?ltnW //.
      by rewrite [j1 + _]addnC subnK // ltnW.
    by rewrite addnC.
  rewrite [k1 + _]addnC !catA -catA  rot_size_cat.
  exists (false, k2 - (i1 - j1 - (j2 + k1)) + j1, 
            j2 + k1, (i1 - j1 - (j2 + k1))).
  by rewrite !nseqD !catA.
rewrite rot_oversize.
by exists (false, j1, k1 + j2, k2); rewrite !catA.
rewrite !size_cat !size_nseq.
rewrite -leq_subRL; last by apply: ltnW.
by rewrite -leq_subRL ltnW.
Qed.

Lemma bitonic_half_cleaner fb m (t : (m + m).-tuple bool) :
  (t : seq _) \is bitonic -> 
  let t1 := cfun (half_cleaner fb m) t in 
    (ttake t1 == nseq m fb :> seq _) && 
    ((tdrop t1 : seq _) \is bitonic)
  ||
    (tdrop t1 == nseq m (~~fb) :> seq _) && 
    ((ttake t1 : seq _) \is bitonic).
Proof.
move=> /bitonic_boolP[[[[b i] j] k] tE] /=; set t1 := cfun _ _.
have mmE : m + m = i + j + k.
  by rewrite -(size_tuple t) tE !size_cat !size_nseq addnA.
have [iLm|mLi]:= leqP i m; last first.
  (*** 
         b b b b b b b
         b b~b~b b b b
    min  b b 0 0 b b b 
    max  b b 1 1 b b b
  ***)
  pose smin := nseq (i - m) b ++ nseq j false ++ nseq k b.
  pose smax := nseq (i - m) b ++ nseq j true ++ nseq k b.
  have mE : m = i - m + j + k.
    by rewrite -addnA addnBAC 1?ltnW // addnA -mmE addnK.
  have ttE : ttake t1 = (if fb then smax else smin) :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by case: (fb); rewrite size_tuple !size_cat !size_nseq addnA.
    rewrite size_tuple => uLm.
    rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
    have uLi : u < i by apply: ltn_trans mLi.
    have uLmm : u < m + m by apply: leq_trans uLm (leq_addl _ _).
    rewrite (nth_map (Ordinal uLmm)) -1?enum_ord ?size_enum_ord //.
    have {2}->: u = (Ordinal uLmm) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
       repeat (case: leqP => ?; try lia); case: (b).
  have tdE : tdrop t1 = (if fb then smin else smax) :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by rewrite fun_if size_tuple !size_cat !size_nseq addnA if_same.
    rewrite size_tuple => uLn.
    rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
    have uLi : u < i by apply: ltn_trans mLi.
    have muLmm : m + u < m + m by rewrite ltn_add2l.
    rewrite (nth_map (Ordinal muLmm)) -1?enum_ord ?size_enum_ord //.
    have {2}->: m + u = (Ordinal muLmm) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
      by have := ltn_ord u1; lia.
    have {}uE : u = u1 by rewrite -[u](addnK m) addnC uE addnC addnK.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
       repeat (case: leqP => ?; try lia); case: (b).
  rewrite {}/smin {}/smax in ttE tdE.
  case: (fb) tE ttE tdE; case: (b); rewrite -!nseqD => /= tE ttE tdE.
  - apply/orP; left.
    rewrite ttE addnBAC 1?ltnW // addnA -mmE addnK eqxx /=.
    by apply/bitonic_boolP; exists (true, i - m, j, k).
  - apply/orP; right.
    rewrite tdE addnBAC 1?ltnW // addnA -mmE addnK eqxx /=.
    by apply/bitonic_boolP; exists (false, i - m, j, k).
  - apply/orP; right.
    rewrite tdE addnBAC 1?ltnW // addnA -mmE addnK eqxx /=.
    by apply/bitonic_boolP; exists (true, i - m, j, k).
  apply/orP; left.
  rewrite ttE addnBAC 1?ltnW // addnA -mmE addnK eqxx /=.
  by apply/bitonic_boolP; exists (false, i - m, j, k).
have [ijLm|mLij]:= leqP (i + j) m.
  (***  0 -> (i + j - m) -> (i - (i + j - m)) - j -> m - i
         b b b~b~b~b b
         b b b b b b b
    min  b b b 0 0 0 b 
    max  b b b 1 1 1 b
  ***)
  have mE : m = i + j + k - m by rewrite -mmE addnK.
  pose smin := nseq i b ++ nseq j false ++ nseq (m - (i + j)) b.
  pose smax := nseq i b ++ nseq j true ++ nseq (m - (i + j)) b.
  have ttE : ttake t1 = (if fb then smax else smin) :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by case: (fb); rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLm.
    rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
    have uLmm : u < m + m by apply: leq_trans uLm (leq_addl _ _).
    rewrite (nth_map (Ordinal uLmm)) -1?enum_ord ?size_enum_ord //.
    have {2}->: u = (Ordinal uLmm) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
       repeat (case: leqP => ?; try lia); case: (b).
  have tdE : tdrop t1 = (if fb then smin else smax) :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by case: (fb); rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLn.
    rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
    have uLmm : u < m + m by apply: leq_trans uLn (leq_addl _ _).
    have muLmm : m + u < m + m by rewrite ltn_add2l.
    rewrite (nth_map (Ordinal muLmm)) -1?enum_ord ?size_enum_ord //.
    have {2}->: m + u = (Ordinal muLmm) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
      by move: (ltn_ord u1); lia.
    have {}uE : u = u1 by rewrite -[u](addnK m) addnC uE addnC addnK.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
       repeat (case: leqP => ?; try lia); case: (b).
  rewrite {}/smin {}/smax in ttE tdE.
  case: (fb) tE ttE tdE; case: (b); rewrite -!nseqD => /= tE ttE tdE.
  - apply/orP; left.
    rewrite ttE addnA addnC subnK // eqxx /=.
    by apply/bitonic_boolP; exists (true, i, j, m - (i + j)).
  - apply/orP; right.
    rewrite tdE addnA addnC subnK // eqxx /=.
    by apply/bitonic_boolP; exists (false, i, j, m - (i + j)).
  - apply/orP; right.
    rewrite tdE addnA addnC subnK // eqxx /=.
    by apply/bitonic_boolP; exists (true, i, j, m - (i + j)).
  apply/orP; left.
  rewrite ttE addnA addnC subnK // eqxx /=.
  by apply/bitonic_boolP; exists (false, i, j, m - (i + j)).
have mE : m = i + j + k - m by rewrite -mmE addnK.
have [jLm|mLj]:= leqP j m.
  (*** 
         b b b b b~b~b
        ~b~b b b b b b
    min  0 0 b b b 0 0 
    max  1 1 b b b 1 1
  ***)
  pose smin := nseq (i + j - m) false ++ nseq (m - j) b ++ nseq (m - i) false.
  pose smax := nseq (i + j - m) true ++ nseq (m - j) b ++ nseq (m - i) true.
  have ttE : ttake t1 = (if fb then smax else smin) :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by case: (fb); rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLm.
    rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
    have uLmm : u < m + m by lia.
    rewrite (nth_map (Ordinal uLmm)) -1?enum_ord ?size_enum_ord //.
    have {2}->: u = (Ordinal uLmm) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
       repeat (case: leqP => ?; try lia); case: (b).
  have tdE : tdrop t1 = (if fb then smin else smax) :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by case: (fb); rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLm.
    rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
    have uLmm : u < m + m by apply: leq_trans uLm (leq_addl _ _).
    have muLmm : m + u < m + m by rewrite ltn_add2l.
    rewrite (nth_map (Ordinal muLmm)) -1?enum_ord ?size_enum_ord //.
    have {2}->: m + u = (Ordinal muLmm) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
      by move: (ltn_ord u1); lia.
    have {}uE : u = u1 by rewrite -[u](addnK m) addnC uE addnC addnK.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
       repeat (case: leqP => ?; try lia); case: (b).
  rewrite {}/smin {}/smax in ttE tdE.
  case: (fb) tE ttE tdE; case: (b); rewrite -!nseqD => /= tE ttE tdE.
  - apply/orP; left.
    rewrite ttE; apply/andP; split; first by apply/eqP; congr nseq; lia.
    by apply/bitonic_boolP; exists (false, i + j - m, m - j, m - i).
  - apply/orP; right.
    rewrite tdE; apply/andP; split; first by apply/eqP; congr nseq; lia.
    by apply/bitonic_boolP; exists (true, i + j - m, m - j, m - i).
  - apply/orP; right.
    rewrite tdE; apply/andP; split; first by apply/eqP; congr nseq; lia.
    by apply/bitonic_boolP; exists (false, i + j - m, m - j, m - i).
  apply/orP; left.
  rewrite ttE; apply/andP; split; first by apply/eqP; congr nseq; lia.
  by apply/bitonic_boolP; exists (true, i + j - m, m - j, m - i).
(*** 
       b b~b~b~b~b~b
      ~b~b~b~b~b b b
  min  0 0~b~b~b 0 0 
  max  1 1~b~b~b 1 1
***)
pose smin := nseq i false ++ nseq (j - m) (~~b) ++ nseq k false.
pose smax := nseq i true ++ nseq (j - m) (~~ b) ++ nseq k true.
have ttE : ttake t1 = (if fb then smax else smin) :> seq bool.
  apply: (@eq_from_nth _ false) => [|u].
    by case: (fb); rewrite size_tuple !size_cat !size_nseq; lia.
  rewrite size_tuple => uLm.
  rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
  have uLmm : u < m + m by lia.
  rewrite (nth_map (Ordinal uLmm)) -1?enum_ord ?size_enum_ord //.
  have {2}->: u = (Ordinal uLmm) :> nat by [].
  rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
  rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
  by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
     repeat (case: leqP => ?; try lia); case: (b).
have tdE : tdrop t1 = (if fb then smin else smax) :> seq bool.
  apply: (@eq_from_nth _ false) => [|u].
    by case: (fb); rewrite size_tuple !size_cat !size_nseq; lia.
  rewrite size_tuple => uLm.
  rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
  have uLmm : u < m + m by apply: leq_trans uLm (leq_addl _ _).
  have muLmm : m + u < m + m by rewrite ltn_add2l.
  rewrite (nth_map (Ordinal muLmm)) -1?enum_ord ?size_enum_ord //.
  have {2}->: m + u = (Ordinal muLmm) :> nat by [].
  rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
    by move: (ltn_ord u1); lia.
  have {}uE : u = u1 by rewrite -[u](addnK m) addnC uE addnC addnK.
  rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
  by case: (fb); rewrite !nth_cat !size_nseq !nth_nseq;
     repeat (case: leqP => ?; try lia); case: (b).
rewrite {}/smin {}/smax in ttE tdE.
case: (fb) tE ttE tdE; case: (b); rewrite -!nseqD => /= tE ttE tdE.
- apply/orP; right.
 rewrite tdE; apply/andP; split; first by apply/eqP; congr nseq; lia.
 by apply/bitonic_boolP; exists (true, i, j - m, k).
- apply/orP; left.
  rewrite ttE; apply/andP; split; first by apply/eqP; congr nseq; lia.
  by apply/bitonic_boolP; exists (false, i, j - m, k).
- apply/orP; left.
  rewrite ttE; apply/andP; split; first by apply/eqP; congr nseq; lia.
  by apply/bitonic_boolP; exists (true, i, j - m, k).
apply/orP; right.
rewrite tdE; apply/andP; split; first by apply/eqP; congr nseq; lia.
by apply/bitonic_boolP; exists (false, i, j - m, k).
Qed.

Lemma sorted_half_cleaner_rec b m (t : (`2^ m).-tuple bool) :
  (t : seq _) \is bitonic -> 
  sorted (if b then (>=%O : rel _) else <=%O) (nfun (half_cleaner_rec b m) t).
Proof.
elim: m t b => /= [|m IH t b tB]; first by (do 2 case => //=) => x [].
rewrite nfun_dup.
have /orP[/andP[Ht Hd]|/andP[Ht Hd]] := bitonic_half_cleaner b tB.
  have -> : ttake (cfun (half_cleaner b (`2^ m)) t) =
            [tuple of nseq (`2^ m) b].
    by apply/val_eqP.
  rewrite nfun_const.
  case: b Ht Hd => Ht Hd; last by rewrite sorted_bool_constl ; apply: IH.
  rewrite -rev_sorted rev_cat /= rev_nseq sorted_bool_constr rev_sorted /=.
  by apply: IH.
have -> : tdrop (cfun (half_cleaner b (`2^ m)) t) = 
          [tuple of nseq (`2^ m) (~~b)].
  by apply/val_eqP.
rewrite nfun_const.
case: b Ht Hd => Ht Hd; last by rewrite sorted_bool_constr; apply: IH.
rewrite -rev_sorted rev_cat /= rev_nseq sorted_bool_constl rev_sorted /=.
by apply: IH.
Qed.

Section RHalfCleaner.

Variable d : disp_t.
Variable A : orderType d.

Definition clink_rhalf_cleaner m : {ffun 'I_m -> 'I_m} := [ffun i => rev_ord i].

Lemma clink_rhalf_cleaner_proof m : 
  [forall i : 'I_(m + m), clink_rhalf_cleaner _ (clink_rhalf_cleaner _ i) == i].
Proof. by apply/forallP => i; rewrite !ffunE rev_ordK. Qed.
  
Definition rhalf_cleaner m :=
  connector_of (clink_rhalf_cleaner_proof m) (cflip_default _ false).

Lemma cfun_rhalf_cleaner m (t : (m + m).-tuple A) : 
  cfun (rhalf_cleaner m) t = 
  [tuple
    match split i with 
    | inl x => min (tnth t i) (tnth t (rshift m (rev_ord x)))  
    | inr x => max (tnth t (lshift m (rev_ord x))) (tnth t i)
    end | i < m + m].
Proof.
apply: eq_from_tnth => i /=.
rewrite /rhalf_cleaner /cfun /= !tnth_map /= tnth_ord_tuple !ffunE.
case: splitP => [j iE|k iE]; rewrite /= iE.
  rewrite leq_subRL ?(leq_trans (ltn_ord _)) ?leq_addr //.
  rewrite leq_add // 1?ltnW //.
  by congr (min _ (tnth _ _)); apply/val_eqP; rewrite /= iE addnBA.
rewrite -addnS subnDl leqNgt ltn_subLR // addSn ltnS addnC -addnA leq_addr /=.
rewrite maxC; congr (max (tnth _ _) _).
by apply/val_eqP; rewrite /= iE -addnS subnDl.
Qed.

Lemma cfun_rhalf_cleaner_rev_take m (t : (m + m).-tuple A) : 
  ttake (cfun (rhalf_cleaner m) t) =
  ttake (cfun (half_cleaner false m) [tuple of ttake t ++ rev (tdrop t)]).
Proof.
rewrite cfun_rhalf_cleaner cfun_half_cleaner.
apply: eq_from_tnth => i /=.
have st : size (ttake t) = m.
  rewrite ttakeE size_take size_tuple.
  by case: (m) => // n1; rewrite addSn ltnS addnS ltnS leq_addr.
have sd : size (tdrop t) = m.
  by rewrite tdropE size_drop size_tuple addnK.
pose k : 'I_(m + m) := lshift _ i; pose a := tnth t k.
rewrite !(tnth_nth a) !ttakeE !nth_take //=.
rewrite !(nth_map k) //; last first.
- by rewrite fintype.size_enum_ord (leq_trans (ltn_ord _) (leq_addr _ _)).
- by rewrite fintype.size_enum_ord (leq_trans (ltn_ord _) (leq_addr _ _)).
- by rewrite -fintype.enumT fintype.size_enum_ord (leq_trans (ltn_ord _)
             (leq_addr _ _)).
have -> : i = k :> nat by [].
rewrite -fintype.enumT fintype.nth_ord_enum.
case: splitP => [j kE|j kE]; last first.
  by have := ltn_ord i; rewrite [i : nat]kE ltnNge leq_addr.
congr min.
  by rewrite !(tnth_nth a) nth_cat /= st ltn_ord ttakeE nth_take.
rewrite !(tnth_nth a) nth_cat /= st ifN; last by rewrite -leqNgt leq_addr.
rewrite nth_rev; last by rewrite sd addnC addnK.
rewrite sd tdropE nth_drop //.
by congr nth; lia.
Qed.

Lemma cfun_rhalf_cleaner_rev_drop m (t : (m + m).-tuple A) : 
  tdrop (cfun (rhalf_cleaner m) t) =
  trev
  (tdrop (cfun (half_cleaner false m) [tuple of ttake t ++ rev (tdrop t)])).
Proof.
rewrite cfun_rhalf_cleaner cfun_half_cleaner.
apply: eq_from_tnth => i /=.
have st : size (ttake t) = m.
  rewrite ttakeE size_take size_tuple.
  by case: (m) => // n1; rewrite addSn ltnS addnS ltnS leq_addr.
have sd : size (tdrop t) = m.
  by rewrite tdropE size_drop size_tuple addnK.
pose k : 'I_(m + m) := rshift _ i; pose a := tnth t k.
rewrite !(tnth_nth a) nth_rev; last first.
  by rewrite tdropE size_drop size_tuple addnK.
rewrite !tdropE !nth_drop !(nth_map k) //; last first.
- by rewrite size_tuple ltn_add2l.
- by rewrite -fintype.enumT fintype.size_enum_ord ltn_add2l.
- by rewrite size_drop !size_tuple; have := ltn_ord i; lia.
- rewrite size_drop !size_tuple -fintype.enumT fintype.size_enum_ord.
  by have := ltn_ord i; lia.
have -> : m + i = k :> nat by [].
rewrite -fintype.enumT fintype.nth_ord_enum.
case: splitP => [j kE|j kE].
  by have := ltn_ord j; rewrite -kE /= ltnNge leq_addr.
rewrite size_drop size_tuple addnK.
have -> : m + (m - i.+1) = rshift m (rev_ord i) by [].
rewrite fintype.nth_ord_enum.
case: splitP => /= [l lE | l lE]; first by have := ltn_ord l; lia.
rewrite maxC.
congr max.
  rewrite !(tnth_nth a) nth_cat /= st lE ltnNge leq_addr /=. 
  rewrite nth_rev; last by rewrite sd; have := ltn_ord i; lia.
  rewrite tdropE nth_drop // size_drop size_tuple addnK.
  congr nth.
  have : m + i = m + j by rewrite -kE.
  by have := ltn_ord i; lia.
rewrite !(tnth_nth a) nth_cat /= st ltn_ord.
rewrite ttakeE nth_take //; congr nth.
have : m + i = m + j by rewrite -kE.
by have := ltn_ord i; lia.
Qed.

Lemma cfun_rhalf_cleaner_rev n (t : (n + n).-tuple A) : 
  let t1 :=  cfun (half_cleaner false n) [tuple of ttake t ++ rev (tdrop t)] in
  cfun (rhalf_cleaner n) t =
  [tuple of ttake t1 ++ rev (tdrop t1)].
Proof.
rewrite /= [LHS]cat_ttake_tdrop; congr [tuple of _ ++ _].
  by apply: cfun_rhalf_cleaner_rev_take.
by apply: cfun_rhalf_cleaner_rev_drop.
Qed.

Definition rhalf_cleaner_rec n : network (`2^ n) :=
  if n is n1.+1 then
    rhalf_cleaner (`2^ n1) :: ndup (half_cleaner_rec false n1)
  else [::].

Lemma size_rhalf_cleaner_rec n : size (rhalf_cleaner_rec n) = n.
Proof.
case: n => //= n.
by rewrite /ndup /= size_map size_zip size_half_cleaner_rec minnn.
Qed.

End RHalfCleaner.

Lemma sorted_rhalf_cleaner_rec m (t : (`2^ m.+1).-tuple bool) :
  sorted <=%O (ttake t : seq _) -> sorted <=%O (tdrop t : seq _) ->
  sorted <=%O (nfun (rhalf_cleaner_rec m.+1) t).
Proof.        
rewrite /rhalf_cleaner_rec /= => Hst Hsd.
rewrite nfun_dup.
rewrite cfun_rhalf_cleaner_rev_drop -/e2n cfun_rhalf_cleaner_rev_take -/e2n.
set u : (`2^ m.+1).-tuple _ := [tuple of _ ++ rev _].
have uB : (u : seq _) \is bitonic.
  apply: bitonic_cat => //.
  by rewrite rev_sorted.
have := bitonic_half_cleaner false uB;
      rewrite -/e2n => /orP[/andP[Ht Hd]|/andP[Ht Hd]].
  have -> : ttake (cfun (half_cleaner false (`2^ m)) u) = 
            [tuple of nseq (`2^ m) false].
    by apply/val_eqP.
  rewrite nfun_const sorted_bool_constl.
  apply: sorted_half_cleaner_rec.
  by rewrite bitonic_rev.
have -> : trev (tdrop (cfun (half_cleaner false (`2^ m)) u)) = 
            [tuple of nseq (`2^ m) true].
  by apply/val_eqP; rewrite /= (eqP Ht) rev_nseq.
rewrite nfun_const sorted_bool_constr.
by apply: sorted_half_cleaner_rec.
Qed.

Section BitonicSort.

Variable d : disp_t.
Variable A : orderType d.

Fixpoint bsort m : network (`2^ m) :=
  if m is m1.+1 then ndup (bsort m1) ++ rhalf_cleaner_rec m1.+1 
  else [::].

Lemma size_bsort m : size (bsort m) = (m * m.+1)./2.
Proof.
elim: m => [|m IH] //.
rewrite /ndup [LHS]/= size_cat [LHS]/= size_map size_zip.
rewrite minnn size_map size_zip size_half_cleaner_rec minnn IH.
by rewrite -addn2 mulnDr -!divn2 divnDMl // mulnC.
Qed.

Lemma sorting_bsort m : bsort m \is sorting.
Proof.
elim: m => [|m IH]; first by apply: sorting1.
apply/forallP => t.
rewrite /bsort -/bsort nfun_cat.
apply: sorted_rhalf_cleaner_rec; first by rewrite nfun_dup ttakeK (forallP IH).
by rewrite nfun_dup tdropK (forallP IH).
Qed.

End BitonicSort.

Section BitonicSort.

Variable d : disp_t.
Variable A : orderType d.

Fixpoint bfsort (b : bool) m : network (`2^ m) :=
  if m is m1.+1 then nmerge (bfsort b m1) (bfsort (~~b) m1) ++
                     half_cleaner_rec b m1.+1 
  else [::].

Lemma size_bfsort b m : size (bfsort b m) = (m * m.+1)./2.
Proof.
elim: m b => [b|m IH b] //.
rewrite [LHS]/= size_cat [LHS]/= size_map size_zip.
rewrite !IH minnn size_map size_zip size_half_cleaner_rec minnn.
by rewrite -addn2 mulnDr -!divn2 divnDMl // mulnC.
Qed.

Lemma sorting_bfsort m : bfsort false m \is sorting.
Proof.
rewrite /sorting.
rewrite -[<=%O]/(if false then (>=%O : rel _) else <=%O).
elim: m false => [b|m IH b]; first by apply/forallP => /= [] [[|x[]]].
apply/forallP => t.
rewrite /bfsort -/bfsort nfun_cat.
apply: sorted_half_cleaner_rec.
rewrite nfun_merge ?size_bfsort //.
case: b; last first.
  apply: bitonic_cat; first by have /forallP := IH false; apply.
  by have /forallP := IH true; apply.
apply: bitonic_catr; first by have /forallP := IH true; apply.
by have /forallP := IH false; apply.
Qed.

End BitonicSort.

