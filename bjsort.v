From mathcomp Require Import all_ssreflect perm algebra.zmodp.
From mathcomp Require Import zify.
Require Import more_tuple nsort.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of the Knuth exchange sorting algorithm                        *)
(*                                                                            *)
(*      knuth_merge == the connector that links i to i.+1 for i odd           *)
(*  knuth_merge_rec == the recursive connect that calls itself on             *)
(*                       the even and odd parts and then apply Batcher_merge  *)
(*   knuth_exchange == the recursive connect that calls itself on             *)
(*                       the even and odd parts and then apply Batcher_merge  *)
(*   iknuth_exchange_exchange == an iterative version of knuth that works     *)
(*                               directly on list                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Knuth.

Variable d : disp_t.
Variable A : orderType d.

Definition clink_eswap m : {ffun 'I_m -> 'I_m} :=
  [ffun i : 'I_ _ => if odd i then ipred i else inext i].

Lemma clink_eswap_proof m : 
  [forall i : 'I_m, clink_eswap _ (clink_eswap _ i) == i].
Proof.
apply/forallP => i /=; apply/eqP/val_eqP; rewrite !ffunE.
have m_gt0 : 0 < m by apply: leq_ltn_trans (ltn_ord i).
have [/= iO|iE] := boolP (odd i); rewrite ?(val_inext, val_ipred) /=.
  case: (ltngtP i 0) => // [o_gt0 | iE]; last by rewrite iE in iO.
  rewrite -[odd _]negbK -oddS prednK // iO val_inext val_ipred.
  rewrite -[i.-1 == _]eqSS !prednK //.
  by rewrite [(i : nat) == m]eqn_leq [m <= _]leqNgt ltn_ord andbF.
have [iE1 | /eqP iD] := (i : nat) =P m.-1.
  by rewrite (negPf iE) !val_inext /= iE1 !eqxx.
by rewrite oddS (negPf iE) /= /= val_ipred /= val_inext /= (negPf iD).
Qed.
  
Definition ceswap {m} :=
  connector_of (clink_eswap_proof m) (cflip_default _ false).

Lemma cfun_eswap n (t : n.-tuple A) : 
  cfun ceswap t = 
  [tuple
    if odd i then max (tnth t i) (tnth t (ipred i))
    else min (tnth t i) (tnth t (inext i)) | i < n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /ceswap /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple !ffunE.
have [iO|iE] := boolP (odd i); last by rewrite ifT // val_inext; case: eqP.
case: leqP => [iLip|] //.
suff -> : ipred i = i by rewrite maxxx minxx.
apply/val_eqP =>> /=; move: iLip; rewrite !val_ipred /=.
by case: (i : nat) => //= i1; rewrite ltnn.
Qed.

Fixpoint knuth_jump_rec m k r : network m :=
  if k is k1.+1 then codd_jump r :: knuth_jump_rec _ k1 (uphalf r).-1
  else [::].

Lemma size_knuth_jump_rec m k : size (knuth_jump_rec m k ((`2^ k).-1)) = k.
Proof.
elim: k => //= k IH.
by rewrite -e2Sn uphalfE prednK ?e2n_gt0 // e2Sn addnn doubleK IH.
Qed.

Fixpoint knuth_exchange m : network (`2^ m) :=
  if m is m1.+1 then
    neodup (knuth_exchange m1) ++ ceswap :: knuth_jump_rec _ m1 ((`2^ m1).-1)
  else [::].

Lemma size_knuth_exchange m : size (knuth_exchange m) = (m * m.+1)./2.
Proof.
elim: m => // m IH.
rewrite [LHS]/= size_cat /neodup /neomerge size_map size_zip minnn IH.
rewrite [LHS]/= size_knuth_jump_rec -addn2 mulnDr halfD.
by rewrite oddM  muln2 odd_double andbF add0n doubleK mulnC.
Qed.

End Knuth.

Lemma sorted_eswap m (t : (m + m).-tuple bool) :
  sorted <=%O (tetake t) -> sorted <=%O (totake t) -> 
  let t1 := cfun ceswap t in
  [/\ sorted <=%O (tetake t1), 
      sorted <=%O (totake t1) & 
      noF (totake t1) <= noF (tetake t1)].
Proof.
rewrite !isorted_noFT => /eqP teE /eqP toE t1.
set a := noF (tetake t) in teE; set b := noT (tetake t) in teE.
set c := noF (totake t) in toE; set d := noT (totake t) in toE.
have mEmaxmin : m = maxn a c + minn b d.
  case: (leqP a c) => [aLc | cLa].
    rewrite (minn_idPr _); first by rewrite size_noFT size_tuple.
    rewrite -(leq_add2l a) size_noFT size_tuple -(size_tuple (totake t)).
    by rewrite -size_noFT -/c -/d leq_add2r.
  rewrite (minn_idPl _); first by rewrite size_noFT size_tuple.
  rewrite -(leq_add2l a) size_noFT size_tuple -(size_tuple (totake t)).
  by rewrite -size_noFT -/c -/d leq_add2r ltnW.
have mEminmax : m = minn a c + maxn b d.
  case: (leqP a c) => [aLc | cLa].
    rewrite (maxn_idPl _); first by rewrite size_noFT size_tuple.
    rewrite -(leq_add2l a) size_noFT size_tuple -(size_tuple (totake t)).
    by rewrite -size_noFT -/c -/d leq_add2r.
  rewrite (maxn_idPr _); first by rewrite size_noFT size_tuple.
  rewrite -(leq_add2l a) size_noFT size_tuple -(size_tuple (totake t)).
  by rewrite -size_noFT -/c -/d leq_add2r ltnW.
suff t1E :  t1 = eocat (nseq (maxn a c) false ++ nseq (minn b d) true) 
                      (nseq (minn a c) false ++ nseq (maxn b d) true) :> seq _.
  rewrite tetakeE totakeE t1E otakeK ?etakeK.
    by rewrite !isorted_noFT !noE !eqxx; case: (ltngtP a c) => // /ltnW->.
  by rewrite !(size_cat, size_nseq) -mEmaxmin.
apply: (@eq_from_nth _ true) => [|i].
  rewrite /= [LHS]size_tuple card_ord size_eocat size_cat !size_nseq.
  by rewrite -mEmaxmin.
rewrite [X in _ < X -> _]size_tuple => iLab.
pose x := Ordinal iLab.
rewrite /t1 cfun_eswap /= (nth_map x) /= -[i]/(x : nat); last first.
  by rewrite -enum_ord size_enum_ord.
rewrite -enum_ord !nth_ord_enum.
rewrite nth_eocat; last first.
  by rewrite !size_cat !size_nseq // -mEminmax.
rewrite !(tnth_nth true) [t]eocat_tetake_totake /=.
rewrite !nth_eocat /=; try by rewrite !size_tuple.
have i2Lm : i./2 < m by rewrite ltn_half_double -addnn.
have [iO|iE] := boolP (odd _).
  have i_gt0 : 0 < i by case: (i) iO.
  have i1E : ~~ odd i.-1 by rewrite -oddS prednK.
  rewrite val_ipred /= (negPf i1E).
  have -> : i.-1./2 = i./2.
    by rewrite -[X in _ = X./2]prednK // -uphalfE uphalf_half (negPf i1E).
  by rewrite teE toE !nth_cat_seqT -/a  -/c geq_min; do 2 case: leqP => ?.
rewrite val_inext; case: eqP =>/= [i1E| _].
  have := iE; rewrite i1E -oddS prednK ?(leq_ltn_trans _ iLab) //.
  by rewrite [X in odd X]addnn odd_double.
rewrite (negPf iE) /= uphalf_half (negPf iE) /= add0n.
by rewrite teE toE !nth_cat_seqT -/a  -/c geq_max; do 2 case: leqP => ?.
Qed.

Lemma sorted_knuth_jump_rec m (t : (m + m).-tuple bool) k :
  sorted <=%O (tetake t) -> sorted <=%O (totake t) ->
  noF (totake t) <= noF (tetake t) <= noF (totake t) + `2^ k ->
  sorted <=%O (nfun (knuth_jump_rec (m + m) k (`2^ k).-1) t).
Proof.
move=> teS toS /andP[noL noI].
set t1 := nfun _ _.
pose i := noF (tetake t) - noF (totake t).
suff [te1S to1S noFE] : [/\ sorted <=%O (tetake t1), 
                          sorted <=%O (totake t1) & 
                          noF (tetake t1) = noF (totake t1) + odd i].
  apply: sorted_tetake_totake => //.
  by rewrite noFE; case: odd; rewrite !(addn1, addn0) leqnn leqnSn.
have : i <= `2^ k by rewrite leq_subLR.
elim: k t teS toS @i @t1 {noI} noL => [|k IH] t teS toS i;
      rewrite [nfun _ _]/= => t1 nt2Lnt1 iL2k.
  rewrite teS toS /i.
  move: iL2k; rewrite leq_subLR addn1.
  case: ltngtP nt2Lnt1 => // [|->]; last by rewrite subnn addn0.
  case: (ltngtP (noF (totake _)).+1) => // <-.
  by rewrite subSn // subnn addn1.
move: @t1; set cf := cfun _ _ => t1.
have k2O : odd (`2^ k.+1).-1.
  by rewrite -[odd _]negbK -oddS prednK ?e2n_gt0 // e2Sn addnn odd_double.
have uhE : (uphalf (`2^ k.+1).-1).*2 = `2^ k.+1.
  by rewrite uphalfE prednK ?e2n_gt0 // e2Sn addnn doubleK -addnn.
have iLuh : i <= (uphalf (`2^ k.+1).-1).*2 by rewrite uhE.
have [] := sorted_odd_jump k2O iLuh teS toS.
  by rewrite addnC subnK.
rewrite doubleB uhE -/cf => te1S to1S nteE.
move: @t1; rewrite -e2Sn.
have -> : (uphalf (`2^ k.+1).-1).-1 = (`2^ k).-1.
  by rewrite uphalfE prednK ?e2n_gt0 // e2Sn addnn doubleK.
have -> : odd i = odd (noF (tetake cf) - noF (totake cf)).
  rewrite nteE addnC addnK oddB.
    by rewrite e2Sn addnn -doubleB odd_double addbC.
  by rewrite leq_subLR -addnn leq_add2r.
apply: IH => //; first by rewrite nteE leq_addr.
rewrite nteE addnC addnK leq_subLR.
have [iLk|kLi] := leqP i (`2^ k); first by apply: leq_trans (leq_addl _ _).
rewrite e2Sn -addnn subnDA subnK.
  by rewrite -addnBA ?leq_addr // ltnW.
 rewrite leq_subRL //.
  by rewrite !addnn leq_double // ltnW.
by apply: (leq_trans (ltnW _) (leq_addr _ _)).
Qed.

Lemma sorted_nfun_knuth_exchange m (t : (`2^ m).-tuple bool) :
  sorted <=%O (nfun (knuth_exchange m) t).
Proof.
elim: m t => [t|m IH t] /=; first by apply: tsorted01.
rewrite nfun_cat /= nfun_eodup.
set v := teocat _ _; have [||ste sto nto] := (@sorted_eswap _ v).
- by rewrite tetakeK IH.
- by rewrite totakeK IH.
apply: sorted_knuth_jump_rec => //.
rewrite nto andTb.
rewrite -[X in _ <= _ + X](size_tuple (tetake (cfun ceswap v))).
by rewrite -size_noFT addnCA leq_addr.
Qed.

Lemma sorting_knuth_exchange m : knuth_exchange m \is sorting.
Proof. apply/forallP => x; apply: sorted_nfun_knuth_exchange. Qed.

(** Iterative version *)

Fixpoint eotake (A : Type) d n (s : seq A) := 
 if d is d1.+1 then 
   if odd n then eotake d1 n./2 (otake s)
            else eotake d1 n./2 (etake s)
 else s.

Lemma eotake_mod (A : Type) d n (s : seq A) :
  eotake d (n %% `2^ d) s = eotake d n s.
Proof.
elim: d n s => //= d IH n s; rewrite odd_mod ?(odd_e2 d.+1) //.
case: (boolP (odd n)) => [nO|nE]; last first.
  rewrite -[in LHS](odd_double_half n) (negPf nE) add0n addnn.
  by rewrite -!muln2 -muln_modl muln2 doubleK IH.
rewrite -[in LHS](odd_double_half n) nO add1n modnS.
rewrite addnn -!muln2 -muln_modl !muln2 ifN.
  by rewrite -uphalfE uphalf_half odd_double doubleK IH.
apply/negP=> /dvdnP => [] [k H].
by move: (nO); rewrite -[n]odd_double_half nO addSn H -doubleMr odd_double.
Qed.

Lemma nth_eotake (A : Type) d n (s : seq A) a x :
  nth a (eotake d n s) x = nth a s ((n %% `2^ d) + `2^ d * x).
Proof.
elim: d n s a x => /= [n s a x|d IH n s a x]; first by rewrite modn1 mul1n.
case: (boolP (odd n)) => [nO|nE]; rewrite addnn; last first.
  rewrite IH nth_etake doubleD doubleMl.
  by rewrite -muln2 muln_modl !muln2 -[in RHS](odd_double_half n) (negPf nE).
rewrite IH nth_otake doubleD -addSn doubleMl.
rewrite -muln2 muln_modl !muln2.
rewrite -[in RHS](odd_double_half n) nO add1n modnS ifN //.
apply/negP=> /dvdnP => [] [k H].
by move: (nO); rewrite -[n]odd_double_half nO addSn H -doubleMr odd_double. 
Qed.

Lemma nth_eotake_div (A : Type) d (s : seq A) a n :
  nth a (eotake d n s) (n %/ `2^ d) = nth a s n.
Proof. by rewrite nth_eotake mulnC addnC -divn_eq. Qed.

Lemma eq_size_eotake (A:  Type) d n (s1 s2 : seq A) :
  size s1 = size s2 -> size (eotake d n s1) = size (eotake d n s2).
Proof.
elim: d n s1 s2 => //= d IH n s1 s2 ss1Ess2.
case: odd; apply: IH; first by apply: eq_size_otake.
by apply: eq_size_etake.
Qed.

Lemma gtn_size_eotake (A : Type) k p i (s : seq A) :
   i < `2^ p -> k < size (eotake p i s) -> i + `2^ p * k < size s.
Proof.
elim: p i k s => [[]// k s _|p IH i k s iLk kLs]; first by rewrite mul1n.
rewrite /= in kLs.
case: (boolP (odd _)) kLs => iO /IH; 
  rewrite ?(size_otake, size_etake) ltn_half_double -addnn -e2Sn =>
      /(_ iLk) ikLs.
  rewrite -(odd_double_half i) iO -addSn -doubleS.
  rewrite e2Sn addnn -doubleMl -doubleD.
  rewrite -(odd_double_half (size s)).
  apply: leq_trans (leq_addl _ _).
  by rewrite leq_double addSn.
move: ikLs.
rewrite uphalf_half -[X in i + _ < X](odd_double_half (size s)).
rewrite -[i as X in (X + _ < _)]odd_double_half (negPf iO) add0n.
rewrite e2Sn addnn -doubleMl -doubleD.
case: odd => /=; first by rewrite !ltnS leq_double.
by rewrite ltn_double.
Qed.

Lemma eotakeS (A : Type) (d n : nat) (s : seq A) :
  eotake d.+1 n s =
    if odd n
      then eotake d n./2 (otake s)
      else eotake d n./2 (etake s).
Proof. by []. Qed.

Lemma eotcat_take (A : Type) d n (s : seq A) : n < `2^ d -> 
  eotcat (eotake d.+1 n s) (eotake d.+1 (`2^ d + n) s) = 
  eotake d n s.
Proof.
move=> nL2d.
have IH0 d1 s1 : eotcat (eotake d1.+1 0 s1) (eotake d1.+1 (`2^ d1) s1) = 
                 eotake d1 0 s1.
  elim: d1 s1 => [/= s1|d1 IH s1]; first by rewrite eotcatK.
  rewrite !(eotakeS d1.+1).
  by rewrite [RHS]/= -[RHS]IH /= addnn odd_double doubleK.
have [m leMn] := ubnP n.
elim: m n d s leMn nL2d => [[]//|m IH n [|d] s nLm nLd].
  by case: (n) nLd => //= _; apply: eotcatK.
rewrite !(eotakeS d.+1) [X in odd(X + _)]addnn oddD odd_double addFb [RHS]/=.
have -> : (`2^ d.+1 + n)./2  = `2^d + n./2.
  by rewrite /= addnn halfD doubleK odd_double.
rewrite -(odd_double_half n) in nLm nLd.
case: (boolP (odd n)) nLm nLd; rewrite ?(addSn, add0n, ltnS) => nO nLm nLd.
  apply: IH => //.
    by rewrite (leq_ltn_trans _ nLm) // -addnn leq_addr.
  by rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd).
case: (ltngtP 0 n) => // [n_gt0|<-]; last by rewrite addn0 IH0.
apply: IH => //.
  case: (n) nO n_gt0 nLm => // [] [|n1] //= _ _ n1Lm.
  by rewrite (leq_trans _ n1Lm) // -addnn addnS addSn !ltnS leq_addr.
by rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd).
Qed.

Lemma etake_eotake (A : Type) d n (s : seq A) : n < `2^ d -> 
  etake (eotake d n s) =  eotake d.+1 n s.
Proof.
have IH0 d1 l1 : etake (eotake d1 0 l1) = eotake d1.+1 0 l1.
  elim: d1 l1 => [//|d1 IH l1].
  by rewrite !(eotakeS d1.+1) -[RHS]IH.
move=> nL2d.
have [m leMn] := ubnP n.
elim: m n d s leMn nL2d => [[]//|m IH n [|d] s nLm nLd].
  by case: (n) nLd => //= _; apply: eotcatK.
case: (ltngtP 0 n) => // [n_gt0|<-]; last by rewrite IH0.
have n2Ld : n./2 < `2^ d.
  rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd) //.
  by rewrite -[X in _ <= X](odd_double_half n) leq_addl.
have n2Lm : n./2 < m.
  case: (n) n_gt0 nLm => // [] [|m1] //= _.
  rewrite -(odd_double_half m1.+2) /= doubleS  addnS ltnS.
  move => /(leq_ltn_trans _)->//.
  by rewrite addnS ltnS -addnn addnA leq_addl.
by rewrite !(eotakeS d.+1) [LHS]/=; case: odd; apply: IH.
Qed.

Lemma otake_eotake (A : Type) d n (s : seq A) : n < `2^ d -> 
  otake (eotake d n s) =  eotake d.+1 (`2^ d + n) s.
Proof.
have IH0 d1 s1 : otake (eotake d1 0 s1) = eotake d1.+1 (`2^ d1) s1.
  elim: d1 s1 => [//=|d1 IH s1].
  rewrite !(eotakeS d1.+1) [X in odd X]/= addnn odd_double.
  by rewrite [X in X./2]addnn doubleK -[RHS]IH.
move=> nL2d.
have [m leMn] := ubnP n.
elim: m n d s leMn nL2d => [[]//|m IH n [|d] s nLm nLd].
  by case: (n) nLd => //= _; apply: eotcatK.
case: (ltngtP 0 n) => // [n_gt0|<-]; last by rewrite addn0 IH0.
have n2Ld : n./2 < `2^ d.
  rewrite -ltn_double -[X in _ < X]addnn (leq_ltn_trans _ nLd) //.
  by rewrite -[X in _ <= X](odd_double_half n) leq_addl.
have n2Lm : n./2 < m.
  case: (n) n_gt0 nLm => // [] [|m1] //= _.
  rewrite -(odd_double_half m1.+2) /= doubleS  addnS ltnS.
  move => /(leq_ltn_trans _)->//.
  by rewrite addnS ltnS -addnn addnA leq_addl.
have HE : (`2^ d.+1 + n)./2 = `2^ d + n./2.
  by rewrite halfD odd_e2 /= addnn doubleK. 
rewrite !(eotakeS d.+1) oddD odd_e2 HE.
rewrite -IH // [LHS]/=.
by case: odd => //=; rewrite IH.
Qed.

Lemma leq_size_eotake_e2n (A : Type) i p q (s : seq A) :
  i <= q -> size s <= `2^ q -> size (eotake i p s) <= `2^ (q - i).
Proof.
elim: i p q s => [|i IH] p q s iLq Hs /=; first by rewrite subn0.
have q_gt0 : 0 < q by apply: leq_ltn_trans iLq.
case: odd.
  apply: leq_trans (IH _ q.-1 _ _ _) _.
  - by rewrite -ltnS prednK // (leq_ltn_trans _ iLq).
  - rewrite size_otake -leq_double -!addnn -e2Sn addnn.
    rewrite prednK // (leq_trans _ Hs) //.
    by rewrite -[X in _ <= X]odd_double_half; case: odd.
  by case: (q) q_gt0.
apply: leq_trans (IH _ q.-1 _ _ _) _.
- by rewrite -ltnS prednK // (leq_ltn_trans _ iLq).
- by rewrite size_etake leq_uphalf_e2n // prednK.
by case: (q) q_gt0.
Qed.

Lemma eotcat_nseq (A : Type) (a : A) n m : 
  m <= n <= m.+1 -> eotcat (nseq n a) (nseq m a) = nseq (n + m) a.
Proof.
elim: n m => [[]//|n IH [|m]]; first by case: (n).
rewrite addnS /= !ltnS => H.
by rewrite IH.
Qed.

Lemma sorted_eotake (p : nat) (s : seq bool) i :
  i < `2^ p -> 
  [/\ sorted <=%O (eotake p.+1 i s),
      sorted <=%O (eotake p.+1 (`2^ p + i) s) & 
  noF (eotake p.+1 (`2^p + i) s) <= noF (eotake p.+1 i s) <=
  noF (eotake p.+1 (`2^p + i) s) + 1] ->
  sorted <=%O (eotake p i s).
Proof.
move=> iL2p [/isorted_boolP[[a1 b1] E1 /isorted_boolP[[a2 b2] E2]]].
rewrite E1 E2 !noE addn1 => a2La1.
rewrite -eotcat_take // E1 E2.
have := size_etake (eotake p i s).
have := size_otake (eotake p i s).
rewrite etake_eotake // otake_eotake // E1 E2 uphalf_half => <-.
rewrite !size_cat !size_nseq.
elim: a1 {E1 E2}a2 a2La1 => [[|a2]//= _ Hs|a1 IH [|a2]].
- rewrite eotcat_nseq //.
    by apply/isorted_boolP; exists (0, b1 + b2).
  rewrite add0n in Hs.
  by rewrite Hs; case: odd; rewrite ?add1n !leqnn ?andbT //=.
- case: (a1) => // _; case: (b1); case: (b2) => // b3 b4 Hs.
  rewrite /= in Hs.
  rewrite ![_ ++ _]/= eotcat_cons (@eotcat_nseq _ true b4.+1).
    rewrite isorted_consF.
    by apply/isorted_boolP; exists (0, (b4.+1 + b3).+1).
  rewrite add1n add0n addnS in Hs.
  by case: Hs=> ->; case: odd; rewrite ?add1n !leqnn ?andbT /=.
rewrite ![_ ++ _]/= !ltnS => HS1 HS2.
rewrite !addSn addnS in HS2.
rewrite [_ ++ nseq b2 _]/= eotcat_cons !isorted_consF.
apply: IH => //.
by case: HS2.
Qed.

Section IKnuthExchance.

Variables (d : disp_t) (A : orderType d).

Definition swap i j (s : seq A) :=
  if s is a :: _ then
    let s1 := take i s in  
    let s2 := drop i s in
    let s3 := behead s2 in
    let s4 := take (j - i).-1 s3 in
    let s5 := drop (j - i).-1 s3 in
    let v1 := head a s2 in
    let v2 := head a s5 in
    s1 ++ min v1 v2 :: s4 ++ max v1 v2 :: behead s5
  else [::].

Fixpoint iter1_aux k n p i (s : seq A) :=
  if k is k1.+1 then
  if i + p < n then
     iter1_aux k1 n p i.+1 
       (if odd (i %/ p) then s else swap i (i + p) s)
  else s
  else s.

Definition iter1 p (s : seq A) := iter1_aux (size s).+1 (size s) p 0 s.

Fixpoint iter2_aux k n p q i (s : seq A) :=
  if k is k1.+1 then
  if i + q < n then
     iter2_aux k1 n p q i.+1 
       (if odd (i %/ p) then s else swap (i + p) (i + q) s)
  else s
  else s.

Definition iter2 p q (s : seq A) :=  iter2_aux (size s).+1 (size s) p q 0 s.

Fixpoint iter3_aux k p q (s : seq A) :=
  if k is k1.+1 then
    if q > p then iter3_aux k1 p q./2 (iter2 p q s) else s
  else s.

Definition iter3 top p (s : seq A) := iter3_aux (size s).+1 p top s.

Fixpoint iknuth_exchange_aux k top p (s : seq A) :=
  if k is k1.+1 then
  if p > 0 then
     let l1 := iter3 top p (iter1 p s) in
     iknuth_exchange_aux k1 top p./2 l1
  else s
  else s.

Definition iknuth_exchange (s : seq A) : seq A :=
  let top := `2^ ((up_log 2 (size s)).-1) in
  iknuth_exchange_aux (size s) top top s.

End IKnuthExchance.

Compute iknuth_exchange [::8; 7; 6; 5; 4; 3; 2; 1].
Compute iknuth_exchange [::true; true; true; true; false; false; false; false].

Section IKnuthExchangeProof.

Variables (d : disp_t) (A : orderType d).

(******************************************************************************)
(* Proof for swap                                                             *)
(******************************************************************************)

Lemma perm_swap (s : seq A) i j : i < j < size s -> perm_eq (swap i j s) s.
Proof.
case: s => //= a s /andP[iLj jLs].
rewrite -[X in perm_eq _ X](cat_take_drop i).
rewrite perm_cat2l.
have := size_drop i (a :: s).
rewrite /= -[_ - _]prednK; last first.
  by rewrite subn_gt0 (ltn_trans iLj).
case: drop => //= a1 l1.
rewrite prednK; last by rewrite subn_gt0 (ltn_trans iLj).
move=> sl1E.
rewrite -[X in perm_eq _ (_ :: X)](cat_take_drop (j - i).-1).
move: (sl1E) => sl1E1.
have jBiL : j - i < (size s).+1 - i.
  rewrite -(ltn_add2r i) !subnK //; last by apply: ltnW.
  by apply: (leq_trans (ltnW iLj) (ltnW _)).
rewrite -[l1](cat_take_drop (j - i).-1) size_cat size_take ifT in sl1E;
      last by rewrite -ltnS sl1E1 prednK ?subn_gt0.
case: drop sl1E => [|b l2 _] /=.
  rewrite addn0 prednK ?subn_gt0 // => jBiE.
  by rewrite jBiE ltnn in jBiL.
case: (ltP a1 b) => _ //.
rewrite -!seq.cat_cons -!cat_rcons perm_cat2r /=.
set l4 := take _ _.
have <- := perm_rcons b (rcons l4 a1).
rewrite perm_sym.
have <- := perm_rcons a1 (rcons l4 b).
rewrite -[X in perm_eq X]cats0 !cat_rcons.
rewrite -[X in perm_eq _ X]cats0 !cat_rcons.
rewrite perm_cat2l.
by have <- := perm_rcons b [::a1].
Qed.

Lemma size_swap (s : seq A) i j : i < j < size s -> size (swap i j s) = size s.
Proof. by move=> jB; apply/perm_size/perm_swap. Qed.

Lemma nth_swap a i j (s : seq A) k : 
   i < j < size s -> nth a (swap i j s) k = 
    (if k == i then min (nth a s i) (nth a s j)
     else if k == j then max (nth a s i) (nth a s j)
     else nth a s k).
Proof.
case: s => [/andP[]|/= b s /andP[iLj jLs]]; first by case: j.
rewrite nth_cat size_take /= (ltn_trans iLj jLs).
case: (ltngtP k i) => [kLi|iLk|->]; first 2 last.
- rewrite subnn /=; congr min.
    rewrite -nth0 nth_drop addn0.
    by apply: set_nth_default; rewrite /= (ltn_trans iLj).
  rewrite -nth0 nth_drop addn0 nth_behead nth_drop prednK ?subn_gt0 //.
  by rewrite addnC subnK 1?ltnW //; apply: set_nth_default.
- by rewrite ?nth_take // ifN // neq_ltn (ltn_trans kLi).
rewrite -[k - i]prednK ?subn_gt0 //=.
rewrite nth_cat size_take size_behead size_drop /=.
rewrite !prednK ?subn_gt0 // subSn /=; last first.
  by rewrite -ltnS (leq_trans iLj (ltnW _)).
rewrite leq_sub2r // -ltnS prednK ?subn_gt0 //.
rewrite -(ltn_add2r i) !subnK //; try by rewrite ltnW.
case: (ltngtP k j) => [kLj|jLk|->]; first 2 last.
- rewrite subnn /= -!nth0 !(nth_drop, nth_behead) !addn0.
  rewrite prednK ?subn_gt0 // addnC subnK; last by rewrite ltnW.
  congr max; apply: set_nth_default => //.
  by rewrite (leq_trans iLj (ltnW _)).
- rewrite nth_take; last first.
    rewrite -ltnS !prednK ?subn_gt0 //.
    by rewrite -(ltn_add2r i) !subnK // ltnW.
- by rewrite nth_behead nth_drop prednK ?subn_gt0 // addnC subnK // ltnW.
rewrite -[_.-1 - _.-1]subSS !prednK ?subn_gt0 //.
rewrite subnBA 1?ltnW // subnK 1?ltnW // -[k - j]prednK ?subn_gt0 //=.
rewrite !(nth_behead, nth_drop) prednK ?subn_gt0 // -addSn prednK ?subn_gt0 //.
by rewrite addnCA addnA subnK 1?ltnW // addnC subnK 1?ltnW.
Qed.

(******************************************************************************)
(* Proof for iter1                                                             *)
(******************************************************************************)

Lemma nth_iter1_aux k n p i s s1 (a : A) :
  0 < p -> n = size s -> n = size s1 -> n <= k + i ->  
  (forall j,
  nth a s1 j = 
    if odd (j %/ p) then 
      if (j < i + p) then max (nth a s (j - p)) (nth a s j)
      else nth a s j
    else 
      if (j + p < n) && (j < i) then min (nth a s j) (nth a s (j + p))
      else nth a s j) -> 
  (forall j, j < n ->
  nth a (iter1_aux k n p i s1) j = 
    if odd (j %/ p) then max (nth a s (j - p)) (nth a s j)
    else 
      if j + p < n then min (nth a s j) (nth a s (j + p))
      else nth a s j).
Proof.
move=> p_gt0 nEl nEl1.
elim: k i s1 nEl1 => [i s1 nEl1 nLi /= Hc j jLn|
                      /= k IH i s1 nEl1 nLi Hc j jLn /=].
  have := Hc j.
  rewrite (leq_trans jLn nLi) andbT.
  suff -> : j < i + p by [].
  by rewrite (leq_trans (leq_trans jLn nLi) (leq_addr _ _)).
case: (ltnP (i + p)) => [ipLn|nLip]; last first.
  have := Hc j.
  have [jpO|jpE] := boolP (odd _).
    by rewrite ifT // (leq_trans jLn).
  case: (ltnP (j + p)) => [jpLn|nLjp]//=.
  by rewrite -(ltn_add2r p) (leq_trans jpLn).
have ipB : i < i + p < n.
  by rewrite -ltn_subLR // subnn p_gt0.
rewrite IH //.
- by case: odd; rewrite // size_swap // -nEl1.
- by rewrite -addSnnS.
move=> j1.
case: (boolP (odd _)) => [ipO|ipE].
  case: (boolP (odd _)) => [jpO|jpE].
    have j1Dip : j1 != i + p.
      rewrite -[odd _]negbK in jpO.
      apply: contra jpO => /eqP->.
      by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= negbK.
    by rewrite Hc jpO addSn ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
  rewrite Hc (negPf jpE) /=.
  rewrite ltnS [j1 <= _]leq_eqVlt; case: eqP =>> //= j1Ei.
  by case/negP: jpE; rewrite j1Ei.
rewrite nth_swap -?nEl1 //.
case: eqP => [->|/eqP j1Di].
  rewrite (negPf ipE) ltnS ipLn leqnn //=.
  rewrite !Hc (negPf ipE) ipLn !ltnn /=.
  by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n.
case: eqP => [->|/eqP j1Dip].
  rewrite leqnn.
  rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n addnK.
  rewrite !Hc (negPf ipE) ipLn !ltnn /=.
  by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n.
case: (boolP (odd _)) => [j1pO|j1pE].
  by rewrite Hc j1pO addSn ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
by rewrite Hc (negPf j1pE) ltnS [j1 <= _]leq_eqVlt (negPf j1Di).
Qed.

Lemma perm_iter1_aux k n p i (s : seq A) :
  0 < p -> n = size s -> perm_eq (iter1_aux k n p i s) s.
Proof.
move=> p_gt0.
elim: k i s => //= k1 IH i s nE.
case: ltnP => // ipLn.
have ipB : i < i + p < n by rewrite -ltn_subLR // subnn p_gt0.
apply: perm_trans (IH _ _ _) _.
  by case: odd => //=; rewrite size_swap // -nE.
by case: odd => //; apply: perm_swap; rewrite -nE.
Qed.

Lemma size_iter1_aux k n p i (s : seq A) :
  0 < p -> n = size s -> size (iter1_aux k n p i s) = size s.
Proof. by move=> p_gt0 nE; apply/perm_size/perm_iter1_aux. Qed.

Lemma iter1_auxS k n p i (s : seq A) :
  iter1_aux k.+1 n p i s =
  if i + p < n then
     iter1_aux k n p i.+1 (if odd (i %/ p) then s else swap i (i + p) s)
  else s.
Proof. by []. Qed.

Lemma perm_iter1 p (s : seq A) : 0 < p -> perm_eq (iter1 p s) s.
Proof. by move=> p_gt0; apply: perm_iter1_aux. Qed.

Lemma size_iter1 p (s : seq A) : 0 < p -> size (iter1 p s) = size s.
Proof. by move=> p_gt0; apply/perm_size/perm_iter1. Qed.

Lemma nth_iter1 p s (a : A) j :
  0 < p -> 
  nth a (iter1 p s) j = 
    if odd (j %/ p) then 
      if j < size s then max (nth a s (j - p)) (nth a s j)
      else nth a s j
    else 
      if j + p < size s then min (nth a s j) (nth a s (j + p))
      else nth a s j.
Proof.
move=> p_gt0.
case: (ltnP j (size s)) => jLs; last first.
  rewrite !nth_default ?minxx ?if_same ?size_iter1 //.
  by rewrite (leq_trans _ (leq_addr _ _)).
apply: nth_iter1_aux; rewrite ?(addn0, add0n) // => j1.
rewrite ltn0 andbF.
case: (boolP (odd _)) => [j1pO|]//.
rewrite ifN // -leqNgt.
by rewrite -divn_gt0; case: (_ %/ _) j1pO.
Qed.
  
(******************************************************************************)
(* Proof for iter2                                                            *)
(******************************************************************************)

Lemma iter2_auxS k n p q i (s : seq A) :
iter2_aux k.+1 n p q i (s : seq A) =
  if i + q < n then
     iter2_aux k n p q i.+1 
       (if odd (i %/ p) then s else swap (i + p) (i + q) s)
  else s.
Proof. by []. Qed.

Lemma nth_iter2_aux k n p q i s s1 (a : A) :
  0 < p -> 0 < q -> p %| q -> ~~ odd (q %/ p) ->
  n = size s -> n = size s1 -> n <= k + i ->  
  (forall j,
  nth a s1 j = 
    if odd (j %/ p) then 
      if (j < i + p) && (j + q < n + p) 
      then min (nth a s j) (nth a s (j + q - p))
      else nth a s j
    else 
      if (q <= j < i + q) then max (nth a s (j - q + p)) (nth a s j)
      else nth a s j) -> 
  (forall j, j < n ->
  nth a (iter2_aux k n p q i s1) j = 
    if odd (j %/ p) then 
      if (j + q < n + p) then 
        min (nth a s j) (nth a s (j + q - p))
      else nth a s j
    else 
      if (q <= j) then max (nth a s (j - q + p)) (nth a s j)
      else nth a s j).
Proof.
move=> p_gt0 q_gt0 pDq pDqE nEl nEl1.
have pLq : p < q.
  have : p <= q by rewrite dvdn_leq.
  by case: ltngtP => // pE; case/negP: pDqE; rewrite pE divnn q_gt0.
elim: k i s1 nEl1 => [i s1 nEl1 nLi /= Hc j jLn|
                      /= k IH i s1 nEl1 nLi Hc j jLn /=].
  have := Hc j.
  rewrite (leq_trans (leq_trans jLn _) (leq_addr q i)) // andbT.
  by rewrite (leq_trans (leq_trans jLn _) (leq_addr p i)) // andbT.
case: (ltnP (i + q)) => [iqLn|nLiq]; last first.
  have := Hc j.
  have [jpO|jpE]/= := boolP (odd _).
    case: (ltnP (j + q)); rewrite !(andbT, andbF) // => jqLnp.
      case: (ltnP j); rewrite // leqNgt.
    by rewrite -(ltn_add2r q) (leq_trans jqLnp) // addnAC leq_add2r.
  by rewrite (leq_trans jLn _) // andbT.
have iqB : i + p < i + q < n by rewrite ltn_add2l pLq iqLn.
rewrite IH //.
- by case: odd; rewrite // size_swap // -nEl1.
- by rewrite -addSnnS.
move=> j1.
case: (boolP (odd _)) => [ipO|ipE]/=.
  have iqO : odd ((i + q) %/ p).
    case/dvdnP: pDq pDqE => r ->.
    by rewrite mulnK // divnDMl // oddD => /negPf->; rewrite addbF.
  case: (boolP (odd _)) => [j1pO|j1pE]/=.
    have j1Dip : j1 != i + p.
      rewrite -[odd _]negbK in j1pO.
      apply: contra j1pO => /eqP->.
      by rewrite -[X in _ + X]mul1n divnDMl // addn1 /= negbK.
    by rewrite Hc j1pO addSn /= ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
  rewrite Hc (negPf j1pE) /=.
  rewrite ltnS [j1 <= _]leq_eqVlt; case: eqP =>> //= j1Ei.
  by case/negP: j1pE; rewrite j1Ei.
rewrite nth_swap -?nEl1 //.
have ipO : odd ((i + p) %/ p).
  by rewrite -[X in _ + X]mul1n divnDMl // addn1 /=.
have iqE : ~~ odd ((i + q) %/ p).
  case/dvdnP: pDq pDqE => r ->.
  by rewrite mulnK // divnDMl // oddD => /negPf->; rewrite addbF.
case: eqP => [->|/eqP j1Di].
  rewrite -[X in _ + X]mul1n divnDMl // addn1 /= ipE mul1n.
  rewrite leqnn.
  rewrite addnAC ltn_add2r iqLn /=.
  by rewrite !Hc (negPf iqE) ipO !ltnn !andbF /= addnK.
case: eqP => [->|/eqP j1Dip].
  rewrite (negPf iqE) leq_addl leqnn /= addnK.
  by rewrite !Hc (negPf iqE) ipO !ltnn !leq_addl.
case: (boolP (odd _)) => [j1pO|j1pE].
  by rewrite Hc j1pO addSn ltnS [j1 <= _]leq_eqVlt (negPf j1Di).
by rewrite Hc (negPf j1pE) ltnS [j1 <= _]leq_eqVlt (negPf j1Dip).
Qed.

Lemma perm_iter2_aux k n p q i (s : seq A) :
  0 < p -> p < q -> n = size s -> perm_eq (iter2_aux k n p q i s) s.
Proof.
move=> p_gt0 pLq.
elim: k i s => //= k1 IH i s nE.
case: ltnP => // ipLn.
have ipB : i + p < i + q < n by rewrite ltn_add2l pLq.
apply: perm_trans (IH _ _ _) _.
  by case: odd => //=; rewrite size_swap // -nE.
by case: odd => //; apply: perm_swap; rewrite -nE.
Qed.

Lemma size_iter2_aux k n p q i (s : seq A) :
  0 < p -> p < q -> n = size s -> size (iter2_aux k n p q i s) = size s.
Proof. by move=> p_gt0 qLp nE; apply/perm_size/perm_iter2_aux. Qed.

Lemma perm_iter2 p q (s : seq A) : 0 < p -> p < q -> perm_eq (iter2 p q s) s.
Proof. by move=> p_gt0 pLq; apply: perm_iter2_aux. Qed.

Lemma size_iter2 p q (s : seq A) :
  0 < p -> p < q -> size (iter2 p q s) = size s.
Proof. by move=> p_gt0 pLq; apply/perm_size/perm_iter2. Qed.

Lemma nth_iter2 p q s (a : A) j :
  0 < p -> 0 < q -> p %| q -> ~~ odd (q %/ p) -> 
  nth a (iter2 p q s) j = 
    if odd (j %/ p) then 
      if (j + q < size s + p) then 
        min (nth a s j) (nth a s (j + q - p))
      else nth a s j
    else 
      if (q <= j < size s) then max (nth a s (j - q + p)) (nth a s j)
      else nth a s j.
Proof.
move=> p_gt0 q_gt0 pDq qpE.
have pLq : p < q.
  have : p <= q by rewrite dvdn_leq.
  by case: ltngtP => // pE; case/negP: qpE; rewrite pE divnn q_gt0.
case: (ltnP j (size s)) => jLs; last first.
  rewrite andbF !nth_default ?(maxxx, minxx) ?if_same ?size_iter2 //.
  by rewrite -addnBA ?(leq_trans jLs (leq_addr _ _)) // ltnW.
rewrite andbT.
apply: nth_iter2_aux; rewrite ?(addn0, add0n) // => j1.
case: (boolP (odd _)) => [j1pO|j1pE]//.
  have pLj1 : p <= j1 by rewrite -divn_gt0 //; case: (_ %/ _) j1pO. 
  by rewrite ifN // negb_and; case: leqP pLj1.
by rewrite ifN // negb_and; case: leqP.
Qed.

(******************************************************************************)
(* Proof for iter3                                                            *)
(******************************************************************************)

Lemma iter3_auxS k p q (s : seq A) :
  iter3_aux k.+1 p q (s : seq A) =
  if q > p then iter3_aux k p q./2 (iter2 p q s) else s.
Proof. by []. Qed.

Lemma perm_iter3_aux k p q (s : seq A) : 0 < p -> perm_eq (iter3_aux k p q s) s.
Proof.
move=> p_gt0.
elim: k q s => //= k IH q s.
case: leqP => // H.
apply: perm_trans.
apply: IH.
by apply: perm_iter2.
Qed.

Lemma size_iter3_aux k p q (s : seq A) :
  0 < p -> size (iter3_aux k p q s) = size s.
Proof. by move=> p_gt; apply/perm_size/perm_iter3_aux. Qed.

Lemma perm_iter3 p q (s : seq A) : 0 < q -> perm_eq (iter3 p q s) s.
Proof. by apply: perm_iter3_aux. Qed.

Lemma size_iter3  p q (s : seq A) : 0 < q -> size (iter3 p q s) = size s.
Proof. by move=> q_gt; apply/perm_size/perm_iter3. Qed.

(******************************************************************************)
(* Proof for iknuth_exchange                                                             *)
(******************************************************************************)

Lemma perm_iknuth_exchange_aux k p q (s : seq A) :
  perm_eq (iknuth_exchange_aux k p q s) s.
Proof.
elim: k p q s => //= k IH p q s.
case: leqP => // q_gt0.
apply: perm_trans; first by apply: IH.
apply: perm_trans; first by apply: perm_iter3.
by apply: perm_iter1.
Qed.  

Lemma size_iknuth_exchange_aux k p q (s : seq A) :
  size (iknuth_exchange_aux k p q s) = size s.
Proof. by apply/perm_size/perm_iknuth_exchange_aux. Qed.

Lemma perm_iknuth_exchange (s : seq A) : perm_eq (iknuth_exchange s) s.
Proof. by apply: perm_iknuth_exchange_aux. Qed.

Lemma size_iknuth_exchange (s : seq A) : size (iknuth_exchange s) = size s.
Proof. by apply/perm_size/perm_iknuth_exchange_aux. Qed.

End IKnuthExchangeProof.


Lemma sorted_iter1 (p : nat) (s : seq bool) i :
  i < `2^ p -> 
  let s1 := iter1 (`2^ p) s in 
  sorted <=%O (eotake p.+1 i s) ->
  sorted <=%O (eotake p.+1 (`2^ p + i) s) 
  -> 
  [/\ 
  sorted <=%O (eotake p.+1 i s1),
  sorted <=%O (eotake p.+1 (`2^p + i) s1) &
  noF (eotake p.+1 (`2^p + i) s1) <= noF (eotake p.+1 i s1)].
Proof.
move=> iL2p s1.
set s2 := eotake _ _ _; set s3 := eotake _ _ _.
pose d : nat := (size s2 != size s3).
move=> /isorted_boolP[[a1 b1] s2E] /isorted_boolP[[a2 b2] s3E].
pose sl := eotake p i s.
have ss2E : size s2 = uphalf (size sl) by rewrite -size_etake etake_eotake.
have ss3E : size s3 = (size sl)./2 by rewrite -size_otake otake_eotake.
have dE : d = odd (size sl).
  rewrite /d ss2E ss3E uphalf_half; case odd; rewrite /= ?eqxx ?add1n //.
  by case: ltngtP (leqnn (size sl)./2.+1).
rewrite uphalf_half -dE s2E size_cat !size_nseq in ss2E.
rewrite s3E size_cat !size_nseq in ss3E.
have a1b1E : a1 + b1 = a2 + b2 + d by rewrite ss2E addnC ss3E.
pose s4 := nseq (maxn a1 a2) false ++ nseq (minn b1 (d + b2)) true. 
have s4S : size s4 = size (eotake p.+1 i s1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter1 s (e2n_gt0 _))).
  rewrite -/s2 s2E size_cat !size_nseq.
  lia.
pose s5 := nseq (minn a1 a2) false ++ nseq (maxn b1 (d + b2) - d) true.
have s5S : size s5 = size (eotake p.+1 (`2^ p + i) s1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter1 s (e2n_gt0 _))).
  rewrite -/s3 s3E size_cat !size_nseq.
  lia.
have <- : s4 = eotake p.+1 i s1.
  apply: (@eq_from_nth _ true) => // k kLs.
  rewrite !nth_cat !nth_nseq if_same.
  rewrite nth_eotake nth_iter1 ?e2n_gt0 //.
  rewrite -nth_eotake -/s2 !modn_small; last first.
    by rewrite (leq_trans iL2p) // leq_addr.
  rewrite [_ + `2^ _]addnC addnA.
  rewrite -[_ + i](modn_small (_ : _ < `2^ p.+1)); last first.
    by rewrite e2Sn ltn_add2l.
  rewrite -nth_eotake -/s3.
  rewrite [X in (i + X * _) %/ _]e2Sn addnn -muln2 -mulnA mulnC.
  rewrite divnDMl ?e2n_gt0 // oddD mul2n odd_double addbF.
  rewrite divn_small //= modn_small ?ltn_add2l //.
  rewrite s2E s3E !nth_cat !nth_nseq !size_nseq !if_same.
  case: (ltnP a1 a2) => [a1La2|a2La1].
    case: (ltnP k a1) => [a1Lk|kLa1].
      rewrite !(leq_trans a1Lk (ltnW _)) //=; last first.
      by rewrite minxx if_same.
    case: (ltnP k a2) => [a2Lk|kLa2].
      suff /gtn_size_eotake-> : k < size (eotake p.+1 (`2^ p + i) s).
      - by rewrite minbF.
      - by rewrite ltn_add2l.
      have : k < size s5.
        rewrite size_cat !size_nseq.
        have -> : minn a1 a2 = a1 by lia.
        have -> : maxn b1 (d + b2) = b1 by lia.
        have -> : a1 + (b1 - d) = a2 + b2 by lia.
        by apply: leq_trans (leq_addr _ _).
      rewrite s5S.
      by rewrite (eq_size_eotake _ _ (size_iter1 _ _)) // e2n_gt0.
    by rewrite !if_same.
  case: (ltnP k a2) => [a2Lk|kLa2].
    by rewrite !(leq_trans a2Lk _) // minxx if_same.
  by case: (ltnP k a1) => [a1Lk|kLa1]; rewrite if_same.
have <- : nseq (minn a1 a2) false ++ nseq (maxn b1 (d + b2) - d) true =
          eotake p.+1 (`2^ p + i) s1.
  apply: (@eq_from_nth _ true) => [|k].
    rewrite size_cat !size_nseq.
    rewrite (eq_size_eotake _ _ (size_iter1 s (e2n_gt0 _))).
    rewrite -/s3 s3E size_cat !size_nseq.
    lia.
  rewrite nth_cat !nth_nseq !size_cat !size_nseq if_same.
  rewrite nth_eotake nth_iter1 ?e2n_gt0 //.
  rewrite -nth_eotake -/s2 !modn_small; last first.
    by rewrite e2Sn ltn_add2l.
  rewrite [_ + `2^ _]addnC addnA.
  rewrite -[X in X - `2^ _]addnA [X in X - `2^ _]addnC addnK.
  rewrite -[in i + _ * k](modn_small (_ : i < `2^ p.+1)); last first.
    by rewrite (leq_trans iL2p (leq_addr _ _)).
  rewrite -nth_eotake -/s2 -/s3.
  rewrite [X in (_ + X * _) %/ _]e2Sn addnn -muln2 -mulnA mulnC.
  rewrite divnDMl ?e2n_gt0 // oddD mul2n odd_double addbF.
  rewrite -[X in X + i]mul1n [1 * _ + _]addnC divnDMl ?e2n_gt0 //.
  rewrite divn_small //= mul1n.
  rewrite s2E s3E !nth_cat !nth_nseq !size_nseq !if_same.
  case: (ltnP a1 a2) => [a1La2|a2La1].
    have -> : maxn b1 (d + b2) = b1 by lia.
    case: (ltnP k a1) => [a1Lk|kLa1].
      rewrite !(leq_trans a1Lk _) //=; last first.
      - by apply: (leq_addr _ _).
      - by apply: ltnW.
      by rewrite maxxx if_same.
    case: (ltnP k a2) => [a2Lk|kLa2].
      rewrite ifT // -e2Sn [i + _]addnC.
      suff /gtn_size_eotake-> : k < size (eotake p.+1 (`2^ p + i) s) => //.
        by rewrite ltn_add2l.
      have : k < size s5.
        rewrite size_cat !size_nseq.
        have -> : minn a1 a2 = a1 by lia.
        have -> : maxn b1 (d + b2) = b1 by lia.
        have -> : a1 + (b1 - d) = a2 + b2 by lia.
        by apply: leq_trans (leq_addr _ _).
      rewrite s5S.
      by rewrite (eq_size_eotake _ _ (size_iter1 _ _)) // e2n_gt0.
    by rewrite !if_same.
  have -> : maxn b1 (d + b2) = d + b2 by lia.
  case: (ltnP k a2) => [a2Lk|kLa2] _.
    by rewrite !(leq_trans a2Lk _) // maxxx if_same.
  by case: (ltnP k a1) => [a1Lk|kLa1]; rewrite if_same.
split.
- by apply/isorted_boolP; exists (maxn a1 a2, minn b1 (d + b2)).
- by apply/isorted_boolP; exists (minn a1 a2, maxn b1 (d + b2) - d).
by rewrite !noE; case: (ltnP a1 a2) => // ?; rewrite ltnW.
Qed.

Lemma sorted_iter2 (p : nat) q (s : seq bool) i :
  i < `2^ p -> p < q ->
  let s1 := iter2 (`2^ p) (`2^ q) s in 
  [/\ 
  sorted <=%O (eotake p.+1 i s),
  sorted <=%O (eotake p.+1 (`2^ p + i) s) & 
  noF (eotake p.+1 (`2^p + i) s) <= noF (eotake p.+1 i s) <=
  noF (eotake p.+1 (`2^p + i) s) + `2^ (q - p)]
  -> 
  [/\ 
  sorted <=%O (eotake p.+1 i s1),
  sorted <=%O (eotake p.+1 (`2^p + i) s1) &
  noF (eotake p.+1 (`2^p + i) s1) <= noF (eotake p.+1 i s1) <=
  noF (eotake p.+1 (`2^p + i) s1) + `2^ (q.-1 - p)].
Proof.
move=> iL2p pLq s1.
have q_gt0 : 0 < q by apply: leq_ltn_trans pLq.
have p2Lq2 : `2^ p < `2^ q by rewrite ltn_e2n.
have p2Dq2 : `2^ p %| `2^ q by  rewrite dvdn_e2n ltnW.
set s2 := eotake _ _ _; set s3 := eotake _ _ _.
pose d : nat := (size s2 != size s3).
move=> [] /isorted_boolP[[a1 b1] s2E] /isorted_boolP[[a2 b2] s3E].
pose sl := eotake p i s.
pose xi := a1 - a2.
pose j := xi - `2^(q - p.+1).
have ss2E : size s2 = uphalf (size sl) by rewrite -size_etake etake_eotake.
have ss3E : size s3 = (size sl)./2 by rewrite -size_otake otake_eotake.
have dE : d = odd (size sl).
  rewrite /d ss2E ss3E uphalf_half; case odd; rewrite /= ?eqxx ?add1n //.
  by case: ltngtP (leqnn (size sl)./2.+1).
rewrite uphalf_half -dE s2E size_cat !size_nseq in ss2E.
rewrite s3E size_cat !size_nseq in ss3E.
have a1b1E : a1 + b1 = a2 + b2 + d by rewrite ss2E addnC ss3E.
rewrite s3E s2E !noE => a1B.
pose s4 := nseq (a1 - j) false ++ nseq (b1 + j) true.
have s4S : size s4 = size (eotake p.+1 i s1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter2 s (e2n_gt0 _) _)) //.
  rewrite -/s2 s2E size_cat !size_nseq.
  lia.
pose s5 := nseq (a2 + j) false ++ nseq (b2 - j) true.
have s5S : size s5 = size (eotake p.+1 (`2^ p + i) s1).
  rewrite size_cat !size_nseq.
  rewrite (eq_size_eotake _ _ (size_iter2 s (e2n_gt0 _) _)) //.
  rewrite -/s3 s3E size_cat !size_nseq.
  rewrite -subSS subSn // e2Sn in a1B.
  lia.
have xiLpq : xi <= `2^ (q - p) by lia.
have <- : s4 = eotake p.+1 i s1.
  apply: (@eq_from_nth _ true) => // k kLs.
  rewrite !nth_cat !nth_nseq size_nseq if_same.
  rewrite nth_eotake /s1 nth_iter2 ?e2n_gt0 //; last first.
    rewrite -[q]prednK // e2Sn addnn -muln2.
    rewrite -divn_mulAC ?muln2 ?odd_double // dvdn_e2n //.
    by rewrite -ltnS prednK.
  rewrite -nth_eotake -/s2 !modn_small; last first.
    by rewrite (leq_trans iL2p) // leq_addr.
  rewrite s2E !nth_cat !nth_nseq !size_nseq if_same.
  rewrite [X in (i + X * _) %/ _]e2Sn addnn -doubleMl doubleMr.
  rewrite [_ * _.*2]mulnC divnDMl ?e2n_gt0 // oddD odd_double.
  rewrite divn_small //=.
  have := kLs; rewrite s4S => /gtn_size_eotake.
  have ss : size s1 = size s.
    by apply: size_iter2 => //; apply: e2n_gt0.
  rewrite ss => ->; last first.
    by rewrite // ?(leq_trans _ (leq_addr _ _)) //.
  rewrite andbT.
  case: ltnP => [kLa1j|a1jLk].
    rewrite (leq_trans kLa1j (leq_subr _ _)).
    case: leqP => // q2Lipk.
    have qp2L1k : `2^ (q -p) <= 1 + k.*2.
      have : `2^ q <= `2^ p + (`2^ p + `2^ p) * k
        by apply: leq_trans q2Lipk _; rewrite leq_add2r ltnW.
      rewrite -[in X in X <= _](subnK (ltnW pLq)) e2nD.
      rewrite addnn -doubleMl doubleMr.
      rewrite -[X in _ <= X + _]mul1n  [`2^ p * _]mulnC -mulnDl leq_mul2r.
      by case: e2n (e2n_gt0 p).
    have qp2Lk : `2^ (q - p) <= k.*2.
      have := half_leq qp2L1k.
      rewrite e2n_div2 ?subn_gt0 // halfD /= odd_double /= -leq_double.
      by rewrite -addnn -e2Sn doubleK prednK // subn_gt0.
    rewrite -addnBA; last first.
      rewrite -e2Sn -(subnK pLq) e2nD mulnC leq_mul2l.
      case: e2n (e2n_gt0 p.+1) => //= _ _.
      by rewrite subnS -e2n_div2 ?subn_gt0 // leq_half_double.
    rewrite [i + _ + _]addnAC [i + `2^ _]addnC.
    rewrite -e2Sn -(subnK pLq) [_ - _ + _]addnC e2nD -mulnBr.
    rewrite -[_ + i](modn_small (_ : _ < `2^ p.+1)); last by rewrite ltn_add2l.
    rewrite -nth_eotake -/s3 s3E nth_cat !nth_nseq /= size_nseq.
    case: leqP => //.
    have : (`2^ (q -p.+1)).*2 = `2^ (q -p).
      by rewrite -addnn -e2Sn -subSn.
    lia.
  case: (leqP (`2^ q)) => [q2Lipk|ipkLq2].
    have qp2L1k : `2^ (q -p) <= 1 + k.*2.
      have : `2^ q <= `2^ p + (`2^ p + `2^ p) * k
        by apply: leq_trans q2Lipk _; rewrite leq_add2r ltnW.
      rewrite -[in X in X <= _](subnK (ltnW pLq)) e2nD.
      rewrite addnn -doubleMl doubleMr.
      rewrite -[X in _ <= X + _]mul1n  [`2^ p * _]mulnC -mulnDl leq_mul2r.
      by case: e2n (e2n_gt0 p).
    have qp2Lk : `2^ (q - p) <= k.*2.
      have := half_leq qp2L1k.
      rewrite e2n_div2 ?subn_gt0 // halfD /= odd_double /= -leq_double.
      by rewrite -addnn -e2Sn doubleK prednK // subn_gt0.
    rewrite -addnBA; last first.
      rewrite -e2Sn -(subnK pLq) e2nD mulnC leq_mul2l.
      case: e2n (e2n_gt0 p.+1) => //= _ _.
      by rewrite -leq_double -addnn -e2Sn -subSn.
    rewrite [i + _ + _]addnAC [i + `2^ _]addnC.
    rewrite -e2Sn -(subnK pLq) [_ - _ + _]addnC e2nD -mulnBr.
    rewrite -[_ + i](modn_small (_ : _ < `2^ p.+1)); last by rewrite ltn_add2l.
    rewrite -nth_eotake -/s3 s3E nth_cat !nth_nseq /= size_nseq.
    case: leqP => // k2pqLa2; first by rewrite if_same maxTb.
    case: leqP => //.
    lia.
  case: leqP => //.
  have : (`2^ (q -p) * `2^ p) = `2^ q by rewrite -e2nD subnK // ltnW.
  have : (`2^ (q -p.+1)).*2 = `2^ (q -p) by rewrite -addnn -e2Sn -subSn.
  move=> {ss kLs xiLpq s5S s4S a1B a1b1E ss2E ss3E dE s3E s2E p2Dq2}//. 
  by nia.
have <- : s5 = eotake p.+1 (`2^ p + i) s1.
  apply: (@eq_from_nth _ true) => // k kLs.
  rewrite !nth_cat !nth_nseq size_nseq if_same.
  rewrite nth_eotake /s1 nth_iter2 ?e2n_gt0 //; last first.
    rewrite -[q]prednK // e2Sn addnn -muln2.
    rewrite -divn_mulAC ?muln2 ?odd_double // dvdn_e2n //.
    by rewrite -ltnS prednK.
  rewrite -nth_eotake -/s2 !modn_small; last first.
    by rewrite ltn_add2l.
  rewrite -/s3.
  rewrite s3E !nth_cat !nth_nseq !size_nseq if_same.
  rewrite [X in (_ + i + X * _) %/ _]e2Sn addnn -doubleMl doubleMr.
  rewrite [_ * _.*2]mulnC divnDMl ?e2n_gt0 // oddD odd_double.
  rewrite -[X in (X + i) %/ _]mul1n [X in X %/ _]addnC divnDMl ?e2n_gt0 //.
  rewrite addn1 /= divn_small //=.
  rewrite -!addnA [`2^ p + (_ + _)]addnC !addnA addnK ltn_add2r.
  case: (ltnP k a2) => [kLa2|a2Lk].
    rewrite (leq_trans kLa2 (leq_addr _ _)).
    by rewrite minFb if_same.
  rewrite minTb.
  case: leqP => [a2jLk|kLa2j].
    case: leqP => // q2Lipk.
    rewrite -[i](modn_small (_ : _ < `2^ p.+1)); last first.
      by rewrite e2Sn; lia.
    rewrite -e2Sn -(subnK pLq) e2nD -addnA [_ * k]mulnC -mulnDl mulnC.
    rewrite -nth_eotake.
    rewrite -/s2 s2E nth_cat !nth_nseq /= size_nseq if_same.
    by case: leqP => //; lia.
  rewrite ifT; last first.
    have kqpLa1 : k + `2^ (q - p.+1) < a1 by lia.
    have iL2p1 : i < `2^ p.+1 by rewrite (leq_trans iL2p (leq_addr _ _)).
    have kqpLss2 : k + `2^ (q - p.+1) < size s2.
      by rewrite s2E size_cat !size_nseq; lia.
    rewrite -e2Sn.
    have <- : (`2^ (q -p.+1) * `2^ p.+1) = `2^ q by rewrite -e2nD subnK // ltnW.
    rewrite [_ * `2^ p.+1]mulnC -addnA -mulnDr.
    by apply: gtn_size_eotake iL2p1 kqpLss2.
  rewrite -[i](modn_small (_ : _ < `2^ p.+1)); last first.
    by rewrite e2Sn; lia.
  rewrite -e2Sn -(subnK pLq) e2nD -addnA [_ * k]mulnC -mulnDl mulnC.
  rewrite -nth_eotake.
  rewrite -/s2 s2E nth_cat !nth_nseq /= size_nseq if_same.
  by case: leqP => //; lia.
split.
- by apply/isorted_boolP; exists (a1 - j, b1 + j).
- by apply/isorted_boolP; exists (a2 + j, b2 - j).
rewrite !noE.
have : (`2^ (q.-1 - p)).*2 = `2^ (q -p).
  by rewrite -addnn -e2Sn -subSn ?prednK; lia.
have : (`2^ (q - p.+1)).*2 = `2^ (q -p).
  rewrite -addnn -e2Sn -subSn ?subSS //.
lia.
Qed.

Lemma sorted_iter3_aux k (p : nat) q (s : seq bool) i :
  i < `2^ p -> q < k + p ->
  let l1 := iter3_aux k (`2^ p) (`2^ q) s in 
  [/\ 
  sorted <=%O (eotake p.+1 i s),
  sorted <=%O (eotake p.+1 (`2^ p + i) s) & 
  noF (eotake p.+1 (`2^p + i) s) <= noF (eotake p.+1 i s) <=
  noF (eotake p.+1 (`2^p + i) s) + `2^ (q - p)]
  -> 
  [/\ 
  sorted <=%O (eotake p.+1 i l1),
  sorted <=%O (eotake p.+1 (`2^p + i) l1) &
  noF (eotake p.+1 (`2^p + i) l1) <= noF (eotake p.+1 i l1) <=
  noF (eotake p.+1 (`2^p + i) l1) + 1].
Proof.
move=> iL2p.
elim: k q s => [q s | k IH q s qLp].
  rewrite [iter3_aux _ _ _ _]/= => qLp.
  by have -> : q - p = 0 by lia.
rewrite [iter3_aux _ _ _ _]/=.
case: leqP => [p2Lq2|q2Lp2].
  move=> l1; suff -> : q - p = 0 by [].
  by apply/eqP; rewrite subn_eq0 -leq_e2n.
have q_gt0 : 0 < q by rewrite (leq_ltn_trans (_ : 0 <= p)) -1?ltn_e2n.
rewrite e2n_div2 // => l1 Hs.
apply: IH; try lia.
apply: sorted_iter2 => //.
by rewrite -ltn_e2n.
Qed.

Lemma sorted_iter3 (p : nat) q (s : seq bool) i :
  i < `2^ p -> `2^ q < size s <= `2^ q.+1 -> p <= q ->
  let l1 := iter3 (`2^ q) (`2^ p) s in 
  [/\ 
  sorted <=%O (eotake p.+1 i s),
  sorted <=%O (eotake p.+1 (`2^ p + i) s) & 
  noF (eotake p.+1 (`2^p + i) s) <= noF (eotake p.+1 i s)]
  -> 
  sorted <=%O (eotake p i l1).
Proof.
move=> iLp /andP[qLsl slL2q] pLq s1 [Hl Hr Hw].
apply: sorted_eotake => //.
apply: sorted_iter3_aux => //.
  apply: leq_trans (leq_addr _ _).
  by rewrite ltnS (leq_trans (ltnW (ltn_ne2n _)) (ltnW qLsl)).
split => //.
apply/andP; split => //.
apply: leq_trans (leq_addl _ _).
apply: leq_trans (_ : size (eotake p.+1 i s) <= _).
  by rewrite -size_noFT leq_addr.
rewrite -subSS.
by apply: leq_size_eotake_e2n.
Qed.

Lemma sorted_iknuth_exchange_aux k (p : nat) q (s : seq bool) :
  0 < q -> `2^ q < size s <= `2^ q.+1 -> p <= q -> p < k ->
  let s1 := iknuth_exchange_aux k (`2^ q) (`2^ p) s in 
  (forall i, i < `2^ p -> 
  [/\ 
  sorted <=%O (eotake p.+1 i s) &
  sorted <=%O (eotake p.+1 (`2^ p + i) s)]) ->
  sorted <=%O s1.
Proof.
move=> g_gt0.
elim: k p s => // k IH [|p] s qLs pLq pLk s1 Hs.
  rewrite {}/s1.
  case: {IH pLk}k => /= [|_].
  - apply: (@sorted_iter3 0 q (iter1 1 s) 0) => //.
      by rewrite size_iter1.
    have [|H1 H2]// := Hs 0.
    by apply: sorted_iter1.
  apply: (@sorted_iter3 0 q (iter1 1 s) 0) => //.
    by rewrite size_iter1.
  have [|H1 H2]// := Hs 0.
  by apply: sorted_iter1.
rewrite /s1 /= -e2Sn e2n_gt0 e2n_div2 //.
apply: IH => //.
- by rewrite size_iter3 ?e2n_gt0 // size_iter1 ?e2n_gt0.
- by rewrite /= // (leq_trans _ pLq).
move=> i Hi.
split => //.
  have iL2p : i < `2^ p.+1 by apply: leq_trans Hi _; rewrite leq_e2n.
  have [Hs1 Hs2] := Hs _ iL2p.
  apply: sorted_iter3 => //.
    by rewrite size_iter1 ?e2n_gt0.
  by apply: sorted_iter1.
have iL2p : `2^ p + i < `2^ p.+1 by rewrite ltn_add2l.
have [Hs1 Hs2] := Hs _ iL2p.
apply: sorted_iter3 => //.
  by rewrite size_iter1 ?e2n_gt0.
by apply: sorted_iter1.
Qed.

Lemma sorted_iknuth_exchange (s : seq bool) :
  sorted <=%O (iknuth_exchange s).
Proof.
case: (ltP 3 (size s)) => [sl_gt4|]; last first.
  case: s => // a [|b [|c []]]//= _; lia.
have ss_gt1 : 1 < size s by apply: leq_trans sl_gt4.
have up_gt0 : 0 < up_log 2 (size s).
  by rewrite up_log_gt0 // (leq_trans _ sl_gt1).
have up_gt1 : 1 < up_log 2 (size s).
  by rewrite -{1}[2]/(up_log 2 4) leq_up_log.
apply: sorted_iknuth_exchange_aux => //.
- by rewrite -ltnS prednK.
- rewrite prednK //.
  by rewrite !e2nE; apply: up_log_bounds.
- apply: ltn_trans (ltn_ne2n _) _.
  have /andP[] := (up_log_bounds (isT: 1 < 2) ss_gt1).
  by  rewrite e2nE.
move=> i iLu;rewrite prednK //.
set x := up_log 2 _; split.
  have : size (eotake x i s) <= `2^ (x - x).
    apply: leq_size_eotake_e2n => //.
    by rewrite e2nE; apply: up_logP.
  by rewrite subnn; case: eotake => //= a [|].
have : size (eotake x (`2^ x.-1 + i) s) <= `2^ (x - x).
  apply: leq_size_eotake_e2n => //.
  by rewrite e2nE; apply: up_logP.
by rewrite subnn; case: eotake => //= a [|].
Qed.

