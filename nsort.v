From mathcomp Require Import all_ssreflect perm.
From mathcomp Require Import zify.

Import Order POrderTheory TotalTheory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Network.

Variable m : nat.

(* Representing a network as a sequence of swap *)
Definition network := seq ('I_m * 'I_m).

(* Empty network *)
Definition nempty : network := [::].

Variable d : unit.
Variable A : orderType d.

Implicit Types t : m.-tuple A.
Implicit Types a : 'I_m * 'I_m.
Implicit Types n : network.

(* Swaping two elements *)
Definition nswap a t :=
  if (tnth t a.1 <= tnth t a.2)%O then t else
    [tuple tnth t (tperm a.1 a.2 i) | i < m].

Lemma nswapE_neq a t i : i != a.1 -> i != a.2 ->  tnth (nswap a t) i = tnth t i.
Proof.
rewrite /nswap; case: (_ <= _)%O => //.
by rewrite tnth_map /= tnth_ord_tuple; case: tpermP => // ->; rewrite eqxx.
Qed.

Lemma nswapE_min a t : tnth (nswap a t) a.1 = min (tnth t a.1) (tnth t a.2).
Proof.
rewrite /nswap; case: leP => //.
by rewrite tnth_map /= tnth_ord_tuple tpermL.
Qed.

Lemma nswapE_max a t : tnth (nswap a t) a.2 = max (tnth t a.1) (tnth t a.2).
Proof.
rewrite /nswap; case: leP => //.
by rewrite tnth_map /= tnth_ord_tuple tpermR.
Qed.

Lemma nswap_perm t a : perm_eq (nswap a t) t.
Proof.
rewrite /nswap; case: (_ <= _)%O => //.
by apply/tuple_permP; exists (tperm a.1 a.2) => /=.
Qed.

(* turn a network into a function *)
Definition nfun n t := foldl (fun t a => nswap a t) t n.

Lemma nfunE n a t : nfun (a :: n) t = nfun n (nswap a t).
Proof. by []. Qed.

Lemma nfun_cat n1 n2 t : nfun (n1 ++ n2) t = nfun n2 (nfun n1 t).
Proof. by elim: n1 t => /=. Qed.

Lemma nfun_perm n t : perm_eq (nfun n t) t.
Proof.
elim: n t => //= p n IH t.
by apply: perm_trans (IH _) (nswap_perm _ _).
Qed.

Lemma fun_of_network_empty : nfun nempty =1 id.
Proof. by []. Qed.

End Network.

Section E2.

Fixpoint e2 n := if n is n1.+1 then e2 n1 + e2 n1 else 1.

Lemma e2E n : e2 n = 2 ^ n.
Proof. by elim: n => //= n ->; rewrite expnS mul2n addnn. Qed. 

Lemma e2S n : e2 n.+1 = e2 n + e2 n.
Proof. by []. Qed.

End E2.

Section TMap.

Variable m : nat.
Variable d1 d2 : unit.
Variable A : orderType d1.
Variable B : orderType d2.
Variable f : A -> B.

Definition tmap (A1 A2 : Type) (g : A1 -> A2) t := [tuple g (tnth t i) | i < m].

Lemma tmap_val (A1 A2 : Type) (g : A1 -> A2) t : tmap g t = map g t :> seq A2.
Proof.
have -> : tmap g t = [tuple of [seq g (tnth t i) | i <- ord_tuple m]].
  by apply: eq_from_tnth => i; rewrite !(tnth_map, tnth_ord_tuple).
congr tval.
by apply: eq_from_tnth => i; rewrite !(tnth_map, tnth_ord_tuple).
Qed.

Lemma tmap_nswap a t : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} ->
  nswap a (tmap f t) = tmap f (nswap a t).
Proof.
move=> Hm; apply: eq_from_tnth => i.
rewrite /nswap !tnth_map !tnth_ord_tuple.
case: (leP (tnth _ _)) => [/Hm->//|a2La1].
 by rewrite !(tnth_map, tnth_ord_tuple).
case: leP; rewrite !(tnth_map, tnth_ord_tuple) // => a1La2.
by case: tpermP => [->|->|//]; apply/eqP; rewrite eq_le a1La2 Hm // ltW.
Qed.

Lemma tmap_nfun n t : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} ->
  nfun n (tmap f t) = tmap f (nfun n t).
Proof.
by move=> Hm; elim: n t => //= a n IH t; rewrite tmap_nswap // IH.
Qed.

End TMap.

Section SortedPn.

Variable d : unit.
Variable A : orderType d.

Lemma sortedPn (l : seq A) :
  reflect 
    (exists2 x, l = x.2.1 ++ [:: x.1.1, x.1.2 & x.2.2] & (x.1.2 < x.1.1)%O)
    (~~ sorted <=%O l).
Proof.
elim: l => [|a [|b l] IH].
- by apply: (iffP idP) => // [[[x1 [[|x x21] x22] []]]].
- by apply: (iffP idP) => // [[[x1 [[|x [| y x21]] x22] []]]].
rewrite /= negb_and; case: leP => [aLb | bLa] /=; last first.
  by apply: (iffP idP) => // _; exists ((a, b), ([::], l)).
apply: (iffP IH) => [] [[[x1 x2] [l1 l2]] /= blE x2Lx1] /=.
  by exists ((x1, x2), (a :: l1, l2)) => //=; rewrite blE.
case: l1 blE => [[aE bE lE]|x3 l1 [aE blE]].
  by move: aLb; rewrite aE bE leNgt x2Lx1.
by exists ((x1, x2), (l1, l2)).
Qed.

End SortedPn.

Section Sorting.

Variable m : nat.
Variable d : unit.
Variable A : orderType d.

(* Decided sorting using boolean (we use the 0-1 theorem for the def) *)
Definition sorting :=
  [qualify n | [forall r : m.-tuple bool, sorted <=%O (nfun n r)]].

Lemma sorted_sorting n (x1 x2 : A) : 
  x1 != x2 -> (forall r : m.-tupleA, sorted <=%O (nfun n r)) -> n \is sorting.
Proof.
wlog x1Lx2 : x1 x2 / (x1 < x2)%O => [Hgs x1Dx2 Hs|].
  case: (ltgtP x1 x2) => [/Hgs->|/Hgs->|] //; first by rewrite eq_sym.
  by move/eqP; rewrite (negPf x1Dx2).
move=> x1Dx2 Hgs; apply/forallP => /= t.
pose f x := if x then x2 else x1.
pose g x := if (x <= x1)%O then false else true.
have fK : cancel f g by case => /=; rewrite /g ?le_refl // leNgt x1Lx2.
have gM : {homo g : x y / (x <= y)%O >-> (x <= y)%O}.
  move=> i j; rewrite /g.
  case: (leP i x1); case: (leP j x1) => // jLx1 x1Li.
  by rewrite leNgt (le_lt_trans jLx1).
have -> : t = tmap g (tmap f t).
  by apply: eq_from_tnth => i; rewrite !tnth_map !tnth_ord_tuple fK.
by rewrite tmap_nfun // tmap_val (homo_sorted gM _ _).
Qed.

Lemma sorting_sorted n (r : m.-tuple A) :
  n \is sorting -> sorted <=%O (nfun n r).
Proof.
apply: contraLR => /sortedPn[[[x1 x2]][l1 l2] /= nfunE x2Lx1].
rewrite negb_forall.
pose g x := if (x <= x2)%O then false else true.
have gM : {homo g : x y / (x <= y)%O >-> (x <= y)%O}.
  move=> i j; rewrite /g.
  case: (leP i x2); case: (leP j x2) => // jLx2 x2Li.
  by rewrite leNgt (le_lt_trans jLx2).
apply/existsP; exists (tmap g r).
apply/sortedPn; exists ((g x1, g x2), (map g l1, map g l2)) => /=.
  by rewrite tmap_nfun // tmap_val nfunE map_cat.
by rewrite /g lexx leNgt x2Lx1.
Qed.

End Sorting.

Section Bitonic.

Variable d : unit.
Variable A : orderType d.

Search drop size.

Definition bitonic := [qualify p | 
 [exists r : 'I_(size (p : seq A)).+1, 
  exists n : 'I_(size (p : seq A)).+1,
  let p1 := rot r p in sorted (<=%O) (take n p1) && sorted (>=%O) (drop n.-1 p1)]].

Lemma ttake_proof m1 m2 : minn m1 (m1 + m2) = m1.
Proof. by rewrite minnC minnE [m1 + m2]addnC addnK [m2 + m1]addnC addnK. Qed.

Lemma tdrop_proof m1 m2 : (m1 + m2) - m1 = m2.
Proof. by rewrite addnC addnK. Qed.

Definition ttake (m1 m2 : nat) (t : (m1 + m2).-tuple A) :=
  tcast (ttake_proof m1 m2) [tuple of take m1 t].

Lemma ttakeE (m1 m2 : nat) (t : (m1 + m2).-tuple A) : 
  ttake t = take m1 t :> seq A.
Proof. by rewrite val_tcast. Qed.

Definition tdrop (m1 m2 : nat) (t : (m1 + m2).-tuple A) :=
  tcast (tdrop_proof m1 m2) [tuple of drop m1 t].

Lemma tdropE (m1 m2 : nat) (t : (m1 + m2).-tuple A) : 
  tdrop t = drop m1 t :> seq A.
Proof. by rewrite val_tcast. Qed.

Definition tsplit (m1 m2 : nat) (t : (m1 + m2).-tuple A) :=
  (ttake t, tdrop t).

Definition trev m (t : m.-tuple A) := [tuple of rev t].

Fixpoint tmerge (m : nat) : forall t  : (e2 m).-tuple A, (e2 m).-tuple A := 
  if m is m1.+1 then fun t =>
  let t1 := ttake t in
  let t2 := tdrop t in
  let t3 := [tuple min (tnth t1 i) (tnth t2 i) | i < e2 m1] in 
  let t4 := [tuple max (tnth t1 i) (tnth t2 i) | i < e2 m1] in
  [tuple of tmerge t3 ++ tmerge t4]
  else fun t => t.

Fixpoint lmerge (m : nat) (l : seq A) := 
  if m is m1.+1 then
  let n := e2 m1 in
  let l1 := take n l in
  let l2 := drop n l in
  let l3 := [seq min i.1 i.2 | i <- zip l1 l2] in
  let l4 := [seq max i.1 i.2 | i <- zip l1 l2] in
  lmerge m1 l3 ++ lmerge m1 l4
  else l.

Lemma tmergeE m (t : (e2 m).-tuple A) : tmerge t = lmerge m t :> seq A.
Proof.
elim: m t => //= m IH t.
have e2P : 0 < e2 m by rewrite e2E expn_gt0.
have e2DP : 0 < e2 m + e2 m by rewrite addn_gt0 e2P.
have e2D2P : e2 m < e2 m + e2 m by rewrite -addn1 leq_add2l.
pose x := tnth t (Ordinal e2DP).
rewrite !IH; congr (lmerge _ _ ++ lmerge _ _); apply: (@eq_from_nth _ x) => //=.
- rewrite !size_map size_zip size_take size_drop size_tuple addnK.
- by rewrite -fintype.enumT -enum_ord size_enum_ord e2D2P minnn.
- move=> i; rewrite size_map -fintype.cardT /= card_ord => iLe2.
  rewrite -enum_ord (nth_map (Ordinal e2P)) ?size_enum_ord //.
  rewrite (nth_map (x, x)) ?nth_zip /=.
  - by rewrite !(tnth_nth x) nth_enum_ord // !val_tcast.
  - by rewrite size_take size_drop size_tuple e2D2P addnK.
  by rewrite size_zip size_take size_drop size_tuple e2D2P addnK minnn.
  - rewrite !size_map size_zip.
  rewrite -fintype.enumT -enum_ord size_enum_ord.
  by rewrite size_take size_drop size_tuple e2D2P addnK minnn.
move=> i; rewrite size_map -fintype.cardT /= card_ord => iLe2.
rewrite -enum_ord (nth_map (Ordinal e2P)) ?size_enum_ord //.
rewrite (nth_map (x, x)) ?nth_zip /=.
- by rewrite !(tnth_nth x) nth_enum_ord // !val_tcast.
- by rewrite size_take size_drop size_tuple e2D2P addnK.
by rewrite size_zip size_take size_drop size_tuple e2D2P addnK minnn.
Qed.

Fixpoint bsort (m : nat) : forall (t : (e2 m).-tuple A), (e2 m).-tuple A := 
  if m is m1.+1 then fun t =>
  let t1 := bsort (ttake t) in
  let t2 := trev (bsort (tdrop t)) in
  tmerge ([tuple of t1 ++  t2] : (e2 m1.+1).-tuple A)
  else fun t => t.

Fixpoint lsort (m : nat) (l : seq A) := 
  if m is m1.+1 then
  let n := e2 m1 in 
  let t1 := lsort m1 (take n l) in
  let t2 := rev (lsort m1 (drop n l)) in
  lmerge m1.+1 (t1 ++  t2)
  else l.

Lemma bsortE m (t : (e2 m).-tuple A) : bsort t = lsort m t :> seq A.
Proof.
elim: m t => //= m IH t.
have e2P : 0 < e2 m by rewrite e2E expn_gt0.
have e2DP : 0 < e2 m + e2 m by rewrite addn_gt0 e2P.
have e2D2P : e2 m < e2 m + e2 m by rewrite -addn1 leq_add2l.
pose x := tnth t (Ordinal e2DP).
rewrite !tmergeE.
congr (lmerge _ _ ++ lmerge _ _); apply: (@eq_from_nth _ x) => //=.
- rewrite !size_map size_zip size_take size_drop size_cat size_rev.
  rewrite -ttakeE -tdropE -!IH !size_tuple e2D2P addnK minnn.
  by rewrite -fintype.enumT -enum_ord size_enum_ord.
- move=> i.
  rewrite size_map -?fintype.cardT /= ?card_ord => iLe2.
  rewrite -enum_ord (nth_map (Ordinal e2P)) ?size_enum_ord //.
  rewrite (nth_map (x, x)) ?nth_zip /=.
  - by rewrite !(tnth_nth x) nth_enum_ord // !val_tcast /= -/e2 !IH
               ttakeE tdropE.
  - by rewrite size_take size_drop size_cat size_rev -ttakeE -tdropE -!IH 
               !size_tuple e2D2P addnK.
  by rewrite size_zip size_take size_drop size_cat size_rev -ttakeE -tdropE -!IH 
               !size_tuple e2D2P addnK minnn.
  rewrite !size_map size_zip size_take size_drop size_cat size_rev.
  rewrite -ttakeE -tdropE -!IH !size_tuple e2D2P addnK minnn.
  by rewrite -fintype.enumT -enum_ord size_enum_ord.
move=> i.
rewrite size_map -?fintype.cardT /= ?card_ord => iLe2.
rewrite -enum_ord (nth_map (Ordinal e2P)) ?size_enum_ord //.
rewrite (nth_map (x, x)) ?nth_zip /=.
- by rewrite !(tnth_nth x) nth_enum_ord // !val_tcast /= -/e2 !IH
              ttakeE tdropE.
- by rewrite size_take size_drop size_cat size_rev -ttakeE -tdropE -!IH 
             !size_tuple e2D2P addnK.
by rewrite size_zip size_take size_drop size_cat size_rev -ttakeE -tdropE -!IH 
           !size_tuple e2D2P addnK minnn.
Qed.

End Bitonic.

Arguments bitonic {d A}.

Lemma isorted_consF l : sorted <=%O (false :: l) = sorted <=%O (l).
Proof. by elim: l. Qed.

Lemma dsorted_consF l : sorted >=%O (false :: l) = (l == nseq (size l) false).
Proof. by elim: l => // [[]] //= [|[]]. Qed.

Lemma isorted_consT l : sorted <=%O (true :: l) = (l == nseq (size l) true).
Proof. by elim: l => // [[]] //= [|[]]. Qed.

Lemma dsorted_consT l : sorted >=%O (true :: l) = sorted >=%O l.
Proof. by elim: l => //= [[]]. Qed.

Lemma isorted_boolP (l : seq bool) :
  reflect (exists t,
            let: (j,k) := t in l = nseq j false ++ nseq k true) 
          (sorted <=%O l).
Proof.
elim: l => [|[] l IH].
- by apply: (iffP idP) => // _; exists (0,0).
- rewrite isorted_consT; apply: (iffP eqP) => [->|[[[|j] k]]] /=.
  + by exists (0, (size l).+1).
  + by case: k => [|k /= [->]]; rewrite ?size_nseq.
  by case.
rewrite isorted_consF; apply: (iffP IH) => [] [[j k]].
  by move=> ->; exists (j.+1, k).
case: j => /= [|j [->]]; first by case: k.
by exists (j, k).
Qed.

Lemma dsorted_boolP (l : seq bool) :
  reflect (exists t,
            let: (j,k) := t in l = nseq j true ++ nseq k false) 
          (sorted >=%O l).
Proof.
elim: l => [|[] l IH].
- by apply: (iffP idP) => // _; exists (0,0).
- rewrite dsorted_consT; apply: (iffP IH) => [] [[j k]].
    by move=> ->; exists (j.+1, k).
  case: j => /= [|j [->]]; first by case: k.
  by exists (j, k).
rewrite dsorted_consF; apply: (iffP eqP) => [->|[[[|j] k]]] /=.
- by exists (0, (size l).+1).
- by case: k => [|k /= [->]]; rewrite ?size_nseq.
by case.
Qed.

Section HalfCleaner.

Variable d : unit.
Variable A : orderType d.

Definition half_cleaner n := [seq (lshift n i, rshift n i) | i  <- enum 'I_n].

Lemma nfun_half_cleaner n (t : (n + n).-tuple A) : 
  nfun (half_cleaner n) t = 
  [tuple
    match split i with 
    | inl x => min (tnth t i) (tnth t (rshift n x))  
    | inr x => max (tnth t (lshift n x)) (tnth t i)
    end | i < n + n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /half_cleaner.
pose i1 := match split i with inl x => x | inr x => x end.
rewrite tnth_map /= tnth_ord_tuple.
set v := LHS; set v1 := RHS.
suff : if i1 \in (enum 'I_n) then v = v1 else v = tnth t i.
  by rewrite mem_enum inE.
rewrite {}/v1 {}/v {}/i1; elim: (enum _) (enum_uniq 'I_n) t => 
     //= a l IH /andP[aNIl Ul] t.
rewrite inE; case: eqP => [aE|/eqP aNE] /=.
  have := IH Ul (nswap (lshift n a, rshift n a) t).
  case: splitP aE aNIl => [j iE <- /negPf -> -> |j iE <- /negPf -> ->].
    suff -> : lshift n j = i by apply: nswapE_min.
    by apply/val_eqP; rewrite /= iE.
  suff -> : rshift n j = i by apply: nswapE_max.
  by apply/val_eqP; rewrite /= iE.
have := IH Ul (nswap (lshift n a, rshift n a) t).
case: splitP aNE aNIl => [j iE jDa aNIl |j iE jDa aNIl].
  have njDa : n + j != a.
    by rewrite neq_ltn (leq_trans (ltn_ord _)) ?orbT ?leq_addr.
  have iDa : i != a :> nat by rewrite iE.
  have iDna : i != n + a :> nat.
    by rewrite neq_ltn iE (leq_trans (ltn_ord _)) ?leq_addr.
  by have [jIl -> |jNIl ->] := boolP (j \in l);
     rewrite !nswapE_neq //=; apply/eqP/val_eqP; rewrite /= ?eqn_add2l.
have iDa : i != a :> nat.
  by rewrite iE neq_ltn (leq_trans (ltn_ord _)) ?orbT ?leq_addr.
have iDna : i != n + a :> nat by rewrite iE eqn_add2l.
have jDna : j != n + a :> nat.
  by rewrite neq_ltn (leq_trans (ltn_ord _)) ?leq_addr.
by have [jIl -> |jNIl ->] := boolP (j \in l);
   rewrite !nswapE_neq //=; apply/eqP/val_eqP.
Qed.

End HalfCleaner.

Lemma bitonic_boolP (l : seq bool) :
  reflect (exists t,
            let: (b,i,j,k) := t in l = nseq i b ++ nseq j (~~ b) ++ nseq k b)
          (l \is bitonic).
Proof.
apply: (iffP existsP) => /= [[x /existsP[n /andP[isort dsort]]]|
                             [[[[b i] j] k] ->]]; last first.
  rewrite !size_cat !size_nseq.
  case: b => /=.
    have iL : i < (i + (j + k)).+1 by rewrite ltnS leq_addr.
    have ijkL : i + (j + k)  < (i + (j + k)).+1 by [].
    exists (Ordinal iL); apply/existsP; exists (Ordinal ijkL) => /=.
    rewrite -[X in rot X](size_nseq i true) rot_size_cat.
    rewrite take_oversize; last by rewrite ?(size_cat, size_nseq) addnC.
    apply/andP; split.
      by apply/isorted_boolP; exists (j, k + i); rewrite nseqD catA.
    set l1 := drop _ _; suff : size l1 <= 1 by case: l1 => // a [].
    rewrite size_drop !size_cat !size_nseq addnC.
    by case: (_ + _) => //= n; rewrite subSnn.
  have ijL : i + j < (i + (j + k)).+1 by rewrite ltnS addnA leq_addr.
  have ijkL : i + (j + k)  < (i + (j + k)).+1 by [].
  exists (Ordinal ijL); apply/existsP; exists (Ordinal ijkL) => /=.
  have -> : (i + j) = size (nseq i false ++ nseq j true).
    by rewrite size_cat !size_nseq.
  rewrite catA rot_size_cat.
  rewrite take_oversize; last by rewrite ?(size_cat, size_nseq) addnC addnA.
  apply/andP; split.
    by apply/isorted_boolP; exists (k + i, j); rewrite nseqD catA.
  set l1 := drop _ _; suff : size l1 <= 1 by case: l1 => // a [].
  rewrite size_drop !size_cat !size_nseq addnC addnA.
  by case: (_ + _) => //= n; rewrite subSnn.
case: (val n) isort dsort => [|n1] /= isort dsort /=.
  rewrite drop0 in dsort.
  have /dsorted_boolP[[j2 k2] Hrot] := dsort.
  have -> : l = rotr x (nseq j2 true ++ nseq k2 false).
    by apply: (@rot_inj x); rewrite rotrK.
  rewrite /rotr !size_cat !size_nseq.
  set i2 := j2 + k2 - x.
  have [i2Lj2|j2Li2] := leqP i2 j2.
    rewrite -(subnK i2Lj2) addnC nseqD -catA.
    rewrite -{1}[i2](size_nseq i2 true) rot_size_cat.
    by exists (true, j2 - i2, k2, i2); rewrite !catA.
  have [i2j2Lk2|k2Li2j2] := leqP (i2 - j2) k2.
    rewrite -(subnK i2j2Lk2) addnC nseqD catA.
    have {1}-> : i2 = size (nseq j2 true ++ nseq (i2 - j2) false).
      by rewrite size_cat !size_nseq addnC subnK // ltnW.
    rewrite rot_size_cat.
    by exists (false, k2 - (i2 - j2), j2, i2 - j2); rewrite !catA.
  rewrite rot_oversize.
    by exists (true, j2, k2, 0); rewrite !catA cats0.
  rewrite size_cat !size_nseq.
  by rewrite -leq_subRL ltnW.
have /isorted_boolP[[j1 k1] Hirot] := isort.
have /dsorted_boolP[[[|j2] /= k2] Hdrot] := dsort.
  case: k2 Hdrot => [|k2] /= Hdrot.
    have -> : l = rotr x (nseq j1 false ++ nseq k1 true).
      apply: (@rot_inj x); rewrite rotrK.
      rewrite -[LHS](cat_take_drop n1.+1) Hirot.
      suff -> : drop n1.+1 (rot x l) = [::] by rewrite cats0.
      by rewrite -[n1.+1]add1n -drop_drop Hdrot.
    rewrite /rotr !size_cat !size_nseq.
    set i1 := j1 + k1 - x.
    have [i1Lj1|j1Li1] := leqP i1 j1.
      rewrite -(subnK i1Lj1) addnC nseqD -catA.
      rewrite -{1}[i1](size_nseq i1 false) rot_size_cat.
      by exists (false, j1 - i1, k1, i1); rewrite !catA.
    have [i1j1Lk1|k1Li1j1] := leqP (i1 - j1) k1.
      rewrite -(subnK i1j1Lk1) addnC nseqD catA.
      have {1}-> : i1 = size (nseq j1 false ++ nseq (i1 - j1) true).
        by rewrite size_cat !size_nseq addnC subnK // ltnW.
      rewrite rot_size_cat.
      by exists (true, k1 - (i1 - j1), j1, i1 - j1); rewrite !catA.
    rewrite rot_oversize.
      by exists (false, j1, k1, 0); rewrite !catA cats0.
    rewrite size_cat !size_nseq.
    by rewrite -leq_subRL ltnW.
  have -> : l = rotr x (nseq j1 false ++ nseq k1 true ++ nseq k2 false).
    apply: (@rot_inj x); rewrite rotrK.
    rewrite -[LHS](cat_take_drop n1.+1) Hirot.
    by rewrite -[n1.+1]add1n -drop_drop Hdrot /= drop0 !catA.
  rewrite /rotr !size_cat !size_nseq.
  set i1 := j1 + (k1 + k2) - x.
  have [i1Lj1|j1Li1] := leqP i1 j1.
    rewrite -(subnK i1Lj1) addnC nseqD -catA.
    rewrite -{1}[i1](size_nseq i1 false) rot_size_cat.
    by exists (false, j1 - i1, k1, k2 + i1); rewrite nseqD !catA.
  have [i1j1Lk1|k1Li1j1] := leqP (i1 - j1) k1.
    rewrite -(subnK i1j1Lk1) addnC nseqD -!catA catA.
    have {1}-> : i1 = size (nseq j1 false ++ nseq (i1 - j1) true).
      by rewrite size_cat !size_nseq addnC subnK // ltnW.
    rewrite rot_size_cat.
    by exists (true, k1 - (i1 - j1), k2 + j1, i1 - j1); rewrite nseqD !catA.
  have [i1j1k1Lk2|k2Li1j1k1] := leqP (i1 - j1 - k1) k2.
    rewrite -(subnK i1j1k1Lk2) addnC nseqD.
    have {1}-> : i1 = size (nseq j1 false ++ nseq k1 true ++
                            nseq (i1 - j1 - k1) false ).
      rewrite !size_cat !size_nseq [k1 + _]addnC subnK 1?ltnW //.
      by rewrite addnC subnK // ltnW.
    rewrite !catA -catA rot_size_cat.
    exists (false, k2 - (i1 - j1 - k1) + j1, k1, (i1 - j1 - k1)).
    by rewrite nseqD !catA.
  rewrite rot_oversize.
    by exists (false, j1, k1, k2); rewrite !catA.
  rewrite !size_cat !size_nseq.
  by rewrite -!leq_subRL ltnW.
have -> : l = rotr x (nseq j1 false ++ nseq (k1 + j2) true ++ nseq k2 false).
  apply: (@rot_inj x); rewrite rotrK.
  rewrite -[LHS](cat_take_drop n1.+1) Hirot.
  by rewrite -[n1.+1]add1n -drop_drop Hdrot /= drop0 nseqD !catA.
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

Lemma half_cleaner_bool n (t : (n + n).-tuple bool) :
  (t : seq _) \is bitonic -> 
  let t1 := nfun (half_cleaner n) t in 
    ((ttake t1 == nseq n false :> seq bool) && 
    ((tdrop t1 : seq bool) \is bitonic))
  ||
    ((tdrop t1 == nseq n true :> seq bool) && 
    ((ttake t1 : seq bool) \is bitonic)).
Proof.
move=> /bitonic_boolP[[[[b i] j] k] tE] /=; set t1 := nfun _ _.
have nnE : n + n = i + j + k.
  by rewrite -(size_tuple t) tE !size_cat !size_nseq addnA.
have [iLn|nLi]:= leqP i n; last first.
  (*** 
         b b b b b b b
         b b~b~b b b b
    min  b b 0 0 b b b 
    max  b b 1 1 b b b
  ***)
  have nE : n = i - n + j + k.
    by rewrite -addnA addnBAC 1?ltnW // addnA -nnE addnK.
  have ttE : ttake t1 = nseq (i - n) b ++ nseq j false ++ nseq k b :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by rewrite size_tuple !size_cat !size_nseq addnA.
    rewrite size_tuple => uLn.
    rewrite /ttake /= val_tcast /= nth_take // /t1 nfun_half_cleaner /=.
    have uLi : u < i by apply: ltn_trans nLi.
    have uLnn : u < n + n by apply: leq_trans uLn (leq_addl _ _).
    rewrite (nth_map (Ordinal uLnn)) -1?enum_ord ?size_enum_ord //.
    have {2}->: u = (Ordinal uLnn) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by repeat (case: leqP => ?; try lia).
  have tdE : tdrop t1 = nseq (i - n) b ++ nseq j true ++ nseq k b :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by rewrite size_tuple !size_cat !size_nseq addnA.
    rewrite size_tuple => uLn.
    rewrite /tdrop /= val_tcast /= nth_drop // /t1 nfun_half_cleaner /=.
    have uLi : u < i by apply: ltn_trans nLi.
    have nuLnn : n + u < n + n by rewrite ltn_add2l.
    rewrite (nth_map (Ordinal nuLnn)) -1?enum_ord ?size_enum_ord //.
    have {2}->: n + u = (Ordinal nuLnn) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
      by have := ltn_ord u1; lia.
    have {}uE : u = u1 by rewrite -[u](addnK n) addnC uE addnC addnK.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by repeat (case: leqP => ?; try lia).
  case: b tE ttE tdE => tE ttE tdE.
    apply/orP; right.
    rewrite tdE -!nseqD addnBAC 1?ltnW // addnA -nnE addnK eqxx /=.
    by apply/bitonic_boolP; exists (true, i - n, j, k).
  apply/orP; left.
  rewrite ttE -!nseqD addnBAC 1?ltnW // addnA -nnE addnK eqxx /=.
  rewrite tdE.
  by apply/bitonic_boolP; exists (false, (i - n), j , k).
have [ijLn|nLij]:= leqP (i + j) n.
  (***  0 -> (i + j -n) -> (i - (i + j - n)) - j -> n - i
         b b b~b~b~b b
         b b b b b b b
    min  b b b 0 0 0 b 
    max  b b b 1 1 1 b
  ***)
  have nE : n = i + j + k - n by rewrite -nnE addnK.
  have ttE : ttake t1 = nseq i b ++ nseq j false
                             ++ nseq (n - (i + j)) b :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLn.
    rewrite /ttake /= val_tcast /= nth_take // /t1 nfun_half_cleaner /=.
    have uLnn : u < n + n by apply: leq_trans uLn (leq_addl _ _).
    rewrite (nth_map (Ordinal uLnn)) -1?enum_ord ?size_enum_ord //.
    have {2}->: u = (Ordinal uLnn) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by repeat (case: leqP => ?; try lia).
  have tdE : tdrop t1 = nseq i b ++ nseq j true
                             ++ nseq (n - (i + j)) b :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLn.
    rewrite /tdrop /= val_tcast /= nth_drop // /t1 nfun_half_cleaner /=.
    have uLnn : u < n + n by apply: leq_trans uLn (leq_addl _ _).
    have nuLnn : n + u < n + n by rewrite ltn_add2l.
    rewrite (nth_map (Ordinal nuLnn)) -1?enum_ord ?size_enum_ord //.
    have {2}->: n + u = (Ordinal nuLnn) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
      by move: (ltn_ord u1); lia.
    have {}uE : u = u1 by rewrite -[u](addnK n) addnC uE addnC addnK.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by repeat (case: leqP => ?; try lia).
  case: b tE ttE tdE => tE ttE tdE.
    apply/orP; right.
    rewrite tdE -!nseqD addnA addnC subnK // eqxx /=.
    by apply/bitonic_boolP; exists (true, i, j, n - (i + j)).
  apply/orP; left.
  rewrite ttE -!nseqD addnA addnC subnK // eqxx /=.
  rewrite tdE.
  by apply/bitonic_boolP; exists (false, i, j , n - (i + j)).
have nE : n = i + j + k - n by rewrite -nnE addnK.
have [jLn|nLj]:= leqP j n.
  (*** 
         b b b b b~b~b
        ~b~b b b b b b
    min  0 0 b b b 0 0 
    max  1 1 b b b 1 1
  ***)
  have ttE : ttake t1 = nseq (i + j - n) false ++ nseq (n - j) b
                             ++ nseq (n - i) false :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLn.
    rewrite /ttake /= val_tcast /= nth_take // /t1 nfun_half_cleaner /=.
    have uLnn : u < n + n by lia.
    rewrite (nth_map (Ordinal uLnn)) -1?enum_ord ?size_enum_ord //.
    have {2}->: u = (Ordinal uLnn) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by repeat (case: leqP => ?; try lia).
  have tdE : tdrop t1 = nseq (i + j - n) true ++ nseq (n - j) b
                             ++ nseq (n - i) true :> seq bool.
    apply: (@eq_from_nth _ false) => [|u].
      by rewrite size_tuple !size_cat !size_nseq; lia.
    rewrite size_tuple => uLn.
    rewrite /tdrop /= val_tcast /= nth_drop // /t1 nfun_half_cleaner /=.
    have uLnn : u < n + n by apply: leq_trans uLn (leq_addl _ _).
    have nuLnn : n + u < n + n by rewrite ltn_add2l.
    rewrite (nth_map (Ordinal nuLnn)) -1?enum_ord ?size_enum_ord //.
    have {2}->: n + u = (Ordinal nuLnn) :> nat by [].
    rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
      by move: (ltn_ord u1); lia.
    have {}uE : u = u1 by rewrite -[u](addnK n) addnC uE addnC addnK.
    rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
    by repeat (case: leqP => ?; try lia).
  case: b tE ttE tdE => tE ttE tdE.
    apply/orP; right.
    rewrite tdE -!nseqD; apply/andP; split; first by apply/eqP; congr nseq; lia.
    by apply/bitonic_boolP; exists (false, i + j - n, n - j, n - i).
  apply/orP; left.
  rewrite ttE -!nseqD; apply/andP; split; first by apply/eqP; congr nseq; lia.
  by apply/bitonic_boolP; exists (true, i + j - n, n - j , n - i).
(*** 
       b b~b~b~b~b~b
      ~b~b~b~b~b b b
  min  0 0~b~b~b 0 0 
  max  1 1~b~b~b 1 1
***)
have ttE : ttake t1 = nseq i false ++ nseq (j - n) (~~b)
                           ++ nseq k false :> seq bool.
  apply: (@eq_from_nth _ false) => [|u].
    by rewrite size_tuple !size_cat !size_nseq; lia.
  rewrite size_tuple => uLn.
  rewrite /ttake /= val_tcast /= nth_take // /t1 nfun_half_cleaner /=.
  have uLnn : u < n + n by lia.
  rewrite (nth_map (Ordinal uLnn)) -1?enum_ord ?size_enum_ord //.
  have {2}->: u = (Ordinal uLnn) :> nat by [].
  rewrite nth_ord_enum /=; case: splitP => /= u1 uE; last by lia.
  rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
  by repeat (case: leqP => ?; try lia).
have tdE : tdrop t1 = nseq i true ++ nseq (j -n) (~~ b)
                      ++ nseq k true :> seq bool.
  apply: (@eq_from_nth _ false) => [|u].
    by rewrite size_tuple !size_cat !size_nseq; lia.
  rewrite size_tuple => uLn.
  rewrite /tdrop /= val_tcast /= nth_drop // /t1 nfun_half_cleaner /=.
  have uLnn : u < n + n by apply: leq_trans uLn (leq_addl _ _).
  have nuLnn : n + u < n + n by rewrite ltn_add2l.
  rewrite (nth_map (Ordinal nuLnn)) -1?enum_ord ?size_enum_ord //.
  have {2}->: n + u = (Ordinal nuLnn) :> nat by [].
  rewrite nth_ord_enum /=; case: splitP => /= u1 uE.
    by move: (ltn_ord u1); lia.
  have {}uE : u = u1 by rewrite -[u](addnK n) addnC uE addnC addnK.
  rewrite !(tnth_nth false) /= tE !nth_cat !size_nseq !nth_nseq -uE.
  by repeat (case: leqP => ?; try lia).
case: b tE ttE tdE => tE ttE tdE.
  apply/orP; left.
  rewrite ttE -!nseqD; apply/andP; split; first by apply/eqP; congr nseq; lia.
  by apply/bitonic_boolP; exists (true, i, j - n, k).
apply/orP; right.
rewrite tdE -!nseqD; apply/andP; split; first by apply/eqP; congr nseq; lia.
by apply/bitonic_boolP; exists (false, i, j - n, k).
Qed.

