From mathcomp Require Import all_ssreflect perm algebra.zmodp.
From mathcomp Require Import zify.

Import Order POrderTheory TotalTheory.
Require Import more_tuple.

(******************************************************************************)
(*  Definition of some network sorting algorithms                             *)
(*                                                                            *)
(*       ttake t == take the left part of a (m + n).-tuple                    *)
(*       tdrop t == take the right part of a (m + n).-tuple                   *)
(*      tmap f t == apply f to the tuple t                                    *)
(*        trev t == get the reverse of a tuple                                *)
(*   connector m == a connector links independent pairs of wires              *)
(*  cmerge c1 c2 == do the merge of two connectors : if c1 is a m1 connector  *)
(*                  c2 a m2 connector, we get an (m1 + m2) connector          *)
(*     cswap i j == the connector that link the wire i and the wire j         *)
(*       cdup c  == duplicate a connector : if c is a m connector  we get an  *)
(*                 (m1 + m2) connector                                        *)
(*    cfun c t   == apply the connector c to some wire state t. States are    *)
(*                  represented as the tuple. If two wires i, j are linked,   *)
(*                  min(i,j) receives the minimal value, and max(i, j) the    *)
(*                  maximal one                                               *)
(*     ctransp c == the connector c is a transposition : cfun (cfun c t) = t  *)
(*   network m   == a network is a sequence of connectors for m wires         *)
(*    nempty m   == the empty network                                         *)
(* nmerge c1 c2  == do the merge of two networks with cat                     *)
(*      ndup c   == duplicate a network with cat                              *)
(* eomerge c1 c2 == do the merge of two networks with eocat                   *)
(*      eodup c   == duplicate a network with eocat                           *)
(*    nfun n t   == apply the network n to some wire state t                  *)
(*     ntransp n == the n is composed of transpositions only                  *)
(* n \is sorting == the network n is a sorting network, i.e it always returns *)
(*                  a sorted tuple                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Connector.

Definition involutiveb (A : finType) (f : {ffun A -> A}) := 
    [forall i, f (f i) == i].

Lemma involutiveP (A : finType) (f : {ffun A -> A}) : 
  reflect (involutive f) (involutiveb f).
Proof.
by apply: (iffP forallP) => [H x|H x]; [rewrite (eqP (H x)) | rewrite H].
Qed.

(* In connector c, a wire i is connected to the wire (clink c i) *)
(* A wire is not connected if clink c i = i                      *)

Record connector (m : nat):= connector_of {
  clink : {ffun 'I_m -> 'I_m};
  cfinv : [forall i, clink (clink i) == i]}.

Definition clink_merge m1 m2 (c1 : connector m1) (c2 : connector m2) :=
  [ffun i => match split i with 
             | inl x => lshift _ (clink c1 x)
             | inr x => rshift _ (clink c2 x)
             end].

Lemma clink_merge_proof m1 m2 (c1 : connector m1) (c2 : connector m2) :
  [forall i, (clink_merge c1 c2 (clink_merge c1 c2 i)) == i].
Proof.
apply/forallP=> i /=.
rewrite !ffunE; case: (splitP i) => [j iE|k iE]; apply/eqP/val_eqP/eqP=> /=.
  by rewrite split_lshift (eqP (forallP (cfinv c1) j)) iE.
by rewrite split_rshift (eqP (forallP (cfinv c2) k)).
Qed.

Definition cmerge m1 m2 (c1 : connector m1) (c2 : connector m2) := 
  connector_of (clink_merge_proof c1 c2).

Definition cdup m (c : connector m) := cmerge c c.

Definition clink_eomerge m (c1 : connector m) (c2 : connector m) :=
  [ffun i : 'I_(m + m) => 
    if odd i then olift (clink c2 (idiv2 i)) else elift (clink c1 (idiv2 i))].
  
Lemma clink_eomerge_proof m (c1 : connector m) (c2 : connector m) :
  [forall i, (clink_eomerge c1 c2 (clink_eomerge c1 c2 i)) == i].
Proof.
apply/forallP=> i /=.
rewrite !ffunE /=; have [iO|iE] := boolP (odd i).
  rewrite oliftK val_olift /= odd_double /= (eqP (forallP (cfinv c2) _)).
  by rewrite idiv2K_odd.
rewrite eliftK val_elift /= odd_double /= (eqP (forallP (cfinv c1) _)).
by rewrite idiv2K_even.
Qed.

Definition ceomerge m (c1 : connector m) (c2 : connector m) := 
  connector_of (clink_eomerge_proof c1 c2).

Definition ceodup m (c : connector m) := ceomerge c c.

End Connector.

Section Network.

Variable m : nat.

(* Representing a network as a sequence of connectors *)
Definition network := seq (connector m).

(* Empty network *)
Definition nempty : network := [::].

Variable d : unit.
Variable A : orderType d.

Implicit Types t : m.-tuple A.
Implicit Types c : connector m.
Implicit Types n : network.

(* Applying a connector to a tuple *)
Definition cfun c t :=
    [tuple if i <= clink c i 
           then min (tnth t i) (tnth t (clink c i))
           else max (tnth t i) (tnth t (clink c i)) | i < m].

Lemma cswap_proof (i j : 'I_m) :
  let clink := [ffun x => if x == i then j else 
                          if x == j then i else x]  in
                          [forall i, clink (clink i) == i].
Proof.
apply/forallP => /= x.
rewrite !ffunE; case: (x =P i) => [->|/eqP xDi]; rewrite ?eqxx.
  by case: (j =P i) => [->|] //.
by case: (x =P j) => [->|/eqP xDj]; rewrite ?(negPf xDi, negPf xDj) !eqxx.
Qed.

(* A connector that swaps the value of two wire i1 i2 *)
Definition cswap i j := connector_of (cswap_proof i j).

Lemma cswapE_neq t i j k : 
  k != i -> k != j ->  tnth (cfun (cswap i j) t) k = tnth t k.
Proof.
move=> kDi kDj.
rewrite tnth_map !ffunE tnth_ord_tuple.
by rewrite (negPf kDi) (negPf kDj) leqnn minxx.
Qed.

Lemma cswapE_min t (i j : 'I_m) :
  i <= j -> tnth (cfun (cswap i j) t) i = min (tnth t i) (tnth t j).
Proof. by move=> iLj; rewrite tnth_map !ffunE tnth_ord_tuple eqxx iLj. Qed.

Lemma cswapE_max t (i j : 'I_m) :
  i <= j -> tnth (cfun (cswap i j) t) j = max (tnth t i) (tnth t j).
Proof. 
move=> iLj; rewrite tnth_map !ffunE tnth_ord_tuple eqxx.
case: (j =P i) => [->|/val_eqP /= jDi]; first by rewrite leqnn minxx maxxx.
by rewrite leq_eqVlt (negPf jDi) /= ltnNge iLj //= maxC.
Qed.

Lemma cswapC i j : cfun (cswap i j) =1 cfun (cswap j i).
Proof.
move=> t; apply: eq_from_tnth => k.
rewrite !tnth_map !ffunE tnth_ord_tuple.
case: (k =P i) => [->|/eqP kDi]; first by case: (i =P j) => [->|].
by case: (k =P j) => [->|/eqP kDj].
Qed.

Lemma perm_cfun c t : perm_eq (cfun c t) t.
Proof.
apply/tuple_permP.
pose cfunS c t :=
    [fun i =>
           if (i : 'I_m) <= clink c i 
           then if (tnth t i <= tnth t (clink c i))%O then i else (clink c i)
           else if (tnth t (clink c i) <= tnth t i)%O then i else (clink c i)].
have cI : involutive (cfunS c t).
  move=> i /=.
  have cIE x :  clink c (clink c x) = x by have /forallP/(_ x)/eqP := cfinv c.
  case: (leqP i) => [iLc|cLi].
    case: (leP (tnth t i)) => [tiLtc|tcLti]; first by rewrite iLc tiLtc.
    rewrite cIE (ltW tcLti); case: leqP => [|cLi].
      by case: ltngtP iLc => // *; apply/val_eqP/eqP.
    by rewrite leNgt tcLti.
  case: (leP _ (tnth t i)) => [tcLti|tiLtc].
    by rewrite (leqNgt i) cLi /= tcLti.
  by rewrite cIE ltnW // leNgt tiLtc.
exists (perm (inv_inj cI)).
apply/eqP/val_eqP; apply: eq_from_tnth => i.
rewrite !tnth_map tnth_ord_tuple /= permE /=.
by case: leqP => iLc; case: leP.
Qed.

(* turn a network into a function *)
Definition nfun n t := foldl (fun t c => cfun c t) t n.

Lemma nfunE n c t : nfun (c :: n) t = nfun n (cfun c t).
Proof. by []. Qed.

Lemma nfun_cat n1 n2 t : nfun (n1 ++ n2) t = nfun n2 (nfun n1 t).
Proof. by elim: n1 t => /=. Qed.

Lemma nfun_rcons n c t : nfun (rcons n c) t = cfun c (nfun n t).
Proof. exact: foldl_rcons. Qed.

Lemma perm_nfun n t : perm_eq (nfun n t) t.
Proof.
elim: n t => //= p n IH t.
by apply: perm_trans (IH _) (perm_cfun _ _).
Qed.

Lemma fun_of_network_empty : nfun nempty =1 id.
Proof. by []. Qed.

Lemma cfun_const (a : A) c : cfun c [tuple of nseq m a] = [tuple of nseq m a].
Proof.
apply: eq_from_tnth => /= i.
by rewrite tnth_map /= !(tnth_nth a) /= !nth_nseq !if_same maxxx.
Qed.

Lemma nfun_const (a : A) n : nfun n [tuple of nseq m a] = [tuple of nseq m a].
Proof. by elim: n => //= n p IH; rewrite cfun_const IH. Qed.

End Network.

Section Merge.

Variable m : nat.
Variable d : unit.
Variable A : orderType d.

Implicit Types t : m.-tuple A.
Implicit Types c : connector m.
Implicit Types n : network m.

Lemma cfun_merge m1 m2 (c1 : connector m1) (c2 : connector m2) 
                        (t : (m1 + m2).-tuple A) : 
  cfun (cmerge c1 c2) t = [tuple of cfun c1 (ttake t) ++ cfun c2 (tdrop t)].
Proof.
apply: eq_from_tnth => i.
pose a := tnth t i.
rewrite /= !(tnth_nth a) /= ?nth_cat !(nth_map i) /=; last 2 first.
- by rewrite -fintype.enumT -enum_ord size_enum_ord.
- by rewrite -enum_ord size_enum_ord.
set u := nth i _ _; have -> : u = i.
  by apply/val_eqP; rewrite /= /u -fintype.enumT -enum_ord /= nth_enum_ord.
rewrite {u}size_map -enum_ord size_enum_ord.
rewrite /= !(tnth_nth a) !ffunE /=; case: splitP => /= [j iE|k iE]; rewrite iE.
  rewrite (nth_map j) /=; last by rewrite size_enum_ord.
  set u := nth j _ _; have -> : u = j.
    by apply/val_eqP; rewrite /= /u nth_enum_ord.
  by rewrite !(tnth_nth a) /= ttakeE !nth_take.
rewrite leq_add2l addKn (nth_map k) /=; last first.
  by rewrite  -enum_ord  size_enum_ord.
set u := nth k _ _; have -> : u = k.
  by apply/val_eqP; rewrite /= /u -enum_ord nth_enum_ord.
by rewrite !(tnth_nth a) /= tdropE !nth_drop.
Qed.

Lemma cfun_dup (c : connector m) (t : (m + m).-tuple A) :
  cfun (cdup c) t = [tuple of cfun c (ttake t) ++ cfun c (tdrop t)].
Proof. by apply: cfun_merge. Qed.

Definition nmerge m1 m2 (n1 : network m1) (n2 : network m2) := 
    [seq cmerge i.1 i.2 | i <- zip n1 n2].

Definition ndup m (n : network m) : network (m + m) := nmerge n n.

Lemma nfun_dup (n : network m) (t : (m + m).-tuple A) : 
  nfun (ndup n) t = [tuple of nfun n (ttake t) ++ nfun n (tdrop t)].
Proof.
elim: n t => /= [t|c n IH t]; first by apply: cat_ttake_tdrop.
by rewrite IH !cfun_dup ttakeK tdropK.
Qed.

End Merge.

Section TMap.

Variable m : nat.
Variable d1 d2 : unit.
Variable A : orderType d1.
Variable B : orderType d2.
Variable f : A -> B.

Lemma tmap_connector (c : connector m) : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} ->
  {morph tmap f : t / cfun c t >-> cfun c t}.
Proof.
move=> Hm t ; apply: eq_from_tnth => i.
rewrite /cfun !tnth_map !tnth_ord_tuple -(min_homo Hm) -(max_homo Hm).
by case: leqP.
Qed.

Lemma tmap_network (n : network m) : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} ->
  {morph tmap f : t / nfun n t >-> nfun n t}.
Proof.
by move=> Hm t; elim: n t => //= a n IH t; rewrite -tmap_connector // IH.
Qed.

End TMap.

Section Sorting.

Variable m : nat.
Variable d : unit.
Variable A : orderType d.

(* Decided sorting using boolean (we use the 0-1 theorem for the def) *)
Definition sorting :=
  [qualify n | [forall r : m.-tuple bool, sorted <=%O (nfun n r)]].

Lemma sorted_sorting n (x1 x2 : A) : 
  x1 != x2 -> (forall t : m.-tupleA, sorted <=%O (nfun n t)) -> n \is sorting.
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
by rewrite -tmap_network // val_tmap (homo_sorted gM _ _).
Qed.

Lemma sorting_sorted n (t : m.-tuple A) :
  n \is sorting -> sorted <=%O (nfun n t).
Proof.
apply: contraLR => /sortedPn[[[x1 x2]][s1 s2] /= nfunE x2Lx1].
rewrite negb_forall.
pose g x := if (x <= x2)%O then false else true.
have gM : {homo g : x y / (x <= y)%O >-> (x <= y)%O}.
  move=> i j; rewrite /g.
  case: (leP i x2); case: (leP j x2) => // jLx2 x2Li.
  by rewrite leNgt (le_lt_trans jLx2).
apply/existsP; exists (tmap g t).
apply/sortedPn; exists ((g x1, g x2), (map g s1, map g s2)) => /=.
  by rewrite -tmap_network // val_tmap nfunE map_cat.
by rewrite /g lexx leNgt x2Lx1.
Qed.

End Sorting.

Arguments sorting{m}.

Lemma sorting1 (n : network 1) : n \is sorting.
Proof. by apply/forallP => /= t; case: nfun => /= [] [] // a []. Qed.

Section Transposition.

Definition ctransp {m} (c : connector m) := 
  [forall i, (clink c i != i) ==>
            ((clink c i == i.+1 :> nat) || (clink c i == i.-1 :> nat))]. 

Lemma ctranspP {m} (c : connector m) :
  reflect 
    (forall i, (clink c i != i) ->
            ((clink c i = i.+1 :> nat) \/ (clink c i = i.-1 :> nat)))
    (ctransp c).
Proof.
apply: (iffP forallP) => H i; have := H i.
  by case: eqP => //= _ /orP[] /eqP-> _; [left | right].
by case: eqP => //= _ [] // ->; rewrite eqxx // orbT.
Qed.

Definition ntransp m (n : network m) := all ctransp n.

End Transposition.

Section LeqC.

Variable d : unit.
Variable A : orderType d.

Lemma leqt_cfun m (c : connector m) : 
  ctransp c -> {homo (cfun c : m.-tuple A -> m.-tuple A)  : i j / leqt i j}.
Proof.
(* This proof is slightly more complicate in our setting because 
   a connector can contain simultaneous transposition *)
move=> /ctranspP cT t1 t2 /leqtP t1Lt2; apply/leqtP => a b.
rewrite leq_eqVlt => /orP[/val_eqP<-//|aLb].
have b_gt0 : 0 < b by case: (nat_of_ord b) aLb.
have aLLb : a <= b by apply: ltnW.
rewrite !tnth_map !tnth_ord_tuple //.
have [->|/eqP cD] := clink c a =P a; last case: (cT _ cD) => cE.
- rewrite leqnn !minxx.
  have [->|/eqP /cT[] cE] := clink c b =P b.
  - by rewrite leqnn !minxx; apply/t1Lt2.
  - rewrite cE leqnSn.
    have aLc : a <= clink c b by rewrite cE -ltnS (leq_trans aLb) // ltnW.
    case: (ltP (tnth t1 b)) => C1.
      rewrite min_l; first by apply/t1Lt2/ltnW.
      apply/t1Lt2; last by apply: ltW.
      by rewrite cE leqnSn.
    move=> t1aLt1c.
    rewrite le_minr !t1Lt2 => //; try by apply: ltnW.
    by apply: le_trans C1.
  have cLb : clink c b < b.
    by rewrite cE /=; case: (nat_of_ord b) aLb.
  have aLc : a <= clink c b.
    by rewrite -ltnS cE prednK.
  rewrite (leqNgt b) cLb /=.
  case: (ltP (tnth t1 b)) => C1.
    by rewrite le_maxr=>/(t1Lt2 _ _ aLc) ->; rewrite orbT.
  by rewrite le_maxr=>/(t1Lt2 _ _ (ltnW aLb)) ->.
- rewrite cE leqnSn /=.
  have [->|/eqP /cT[] c1E] := clink c b =P b.
  - rewrite leqnn !minxx.
    case: (ltP (tnth t1 a)); rewrite le_minl.
      by move=> _ /t1Lt2-> //; apply: ltnW.
    move=> _ /t1Lt2-> //; first by rewrite orbT.
    by rewrite cE.
  - rewrite c1E leqnSn.
    case: (ltP (tnth t1 a)); rewrite !le_minr.
      move=> t1aLt1c; rewrite min_l.
        move/andP => [] /t1Lt2-> // /t1Lt2 -> //.
        by rewrite c1E (leq_trans aLLb).
      apply: t1Lt2; first by rewrite cE.
      by apply: ltW.
    rewrite !le_minl => H /andP[] /t1Lt2 -> //; last by rewrite cE.
    move=> /t1Lt2 ->; rewrite ?orbT //.
    by rewrite cE c1E ltnS.
  have /negPf-> : ~~ (b <= clink c b).
    by rewrite c1E; case: (nat_of_ord b) aLb => //= n; rewrite ltnn.
  have [<-|/eqP aD] := a =P clink c b.
    by rewrite !(le_minl, le_maxr) !lexx !orbT.
  have aLb1 : a <= b.-1 by 
    by rewrite -ltnS prednK //; case: (nat_of_ord b) aLb.
  rewrite !(le_minl, le_maxr) -orbA => /or4P[] /t1Lt2->//; 
      rewrite ?(orbT, cE, c1E) //.  
  by rewrite ltn_neqAle -c1E aD c1E.
rewrite leqNgt ltn_neqAle cD cE leq_pred /=.
have [->|/eqP /cT[] c1E] := clink c b =P b.
- rewrite leqnn !minxx.
  case: (ltP (tnth t1 a)); rewrite le_maxl.
    move=> t1aLt1c t1cLtb; rewrite !t1Lt2 //.
      by rewrite cE (leq_trans (leq_pred _)).
    by apply: le_trans (ltW t1aLt1c) _.
  move=> t1aLt1c t1cLtb.
  have t2aLt2b : (tnth t2 a <= tnth t2 b)%O by apply: t1Lt2.
  rewrite t2aLt2b (le_trans _ t2aLt2b) // t1Lt2 //.
  by rewrite cE leq_pred.
- rewrite c1E leqnSn !le_maxl !le_minr -!andbA => 
     /and4P[t1aLtb t1aLt1c t1cLtb t1cLt1c].
  by rewrite !t1Lt2 ?(cE, c1E, (leq_trans (leq_pred _))) // ltnW.
have /negPf-> : ~~ (b <= clink c b).
  by rewrite c1E; case: (nat_of_ord b) aLb => //= n; rewrite ltnn.
rewrite !(le_maxl, le_maxr) => /andP[] /orP[] /t1Lt2-> //=; last first.
- by rewrite c1E -ltnS prednK.
- rewrite !orbT /=; case/orP => /t1Lt2-> //; rewrite ?orbT //.
    by rewrite cE (leq_trans (leq_pred _)).
  by rewrite cE c1E (leq_trans (leq_pred _)) // -ltnS prednK.
case/orP => /t1Lt2-> //; rewrite ?orbT //.
  by rewrite cE (leq_trans (leq_pred _)).
rewrite cE c1E -ltnS !prednK //.
move/eqP/val_eqP: cD => /=.
by rewrite /= cE; case: nat_of_ord.
Qed.

Lemma leqt_nfun m (n : network m) : 
  ntransp n -> {homo (nfun n : m.-tuple A -> m.-tuple A) : i j / leqt i j}.
Proof.
elim: n => /= [_| c n IH /andP[cT nT]] t1 t2 t1Lt2 //=.
by apply: IH => //; apply: leqt_cfun.
Qed.

Lemma leqt_nsorted m (x1 x2 : A) (t : m.-tuple A) (n : network m) : 
  x1 != x2 -> ntransp n -> 
  sorted (>%O) t -> sorted (<=%O) (nfun n t) -> n \is sorting.
Proof.
move=> x1Dx2 nT tS tS1; apply: sorted_sorting x1Dx2 _ => t1.
suff : forall a b,
   a <= b < size (nfun n t1) ->
  (nth x1 (nfun n t1) a <= nth x1 (nfun n t1) b)%O.
  elim: tval => // y1 [|y2 l] // IH H.
  rewrite /= (H 0 1) //=.
  apply: IH => a b /= /andP[aLb bLs].
  by apply: (H a.+1 b.+1); rewrite /= !ltnS //= aLb -ltnS.
rewrite size_tuple => a b /andP[aLb bLs].
have aLs : a < m by apply: leq_ltn_trans aLb _.
pose a1 := Ordinal aLs; pose b1 := Ordinal bLs.
have /leqtP/(_ a1 b1 aLb) : leqt (nfun n t) (nfun n t1).
  apply: leqt_nfun => //.
  by apply: leqt_sorted.
rewrite !(tnth_nth x1); apply.
by apply: (sorted_leq_nth le_trans le_refl x1 tS1); rewrite ?(inE, size_tuple).
Qed.

End LeqC.

Section EOMerge.

Variable m : nat.
Variable d : unit.
Variable A : orderType d.

Implicit Types t : m.-tuple A.
Implicit Types c : connector m.
Implicit Types n : network m.

Lemma cfun_eomerge (c1 : connector m) (c2 : connector m) 
                   (t : (m + m).-tuple A) : 
  cfun (ceomerge c1 c2) t = teocat (cfun c1 (tetake t)) (cfun c2 (totake t)).
Proof.
apply: eq_from_tnth => i.
have iLm : i < m + m by apply: ltn_ord.
have i2Lm : i./2 < m by have := ltn_ord (idiv2 i); rewrite val_idiv2.
pose a := tnth t i.
rewrite /= !(tnth_nth a) /= ?nth_cat !(nth_map i) /=; last 2 first.
- by rewrite -fintype.enumT -enum_ord size_enum_ord.
- by rewrite -enum_ord size_enum_ord.
set u := nth i _ _; have -> : u = i.
  by apply/val_eqP; rewrite /= /u -fintype.enumT -enum_ord /= nth_enum_ord.
rewrite !ffunE {u}nth_eocat; last by rewrite !size_map.
have [iO|iE] := boolP (odd i).
  rewrite !(nth_map (idiv2 i)); last 2 first.
  - by rewrite -fintype.enumT -enum_ord size_enum_ord.
  - by rewrite -enum_ord size_enum_ord.
  set u := nth _ _ _; have -> : u = idiv2 i.
    apply/val_eqP; rewrite /= /u.
    by rewrite -fintype.enumT -enum_ord /= !nth_enum_ord ?val_idiv2.
  rewrite !(tnth_nth a) /= !nth_otake /= val_olift /= val_idiv2.
  have F : i = i./2.*2.+1 :> nat by rewrite -[LHS]odd_double_half iO.
  by rewrite -F {1}F ltnS leq_double.
rewrite !(nth_map (idiv2 i)); last 2 first.
- by rewrite -fintype.enumT -enum_ord size_enum_ord.
- by rewrite -enum_ord size_enum_ord.
set u := nth _ _ _; have -> : u = idiv2 i.
  apply/val_eqP; rewrite /= /u.
  by rewrite -fintype.enumT -enum_ord /= !nth_enum_ord ?val_idiv2.
rewrite !(tnth_nth a) /= !nth_etake /= val_elift /= val_idiv2.
have F : i = i./2.*2 :> nat by rewrite -[LHS]odd_double_half (negPf iE).
by rewrite -F {1}F leq_double.
Qed.

Lemma cfun_eodup (c : connector m) (t : (m + m).-tuple A) :
  cfun (ceodup c) t = teocat (cfun c (tetake t)) (cfun c (totake t)).
Proof. by apply: cfun_eomerge. Qed.

Definition neomerge m (n1 : network m) (n2 : network m) := 
    [seq ceomerge i.1 i.2 | i <- zip n1 n2].

Definition neodup m (n : network m) : network (m + m) := neomerge n n.

Lemma nfun_eodup (n : network m) (t : (m + m).-tuple A) : 
  nfun (neodup n) t = teocat (nfun n (tetake t)) (nfun n (totake t)).
Proof.
elim: n t => /= [t|c n IH t]; first by rewrite -eocat_tetake_totake.
by rewrite IH !cfun_eodup tetakeK totakeK.
Qed.

End EOMerge.

Section OddJump.

Variable d : unit.
Variable A : orderType d.

Definition clink_odd_jump m k : {ffun 'I_m -> 'I_m} :=
  if odd k then 
    [ffun i : 'I_ _ => if odd i then iadd k i else isub k i]
  else [ffun i => i].

Lemma clink_odd_jump_proof m k : 
  [forall i : 'I_m, clink_odd_jump _ k (clink_odd_jump _ k i) == i].
Proof.
rewrite /clink_odd_jump.
have [/= kO|kI] := boolP (odd k);
     apply/forallP => i /=; apply/eqP/val_eqP; rewrite !ffunE //.
have m_gt0 : 0 < m by apply: leq_ltn_trans (ltn_ord i).
have [/= iO|iE] := boolP (odd i); rewrite ?(val_iadd, val_isub) /=.
  case: ltnP => [kiLm|mLki]; last first.
    by rewrite iO !val_iadd [k + i < m]ltnNge mLki /= [k + i < m]ltnNge mLki.
  by rewrite oddD iO kO /= ?(val_iadd, val_isub) /= kiLm leq_addr addnC addnK.
case: leqP => [kLi|iLk]; last first.
  by rewrite (negPf iE) !val_isub [k <= i]leqNgt iLk /= [k <= i]leqNgt iLk.
rewrite oddB // (negPf iE) kO /= ?(val_iadd, val_isub) /= kLi.
by rewrite addnC subnK // ifT.
Qed.
  
Definition codd_jump {m} k := connector_of (clink_odd_jump_proof m k).

Lemma cfun_odd_jump n k (t : n.-tuple A) : 
  odd k ->
  cfun (codd_jump k) t = 
  [tuple
    if odd i then min (tnth t i) (tnth t (iadd k i))
    else max (tnth t i) (tnth t (isub k i)) | i < n].
Proof.
move=> kO; apply: eq_from_tnth => i /=.
rewrite /codd_jump /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple.
rewrite /clink_odd_jump kO ffunE.
have [iO|iE] := boolP (odd i).
  by rewrite ifT // val_iadd; case: ltnP => // *; apply: leq_addl.
rewrite val_isub; case: (leqP k) => [kLi|iLk]; last first.
  suff -> : isub k i = i by rewrite minxx maxxx if_same.
  by apply/val_eqP; rewrite /= val_isub leqNgt iLk.
rewrite ifN // -ltnNge ltn_subLR //.
by case: (k) kO => // k1 _; rewrite addSn ltnS leq_addl.
Qed.

End OddJump.

Lemma sorted_odd_jump m (t : (m + m).-tuple bool) i k :
  odd k -> i <= (uphalf k).*2 ->
  sorted <=%O (tetake t) -> sorted <=%O (totake t) -> 
  noF (tetake t) = noF (totake t) + i ->
  let j := i - uphalf k in  
  let t1 := cfun (codd_jump k) t in
  [/\ sorted <=%O (tetake t1), 
      sorted <=%O (totake t1) & 
      noF (tetake t1) = noF (totake t1) + (i - j.*2)].
Proof.
rewrite !isorted_noFT.
set a := noF (totake t); set b := noT (tetake t) => 
         kO iL2k /eqP teE /eqP toE nt1E j t1.
rewrite nt1E in teE.
have ntoE : noT (totake t) = b + i.
  apply: (@addnI a);rewrite size_noFT.
  by rewrite size_tuple -(size_tuple (tetake t)) teE size_cat 
             !size_nseq addnAC addnA.
rewrite ntoE in toE.
have jLi : j <= i by apply: leq_subr.
have aibC : a + i + b = a + (b + i) by rewrite [b + _]addnC addnA.
have aibE : a + i + b = m by rewrite aibC -ntoE size_noFT size_tuple.
have aijbjE : a + i - j + (b + j) = m.
  by rewrite [b + j]addnC -addnBA // addnA -[_ + j]addnA subnK.
have ajbijE : a + j + (b + i - j) = m.
  by rewrite addnAC -addnA subnK ?(leq_trans _ (leq_addl _ _)) // -aibC.
suff t1E : t1 = eocat (nseq (a + i - j) false ++ nseq (b + j) true)
                      (nseq (a + j) false ++ nseq (b + i - j) true) :> seq _.
  rewrite tetakeE totakeE t1E otakeK ?etakeK.
    rewrite !isorted_noFT !noE !eqxx /= -addnn subnDA addnAC.
    rewrite -addnA subnK; first by rewrite -addnBA //.
    have [|k2Li] := leqP i (uphalf k); first by rewrite /j -subn_eq0 => /eqP->.
    by rewrite subKn ?leq_subLR ?addnn // ltnW.
  by rewrite !(size_cat, size_nseq) ajbijE.
apply: (@eq_from_nth _ true) => [|v].
  by rewrite /= [LHS]size_tuple card_ord size_eocat size_cat !size_nseq aijbjE.
rewrite [X in _ < X -> _]size_tuple => iLab.
pose x := Ordinal iLab.
rewrite /t1 cfun_odd_jump //= (nth_map x) /= -[v]/(x : nat); last first.
  by rewrite -enum_ord size_enum_ord.
rewrite -enum_ord !nth_ord_enum.
rewrite nth_eocat; last first.
  by rewrite !size_cat !size_nseq aijbjE.
rewrite !(tnth_nth true) [t]eocat_tetake_totake /=.
rewrite !nth_eocat /=; try by rewrite !size_tuple.
have v2Lab : v./2 < a + i + b.
  by rewrite ltn_halfl -addnn -nt1E size_noFT size_tuple.
have [vO|vE] := boolP (odd _).
  rewrite !nth_cat_seqT.
  have i_gt0 : 0 < v by case: (v) vO.
  rewrite val_iadd /=.
  case: leqP => [kvLaib|aibLc].
    rewrite vO toE nth_cat_seqT minxx.
    case: leqP => [aLv2|v2La]; last first.
      by rewrite leqNgt (leq_trans v2La (leq_addr _ _)).
    rewrite geq_halfr -addnn.
    case: (leqP (uphalf k) i) => [k2Li|iLk2].
      have i2E : i.*2 = j.*2 + k.+1.
        rewrite doubleB - [X in _ + X]odd_double_half oddS kO subnK //.
        by rewrite leq_double.
      rewrite -(leq_add2l k.+1) addnn addnC doubleD -addnA -i2E -doubleD.
      rewrite (leq_trans (leq_addr b.*2 _)) // -doubleD -addnn.
      by rewrite aibE (leq_trans kvLaib) // leq_add2r.
    have -> : j = 0 by apply/eqP; rewrite subn_eq0 ltnW.
    by rewrite addn0 addnn -geq_halfr.
  rewrite oddD kO vO /= teE toE !nth_cat_seqT.
  case: leqP => [aLv2|v2La]; last first.
    by rewrite minFb leqNgt (leq_trans v2La (leq_addr _ _)).
  rewrite minTb.
  case: (leqP i (uphalf k)) => [iLk2|k2Li].
    have /eqP jE0 : j == 0 by rewrite subn_eq0.
    rewrite jE0 addn0 aLv2 /=.
    have -> : (k + v)./2 = (k.+1 + v)./2.
      by rewrite addSn -uphalfE uphalf_half oddD kO vO.
    by rewrite geq_halfr addnC doubleD leq_add // -geq_halfr.
  have j_gt0 : 0 < j by rewrite subn_gt0.
  case: leqP => H1.
    rewrite geq_halfr in H1.
      rewrite geq_halfr doubleD doubleB addnBA.
      rewrite leq_subLR -doubleD (leq_trans H1) // leq_add2r.
      by rewrite -ltnS -[X in X <= _]odd_double_half oddS kO.
    by rewrite leq_double ltnW // -subn_gt0.
  rewrite halfD kO vO addnA /= in H1.
  rewrite addnBA //; last by apply : ltnW.
  by rewrite leq_subLR uphalf_half kO leqNgt H1.
rewrite val_isub /=.
case: leqP => [kLv|vLk].
  rewrite oddB // (negPf vE) /= kO teE toE !nth_cat_seqT.
  case: (leqP i (uphalf k)) => [iLk2|k2Li].
    have /eqP jE0 : j == 0 by rewrite subn_eq0.
    rewrite jE0 subn0.
    case: leqP => [aiLv2|v2Lai]; first by rewrite maxTb.
    rewrite maxFb; apply/idP/negP; rewrite -ltnNge -(ltn_add2r i).
    rewrite (leq_ltn_trans _ v2Lai) //.
    rewrite -{2}(subnK kLv) halfD oddB // kO (negPf vE) /=.
    by rewrite addnCA leq_add2l -[1]/(true : nat) -kO -uphalf_half.
  have j_gt0 : 0 < j by rewrite subn_gt0.
  case: (leqP (a + i - j) v./2) => [aijLv2|v2Laij]; last first.
    rewrite leqNgt (leq_trans v2Laij (leq_subr _ _)) maxFb.
    rewrite leqNgt -(ltn_add2r (uphalf k)) {1}uphalf_half kO addnCA /=.
    rewrite -(subnK kLv) // halfD oddB // kO (negPf vE) /= in v2Laij.
    by rewrite (leq_trans v2Laij) // -addnBA // leq_add2l subKn // ltnW.
  rewrite -addnBA //subKn in aijLv2; last by apply: ltnW.
  rewrite -(subnK kLv) // halfD oddB // kO (negPf vE) /= in aijLv2.
  rewrite addnCA -[1]/(true : nat) -kO -uphalf_half leq_add2r in aijLv2.
  by rewrite aijLv2 maxbT.
rewrite (negPf vE) maxxx teE !nth_cat_seqT.
case: (leqP i (uphalf k)) => [iLk2|k2Li].
  have /eqP-> : j == 0 by rewrite subn_eq0.
  by rewrite subn0.
have j_gt0 : 0 < j by rewrite subn_gt0.
  rewrite -addnBA // subKn; last by apply: ltnW.
case: leqP => [aiLv2|v2Lai].
  by rewrite (leq_trans _ aiLv2) // leq_add2l ltnW.
rewrite leqNgt ltn_halfl (leq_trans vLk) // doubleD.
rewrite (leq_trans _ (leq_addl _ _)) //.
by rewrite -[X in X <= _]odd_double_half uphalf_half kO doubleD !addSn.
Qed.


