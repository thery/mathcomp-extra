From mathcomp Require Import all_ssreflect perm.
From mathcomp Require Import zify.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of some network sorting algorithms                             *)
(*                                                                            *)
(*          e2 m == 2 ^ n so that e2 m.+1 = e2 m + e2 m is true by reduction  *)
(*       ttake t == take the left part of a (m + n).-tuple                    *)
(*       tdrop t == take the right part of a (m + n).-tuple                   *)
(*      tmap f t == apply f to the tuple t                                    *)
(*        trev t == get the reverse of a tuple                                *)
(* l \is bitonic == a sequence is bitonic if one of its rotation is increasing*)
(*                  then decreasing                                           *)
(*   connector m == a connector links independent pairs of wires              *)
(*  cmerge c1 c2 == do the merge of two connectors : if c1 is a m1 connector  *)
(*                  c2 a m2 connector, we get an (m1 + m2) connector          *)
(*     cswap i j == the connector that link the wire i and the wire j         *)
(*       cdup c  == duplicate a connector : if c is a m connector  we get an  *)
(*                 (m1 + m2) connector                                        *)
(*  half_cleaner == an (m + m) connector where wire i is linked to wire i + m *)
(* rhalf_cleaner == an m connector where wire i is linked to wire m - i       *)
(*    cfun c t   == apply the connector c to some wire state t. States are    *)
(*                  represented as the tuple. If two wires i, j are linked,   *)
(*                  min(i,j) receives the minimal value, and max(i, j) the    *)
(*                  maximal one                                               *)
(*   network m   == a network is a sequence of connectors for m wires         *)
(*    nempty m   == the empty network                                         *)
(* nmerge c1 c2  == do the merge of two networks                              *)
(*      ndup c   == duplicate a network                                       *)
(*    nfun n t   == apply the network n to some wire state t                  *)
(*   rhalf_cleaner_rec m                                                      *)
(*               == the (e2 m) network composed of the recursive duplication  *)
(*                  of an half_cleaner                                        *)
(*   rhalf_cleaner_rec m                                                      *)
(*               == the (e2 m) network composed of a rhalf_cleaner and then   *)
(*                  the duplication of a half_cleaner_rec                     *)
(*       bsort m == the (e2 m) network that implements the bitonic sort       *)
(* n \is sorting == the network n is a sorting network, i.e it always returns *)
(*                  a sorted tuple                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section E2.

(* We define an explicte function e2 n = 2 ^ n so that e2 n.+1 reduces        *)
(* to e2 m + e2 m                                                             *)

Fixpoint e2 m := if m is m1.+1 then e2 m1 + e2 m1 else 1.

Lemma e2E m : e2 m = 2 ^ m.
Proof. by elim: m => //= m ->; rewrite expnS mul2n addnn. Qed. 

Lemma e2S m : e2 m.+1 = e2 m + e2 m.
Proof. by []. Qed.

End E2.

Section Tuple.

Lemma ttake_proof m1 m2 : minn m1 (m1 + m2) = m1.
Proof. by rewrite minnC minnE [m1 + m2]addnC addnK [m2 + m1]addnC addnK. Qed.

Lemma tdrop_proof m1 m2 : (m1 + m2) - m1 = m2.
Proof. by rewrite addnC addnK. Qed.

Variable A : eqType.

Definition ttake (m1 m2 : nat) (t : (m1 + m2).-tuple A) :=
  tcast (ttake_proof m1 m2) [tuple of take m1 t].

Lemma ttakeE (m1 m2 : nat) (t : (m1 + m2).-tuple A) : 
  ttake t = take m1 t :> seq A.
Proof. by rewrite val_tcast. Qed.

Lemma ttakeK (m1 m2 : nat) (t1 : m1.-tuple A) (t2 : m2.-tuple A) : 
  ttake [tuple of t1 ++ t2] = t1.
Proof.
apply/val_eqP => /=.
by rewrite ttakeE take_cat size_tuple ltnn subnn /= take0 cats0.
Qed.

Definition tdrop (m1 m2 : nat) (t : (m1 + m2).-tuple A) :=
  tcast (tdrop_proof m1 m2) [tuple of drop m1 t].

Lemma tdropE (m1 m2 : nat) (t : (m1 + m2).-tuple A) : 
  tdrop t = drop m1 t :> seq A.
Proof. by rewrite val_tcast. Qed.

Lemma tdropK (m1 m2 : nat) (t1 : m1.-tuple A) (t2 : m2.-tuple A) : 
  tdrop [tuple of t1 ++ t2] = t2.
Proof.
apply/val_eqP => /=.
by rewrite tdropE drop_cat size_tuple ltnn subnn /= drop0.
Qed.

Lemma cat_ttake_tdrop n (t : (n + n).-tuple A) : 
  t = [tuple of ttake t ++ tdrop t].
Proof. by apply/val_eqP; rewrite /= ttakeE tdropE; rewrite cat_take_drop. Qed.

Definition trev m (t : m.-tuple A) := [tuple of rev t].

End Tuple.

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

Lemma split_lshift m i (j : 'I_m) : split (lshift i j) = inl j.
Proof.
case: splitP => [j1 j1E|/= k kE]; first by congr (inl _); apply/val_eqP/eqP.
by have := ltn_ord j; rewrite leqNgt kE ltnS leq_addr.
Qed.

Lemma split_rshift m i (j : 'I_m) : split (rshift i j) = inr j.
Proof.
case: splitP => [j1 j1E|k kE]; last first.
  congr (inr _).
  by apply/val_eqP/eqP; rewrite /= -[k : nat](addKn i) -kE addKn.
by have := ltn_ord j1; rewrite leqNgt -j1E ltnS leq_addr.
Qed.

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

Lemma cfun_perm c t : perm_eq (cfun c t) t.
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

Lemma nfun_perm n t : perm_eq (nfun n t) t.
Proof.
elim: n t => //= p n IH t.
by apply: perm_trans (IH _) (cfun_perm _ _).
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

Definition tmap (A1 A2 : Type) (g : A1 -> A2) t := [tuple g (tnth t i) | i < m].

Lemma tmap_val (A1 A2 : Type) (g : A1 -> A2) t : tmap g t = map g t :> seq A2.
Proof.
have -> : tmap g t = [tuple of [seq g (tnth t i) | i <- ord_tuple m]].
  by apply: eq_from_tnth => i; rewrite !(tnth_map, tnth_ord_tuple).
congr tval.
by apply: eq_from_tnth => i; rewrite !(tnth_map, tnth_ord_tuple).
Qed.

Lemma min_homo x y : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} -> min (f x) (f y) = f (min x y).
Proof.
(move=> fH; case: leP => [fxLfy|fyLfx]; case: leP => //).
  by rewrite lt_neqAle => /andP[_ /fH]; case: ltgtP fxLfy.
by move=> /fH; case: ltgtP fyLfx.
Qed.

Lemma max_homo x y : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} -> max (f x) (f y) = f (max x y).
Proof.
(move=> fH; case: leP => [fxLfy|fyLfx]; case: leP => //).
  by rewrite lt_neqAle => /andP[_ /fH]; case: ltgtP fxLfy.
by move=> /fH; case: ltgtP fyLfx.
Qed.

Lemma tmap_connector c t : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} ->
  cfun c (tmap f t) = tmap f (cfun c t).
Proof.
move=> Hm; apply: eq_from_tnth => i.
rewrite /cfun !tnth_map !tnth_ord_tuple min_homo // max_homo //.
by case: leqP.
Qed.

Lemma tmap_nfun n t : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} ->
  nfun n (tmap f t) = tmap f (nfun n t).
Proof.
by move=> Hm; elim: n t => //= a n IH t; rewrite tmap_connector // IH.
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
- by apply: (iffP idP) => // [[[x1 [[|x x21] x22]]]].
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

Arguments sorting{m}.

Lemma sorting1 (n : network 1) : n \is sorting.
Proof. by apply/forallP => /= t; case: nfun => /= [] [] // a []. Qed.

Section Bitonic.

Variable d : unit.
Variable A : orderType d.

Definition bitonic := [qualify p | 
 [exists r : 'I_(size (p : seq A)).+1, 
  exists n : 'I_(size (p : seq A)).+1,
  let p1 := rot r p in sorted (<=%O) (take n p1) && sorted (>=%O) (drop n p1)]].

Lemma bitonic_sorted (l : seq A) : sorted <=%O l -> l \is bitonic.
Proof.
move=> lS; apply/existsP; exists (inord 0); rewrite !inordK //= rot0.
apply/existsP; exists (inord (size l)); rewrite !inordK //.
by rewrite take_size lS /= drop_size.
Qed.

Lemma bitonic_r_sorted (l : seq A) : sorted >=%O l -> l \is bitonic.
Proof.
move=> lS; apply/existsP; exists (inord 0); rewrite !inordK //= rot0.
by apply/existsP; exists (inord 0); rewrite !inordK // take0 drop0.
Qed.

Lemma bitonic_cat (l1 l2 : seq A) :  
  sorted <=%O l1 -> sorted >=%O l2 -> (l1 ++ l2) \is bitonic.
Proof.
move=> l1S l2S.
apply/existsP; exists (inord 0); rewrite inordK ?rot0 //=.
apply/existsP; rewrite size_cat /=.
have sLs : size l1 < (size l1 + size l2).+1 by rewrite ltnS leq_addr.
exists (Ordinal sLs) => /=.
rewrite take_cat ltnn subnn take0 cats0 l1S /=.
by rewrite drop_cat ltnn subnn drop0.
Qed.

Lemma bitonic_rev (l : seq A) : (rev l \is  bitonic) = (l \is bitonic).
Proof.
suff {l}Hi (l : seq A) : l \is  bitonic -> rev l \is  bitonic.
  apply/idP/idP=> [H|]; last by apply: Hi.
  by rewrite -[l]revK; apply: Hi.
move=> /existsP[/= r /existsP[n /andP[tS dS]]].
apply/existsP; rewrite size_rev.
have xO : size l - r < (size l).+1 by rewrite ltnS leq_subr.
exists (Ordinal xO) => /=.
have yO : size l - n < (size l).+1 by rewrite ltnS leq_subr.
apply/existsP; exists (Ordinal yO) => /=.
rewrite -rev_rotr take_rev drop_rev !rev_sorted size_rotr /rotr.
by rewrite !subnA ?subnn -1?ltnS // dS.
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

Lemma isorted_bool_nseq (b : bool) k : (sorted <=%O (nseq k b)).
Proof.
case: b; apply/isorted_boolP; first by exists (0, k).
by exists (k, 0); rewrite cats0.
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

Lemma dsorted_bool_nseq (b : bool) k : (sorted >=%O (nseq k b)).
Proof.
case: b; apply/dsorted_boolP; first by exists (k, 0); rewrite cats0.
by exists (0, k).
Qed.

Section HalfCleaner.

Variable d : unit.
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
  
Definition half_cleaner m := connector_of (clink_half_cleaner_proof m).

Lemma cfun_half_cleaner n (t : (n + n).-tuple A) : 
  cfun (half_cleaner n) t = 
  [tuple
    match split i with 
    | inl x => min (tnth t i) (tnth t (rshift n x))  
    | inr x => max (tnth t (lshift n x)) (tnth t i)
    end | i < n + n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /half_cleaner /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple ffunE.
case: splitP => /= [j iE|k iE]; first by rewrite iE leq_addl.
rewrite ifN 1?maxC //=.
by rewrite -ltnNge (leq_trans (ltn_ord _) _) // iE leq_addr.
Qed.

Fixpoint half_cleaner_rec n : network (e2 n) :=
  if n is n1.+1 then half_cleaner (e2 n1) :: ndup (half_cleaner_rec n1)
  else [::].

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
have -> : l = rotr x (nseq j1 false ++ nseq (k1 + j2) true ++ nseq k2 false).
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

Lemma half_cleaner_bool n (t : (n + n).-tuple bool) :
  (t : seq _) \is bitonic -> 
  let t1 := cfun (half_cleaner n) t in 
    ((ttake t1 == nseq n false :> seq bool) && 
    ((tdrop t1 : seq bool) \is bitonic))
  ||
    ((tdrop t1 == nseq n true :> seq bool) && 
    ((ttake t1 : seq bool) \is bitonic)).
Proof.
move=> /bitonic_boolP[[[[b i] j] k] tE] /=; set t1 := cfun _ _.
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
    rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
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
    rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
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
    rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
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
    rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
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
    rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
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
    rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
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
  min  0 0~b~b~bhalf_cleaner 0 0 
  max  1 1~b~b~b 1 1
***)
have ttE : ttake t1 = nseq i false ++ nseq (j - n) (~~b)
                           ++ nseq k false :> seq bool.
  apply: (@eq_from_nth _ false) => [|u].
    by rewrite size_tuple !size_cat !size_nseq; lia.
  rewrite size_tuple => uLn.
  rewrite /ttake val_tcast nth_take // /t1 cfun_half_cleaner /=.
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
  rewrite /tdrop val_tcast nth_drop // /t1 cfun_half_cleaner /=.
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

Lemma sorted_bool_constl m (l : seq bool) :
  sorted <=%O ((nseq m false) ++ l) = sorted <=%O l.
Proof.
by elim: m => // [] n; rewrite [nseq _.+1 _ ++ _]/= isorted_consF.
Qed.

Lemma sorted_bool_constr m (l : seq bool) :
  sorted <=%O (l ++ (nseq m true)) = sorted <=%O l.
Proof.
elim: l => [|[] l IH].
- by case: m => // m; rewrite [nseq _.+1 _]/= isorted_consT size_nseq eqxx.
- rewrite [(_ :: _) ++ _]/= !isorted_consT size_cat nseqD size_nseq.
  by rewrite eqseq_cat ?eqxx ?andbT ?size_nseq.
by rewrite [(_ :: _) ++ _]/= !isorted_consF.
Qed.

Lemma half_cleaner_rec_bool m (t : (e2 m).-tuple bool) :
  (t : seq _) \is bitonic -> 
  sorted <=%O (nfun (half_cleaner_rec m) t).
Proof.
elim: m t => /= [|m IH t tB]; first by (do 2 case => //=) => x [].
rewrite nfun_dup.
have /orP[/andP[Ht Hd]|/andP[Ht Hd]] := half_cleaner_bool tB.
  have -> : ttake (cfun (half_cleaner (e2 m)) t) = [tuple of nseq (e2 m) false].
    by apply/val_eqP.
  rewrite nfun_const sorted_bool_constl.
  by apply: IH.
have -> : tdrop (cfun (half_cleaner (e2 m)) t) = [tuple of nseq (e2 m) true].
  by apply/val_eqP.
rewrite nfun_const sorted_bool_constr.
by apply: IH.
Qed.

Section RHalfCleaner.

Variable d : unit.
Variable A : orderType d.

Definition clink_rhalf_cleaner m : {ffun 'I_m -> 'I_m} := [ffun i => rev_ord i].

Lemma clink_rhalf_cleaner_proof m : 
  [forall i : 'I_(m + m), clink_rhalf_cleaner _ (clink_rhalf_cleaner _ i) == i].
Proof. by apply/forallP => i; rewrite !ffunE rev_ordK. Qed.
  
Definition rhalf_cleaner m := connector_of (clink_rhalf_cleaner_proof m).

Lemma cfun_rhalf_cleaner n (t : (n + n).-tuple A) : 
  cfun (rhalf_cleaner n) t = 
  [tuple
    match split i with 
    | inl x => min (tnth t i) (tnth t (rshift n (rev_ord x)))  
    | inr x => max (tnth t (lshift n (rev_ord x))) (tnth t i)
    end | i < n + n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /rhalf_cleaner /cfun /= !tnth_map /= tnth_ord_tuple ffunE.
case: splitP => [j iE|k iE]; rewrite /= iE.
  rewrite leq_subRL ?(leq_trans (ltn_ord _)) ?leq_addr //.
  rewrite leq_add // 1?ltnW //.
  by congr (min _ (tnth _ _)); apply/val_eqP; rewrite /= iE addnBA.
rewrite -addnS subnDl leqNgt ltn_subLR // addSn ltnS addnC -addnA leq_addr /=.
rewrite maxC; congr (max (tnth _ _) _).
by apply/val_eqP; rewrite /= iE -addnS subnDl.
Qed.

Lemma cfun_rhalf_cleaner_rev_take n (t : (n + n).-tuple A) : 
  ttake (cfun (rhalf_cleaner n) t) =
  ttake (cfun (half_cleaner n) [tuple of ttake t ++ rev (tdrop t)]).
Proof.
rewrite cfun_rhalf_cleaner cfun_half_cleaner.
apply: eq_from_tnth => i /=.
have st : size (ttake t) = n.
  rewrite ttakeE size_take size_tuple.
  by case: (n) => // n1; rewrite addSn ltnS addnS ltnS leq_addr.
have sd : size (tdrop t) = n.
  by rewrite tdropE size_drop size_tuple addnK.
pose k : 'I_(n + n) := lshift _ i; pose a := tnth t k.
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

Lemma cfun_rhalf_cleaner_rev_drop n (t : (n + n).-tuple A) : 
  tdrop (cfun (rhalf_cleaner n) t) =
  trev
  (tdrop (cfun (half_cleaner n) [tuple of ttake t ++ rev (tdrop t)])).
Proof.
rewrite cfun_rhalf_cleaner cfun_half_cleaner.
apply: eq_from_tnth => i /=.
have st : size (ttake t) = n.
  rewrite ttakeE size_take size_tuple.
  by case: (n) => // n1; rewrite addSn ltnS addnS ltnS leq_addr.
have sd : size (tdrop t) = n.
  by rewrite tdropE size_drop size_tuple addnK.
pose k : 'I_(n + n) := rshift _ i; pose a := tnth t k.
rewrite !(tnth_nth a) nth_rev; last first.
  by rewrite tdropE size_drop size_tuple addnK.
rewrite !tdropE !nth_drop !(nth_map k) //; last first.
- by rewrite size_tuple ltn_add2l.
- by rewrite -fintype.enumT fintype.size_enum_ord ltn_add2l.
- by rewrite size_drop !size_tuple; have := ltn_ord i; lia.
- rewrite size_drop !size_tuple -fintype.enumT fintype.size_enum_ord.
  by have := ltn_ord i; lia.
have -> : n + i = k :> nat by [].
rewrite -fintype.enumT fintype.nth_ord_enum.
case: splitP => [j kE|j kE].
  by have := ltn_ord j; rewrite -kE /= ltnNge leq_addr.
rewrite size_drop size_tuple addnK.
have -> : n + (n - i.+1) = rshift n (rev_ord i) by [].
rewrite fintype.nth_ord_enum.
case: splitP => /= [l lE | l lE]; first by have := ltn_ord l; lia.
congr max.
  rewrite !(tnth_nth a) nth_cat /= st ltn_ord.
  rewrite ttakeE nth_take //; congr nth.
  have : n + i = n + j by rewrite -kE.
  by have := ltn_ord i; lia.
rewrite !(tnth_nth a) nth_cat /= st ifN; last by rewrite -leqNgt leq_addr.
rewrite nth_rev; last by rewrite sd; have := ltn_ord i; lia.
rewrite tdropE nth_drop //.
congr nth.
rewrite size_drop size_tuple.
by have := ltn_ord i; lia.
Qed.

Lemma cfun_rhalf_cleaner_rev n (t : (n + n).-tuple A) : 
  let t1 :=  cfun (half_cleaner n) [tuple of ttake t ++ rev (tdrop t)] in
  cfun (rhalf_cleaner n) t =
  [tuple of ttake t1 ++ rev (tdrop t1)].
Proof.
rewrite /= [LHS]cat_ttake_tdrop; congr [tuple of _ ++ _].
  by apply: cfun_rhalf_cleaner_rev_take.
by apply: cfun_rhalf_cleaner_rev_drop.
Qed.

Definition rhalf_cleaner_rec n : network (e2 n) :=
  if n is n1.+1 then
    rhalf_cleaner (e2 n1) :: ndup (half_cleaner_rec n1)
  else [::].

End RHalfCleaner.

Lemma rhalf_cleaner_rec_bool m (t : (e2 m.+1).-tuple bool) :
  sorted <=%O (ttake t : seq _) -> sorted <=%O (tdrop t : seq _) ->
  sorted <=%O (nfun (rhalf_cleaner_rec m.+1) t).
Proof.        
rewrite /rhalf_cleaner_rec /= => Hst Hsd.
rewrite nfun_dup.
rewrite cfun_rhalf_cleaner_rev_drop -/e2 cfun_rhalf_cleaner_rev_take -/e2.
set u : (e2 m.+1).-tuple _ := [tuple of _ ++ rev _].
have uB : (u : seq _) \is bitonic.
  apply: bitonic_cat => //.
  by rewrite rev_sorted.
have := half_cleaner_bool uB; rewrite -/e2 => /orP[/andP[Ht Hd]|/andP[Ht Hd]].
  have -> : ttake (cfun (half_cleaner (e2 m)) u) = [tuple of nseq (e2 m) false].
    by apply/val_eqP.
  rewrite nfun_const sorted_bool_constl.
  apply: half_cleaner_rec_bool.
  by rewrite bitonic_rev.
have -> : trev (tdrop (cfun (half_cleaner (e2 m)) u)) = 
            [tuple of nseq (e2 m) true].
  by apply/val_eqP; rewrite /= (eqP Ht) rev_nseq.
rewrite nfun_const sorted_bool_constr.
by apply: half_cleaner_rec_bool.
Qed.

Section BitonicSort.

Variable d : unit.
Variable A : orderType d.

Fixpoint bsort m : network (e2 m) :=
  if m is m1.+1 then ndup (bsort m1) ++ rhalf_cleaner_rec m1.+1 
  else [::].

Lemma sorting_bsort m : bsort m \is sorting.
Proof.
elim: m => [|m IH]; first by apply: sorting1.
apply/forallP => t.
rewrite /bsort -/bsort nfun_cat.
apply: rhalf_cleaner_rec_bool; first by rewrite nfun_dup ttakeK (forallP IH).
by rewrite nfun_dup tdropK (forallP IH).
Qed.

End BitonicSort.
