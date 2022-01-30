From mathcomp Require Import all_ssreflect perm algebra.zmodp.
From mathcomp Require Import zify.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of some network sorting algorithms                             *)
(*                                                                            *)
(*         `2^ m == 2 ^ n so that                                             *)
(*                  `2^ m.+1 = `2^ m + `2^ m is true by reduction             *)
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
(*               == the (`2^ m) network composed of the recursive duplication  *)
(*                  of an half_cleaner                                        *)
(*   rhalf_cleaner_rec m                                                      *)
(*               == the (`2^ m) network composed of a rhalf_cleaner and then   *)
(*                  the duplication of a half_cleaner_rec                     *)
(*       bsort m == the (`2^ m) network that implements the bitonic sort       *)
(* n \is sorting == the network n is a sorting network, i.e it always returns *)
(*                  a sorted tuple                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section E2.

(* We define an explicte function `2^ n = 2 ^ n so that `2^ n.+1 reduces        *)
(* to `2^ m + `2^ m                                                             *)

Fixpoint e2n m := if m is m1.+1 then e2n m1 + e2n m1 else 1.

Notation "`2^ n" := (e2n n) (at level 40).

Lemma e2nE m : `2^ m = 2 ^ m.
Proof. by elim: m => //= m ->; rewrite expnS mul2n addnn. Qed.

Lemma e2Sn m : `2^ m.+1 = `2^ m + `2^ m.
Proof. by []. Qed.

Lemma e2n_gt0 m : 0 < `2^ m.
Proof. by rewrite e2nE expn_gt0. Qed.

Lemma odd_e2 m : odd (`2^ m) = (m == 0).
Proof. by case: m => //= m; rewrite addnn odd_double. Qed.

End E2.

Notation "`2^ n" := (e2n n) (at level 40).

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

Fixpoint etake (l : seq A) :=
  if l is a :: l1 then a :: (if l1 is _ :: l2 then etake l2 else [::])
  else [::].

Definition otake l := if l is _ :: l1 then etake l1 else [::].

Lemma etake_cons a (l : seq A) : etake (a :: l) = a :: otake l.
Proof. by []. Qed.

Lemma otake_cons a (l : seq A) : otake (a :: l) = etake l.
Proof. by []. Qed.

Lemma nth_etake a (l : seq A) n : nth a (etake l) n = nth a l n.*2.
Proof.
have [m leMm] := ubnP (size l);
    elim: m l leMm n => [[]//|m IH [|b [|c l]]] HS n.
- by rewrite /= !nth_nil.
- by case: n => [|n]; rewrite //= nth_nil.
rewrite etake_cons otake_cons; case: n => //= n.
rewrite ltnS in HS.
by apply: IH; apply: leq_trans HS => /=.
Qed.

Lemma nth_otake a (l : seq A) n : nth a (otake l) n = nth a l n.*2.+1.
Proof.
by case: l; rewrite //= ?nth_nil // => _ l; rewrite nth_etake.
Qed.

Lemma size_etake l : size (etake l) = (size l).+1./2.
Proof.
have [n leMn] := ubnP (size l); elim: n l leMn => // n IH [|a [|bl]] //= l.
rewrite !ltnS => slLn.
by rewrite IH //= (leq_trans _ slLn).
Qed.

Lemma etake_tupleP m (t : (m + m).-tuple A) : size (etake t) == m.
Proof. by rewrite size_etake size_tuple /= addnn uphalf_double. Qed.
Canonical etake_tuple m (t : (m + m).-tuple A) := Tuple (etake_tupleP t).

Lemma size_otake l : size (otake l) = (size l)./2.
Proof. by case: l => //= a l; rewrite size_etake. Qed.

Lemma otake_tupleP m (t : (m + m).-tuple A) : size (otake t) == m.
Proof. by rewrite size_otake size_tuple addnn doubleK. Qed.
Canonical otake_tuple m (t : (m + m).-tuple A) := Tuple (otake_tupleP t).

Lemma etake_nseq i (a : A) : etake (nseq i a) = nseq (uphalf i) a.
Proof.
have [n leMi] := ubnP i; elim: n i leMi => // n IH [|[|i]] //= iLn.
by rewrite IH // -ltnS (leq_trans _ iLn).
Qed.

Lemma otake_nseq i (a : A) : otake (nseq i a) = nseq i./2 a.
Proof. by case: i => //= i; exact: etake_nseq. Qed.

Lemma etake_cat (l1 l2 : seq A) : 
  etake (l1 ++ l2) = etake l1 ++ if odd (size l1) then otake l2 else etake l2.
Proof.
have [n leMl1] := ubnP (size l1).
elim: n l1 leMl1 => // n IH [|a[|b l1]] //= slLn.
by rewrite negbK IH // -ltnS (leq_trans _ slLn).
Qed.

Lemma otake_cat (l1 l2 : seq A) : 
  otake (l1 ++ l2) = otake l1 ++ if odd (size l1) then etake l2 else otake l2.
Proof. by case: l1 => // a l; rewrite /= if_neg etake_cat. Qed.

Lemma uphalfE n : uphalf n = n.+1./2.
Proof. by []. Qed.

Lemma etake_cat_nseq (l1 l2 : seq A) (a1 a2 : A) m1 m2 : 
  etake (nseq m1 a1 ++ nseq m2 a2) = 
  nseq (uphalf m1) a1 ++ nseq (~~odd m1 + m2)./2 a2.
Proof.
by rewrite etake_cat !etake_nseq otake_nseq size_nseq; case: (odd m1).
Qed.

Lemma otake_cat_nseq (l1 l2 : seq A) (a1 a2 : A) m1 m2 : 
  otake (nseq m1 a1 ++ nseq m2 a2) = 
  nseq m1./2 a1 ++ nseq (odd m1 + m2)./2 a2.
Proof.
by rewrite otake_cat !otake_nseq etake_nseq size_nseq; case: (odd m1).
Qed.


Definition tetake (m : nat) (t : (m + m).-tuple A) := [tuple of etake t].
Definition totake (m : nat) (t : (m + m).-tuple A) := [tuple of otake t].

Lemma tetakeE (m : nat) (t : (m + m).-tuple A) : tetake t = etake t :> seq A.
Proof. by []. Qed.

Lemma totakeE (m : nat) (t : (m + m).-tuple A) : totake t = otake t :> seq A.
Proof. by []. Qed.

Fixpoint eocat (l1 l2 : seq A) :=
  if l1 is a :: l3 then a :: head a l2 :: eocat l3 (behead l2) else [::].

Lemma size_eocat l1 l2 : size (eocat l1 l2) = (size l1 + size l1).
Proof. by elim: l1 l2 => //= a l1 IH l2; rewrite IH addnS. Qed.

Lemma nth_eocat a (l1 l2 : seq A) n : 
  size l1 = size l2 ->
  nth a (eocat l1 l2) n = nth a (if odd n then l2 else l1) n./2.
Proof.
elim: l1 l2 n => /= [[]//= n|b l1 IH [//= n|c l2 [|[|n]] //= [Hs]/=]].
  by rewrite if_same !nth_nil.
by rewrite negbK IH; case: odd.
Qed.

Lemma eocat_etake_otake n l : size l = n + n -> eocat (etake l) (otake l) = l.
Proof.
elim: n l =>[[]// | n IH [//|a [|b l]]]; rewrite !addnS //.
by rewrite !(etake_cons, otake_cons) /= => [] [H]; rewrite IH.
Qed.

Lemma etakeK l1 l2 : etake (eocat l1 l2) = l1.
Proof. by elim: l1 l2 => //= a l IH l2; rewrite IH. Qed.

Lemma otakeK l1 l2 : size l1 = size l2 -> otake (eocat l1 l2) = l2.
Proof.
elim: l1 l2 => [[]//|a l1 IH [|b l2] //].
by rewrite [eocat _ _]/= otake_cons etake_cons /= => [] [/IH->].
Qed.

Lemma etake_eocat (l1 l2 : seq A) :  etake (eocat l1 l2) = l1.
Proof.
have [n leMl1] := ubnP (size l1).
elim: n l1 leMl1 l2 => // n IH [|a[|b l1]] //= slLn l2.
by rewrite IH // -ltnS (leq_trans _ slLn).
Qed.

Lemma otake_eocat (l1 l2 : seq A) :
  size l1 = size l2 -> otake (eocat l1 l2) = l2.
Proof.
elim: l1 l2 => [|a l1 IH] l2; first by case: l2.
case: l2 => [//|b l2].
by rewrite [eocat _ _]/= otake_cons etake_cons => [] [/IH->].
Qed.

Lemma eocat_tupleP m1 m2 (t1 : m1.-tuple A) (t2 : m2.-tuple A) :
  size (eocat t1 t2) == m1 + m1.
Proof. by rewrite size_eocat size_tuple. Qed.
Canonical eocat_tuple m1 m2 (t1 : m1.-tuple A) (t2 : m2.-tuple A) :=
  Tuple (eocat_tupleP t1 t2).

Lemma eocat_tetake_totake n (t : (n + n).-tuple A) : 
  t = [tuple of eocat (tetake t) (totake t)].
Proof. 
by apply/val_eqP; rewrite /= (@eocat_etake_otake n) // size_tuple.
Qed.

Lemma tetakeK (m : nat) (t1 t2 : m.-tuple A) : 
  tetake [tuple of eocat t1 t2] = t1.
Proof.
by apply/val_eqP; rewrite /= tetakeE /= etake_eocat.
Qed.

Lemma totakeK (m : nat) (t1 t2 : m.-tuple A) : 
  totake [tuple of eocat t1 t2] = t2.
Proof.
by apply/val_eqP; rewrite /= totakeE /= otake_eocat // !size_tuple.
Qed.

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

Definition elift m : 'I_m -> 'I_(m + m) := 
  if m is m1.+1 then fun i => inZp (i.*2) else fun i => i.

Lemma elift_val m (i : 'I_m) : elift i = i.*2 :> nat.
Proof.
case: m i => [[]//|m i].
by rewrite -[LHS]/(i.*2 %% (m.+1 + m.+1)) modn_small // addnn ltn_double.
Qed.

Definition olift m : 'I_m -> 'I_(m + m) := 
  if m is m1.+1 then fun i => inZp (i.*2.+1) else fun i => i.

Lemma olift_val m (i : 'I_m) : olift i = i.*2.+1 :> nat.
Proof.
case: m i => [[]//|m i].
rewrite -[LHS]/(i.*2.+1 %% (m.+1 + m.+1)) modn_small //.
by rewrite addnS addSn !ltnS addnn leq_double -ltnS.
Qed.

Definition idiv2 m : 'I_(m + m) -> 'I_m := 
  if m is m1.+1 then fun i => inZp (i./2) else fun i => i.

Lemma idiv2_val m (i : 'I_(m + m)) : idiv2 i = i./2 :> nat.
Proof.
case: m i => [[]//|n i /=].
rewrite modn_small // -ltn_double -[X in _ < X]addnn.
rewrite (leq_ltn_trans _ (ltn_ord i)) //.
by rewrite -[X in _ <= X]odd_double_half leq_addl.
Qed.

Lemma oliftK m (i : 'I_m) : idiv2 (olift i) = i.
Proof.
apply/val_eqP; rewrite /= idiv2_val /= olift_val.
by rewrite -divn2 -muln2 -addn1 divnMDl // addn0.
Qed.

Lemma idiv2K_odd m (i : 'I_(m + m)) : odd i -> olift (idiv2 i) = i.
Proof.
move=> iO.
apply/val_eqP; rewrite /= olift_val /= idiv2_val.
by rewrite -[X in _ == X]odd_double_half iO.
Qed.

Lemma idiv2K_even m (i : 'I_(m + m)) : ~~ odd i -> elift (idiv2 i) = i.
Proof.
move=> iO.
apply/val_eqP; rewrite /= elift_val /= idiv2_val.
by rewrite -[X in _ == X]odd_double_half (negPf iO).
Qed.

Lemma eliftK m (i : 'I_m) : idiv2 (elift i) = i.
Proof.
by apply/val_eqP; rewrite /= idiv2_val /= elift_val doubleK.
Qed.

Definition clink_eomerge m (c1 : connector m) (c2 : connector m) :=
  [ffun i : 'I_ _ => 
    if odd i then olift (clink c2 (idiv2 i)) else elift (clink c1 (idiv2 i))].
  
Lemma clink_eomerge_proof m (c1 : connector m) (c2 : connector m) :
  [forall i, (clink_eomerge c1 c2 (clink_eomerge c1 c2 i)) == i].
Proof.
apply/forallP=> i /=.
rewrite !ffunE /=; have [iO|iE] := boolP (odd i).
  rewrite oliftK olift_val /= odd_double /= (eqP (forallP (cfinv c2) _)).
  by rewrite idiv2K_odd.
rewrite eliftK elift_val /= odd_double /= (eqP (forallP (cfinv c1) _)).
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

Fixpoint half_cleaner_rec n : network (`2^ n) :=
  if n is n1.+1 then half_cleaner (`2^ n1) :: ndup (half_cleaner_rec n1)
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

Lemma half_cleaner_rec_bool m (t : (`2^ m).-tuple bool) :
  (t : seq _) \is bitonic -> 
  sorted <=%O (nfun (half_cleaner_rec m) t).
Proof.
elim: m t => /= [|m IH t tB]; first by (do 2 case => //=) => x [].
rewrite nfun_dup.
have /orP[/andP[Ht Hd]|/andP[Ht Hd]] := half_cleaner_bool tB.
  have -> : ttake (cfun (half_cleaner (`2^ m)) t) = [tuple of nseq (`2^ m) false].
    by apply/val_eqP.
  rewrite nfun_const sorted_bool_constl.
  by apply: IH.
have -> : tdrop (cfun (half_cleaner (`2^ m)) t) = [tuple of nseq (`2^ m) true].
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

Definition rhalf_cleaner_rec n : network (`2^ n) :=
  if n is n1.+1 then
    rhalf_cleaner (`2^ n1) :: ndup (half_cleaner_rec n1)
  else [::].

End RHalfCleaner.

Lemma rhalf_cleaner_rec_bool m (t : (`2^ m.+1).-tuple bool) :
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
have := half_cleaner_bool uB; rewrite -/e2n => /orP[/andP[Ht Hd]|/andP[Ht Hd]].
  have -> : ttake (cfun (half_cleaner (`2^ m)) u) = [tuple of nseq (`2^ m) false].
    by apply/val_eqP.
  rewrite nfun_const sorted_bool_constl.
  apply: half_cleaner_rec_bool.
  by rewrite bitonic_rev.
have -> : trev (tdrop (cfun (half_cleaner (`2^ m)) u)) = 
            [tuple of nseq (`2^ m) true].
  by apply/val_eqP; rewrite /= (eqP Ht) rev_nseq.
rewrite nfun_const sorted_bool_constr.
by apply: half_cleaner_rec_bool.
Qed.

Section BitonicSort.

Variable d : unit.
Variable A : orderType d.

Fixpoint bsort m : network (`2^ m) :=
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

Variable d : unit.
Variable A : orderType d.

Definition leqc m (t1 t2 : m.-tuple A) :=
  [forall a : 'I_m, forall b : 'I_m, 
    (a <= b) ==> (tnth t1 a <= tnth t1 b)%O ==> (tnth t2 a <= tnth t2 b)%O].

Lemma leqcP m (t1 t2 : m.-tuple A) :
  reflect 
  (forall a b : 'I_m, a <= b ->
                (tnth t1 a <= tnth t1 b)%O -> (tnth t2 a <= tnth t2 b)%O)
  (leqc t1 t2).
Proof.
apply: (iffP forallP) => [H a b aLb t1aLt1b|H a].
  by have /forallP/(_ b) := H a; rewrite aLb t1aLt1b.
by apply/forallP=> b; case: leqP => //= aLb; apply/implyP/H.
Qed.

Lemma leqcc m : reflexive (@leqc m).
Proof. by move=>t; apply/leqcP. Qed.

Lemma leqc_trans m : transitive (@leqc m).
Proof.
move=>t2 t1 t3 /leqcP Ht1t2 /leqcP Ht2t3.
apply/leqcP => a b aLb t2aLt2b.
by apply: Ht2t3 => //; apply: Ht1t2.
Qed.

Lemma leqc_sorted m (t1 t2 : m.-tuple A) : sorted (>%O) t1 -> leqc t1 t2.
Proof.
move=> sS; apply/leqcP => a b.
rewrite leq_eqVlt => /orP[/val_eqP->//|aLb].
pose v := tnth t1 a; rewrite leNgt !(tnth_nth v).
by rewrite -DualPOrder.ltEdual lt_sorted_ltn_nth ?(aLb, inE, size_tuple).
Qed.

Lemma leqc_cfun m (c : connector m) : 
  ctransp c -> {homo cfun c : i j / leqc i j}.
Proof.
(* This proof is slightly more complicate in our setting because 
   a connector can contain simultaneous transposition *)
move=> /ctranspP cT t1 t2 /leqcP t1Lt2; apply/leqcP => a b.
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

Lemma leqc_nfun m (n : network m) : 
  ntransp n -> {homo nfun n : i j / leqc i j}.
Proof.
elim: n => /= [_| c n IH /andP[cT nT]] t1 t2 t1Lt2 //=.
by apply: IH => //; apply: leqc_cfun.
Qed.

Lemma leqc_nsorted m (x1 x2 : A) (t : m.-tuple A) (n : network m) : 
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
have /leqcP/(_ a1 b1 aLb) : leqc (nfun n t) (nfun n t1).
  apply: leqc_nfun => //.
  by apply: leqc_sorted.
rewrite !(tnth_nth x1); apply.
by apply: (sorted_leq_nth le_trans le_refl x1 tS1); rewrite ?(inE, size_tuple).
Qed.

End Transposition.

Section EOMerge.

Variable m : nat.
Variable d : unit.
Variable A : orderType d.

Implicit Types t : m.-tuple A.
Implicit Types c : connector m.
Implicit Types n : network m.

Lemma cfun_eomerge (c1 : connector m) (c2 : connector m) 
                   (t : (m + m).-tuple A) : 
  cfun (ceomerge c1 c2) t = [tuple of eocat (cfun c1 (tetake t)) 
                                            (cfun c2 (totake t))].
Proof.
apply: eq_from_tnth => i.
have iLm : i < m + m by apply: ltn_ord.
have i2Lm : i./2 < m by have := ltn_ord (idiv2 i); rewrite idiv2_val.
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
    by rewrite -fintype.enumT -enum_ord /= !nth_enum_ord ?idiv2_val.
  rewrite !(tnth_nth a) /= !nth_otake /= olift_val /= idiv2_val.
  have F : i = i./2.*2.+1 :> nat by rewrite -[LHS]odd_double_half iO.
  by rewrite -F {1}F ltnS leq_double.
rewrite !(nth_map (idiv2 i)); last 2 first.
- by rewrite -fintype.enumT -enum_ord size_enum_ord.
- by rewrite -enum_ord size_enum_ord.
set u := nth _ _ _; have -> : u = idiv2 i.
  apply/val_eqP; rewrite /= /u.
  by rewrite -fintype.enumT -enum_ord /= !nth_enum_ord ?idiv2_val.
rewrite !(tnth_nth a) /= !nth_etake /= elift_val /= idiv2_val.
have F : i = i./2.*2 :> nat by rewrite -[LHS]odd_double_half (negPf iE).
by rewrite -F {1}F leq_double.
Qed.

Lemma cfun_eodup (c : connector m) (t : (m + m).-tuple A) :
  cfun (ceodup c) t = [tuple of eocat (cfun c (tetake t)) (cfun c (totake t))].
Proof. by apply: cfun_eomerge. Qed.

Definition neomerge m (n1 : network m) (n2 : network m) := 
    [seq ceomerge i.1 i.2 | i <- zip n1 n2].

Definition neodup m (n : network m) : network (m + m) := neomerge n n.

Lemma nfun_eodup (n : network m) (t : (m + m).-tuple A) : 
  nfun (neodup n) t = [tuple of eocat (nfun n (tetake t)) (nfun n (totake t))].
Proof.
elim: n t => /= [t|c n IH t]; first by rewrite -eocat_tetake_totake.
by rewrite IH !cfun_eodup tetakeK totakeK.
Qed.

End EOMerge.

Section Batcher.

Variable d : unit.
Variable A : orderType d.


Definition inext m : 'I_m -> 'I_m := 
  if m is m1.+1 then fun i => inZp (if i == m1 :> nat then i : nat else i.+1)
  else fun i => i.

Lemma inext_val m (i : 'I_m) : 
  inext i = if i == m.-1 :> nat then i : nat else i.+1 :> nat.
Proof.
case: m i => [[]//|n i /=].
have:= (ltn_ord i); rewrite ltnS leq_eqVlt.
by case: eqP => [->|_] /= iLn; rewrite modn_small.
Qed.

Definition ipred m : 'I_m -> 'I_m := 
  if m is m1.+1 then fun i => inZp (i.-1) else fun i => i.

Lemma ipred_val m (i : 'I_m) : ipred i = i.-1 :> nat.
Proof.
case: m i => [[]//|n i /=].
by rewrite modn_small // (leq_ltn_trans (leq_pred _) (ltn_ord i)).
Qed.

Definition clink_Batcher_merge m : {ffun 'I_m -> 'I_m} :=
  [ffun i : 'I_ _ => if odd i then inext i else ipred i].

Lemma clink_Batcher_merge_proof m : 
  [forall i : 'I_(m + m), clink_Batcher_merge _ (clink_Batcher_merge _ i) == i].
Proof.
apply/forallP => i /=; apply/eqP/val_eqP; rewrite !ffunE.
have mmE : ~~ (odd (m + m)) by rewrite addnn odd_double.
have mm_gt0 : 0 < m + m by apply: leq_ltn_trans (ltn_ord i).
have [iO|iE] := boolP (odd i); rewrite /= !(ipred_val, inext_val).
  case:  ((i : nat) =P (m + m).-1) => [/eqP iEm | /eqP iDm].
    by rewrite iO !inext_val /= !iEm.
  by rewrite /= iO /= ipred_val inext_val (negPf iDm).
have [i1O|i1E] := boolP (odd i.-1); rewrite /= !(ipred_val, inext_val).
  have i_gt0 : 0 < i by case: (i : nat) iE i1O.
  by rewrite prednK // ifN // -eqSS !prednK // neq_ltn ltn_ord.
by case: (i : nat) iE i1E => //= n; case: odd.
Qed.
  
Definition Batcher_merge {m} := connector_of (clink_Batcher_merge_proof m).

Lemma cfun_Batcher_merge n (t : (n + n).-tuple A) : 
  cfun Batcher_merge t = 
  [tuple
    if odd i then min (tnth t i) (tnth t (inext i))
    else max (tnth t i) (tnth t (ipred i)) | i < n + n].
Proof.
apply: eq_from_tnth => i /=.
rewrite /Batcher_merge /cfun /=.
rewrite !tnth_map /= !tnth_ord_tuple ffunE.
have [iO|iE] := boolP (odd i).
  by rewrite ifT // inext_val; case: eqP.
case: leqP => [iLip|] //.
suff -> : ipred i = i by rewrite maxxx minxx.
apply/val_eqP =>> /=; move: iLip; rewrite !ipred_val /=.
by case: (i : nat) => //= i1; rewrite ltnn.
Qed.

Fixpoint Batcher_merge_rec_aux m : network (`2^ m.+1) :=
  if m is m1.+1 then rcons (neodup (Batcher_merge_rec_aux m1)) Batcher_merge
  else [:: cswap ord0 ord_max].

Definition Batcher_merge_rec m := 
  if m is m1.+1 then Batcher_merge_rec_aux m1 else [::].

Fixpoint Batcher m : network (`2^ m) :=
  if m is m1.+1 then ndup (Batcher m1) ++ Batcher_merge_rec m1.+1
  else [::].

End Batcher.


Lemma aabbEabab a b : (a + a) + (b + b) = (a + b) + (a + b).
Proof. by rewrite [RHS]addnAC !addnA. Qed.

Lemma minFb x : min false x = false.
Proof. by case: x. Qed.

Lemma minbF x : min x false = false.
Proof. by case: x. Qed.

Lemma maxFb x : max false x = x.
Proof. by case: x. Qed.

Lemma maxbF x : max x false = x.
Proof. by case: x. Qed.

Lemma minTb x : min true x = x.
Proof. by case: x. Qed.

Lemma minbT x : min x true = x.
Proof. by case: x. Qed.

Lemma maxTb x : max true x = true.
Proof. by case: x. Qed.

Lemma maxbT x : max x true = true.
Proof. by case: x. Qed.


Lemma cfun_Batcher_merge_case1 a b c (H : a + b = c + c) : 
  let t1 := tcast H [tuple of nseq a false ++ nseq b true] in
  cfun Batcher_merge t1 = t1. 
Proof.
move=> t1.
rewrite cfun_Batcher_merge.
apply: eq_from_tnth => i.
have cc_gt0 : 0 < c + c by apply: leq_ltn_trans (ltn_ord i).
rewrite !tcastE !(tnth_nth false) /= nth_cat !nth_nseq /= ?size_nseq.
rewrite !if_same -enum_ord !(nth_map i) ?size_enum_ord //.
rewrite !tcastE  nth_ord_enum !(tnth_nth false) /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq inext_val ipred_val.
rewrite !if_same.
have [iLa|aLi] := ltnP i.
  by rewrite minFb (_ : i.-1 < a) ?if_same // (leq_ltn_trans (leq_pred _) iLa).
rewrite ltn_subLR // H ltn_ord /= maxTb minTb.
case: eqP => [->|/eqP iDcc].
  have aLcc : a <= (c + c).-1.
    by rewrite -ltnS prednK // (leq_ltn_trans aLi).
  rewrite ltnNge aLcc /= ltn_subLR // H.
  by case: (c + c) cc_gt0 => //= c1; rewrite leqnn if_same.
have aLi1 : a <= i.+1 by apply: leq_trans aLi _.
rewrite ltnNge aLi1 /= ltn_subLR // H.
rewrite -[odd i]negbK -oddS.
move: (ltn_ord i); rewrite leq_eqVlt => /orP[/eqP HH|->].
  by rewrite -[in X in _ != X]HH eqxx in iDcc.
by rewrite if_same.
Qed.

Lemma cfun_Batcher_merge_case12 a b c 
  (H1 : a + b.+2 = c + c) (H2 : a.+1 + b.+1 = c + c) : 
  odd a ->
  let t1 := tcast H1 [tuple of nseq a false ++ true :: false :: nseq b true] in
  let t2 := tcast H2 [tuple of nseq a.+1 false ++ nseq b.+1 true] in
  cfun Batcher_merge t1 = t2. 
Proof.
move=> aO t1 t2.
have bO : odd b.
  have : ~~ odd (c + c) by rewrite addnn odd_double.
  by rewrite -H2 oddD /= aO /= negbK.
rewrite cfun_Batcher_merge.
apply: eq_from_tnth => i.
have cc_gt0 : 0 < c + c by apply: leq_ltn_trans (ltn_ord i).
rewrite !tcastE /= !(tnth_nth false) /= !(nth_map i); last 2 first.
- by rewrite -fintype.enumT -enum_ord size_enum_ord.
- by rewrite -enum_ord size_enum_ord.
rewrite -fintype.enumT -enum_ord !nth_enum_ord // !nth_ord_enum.
rewrite !tcastE /= (tnth_nth false) /= /t1 /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq /=.
rewrite !(tnth_nth false) /=.
rewrite !nth_cat !nth_nseq /= ?size_nseq inext_val ipred_val.
have [iLa|aLi] := ltnP i.
  rewrite minFb maxFb (_ : i.-1 < a) ?if_same; last first.
    by rewrite (leq_ltn_trans (leq_pred _) iLa).
  rewrite (nth_cat _ (nseq _.+1 _)) ?size_nseq /= ltnS ltnW //.
  by rewrite (nth_nseq _ _.+1) if_same.
rewrite (nth_cat _ (nseq _.+1 _)) ?size_nseq ltnS.
rewrite if_same.
move: aLi; rewrite leq_eqVlt => /orP[/eqP<-|aLi].
  rewrite subnn /= leqnn (nth_nseq _ _.+1) leqnn.
  rewrite minTb maxTb.
  case: eqP (H2) => [->/eqP|/eqP iDcc _].
    by rewrite prednK // -[X in _ == X -> _]addn0 eqn_add2l.
  by rewrite aO ltnNge leqnSn /= subSn // subnn.
have i_gt0 : 0 < i by apply: leq_ltn_trans aLi.
rewrite prednK // [i <= a]leqNgt aLi /=.
rewrite (nth_nseq _ _.+1) ltn_subLR // H2 ltn_ord /=.
have i1La : a <= i.+1 by rewrite -ltnS (leq_trans aLi) // ltnW.
move: aLi; rewrite leq_eqVlt => /orP[/eqP<-|aLi].
  by rewrite subSn // subnn /= aO.
have iaE : i - a = (i - a).-2.+2.
  have iLa : a < i by apply: ltn_trans aLi.
  by rewrite !prednK ?subn_gt0 // -ltnS prednK // ltn_subRL ?addn1 // addn0.
rewrite iaE /= nth_nseq.
have ia2Lb : (i - a).-2 < b.
  rewrite -subn2 ltn_subLR ?add2n; last by rewrite iaE.
  rewrite ltn_subLR; last by apply: leq_trans (ltnW aLi).
  by rewrite -addSnnS [X in i < X]H2 ltn_ord.
rewrite ia2Lb minTb maxTb.
case: eqP => [|/eqP iDcc].
  by rewrite iaE /= nth_nseq ia2Lb ltnNge (leq_trans _ (ltnW aLi)) //= if_same.
rewrite [i.+1 < a]ltnNge i1La /=.
have i1aE : i.+1 - a = (i.+1 - a).-2.+2.
  rewrite subSn /=.
    by rewrite prednK /= // subn_gt0 (ltn_trans _ aLi).
  by apply: leq_trans (ltnW aLi).
rewrite i1aE /= nth_nseq.
move: aLi; rewrite leq_eqVlt => /orP[/eqP HH|aLi].
  rewrite -HH /= aO /= -add3n addnK /=.
  have := ltn_ord i.
  rewrite -[X in _ < X]H2 -HH -addSnnS -addn1 leq_add2l.
  rewrite leq_eqVlt => /orP[/eqP bE|->//].
  by have := iDcc; rewrite -HH -H2 -addSnnS -bE addn1 eqxx.
suff -> : (i.+1 - a).-2 < b by rewrite if_same.
rewrite -subn2 !ltn_subLR //; last by rewrite i1aE.
rewrite add2n -addSnnS [X in _ < X]H2.
have := ltn_ord i; rewrite leq_eqVlt => /orP[/eqP HH|//].
by case/eqP: iDcc; rewrite -[in RHS]HH.
Qed.


Lemma halfDlt i a : (i./2 < a) = (i < a + a).
Proof.
apply/idP/idP => [|iLaa]; last first.
  rewrite -ltn_double -!addnn (leq_ltn_trans _ iLaa) //.
  by rewrite addnn -[X in _ <= X]odd_double_half leq_addl.
rewrite -leq_double -addnn addnS addnn => /(leq_ltn_trans _)-> //.
rewrite addSn -add1n -[X in X <= _]odd_double_half addnn leq_add2r.
by case: odd.
Qed.

Lemma halfDle i a : (a <= i./2) = (a + a <= i).
Proof. by rewrite leqNgt halfDlt -leqNgt. Qed.

Lemma eocat_nseq_nseq (A : eqType) (v : A) a b :
  eocat (nseq a v) (nseq b v) = nseq (a + a) v.
Proof.
by elim: a b => // n IH [|b]; rewrite addnS /= ?IH // (IH 0).
Qed.

Lemma eocat_nseq_cat_id (A : eqType) (v1 v2 : A) a b c :
  eocat (nseq a v1 ++ nseq b v2) (nseq a v1 ++ nseq c v2) = 
        (nseq (a + a) v1 ++ nseq (b + b) v2).
Proof.
elim: a b c => // [b c | n IH b c]; first by rewrite eocat_nseq_nseq.
by rewrite addnS /= IH.
Qed.

Lemma nseqS (A : eqType) a (b : A) : nseq a.+1 b = b :: nseq a b.
Proof. by []. Qed.

Lemma eocat_cons (A : eqType) (a b : A) l1 l2 :
  eocat (a :: l1) (b :: l2) = a :: b :: eocat l1 l2.
Proof. by []. Qed.

Lemma cat_cons (A : eqType) (a : A) l1 l2 :
  (a :: l1) ++ l2 = a :: (l1 ++ l2).
Proof. by []. Qed.

Lemma eocat_nseq_catS (A : eqType) (v1 v2 : A) a b :
  eocat (nseq a.+1 v1 ++ nseq b v2) (nseq a v1 ++ nseq b.+1 v2) = 
        (nseq (a + a).+1 v1 ++ nseq (b + b).+1 v2).
Proof.
elim: a b => // [b | a IH b].
  by case: b => //= b; rewrite eocat_nseq_nseq [(_ + _)%Nrec]addnS.
by rewrite addnS (nseqS a) (nseqS a.+1) 2!(cat_cons v1) eocat_cons IH.
Qed.

Lemma eocat_nseq_catSS (A : eqType) (v1 v2 : A) a b :
  eocat (nseq a.+2 v1 ++ nseq b v2) (nseq a v1 ++ nseq b.+2 v2) = 
        (nseq (a + a).+1 v1 ++ v2 :: v1 :: nseq (b + b).+1 v2).
Proof.
elim: a b => // [b | a IH b].
  by case: b => //= b; rewrite eocat_nseq_nseq [(_ + _)%Nrec]addnS.
by rewrite addnS (nseqS a) (nseqS a.+2) 2!(cat_cons v1) eocat_cons IH.
Qed.

