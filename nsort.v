From mathcomp Require Import all_ssreflect perm.

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

Lemma nfun_perm n t : perm_eq (nfun n t) t.
Proof.
elim: n t => //= p n IH t.
by apply: perm_trans (IH _) (nswap_perm _ _).
Qed.

Lemma fun_of_network_empty : nfun nempty =1 id.
Proof. by []. Qed.

End Network.

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

Definition bitonic := [qualify p | 
 [exists r : 'I_(size (p : seq A)), 
  exists n : 'I_(size (p : seq A)), 
  sorted (<=%O) (take n (rot r p)) && sorted (>=%O) (drop n (rot r p))]].

End Bitonic.

Check sorting_sorted.
