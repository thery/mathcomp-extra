(******************************************************************************)
(*                                                                            *)
(* disarium n  ==  n is equal to the sum of its decimal digits, each raised  *)
(*                 to its position counted from the left starting at 1        *)
(*                 (89 = 8 ^ 1 + 9 ^ 2, 135 = 1 ^ 1 + 3 ^ 2 + 5 ^ 3)          *)
(*                 The digits are the ones of digitn and ndigits (digitn.v),  *)
(*                 so 0 has the single digit 0 and is a disarium number.      *)
(*                                                                            *)
(* This file shows that there are only 20 disarium numbers (disariumE):       *)
(*   0 1 2 3 4 5 6 7 8 9 89 135 175 518 598 1306 1676 2427 2646798            *)
(*   12157692622039623539                                                     *)
(*                                                                            *)
(* - disarium_bound : a disarium number has at most 22 digits, since for      *)
(*   k >= 23 digits the sum is at most 9 + 9 ^ 2 + ... + 9 ^ k < 10 ^ (k - 1) *)
(* - with k digits d_j (j counted from the right), n is a disarium number iff *)
(*   the sum of the c_j(d_j) is 0, with c_j(d) = d * 10 ^ j - d ^ (k - j).    *)
(*   dsearch k computes the solutions by branch and bound: the positions are  *)
(*   sorted by decreasing spread, a branch is cut when the partial sum plus   *)
(*   the minimum (maximum) of the remaining contributions is positive         *)
(*   (negative), and the sums of the last 6 positions are looked up in a      *)
(*   precomputed table, a persistent array of 2 ^ 20 buckets indexed by the   *)
(*   low bits of the sum (a Uint63). search_complete proves that the cut and  *)
(*   the table lose no solution, so dsearch k contains all the solutions.     *)
(* - dsearch_ok runs the 22 searches with vm_compute (several minutes).       *)
(*                                                                            *)
(******************************************************************************)

From HB Require Import structures.
From Stdlib Require Import ZArith Lia Uint63.
From Stdlib Require PArray.
From mathcomp Require Import boot.
Require Import digitn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Z_eqP : Equality.axiom Z.eqb.
Proof. by move=> x y; case: Z.eqb_spec; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build Z Z_eqP.

Lemma int_eqP : Equality.axiom PrimInt63.eqb.
Proof.
move=> x y; apply: (iffP idP) => [/eqb_spec //|xy]; exact/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build int int_eqP.

HB.instance Definition _ :=
  Monoid.isComLaw.Build Z 0%Z Z.add Z.add_assoc Z.add_comm Z.add_0_l.

Definition disarium := [qualify a n |
  \sum_(i < ndigits 10 n) digitn 10 n i ^ (ndigits 10 n - i) == n].

(* The search: the options of a position are triples (c, c mod 2^63, v)      *)
(* where c is the contribution to the sum and v the contribution to n.       *)

Definition opt := (Z * int * Z)%type.
Definition oc (o : opt) := o.1.1.
Definition om (o : opt) := o.1.2.
Definition ov (o : opt) := o.2.

Definition bmin (l : seq opt) :=
  if l is o :: l' then foldr (fun o m => Z.min (oc o) m) (oc o) l' else 0%Z.
Definition bmax (l : seq opt) :=
  if l is o :: l' then foldr (fun o m => Z.max (oc o) m) (oc o) l' else 0%Z.

Definition mask : int := 1048575%uint63.
Definition key (x : int) := PrimInt63.land x mask.

(* The table lives above Set so that the PArray axioms apply to it *)
Local Unset Universe Minimization ToSet.
Definition table := PArray.array (seq (int * int)).

Fixpoint fill (tp : seq (seq (int * int))) (cm vm : int) (a : table) :=
  if tp is ch :: tp' then
    foldl (fun a o => fill tp' (cm + o.1) (vm + o.2) a) a ch
  else let i := key cm in PArray.set a i ((cm, vm) :: PArray.get a i).

Definition level := (seq opt * Z * Z)%type.

Definition cut (s mn mx : Z) := (0 <? s + mn)%Z || (s + mx <? 0)%Z.

Definition lookup (t : int) (vs : Z) (b : seq (int * int)) :=
  [seq (vs + to_Z e.2)%Z | e <- b & PrimInt63.eqb e.1 t].

Section Go.
Variables (tbl : table) (tmin tmax : Z).
Fixpoint go (lv : seq level) (s : Z) (sm : int) (vs : Z) : seq Z :=
  if lv is (ch, mn, mx) :: lv' then
    if cut s mn mx then [::] else
    flatten [seq go lv' (s + oc o) (sm + om o) (vs + ov o) | o <- ch]
  else if cut s tmin tmax then [::] else
    let t := (0 - sm)%uint63 in lookup t vs (PArray.get tbl (key t)).
End Go.

Definition sumb (f : seq opt -> Z) (l : seq (seq opt)) :=
  foldr (fun ch s => f ch + s)%Z 0%Z l.

Definition build (tmin tmax : Z) (top : seq (seq opt)) : seq level :=
  foldr (fun ch lv =>
     let: (mn, mx) := if lv is (_, mn, mx) :: _ then (mn, mx) else (tmin, tmax)
     in (ch, mn + bmin ch, mx + bmax ch)%Z :: lv) [::] top.

Definition tconv (l : seq opt) := [seq (om o, Uint63.of_Z (ov o)) | o <- l].

Definition vmax (l : seq opt) := foldr (fun o m => Z.max (ov o) m) 0%Z l.
Definition vpos (l : seq opt) := all (fun o => 0 <=? ov o)%Z l.

Definition search (t : nat) (L : seq (seq opt)) : option (seq Z) :=
  let top := take (size L - t) L in
  let tab := drop (size L - t) L in
  if all vpos tab && (sumb vmax tab <? wB)%Z then
    let tmin := sumb bmin tab in
    let tmax := sumb bmax tab in
    let tbl := fill (map tconv tab) 0 0 (PArray.make (mask + 1) [::]) in
    Some (go tbl tmin tmax (build tmin tmax top) 0 0 0)
  else None.

(* Disarium numbers with k digits: position j (from the right) of digit d    *)
(* contributes d 10^j - d^(k-j) to the sum, the leading digit is not 0      *)
Definition cval (k j d : nat) : Z :=
  (Z.of_nat d * 10 ^ Z.of_nat j - Z.of_nat d ^ Z.of_nat (k - j))%Z.
Definition vval (j d : nat) : Z := (Z.of_nat d * 10 ^ Z.of_nat j)%Z.
Definition mkopt (k j d : nat) : opt :=
  let c := cval k j d in (c, Uint63.of_Z c, vval j d).
Definition digits_of (k j : nat) :=
  if (j == k.-1) && (1 < k) then iota 1 9 else iota 0 10.
Definition opts k j := [seq mkopt k j d | d <- digits_of k j].
Definition spread (l : seq opt) := (bmax l - bmin l)%Z.
Definition order k :=
  sort (fun i j => spread (opts k j) <=? spread (opts k i))%Z (iota 0 k).
Definition dsearch k := search 6 [seq opts k j | j <- order k].

(* Completeness of the search *)

Definition sumc (xs : seq opt) := foldr (fun x s => oc x + s)%Z 0%Z xs.
Definition sumv (xs : seq opt) := foldr (fun x s => ov x + s)%Z 0%Z xs.
Definition chosen (xs : seq opt) (L : seq (seq opt)) :=
  all2 (fun x l => x \in l) xs L.
Definition wfo (o : opt) := om o == Uint63.of_Z (oc o).

Lemma bmin_le l x : x \in l -> (bmin l <= oc x)%Z.
Proof.
case: l => // o l; rewrite /bmin.
have F a : (foldr (fun o m => Z.min (oc o) m) a l <= a)%Z.
  by elim: l => /= [|o1 l IH]; lia.
rewrite in_cons => /orP[/eqP->|]; first exact: F.
by elim: l {F} => // o1 l IH; rewrite in_cons => /orP[/eqP->|/IH] /=; lia.
Qed.

Lemma bmax_ge l x : x \in l -> (oc x <= bmax l)%Z.
Proof.
case: l => // o l; rewrite /bmax.
have F a : (a <= foldr (fun o m => Z.max (oc o) m) a l)%Z.
  by elim: l => /= [|o1 l IH]; lia.
rewrite in_cons => /orP[/eqP->|]; first exact: F.
by elim: l {F} => // o1 l IH; rewrite in_cons => /orP[/eqP->|/IH] /=; lia.
Qed.

Lemma vmax_ge l x : x \in l -> (ov x <= vmax l)%Z.
Proof.
by elim: l => // o l IH; rewrite in_cons /= => /orP[/eqP->|/IH]; lia.
Qed.

Lemma sumc_bounds xs L :
  chosen xs L -> (sumb bmin L <= sumc xs <= sumb bmax L)%Z.
Proof.
elim: xs L => [|x xs IH] [|l L] //= /andP[xl /IH].
by have := bmin_le xl; have := bmax_ge xl; lia.
Qed.

Lemma sumv_bounds xs L :
  chosen xs L -> all vpos L -> (0 <= sumv xs <= sumb vmax L)%Z.
Proof.
elim: xs L => [|x xs IH] [|l L] //= /andP[xl /IH xsP] /andP[lP LP].
have := vmax_ge xl; have /Z.leb_le := allP lP _ xl; have := xsP LP; lia.
Qed.

Lemma chosen_all (P : pred opt) xs L :
  chosen xs L -> all (all P) L -> all P xs.
Proof.
elim: xs L => [|x xs IH] [|l L] //= /andP[xl /IH xsP] /andP[lP LP].
by rewrite (allP lP _ xl) xsP.
Qed.

Lemma chosen_take_drop m xs L :
  chosen xs L -> chosen (take m xs) (take m L) && chosen (drop m xs) (drop m L).
Proof.
rewrite /chosen; elim: xs L m => [|x xs IH] [|l L] [|m] //= /andP[xl xsL].
by rewrite xl; apply: IH.
Qed.

Lemma sumc_cat xs1 xs2 : sumc (xs1 ++ xs2) = (sumc xs1 + sumc xs2)%Z.
Proof. by elim: xs1 => //= x xs1 ->; lia. Qed.

Lemma sumv_cat xs1 xs2 : sumv (xs1 ++ xs2) = (sumv xs1 + sumv xs2)%Z.
Proof. by elim: xs1 => //= x xs1 ->; lia. Qed.

Lemma of_ZD a b : Uint63.of_Z (a + b) = (Uint63.of_Z a + Uint63.of_Z b)%uint63.
Proof. by apply: to_Z_inj; rewrite add_spec !of_Z_spec Zplus_mod. Qed.

Lemma of_ZN a : Uint63.of_Z (- a) = (0 - Uint63.of_Z a)%uint63.
Proof.
apply: to_Z_inj; rewrite sub_spec !of_Z_spec Zminus_mod_idemp_r.
by rewrite -Z.sub_0_l.
Qed.

Lemma add0i x : (0 + x)%uint63 = x.
Proof.
apply: to_Z_inj; rewrite add_spec Z.add_0_l Z.mod_small //.
exact: to_Z_bounded.
Qed.

Lemma addi0 x : (x + 0)%uint63 = x.
Proof.
apply: to_Z_inj; rewrite add_spec Z.add_0_r Z.mod_small //.
exact: to_Z_bounded.
Qed.

Lemma key_lt x : (key x <? mask + 1)%uint63 = true.
Proof.
apply/ltb_spec; rewrite land_spec' (_ : to_Z mask = Z.ones 20) //.
rewrite Z.land_ones // (_ : to_Z (mask + 1) = 2 ^ 20)%Z //.
by have := Z.mod_pos_bound (to_Z x) (2 ^ 20); lia.
Qed.

Lemma fill_length tp cm vm a :
  PArray.length (fill tp cm vm a) = PArray.length a.
Proof.
elim: tp cm vm a => [|ch tp IH] cm vm a /=; first by rewrite PArray.length_set.
by elim: ch a => //= o ch IHch a; rewrite IHch IH.
Qed.

Lemma fill_mono tp cm vm a j e :
  e \in PArray.get a j -> e \in PArray.get (fill tp cm vm a) j.
Proof.
elim: tp cm vm a => [|ch tp IH] cm vm a /=; last first.
  by elim: ch a => //= o ch IHch a He; apply: IHch; apply: IH.
have [<- eI|/eqP kj] := eqVneq (key cm) j; last by rewrite PArray.get_set_other.
case: (boolP (key cm <? PArray.length a)%uint63) => [kL|/negbTE kNL].
  by rewrite PArray.get_set_same // in_cons eI orbT.
rewrite PArray.get_out_of_bounds ?PArray.length_set //.
by rewrite PArray.default_set -(PArray.get_out_of_bounds _ _ _ kNL).
Qed.

Lemma fill_complete tp ys cm vm a :
  PArray.length a = (mask + 1)%uint63 -> all2 (fun y l => y \in l) ys tp ->
  let s1 := foldr (fun y s => y.1 + s)%uint63 0%uint63 ys in
  let s2 := foldr (fun y s => y.2 + s)%uint63 0%uint63 ys in
  (cm + s1, vm + s2)%uint63 \in PArray.get (fill tp cm vm a) (key (cm + s1)).
Proof.
elim: tp ys cm vm a => [|ch tp IH] [|y ys] cm vm a aL //=.
  rewrite !addi0 PArray.get_set_same ?mem_head //.
  by rewrite aL key_lt.
case/andP=> yI yA.
elim: ch a aL yI => // o ch IHch a aL; rewrite in_cons => /orP[/eqP<-|yI] /=.
  apply: (fill_mono (ch :: tp)); rewrite !add_assoc.
  exact: IH.
by apply: IHch => //; rewrite fill_length.
Qed.

Lemma build_cons tmin tmax ch top :
  build tmin tmax (ch :: top) =
  (ch, sumb bmin (ch :: top) + tmin, sumb bmax (ch :: top) + tmax)%Z
     :: build tmin tmax top.
Proof.
elim: top ch => [|ch1 top IH] ch.
  by rewrite /= !Z.add_0_r Z.add_comm (Z.add_comm (bmax _)).
move: (IH ch1); rewrite /build /= => ->.
by congr ((_, _, _) :: _); lia.
Qed.

Lemma go_complete tbl tmin tmax top xs2 :
  all (all wfo) top ->
  (tmin <= sumc xs2 <= tmax)%Z -> (0 <= sumv xs2 < wB)%Z ->
  (Uint63.of_Z (sumc xs2), Uint63.of_Z (sumv xs2)) \in
     PArray.get tbl (key (Uint63.of_Z (sumc xs2))) ->
  forall xs1 s sm vs, chosen xs1 top -> sm = Uint63.of_Z s ->
  (s + sumc xs1 + sumc xs2 = 0)%Z ->
  (vs + sumv xs1 + sumv xs2)%Z \in
    go tbl tmin tmax (build tmin tmax top) s sm vs.
Proof.
move=> wf cB vB tE xs1.
elim: top xs1 wf => [|ch top IH] [|x xs1] // wf s sm vs;
  last rewrite build_cons /=.
  move=> _ smE /= sE; rewrite /= /cut.
  have -> : (0 <? s + tmin)%Z = false by apply/Z.ltb_ge; lia.
  have -> : (s + tmax <? 0)%Z = false by apply/Z.ltb_ge; lia.
  apply/mapP; exists (Uint63.of_Z (sumc xs2), Uint63.of_Z (sumv xs2)).
    rewrite smE -of_ZN.
    have -> : (- s = sumc xs2)%Z by lia.
    by rewrite mem_filter /= eqb_refl.
  by rewrite /= of_Z_spec Z.mod_small //; lia.
case/andP: wf => wfch wf.
rewrite /chosen /= => /andP[xI xsI] smE sE.
have /= := sumc_bounds xsI.
rewrite /cut => sB.
have := bmin_le xI; have := bmax_ge xI => xB1 xB2.
have -> : (0 <? s + (bmin ch + sumb bmin top + tmin))%Z = false.
  by apply/Z.ltb_ge; lia.
have -> : (s + (bmax ch + sumb bmax top + tmax) <? 0)%Z = false.
  by apply/Z.ltb_ge; lia.
apply/flatten_mapP; exists x => //.
have -> : (vs + (ov x + sumv xs1) = (vs + ov x) + sumv xs1)%Z by lia.
apply: IH => //.
  by rewrite smE (eqP (allP wfch _ xI)) of_ZD.
by lia.
Qed.

Lemma search_complete t L xs r :
  all (all wfo) L -> search t L = Some r -> chosen xs L -> sumc xs = 0%Z ->
  sumv xs \in r.
Proof.
move=> wf; rewrite /search; set m := size L - t.
case: ifP => [/andP[vP /Z.ltb_lt vB]|_]; last by [].
have aL : PArray.length (PArray.make (mask + 1) ([::] : seq (int * int))) =
          (mask + 1)%uint63 by rewrite PArray.length_make.
move: (PArray.make _ _) aL => a0 aL [<-] xsL xs0.
have /andP[xs1L xs2L] := chosen_take_drop m xsL.
have wfd : all (all wfo) (drop m L).
  by apply/allP => l /mem_drop lI; exact: (allP wf).
have wft : all (all wfo) (take m L).
  by apply/allP => l /mem_take lI; exact: (allP wf).
have wfx := chosen_all xs2L wfd.
have [cB1 cB2] := sumc_bounds xs2L.
have [vB1 vB2] := sumv_bounds xs2L vP.
rewrite -(cat_take_drop m xs) sumv_cat -[X in X \in _]Z.add_0_l Z.add_assoc.
apply: go_complete => //; first by lia.
  have := @fill_complete [seq tconv i | i <- drop m L]
            [seq (om o, Uint63.of_Z (ov o)) | o <- drop m xs] 0 0 a0 aL.
  cbv zeta; rewrite !add0i.
  have -> : foldr (fun y s => y.1 + s)%uint63 0%uint63
              [seq (om o, Uint63.of_Z (ov o)) | o <- drop m xs] =
            Uint63.of_Z (sumc (drop m xs)).
    elim: (drop m xs) wfx => //= x xs' IH /andP[/eqP-> /IH->].
    by rewrite -of_ZD.
  have -> : foldr (fun y s => y.2 + s)%uint63 0%uint63
              [seq (om o, Uint63.of_Z (ov o)) | o <- drop m xs] =
            Uint63.of_Z (sumv (drop m xs)).
    by elim: (drop m xs) => //= x xs' ->; rewrite -of_ZD.
  apply.
  elim: (drop m xs) (drop m L) xs2L => [|x xs' IH] [|l L'] //=.
  by case/andP => xl /IH ->; rewrite andbT /tconv map_f.
by rewrite -sumc_cat cat_take_drop; lia.
Qed.

Lemma natpowE m e : m ^ e = Nat.pow m e.
Proof. by elim: e => // e IH; rewrite expnS IH. Qed.

Lemma Z_of_nat_pow m e : Z.of_nat (m ^ e) = (Z.of_nat m ^ Z.of_nat e)%Z.
Proof. by rewrite natpowE Nat2Z.inj_pow. Qed.

Lemma Z_of_nat_sum (I : Type) (r : seq I) (F : I -> nat) :
  Z.of_nat (\sum_(i <- r) F i) = \big[Z.add/0%Z]_(i <- r) Z.of_nat (F i).
Proof. by apply: (big_morph Z.of_nat) => // a b; exact: Nat2Z.inj_add. Qed.

Lemma sumc_mkopt k f s :
  sumc [seq mkopt k j (f j) | j <- s] = \big[Z.add/0%Z]_(j <- s) cval k j (f j).
Proof. by elim: s => [|j s IH]; rewrite ?big_nil ?big_cons //= IH. Qed.

Lemma sumv_mkopt k f s :
  sumv [seq mkopt k j (f j) | j <- s] = \big[Z.add/0%Z]_(j <- s) vval j (f j).
Proof. by elim: s => [|j s IH]; rewrite ?big_nil ?big_cons //= IH. Qed.

Lemma chosen_map (f : nat -> opt) (g : nat -> seq opt) s :
  (forall j, j \in s -> f j \in g j) ->
  chosen [seq f j | j <- s] [seq g j | j <- s].
Proof.
rewrite /chosen; elim: s => //= j s IH H.
by rewrite H ?mem_head // IH // => i iI; apply: H; rewrite in_cons iI orbT.
Qed.

Lemma dsearch_complete k n r :
  ndigits 10 n = k -> n \is a disarium -> dsearch k = Some r ->
  Z.of_nat n \in r.
Proof.
move=> nk nD dE.
pose d j := digitn 10 n j.
have nE := digitnE_ndigits n (isT : 1 < 10).
have pS : perm_eq (order k) (iota 0 k) by rewrite /order perm_sort perm_refl.
have iE : iota 0 k = index_iota 0 k by rewrite /index_iota subn0.
have sv : \big[Z.add/0%Z]_(i < k) vval i (d i) = Z.of_nat n.
  rewrite [in RHS]nE nk Z_of_nat_sum; apply: eq_bigr => j _.
  by rewrite /vval Nat2Z.inj_mul Z_of_nat_pow.
have := @search_complete _ _ [seq mkopt k j (d j) | j <- order k] _ _ dE.
rewrite sumv_mkopt (perm_big _ pS) /= iE big_mkord sv; apply.
- apply/allP => l /mapP[j _ ->]; apply/allP => o /mapP[e _ ->].
  by rewrite /wfo eqxx.
- apply: chosen_map => j; rewrite mem_sort mem_iota /= => jk.
  apply: map_f; rewrite /digits_of; case: ifP => [/andP[/eqP jE k1]|_].
    rewrite mem_iota ltn_digitn // andbT lt0n; apply/eqP => dj.
    have := @digitn_ndigits_pred 10 n (isT : 1 < 10).
    by rewrite nk -jE => /(_ dj) n0; move: k1; rewrite -nk n0 ndigits0.
  by rewrite mem_iota ltn_digitn.
rewrite sumc_mkopt (perm_big _ pS) /= iE big_mkord.
have -> : \big[Z.add/0%Z]_(i < k) cval k i (d i) =
          \big[Z.add/0%Z]_(i < k) (vval i (d i) + - Z.of_nat (d i ^ (k - i)))%Z.
  by apply: eq_bigr => i _; rewrite /cval Z_of_nat_pow.
rewrite big_split /= sv -(big_morph Z.opp Z.opp_add_distr (erefl : - 0 = 0)%Z).
by rewrite -Z_of_nat_sum -nk (eqP nD); lia.
Qed.


(* A disarium number has at most 22 digits *)

Lemma sum_exp9 k : (\sum_(i < k) 9 ^ (k - i)) * 8 + 9 = 9 ^ k.+1.
Proof.
elim: k => [|k IH]; first by rewrite big_ord0.
rewrite big_ord_recl subn0 mulnDl -addnA.
under eq_bigr => i _ do rewrite subSS.
by rewrite IH -mulnSr -expnSr.
Qed.

Lemma ltn_Zpow a e b c f :
  (Z.of_nat a ^ Z.of_nat e < Z.of_nat b * Z.of_nat c ^ Z.of_nat f)%Z ->
  a ^ e < b * c ^ f.
Proof.
by move=> H; apply/ltP/Nat2Z.inj_lt; rewrite Nat2Z.inj_mul !Z_of_nat_pow.
Qed.

Lemma ltn_exp9 k : 22 < k -> 9 ^ k.+1 < 8 * 10 ^ k.-1.
Proof.
move=> kL; rewrite -(subnK kL); set m := k - 23.
have -> : (m + 23).-1 = m + 22 by rewrite addnS.
rewrite -addnS !expnD mulnCA.
apply: leq_ltn_trans (_ : 10 ^ m * 9 ^ 24 < _).
  apply: leq_mul (leqnn _).
  by elim: (m) => // e IH; rewrite !expnS leq_mul.
have p10 : 0 < 10 ^ m by rewrite expn_gt0.
rewrite (ltn_pmul2l p10).
by apply: ltn_Zpow.
Qed.

Lemma disarium_bound n : n \is a disarium -> ndigits 10 n <= 22.
Proof.
move=> nD; rewrite leqNgt; apply/negP => kL.
have n_pos : 0 < n by case: n nD kL => //; rewrite ndigits0.
have l1 : 10 ^ (ndigits 10 n).-1 <= n := ndigits_leq (isT : 1 < 10) n_pos.
have l2 : \sum_(i < ndigits 10 n) digitn 10 n i ^ (ndigits 10 n - i) <=
          \sum_(i < ndigits 10 n) 9 ^ (ndigits 10 n - i).
  apply: leq_sum => i _; rewrite leq_exp2r ?subn_gt0 //.
  by rewrite -ltnS ltn_digitn.
have := ltn_exp9 kL; rewrite -sum_exp9 ltnNge => /negP[].
apply: leq_trans (_ : 8 * n <= _); first by rewrite leq_mul2l l1 orbT.
rewrite -[in X in X <= _](eqP nD) mulnC.
by apply: leq_trans (leq_addr _ _); rewrite leq_mul2r l2 orbT.
Qed.

(* Checking that a given number is a disarium *)

Fixpoint zdigits_rec (f : nat) (z : Z) : seq nat :=
  if f is f1.+1 then
    Z.to_nat (z mod 10) ::
      (if (z / 10 =? 0)%Z then [::] else zdigits_rec f1 (z / 10))
  else [::].

Definition zdigits z := zdigits_rec 64 z.

Definition zsum (F : nat -> Z) k := foldr (fun j s => F j + s)%Z 0%Z (iota 0 k).

Lemma Z_of_nat_sum_ord k (F : nat -> nat) :
  Z.of_nat (\sum_(j < k) F j) = zsum (fun j => Z.of_nat (F j)) k.
Proof.
rewrite -(big_mkord xpredT) /index_iota subn0 /zsum.
elim: (iota 0 k) => [|j r IH]; rewrite ?big_nil ?big_cons //=.
by rewrite Nat2Z.inj_add IH.
Qed.

Lemma eq_zsum (F G : nat -> Z) k : F =1 G -> zsum F k = zsum G k.
Proof.
by move=> FG; rewrite /zsum; elim: (iota 0 k) => //= j r ->; rewrite FG.
Qed.

Definition zcheck (z : Z) :=
  let ds := zdigits z in
  let k := size ds in
  [&& 0 < k, all (fun d => d < 10) ds, (k == 1) || (nth 0 ds k.-1 != 0),
      zsum (fun j => Z.of_nat (nth 0%N ds j) * 10 ^ Z.of_nat j)%Z k == z &
      zsum (fun j => Z.of_nat (nth 0%N ds j) ^ Z.of_nat (k - j))%Z k == z].

Lemma disarium_digits (ds : seq nat) :
  0 < size ds -> all (fun d => d < 10) ds ->
  (size ds == 1) || (nth 0 ds (size ds).-1 != 0) ->
  (\sum_(j < size ds) nth 0 ds j * 10 ^ j \is a disarium) =
  (\sum_(j < size ds) nth 0 ds j ^ (size ds - j) ==
   \sum_(j < size ds) nth 0 ds j * 10 ^ j).
Proof.
move=> sP dsP lP.
set k := size ds in sP lP *; set n := \sum_(j < k) _.
have fB j : j < k -> nth 0 ds j < 10.
  by move=> jk; apply: (allP dsP); rewrite mem_nth.
have nB : n < 10 ^ k.
  rewrite -[10 ^ k]prednK ?expn_gt0 // ltnS predX_sum.
  by apply: leq_sum => j _; rewrite leq_mul2r -ltnS fB ?orbT.
have nk : ndigits 10 n = k.
  case/orP: lP => [/eqP k1|lP].
    by move: nB; rewrite k1 expn1 => nB; exact: ndigits_small.
  have nL : 10 ^ k.-1 <= n.
    rewrite /n; case: (k) sP lP => // k1 _ lP; rewrite big_ord_recr /=.
    by apply: leq_trans (leq_addl _ _); rewrite leq_pmull // lt0n.
  have n_pos : 0 < n by apply: leq_trans nL; rewrite expn_gt0.
  by apply: ndigits_eq; rewrite ?nL.
rewrite qualifE nk; congr (_ == _); apply: eq_bigr => j _.
by rewrite digitn_sum.
Qed.

Lemma zcheck_disarium n : zcheck (Z.of_nat n) -> n \is a disarium.
Proof.
rewrite /zcheck; move: (zdigits _) => ds.
case/and5P => sP dsP lP /eqP vE /eqP dE.
have nE : n = \sum_(j < size ds) nth 0 ds j * 10 ^ j.
  apply: Nat2Z.inj.
  rewrite (Z_of_nat_sum_ord _ (fun j => nth 0 ds j * 10 ^ j)) -vE.
  by apply: eq_zsum => j; rewrite Nat2Z.inj_mul Z_of_nat_pow.
rewrite nE disarium_digits // -nE; apply/eqP/Nat2Z.inj.
rewrite (Z_of_nat_sum_ord _ (fun j => nth 0 ds j ^ (size ds - j))) -dE.
by apply: eq_zsum => j; rewrite Z_of_nat_pow.
Qed.

Fixpoint zuint (d : Decimal.uint) (a : Z) : Z :=
  match d with
  | Decimal.Nil => a
  | Decimal.D0 d => zuint d (10 * a)
  | Decimal.D1 d => zuint d (10 * a + 1)
  | Decimal.D2 d => zuint d (10 * a + 2)
  | Decimal.D3 d => zuint d (10 * a + 3)
  | Decimal.D4 d => zuint d (10 * a + 4)
  | Decimal.D5 d => zuint d (10 * a + 5)
  | Decimal.D6 d => zuint d (10 * a + 6)
  | Decimal.D7 d => zuint d (10 * a + 7)
  | Decimal.D8 d => zuint d (10 * a + 8)
  | Decimal.D9 d => zuint d (10 * a + 9)
  end%Z.

Lemma Z_of_nat_uint_acc d a :
  Z.of_nat (Nat.of_uint_acc d a) = zuint d (Z.of_nat a).
Proof.
elim: d a => //= d IH a; rewrite IH Nat.tail_mul_spec;
  by congr zuint; rewrite ?Nat2Z.inj_succ Nat2Z.inj_mul /=; lia.
Qed.

Lemma Z_of_nat_num d :
  Z.of_nat (Nat.of_num_uint (Number.UIntDecimal d)) = zuint d 0.
Proof. exact: Z_of_nat_uint_acc d 0. Qed.

(* The 22 searches *)

Definition zlist : seq Z := [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 89; 135; 175; 518;
  598; 1306; 1676; 2427; 2646798; 12157692622039623539]%Z.

Lemma zlist_ok : all zcheck zlist.
Proof. by vm_compute. Qed.

Lemma dsearch_ok :
  all (fun k => if dsearch k is Some r then all (fun z => z \in zlist) r
                else false) (iota 1 22).
Proof. by vm_cast_no_check (erefl true). Qed.

Lemma Z_of_nat_numE d z :
  zuint d 0 = z -> Z.of_nat (Nat.of_num_uint (Number.UIntDecimal d)) = z.
Proof. by rewrite Z_of_nat_num. Qed.

Lemma map_eq_cons (f : nat -> Z) x s z zs :
  f x = z -> map f s = zs -> map f (x :: s) = z :: zs.
Proof. by move=> /= <- <-. Qed.

#[warnings="-abstract-large-number"]
Lemma disariumE n :
  (n \is a disarium) =
  (n \in [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 89; 135; 175; 518; 598; 1306; 1676;
             2427; 2646798; 12157692622039623539]).
Proof.
rewrite -[RHS](mem_map Nat2Z.inj); set l := map _ _.
have -> : l = zlist.
  rewrite /l /zlist; do 18 (apply: map_eq_cons; first by []).
  by do 2 (apply: map_eq_cons; first by apply: Z_of_nat_numE; vm_compute).
apply/idP/idP => [nD|/(allP zlist_ok)/zcheck_disarium //].
have /allP/(_ (ndigits 10 n)) := dsearch_ok.
rewrite mem_iota ndigits_gt0 add1n ltnS disarium_bound // => /(_ isT).
case E : dsearch => [r|] // /allP; apply.
exact: dsearch_complete E.
Qed.
