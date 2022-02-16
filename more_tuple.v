From mathcomp Require Import all_ssreflect perm algebra.zmodp.
From mathcomp Require Import zify.

Import Order POrderTheory TotalTheory.

(******************************************************************************)
(*  Definition of some network sorting algorithms                             *)
(*                                                                            *)
(*         `2^ m == 2 ^ n so that                                             *)
(*                  `2^ m.+1 = `2^ m + `2^ m is true by reduction             *)
(*       ipred i == i.-1                                                      *)
(*       inext i == i.+1 when possible otherwise i                            *)
(*      isub k i == i - k when k <= i otherwise i                             *)
(*      iadd k i == i.+ k when possible otherwise i                           *)
(*       olift t == odd lift : move n of 'I_m into n.*2.+1 in 'I_(m + m)      *)
(*       elift t == even lift : move n of 'I_m into n.*2 in 'I_(m + m)        *)
(*       olift t == odd lift : move n of 'I_m into n.*2.+1 in 'I_(m + m)      *)
(*       idiv2 t == div2 on I_n : move n of 'I_(m + m) into n./2 in 'I_m      *)
(*       ttake t == take the left part of a (m + n).-tuple                    *)
(*       tdrop t == take the right part of a (m + n).-tuple                   *)
(*       etake t == take the even part of a sequence                          *)
(*      tetake t == take the even part of a (m + n).-tuple                    *)
(*       otake t == take the odd part of a sequence                           *)
(*      totake t == take the odd part of a (m + n).-tuple                     *)
(*      tmap f t == apply f to the tuple t                                    *)
(*        trev t == get the reverse of a tuple                                *)
(*    leqt t1 t2 == all the elements of t1 are <=%O to their respective       *)
(*                  element in t2                                             *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Missing theorems they should be moved to mathcomo *)
Lemma uphalfE n : uphalf n = n.+1./2.
Proof. by []. Qed.

Lemma ltn_halfl i a : (i./2 < a) = (i < a.*2).
Proof.
apply/idP/idP => [|iLaa]; last first.
  rewrite -ltn_double (leq_ltn_trans _ iLaa) //.
  by rewrite -[X in _ <= X]odd_double_half leq_addl.
rewrite -leq_double doubleS => /(leq_ltn_trans _) -> //.
rewrite -add1n -[X in X <= _]odd_double_half leq_add2r.
by case: odd.
Qed.

Lemma geq_halfr i a : (a <= i./2) = (a.*2 <= i).
Proof. by rewrite leqNgt ltn_halfl -leqNgt. Qed.

Lemma leq_halfl n m : n <= m.*2 -> n./2 <= m.
Proof.
by move => nLm2; rewrite -{1}(doubleK m); apply: half_leq.
Qed.

Lemma half_gtnn n : (n./2 < n) = (n != 0).
Proof.
case: n => // [] [|n] //.
rewrite eqn_leq [n.+2 <= _]leqNgt -[X in _ < X]odd_double_half -addnn addnA.
by rewrite /= [~~ _ + _]addnS addSn !ltnS leq_addl.
Qed.

Section E2.

(* We define an explicte function `2^ n = 2 ^ n so that `2^ n.+1 reduces      *)
(* to `2^ m + `2^ m                                                           *)

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

Lemma ltn_ne2n n : n < `2^ n.
Proof.
elim: n => // [] [|n] // IH.
apply: leq_ltn_trans (_ : n.+1.*2 < _).
  by rewrite -addnn addnS addSn !ltnS leq_addr.
by rewrite e2Sn addnn ltn_double.
Qed.

Lemma leq_uphalf_e2n n m : n <= `2^ m.+1 -> uphalf n <= `2^ m.
Proof.
rewrite -{1}(odd_double_half n) uphalf_half e2Sn addnn.
by case: odd; rewrite //= ?add1n ?ltn_double // leq_double.
Qed.

Lemma e2n_div2 n : 0 < n -> (`2^ n)./2 = `2^ n.-1.
Proof. by case: n => // n _; rewrite e2Sn addnn doubleK. Qed.

Lemma dvdn_e2n m n : (`2^ m %| `2^ n) = (m <= n).
Proof.
elim: n m => [[|m]//=|n IH [/=|m]].
- rewrite dvdn1.
  by rewrite eqn_leq leqNgt -add1n !addnn leq_double e2n_gt0.
- by rewrite dvd1n.
by rewrite !e2Sn !addnn -!muln2 dvdn_pmul2r // IH.
Qed.

Lemma e2nD m n : `2^ (m + n) = `2^ m * (`2^ n).
Proof.
elim: m => /= [|m IH]; first by rewrite mul1n.
by rewrite !addnn -doubleMl IH.
Qed.


Lemma ltn_e2n m n : (`2^ m < `2^ n) = (m < n).
Proof.
elim: n m => [/= [|m]//|n IH [|m]].
- by rewrite ltnS; case: e2n (e2n_gt0 m.+1).
- by rewrite !e2Sn !addnn (leq_double 1) e2n_gt0.
by rewrite !e2Sn !addnn ltn_double IH.
Qed.

Lemma leq_e2n m n : (`2^ m <= `2^ n) = (m <= n).
Proof.
elim: n m => [/= [|m]//|n IH [|m]].
- by rewrite e2Sn; case: e2n (e2n_gt0 m) => //= n; rewrite addnS.
- rewrite (leq_trans _ (_ : `2^ 1 <= `2^ n.+1)) //.
  by rewrite !e2Sn !addnn (leq_double 1) e2n_gt0.
by rewrite !e2Sn !addnn leq_double IH.
Qed.

End E2.

Notation "`2^ n" := (e2n n) (at level 40).

Section Sorted.

Lemma isorted_consF l : sorted <=%O (false :: l) = sorted <=%O (l).
Proof. by elim: l. Qed.

Lemma dsorted_consF l : sorted >=%O (false :: l) = (l == nseq (size l) false).
Proof. by elim: l => // [[]] //= [|[]]. Qed.

Lemma isorted_consT l : sorted <=%O (true :: l) = (l == nseq (size l) true).
Proof. by elim: l => // [[]] //= [|[]]. Qed.

Lemma dsorted_consT l : sorted >=%O (true :: l) = sorted >=%O l.
Proof. by elim: l => //= [[]]. Qed.

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

Variable d : unit.
Variable A : orderType d.

Lemma tsorted01 n (t : n.-tuple A) : n <= 1 -> sorted <=%O t.
Proof. 
case: n t => [|[|//]]; first by do 2 case.
by case => [] [] // a [] // b [] //= i; rewrite !(tnth_nth a) /= andbT.
Qed.

Lemma tsorted2 (t : 2.-tuple A) :
  sorted <=%O t = (tnth t ord0 <= tnth t ord_max)%O.
Proof.
by case: t => [] [] // a [] // b [] //= i; rewrite !(tnth_nth a) /= andbT.
Qed.

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

End Sorted.

Section MoreIn.

Definition inext m : 'I_m -> 'I_m := 
  if m is m1.+1 then fun i => inZp (if i == m1 :> nat then i : nat else i.+1)
  else fun i => i.

Lemma val_inext m (i : 'I_m) : 
  inext i = if i == m.-1 :> nat then i : nat else i.+1 :> nat.
Proof.
case: m i => [[]//|n i /=].
have:= (ltn_ord i); rewrite ltnS leq_eqVlt.
by case: eqP => [->|_] /= iLn; rewrite modn_small.
Qed.

Definition ipred m : 'I_m -> 'I_m := 
  if m is m1.+1 then fun i => inZp (i.-1) else fun i => i.

Lemma val_ipred m (i : 'I_m) : ipred i = i.-1 :> nat.
Proof.
case: m i => [[]//|n i /=].
by rewrite modn_small // (leq_ltn_trans (leq_pred _) (ltn_ord i)).
Qed.

Definition iadd m k : 'I_m -> 'I_m := 
  if m is m1.+1 then fun i => inZp (if k + i <= m1 then k + i else i)
  else fun i => i.

Lemma val_iadd m (i : 'I_m) k : 
  iadd k i = if k + i < m then k + i else i :> nat.
Proof.
case: m i => [[]//|n i /=]; have iLn := ltn_ord i.
by rewrite modn_small ?ltnS //=; case: (leqP (k + i)).
Qed.

Lemma inextE m (i : 'I_m) : inext i = iadd 1 i.
Proof.
apply/val_eqP; rewrite /= val_inext val_iadd.
have := ltn_ord i; rewrite leq_eqVlt => /orP[/eqP iE|iLm].
  by rewrite -[X in X.-1]iE /= eqxx -[X in _ < X]iE ltnn.
rewrite iLm [_ == _.-1]eqn_leq [_.-1 <= _]leqNgt.
by rewrite -[i < _]ltnS prednK ?iLm ?andbF // (ltn_trans _ iLm).
Qed.

Definition isub m k : 'I_m -> 'I_m := 
  if m is m1.+1 then fun i => inZp (if k <= i then i - k else i)
  else fun i => i.

Lemma val_isub m (i : 'I_m) k : isub k i = if k <= i then i - k else i :> nat.
Proof.
case: m i => [[]//|n i /=]; have iLn := ltn_ord i.
rewrite modn_small //=; case: (leqP k) => // _.
apply: leq_ltn_trans _ iLn.
by rewrite -[X in _ <= X]subn0 leq_sub.
Qed.

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

Definition elift m : 'I_m -> 'I_(m + m) := 
  if m is m1.+1 then fun i => inZp (i.*2) else fun i => i.

Lemma val_elift m (i : 'I_m) : elift i = i.*2 :> nat.
Proof.
case: m i => [[]//|m i].
by rewrite -[LHS]/(i.*2 %% (m.+1 + m.+1)) modn_small // addnn ltn_double.
Qed.

Definition olift m : 'I_m -> 'I_(m + m) := 
  if m is m1.+1 then fun i => inZp (i.*2.+1) else fun i => i.

Lemma val_olift m (i : 'I_m) : olift i = i.*2.+1 :> nat.
Proof.
case: m i => [[]//|m i].
rewrite -[LHS]/(i.*2.+1 %% (m.+1 + m.+1)) modn_small //.
by rewrite addnS addSn !ltnS addnn leq_double -ltnS.
Qed.

Definition idiv2 m : 'I_(m + m) -> 'I_m := 
  if m is m1.+1 then fun i => inZp (i./2) else fun i => i.

Lemma val_idiv2 m (i : 'I_(m + m)) : idiv2 i = i./2 :> nat.
Proof.
case: m i => [[]//|n i /=].
rewrite modn_small // -ltn_double -[X in _ < X]addnn.
rewrite (leq_ltn_trans _ (ltn_ord i)) //.
by rewrite -[X in _ <= X]odd_double_half leq_addl.
Qed.

Lemma oliftK m (i : 'I_m) : idiv2 (olift i) = i.
Proof.
apply/val_eqP; rewrite /= val_idiv2 /= val_olift.
by rewrite -divn2 -muln2 -addn1 divnMDl // addn0.
Qed.

Lemma idiv2K_odd m (i : 'I_(m + m)) : odd i -> olift (idiv2 i) = i.
Proof.
move=> iO.
apply/val_eqP; rewrite /= val_olift /= val_idiv2.
by rewrite -[X in _ == X]odd_double_half iO.
Qed.

Lemma idiv2K_even m (i : 'I_(m + m)) : ~~ odd i -> elift (idiv2 i) = i.
Proof.
move=> iO.
apply/val_eqP; rewrite /= val_elift /= val_idiv2.
by rewrite -[X in _ == X]odd_double_half (negPf iO).
Qed.

Lemma eliftK m (i : 'I_m) : idiv2 (elift i) = i.
Proof.
by apply/val_eqP; rewrite /= val_idiv2 /= val_elift doubleK.
Qed.

End MoreIn.

Section Tuple.

Variable A : eqType.

Lemma ttake_proof m1 m2 : minn m1 (m1 + m2) = m1.
Proof. by rewrite minnC minnE [m1 + m2]addnC addnK [m2 + m1]addnC addnK. Qed.

Lemma tdrop_proof m1 m2 : (m1 + m2) - m1 = m2.
Proof. by rewrite addnC addnK. Qed.

Definition ttake (T : Type) (m1 m2 : nat) (t : (m1 + m2).-tuple T) :=
  tcast (ttake_proof m1 m2) [tuple of take m1 t].

Lemma ttakeE (T : Type) (m1 m2 : nat) (t : (m1 + m2).-tuple T) : 
  ttake t = take m1 t :> seq T.
Proof. by rewrite val_tcast. Qed.

Lemma ttakeK m1 m2 (t1 : m1.-tuple A) (t2 : m2.-tuple A) :
  ttake [tuple of t1 ++ t2] = t1.
Proof.
apply/val_eqP => /=.
by rewrite ttakeE take_cat size_tuple ltnn subnn /= take0 cats0.
Qed.

Definition tdrop m1 m2 (t : (m1 + m2).-tuple A) :=
  tcast (tdrop_proof m1 m2) [tuple of drop m1 t].

Lemma tdropE m1 m2 (t : (m1 + m2).-tuple A) : tdrop t = drop m1 t :> seq A.
Proof. by rewrite val_tcast. Qed.

Lemma tdropK m1 m2 (t1 : m1.-tuple A) (t2 : m2.-tuple A) : 
  tdrop [tuple of t1 ++ t2] = t2.
Proof.
apply/val_eqP => /=.
by rewrite tdropE drop_cat size_tuple ltnn subnn /= drop0.
Qed.

Lemma cat_ttake_tdrop m (t : (m + m).-tuple A) : 
  t = [tuple of ttake t ++ tdrop t].
Proof. by apply/val_eqP; rewrite /= ttakeE tdropE; rewrite cat_take_drop. Qed.

Definition trev (T : Type) m (t : m.-tuple T) := [tuple of rev t].

Fixpoint etake (T : Type) (l : seq T) :=
  if l is a :: l1 then a :: (if l1 is _ :: l2 then etake l2 else [::])
  else [::].

Definition otake (T : Type) (l : seq T) := 
  if l is _ :: l1 then etake l1 else [::].

Lemma etake_cons (T : Type) a (l : seq T) : etake (a :: l) = a :: otake l.
Proof. by []. Qed.

Lemma otake_cons (T : Type) a (l : seq T) : otake (a :: l) = etake l.
Proof. by []. Qed.

Lemma nth_etake (T : Type) a (l : seq T) n : nth a (etake l) n = nth a l n.*2.
Proof.
have [m leMm] := ubnP (size l);
    elim: m l leMm n => [[]//|m IH [|b [|c l]]] HS n.
- by rewrite /= !nth_nil.
- by case: n => [|n]; rewrite //= nth_nil.
rewrite etake_cons otake_cons; case: n => //= n.
rewrite ltnS in HS.
by apply: IH; apply: leq_trans HS => /=.
Qed.

Lemma nth_otake (T : Type) a (l : seq T) n :
  nth a (otake l) n = nth a l n.*2.+1.
Proof.
by case: l; rewrite //= ?nth_nil // => _ l; rewrite nth_etake.
Qed.

Lemma size_etake (T : Type) (l : seq T) : size (etake l) = uphalf (size l).
Proof.
have [n leMn] := ubnP (size l); elim: n l leMn => // n IH [|a [|bl]] //= l.
rewrite !ltnS => slLn.
by rewrite IH //= (leq_trans _ slLn).
Qed.

Lemma etake_tupleP m (T : Type) (t : (m + m).-tuple T) : size (etake t) == m.
Proof. by rewrite size_etake size_tuple /= addnn uphalf_double. Qed.
Canonical etake_tuple (T : Type) m (t : (m + m).-tuple T) :=
  Tuple (etake_tupleP t).

Lemma size_otake (T : Type) (l : seq T) : size (otake l) = (size l)./2.
Proof. by case: l => //= a l; rewrite size_etake. Qed.

Lemma otake_tupleP (T : Type) m (t : (m + m).-tuple T) : size (otake t) == m.
Proof. by rewrite size_otake size_tuple addnn doubleK. Qed.
Canonical otake_tuple (T : Type) m (t : (m + m).-tuple T) :=
  Tuple (otake_tupleP t).

Lemma etake_nseq (T : Type) i (a : T) : etake (nseq i a) = nseq (uphalf i) a.
Proof.
have [n leMi] := ubnP i; elim: n i leMi => // n IH [|[|i]] //= iLn.
by rewrite IH // -ltnS (leq_trans _ iLn).
Qed.

Lemma otake_nseq i (T : Type) (a : T) : otake (nseq i a) = nseq i./2 a.
Proof. by case: i => //= i; exact: etake_nseq. Qed.

Lemma etake_cat (T : Type) (l1 l2 : seq T) : 
  etake (l1 ++ l2) = etake l1 ++ if odd (size l1) then otake l2 else etake l2.
Proof.
have [n leMl1] := ubnP (size l1).
elim: n l1 leMl1 => // n IH [|a[|b l1]] //= slLn.
by rewrite negbK IH // -ltnS (leq_trans _ slLn).
Qed.

Lemma otake_cat (T : Type) (l1 l2 : seq T) : 
  otake (l1 ++ l2) = otake l1 ++ if odd (size l1) then etake l2 else otake l2.
Proof. by case: l1 => // a l; rewrite /= if_neg etake_cat. Qed.

Lemma etake_cat_nseq (T : Type) (a1 a2 : T) m1 m2 : 
  etake (nseq m1 a1 ++ nseq m2 a2) = 
  nseq (uphalf m1) a1 ++ nseq (~~odd m1 + m2)./2 a2.
Proof.
by rewrite etake_cat !etake_nseq otake_nseq size_nseq; case: (odd m1).
Qed.

Lemma otake_cat_nseq (T : Type) (a1 a2 : T) m1 m2 : 
  otake (nseq m1 a1 ++ nseq m2 a2) = 
  nseq m1./2 a1 ++ nseq (odd m1 + m2)./2 a2.
Proof.
by rewrite otake_cat !otake_nseq etake_nseq size_nseq; case: (odd m1).
Qed.

Lemma etake_sorted (leA : rel A) (s : seq A) :
  transitive leA -> sorted leA s -> sorted leA (etake s).
Proof.
move=> leA_trans.
have [n leMs] := ubnP (size s).
elim: n s leMs => // k IH [|a [|b [| c s]]] // H1 H2.
rewrite /= in H2; have /and3P[aLb bLc cPs] := H2.
suff : leA a c && sorted leA (etake (c :: s)) by [].
rewrite (leA_trans _ _ _ aLb bLc) // IH //=.
by rewrite /= ltnS in H1; rewrite (leq_ltn_trans _ H1).
Qed.

Lemma otake_sorted (leA : rel A) (s : seq A) :
  transitive leA -> sorted leA s -> sorted leA (otake s).
Proof.
move=> leT_trans; case: s => //= a s sS.
by apply: etake_sorted => //; case: s sS => //= b l /andP[].
Qed.

Lemma eq_size_etake (T :  Type) (l1 l2 : seq T) :
  size l1 = size l2 -> size (etake l1) = size (etake l2).
Proof.
have [k leMl] := ubnP (size l1).
elim: k l1 l2 leMl => // k IH [|a [|b l1]] [|c [|d l2]] //= sl1Lk [] /IH -> //.
by rewrite -ltnS ltnW.
Qed.

Lemma eq_size_otake (T : Type) (l1 l2 : seq T) :
  size l1 = size l2 -> size (otake l1) = size (otake l2).
Proof.
by case: l1; case: l2 => //= b l2 a l1 [] /eq_size_etake.
Qed.

Definition tetake (T : Type) (m : nat) (t : (m + m).-tuple T) :=
  [tuple of etake t].
Definition totake (T : Type) (m : nat) (t : (m + m).-tuple T) := 
  [tuple of otake t].

Lemma tetakeE (T : Type) (m : nat) (t : (m + m).-tuple T) :
  tetake t = etake t :> seq T.
Proof. by []. Qed.

Lemma totakeE (T : Type) (m : nat) (t : (m + m).-tuple T) :
  totake t = otake t :> seq T.
Proof. by []. Qed.

Fixpoint eocat (T : Type) (l1 l2 : seq T) :=
  if l1 is a :: l3 then a :: head a l2 :: eocat l3 (behead l2) else [::].

Lemma size_eocat (T : Type) (l1 l2 : seq T) :
  size (eocat l1 l2) = (size l1 + size l1).
Proof. by elim: l1 l2 => //= a l1 IH l2; rewrite IH addnS. Qed.

Lemma nth_eocat (T : Type) a (l1 l2 : seq T) n : 
  size l1 = size l2 ->
  nth a (eocat l1 l2) n = nth a (if odd n then l2 else l1) n./2.
Proof.
elim: l1 l2 n => /= [[]//= n|b l1 IH [//= n|c l2 [|[|n]] //= [Hs]/=]].
  by rewrite if_same !nth_nil.
by rewrite negbK IH; case: odd.
Qed.

Lemma eocat_cat (T : Type) (l1 l2 l3 l4 : seq T) :
  ~~ odd (size l1) -> size l1 = size l3 -> 
  eocat (l1 ++ l2) (l3 ++ l4) = eocat l1 l3 ++ eocat l2 l4.
Proof.
have [n leMl1] := ubnP (size l1).
elim: n l1 l3 leMl1 => //= n IH [|a[|b l1]] [|c[|d l3]] //=.
rewrite !ltnS negbK => sl1Ln sl1O [sl1E].
by rewrite IH // (leq_ltn_trans _ sl1Ln).
Qed.

Lemma eocat_etake_otake (T : Type) n (l : seq T) :
  size l = n + n -> eocat (etake l) (otake l) = l.
Proof.
elim: n l =>[[]// | n IH [//|a [|b l]]]; rewrite !addnS //.
by rewrite !(etake_cons, otake_cons) /= => [] [H]; rewrite IH.
Qed.

Lemma etakeK (T : Type) (l1 l2 : seq T) : etake (eocat l1 l2) = l1.
Proof. by elim: l1 l2 => //= a l IH l2; rewrite IH. Qed.

Lemma otakeK (T : Type) (l1 l2 : seq T) :
  size l1 = size l2 -> otake (eocat l1 l2) = l2.
Proof.
elim: l1 l2 => [[]//|a l1 IH [|b l2] //].
by rewrite [eocat _ _]/= otake_cons etake_cons /= => [] [/IH->].
Qed.

Lemma etake_eocat (T : Type) (l1 l2 : seq T) :  etake (eocat l1 l2) = l1.
Proof.
have [n leMl1] := ubnP (size l1).
elim: n l1 leMl1 l2 => // n IH [|a[|b l1]] //= slLn l2.
by rewrite IH // -ltnS (leq_trans _ slLn).
Qed.

Lemma otake_eocat (T : Type) (l1 l2 : seq T) :
  size l1 = size l2 -> otake (eocat l1 l2) = l2.
Proof.
elim: l1 l2 => [|a l1 IH] l2; first by case: l2.
case: l2 => [//|b l2].
by rewrite [eocat _ _]/= otake_cons etake_cons => [] [/IH->].
Qed.

Lemma eocat_nseqD (T : Type) (v : T) a b :
  eocat (nseq a v) (nseq b v) = nseq (a + a) v.
Proof. by elim: a b => // n IH [|b]; rewrite addnS /= ?IH // (IH 0).  Qed.

Lemma eocat_nseq_catD (T : Type) (v1 v2 : T) a b c :
  eocat (nseq a v1 ++ nseq b v2) (nseq a v1 ++ nseq c v2) = 
        (nseq (a + a) v1 ++ nseq (b + b) v2).
Proof.
elim: a b c => // [b c | n IH b c]; first by rewrite eocat_nseqD.
by rewrite addnS /= IH.
Qed.

Lemma nseqS (T : Type) a (b : T) : nseq a.+1 b = b :: nseq a b.
Proof. by []. Qed.

Lemma cat_cons (T : Type) (a : T) l1 l2 : (a :: l1) ++ l2 = a :: (l1 ++ l2).
Proof. by []. Qed.

Lemma eocat_cons (T : Type) (a b : T) l1 l2 :
  eocat (a :: l1) (b :: l2) = a :: b :: eocat l1 l2.
Proof. by []. Qed.

Lemma eocat_nseq_catDS (T : Type) (v1 v2 : T) a b :
  eocat (nseq a.+1 v1 ++ nseq b v2) (nseq a v1 ++ nseq b.+1 v2) = 
        (nseq (a + a).+1 v1 ++ nseq (b + b).+1 v2).
Proof.
elim: a b => // [b | a IH b].
  by case: b => //= b; rewrite eocat_nseqD [(_ + _)%Nrec]addnS.
by rewrite addnS (nseqS a) (nseqS a.+1) 2!(cat_cons v1) eocat_cons IH.
Qed.

Lemma eocat_nseq_catDSS (T : Type) (v1 v2 : T) a b :
  eocat (nseq a.+2 v1 ++ nseq b v2) (nseq a v1 ++ nseq b.+2 v2) = 
        (nseq (a + a).+1 v1 ++ v2 :: v1 :: nseq (b + b).+1 v2).
Proof.
elim: a b => // [b | a IH b].
  by case: b => //= b; rewrite eocat_nseqD [(_ + _)%Nrec]addnS.
by rewrite addnS (nseqS a) (nseqS a.+2) 2!(cat_cons v1) eocat_cons IH.
Qed.

Lemma nth_cat_seqT a b i : nth true (nseq a false ++ nseq b true) i = (a <= i). 
Proof.
by rewrite nth_cat !nth_nseq !size_nseq if_same; case: leqP.
Qed.

Lemma nseq_cat_sortedE (l : seq bool) m1 m2 m3 m4 : 
  sorted (<=%O) l ->  
  perm_eq l (nseq m1 false ++ nseq m2 true ++ nseq m3 false ++ nseq m4 true) ->
  l = nseq (m1 + m3) false ++ nseq (m2 + m4) true.
Proof.
move=> /isorted_boolP[[u v] ->] /allP; set l1 := _ ++ _ => permH.
congr (nseq _ _ ++ nseq _ _).
  have [/permH/=|] := boolP (false \in l1).
    by rewrite !(count_cat, count_nseq) /= !(mul0n, mul1n, addn0, add0n) =>/eqP.
  by rewrite !(mem_cat, mem_nseq) /= eqxx !negb_or /=; 
     case: (m1) => [|k1];  case: (m3) => [|k2]; rewrite ?(andbF, andbT) //; 
     case: (u).
have [/permH/=|] := boolP (true \in l1).
  by rewrite !(count_cat, count_nseq) /= !(mul0n, mul1n, addn0, add0n) =>/eqP.
by rewrite !(mem_cat, mem_nseq) /= eqxx !negb_or /=; 
   case: (m2) => [|k1];  case: (m4) => [|k2]; rewrite ?(andbF, andbT) //; 
   case: (v).
Qed.

Lemma take_etakeE (T : Type) (l : seq T) :
  ~~ odd (size l) ->   ~~ odd (size l)./2 -> 
  take (size l)./2./2 (etake l) = etake (take (size l)./2 l).
Proof.
move=> H1 H2.
pose l1 := take (size l)./2 l; pose l2 := drop (size l)./2 l.
pose l3 := etake l; pose l4 := otake l.
have lE : l = l1 ++ l2 by rewrite cat_take_drop.
have sl1E : size l1 = (size l)./2 by rewrite size_take half_gtnn; case: size.
rewrite -/l1.
rewrite {2}lE etake_cat sl1E (negPf H2).
rewrite take_cat size_etake sl1E.
by rewrite uphalf_half (negPf H2) /= ltnn subnn take0 cats0.
Qed.

Lemma ttake_etakeE n (t : ((n + n) + (n + n)).-tuple A) :
  ttake (tetake t) = tetake (ttake t).
Proof.
apply/val_eqP; rewrite /= !(ttakeE, tetakeE).
have nnE : n + n = (size t)./2.
  by rewrite size_tuple /= [in RHS]addnn doubleK.
rewrite [X in _ == _ (_ X _)]nnE.
have nE : n = (size t)./2./2.
  by rewrite size_tuple /= !addnn !doubleK.
rewrite [X in take X _]nE take_etakeE //.
  by rewrite size_tuple /= addnn odd_double.
by rewrite -nnE addnn odd_double.
Qed.

Lemma take_otakeE (T : Type) (l : seq T) :
  ~~ odd (size l) ->   ~~ odd (size l)./2 -> 
  take (size l)./2./2 (otake l) = otake (take (size l)./2 l).
Proof.
move=> H1 H2.
pose l1 := take (size l)./2 l; pose l2 := drop (size l)./2 l.
pose l3 := etake l; pose l4 := otake l.
have lE : l = l1 ++ l2 by rewrite cat_take_drop.
have sl1E : size l1 = (size l)./2 by rewrite size_take half_gtnn; case: size.
rewrite -/l1.
rewrite {2}lE otake_cat sl1E (negPf H2).
rewrite take_cat size_otake sl1E.
by rewrite ltnn subnn take0 cats0.
Qed.

Lemma ttake_otakeE n (t : ((n + n) + (n + n)).-tuple A) :
  ttake (totake t) = totake (ttake t).
Proof.
apply/val_eqP; rewrite /= !(ttakeE, totakeE).
have nnE : n + n = (size t)./2.
  by rewrite size_tuple /= [in RHS]addnn doubleK.
rewrite [X in _ == _ (_ X _)]nnE.
have nE : n = (size t)./2./2.
  by rewrite size_tuple /= !addnn !doubleK.
rewrite [X in take X _]nE take_otakeE //.
  by rewrite size_tuple /= addnn odd_double.
by rewrite -nnE addnn odd_double.
Qed.

Lemma drop_etakeE (T : Type) (l : seq T) :
  ~~ odd (size l) ->   ~~ odd (size l)./2 -> 
  drop (size l)./2./2 (etake l) = etake (drop (size l)./2 l).
Proof.
move=> H1 H2.
pose l1 := take (size l)./2 l; pose l2 := drop (size l)./2 l.
pose l3 := etake l; pose l4 := otake l.
have lE : l = l1 ++ l2 by rewrite cat_take_drop.
have sl1E : size l1 = (size l)./2.
  by rewrite size_take half_gtnn; case: size.
rewrite -/l2.
rewrite {2}lE etake_cat sl1E (negPf H2).
rewrite drop_cat size_etake sl1E.
by rewrite uphalf_half (negPf H2) /= ltnn subnn drop0.
Qed.

Lemma tdrop_etakeE n (t : ((n + n) + (n + n)).-tuple A) :
  tdrop (tetake t) = tetake (tdrop t).
Proof.
apply/val_eqP; rewrite /= !(tdropE, tetakeE).
have nnE : n + n = (size t)./2.
  by rewrite size_tuple /= [in RHS]addnn doubleK.
rewrite [X in _ == _ (_ X _)]nnE.
have nE : n = (size t)./2./2.
  by rewrite size_tuple /= !addnn !doubleK.
rewrite [X in drop X _]nE drop_etakeE //.
  by rewrite size_tuple /= addnn odd_double.
by rewrite -nnE addnn odd_double.
Qed.

Lemma drop_otakeE (T : Type) (l : seq T) :
  ~~ odd (size l) ->   ~~ odd (size l)./2 -> 
  drop (size l)./2./2 (otake l) = otake (drop (size l)./2 l).
Proof.
move=> H1 H2.
pose l1 := take (size l)./2 l; pose l2 := drop (size l)./2 l.
pose l3 := etake l; pose l4 := otake l.
have lE : l = l1 ++ l2 by rewrite cat_take_drop.
have sl1E : size l1 = (size l)./2.
  by rewrite size_take half_gtnn; case: size.
rewrite -/l2.
rewrite {2}lE otake_cat sl1E (negPf H2).
by rewrite drop_cat size_otake sl1E ltnn subnn drop0.
Qed.

Lemma tdrop_otakeE n (t : ((n + n) + (n + n)).-tuple A) :
  tdrop (totake t) = totake (tdrop t).
Proof.
apply/val_eqP; rewrite /= !(tdropE, totakeE).
have nnE : n + n = (size t)./2.
  by rewrite size_tuple /= [in RHS]addnn doubleK.
rewrite [X in _ == _ (_ X _)]nnE.
have nE : n = (size t)./2./2.
  by rewrite size_tuple /= !addnn !doubleK.
rewrite [X in drop X _]nE drop_otakeE //.
  by rewrite size_tuple /= addnn odd_double.
by rewrite -nnE addnn odd_double.
Qed.

Lemma eocat_tupleP (T : Type) m1 m2 (t1 : m1.-tuple T) (t2 : m2.-tuple T) :
  size (eocat t1 t2) == m1 + m1.
Proof. by rewrite size_eocat size_tuple. Qed.
Canonical eocat_tuple (T : Type) m1 m2 (t1 : m1.-tuple T) (t2 : m2.-tuple T) :=
  Tuple (eocat_tupleP t1 t2).

Lemma eocat_tetake_totake (T : eqType) n (t : (n + n).-tuple T) : 
  t = [tuple of eocat (tetake t) (totake t)].
Proof. 
by apply/val_eqP; rewrite /= (@eocat_etake_otake T n) // size_tuple.
Qed.

Lemma tetakeK (T : eqType) (m : nat) (t1 t2 : m.-tuple T) : 
  tetake [tuple of eocat t1 t2] = t1.
Proof.
by apply/val_eqP; rewrite /= tetakeE /= etake_eocat.
Qed.

Lemma totakeK (T : eqType) (m : nat) (t1 t2 : m.-tuple T) : 
  totake [tuple of eocat t1 t2] = t2.
Proof.
by apply/val_eqP; rewrite /= totakeE /= otake_eocat // !size_tuple.
Qed.

End Tuple.

Section TMap.
Variable m : nat.
Variables A B : Type.
Variable f : A -> B.

Definition tmap t := [tuple f (tnth t i) | i < m].

Lemma val_tmap t : tmap t = map f t :> seq B.
Proof.
have -> : tmap t = [tuple of [seq f (tnth t i) | i <- ord_tuple m]].
  by apply: eq_from_tnth => i; rewrite !(tnth_map, tnth_ord_tuple).
congr tval.
by apply: eq_from_tnth => i; rewrite !(tnth_map, tnth_ord_tuple).
Qed.

End TMap.

Section LeqT.

Variable d : unit.
Variable A : orderType d.

Definition leqt m (t1 t2 : m.-tuple A) :=
  [forall a : 'I_m, forall b : 'I_m, 
    (a <= b) ==> (tnth t1 a <= tnth t1 b)%O ==> (tnth t2 a <= tnth t2 b)%O].

Lemma leqtP m (t1 t2 : m.-tuple A) :
  reflect 
  (forall a b : 'I_m, a <= b ->
                (tnth t1 a <= tnth t1 b)%O -> (tnth t2 a <= tnth t2 b)%O)
  (leqt t1 t2).
Proof.
apply: (iffP forallP) => [H a b aLb t1aLt1b|H a].
  by have /forallP/(_ b) := H a; rewrite aLb t1aLt1b.
by apply/forallP=> b; case: leqP => //= aLb; apply/implyP/H.
Qed.

Lemma leqtc m : reflexive (@leqt m).
Proof. by move=>t; apply/leqtP. Qed.

Lemma leqt_trans m : transitive (@leqt m).
Proof.
move=>t2 t1 t3 /leqtP Ht1t2 /leqtP Ht2t3.
apply/leqtP => a b aLb t2aLt2b.
by apply: Ht2t3 => //; apply: Ht1t2.
Qed.

Lemma leqt_sorted m (t1 t2 : m.-tuple A) : sorted (>%O) t1 -> leqt t1 t2.
Proof.
move=> sS; apply/leqtP => a b.
rewrite leq_eqVlt => /orP[/val_eqP->//|aLb].
pose v := tnth t1 a; rewrite leNgt !(tnth_nth v).
by rewrite -DualPOrder.ltEdual lt_sorted_ltn_nth ?(aLb, inE, size_tuple).
Qed.

End LeqT.


Section MinMax.

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

Variable m : nat.
Variable d1 d2 : unit.
Variable A : orderType d1.
Variable B : orderType d2.
Variable f : A -> B.


Lemma min_homo : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} -> {morph f : x y / min x y}.
Proof.
(move=> fH x y; case: (leP (f x)) => [fxLfy|fyLfx]; case: leP => //).
  by rewrite lt_neqAle => /andP[_ /fH]; case: ltgtP fxLfy.
by move=> /fH; case: ltgtP fyLfx.
Qed.

Lemma max_homo : 
  {homo f : x y / (x <= y)%O >-> (x <= y)%O} -> {morph f : x y / max x y}.
Proof.
(move=> fH x y; case: (leP (f x)) => [fxLfy|fyLfx]; case: leP => //).
  by rewrite lt_neqAle => /andP[_ /fH]; case: ltgtP fxLfy.
by move=> /fH; case: ltgtP fyLfx.
Qed.

End MinMax.

