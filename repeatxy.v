From HB Require Import structures.
From mathcomp Require Import all_boot.
From Stdlib Require Import NArith.
Require Import digitn.

(******************************************************************************)
(*                                                                            *)
(* A formalisation of the wrong fact                                          *)
(*    If a² ends in the pattern xyxyxyxyxy, then xy is either 21,61 or 84     *)
(*    https://x.com/fermatslibrary/status/2010760010448490722                 *)
(*                                                                            *)
(*    It is 00, 21, 29, 61, 69 or 84                                          *)
(******************************************************************************)

(* 10 digit arithmetic *)

Inductive d10 := dd0 | dd1 | dd2 | dd3 | dd4 | dd5 | dd6 | dd7 | dd8 | dd9.

Inductive dc := nocarry (d : d10) | carry (d : d10).

Definition dadd0 d := nocarry d.

Definition dadd1 d :=
match d with
| dd0 => nocarry dd1
| dd1 => nocarry dd2
| dd2 => nocarry dd3
| dd3 => nocarry dd4
| dd4 => nocarry dd5
| dd5 => nocarry dd6
| dd6 => nocarry dd7
| dd7 => nocarry dd8
| dd8 => nocarry dd9
| dd9 => carry dd0
end.

Definition dadd2 d :=
match d with
| dd0 => nocarry dd2
| dd1 => nocarry dd3
| dd2 => nocarry dd4
| dd3 => nocarry dd5
| dd4 => nocarry dd6
| dd5 => nocarry dd7
| dd6 => nocarry dd8
| dd7 => nocarry dd9
| dd8 => carry dd0
| dd9 => carry dd1
end.

Definition dadd3 d :=
match d with
| dd0 => nocarry dd3
| dd1 => nocarry dd4
| dd2 => nocarry dd5
| dd3 => nocarry dd6
| dd4 => nocarry dd7
| dd5 => nocarry dd8
| dd6 => nocarry dd9
| dd7 => carry dd0
| dd8 => carry dd1
| dd9 => carry dd2
end.

Definition dadd4 d :=
match d with
| dd0 => nocarry dd4
| dd1 => nocarry dd5
| dd2 => nocarry dd6
| dd3 => nocarry dd7
| dd4 => nocarry dd8
| dd5 => nocarry dd9
| dd6 => carry dd0
| dd7 => carry dd1
| dd8 => carry dd2
| dd9 => carry dd3
end.

Definition dadd5 d :=
match d with
| dd0 => nocarry dd5
| dd1 => nocarry dd6
| dd2 => nocarry dd7
| dd3 => nocarry dd8
| dd4 => nocarry dd9
| dd5 => carry dd0
| dd6 => carry dd1
| dd7 => carry dd2
| dd8 => carry dd3
| dd9 => carry dd4
end.

Definition dadd6 d :=
match d with
| dd0 => nocarry dd6
| dd1 => nocarry dd7
| dd2 => nocarry dd8
| dd3 => nocarry dd9
| dd4 => carry dd0
| dd5 => carry dd1
| dd6 => carry dd2
| dd7 => carry dd3
| dd8 => carry dd4
| dd9 => carry dd5
end.

Definition dadd7 d :=
match d with
| dd0 => nocarry dd7
| dd1 => nocarry dd8
| dd2 => nocarry dd9
| dd3 => carry dd0
| dd4 => carry dd1
| dd5 => carry dd2
| dd6 => carry dd3
| dd7 => carry dd4
| dd8 => carry dd5
| dd9 => carry dd6
end.

Definition dadd8 d :=
match d with
| dd0 => nocarry dd8
| dd1 => nocarry dd9
| dd2 => carry dd0
| dd3 => carry dd1
| dd4 => carry dd2
| dd5 => carry dd3
| dd6 => carry dd4
| dd7 => carry dd5
| dd8 => carry dd6
| dd9 => carry dd7
end.

Definition dadd9 d :=
match d with
| dd0 => nocarry dd9
| dd1 => carry dd0
| dd2 => carry dd1
| dd3 => carry dd2
| dd4 => carry dd3
| dd5 => carry dd4
| dd6 => carry dd5
| dd7 => carry dd6
| dd8 => carry dd7
| dd9 => carry dd8
end.

Definition dadd_fun d :=
match d with
| dd0 => dadd0
| dd1 => dadd1
| dd2 => dadd2
| dd3 => dadd3
| dd4 => dadd4
| dd5 => dadd5
| dd6 => dadd6
| dd7 => dadd7
| dd8 => dadd8
| dd9 => dadd9
end.

Definition deq d1 d2 := 
match d1 with
| dd0 => match d2 with dd0 => true | _ => false end
| dd1 => match d2 with dd1 => true | _ => false end
| dd2 => match d2 with dd2 => true | _ => false end
| dd3 => match d2 with dd3 => true | _ => false end
| dd4 => match d2 with dd4 => true | _ => false end
| dd5 => match d2 with dd5 => true | _ => false end
| dd6 => match d2 with dd6 => true | _ => false end
| dd7 => match d2 with dd7 => true | _ => false end
| dd8 => match d2 with dd8 => true | _ => false end
| dd9 => match d2 with dd9 => true | _ => false end
end.

Definition nat10 := list d10.

Fixpoint dincr (n : nat10) : nat10 := 
  if n is d :: n1 then
   match dadd1 d with nocarry d1 => d1 :: n1 | carry d1 => d1 :: dincr n1 end
  else [:: dd1].

Fixpoint dadd (n1 n2 : nat10) : nat10 := 
  if n1 is d1 :: n3 then 
    if n2 is d2 :: n4 then 
      match dadd_fun d1 d2 with 
      | nocarry d3 => d3 :: dadd n3 n4
      | carry d3 => d3 :: dadd n3 (dincr n4)
      end
    else n1
  else n2.

Fixpoint natn10 n  : nat10 := 
  if n is n1.+1 then dincr (natn10 n1) else [:: dd0].

Lemma n2n10S n : natn10 (n.+1) = dincr (natn10 n).
Proof. by []. Qed.

Definition dval d :=
match d with
| dd0 => 0
| dd1 => 1
| dd2 => 2
| dd3 => 3
| dd4 => 4
| dd5 => 5
| dd6 => 6
| dd7 => 7
| dd8 => 8
| dd9 => 9
end.

Lemma deqP : Equality.axiom deq.
Proof. by do 2!case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build d10 deqP.

Lemma deqE d1 d2 : deq d1 d2 = (dval d1 == dval d2).
Proof. by case: d1; case: d2. Qed.

Definition ddval d :=
  match d with nocarry d1 => dval d1 | carry d1 => 10 + dval d1 end.

Fixpoint n10nat n := if n is d :: n1 then dval d + 10 * n10nat n1 else 0.

Lemma n10nat_incr n : n10nat (dincr n) =  (n10nat n).+1.
Proof. by elim: n => // [] [] //= l ->; rewrite mulnS. Qed.

Lemma natn10K n : n10nat (natn10 n) = n.
Proof. by elim: n => //= n IH; rewrite n10nat_incr IH. Qed.

Lemma dadd0_correct d : ddval (dadd0 d) = dval d.
Proof. by case: d. Qed.

Lemma dadd1_correct d : ddval (dadd1 d) = 1 + dval d.
Proof. by case: d. Qed.

Lemma dadd2_correct d : ddval (dadd2 d) = 2 + dval d.
Proof. by case: d. Qed.

Lemma dadd3_correct d : ddval (dadd3 d) = 3 + dval d.
Proof. by case: d. Qed.

Lemma dadd4_correct d : ddval (dadd4 d) = 4 + dval d.
Proof. by case: d. Qed.

Lemma dadd5_correct d : ddval (dadd5 d) = 5 + dval d.
Proof. by case: d. Qed.

Lemma dadd6_correct d : ddval (dadd6 d) = 6 + dval d.
Proof. by case: d. Qed.

Lemma dadd7_correct d : ddval (dadd7 d) = 7 + dval d.
Proof. by case: d. Qed.

Lemma dadd8_correct d : ddval (dadd8 d) = 8 + dval d.
Proof. by case: d. Qed.

Lemma dadd9_correct d : ddval (dadd9 d) = 9 + dval d.
Proof. by case: d. Qed.

Lemma n10nat_add n1 n2 : n10nat (dadd n1 n2) = n10nat n1 + n10nat n2.
Proof.
elim: n1 n2 => //= d1 n1 IH [//|d2 n2]; case: d1; rewrite /= ?addn0 //=.
- by rewrite IH add0n [RHS]addnCA mulnDr.
- case E : dadd1 (dadd1_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 1]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 1]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
- case E : dadd2 (dadd2_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 2]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 2]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
- case E : dadd3 (dadd3_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 3]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 3]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
- case E : dadd4 (dadd4_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 4]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 4]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
- case E : dadd5 (dadd5_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 5]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 5]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
- case E : dadd6 (dadd6_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 6]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 6]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
- case E : dadd7 (dadd7_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 7]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 7]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
- case E : dadd8 (dadd8_correct d2) => [d1|d1] /= Ed1.
    by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 8]addnC Ed1.
  rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 8]addnC.
  by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
case E : dadd9 (dadd9_correct d2) => [d1|d1] /= Ed1.
  by rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr IH [_ + 9]addnC Ed1.
rewrite [RHS]addnCA 2![in RHS]addnA -addnA -mulnDr [_ + 9]addnC.
by rewrite IH n10nat_incr addnS mulnS addnA [_ + 10]addnC Ed1.
Qed.

Definition nzero (n : nat10) := all (deq dd0) n.

Lemma nzeroP n : nzero n = (n10nat n == 0).
Proof. by elim: n => //= [] [] //= l IH; rewrite add0n muln_eq0. Qed.

Fixpoint is_repeat p := 
  if p is d1 :: p1 then
    if p1 is d2 :: p2 then
      if p2 is d3 :: p3 then 
        if deq d1 d3 then 
          if p3 is d4 :: p4 then
            if deq d2 d4 then is_repeat p2 else false
          else false
        else false
      else true
    else false
  else true.

Lemma is_repeat_cons d1 d2 d3 d4 p : 
  is_repeat [:: d1, d2, d3, d4 & p] = 
        if deq d1 d3 then 
          if deq d2 d4 then is_repeat [:: d3, d4 & p] else false
        else false.
Proof. by []. Qed.

Lemma is_repeat_digit n p :
  size p = n.*2 -> is_repeat p = 
  [forall i : 'I_n.*2,  digitn 10 (n10nat p) i == digitn 10 (n10nat p) (i %%2)].
Proof.
have dL d : dval d < 10 by case: d.
elim: n p => [|n IH] [|d1 [|d2 [|d3 [|d4 p]]]] H //.
- by apply/sym_equal/forallP => [] [].
- by rewrite -H; apply/sym_equal/forallP => [] [[|[]]].
- by case: H; case: (n).
rewrite is_repeat_cons.
case: deqP => [->|d1Dd3]; last first.
  have Hp: 2 < n.+1.*2 by rewrite -H.
  apply/sym_equal/forallP => /(_ (Ordinal Hp)) /=.
  rewrite ![dval _ + _]addnC !digitnMD //.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  by move => H1; case: d1Dd3; apply/deqP; rewrite deqE eq_sym.
case: deqP => [->|d2Dd4]; last first.
  have Hp: 3 < n.+1.*2 by rewrite -H.
  apply/sym_equal/forallP => /(_ (Ordinal Hp)) /=.
  rewrite ![dval _ + _]addnC !digitnMD //.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  by move => H1; case: d2Dd4; apply/deqP; rewrite deqE eq_sym.
rewrite IH; last by case:H.
apply/forallP/forallP => /= H1.
  case=> [] [|[|]] //= i Hi.
  have Hp: i < n.*2 by [].
  rewrite ![dval _ + _]addnC !digitnMD // -![_ + dval _]addnC.
  have /eqP->/= := (H1 (Ordinal Hp)).
  rewrite -[_.+2 %% 2]/(i %% 2).
  case: (_ %% 2) (ltn_mod i 2) => //= [_| [_|//]].
    rewrite ![dval _ + _]addnC.
    rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
    rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
    by apply/eqP.
  rewrite ![dval _ + _]addnC !digitnMD //.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  by apply/eqP.
move => i.
have Hp: i.+2 < n.+1.*2 by rewrite doubleS !ltnS.
have /= := (H1 (Ordinal Hp)).
rewrite ![dval _ + _]addnC !digitnMD // -![_ + dval _]addnC => /eqP->.
rewrite -[_.+2 %% 2]/(i %% 2).
case: (_ %% 2) (ltn_mod i 2) => //= [_| [_|//]].
  rewrite ![dval _ + _]addnC.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
  by apply/eqP.
rewrite ![dval _ + _]addnC !digitnMD //.
rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
rewrite digitn0 -modnDml modnMr modn_small; last by apply: dL.
by apply/eqP.
Qed.

Fixpoint ntake n p := 
  if n is n1.+1 then
    if p is d :: p1 then d :: ntake n1 p1 else dd0 :: ntake n1 [::]
  else [::].

Lemma ntake_nil n : n10nat (ntake n [::]) = 0.
Proof. by elim: n => //= n ->. Qed.

Lemma size_ntake n p : size (ntake n p) = n.
Proof. by elim: n p => //= n IH [|d p] /=; rewrite IH. Qed.

Lemma n10nat_ntake n p : n10nat (ntake n p) = n10nat p %% (10 ^ n).
Proof.
elim: n p => [p| n IH [|d p]] //=; first by rewrite modn1.
  by rewrite ntake_nil muln0 mod0n.
rewrite IH [in RHS](divn_eq (n10nat p) (10 ^ n)) mulnDr.
rewrite mulnCA -expnS addnCA modnMDl [RHS]modn_small //.
apply: leq_trans (_ : 10  + 10 * (n10nat p %% 10 ^ n) <= _).
  by rewrite ltn_add2r; case: d.
by rewrite -mulnS expnS leq_mul2l ltn_mod expn_gt0.
Qed.

Inductive res :=
  Res : list nat10 -> nat10 -> nat10 -> res.

Definition n_0 : nat10 := [::].
Definition n_2 : nat10 := [:: dd2].

Fixpoint ninsert (n : nat10) (p : seq nat10) : seq nat10 := 
  if p is n1 :: p1 then 
    if n == n1 then p else n1 :: ninsert n p1 
  else [:: n].

Lemma mem_ninsert n p : ninsert n p =i n :: p.
Proof.
elim: p => //= d p IH; case: eqP => [->|nDd] i; rewrite !inE.
  by case: eqP.
by rewrite IH inE; do 2case: eqP.
Qed.

Definition res_step l r := 
 let: Res res ns n := r in
 let ns1 := ntake l (dincr (dadd ns n)) in
 let n1 := ntake l (dadd  n_2 n) in
 let res1 := if is_repeat ns then ninsert (ntake 2 ns) res else res in
 Res res1 ns1 n1.

Definition res_wf a b l r :=
  let: Res vl ns n := r in 
  [/\ size ns = l.+1.*2, n10nat ns = (b * b) %% 10 ^ l.+1.*2,  
    n10nat n = b.*2 %% 10 ^ l.+1.*2 & 
    forall i, a <= i < b ->
    (forall j, j < l.+1.*2 ->  
      digitn 10 (i ^ 2) j = digitn 10 (i ^ 2) (j %% 2)) ->
     (i ^ 2) %% 100 \in map n10nat vl].

Lemma digitn_modn b n i j : 
  0 < b -> i < j -> digitn b (n %% b ^ j) i = digitn b n i.
Proof.
move=> b_gt0 iLj.
rewrite /digitn [in RHS](divn_eq n (b ^ j)).
have Hi : b ^ j = b ^ (j - i) * b ^ i by rewrite -expnD subnK // ltnW.
rewrite {3}Hi mulnA divnMDl ?expn_gt0 ?b_gt0 //.
by rewrite -[_ - _]prednK ?subn_gt0 // expnS mulnCA mulnC modnMDl.
Qed.

Lemma res_step_wf a b l r : 
  res_wf a b l r -> res_wf a b.+1 l (res_step l.+1.*2 r).
Proof.
case: r => il ns n [H1 H2 H3 H4]; split => [|||i /andP[aLi]].
- by rewrite size_ntake.
- rewrite n10nat_ntake n10nat_incr n10nat_add H2 H3.
  rewrite -addn1 -addnA modnDml addnCA modnDml.
  by rewrite mulnS mulSn !addnA addSn addnn addn1 addSn.
- by rewrite n10nat_ntake n10nat_add H3 doubleS modnDmr add2n.
rewrite ltnS leq_eqVlt => /orP[/eqP -> |iLb] Hj; last first.
  suff Hi : (i * i) %% 100  \in [seq n10nat i  | i <- il].
  case: is_repeat; rewrite ?inE //.
    have -> := eq_mem_map _ (mem_ninsert  (ntake 2 ns) il).
    by rewrite /= inE Hi orbT.
  by apply: H4; rewrite ?aLi.
rewrite ifT; last first.
  rewrite (is_repeat_digit l.+1) //.
  apply/forallP => //= [] [j jLl] /=.
  rewrite H2 !digitn_modn //; first by apply/eqP/Hj.
  by apply: leq_trans (_ : 2  <= _); rewrite // ltn_mod.
have -> := eq_mem_map _ (mem_ninsert  (ntake 2 ns) il).
rewrite map_cons inE n10nat_ntake H2 modn_dvdm ?eqxx //.
by rewrite dvdn_exp2l.
Qed.

Definition res_init l := Res [::] (ntake l.+1.*2 n_0) n_0.

Lemma res_init_wf l : res_wf 0 0 l (res_init l).
Proof.
split => //; first by rewrite size_ntake.
  by rewrite n10nat_ntake.
by rewrite mod0n.
Qed.

Definition run_res n := 
  let n1 := n.+1.*2 in 
  N.iter (N.div (N.pow 10%N (N.of_nat n1)) 2 + 1)%N (res_step n1) (res_init n).

Lemma N_add_nat a b : N.to_nat (a + b) = N.to_nat a + N.to_nat b.
Proof. by rewrite N2Nat.inj_add. Qed.

Lemma N_pow_nat a b : N.to_nat (a ^ b) = N.to_nat a ^ N.to_nat b.
Proof.
rewrite N2Nat.inj_pow; elim: (N.to_nat b) => //= n ->.
by rewrite expnS.
Qed.

Lemma N_div_nat a b : N.to_nat (a / b) = N.to_nat a %/ N.to_nat b.
Proof.
rewrite N2Nat.inj_div; case: (N.to_nat b) => // n; set m := N.to_nat _.
apply/sym_equal/(PeanoNat.Nat.div_unique _ _ _ (m %% n.+1)) => //.
  by apply/ltP/ltn_pmod.
by rewrite [LHS](divn_eq m n.+1) mulnC.
Qed.

Lemma run_res_wf n : 
  let n1 := n.+1.*2 in res_wf 0 (10%N ^ n1)./2.+1 n (run_res n).
Proof.
move=> n1.
have -> : (10%N ^ n1)./2.+1 = N.to_nat (10%N ^(N.of_nat n1) / 2 + 1).
  by rewrite N_add_nat addn1 N_div_nat divn2 N_pow_nat Nat2N.id.
pose P k r := res_wf 0  (N.to_nat k) n r.
apply: (N.iter_ind _ (res_step n.+1.*2) (res_init n) P).
  by apply: res_init_wf.
move=> k r H; rewrite /P N2Nat.inj_succ.
by apply: res_step_wf.
Qed.

Definition get_list n := let: Res l _ _ := run_res n in [seq n10nat i | i <- l].

Lemma get_list_correct n i : i <= (10%N ^ n.+1.*2)./2 ->
  (forall j, j < n.+1.*2 ->  digitn 10 (i ^ 2) j = digitn 10 (i ^ 2) (j %%2)) ->
  (i ^ 2) %% 100 \in get_list n.
Proof.
move=> iLp Hf.
rewrite /get_list; case: run_res (run_res_wf n) => /= l n1 n2 [_ _ _ HH].
by apply: HH; rewrite ?ltnS.
Qed.

Lemma modn_sqrB m n : n <= m -> (m - n) ^ 2 = n ^ 2 %[mod m].
Proof.
move=> nLm.
rewrite -sqrnD_sub // -modnXm -(modnDl n m) modnXm.
suff Hp : 4 * (m * n) <= (m + n) ^ 2.
  by rewrite -[in RHS](subnK Hp) -modnDmr mulnCA -modnMml modnn mod0n addn0.
case: ltngtP nLm => // [nLm|->] _.
  by apply: ltnW; rewrite -subn_gt0 sqrnD_sub ?expn_gt0 ?subn_gt0 ?nLm // ltnW.
by rewrite addnn -mul2n expnMn.
Qed.

Lemma get_list_all_correct n i :
  0 < n ->
  (forall j, j < n.+1.*2 ->  digitn 10 (i ^ 2) j = digitn 10 (i ^ 2) (j %%2)) ->
  (i ^ 2) %% 100 \in get_list n.
Proof.
move=> n_pos Hf.
pose i1 := i %% (10  ^ n.+1.*2).
have -> : i ^ 2 %% 100 = i1 ^ 2 %% 100.
  by rewrite -[in RHS]modnXm modn_dvdm ?modnXm // -[100]/(10 ^2) dvdn_exp2l.
have Hf1 j : j < n.+1.*2 -> digitn 10 (i1 ^ 2) j = digitn 10 (i1 ^ 2) (j %% 2).
  move=> jLn.
  rewrite -(digitn_modn _ _ _ _ _ jLn) // modnXm digitn_modn //.
  have j2Ln : j %% 2 < n.+1.*2.
    apply: leq_trans (_ : 1 < _); first by rewrite ltn_mod.
    by case: (n) n_pos.
  rewrite -(digitn_modn _ _ _ _ _ j2Ln) // modnXm digitn_modn //.
  by apply: Hf.
pose i2 := if i1 <= (10%N ^ n.+1.*2)./2  then i1 else 10  ^ n.+1.*2 - i1.
have -> : i1 ^ 2 %% 100 = i2 ^ 2 %% 100.
  rewrite /i2; case: leqP => // nLi1.
  have Hd : 100 %| 10 ^ n.+1.*2 by rewrite -[100]/(10 ^2) dvdn_exp2l.
  rewrite -[in RHS](modn_dvdm _ Hd) modn_sqrB ?modn_dvdm //.
  by rewrite ltnW // ltn_pmod ?expn_gt0.
apply: get_list_correct.
  rewrite /i2; case: (leqP i1) => // nLi1.
  rewrite leq_subLR -[X in X <= _]even_halfK.
    by rewrite -addnn leq_add2r ltnW.
  by rewrite oddX orbF.
move=> j jLn.
rewrite /i2; case: (leqP i1) => // i1Ln; first by apply: Hf1.
rewrite -(digitn_modn _ _ _ _ _ jLn) // modn_sqrB //; last first.
  by rewrite ltnW // ltn_pmod // expn_gt0.
rewrite digitn_modn //.
have j2Ln : j %% 2 < n.+1.*2.
  apply: leq_trans (_ : 1 < _); first by rewrite ltn_mod.
  by case: (n) n_pos.
rewrite -(digitn_modn _ _ _ _ _ j2Ln) // modn_sqrB //; last first.
  by rewrite ltnW // ltn_pmod // expn_gt0.
rewrite digitn_modn //.
by apply: Hf1.
Qed.

Lemma get_list_all_correct4 i :
  (forall j, j < 4 ->  digitn 10 (i ^ 2) j = digitn 10 (i ^ 2) (j %%2)) ->
  (i ^ 2) %% 100 \in [:: 00; 04; 16; 21; 29; 36; 61; 64; 69; 84; 96].
Proof.
move=> Hf.
pose l := [:: 00;  04; 16; 96; 36; 61; 64; 84; 69; 29; 21].
have -> : [:: 00;  04; 16; 21; 29; 36; 61; 64; 69; 84; 96] =i l.
  by move=> j; rewrite !inE; do 11 (case:eqP => //).
have -> : l = get_list 1 by vm_cast_no_check (refl_equal l).
by apply: get_list_all_correct.
Qed.
    
Lemma get_list_all_correct6 i :
  (forall j, j < 6 ->  digitn 10 (i ^ 2) j = digitn 10 (i ^ 2) (j %%2)) ->
  (i ^ 2) %% 100 \in [:: 00; 16; 21; 29; 61; 64; 69; 84].
Proof.
move=> Hf.
pose l := [:: 00;  16;  64;  61;  29;  84;  21;  69].
have -> : [:: 00; 16; 21; 29; 61; 64; 69; 84] =i l.
  by move=> j; rewrite !inE; do 8 (case:eqP => //).
have -> : l = get_list 2 by vm_cast_no_check (refl_equal l).
by apply: get_list_all_correct.
Qed.

Lemma get_list_all_correct8 i :
  (forall j, j < 8 ->  digitn 10 (i ^ 2) j = digitn 10 (i ^ 2) (j %%2)) ->
  (i ^ 2) %% 100 \in [:: 00; 21; 29; 61; 64; 69; 84].
Proof.
move=> Hf.
pose l := [:: 00; 64; 21; 84; 69; 29; 61].
have -> : [:: 00; 21; 29; 61; 64; 69; 84] =i l.
   move=> j; rewrite !inE; do 7 (case:eqP => //).
have -> : l = get_list 3 by vm_cast_no_check (refl_equal l).
by apply: get_list_all_correct.
Qed.

(* 21 *)
Compute (508853989 ^ 2)%N.
(* 29 *)
Compute (162459327 ^ 2)%N.
(* 61 *)
Compute (1318820881 ^ 2)%N.
(* 69 *)
Compute (541713187 ^ 2)%N.
(* 84 *)
Compute (509895478 ^ 2)%N.

(*

(* This takes 3 hours *)

Lemma get_list_all_correct10 i :
  (forall j, j < 10 ->  digitn 10 (i ^ 2) j = digitn 10 (i ^ 2) (j %%2)) ->
  (i ^ 2) %% 100 \in [:: 00; 21; 29; 61; 69; 84].
Proof.
move=> Hf.
pose l := [:: 0; 29; 21; 84; 69; 61].
have -> : [:: 00; 21; 29; 61; 69; 84] =i l.
   move=> j; rewrite !inE; do 6 (case:eqP => //).
have -> : l = get_list 4 by vm_cast_no_check (refl_equal l).
by apply: get_list_all_correct.
Qed.

*)