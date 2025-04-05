From mathcomp Require Import all_ssreflect all_fingroup.

(******************************************************************************)
(*                                                                            *)
(*  [cyle l] = the cycle defined by l, only makes sense when l is unique      *)
(*                                                                            *)
(******************************************************************************)

Section Lcycle.

Variable T : finType.

Definition lcycle (l : seq T) : {perm T} := 
  if l is a :: l1 then foldr (fun x p => tperm a x * p)%g 1%g l1 else 1%g.

Arguments lcycle : simpl never.

Notation "[cycle  l ]" := (lcycle l).

Lemma lcycle_nil : [cycle [::]] = 1%g.
Proof. by []. Qed.

Lemma lcycle_seq1 x : [cycle [:: x]] = 1%g.
Proof. by []. Qed.

Lemma lcycle_cons2 l x y : 
  [cycle [:: x, y & l]] = (tperm x y * [cycle x :: l])%g.
Proof. by []. Qed.

Lemma lcycle_perm x y : [cycle [:: x; y]] = tperm x y.
Proof. by rewrite /lcycle /= mulg1. Qed.

Lemma lcycle_not_in l x : x \notin l -> [cycle l] x = x.
Proof.
case: l => [|a l] /=; first by rewrite permE.
rewrite inE negb_or => /andP[/negPf xDa].
elim: l => [|b l IH] /=; first by rewrite permE.
rewrite lcycle_cons2 inE negb_or => /andP[/negPf xDb xNIl].
by rewrite permE /= permE /= xDa xDb IH.
Qed.

Lemma lcycle_end l x y : uniq (x :: rcons l y) -> [cycle x :: rcons l y] y = x.
Proof.
rewrite /= mem_rcons inE negb_or => /andP[/andP[/negPf xDy]].
elim: l => [_ _|z l IH]; first by rewrite lcycle_perm tpermR.
rewrite inE negb_or => /andP[/negPf xDz {}/IH IH].
rewrite rcons_uniq inE negb_or => 
  /andP[/andP[/negPf yDz yNIl]] /= /andP[zNIll lU].
by rewrite lcycle_cons2 permE /= permE /= eq_sym xDy yDz IH // rcons_uniq yNIl.
Qed.

Lemma lcycle_next l1 l2 x y : 
  uniq (l1 ++ x :: y :: l2) -> [cycle (l1 ++ x :: y :: l2)] x = y.
Proof.
case: l1 => /= [/and3P[]|z l1 /andP[]].
  rewrite inE negb_or => /andP[/negPf xDy xNIl2] yNIl2 l2U.
  by rewrite /= lcycle_cons2 permE /= tpermL lcycle_not_in // inE eq_sym xDy.
rewrite mem_cat negb_or !inE !negb_or => 
  /andP[zNIl1 /and3P[/negPf zDx zDy zNIl2]].
elim: l1 zNIl1 => /= [_ /and3P[_ yNIl2 _]|t l IH].
  rewrite lcycle_cons2 permE /= tpermR lcycle_cons2 permE /= tpermL.
  by rewrite lcycle_not_in // inE negb_or eq_sym zDy.
rewrite !inE negb_or => /andP[zDt zNIl /andP[tNI lU]].
rewrite lcycle_cons2 permE /= permE /= eq_sym zDx.
suff -> : x == t = false by apply: IH.
by move: tNI; rewrite mem_cat negb_or !inE eq_sym; case: (_ == _); 
   rewrite ?andbF.
Qed.

End Lcycle.

Notation "[cycle  l ]" := (lcycle _ l).
Arguments lcycle : simpl never.

Section Test.

Variable T : finType.

Goal forall i j k : T, uniq [:: k; i; j] -> 
  ([cycle [:: k; i; j]] * [cycle [:: i; j]] = [cycle [:: j; k]])%g.
Proof.
move=> i j k kijU; apply/permP => z; rewrite !lcycle_perm permE /=.
case: (tpermP j) => [->|->|/eqP/negPf zDj /eqP/negPf zDk].
- by rewrite (lcycle_end _ [:: i]) // tpermD //; 
     move: kijU; rewrite /= !inE ![_ == k]eq_sym; do 2 case: (k == _).
- by rewrite (lcycle_next _ [::] [:: j]) // tpermL.
have [->|/eqP /negPf zDi] := z =P i.
  by rewrite (lcycle_next _ [:: k] [::]) // tpermR.
rewrite lcycle_not_in; last by rewrite !inE zDj zDk zDi.
by rewrite tpermD // eq_sym ?zDi // zDj.
Qed.

End Test.
