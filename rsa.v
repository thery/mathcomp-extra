From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(*                                                                            *)
(*                      Proof of the RSA algorithm                            *)
(*                                                                            *)
(******************************************************************************)

(* This should be part of the standard library *)

Lemma prime_modn_expSn p n : prime p -> n.+1 ^ p = (n ^ p).+1 %[mod p].
Proof.
case: p => // p pP.
rewrite -[(_ ^ _).+1]addn0 (expnDn 1) big_ord_recr big_ord_recl /=.
rewrite subnn binn exp1n !mul1n addnAC -modnDmr; congr ((_ + _) %% _).
apply/eqP/dvdn_sum => -[i ?] _; exact/dvdn_mulr/prime_dvd_bin. 
Qed. 

(* This should be part of the standard library *)

Lemma fermat_little a p : prime p -> a ^ p = a %[mod p].
Proof.
move=> pP.
elim: a => [|a IH]; first by rewrite exp0n // prime_gt0.
by rewrite prime_modn_expSn // -addn1 -modnDml IH modnDml addn1.
Qed.

(* This should be part of the standard library *)

Lemma fermat_little_pred a p : prime p -> ~(p %| a) -> a ^ p.-1 = 1 %[mod p].
Proof.
move=> Pp pNDa.
have a_gt0 : 0 < a by case: a pNDa.
have aCp : coprime a p by rewrite coprime_sym prime_coprime //; apply/negP.
have aE : (egcdn a p).1 * a = 1 %[mod p].
  by case: egcdnP => //= km kn -> _; rewrite (eqP aCp) modnMDl.
rewrite -[_^ _]muln1 -modnMmr -{1}aE // modnMmr.
rewrite mulnC -mulnA -expnS prednK ?prime_gt0 //.
by rewrite -modnMmr fermat_little // modnMmr aE.
Qed.

(* We can start *)

Section RSA.

Record rsa := { 
    p : nat;
    q : nat;
   pq : nat;
    e : nat;
    d : nat; 
   wf : [&& prime p, prime q, p != q,
            0 < pq, p.-1 %| pq, q.-1 %| pq &
            e * d == 1 %[mod pq]]}.


(** Encryption *)
Definition encrypt r w : nat := w ^ e r %% (p r * q r).

(** Decription *)
Definition decrypt r w := w ^ d r %% (p r * q r).

(** Correctness of Rsa *)   
Theorem rsa_correct r w : decrypt r (encrypt r w)  = w %[mod p r * q r].
Proof.
case/and5P: (wf r) => Pp Pq pDq pq_gt0 /and3P[pDpq qDpq /eqP edE].
have pCq : coprime (p r) (q r) by rewrite prime_coprime ?dvdn_prime2.
have pq_gt1 : 1 < pq r.
  by case: p q Pp Pq pDq pq_gt0 pDpq qDpq => [] [|[|p1]] // [|[|[|q1]]] //;
     case: pq => [|[|]].
have ed_gt0 : 0 < e r * d r.
  by case: (_ * _) edE; rewrite // mod0n [1 %% _]modn_small.
rewrite /decrypt /encrypt modnXm modn_mod -expnM.
apply/eqP; rewrite chinese_remainder //.
apply/andP; split.
  have [pDw|/negP pNDw] := boolP (p r %| w).
    by rewrite -modnXm (eqP pDw) exp0n ?mod0n.
  rewrite (divn_eq (_ * _) (pq r)) edE [1 %% _]modn_small // addn1 expnS.
  rewrite -{3}[w]muln1 -modnMmr -[_ * 1 %% _]modnMmr.
  apply/eqP; congr (_ * _ %% _).
  rewrite mulnC expnM -(exp1n ((e r * d r) %/ pq r)).
  rewrite -[LHS]modnXm -[RHS]modnXm; congr (_ ^ _ %% _).
  have /dvdnP[k ->] := pDpq.
  rewrite mulnC expnM -[LHS]modnXm fermat_little_pred //.
  by rewrite modnXm exp1n.
have [qDw|/negP qNDw] := boolP (q r %| w).
  by rewrite -modnXm (eqP qDw) exp0n ?mod0n.
rewrite (divn_eq (_ * _) (pq r)) edE [1 %% _]modn_small // addn1 expnS.
rewrite -{3}[w]muln1 -modnMmr -[_ * 1 %% _]modnMmr.
apply/eqP; congr (_ * _ %% _).
rewrite mulnC expnM -(exp1n ((e r * d r) %/ pq r)).
rewrite -[LHS]modnXm -[RHS]modnXm; congr (_ ^ _ %% _).
have /dvdnP[k ->] := qDpq.
rewrite mulnC expnM -[LHS]modnXm fermat_little_pred //.
by rewrite modnXm exp1n.
Qed.

End RSA.