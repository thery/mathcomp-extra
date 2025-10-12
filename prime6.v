From mathcomp Require Import all_ssreflect.

(******************************************************************************)
(*                                                                            *)
(* All prime numbers (except 2 and 3) are next to a multiple of 6             *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Lemma prime6 p : prime p -> 3 < p -> exists n, p = (6 * n).-1 \/ p = (6 * n).+1.
Proof.
move=> pP p_gt3.
have pD2 : 2 != p by apply/eqP=> pE2; rewrite -pE2 in p_gt3.
have pD3 : 3 != p by apply/eqP=> pE3; rewrite -pE3 in p_gt3.
case E : (p %% 6) (ltn_pmod p (isT : 0 < 6)) => [|[|[|[|[|[|]]]]]] _ //.
- case/negP : pD2; rewrite -(dvdn_prime2) // (dvdn_trans (isT : 2 %| 6)) //.
  by apply/eqP.
- by exists (p %/ 6); right; rewrite [LHS](divn_eq p 6) E mulnC addn1.
- case/negP : pD2; rewrite -(dvdn_prime2) // (divn_eq p 6) E dvdn_add //.
  by rewrite -[6]/(3 * 2) mulnA dvdn_mull.
- case/negP : pD3; rewrite -(dvdn_prime2) // (divn_eq p 6) E dvdn_add //.
  by rewrite -[6]/(2 * 3) mulnA dvdn_mull.
- case/negP : pD2; rewrite -(dvdn_prime2) // (divn_eq p 6) E dvdn_add //.
  by rewrite -[6]/(3 * 2) mulnA dvdn_mull.
exists (p %/ 6).+1; left.
by rewrite mulnC [LHS](divn_eq p 6) E [in RHS]mulSn addSn /= addnC.
Qed.
