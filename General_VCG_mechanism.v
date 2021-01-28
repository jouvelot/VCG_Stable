(*

  General_VCG_mechanism.v

  A formalization project for the Vickrey‑Clarke‑Groves auction mechanism, 
  targeting:

  - a specification of the "General VCG" algorithm;

  - a proof of its key properties:
    . agent rationality,
    . no positive transfer,
    . and truthfulness;

  See Tim Roughtgarden lecture notes for more details.
  (http://timroughgarden.org/f16/l/l15.pdf)

  Authors: Pierre Jouvelot(+), Lucas Sguerra(+), Emilio Gallego Arias(++).

  Date: November, 2020.

  (+) MINES ParisTech, PSL University, France
  (++) Inria, France

  Thanks for their insights to the ssreflect community, and in particular:

   - Yves Bertot (sum_split_sOi, below_last_ord),
   - Georges Gonthier (slot_of).

*)

From Coq Require Import Init.Prelude Unicode.Utf8.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Aux.

Lemma max_monotonic 
  (T : finType) 
  (F F' : T -> nat) 
  (ltFF' : forall o : T, F o <= F' o) :
  \max_o F o <= \max_o F' o.
Proof.
elim/big_ind2: _ => // m1 m2 n1 n2  h1 h2. 
by rewrite geq_max !leq_max h1 h2 orbT.
Qed.

End Aux.

Section Ordinal.

Definition addS_ord m (j : 'I_(m.+1)) :=
  match j with
  | Ordinal v p => if v == m then m else v.+1
  end.

Lemma lt_j1_m m (j : 'I_(m.+1)) (ltjm : j < m) : j.+1 < m.+1.
Proof. by []. Qed.

Definition proper_addS_ord m (j : 'I_(m.+1)) (ltjm : j < m) :=
  Ordinal (lt_j1_m ltjm).

Lemma eq_proper_addS m (j : 'I_(m.+1)) (ltjm : j < m) :
  @addS_ord m j = @proper_addS_ord m j ltjm.
Proof.
case: j ltjm => j ltjn /=.
by move/ltn_eqF => ->.
Qed.

Lemma ltn_addS_ord m (j : 'I_m.+1) : addS_ord j < m.+1.
Proof.
move: j => [j ltjm1] //=.
case eqjm: (j == m).
by rewrite ltnSn.
have //: j < m. 
  by move: eqjm; rewrite ltn_neqAle => ->. 
Qed.

Definition ord_succ m (j : 'I_(m.+1)) := Ordinal (@ltn_addS_ord m j).
  
Lemma lt_ord_succ m (x : 'I_m.+1) : x < m -> x < ord_succ x.
Proof.
case: x => [s p] /= /ltn_eqF ->.
by rewrite ltnS.
Qed.

Lemma le_ord_succ m (x : 'I_m.+1) : x <= ord_succ x.
Proof.
case: x => [s p] /=. 
case: (s == m); last by rewrite leqnSn.
by rewrite -ltnS.
Qed.

Lemma ltn_subS_ord m (j : 'I_m) : j.-1 < m.
Proof. by move: (leq_pred j) (ltn_ord j); apply: leq_ltn_trans. Qed.

Definition ord_pred m j := Ordinal (@ltn_subS_ord m j).

Lemma below_last_ord m (j : 'I_(m.+1)) : (j != ord_max) = (j < m).
Proof.
by move: j => [j p]; rewrite -(inj_eq val_inj) ltn_neqAle -ltnS p andbT.
Qed.

Lemma cancel_ord_pred m (s : 'I_m.+1) : 0 < s -> ord_succ (ord_pred s) = s.
Proof.
move: s => [s p] /=.
move=> lt0s.
apply: ord_inj => //=.
rewrite prednK //. 
have/ltn_eqF -> //: s.-1 < m.
  move: p.
  by rewrite -[X in X < m.+1](@prednK s).
Qed.

Definition last_ord m := Ordinal (ltnSn m).

Lemma cancel_ord_succ m (s : 'I_m.+1) :
  s < last_ord m -> ord_pred (ord_succ s) = s.
Proof.
move: s => [s p] /=.
move=> ltsm. 
apply: ord_inj => //=.
by move/ltn_eqF: ltsm => ->.
Qed.

Lemma big_cropr m F (i : nat) :
  \sum_(s < m.+1 |(i <= s) && (s != ord_max)) F s =
    \sum_(s < m.+1 | i <= s < m) F s.
Proof. by apply: eq_bigl => s; rewrite below_last_ord. Qed.

Lemma sum0_gt_last m (F : 'I_m.+1 -> nat) : \sum_(s < m.+1 | m < s) F s = 0.
Proof.
rewrite (@eq_bigl _ _ _ _ _ (fun s : 'I_m.+1 => m < s) xpred0) => [|s].
by rewrite big_pred0_eq. 
apply: negbTE.
by rewrite -leqNgt (leq_ord s). 
Qed.

End Ordinal.

Variable (n'' : nat).
Definition n' := n''.+1.
Definition n := n'.+1.

Definition A := 'I_n.

Section Agent.

Definition last_agent : A := ord_max.

Definition agent_succ j : A := @ord_succ n' j.

Definition agent_pred j := @ord_pred n j.

Lemma agent_succ_mon (j j' : A) : j <= j' -> agent_succ j <= agent_succ j'.
Proof.
move=> lejj' /=.
have [] := boolP (j' != last_agent) => j'notlast.
- rewrite !eq_proper_addS //=.
  rewrite below_last_ord in j'notlast => //.
  exact: leq_ltn_trans lejj' j'notlast.
  by rewrite below_last_ord in j'notlast.
- move: j'notlast; rewrite negbK => /eqP -> /=.
  rewrite ifT //=.
  exact: ltn_addS_ord.
Qed.

Lemma leq_eqVlt_agent (j j' : A) : (j <= j') = (j == j') || (j < j').
Proof. exact: leq_eqVlt. Qed.

Lemma lt_le_agent (j j' : A)
  (jnotlast : j != last_agent) :
  (j < j') = (agent_succ j <= j').
Proof. by rewrite /= !eq_proper_addS; rewrite below_last_ord in jnotlast. Qed.

End Agent.

Module VCG.

(* General VCG and key properties. *)

Section Mechanism.

Variable (O : finType) (o0 : O) (i : A).

Definition bidding := {ffun O -> nat}.
Definition biddings := n.-tuple bidding.

Variable (bs : biddings).
Local Notation "'bidding_ j" := (tnth bs j) (at level 10).

Implicit Types (o : O) (bs : biddings).

Definition bidSum o := \sum_(j < n) 'bidding_j o.
Definition bidSum_i o := \sum_(j < n | j != i) 'bidding_j o.

Definition oStar := [arg max_(o > o0) (bidSum o)].

Definition welfare_with_i := bidSum_i oStar.

Definition welfare_without_i := \max_o bidSum_i o.

Definition price := welfare_without_i - welfare_with_i.

(* Alternative definition for welfare_without_i (i=0). *)

Definition bs'' : biddings :=
  [tuple [ffun o : O => (if j != i then 'bidding_j o else 0)]| j < n].

Notation "'bidding''_ j" := (tnth bs'' j) (at level 10).

Definition bidSum'' o := \sum_(j < n) 'bidding''_j o.

Definition welfare_without_i'' := \max_o bidSum'' o.

Definition price'' := welfare_without_i'' - welfare_with_i.

Lemma eq_bidSum'' o : bidSum'' o = bidSum_i o.
Proof. 
rewrite /bidSum'' /bidSum_i.
rewrite (big_mkcond (fun j => j != i)) //=.
set F2 := (X in _ = \sum_(i0 < n) X i0).
rewrite (eq_bigr F2) => [//=|j _].
by rewrite tnth_mktuple ffunE /F2.
Qed.

Lemma eq_welfare'' : welfare_without_i = welfare_without_i''.
Proof.
rewrite /welfare_without_i /welfare_without_i''.
rewrite (eq_bigr bidSum'') => [//=|o _].
by rewrite eq_bidSum''.
Qed.

Lemma eq_price'' : price = price''.
Proof. by rewrite /price'' -eq_welfare''. Qed.

(* Useful properties. *)

Lemma bidSumD1 o : bidSum o = 'bidding_i o + bidSum_i o.
Proof. by rewrite /bidSum (bigD1 i). Qed.

Theorem no_positive_transfer : (* 0 <= price *)
  welfare_with_i <= welfare_without_i.
Proof. exact: leq_bigmax. Qed.

Variable (value : bidding).

Hypothesis value_is_bid : 'bidding_i = value.

Lemma rational : price <= value oStar.
Proof.
rewrite -value_is_bid leq_subLR addnC -bidSumD1 -bigmax_eq_arg //.
have rebate_ge0 o : bidSum_i o <= bidSum o.
  by rewrite (bidSumD1 o) leq_addl.
exact: max_monotonic.
Qed.

End Mechanism.

Section Truthfulness.

Variable (O : finType) (o0 : O) (i : A).

Variable (bs : biddings O).

Notation "'bidding_ j" := (tnth bs j) (at level 10).
Notation "'o* bs" := (@oStar O o0 bs) (at level 10).

Variable (value : bidding O).

Definition utility bs := value ('o* bs) - (@price O o0 i bs).

Definition differ_only_i bs' := forall j, j != i -> tnth bs' j = 'bidding_j.

Theorem truthful bs' :
  'bidding_i =1 value ->
    differ_only_i bs' ->
      utility bs' <= utility bs.
Proof.
move=> value_is_bid diff.
rewrite /utility /price.
have eq_Sum_i : bidSum_i i bs  =1 bidSum_i i bs'.
  move=> o.
  apply: eq_bigr => j jnoti.
  rewrite /differ_only_i in diff.
  by move: diff => ->.
rewrite /price /welfare_without_i /welfare_with_i.
rewrite (@eq_bigr _ _ _ _ _ _ (bidSum_i i bs) (bidSum_i i bs')) //.
rewrite ?2!subnBA ?leq_sub2r //; last by exact: bigmax_sup.
rewrite -2!value_is_bid -eq_Sum_i -2!bidSumD1 /('o* bs) -bigmax_eq_arg //.
exact: bigmax_sup.
rewrite eq_Sum_i. 
exact: bigmax_sup.
Qed.

End Truthfulness.

End VCG.

