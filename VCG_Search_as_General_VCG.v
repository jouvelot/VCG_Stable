(*

  VCG_Search_as_General_VCG.v

  A formalization project for the Vickrey‑Clarke‑Groves auctions, 
  targeting:

  - a specification of the "VCG for Search" auction variant.

  This embedding of "VCG for Search" into the "General VCG" mechanism should ease proofs
  that this variant also enjoys these key properties. 

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
From mathcomp Require Import fingroup.perm path.

Load General_VCG_mechanism.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Aux.

Lemma leq_transpose b1 b2 c1 c2
      (leb2b1 : b1 >= b2)
      (lec2c1 : c1 >= c2) :
  b1 * c2 + b2 * c1 <= b1 * c1 + b2 * c2.
Proof. 
have f: (b1 - b2) * (c1 - c2) = b1 * c1 + b2 * c2 - (b1 * c2 + b2 * c1).
  rewrite mulnBr 2!mulnBl ?subnBA;
    last by rewrite leq_mul2r leb2b1 orbT. 
  rewrite [X in _ = _ - X]addnC subnDA addnBAC //;
    last by rewrite leq_mul2r leb2b1 orbT.
- have [] := boolP (b2 == b1) => [/eqP -> |]. 
  by rewrite addnC.
- have [] := boolP (c2 == c1) => [/eqP -> //|].
  rewrite !neq_ltn. 
  move/leq_gtF: lec2c1; move/leq_gtF: leb2b1 => -> ->.
  rewrite !orbF => ltc2c1 ltb2b1.
  apply: ltnW.
  by rewrite -subn_gt0 -f muln_gt0 2!subn_gt0 ltb2b1 ltc2c1.
Qed.

Definition singleton (T : eqType) (P : T -> Type) :=
  forall (x y : T), P x -> P y -> x = y.

Lemma reindex_ge_i (i : A) m (F : 'I_m.+1 -> nat) :
  0 < m ->
    i < last_ord m ->
      \sum_(s < m.+1 | i < s) F s =
        \sum_(s < m.+1 | i <= s < m) F (ord_succ s).
Proof.
move=> lt0m ltil.
rewrite (bigD1 ord_max) //=.
rewrite [in RHS](bigD1 (ord_pred ord_max)) //=; last first.
apply/andP. split; last by rewrite ltn_predL.
rewrite -ltnS (ltn_predK lt0m) //.
rewrite cancel_ord_pred //=; last first.
congr (_ + _).
pose P := fun s : 'I_m.+1 => (i < s) && (s != ord_max).
rewrite (@reindex_onto _ _ _ _ _
    (@ord_succ m) (@ord_pred m.+1) P) //=; last first. 
- move=> s /andP [ltis nesx].
  rewrite cancel_ord_pred //.
  exact: (leq_ltn_trans (leq0n i)).
- apply: eq_bigl => s.
  rewrite /P below_last_ord //=.
  case: s => [s' p] /=.
  rewrite -![X in _ = _ && ~~ X](inj_eq val_inj) /=.
  - case eqs'm: (s' == m).
    rewrite ltnn andbF andFb.
    move: eqs'm => /eqP ->.
    by rewrite ltnn andbF andFb.
  - rewrite cancel_ord_succ //= ?eqxx ?andbT.
    rewrite ltnS -ltn_predRL.
    rewrite -andbA [X in _ = _ && X]andbC.
    rewrite -(@prednK m lt0m) ltnS.
    by rewrite -ltn_neqAle.
  move: eqs'm p; rewrite ltnS leq_eqVlt => ->.
  by rewrite orFb.
Qed.

Lemma big_split_subn k (P : 'I_k -> bool) F1 F2
      (H : forall s : 'I_k, P s -> F2 s <= F1 s) :
  \sum_(s < k | P s) (F1 s - F2 s) =
  \sum_(s < k | P s) F1 s - \sum_(s < k | P s) F2 s.
Proof.
suff:
  \sum_(s < k | P s) (F1 s - F2 s) =
    \sum_(s < k | P s) F1 s - \sum_(s < k | P s) F2 s /\
    \sum_(s < k | P s) F2 s <= \sum_(s < k | P s) F1 s by case.
pose K x y z := x = y - z /\ z <= y.
apply: (big_rec3 K); first by []; rewrite {}/K.
move=> i b_x b_y b_z /H Pi [] -> Hz; split; last exact: leq_add.
by rewrite addnBA ?addnBAC ?subnDA.
Qed.

Lemma only_ord0 m (s : 'I_m.+1) : m = 0 -> (s != ord0) = false.
Proof.
move=> eq0m.
move: s (ltn_ord s) => [s' p] /=.
by rewrite -!(inj_eq val_inj) /= eq0m ltnS leqNgt -eqn0Ngt => /eqP ->.
Qed.

Lemma sum_ord0 m (P : 'I_m.+1 -> bool) F : 
  m = 0 -> P ord0 -> \sum_(s < m.+1 | P s) F s = F ord0.
Proof.
move=> eq0m P0.
rewrite (bigD1 ord0) // -[in RHS](addn0 (F ord0)).
congr (_ + _) => //=.
set sum := (X in X = 0).
have -> : sum = \sum_(i < m.+1 | false) F i.
  apply: eq_bigl => i.
  by rewrite only_ord0 // andbF.
exact: big_pred0_eq.
Qed.

Lemma tnth_uniq (T : eqType) m (x : T) (t : m.+1.-tuple T) i j :
  uniq t → (tnth t i == tnth t j) = (i == j).
Proof.
move=> ut.
rewrite !(tnth_nth x) ?nth_uniq //; last by rewrite size_tuple ltn_ord.
by rewrite size_tuple ltn_ord.
Qed.

End Aux.

Ltac nth_split_i j ltji :=
  rewrite nth_cat size_takel ?size_tuple ?(ltnW ltn_ord) //;
  first move: (ltji) => -> /=.

Section Tuple_i.

Variable (T : eqType) (i : A).

Lemma tcast_tuple_i m (lt_i_m : i < m) : minn i m + (m - i.+1 + 1) = m.
Proof.
move/ltnW/minn_idPl: (lt_i_m) => ->. 
have -> :  m - i.+1 + 1 = m - i by rewrite addn1 subnSK.
rewrite addnBCA //; last by move/ltnW: lt_i_m.
by rewrite subnn addn0.
Qed.

Definition tuple_i m (t : m.-tuple T) (x : T) (lt_i_m : i < m) :=
  tcast (tcast_tuple_i lt_i_m) [tuple of take i t ++ (drop i.+1 t ++ [:: x])].

Lemma val_tcast m n (tc : n = m) (t : n.-tuple T) : val (tcast tc t) = val t.
Proof. by case: m / tc. Qed.

Lemma tuple_i_last m (t : m.+1.-tuple T) (x : T) :
  tnth t ord_max = last x (val t).
Proof.
rewrite (tnth_nth x) /=.
have eqns1: m = (size t).-1 by rewrite size_tuple.
rewrite [X in nth _ _ X]eqns1.
exact: nth_last.
Qed.

Lemma id_tuple_i m (t : m.-tuple T) (x : T) (lt_i_m : i < m) (j : 'I_m ) :
  j < i  -> tnth (tuple_i t x lt_i_m) j = tnth t j.
Proof.
move=> ltji.
rewrite tcastE !(tnth_nth x) //=.
nth_split_i j ltji; last by move/ltnW: lt_i_m.
by rewrite nth_take.
Qed.

Lemma shifted_tuple_i m (t : m.+1.-tuple T) (x : T) (lt_i_m : i < m.+1) 
  (j : 'I_m.+1) :
  i <= j -> j < m -> tnth (@tuple_i m.+1 t x lt_i_m) j = tnth t (ord_succ j).
move=> leij ltjn1.
move/ltnW: (ltn_ord i) => lein.
rewrite tcastE !(tnth_nth x) /=.
rewrite nth_cat size_takel; last by rewrite size_tuple; move/ltnW: lt_i_m.
rewrite leq_gtF // nth_cat size_drop size_tuple subnS ltn_predRL -subSn //.  
rewrite ltn_sub2r ?nth_drop //; last first.
have -> // : i.+1 + (j - i) = j.+1 
  by rewrite addnC addnBAC -?addnBA // subSn ?subnn ?addn1. 
by rewrite eq_proper_addS.
Qed.

Lemma last_tuple_i m (t : m.+1.-tuple T) (x : T) (lt_i_m : i < m.+1) :
 tnth (@tuple_i m.+1 t x lt_i_m) ord_max = x.
Proof.
rewrite (@tuple_i_last m _ x).
by rewrite val_tcast /= cats1 last_cat last_rcons.
Qed.

Lemma dropS (s : seq T) j : subseq (drop j.+1 s) (drop j s).
Proof. by elim: s j => //= x s ihs [|j] //; rewrite drop0 subseq_cons. Qed.

Lemma tuple_i_uniq m (t : m.-tuple T) (x : T) (lt_i_m : i < m) :
  uniq (x :: t) -> uniq (tuple_i t x lt_i_m).
Proof.
have H : subseq (take i t ++ drop i.+1 t) t.
  by rewrite -{3}(cat_take_drop i t) cat_subseq ?dropS.
rewrite /tuple_i val_tcast /= catA cat_uniq /= andbT orbF => /andP[h1 h2].
by rewrite (subseq_uniq H) //; apply: contra h1 => ?; rewrite (mem_subseq H).
Qed.

End Tuple_i.

Section Sort.

Variable (m m' : nat) (i : A).

Definition down_sorted_tuple (t : m.+1.-tuple 'I_m'.+1) :=
  forall (s1 s2 : 'I_m.+1), s1 <= s2 -> tnth t s2 <= tnth t s1.
  
Definition sorted_tuple := down_sorted_tuple.

Lemma sorted_tuple_i (t : m.+1.-tuple 'I_m'.+1) (lt_i_m : i < m.+1) :
  sorted_tuple t -> sorted_tuple (tuple_i t ord0 lt_i_m).
Proof.
move=> st s1 s2 lts1s2.
- have [] := boolP (s1 < i) => lts1i.
  rewrite [X in _ <= nat_of_ord X]id_tuple_i //.
  - have [] := boolP (s2 < i) => lts2i.
    by rewrite id_tuple_i //; exact: st.
  - move: lts2i; rewrite -leqNgt => leis2.
    - have [] := boolP (s2 < m) => lts2m1.
      rewrite shifted_tuple_i //.
      apply: (@leq_trans (tnth t s2)); last exact: (st).
      apply: st.
      by rewrite /ord_succ /= eq_proper_addS /=.
    - move: lts2m1; rewrite -below_last_ord negbK => /eqP ->.
      by rewrite last_tuple_i leq0n.
- move: lts1i; rewrite -leqNgt => leis1.
  - have [] := boolP (s1 < m) => lts1m1. 
    rewrite [X in _ <= nat_of_ord X]shifted_tuple_i //.
    - have [] := boolP (s2 < i) => lts2i.
      have: s1 < i by exact: leq_ltn_trans lts1s2 lts2i.
      by rewrite ltnNge leis1.
    - move: lts2i; rewrite -leqNgt => leis2.
      - have [] := boolP (s2 < m) => lts2m1.
        rewrite shifted_tuple_i //.
        have: ord_succ s1 <= ord_succ s2 by rewrite /ord_succ /= !eq_proper_addS.
        exact: st.
      - move: lts2m1; rewrite -below_last_ord negbK => /eqP ->.
        by rewrite last_tuple_i leq0n.
  - move: lts1m1; rewrite -below_last_ord negbK => /eqP eqs1m.
    rewrite (eqs1m).
    have ->: s2 = ord_max.
      apply: val_inj => /=.
      move: (conj lts1s2 (leq_ord s2)) => /andP.
      by rewrite eqs1m /= -eqn_leq eq_sym => /eqP.
    exact: leqnn.
Qed.

Section Transposition.

Variable (i1 i2 : 'I_m.+1).

Definition tuple_tperm (t : m.+1.-tuple 'I_m'.+1) :=
  [tuple tnth t (tperm i1 i2 i) | i < m.+1].
  
Lemma tuple_perm_inj : injective tuple_tperm.
Proof.
move=> t1 t2 /eqP.
rewrite eqEtuple => /forallP eq_tp.
apply/eqP; rewrite eqEtuple; apply/forallP => j.
- have [] := boolP ((i1 != j) && (i2 != j)) => [/andP [nei1 nei2]|/nandP].
  by move: (eq_tp j); rewrite !tnth_mktuple !tpermD.
- rewrite !negbK.
  move=> [/eqP <- |/eqP <-].
  by move: (eq_tp i2); rewrite !tnth_mktuple tpermR.
  by move: (eq_tp i1); rewrite !tnth_mktuple tpermL.
Qed.

Definition itperm : {perm (m.+1.-tuple 'I_m'.+1)} := perm tuple_perm_inj.

End Transposition.

Lemma tuple_tperm_uniq (i1 i2 : 'I_m.+1) (t : m.+1.-tuple 'I_m'.+1) : 
  uniq t -> uniq (tuple_tperm i1 i2 t).
Proof. 
move=> ut.
rewrite map_inj_uniq; first by rewrite val_ord_tuple enum_uniq.
move=> x y.
- have [] := boolP ((i1 != x) && (i2 != x)) => [/andP [nexi1 nexi2]|/nandP].
  rewrite tpermD //.
  - have [] := boolP ((i1 != y) && (i2 != y)) => [/andP [neyi1 neyi2]|/nandP].
    rewrite tpermD // => /eqP. 
    by rewrite (tnth_uniq (inord 0)) // => /eqP.
  - rewrite !negbK;move=> [/eqP <- |/eqP <-].
    - rewrite tpermL => /eqP.
      rewrite (tnth_uniq (inord 0)) // eq_sym.
      by move/negPn; rewrite nexi2.
    - rewrite tpermR => /eqP.
      rewrite (tnth_uniq (inord 0)) // eq_sym.
      by move/negPn; rewrite nexi1. 
- rewrite !negbK; move=> [/eqP <-|/eqP <-].
  - - have [] := boolP ((i1 != y) && (i2 != y)) => [/andP [neyi1 neyi2]|/nandP].
      rewrite tpermL tpermD // => /eqP.
      rewrite (tnth_uniq (inord 0)) //.
      by move/negPn; rewrite neyi2.
    - rewrite !negbK; move=> [/eqP <- |/eqP <-].
      - by rewrite tpermL.
      - rewrite tpermR tpermL => /eqP.     
        by rewrite (tnth_uniq (inord 0)) // => /eqP.
  - - have [] := boolP ((i1 != y) && (i2 != y)) => [/andP [neyi1 neyi2]|/nandP].
      rewrite tpermR tpermD // => /eqP.
      rewrite (tnth_uniq (inord 0)) //.
      by move/negPn; rewrite neyi1.
    - rewrite !negbK; move=> [/eqP <- |/eqP <-] //. 
      rewrite tpermR tpermL => /eqP.
      by rewrite (tnth_uniq (inord 0)) // eq_sym => /eqP.
Qed.

Lemma it_aperm_uniq (t : m.+1.-tuple 'I_m'.+1) (i1 i2 : 'I_m.+1) :
  uniq t -> uniq (aperm t (@itperm i1 i2)).
Proof. by move=> ut; rewrite apermE permE tuple_tperm_uniq. Qed.

Definition bubble_swap :=
  fun (t : m.+1.-tuple 'I_m'.+1) (i1i2 : 'I_m.+1 * 'I_m.+1) =>
    (i1i2.1 < i1i2.2) && (tnth t i1i2.1 >= tnth t i1i2.2).
      
Definition bubble_sort (t : m.+1.-tuple 'I_m'.+1) 
                       (i1i2s : seq ('I_m.+1 * 'I_m.+1)) :=
  foldr (fun i1i2 xo => 
    (bubble_swap xo.2 i1i2 && xo.1, 
     aperm xo.2 (@itperm i1i2.1 i1i2.2)))
  (true, t) 
  i1i2s.
  
Definition up_sorted_tuple (t : m.+1.-tuple 'I_m'.+1) :=
  forall (s1 s2 : 'I_m.+1), s1 <= s2 -> tnth t s1 <= tnth t s2.
  
Lemma bubble_uniq (t : m.+1.-tuple 'I_m'.+1) 
                  (i1i2s : seq ('I_m.+1 * 'I_m.+1)) :
  uniq t -> uniq (bubble_sort t i1i2s).2.
Proof. by move=> ut; elim: i1i2s => [//|? ?]; exact: it_aperm_uniq. Qed.

End Sort.

Hypothesis bubble_sort_spec : forall m m' (t : m.+1.-tuple 'I_m'.+1), 
  exists (i1i2s : seq ('I_m.+1 * 'I_m.+1)), 
    let xo := bubble_sort t i1i2s in
    xo.1 /\ up_sorted_tuple xo.2. 

(* VCG for Search *)

Variable (k' : nat).
Definition k := k'.+1.
Definition slot := 'I_k.

Definition last_slot : slot := ord_max.

(* One can use padding to validate the 'lt_k_n' hypothesis (see 'padded_bs'). *)

Hypothesis lt_k_n : k < n.

Lemma lt_slot_n' (s : slot) : s < n'.
Proof. 
have lt_k'_n' : k' < n' by move: lt_k_n.
exact: leq_ltn_trans (leq_ord s) lt_k'_n'. 
Qed.

Lemma le_k_n : k <= n.
Proof. exact: ltnW lt_k_n. Qed. 

Definition slot_pred (s : slot) : slot := @ord_pred k s.
Definition slot_succ (s : slot) : slot := ord_succ s.

Variable (q' : nat).
Definition q := q'.+1.
Definition ctr := 'I_q.
Definition ctr0 : ctr := Ordinal (ltn0Sn q').

Definition ctrs := k.-tuple ctr.

Variable (cs : ctrs).
Notation "'ctr_ s" := (tnth cs s) (at level 10).

Hypothesis sorted_ctrs : sorted_tuple cs.

Hypothesis last_ctr_eq0 : 'ctr_(last_slot) = ctr0.

Variable p' : nat.
Definition p := p'.+1.
Definition bid := 'I_p.
Definition bid0 : bid := Ordinal (ltn0Sn p').

Definition bids := n.-tuple bid.

Definition sorted_bids (bs : bids) := sorted_tuple bs.

(* VCG for Search algorithm, assuming bids are downsorted. *)
(* Labellings are used to map sorted agents to initial agents. *)

Definition labelling := n.-tuple A. 

Definition labelling_id : labelling := ord_tuple n.

Section VCGforSearchAlgorithm.

Variable (bs : bids).

Notation "'bid_ j" := (tnth bs j) (at level 10).

Lemma slot_as_agent_p (s : slot) : s < n.
Proof. exact: leq_trans (ltn_ord s) le_k_n. Qed.

Definition slot_as_agent (s : slot) := Ordinal (slot_as_agent_p s).

Definition externality (s : slot) :=
  let j := slot_as_agent s in
  'bid_j * ('ctr_(slot_pred s) - ('ctr_s)).

Definition price (sortedbs : sorted_bids bs) (i : A) := 
  if i < k then \sum_(s < k | i.+1 <= s) externality s else 0.

End VCGforSearchAlgorithm.

(* VCG for Search, seen as a special case of General VCG *)

Notation "'bidders" := (k.-tuple A) (at level 10).

Structure O := 
   Outcome {obidders :> 'bidders; 
            ouniq : uniq obidders}.
                          
Coercion bidders_of x := obidders x.

Canonical O_subType := 
  Eval hnf in [subType for bidders_of].
Canonical O_eqType := 
  Eval hnf in EqType _     [eqMixin     of O by <: ].
Canonical O_choiceType := 
  Eval hnf in ChoiceType _ [choiceMixin of O by <:].
Canonical O_countType := 
  Eval hnf in CountType  _ [countMixin  of O by <:].
Canonical O_subCountType := 
  Eval hnf in [subCountType of O].
Canonical O_finType := 
  Eval hnf in FinType    _ [finMixin    of O by <:].
Canonical O_subFinType := 
  Eval hnf in [subFinType of O].

Lemma o_injective (o : O) : injective (tnth o).
Proof.
move=> x y /eqP.
rewrite (tnth_uniq (inord 0)); first by move=> /eqP.
exact: ouniq.
Qed.

Definition slot_of (j : A) (o : 'bidders) :=
  match (tnthP o j) with
  | ReflectT p => proj1_sig (sig_eqW p)
  | ReflectF _ =>  last_slot
  end.

Lemma cancel_slot (o : O) (s : slot) : slot_of (tnth o s) o = s.
Proof. 
have io: tnth o s \in bidders_of o by exact: mem_tnth.
rewrite /slot_of.
case: tnthP => p.
case: sig_eqW => s' p' //=.
by move/o_injective: p' => ->.
by have //=: ∃ s' : slot, tnth o s = tnth o s' by exists s.
Qed.

Lemma tperm_slot (o : O) (s1 s2 s : slot) :
  let tp := tuple_tperm s1 s2 o in
  let tp_uniq := tuple_tperm_uniq s1 s2 (ouniq o) in
  slot_of (tnth o s) (Outcome tp_uniq) = 
  slot_of (tnth o (tperm s1 s2 s)) o. 
Proof.
- have [] := boolP (s1 == s) => eqss1.
  move/eqP: (eqss1) => <-.
  rewrite tpermL cancel_slot /slot_of.
  case: tnthP => p.
  - case: sig_eqW => s' /=.
    have eqs1t: s1 = tperm s1 s2 s2 by rewrite tpermR.
    rewrite tnth_mktuple [in LHS]eqs1t.
    by move/o_injective/perm_inj.
  - have //=: ∃ s, tnth o s1 = tnth (tuple_tperm s1 s2 o) s
      by exists s2; rewrite tnth_mktuple tpermR.
- have [] := boolP (s2 == s) => eqss2.
  move/eqP: (eqss2) => <-.
  rewrite tpermR cancel_slot /slot_of.
  case: tnthP => p.
  - case: sig_eqW => s' /=.
    have eqs2t: s2 = tperm s1 s2 s1 by rewrite tpermL.
    rewrite tnth_mktuple [in LHS]eqs2t.
    by move/o_injective/perm_inj.
  - have //=: ∃ s, tnth o s2 = tnth (tuple_tperm s1 s2 o) s
      by exists s1; rewrite tnth_mktuple tpermL.
- rewrite tpermD // cancel_slot /slot_of.
  case: tnthP => p.
  - case: sig_eqW => s' /=.
    have eqst: s = tperm s1 s2 s by rewrite tpermD.
    rewrite tnth_mktuple [in LHS]eqst.
    by move/o_injective/perm_inj.
  - have //=: ∃ s, tnth o s = tnth (tuple_tperm s1 s2 o) s
      by exists s; rewrite tnth_mktuple tpermD.
have //=: (∃ i : 'I_k, tnth o s = tnth (tuple_tperm s1 s2 o) i)
  by exists s; rewrite tnth_mktuple tpermD.
Qed.

Section OStarForSearch.

Variable (bs : bids).

Notation "'bid_ j" := (tnth bs j) (at level 10).

Hypothesis sorted_bs : sorted_bids bs.

Definition bid_in (j : A) (s : slot) := 'bid_j * 'ctr_s.

Definition t_bidding (j : A) (o : 'bidders) :=
    if j \in o then bid_in j (slot_of j o) else 0.

Definition bidding (j : A) := [ffun o : O => t_bidding j (bidders_of o)].
    
Definition biddings := [tuple bidding j | j < n].

Lemma widen_ord_inj : injective (widen_ord le_k_n).
Proof.
(* See https://perso.crans.org/cohen/work/edr/doc/minor.html *)
set wkn := widen_ord le_k_n.
move => s1 s2 eq_ws1_ws2. 
have /= eq_ws1_ws2_n: wkn s1 = wkn s2 :> nat by rewrite eq_ws1_ws2.
by apply/ord_inj.
Qed.

Definition t_oStar := [tuple widen_ord le_k_n j | j < k].

Lemma oStar_uniq : uniq t_oStar.
Proof.
rewrite map_inj_uniq; last by exact: widen_ord_inj.
by rewrite val_ord_tuple enum_uniq.
Qed.

Definition oStar := Outcome oStar_uniq.

Notation "'a* s" := (tnth oStar s) (at level 10).

Notation "'b* s" := (bidding ('a* s) oStar) (at level 10).

Lemma oStar_id (s : slot) : 'a* s = slot_as_agent s.
Proof. rewrite tnth_mktuple; exact: val_inj. Qed.

Definition sorted_o := up_sorted_tuple.
  
Definition welfare (o : O) := \sum_(s < k) bidding (tnth o s) o. 

Lemma alt_welfare j o : 
  \sum_(s < k) bidding (j s) (o s) = 
      \sum_(s < k) t_bidding (j s) (obidders (o s)).
Proof. by apply: eq_bigr=> s _; rewrite /bidding ffunE. Qed.

Definition max_welfare := welfare oStar.

Lemma le_ioStar_io (o : O) (sorted_o : sorted_o o) : 
  forall (s : slot), 'a* s <= tnth o s.
Proof.
case.
elim=> [lt0k|s IH lts1k].
by rewrite tnth_map ?tnth_ord_tuple.
have lt_s_k: s < k by exact: ltn_trans (ltnSn s) lts1k.
move: (IH lt_s_k).
set s' := (Ordinal lt_s_k); set s'1 := (Ordinal lts1k).
rewrite tnth_map ?tnth_ord_tuple // => les'as'.
have: tnth o s' < tnth o s'1.
  move: (@sorted_o s' s'1 (leqnSn s')).
  rewrite leq_eqVlt => /orP [/eqP|//=].
  move/val_inj/(@o_injective o s' s'1) => /= /eqP.
  by rewrite -(inj_eq val_inj) /= -[X in X == _]addn0 -addn1 eqn_add2l.
move: les'as'.
rewrite tnth_map ?tnth_ord_tuple. 
exact: leq_ltn_trans.
Qed.

Lemma le_welfare_sorted_o_oStar (o : O) (sorted_o : sorted_o o) :
  welfare o <= max_welfare.
Proof.
apply: leq_sum => s _.
rewrite /bidding !ffunE /t_bidding.
case aio: (tnth o s \in bidders_of o); last by rewrite !leq0n.
rewrite !cancel_slot.
case aioStar: ('a* s \in bidders_of oStar); 
  first by rewrite !leq_mul2r sorted_bs ?orbT // le_ioStar_io.
rewrite leqn0 muln_eq0.
move/negbT: aioStar. 
rewrite tnth_mktuple mem_map.
rewrite -(@mem_map _ _ val val_inj) => //=.
rewrite -index_mem size_map size_enum_ord index_map ?index_enum_ord.
rewrite -leqNgt -ltnS -ltn_predRL.
by move/leq_gtF: (leq_ord s) => ->.
exact: ord_inj.
exact: widen_ord_inj.
Qed.

Lemma le_transposed_welfare (i1i2 : 'I_k * 'I_k) (o : O) :
  let ts := aperm (bidders_of o) (@itperm k' n' i1i2.1 i1i2.2) in 
  let ts_uniq := 
    @it_aperm_uniq _ _ (bidders_of o) i1i2.1 i1i2.2 (ouniq o) in
  bubble_swap o i1i2 ->
    welfare o <= welfare (Outcome ts_uniq). 
Proof.
move=> /= /andP [lti1i2 ltt2t1].
set s1 := i1i2.1; set s2 := i1i2.2.
rewrite /welfare (bigD1 s2) 1?(bigD1 s1) //=;
  last by move/ltn_eqF/negbT: lti1i2. 
rewrite [X in _ <= X](bigD1 s2) ?[X in _ <= _ + X](bigD1 s1) //=;
  last by move/ltn_eqF/negbT: lti1i2.
rewrite addnA [X in _ <= X]addnA.
set sum1 := (X in _ + X); set sum2 := (X in _ <= _ + X).
have <- : sum1 = sum2. 
  set F2 := (X in _ = \sum_(i < k | _) X i).
  rewrite /sum1 (eq_bigr F2) // => i /andP [neis2 neis1].
  rewrite eq_sym in neis1; rewrite eq_sym in neis2.
  rewrite /F2 /bidding !ffunE /t_bidding/= apermE permE tnth_mktuple tpermD //.
  rewrite !mem_tnth /tuple_tperm memtE /=.
  have {F2 sum1 sum2} ipi1i2: i = tperm s1 s2 i by rewrite tpermD.
  rewrite ipi1i2 (@mem_map  _ _ (fun j => tnth o (tperm s1 s2 j))) ?mem_enum.
  rewrite !tpermD // cancel_slot [in RHS]/slot_of.
  case: tnthP => p.
  - case: sig_eqW => s /=.
    rewrite tnth_mktuple ipi1i2 => /o_injective /perm_inj <-.
    by rewrite tpermD.
  - have //=: ∃ s, tnth o i = 
      tnth [tuple tnth o (tperm s1 s2 i) | i < k] s
      by exists i; rewrite tnth_mktuple tpermD.
  move=> j s.
  by move/o_injective/perm_inj.
rewrite leq_add2r {sum1 sum2} /bidding !ffunE /= /t_bidding.
rewrite !mem_tnth !apermE permE !tnth_mktuple tpermR tpermL.
rewrite (@tperm_slot _ s1 s2 s1) (@tperm_slot _ s1 s2 s2).
rewrite tpermL tpermR /bid_in !cancel_slot.
set i1 := tnth o s1; set i2 := tnth o s2.
have leb1b2: 'bid_i1 <= 'bid_i2 by exact: sorted_bs. 
have lec2c1: 'ctr_s2 <= 'ctr_s1 by move/ltnW/sorted_ctrs: lti1i2.
rewrite [X in _ <= X]addnC.
exact: leq_transpose.
Qed.

Lemma le_welfare_o_oStar (o : O) : welfare o <= max_welfare.
Proof.
move: (bubble_sort_spec o) => [i1i2s] /= [x].
have lt_w_tw: forall i1i2s o,
    let xo := bubble_sort (bidders_of o) i1i2s in 
    let obu := @bubble_uniq _ _ (bidders_of o) i1i2s (ouniq o) in
    xo.1 -> welfare o <= welfare (Outcome obu). 
  rewrite /welfare /=.
  elim=> [o' _|i1i2 i1i2s' IH o' /= /andP [x12 x12s']].  
  - by apply: leq_sum => s _; rewrite !ffunE. 
  - set bo' := (bubble_sort o' i1i2s').2.
    set bo'_o := (Outcome (bubble_uniq i1i2s' (ouniq o'))).
    move: (@le_transposed_welfare i1i2 bo'_o x12) => /=.
    move: (IH o' x12s').
    rewrite /welfare !alt_welfare /=.
    exact: leq_trans. 
move=> sorted_bo.
move: (lt_w_tw i1i2s o x).
set bo := (X in _ <= welfare X) => ltwowbo.
have/le_welfare_sorted_o_oStar : up_sorted_tuple bo by [].
exact: leq_trans.
Qed.

Lemma not_in_oStar (j : A ) : k' < j -> (j \in (bidders_of oStar)) = false.
Proof.
move=> ltk'j.
apply: negbTE.
rewrite -has_pred1 -all_predC. 
apply/(all_nthP j) => s.
rewrite size_map /= size_enum_ord ltnS => ltsk.
rewrite (nth_map last_slot); last by rewrite size_enum_ord.
by rewrite -(inj_eq val_inj) /= nth_enum_ord // neq_ltn (leq_ltn_trans ltsk). 
Qed.

Lemma slot_in_oStar (j : A) :
  (j \in bidders_of oStar) -> slot_of j oStar = inord j. 
Proof.
move=> jino.
rewrite /slot_of.
move: (@elimT _ _ (tnthP oStar j) jino).
case: tnthP => pj _ /=.
case: sig_eqW => sj //=.
rewrite tnth_mktuple => -> /=.
by rewrite inord_val.
have //: exists s, j = tnth oStar s.
  exists (inord j).  
  rewrite tnth_mktuple. 
  apply: val_inj => /=.
  rewrite inordK //.    
  apply: contraTT jino.
  by rewrite -leqNgt => /not_in_oStar ->.
Qed.

End OStarForSearch.

Definition o0 := oStar.

Section BidSum.

Variable (i : A) (bs : bids).

Hypothesis sorted_bs : sorted_bids bs.

Notation "'bid_ j" := (tnth bs j) (at level 10).

Definition bidSum := @VCG.bidSum O_finType (biddings bs).

Lemma valid_bidSum (o : O) :
  bidSum o = \sum_(j < n) (bidding bs) j o.
Proof. apply: congr_big => //= s _; by rewrite tnth_mktuple. Qed.

Lemma bidSum_out_o (o : O) :
  \sum_(j < n | j \notin (bidders_of o)) (bidding bs) j o = 0.
Proof.
apply/eqP ; rewrite sum_nat_eq0.
apply/forall_inP => j outo ; apply/eqP.
rewrite !ffunE.
exact: ifN.
Qed.

Lemma bidSum_slot (o : O) :
  bidSum o = \sum_(s < k) (bidding bs) (tnth o s) o.
Proof.
rewrite valid_bidSum.
rewrite (bigID (fun j : A => j \in (bidders_of o))) bidSum_out_o /= addn0.
rewrite -(@big_tuple _ _ _ _ _ _ predT (fun j => bidding bs j o)).
rewrite big_uniq => //=.
exact: ouniq.
Qed.

Definition VCG_oStar := @VCG.oStar O_finType o0 (biddings bs).

Notation "'a* s" := (tnth oStar s) (at level 10).

Notation "'b* s" := (bidding bs ('a* s) oStar) (at level 10).

Definition max_bidSum_spec :=
  (@extremum_spec [eqType of nat] geq O_finType predT bidSum).

Lemma VCG_oStar_extremum : max_bidSum_spec VCG_oStar.
Proof. exact: arg_maxnP. Qed.

Lemma bidsSum_sumBid (P : A -> bool) (o : O) :
  forall bs, \sum_(j < n | P j) tnth (biddings bs) j o =
    \sum_(j < n | P j) bidding bs j o.
Proof. by move=> ?; apply: congr_big => //= j _; rewrite tnth_mktuple. Qed.

Lemma oStar_extremum : max_bidSum_spec oStar.
Proof. 
have true_oStar: predT oStar by [].
have max_oStar (o : O) : predT o → geq (bidSum oStar) (bidSum o).
  move=> _.
  rewrite bidSum_slot /bidSum /VCG.bidSum // !bidsSum_sumBid.
  move: (@le_welfare_o_oStar bs sorted_bs o).
  by rewrite /welfare -bidSum_slot valid_bidSum.
exact: ExtremumSpec.
Qed.

Conjecture uniq_max_bidSum : uniq bs -> singleton max_bidSum_spec.
Hypothesis uniq_oStar : singleton max_bidSum_spec.

Definition bid_ctr_slot s := 'bid_(slot_as_agent s) * 'ctr_s.
Definition bid_ctr_agent j := 'bid_j * 'ctr_(slot_of j oStar).

Lemma widen_slot_as_agent (s : slot) : widen_ord le_k_n s = slot_as_agent s.
by rewrite /slot_as_agent; apply: val_inj.
Qed.

Lemma eq_bid_ctr (j : A) : bid_ctr_agent j = bid_ctr_slot (slot_of j oStar).
Proof.
rewrite /bid_ctr_agent /bid_ctr_slot /slot_of.
have: (tnth oStar (slot_of j oStar)) \in (bidders_of oStar).
  rewrite tnth_mktuple widen_slot_as_agent.
  case: tnthP => p //.  
  have //=: (∃ s : slot, slot_as_agent (slot_of j oStar) = 'a* s)
    by exists (slot_of j oStar); rewrite tnth_mktuple; apply: val_inj.
case: tnthP => p.
case: sig_eqW => s' p' //=.
rewrite -widen_slot_as_agent.
have -> //=: j = widen_ord le_k_n s' by rewrite p' tnth_mktuple.
by rewrite last_ctr_eq0 ?muln0 .
Qed.

Lemma s_bid_as_bid_x_ctr (s : slot) : 'b* s = bid_ctr_slot s.
Proof.
rewrite /bidding ffunE /t_bidding tnth_mktuple mem_map.
have ->: s \in ord_tuple k 
  by apply/tnthP; exists s; rewrite tnth_ord_tuple.
rewrite widen_slot_as_agent.
rewrite -oStar_id cancel_slot tnth_mktuple widen_slot_as_agent //.
exact: widen_ord_inj.
Qed.

Lemma bidSum_bid_ctr_slot : bidSum oStar = \sum_(s < k) bid_ctr_slot s.
Proof. 
rewrite bidSum_slot.
apply: congr_big => //= s _.
exact: s_bid_as_bid_x_ctr.
Qed.

Definition bidSum_i := @VCG.bidSum_i O_finType i (biddings bs).

Lemma bidSum_i_bid_ctr_agent : bidSum_i oStar = bidSum oStar - bid_ctr_agent i.
Proof.
rewrite /bidSum_i /VCG.bidSum_i /bidSum /VCG.bidSum.
pose bid j :=  tnth (biddings bs) j oStar. 
rewrite [X in _ = X - _](bigD1 i) => //=.
rewrite addnC -[X in X = _]addn0 -addnBA.
congr (_ + _). 
- rewrite /bid tnth_mktuple ffunE /t_bidding.
  case iino: (i \in bidders_of oStar); first by rewrite subnn.
  by rewrite sub0n.
- rewrite /bid tnth_mktuple ffunE /t_bidding.
  case iino: (i \in bidders_of oStar); first by apply: eq_leq.
  rewrite /bid_ctr_agent /slot_of.
  move: (@elimF _ (i \in bidders_of oStar) (tnthP oStar i) iino).
  case: tnthP => [p|p _] //. 
  by rewrite leqn0 muln_eq0 last_ctr_eq0 ?eq_refl ?orbT. 
Qed.

Lemma bidSum_i_bid_ctr_slot :
  bidSum_i oStar = \sum_(s < k) bid_ctr_slot s - bid_ctr_agent i.
Proof. move: bidSum_i_bid_ctr_agent; by rewrite bidSum_bid_ctr_slot. Qed.

Definition bidSumD1 o := @VCG.bidSumD1 O_finType i (biddings bs) o.

Lemma s_bidSumD1 :
  \sum_(j < n) (bidding bs) j oStar =
    (bidding bs) i oStar + \sum_(j < n | j != i) (bidding bs) j oStar.
Proof. by rewrite (bigD1 i). Qed.

End BidSum.

(* VCG for Search, as a case of General VCG. *)
   
Variable (n_bidders : nat).

Variable (bs_bidders : n_bidders.-tuple bid).

Lemma cast_n_tuple : minn n (n_bidders + (n - n_bidders)) = n.
Proof.
case lenbn: (n_bidders <= n).
- by rewrite subnKC ?minnn.
- move/negbT: lenbn; rewrite -ltnNge; move/ltnW=> lennb.
  move: (lennb); rewrite -subn_eq0 => /eqP ->; rewrite addn0.
  by apply/minn_idPl.
Qed.

Definition padded_bs_bidders : bids :=
  tcast cast_n_tuple 
    (take_tuple n (cat_tuple bs_bidders (nseq_tuple (n - n_bidders) bid0))).

Definition bs0 := locked padded_bs_bidders.

(* Right padding with 0s ensures that k < n is valid, whatever the number 
   n_bidders of actual bidders is.

  Wlog, we can assume that bs0 is already sorted (padding is with 0s). *)

Section VCGforSearchPrice.

Variable (i : A).

Hypothesis i_in_oStar : i \in bidders_of oStar.

Variable (bs0 : bids).

Hypothesis sorted_bs0 : sorted_bids bs0.

Definition bs := bs0.

Hypothesis uniq_oStar : singleton (max_bidSum_spec bs).

Lemma sorted_bs : sorted_bids bs.
Proof. exact: sorted_bs0. Qed.

Notation "'bid_ j" := (tnth bs j) (at level 10).

Definition ls : labelling := labelling_id.

Notation "'lab_ j" := (tnth ls j) (at level 10).

(* VCG social welfare with i. *)

Definition welfare_with_i := @VCG.welfare_with_i O_finType o0 i (biddings bs).

Definition sOi : slot := slot_of i oStar.

Lemma i_has_slot: (∃ s : slot, i = tnth oStar s).
Proof.
exists (slot_of i oStar).
move: (@elimT _ (i \in bidders_of oStar) (tnthP oStar i) i_in_oStar).
rewrite /slot_of.
case: tnthP => p //=.
by case: sig_eqW.
Qed.

Lemma lt_i_k : i < k.
Proof.
move/tnthP: i_in_oStar => [s].
rewrite tnth_mktuple => -> /=.
exact: ltn_ord.
Qed. 

Lemma not_lt_last_slot_i : (last_slot < i) = false.
Proof. 
move: i_has_slot i_in_oStar => [s] ->.
rewrite tnth_map tnth_ord_tuple /=.
by move/ltn_geF: (ltn_ord s).
Qed.

Lemma eq_i_ord0 : k' = 0 -> i = ord0.
Proof.
move=> eq0k'.
have: i <= k' by rewrite leqNgt; move: not_lt_last_slot_i => ->. 
rewrite eq0k' leqn0 => /eqP eqi0.
exact: val_inj.
Qed.

Lemma sum_out F : k' = 0 -> \sum_(s < k | i < s) F s = 0.
Proof.
move=> eq0k'.
rewrite (eq_bigl (fun s => false)); first exact: big_pred0_eq.
move=> s.
apply: leq_gtF.
rewrite eq_i_ord0 // leq_eqVlt. 
move/negbT: (only_ord0 s eq0k').
by rewrite negbK => /eqP ->.
Qed.

Lemma sum_split_ge_i F :
  \sum_(s < k | i <= s) F s = F sOi + \sum_(s < k | i < s) F s.
Proof.
rewrite (bigID (fun s : slot => i < s) (fun s : slot => i <= s)) addnC /=.
congr (_ + _).
rewrite [in LHS](eq_bigl (fun s : slot => i < s)) //;
  last by move=> s; rewrite andb_idl //; move/ltnW.
apply: (@big_pred1 _ _ _ _ sOi (fun s => (i <= s) && ~~ (i < s)) F) => s.
rewrite -leqNgt -eqn_leq pred1E /sOi.
move: i_has_slot => [s' -> //=].
rewrite /slot_of.
case: tnthP => p.
case: sig_eqW => s'' /=.
rewrite !tnth_mktuple.
by move/widen_ord_inj => ->.
by have //=: ∃ i , tnth t_oStar s' = tnth t_oStar i by exists s'.
Qed.

Lemma sum_split_i F :
  \sum_(s < k) F s = \sum_(s < k | s < i) F s + F sOi + \sum_(s < k | i < s) F s.
Proof.
rewrite (bigID (fun s : slot => s < i)) => /=.
rewrite -addnA.
have ltii : ~~ (i < i) by rewrite ltnn.
congr (_ + _).
rewrite (@eq_bigl _ _ _ _ _ (fun s : slot => ~~ (s < i)) (fun s => i <= s));
  last by move=> s; rewrite -leqNgt.
exact: sum_split_ge_i.
Qed.

Lemma s_welfare_with_i :
  welfare_with_i = \sum_(s < k | s < i) bid_ctr_slot bs s +
    \sum_(s < k | i < s) bid_ctr_slot bs s.
Proof.
rewrite /welfare_with_i /VCG.welfare_with_i /VCG.bidSum_i.
rewrite -/(VCG_oStar bs). 
rewrite (uniq_oStar (VCG_oStar_extremum bs) (oStar_extremum sorted_bs)).
rewrite (bidsSum_sumBid (fun j => j != i)).
apply/eqP; rewrite -(eqn_add2l (bidding bs i oStar)); apply/eqP.
rewrite -s_bidSumD1 -valid_bidSum /bidding ffunE /t_bidding.
rewrite i_in_oStar bidSum_bid_ctr_slot.
rewrite /bid_in -/(bid_ctr_slot bs (slot_of i oStar)).
rewrite addnC -addnA [X in _ + X]addnC addnA.
rewrite -/(bid_ctr_agent bs i) eq_bid_ctr -/sOi.
  by rewrite -(sum_split_i (bid_ctr_slot bs)).
Qed.

(* VCG social welfare without i. *)

Lemma tcast_bids'' : minn i n + (1 + (n - i.+1)) = n.
Proof.
move/ltnW/minn_idPl: (ltn_ord i) => ->.
by rewrite addnA addn1 addnC subnK.
Qed.

Definition bs'' : bids :=
  tcast tcast_bids'' [tuple of take i bs ++ [:: bid0] ++ (drop i.+1 bs)].

Definition succ_last_slot_agent : A := inord last_slot.+1.

Lemma oStar_i_uniq : uniq (succ_last_slot_agent :: oStar).
Proof.
rewrite cons_uniq. 
apply/andP; split; last first.
- rewrite map_inj_uniq /=.
  exact: enum_uniq.
  exact: widen_ord_inj.
- rewrite -(@mem_map _ _ val val_inj).
  set l := (X in _ \notin X).
  have -> /=: l = iota 0 k.
    have sz_oStar: size oStar = k.
      by rewrite !size_map -enumT size_enum_ord.
    apply: (@eq_from_nth _ 0); first by rewrite size_iota size_map. 
    move=> s.
    rewrite !size_map -enumT size_enum_ord => ltsk. 
    rewrite nth_iota // add0n. 
    rewrite (@nth_map _ last_agent); last by rewrite sz_oStar.
    rewrite (@nth_map _ last_slot); last by rewrite size_enum_ord.
    by rewrite /= nth_enum_ord.
  rewrite inordK /=; last by exact: lt_k_n.
  have: forall m, m \notin iota 0 m
    by move=> ?; rewrite mem_iota add0n ltnn andbF.
  exact.
Qed.

Definition t_oStar_i := tuple_i oStar succ_last_slot_agent lt_i_k.
Definition oStar_i : O := Outcome (tuple_i_uniq lt_i_k oStar_i_uniq).

Section OStarForSearch_i.

Variable (bs : bids).

Notation "'bid_ j" := (tnth bs j) (at level 10).

Hypothesis sorted_bs : sorted_bids bs.

Definition t_bidding_i j o := if j != i then t_bidding bs j o else 0.

Definition bidding_i (j : A) := [ffun o : O => t_bidding_i j (bidders_of o)].
    
Definition biddings_i := [tuple bidding_i j | j < n].

Notation "'a* s" := (tnth oStar_i s) (at level 10).

Notation "'b* s" := (bidding_i ('a* s) oStar_i) (at level 10).

Lemma oStar_id_i (s : slot) : 
  'a* s = if s < i then slot_as_agent s else agent_succ (slot_as_agent s).
Proof.
move/ltn_eqF: (lt_slot_n' s) => neqsn'.
- have [] := boolP (s < i) => ltsi.
  by rewrite id_tuple_i // oStar_id.
- rewrite -leqNgt in ltsi.
  have [] := boolP (s < k') => ltsk'.
  rewrite shifted_tuple_i // tnth_mktuple. 
  apply: val_inj => /=.
  by rewrite eq_proper_addS /= neqsn'.
- move: ltsk'; rewrite -below_last_ord negbK => /eqP ->.
  rewrite last_tuple_i /succ_last_slot_agent /=.
  apply: val_inj => /=.
  move/ltn_eqF: (lt_slot_n' (inord k')); rewrite inordK // => ->.
  by rewrite inordK ?ltnSn ?lt_k_n.
Qed.

Lemma lt_oStar_succ (s : slot) : 'a* s <= agent_succ (slot_as_agent s).
Proof.
rewrite oStar_id_i.
have [] := boolP (s < i) => ltsi //.
apply/ltnW.
rewrite lt_ord_succ //=.
exact: lt_slot_n' s.
Qed.

Definition welfare_i (o : O) := \sum_(s < k) bidding_i (tnth o s) o. 

Lemma alt_welfare_i j o : 
  \sum_(s < k) bidding_i (j s) (o s) = 
      \sum_(s < k) t_bidding_i (j s) (obidders (o s)).
Proof. by apply: eq_bigr=> s _; rewrite /bidding_i ffunE. Qed.

Definition max_welfare_i := welfare_i oStar_i.

Definition no_i_in o := [forall s : slot, (i == tnth o s) == false].

Lemma notin_no_in o : i \notin bidders_of o -> no_i_in o.
Proof.
rewrite -has_pred1 -all_predC. 
move/all_tnthP => notin.
apply/eqfunP => s.
move: (notin s) => /=.
rewrite eq_sym.
exact: negbTE.
Qed.

Lemma le_ioStar_io_i (o : O) 
      (sorted_o : sorted_o o)
      (noio : no_i_in o) :
  forall (s : slot), 'a* s <= tnth o s.
Proof. 
case.
elim=> [lt0k|s IH lts1k].
- set s := Ordinal lt0k.
  rewrite oStar_id_i.
  have [] := boolP (0 < i) => lt0i //=.
  rewrite -leqNgt leqn0 in lt0i.  
  move: noio => /eqfunP /(_ s).
  rewrite -(inj_eq val_inj) /= eq_sym.
  move: lt0i => /eqP ->.
  exact: neq0_lt0n.
- have lt_s_k: s < k by exact: ltn_trans (ltnSn s) lts1k.
  move: (IH lt_s_k).
  set s' := (Ordinal lt_s_k); set s'1 := (Ordinal lts1k).
  have ltos'os'1: tnth o s' < tnth o s'1.
    move: (@sorted_o s' s'1 (leqnSn s')).
    rewrite leq_eqVlt => /orP [/eqP|//=].
    move/val_inj/(@o_injective o s' s'1) => /= /eqP.
    by rewrite -(inj_eq val_inj) /= -[X in X == _]addn0 -addn1 eqn_add2l.
  have eqsuccs's'1: agent_succ (slot_as_agent s') = slot_as_agent s'1.
    apply: val_inj => /=.
    by move/ltn_eqF: (lt_slot_n' s') => ->.
  have nes'1last : slot_as_agent s'1 != last_agent.
    rewrite -(inj_eq val_inj) /=. 
    by move/ltn_eqF: (lt_slot_n' s'1) => ->.
  rewrite !oStar_id_i. 
  - have [] := boolP (s'1 < i) => lts'1i.
    have lts'i : s' < i by exact: ltn_trans (ltnSn s') lts'1i.
    rewrite ifT // => lesos'.
    exact: leq_ltn_trans lesos' ltos'os'1.
  - move: lts'1i.
    rewrite -leqNgt leq_eqVlt => /orP [eqis'1|ltis'1].
    - have lts'i: s' < i.
        rewrite eq_sym /= in eqis'1. 
        by rewrite leq_eqVlt eqis'1 orTb.
      rewrite ifT // => lesos'.
      have ltsuccos': agent_succ (tnth o s') <= tnth o s'1.
        rewrite /agent_succ /= eq_proper_addS /=; last by [].
        exact: leq_trans ltos'os'1 (leq_ord (tnth o s'1)).
      have ltsuccs': agent_succ (slot_as_agent s') <= agent_succ (tnth o s')
        by exact: agent_succ_mon.
      move: (leq_trans ltsuccs' ltsuccos').
      rewrite leq_eqVlt_agent => /orP [].
      - have ->: agent_succ (slot_as_agent s') = i. 
          apply: val_inj => /=.
          move: eqis'1 => /eqP ->.  
          by move/ltn_eqF: (lt_slot_n' s') => ->.
        by move: noio => /eqfunP /(_ s'1) ->.
      - by rewrite lt_le_agent eqsuccs's'1.
    - have nlts'i: (s' < i) = false by rewrite ltnS in ltis'1; move/leq_gtF: ltis'1. 
      rewrite ifF // => ltsuccs'.
      move: (leq_ltn_trans ltsuccs' ltos'os'1).
      by rewrite lt_le_agent eqsuccs's'1.
Qed.

Lemma no_i_in_oStar_i : no_i_in oStar_i.
Proof.
rewrite /no_i_in /oStar_i /=. 
apply/eqfunP => s.
- have [] := boolP (s < i) => ltsi.
  rewrite id_tuple_i // oStar_id -(inj_eq val_inj) /=.
  exact: gtn_eqF.
- have [] := boolP (s < k') => ltsk'.
  rewrite shifted_tuple_i //; last by rewrite leqNgt.
  rewrite /t_oStar tnth_mktuple -(inj_eq val_inj) /= eq_proper_addS /=.
  rewrite -leqNgt in ltsi.
  by move/ltn_eqF: (leq_ltn_trans ltsi (ltnSn s)).
- move: ltsk'; rewrite -below_last_ord negbK => /eqP ->.
  rewrite last_tuple_i /succ_last_slot_agent /=.
  rewrite -(inj_eq val_inj) /= inordK ; last by exact: lt_k_n.
  by move/ltn_eqF: lt_i_k.
Qed.

Lemma le_welfare_sorted_o_oStar_i (o : O) 
      (sorted_o : sorted_o o) 
      (noio : no_i_in o) :
  welfare_i o <= max_welfare_i.
Proof.
apply: leq_sum => s _.
rewrite /bidding_i !ffunE /t_bidding_i.
move: (noio) => /eqfunP /(_ s).
rewrite eq_sym => ->.
rewrite ifT ?mem_tnth //.
move: no_i_in_oStar_i => /eqfunP /(_ s).
rewrite eq_sym => ->.
rewrite ifT ?mem_tnth // !cancel_slot /bid_in.
by rewrite leq_mul2r sorted_bs ?orbT // le_ioStar_io_i.
Qed.

Lemma le_transposed_welfare_i (i1i2 : 'I_k * 'I_k) (o : O) 
      (noio : no_i_in o) :
  let ts := aperm (bidders_of o) (@itperm k' n' i1i2.1 i1i2.2) in 
  let ts_uniq := 
    @it_aperm_uniq _ _ (bidders_of o) i1i2.1 i1i2.2 (ouniq o) in
  bubble_swap o i1i2 ->
    welfare_i o <= welfare_i (Outcome ts_uniq). 
Proof.
move=> /= /andP [lti1i2 ltt2t1].
set s1 := i1i2.1; set s2 := i1i2.2.
rewrite /welfare_i (bigD1 s2) 1?(bigD1 s1) //=;
  last by move/ltn_eqF/negbT: lti1i2. 
rewrite [X in _ <= X](bigD1 s2) ?[X in _ <= _ + X](bigD1 s1) //=;
  last by move/ltn_eqF/negbT: lti1i2.
rewrite addnA [X in _ <= X]addnA.
set sum1 := (X in _ + X); set sum2 := (X in _ <= _ + X).
have <-: sum1 = sum2. 
  set F2 := (X in _ = \sum_(i < k | _) X i).
  rewrite /sum1 (eq_bigr F2) // => s /andP [neis2 neis1].
  rewrite eq_sym in neis1; rewrite eq_sym in neis2.
  rewrite /F2 /bidding_i !ffunE /t_bidding_i /= eq_sym.
  move: (noio) => /eqfunP /(_ s) -> /=.
  set o_perm := (X in if tnth X s != _ then _ else 0). 
  have noio_perm: no_i_in o_perm. 
    apply/forallP => s'.
    rewrite /o_perm apermE permE !tnth_mktuple.
    - have [] := boolP (s1 == s') => [/eqP <- |nes1s'].
      by rewrite tpermL; move: noio => /forallP /(_ s2).
    - have [] := boolP (s2 == s') => [/eqP <- | nes2s'].
      by rewrite tpermR; move: noio => /forallP /(_ s1).
    - by rewrite tpermD //; move: noio => /forallP /(_ s').
  move: (noio_perm) => /eqfunP /(_ s). 
  rewrite eq_sym apermE permE tnth_mktuple tpermD // => -> /=.
  rewrite /t_bidding !mem_tnth /tuple_tperm memtE /=.
  have {F2 sum1 sum2} ipi1i2: s = tperm s1 s2 s by rewrite tpermD.
  rewrite ipi1i2 (@mem_map  _ _ (fun j => tnth o (tperm s1 s2 j))) ?mem_enum.
  rewrite !tpermD // cancel_slot [in RHS]/slot_of.
  case: tnthP => p.
  - case: sig_eqW => s' /=.
    rewrite tnth_mktuple ipi1i2.
    move/o_injective/perm_inj => <-.
    by rewrite tpermD.
  - have //=: ∃ s', tnth o s = 
      tnth [tuple tnth o (tperm s1 s2 s0) | s0 < k] s'
      by exists s; rewrite tnth_mktuple tpermD.
  move=> j s'.
  by move/o_injective/perm_inj.
rewrite leq_add2r {sum1 sum2} /bidding !ffunE /= /t_bidding_i /t_bidding.
rewrite !mem_tnth !apermE permE !tnth_mktuple tpermR tpermL.
rewrite (@tperm_slot _ s1 s2 s1) (@tperm_slot _ s1 s2 s2).
rewrite tpermL tpermR /bid_in !cancel_slot.
set i1 := tnth o s1; set i2 := tnth o s2.
have leb1b2: 'bid_i1 <= 'bid_i2 by exact: sorted_bs. 
have lec2c1: 'ctr_s2 <= 'ctr_s1 by move/ltnW/sorted_ctrs: lti1i2.
rewrite [X in _ <= X]addnC.
move/eqfunP/(_ s1): (noio); rewrite [in LHS]eq_sym => -> /=.
move/eqfunP /(_ s2): (noio); rewrite [in LHS]eq_sym => -> /=.
exact: leq_transpose.
Qed.

Lemma no_i_in_bubble_sort (o : O) i1i2s (noio : no_i_in o) :
  no_i_in (bubble_sort o i1i2s).2.
Proof.
apply/forallP.
elim: i1i2s => [/=|i1i2 i1i2s IH /=].
by move: noio; rewrite /no_i_in => /forallP.
rewrite apermE permE => s.
rewrite tnth_mktuple.
set s1 := i1i2.1; set s2 := i1i2.2. 
- have [] := boolP (s1 == s) => [/eqP <- |nes1s].
  rewrite tpermL. exact: IH.
- have [] := boolP (s2 == s) => [/eqP <- | ness2].
  rewrite tpermR. exact: IH.
- by rewrite tpermD. 
Qed.

Lemma le_welfare_noio_o_oStar_i (o : O)
      (noio : no_i_in o) :
  welfare_i o <= max_welfare_i.
Proof.
move: (bubble_sort_spec o) => [i1i2s] /= [x]. 
have lt_w_tw: forall i1i2s (o : O) (noio : no_i_in o),
    let xo := bubble_sort (bidders_of o) i1i2s in 
    let obu := @bubble_uniq _ _ (bidders_of o) i1i2s (ouniq o) in
    xo.1 -> welfare_i o <= welfare_i (Outcome obu). 
  rewrite /welfare_i /=.
  elim=> [o' _ _|i1i2 i1i2s' IH o' noio' /= /andP [x12 x12s']]. 
  - by apply: leq_sum => s _; rewrite !ffunE. 
  - set bo' := (bubble_sort o' i1i2s').2.
    set bo'_o := (Outcome (bubble_uniq i1i2s' (ouniq o'))).
    have noibo': no_i_in bo'_o by exact: no_i_in_bubble_sort.
    move: (@le_transposed_welfare_i i1i2 bo'_o noibo' x12) => /=.
    move: (IH o' noio' x12s').
    rewrite /welfare_i !alt_welfare_i /=.
    exact: leq_trans.
move=> sorted_bo.
move: (lt_w_tw i1i2s o noio x).
set bo := (X in _ <= welfare_i X) => ltwowbo.
have noibo: no_i_in bo by exact: no_i_in_bubble_sort.
have: up_sorted_tuple bo by [].
move/le_welfare_sorted_o_oStar_i => /(_ noibo).
exact: leq_trans.
Qed.

Definition t_o_without_i (o : O) (i' : A) :=
  map_tuple (fun j : A => if j != i then j else i') o.

Lemma o_without_i_uniq (o : O) (i' : A) 
      (neii' : i != i') 
      (noi'ino : i' \notin bidders_of o) :
  uniq o -> uniq (t_o_without_i o i').
Proof.
move=> uniqo. 
rewrite map_inj_in_uniq // => j1 j2 j1ino j2ino. 
- have [] := boolP (j1 == i) => [/eqP -> |_] /=.
  - have [] := boolP (j2 == i) => [/eqP -> //=|_ //= eqi'j2]. 
  - by move: noi'ino; rewrite eqi'j2 j2ino. 
- have [] := boolP (j2 != i) => _ //= eqi'j1.
  by move: noi'ino; rewrite -eqi'j1 j1ino.
Qed.

Lemma o_without_i_spec (o : O) (iino : i \in bidders_of o) :
  exists (o' : O), exists (i' : A), forall (s : slot), 
        (tnth o s = i -> tnth o' s = i') /\ 
        (tnth o s != i -> tnth o' s = tnth o s) /\
        i' \notin bidders_of o /\
        i' != i.
Proof.
have [i' _ noi'ino]: exists2 i', i' \in A & i' \notin bidders_of o.
  apply/subsetPn.
  apply: proper_subn.
  rewrite properE.
  apply/andP. split.
  - by apply/subsetP.
  - have (T: finType) (A B : predPredType T) : #|A| < #|B| -> ~~ (B \subset A).
      apply: contraL.
      rewrite -leqNgt.
      exact: subset_leq_card.
    apply.
    move: (ouniq o) => /card_uniqP ->.
    rewrite size_tuple card_ord.
    exact: lt_k_n.
have neii': i != i' by move: noi'ino; apply: contra => /eqP <-.
exists (Outcome (@o_without_i_uniq o i' neii' noi'ino (ouniq o))).
exists i' => s /=.
- split.
  rewrite tnth_map => ->.
  by rewrite eq_refl.
- split; last by rewrite eq_sym. 
  by rewrite tnth_map => ->.
Qed.

Lemma le_welfare_o_oStar_i (o : O) : welfare_i o <= max_welfare_i.
Proof.
- have [] := boolP (no_i_in o) => noio.
  exact: le_welfare_noio_o_oStar_i.
- have/(_ noio) iino: ~~ no_i_in o -> i \in bidders_of o.
    apply: contraR.
    exact: notin_no_in.
  move: (@o_without_i_spec o iino) => [o'] [i' diff_i].
  have/le_welfare_noio_o_oStar_i: no_i_in o'.
    apply/eqfunP => s.
    move: (diff_i s) => [eqi [neqi [noi'ino neii']]].
    - have [] := boolP (tnth o s == i) => eqosi.
      move/eqP/eqi: eqosi.
      rewrite eq_sym => ->.
      exact: negbTE.
    - move: (eqosi) => /neqi ->.
      rewrite eq_sym.
      exact: negbTE.
  have: welfare_i o <= welfare_i o'.  
    apply: leq_sum => s _.
    rewrite /bidding_i !ffunE /t_bidding_i.
    move: (diff_i s) => [eqi [neqi [noi'ino neii']]].
    have [] := boolP (tnth o s != i) => nei //.
    rewrite !(neqi nei) nei /t_bidding cancel_slot. 
    by rewrite -{3 5}(neqi nei) cancel_slot !mem_tnth. 
  exact: leq_trans.  
Qed.

End OStarForSearch_i.

Definition bs' := tuple_i bs bid0 (ltn_ord i).

Notation "'bid'_ j" := (tnth bs' j) (at level 10).

Definition ls' := tuple_i ls (tnth ls i) (ltn_ord i).

Notation "'lab'_ j" := (tnth ls' j) (at level 10).

Lemma eq_lab'_id (j : A) : j < i -> 'lab'_j = j.
Proof.  
have eqljj: 'lab_j = j by rewrite tnth_ord_tuple. 
by rewrite -[in RHS] eqljj; apply: id_tuple_i. 
Qed.

Lemma eq_lab'_succ (j : A) : i <= j  -> j < n.-1 -> 'lab'_j = agent_succ j.
Proof.
move=> leijn1.
have eqljj: forall j, 'lab_j = j by move=> ?; rewrite tnth_ord_tuple.
rewrite -[in RHS](eqljj (agent_succ j)). 
exact: shifted_tuple_i. 
Qed.

Lemma eq_lab'_last : 'lab'_ord_max = i.
Proof. by rewrite last_tuple_i tnth_ord_tuple. Qed.

Lemma commuting_succ_agent (s : slot) :
  i <= s ->
    s < k' ->
      slot_as_agent (slot_succ s) = agent_succ (slot_as_agent s).
Proof.
move=> leis ltsk'.
apply: val_inj => //=.
case: s leis ltsk' => [s' p] /= leis lts'k'.
move/ltn_eqF: (lts'k') => -> //=.
by have/ltn_eqF ->: s' < n' by exact: leq_trans lts'k' le_k_n.
Qed.

Lemma eq_in_oStars_out (j : A) :
  k' < j -> (j  \in bidders_of oStar) = ('lab'_ j  \in bidders_of oStar_i).
Proof.
move=> ltk'j.
move: lt_i_k; rewrite ltnS => leik'.
move/ltnW: (leq_ltn_trans leik' ltk'j) => leij.
rewrite not_in_oStar //.
apply: esym.
apply: negbTE.
- have [] := boolP (j < n') => ltjn'. 
  rewrite shifted_tuple_i // tnth_ord_tuple -has_pred1 -all_predC. 
  apply/all_tnthP => s /=.
  rewrite neq_ltn; apply/orP; left. 
  have ltasj1: agent_succ (slot_as_agent s) < ord_succ j.
    move/ltn_eqF: (lt_slot_n' s) => /= -> /=.
    rewrite /= eq_proper_addS /= ltnS.
    exact: leq_ltn_trans (leq_ord s) ltk'j.
  by move: (leq_ltn_trans (lt_oStar_succ s) ltasj1).
- move: ltjn'; rewrite -below_last_ord negbK => /eqP ->.
  rewrite eq_lab'_last -has_pred1 -all_predC. 
  apply/all_tnthP => s /=.
  - have [] := boolP (s < i) => ltsi.
    by rewrite id_tuple_i // tnth_mktuple -(inj_eq val_inj) ltn_eqF.
  - have [] := boolP (s < k') => ltsk'.
    move: ltsi; rewrite -leqNgt => leis.
    rewrite shifted_tuple_i // neq_ltn; apply/orP; right.
    rewrite tnth_mktuple widen_slot_as_agent /=. 
    by move: leis; rewrite -ltnS eq_proper_addS.
  - move: ltsk'; rewrite -below_last_ord negbK => /eqP ->.
    rewrite last_tuple_i -(inj_eq val_inj) /= inordK.
    rewrite neq_ltn; apply/orP; right.
    by rewrite ltnS.
  exact: lt_k_n. 
Qed.

Ltac inord_in_oStar j := 
   exists (inord j); rewrite tnth_mktuple; 
   apply: val_inj => /=; rewrite inordK //.
   
Lemma eq_in_oStars (j : A) :
   (j \in bidders_of oStar) = ('lab'_j \in bidders_of oStar_i).
Proof.
- have [] := boolP (j < i) => ltji. 
  rewrite eq_lab'_id //=.
  apply/tnthP/tnthP=> [[sj psj]|[sj psj]].
  exists sj; rewrite id_tuple_i //.
  by move: psj ltji => ->; rewrite tnth_mktuple. 
  inord_in_oStar j.
  exact: (ltn_trans _ lt_i_k).
- have [] := boolP (j < k') => ltjk'.
  move: ltji; rewrite -leqNgt => leij.
  move: (ltn_trans ltjk' (ltnSn k')) => ltjk. 
  move: (leq_trans ltjk' lt_k_n) => lejn'.  
  have ltk'n' : k' < n' by move: lt_k_n. 
  rewrite eq_lab'_succ //; last by exact: ltn_trans ltjk' ltk'n'.
  apply/tnthP/tnthP=> [[sj psj]|[sj psj]].
  exists (inord j); rewrite shifted_tuple_i //=; last first. 
  by rewrite inordK //. 
  by rewrite inordK //.
  rewrite tnth_mktuple widen_slot_as_agent commuting_succ_agent; 
    last by rewrite inordK. 
  have <- //: j = slot_as_agent (inord j)
    by apply: val_inj => /=; rewrite inordK.
  by rewrite inordK.
  by inord_in_oStar j.
- move: ltji; rewrite -leqNgt => leij.
  move: ltjk'; rewrite -leqNgt leq_eqVlt => /orP [/eqP eqk'j|ltk'j].
  apply/tnthP/tnthP => [[sj psj]|[sj psj]].
  - move: (psj) => ->; rewrite tnth_mktuple. 
    exists ord_max.
    rewrite last_tuple_i shifted_tuple_i /= ?tnth_ord_tuple; last first. 
    exact: lt_slot_n'.
    move/eqP: psj.
    by rewrite tnth_mktuple -(inj_eq val_inj) /= => /eqP <-.
    rewrite /succ_last_slot_agent widen_slot_as_agent.
    have -> /=: sj = last_slot.
      by apply: val_inj => /=; rewrite eqk'j psj tnth_mktuple. 
    apply: val_inj => /=; rewrite inordK.  
    move/ltn_eqF: (lt_slot_n' last_slot) => /=; apply: ifF.
    exact: lt_k_n.
  - inord_in_oStar j.
    by rewrite eqk'j ltnSn.
exact: eq_in_oStars_out.
Qed.

Lemma eq_slots (j : A) :
  (j \in bidders_of oStar) -> slot_of j oStar = slot_of ('lab'_j) oStar_i.
Proof.
move=> jino.
move: (jino). 
rewrite eq_in_oStars => jino_i.
rewrite slot_in_oStar // /slot_of. 
move: (@elimT _ _ (tnthP oStar_i ('lab'_j)) jino_i).
case: tnthP => pj /=. 
case: sig_eqW => sj psj _ //=.   
have: 'lab'_j = tnth oStar_i (inord j). 
- have [] := boolP (j < i) => ltji. 
  rewrite eq_lab'_id ?id_tuple_i ?tnth_mktuple //.
  apply: val_inj => /=; rewrite inordK //.
  apply: (ltn_trans ltji lt_i_k).  
  rewrite inordK //.
  exact: ltn_trans ltji lt_i_k.
- move: ltji; rewrite -leqNgt => leij. 
  have [] := boolP (j < k') => ltjk'.
  have ltjn': j < n'. 
    move: lt_k_n. 
    rewrite -subn_gt0 subSS subn_gt0.
    exact: ltn_trans ltjk'.
  have ltjk: j < k by exact: ltn_trans ltjk' (ltnSn k').
  rewrite eq_lab'_succ // shifted_tuple_i //; last first.
  by rewrite inordK //. 
  by rewrite inordK //.
  rewrite tnth_mktuple; apply: val_inj => /=.
  by rewrite !eq_proper_addS /= ?inordK.
- move: ltjk'.
  rewrite -leqNgt leq_eqVlt.
  have -> : (k' < j) = false.
    move: jino; apply: contraTF. 
    by move/not_in_oStar/negbT.
  rewrite orbF => /eqP eqk'j. 
  have ltjn': j < n' by rewrite -eqk'j; apply: lt_k_n.
  rewrite eq_lab'_succ //.
  have -> : tnth oStar_i (inord j) = tnth oStar_i ord_max.
    set s := (X in tnth _ X = _); set s' := (X in _ = tnth _ X).
    have -> //: s = s'.
      apply: val_inj => /=.
      rewrite inordK ?eq_sym // -eqk'j.
      exact: ltnSn.
  rewrite last_tuple_i /= /succ_last_slot_agent.
  apply: val_inj => /=. 
  by rewrite eq_proper_addS /= inordK eqk'j.
by rewrite psj;  move/(@o_injective oStar_i).
by [].
Qed.

Definition welfare_without_i'' := VCG.welfare_without_i'' i (biddings bs).

Definition VCG_bidSum'' := VCG.bidSum'' i (biddings bs).

Lemma argmax_bidSum'' :
  VCG_bidSum'' [arg max_(o > o0) VCG_bidSum'' o] = VCG_bidSum'' oStar_i.
Proof.
apply/anti_leq/andP; split; last first.
by rewrite -bigmax_eq_arg ?leq_bigmax.
rewrite -bigmax_eq_arg //.
apply/bigmax_leqP => o _.
rewrite /VCG_bidSum'' /VCG.bidSum''.
have body_o j o' : tnth (VCG.bs'' i (biddings bs)) j o' = t_bidding_i bs j o'.
  by rewrite !tnth_mktuple !ffunE. 
have body o': \sum_(j < n) tnth (VCG.bs'' i (biddings bs)) j o' =
              \sum_(j < n) t_bidding_i bs j o'.
  apply: eq_bigr => j _.
  exact: body_o.
rewrite (body o) (body oStar_i) => {body body_o}.
have bidSum_out_o_i (o' : O) :
    \sum_(j < n | j \notin (bidders_of o')) t_bidding_i bs j o' = 0.
  apply/eqP ; rewrite sum_nat_eq0.
  apply/forall_inP => j outo; apply/eqP.
  rewrite /t_bidding_i /t_bidding.
  case: (j != i) => //.
  by rewrite ifN.
rewrite (bigID (fun j : A => j \in (bidders_of o))) bidSum_out_o_i. 
rewrite [X in _ <= X](bigID (fun j : A => j \in (bidders_of oStar_i))) bidSum_out_o_i.
rewrite /= !addn0.
have eqww o' : welfare_i bs o' = \sum_(i in bidders_of o') t_bidding_i bs i o'.
  rewrite /welfare_i -(@big_tuple _ _ _ _ _ _ predT (fun j => bidding_i bs j o')).
  rewrite big_uniq /=; last by exact: ouniq. 
  rewrite (eq_bigr (fun j => t_bidding_i bs j o')) // => j _.
  by rewrite /bidding_i !ffunE.
rewrite -(eqww o).
set wo_i := (X in _ <= X).
have <- : max_welfare_i bs = wo_i by exact: eqww.
apply: le_welfare_o_oStar_i.
exact: sorted_bs.
Qed.

Definition bidSum' := @VCG.bidSum O_finType (biddings bs').

Lemma eq_welfare_without_i''_bidSum' : welfare_without_i'' = bidSum' oStar.
Proof.
rewrite /welfare_without_i'' /VCG.welfare_without_i'' /bidSum'.
rewrite (@bigmax_eq_arg _ o0 _ (fun o => VCG.bidSum'' i (biddings bs) o)) //. 
move: argmax_bidSum''; rewrite /VCG_bidSum'' => ->.
rewrite /VCG.bidSum'' /VCG.bidSum.
rewrite (bigID (fun j : A => j < i)) [in RHS](bigID (fun j : A => j < i)) /=.
congr (_ + _). 
- apply: eq_bigr => j ltji.
  rewrite !tnth_mktuple !ffunE ifT //; last by move/ltn_eqF/negbT: (ltji).
  rewrite /t_bidding /bid_in id_tuple_i //. 
  move: (eq_in_oStars j); rewrite eq_lab'_id // => <-.
  have [] // := boolP (j \in t_oStar) => inoS.
  by rewrite eq_slots ?eq_lab'_id.
- rewrite (bigID (fun j => j == i)) [in RHS](bigID (fun j => j == last_agent)) /=.
  congr (_ + _).
  - rewrite (big_pred1 i) ?(big_pred1 last_agent) => [|j|j].
    rewrite !tnth_mktuple !ffunE eq_refl /= /t_bidding.
    by have/not_in_oStar ->: k' < last_agent by exact: lt_k_n.
    rewrite pred1E andb_idl; first by rewrite eq_sym.
    by move=> /eqP ->; rewrite -leqNgt leq_ord.
    rewrite pred1E andb_idl; first by rewrite eq_sym.
    by move=> /eqP ->; rewrite ltnn.
  - have -> : \sum_(j < n | ~~ (j < i) && (j != i)) 
                tnth (VCG.bs'' i (biddings bs)) j oStar_i =
             \sum_(j < n | i < j) tnth (VCG.bs'' i (biddings bs)) j oStar_i.
      apply: eq_bigl => j.
      by rewrite -leqNgt ltn_neqAle eq_sym andbC.
    have -> :  \sum_(j < n | ~~ (j < i) && (j != last_agent))
                 tnth (biddings bs') j oStar =
              \sum_(j < n | i <= j < last_agent) tnth (biddings bs') j oStar.
      apply: eq_bigl => j.
      by rewrite -leqNgt below_last_ord.
    rewrite reindex_ge_i /=; last first.
    have le_k_n' : k <= n' by exact: lt_k_n.
    exact: leq_trans lt_i_k le_k_n'.
    exact: ltn0Sn.
    apply: eq_bigr => j /andP [leij ltjn'].
    rewrite !tnth_mktuple !ffunE ifT; last 
      by move/gtn_eqF/negbT: (leq_ltn_trans leij (lt_ord_succ ltjn')).
    rewrite /t_bidding /bid_in shifted_tuple_i //. 
    move: (eq_in_oStars j); rewrite eq_lab'_succ /agent_succ // => <-.
    have [] // := boolP (j \in t_oStar) => inoS.
    by rewrite eq_slots ?eq_lab'_succ.
Qed.

Lemma s_welfare_without_i'' :
  welfare_without_i'' =
    \sum_(s < k | s < i) bid_ctr_slot bs s +
    \sum_(s < k | i <= s) 'bid_(agent_succ (slot_as_agent s)) * 'ctr_s.
Proof.
rewrite eq_welfare_without_i''_bidSum' /bidSum' /VCG.bidSum. 
rewrite bidsSum_sumBid -valid_bidSum bidSum_slot.
rewrite (bigID (fun s : slot => s < i)) //=.
congr (_ + _ ).
- rewrite (eq_bigr (bid_ctr_slot bs)) //= => s ltsi.
  rewrite /bidding ffunE /t_bidding.
  rewrite mem_tnth /bid_in /bid_ctr_slot /slot_of //=.
  case: tnthP => p.
  case: sig_eqW => s' p' //=.
  rewrite tnth_mktuple widen_slot_as_agent.
  have <- : s = s' by exact: (@o_injective oStar).
  by rewrite id_tuple_i.
  have //=: (∃ s' : slot, tnth oStar s = tnth oStar s') by exists s.
- apply: eq_big => s.
  by rewrite -leqNgt.
  rewrite -leqNgt /bidding ffunE /t_bidding /bid_in => leis.
  rewrite mem_tnth.
  congr (_ * _); last first. 
  rewrite /slot_of.
  case: tnthP => p.
  case: sig_eqW => s'' /=.
  rewrite !tnth_mktuple.
  by move/widen_ord_inj => ->.
  have //=: ∃ i : 'I_k, tnth t_oStar s = tnth t_oStar i by exists s.
  rewrite shifted_tuple_i tnth_mktuple -?widen_slot_as_agent //=.
  exact: lt_slot_n'.
Qed.

(* VCG for Search price. *)

Definition vcg_price := @VCG.price [finType of O] o0 i (biddings bs).

Lemma eq_sorted_VCG_price : 
  i < k -> price sorted_bs0 i = vcg_price.
Proof.
move=> ltik.
rewrite /vcg_price /price /externality VCG.eq_price'' /VCG.price''.
rewrite -/welfare_without_i'' -/welfare_with_i.
rewrite s_welfare_without_i'' s_welfare_with_i.
rewrite -/bs subnDl.
- have [] := boolP (k' == 0) => /eqP eq0k'.
  rewrite [X in _ = X - _]sum_ord0 //; 
    last by apply: eq_leq; rewrite eq_i_ord0.
  rewrite !sum_out // subn0. 
  have ->: ord0 = last_slot by exact: val_inj.
  by rewrite if_same last_ctr_eq0 /= ?muln0 // eq0k'.
move: eq0k' => /eqP. rewrite -lt0n => lt0k'. 
set bc := fun s => 'bid_(slot_as_agent s) * 'ctr_s.
set bc' := fun s => 'bid_(slot_as_agent s) * 'ctr_(slot_pred s).
rewrite (eq_bigr (fun s : slot => (bc' s - bc s)));
  last by move=> j _; rewrite mulnBr //.
rewrite (@big_split_subn k (fun s => i < s) bc' bc) => [|s ltis]; last first.
rewrite leq_mul2l; apply/orP; right.
apply: sorted_ctrs; by rewrite leq_pred.
rewrite ltik.
set t := (X in _ - X = _).
apply/eqP; rewrite -(eqn_add2r t); apply/eqP. 
rewrite !subnK; last first.
- rewrite leq_sum //= => s _.
  by rewrite leq_mul2l sorted_ctrs ?orbT ?leq_pred.
case ltilast: (i < last_slot).
- rewrite reindex_ge_i ?[X in _ <= X](bigD1 ord_max) //=.
  rewrite big_cropr last_ctr_eq0 //= muln0 add0n.
  rewrite leq_sum // => s /andP [leis ltsk'].
  rewrite leq_mul //; last by rewrite sorted_ctrs ?le_ord_succ.
  by rewrite commuting_succ_agent. 
- move: ltilast. rewrite ltnNge. move/negbFE.
  rewrite leq_eqVlt => /orP [/eqP <-|].
  by rewrite sum0_gt_last.
  by rewrite not_lt_last_slot_i.
case ltilast: (i < last_slot).
- rewrite reindex_ge_i // [in RHS](bigD1 ord_max) //=. 
  rewrite big_cropr last_ctr_eq0  //= muln0 add0n.
  apply: eq_bigr => s /andP [leis ltsk'].
  rewrite /bc /bc' /slot_pred /slot_succ cancel_ord_succ //. 
  congr (_ * _). 
  by rewrite commuting_succ_agent.
- move: ltilast. rewrite ltnNge. move/negbFE.
  rewrite leq_eqVlt => /orP [/eqP <-|].
  rewrite sum0_gt_last (bigD1 last_slot) //=.
  rewrite last_ctr_eq0 //= muln0 add0n.
  rewrite big_pred0 /last_slot // => j.
  by rewrite below_last_ord ltnNge andbN. 
  by rewrite not_lt_last_slot_i.
Qed.

End VCGforSearchPrice.

(* Handle relabelling to use eq_sorted_VCG_price. *)

Definition geq_bid (b1 b2 : bid) := b1 >= b2.

Lemma transitive_geq_bid : transitive geq_bid.
Proof. exact/rev_trans/leq_trans. Qed.

Lemma reflexive_geq_bid : reflexive geq_bid.
Proof. move=> x. exact: leqnn. Qed.

Lemma anti_geq_bid: antisymmetric geq_bid.
Proof. by move=> x y /anti_leq /val_inj. Qed.

Lemma total_geq_bid: total geq_bid.
Proof. by move=> b1 b2; exact: leq_total. Qed.

Lemma sorted_bids_sorted bs : sorted_bids bs <-> sorted geq_bid bs.
Proof.
split=> sortedbs.
- apply: (@path_sorted _ geq_bid ord_max).
  apply/(pathP ord0) => j ltjz.
  move: j ltjz => [_|m m1].
  - have -> : nth ord0 (ord_max :: bs) 0 = ord_max by rewrite nth0.
    by move: (ltn_ord (nth ord0 bs 0)).
  - rewrite -nth_behead /behead /geq_bid.
    rewrite size_tuple in m1.
    have -> : m.+1 = Ordinal m1 by [].
    rewrite -tnth_nth.
    have eqmom : m = Ordinal (ltn_trans (ltnSn m) m1) by [].
    rewrite [X in nth ord0 _ X]eqmom -tnth_nth.
    by rewrite sortedbs //=.
- move=> j1 j2 lej1j2.
  rewrite !(tnth_nth ord0).
  have jin (j : A) : j \in [pred j' : A | j' < size bs].
    by rewrite unfold_in /= size_tuple ltn_ord.
  apply: (sorted_le_nth transitive_geq_bid leqnn) => //.
  exact: jin.
  exact: jin.
Qed.

Variable sort_labelling : bids -> labelling.

Definition labelling_of (bs : bids) :=
  if [forall j1 : A, forall j2 : A, (j1 <= j2) ==> (tnth bs j2 <= tnth bs j1)] then
    labelling_id
  else
    sort_labelling bs.

Lemma sort_tupleP T n r (t : n.-tuple T): size (sort r t) == n.
Proof. by rewrite size_sort size_tuple. Qed.
Canonical sort_tuple T n r t := Tuple (@sort_tupleP T n r t).

Definition tsort (bs : bids) := [tuple of sort geq_bid bs].

Definition bids_sort (bs : bids) : bids * labelling := (tsort bs, labelling_of bs).

Definition is_labelling (bs bs' : bids) ls' := 
  [forall j' : A, tnth bs' j' == tnth bs (tnth ls' j')].

Hypothesis labelling_spec : forall bs bs' ls',
    bids_sort bs = (bs', ls') -> is_labelling bs bs' ls'.

Lemma labelling_stable_spec bs : sorted_bids bs -> labelling_of bs = labelling_id.
Proof.
move=> sortedbs.
rewrite /labelling_of ifT //.
apply/forallP => j1.
apply/forallP => j2.
by move/implyP: (sortedbs j1 j2).
Qed.

Lemma bids_sort_spec bs0 bs ls :
  (bids_sort bs0 = (bs, ls) -> sorted_bids bs) /\
  (sorted_bids bs0 -> bids_sort bs0 = (bs0, labelling_id)).
Proof.
- split.
  rewrite (surjective_pairing (bids_sort bs0)).
  case=> isbs _.
  apply: (iffRL (sorted_bids_sorted bs)).
  rewrite -isbs sort_sorted //.
  exact: total_geq_bid.
- rewrite /bids_sort => sortedbs0. 
  have -> : tsort bs0 = bs0.
    apply: val_inj => /=.
    apply: (eq_sorted transitive_geq_bid anti_geq_bid). 
    apply: sort_sorted.
    apply: total_geq_bid.
    apply: (iffLR (sorted_bids_sorted bs0)) => //.
    apply: permEl.
    exact: perm_sort.
  by rewrite labelling_stable_spec.
Qed.

Definition relabelled_i_in_oStar i i' bs := exists bs' ls',
    bids_sort bs = (bs', ls') /\ tnth ls' i' = i /\ i' \in bidders_of oStar.

Lemma lt_relabelled_k (i i': A) bs : relabelled_i_in_oStar i i' bs -> i' < k.
Proof. move=> [bs' [ls']] [_ [_ [iino]]]; exact: lt_i_k. Qed.

Lemma id_relabelled_sorted (i : A) bs : 
  i \in bidders_of oStar -> sorted_bids bs -> relabelled_i_in_oStar i i bs.
Proof.
move=> iwins sortedbs.
exists bs. exists labelling_id.
move: (@bids_sort_spec bs bs ls) => [_ /(_ sortedbs)] ->. 
by rewrite tnth_ord_tuple.
Qed.

Section UnsortedVCG.

Variable (bs0 : bids).

Let bs := tsort bs0.
Let ls := (bids_sort bs0).2.

Lemma sortedbs : sorted_bids bs. 
Proof.
move: (@bids_sort_spec bs0 bs ls) => [].
by rewrite {1}(surjective_pairing (bids_sort bs0)) => /(_ erefl).
Qed.

Hypothesis uniq_oStar : singleton (max_bidSum_spec bs).

Variable (i i' : A).

Definition relabelled_price (iwins : relabelled_i_in_oStar i i' bs0) := price sortedbs i'.

Definition relabelled_vcg_price := vcg_price i' bs.

Conjecture VCG_price_sorting_invariant : relabelled_vcg_price = vcg_price i bs0.

Theorem eq_VCG_price (iwins : relabelled_i_in_oStar i i' bs0) :
  relabelled_price iwins = relabelled_vcg_price.
Proof.
have lti'k := lt_relabelled_k iwins.
move: iwins => [bs' [ls']] [bidssortbs [iasi' [iino]]]. 
rewrite /relabelled_price /relabelled_vcg_price.
exact: eq_sorted_VCG_price.
Qed.

End UnsortedVCG.

(* VCG for Search properties. *)

Section VCGProperties.

Variable bs0 : bids.

Variable (i i' : A) (iwins : relabelled_i_in_oStar i i' bs0).

Let bs := tsort bs0.

Hypothesis uniq_oStar : singleton (max_bidSum_spec bs).

Theorem no_positive_transfer : (* 0 <= externality *) 
  forall (s : slot), 'ctr_s <= 'ctr_(slot_pred s).
Proof. move=> s; apply: sorted_ctrs. exact: leq_pred. Qed.

Variable value_per_click : A -> nat.

Definition value := value_per_click i * 'ctr_(sOi i').

Definition value_is_bid_for_bids := bid_in bs i' (sOi i') = value.

Lemma bid_in_oStar (value_bs : value_is_bid_for_bids) :
  bidding bs i' (VCG.oStar o0 (biddings bs)) = value.
Proof. 
rewrite /bidding ffunE /t_bidding.
rewrite -/(VCG_oStar bs). 
rewrite (uniq_oStar (VCG_oStar_extremum bs) (oStar_extremum (sortedbs bs0))).
move: iwins => [bs' [ls']] [bidssortbs [iasi' [iino]]]. 
by rewrite ifT.
Qed.

Theorem rational (value_bs : value_is_bid_for_bids) :
  relabelled_price iwins  <= value.
Proof.
have ltik: i' < k by apply: (lt_relabelled_k iwins).
rewrite (eq_VCG_price uniq_oStar iwins) // /relabelled_vcg_price.
move: (@VCG.rational _ o0 i' (biddings bs) (tnth (biddings bs) i') erefl).
by rewrite -bid_in_oStar ?tnth_mktuple.
Qed.

(* (Partial) truthfulness of VCG for Seach. *)

From mathcomp Require Import ssrint rat ssralg ssrnum.

Import GRing.Theory.
Import Num.Theory.
Import Num.Def.
Import Order.Theory.

Open Scope ring_scope.

Section Utils.

Lemma le_NQ (n m : nat) : (n <= m)%N = (n%:Q <= m%:Q).
Proof. by rewrite ler_nat. Qed.

Lemma eq_divr (r s : rat) (lt0s : 0 < s) : r = (r * s) / s.
Proof. by rewrite -mulrA [X in (_ * X)]mulrC mulVr ?mulr1 ?unitf_gt0. Qed.

End Utils.

Section Utility.

Variable (bs0' : bids) (j l : A) (jwins : relabelled_i_in_oStar j l bs0').

Let bs' := tsort bs0'.

Hypothesis uniq_oStar' : singleton (max_bidSum_spec bs').

Definition click_rate := ('ctr_(sOi l))%:Q.

Definition per_click (n : nat) := n%:Q / click_rate.

Definition price_per_click := per_click (relabelled_price jwins).

Definition utility_per_click :=
  (* max needed since VCG.utility is a nat. *)
  maxr ((value_per_click j)%:Q - price_per_click) 0.

Definition utility := utility_per_click * click_rate.

Definition vcg_utility (j : A) v bs := (VCG.utility o0 j v bs)%:Q.

Definition value_bidding :=
  [ffun o : O => (value_per_click j * 'ctr_(sOi l))%nat].

Lemma eq_VCG_utility :
  0 < click_rate -> utility = vcg_utility l value_bidding (biddings bs').
Proof.
move=> posrate.
have ltlk :=  (@lt_relabelled_k j _ bs0' jwins).
rewrite /vcg_utility /VCG.utility. 
set bbs := biddings bs'.
rewrite /utility /utility_per_click.
- have [] := boolP (value_bidding (VCG.oStar o0 bbs) <= VCG.price o0 l bbs)%N => ltbid. 
  move: (ltbid); rewrite -subn_eq0 => /eqP ->.   
  rewrite le_NQ in ltbid.
  rewrite max_r ?mul0r //.  
  move: ltbid; rewrite ffunE subr_le0 PoszM intrM /price_per_click.
  rewrite (eq_VCG_price uniq_oStar' jwins).
  by rewrite /relabelled_vcg_price /vcg_price /per_click // -ler_pdivl_mulr.
- rewrite -ltnNge in ltbid. 
  rewrite max_l 1?mulrBl; last first.
  move: (ltnW ltbid); rewrite -lez_nat subr_ge0 ffunE PoszM.
  move: (eq_VCG_price uniq_oStar' jwins).
  rewrite /relabelled_vcg_price /vcg_price => <-.
  by rewrite ler_pdivr_mulr // -intrM ler_int.
  move: (ltbid); rewrite -ltz_nat -subzn; last by exact: ltnW ltbid.
  rewrite intrD => ltrbid.
  congr (_ + _).
  by rewrite ffunE PoszM intrM.
  rewrite /price_per_click /per_click (eq_VCG_price uniq_oStar' jwins).
  rewrite /relabelled_vcg_price /vcg_price // -mulrA mulVf; last by rewrite lt0r_neq0.
  by rewrite mulr1 mulrNz.
Qed.

End Utility.

Definition value_per_click_is_bid (bs0' : bids) (j l : A) := 
  [forall o : O, per_click l (bidding (tsort bs0') l o) == (value_per_click j)%:Q].

Definition differ_only_i j (bs bs' : bids) :=
  forall (j' : A), j' != j -> tnth bs' j' = tnth bs j'.

Lemma vcg_differ_only_i (j : A) (bs1 bs2 : bids)
      (diffi : differ_only_i j bs1 bs2) :
  VCG.differ_only_i j (biddings bs1) (biddings bs2).
Proof.
move=> j' nej'j.
apply/ffunP => o.
rewrite !tnth_mktuple !ffunE /t_bidding.
congr (if _ then (_ * _) else _)%nat.
by move/(_ j' nej'j): diffi => ->.
Qed.

Lemma VCGforSearch_stable_truthful (bs0' : bids) 
      (iwins' : relabelled_i_in_oStar i i' bs0') 
      (uniq_oStar' : singleton (max_bidSum_spec (tsort bs0'))) :
  value_per_click_is_bid bs0 i i' ->
  differ_only_i i' bs (tsort bs0') ->
  utility iwins' <= utility iwins.
Proof.
move=> isvaluebid diff.   
- have [] := boolP (0 < click_rate i') => iposrate.
  rewrite !eq_VCG_utility // /vcg_utility ?ler_nat. 
  apply: VCG.truthful => o; last by exact: vcg_differ_only_i.
  move/eqfunP/(_ o): isvaluebid. 
  rewrite tnth_mktuple /per_click /value_bidding [X in bidding _ _ _ = X]ffunE.    
  rewrite (@eq_divr (value_per_click i)%:Q (click_rate i')) // => /eqP. 
  rewrite -subr_eq0 -mulrBl mulrC mulrI_eq0 ?subr_eq0; 
    last by apply/lregP; rewrite lt0r_neq0 ?invr_gt0.
  rewrite -intrM => /eqP /(mulrIz _). 
  move/(_ (oner_neq0 _))=> /eqP.
    by rewrite -PoszM eqz_nat /bs => /eqP. 
- have: 0 <= click_rate i' by exact: ler0z. 
  rewrite /utility le0r => /orP [/eqP -> |/negbF].
  by rewrite !mulr0.
  by rewrite iposrate.
Qed.

Conjecture VCGforSearch_truthful : forall (bs0' : bids) (i'': A) 
      (iwins' : relabelled_i_in_oStar i i'' bs0')
      (uniq_oStar' : singleton (max_bidSum_spec (tsort bs0'))),
  value_per_click_is_bid bs0 i i' ->
  differ_only_i i' bs (tsort bs0') ->
  utility iwins' <= utility iwins.

End VCGProperties.

Print Assumptions VCGforSearch_stable_truthful.
Check VCGforSearch_stable_truthful.

