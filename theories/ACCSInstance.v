(*
   Copyright (c) 2024 Nomadic Labs
   Copyright (c) 2024 Paul Laforgue <paul.laforgue@nomadic-labs.com>
   Copyright (c) 2024 Léo Stefanesco <leo.stefanesco@mpi-sws.org>

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
*)

Require Import Coq.Program.Equality Coq.Strings.String.

From stdpp Require Import base countable finite gmap list gmultiset strings.
From Must Require Import TransitionSystems Must Completeness.

Definition name := string.
Definition name_eq_dec : forall (x y : name), { x = y } + { x <> y } := string_dec.

#[global] Instance name_eqdecision : EqDecision name. by exact name_eq_dec. Defined.
#[global] Instance name_countable' : Countable name. by exact string_countable. Defined.

Inductive proc : Type :=
| pr_output : name -> proc
| pr_par : proc -> proc -> proc
| pr_var : nat -> proc
| pr_rec : nat -> proc -> proc
| g : gproc -> proc

with gproc : Type :=
| gpr_success : gproc
| gpr_nil : gproc
| gpr_input : name -> proc -> gproc
| gpr_tau : proc -> gproc
| gpr_choice : gproc -> gproc -> gproc
.

Notation pr_success := (g gpr_success).
Notation pr_nil := (g gpr_nil).
Notation pr_input a p := (g (gpr_input a p)).
Notation pr_tau p := (g (gpr_tau p)).
Notation pr_choice p q := (g (gpr_choice p q)).

Infix "&" := pr_par (at level 50).
Infix "⊕" := pr_choice (at level 50).
Notation "! a" := (pr_output a) (at level 20).

Fixpoint proc_dec (x y : proc) : { x = y } + { x <> y }
with gproc_dec (x y : gproc) : { x = y } + { x <> y }.
Proof.
  decide equality; destruct (decide (n = n0)); eauto.
  decide equality; destruct (decide (n = n0)); eauto.
Qed.

#[global] Instance proc_eq_decision_instance : EqDecision proc.
Proof. by exact proc_dec. Defined.

Fixpoint size (p : proc) :=
  match p with
  | pr_output _ => 1
  | pr_par p q  => S (size p + size q)
  | pr_var _ => 1
  | pr_rec x p => S (size p)
  | g p => gsize p
  end

with gsize p :=
  match p with
  | gpr_success => 1
  | gpr_nil => 0
  | gpr_input a p => S (size p)
  | gpr_tau p => S (size p)
  | gpr_choice p q => S (gsize p + gsize q)
  end.

Fixpoint pr_subst id p q :=
  match p with
  | pr_output _ => p
  | pr_par p1 p2 => pr_par (pr_subst id p1 q) (pr_subst id p2 q)
  | pr_var id' => if decide (id = id') then q else p
  | pr_rec id' p' =>
    if decide (id = id') then p else pr_rec id' (pr_subst id p' q)
  | g gp => g (gpr_subst id gp q)
end

with gpr_subst id p q {struct p} := match p with
| gpr_success => p
| gpr_nil => p
| gpr_input a p =>
    gpr_input a (pr_subst id p q)
| gpr_tau p =>
    gpr_tau (pr_subst id p q)
| gpr_choice p1 p2 =>
    gpr_choice (gpr_subst id p1 q) (gpr_subst id p2 q)
end.

Inductive lts : proc -> Act name -> proc -> Prop :=
| lts_input : forall {a t},
    lts (pr_input a t) (ActExt (ActIn a)) t
| lts_output : forall {a},
    lts (pr_output a) (ActExt (ActOut a)) pr_nil
| lts_tau : forall {t},
    lts (pr_tau t) τ t
| lts_com : forall {μ p1 p2 q1 q2},
    lts p1 (ActExt μ) p2 ->
    lts q1 (ActExt (co μ)) q2 ->
    lts (pr_par p1 q1) τ (pr_par p2 q2)
| lts_parL : forall {α p1 p2 q},
    lts p1 α p2 ->
    lts (pr_par p1 q) α (pr_par p2 q)
| lts_parR : forall {α p q1 q2},
    lts q1 α q2 ->
    lts (pr_par p q1) α (pr_par p q2)
| lts_choiceL : forall {p1 p2 q α},
    lts (g p1) α q ->
    lts (pr_choice p1 p2) α q
| lts_choiceR : forall {p1 p2 q α},
    lts (g p2) α q ->
    lts (pr_choice p1 p2) α q
| lts_rec : forall {x p},
    lts (pr_rec x p) τ (pr_subst x p (pr_rec x p))
.

#[global] Hint Constructors lts:ccs.

Definition stable p := ~ exists q, lts p τ q.

Lemma guarded_does_no_output p a q : ¬ lts (g p) (ActExt $ ActOut a) q.
Proof. intros l. dependent induction l; eapply IHl; eauto. Defined.

Fixpoint moutputs_of p : gmultiset name :=
  match p with
  | g _ | pr_rec _ _ |pr_var _ => ∅
  | pr_output a => {[+ a +]}
  | pr_par p1 p2 => moutputs_of p1 ⊎ moutputs_of p2
  end.

Definition outputs_of p := dom (moutputs_of p).

Lemma mo_spec_l e a :
  a ∈ moutputs_of e -> {e' | lts e (ActExt $ ActOut a) e' /\ moutputs_of e' = moutputs_of e ∖ {[+ a +]}}.
Proof.
  intros mem.
  dependent induction e.
  + exists pr_nil.
    assert (a = n). multiset_solver. subst.
    repeat split; eauto with ccs. multiset_solver.
  + cbn in mem.
    destruct (decide (a ∈ moutputs_of e1)).
    destruct (IHe1 a e) as (e1' & lts__e1 & eq).
    exists (pr_par e1' e2). repeat split; eauto with ccs.
    multiset_solver.
    destruct (decide (a ∈ moutputs_of e2)).
    destruct (IHe2 a e) as (e2' & lts__e2 & eq).
    exists (pr_par e1 e2'). repeat split; eauto with ccs.
    multiset_solver.
    contradict mem. intro mem. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
    + exfalso. multiset_solver.
Qed.

Lemma mo_spec_r e a :
  {e' | lts e (ActExt $ ActOut a) e' /\ moutputs_of e' = moutputs_of e ∖ {[+ a +]}} -> a ∈ moutputs_of e.
Proof.
  dependent induction e; intros (e' & l & mem).
  + inversion l; subst. set_solver.
  + cbn.
    inversion l; subst.
    eapply gmultiset_elem_of_disj_union. left.
    eapply IHe1. exists p2. split.
    eassumption. cbn in mem. multiset_solver.
    eapply gmultiset_elem_of_disj_union. right.
    eapply IHe2. exists q2. split.
    eassumption. cbn in mem. multiset_solver.
  + inversion l.
  + inversion l.
  + now eapply guarded_does_no_output in l.
Qed.


Lemma outputs_of_spec1 p a : a ∈ outputs_of p -> {q | lts p (ActExt (ActOut a)) q}.
Proof.
  intros mem.
  eapply gmultiset_elem_of_dom in mem.
  eapply mo_spec_l in mem.
  firstorder.
Qed.

Lemma outputs_of_spec2 p a : {q | lts p (ActExt (ActOut a)) q} -> a ∈ outputs_of p.
  intros (p' & lts__p).
  dependent induction p.
  + eapply gmultiset_elem_of_dom.
    cbn. inversion lts__p; subst. multiset_solver.
  + inversion lts__p; subst.
    ++ eapply IHp1 in H3.
       cbn.
       eapply gmultiset_elem_of_dom.
       eapply gmultiset_elem_of_disj_union. left.
       now eapply gmultiset_elem_of_dom.
    ++ eapply IHp2 in H3.
       cbn.
       eapply gmultiset_elem_of_dom.
       eapply gmultiset_elem_of_disj_union. right.
       now eapply gmultiset_elem_of_dom.
  + inversion lts__p.
  + inversion lts__p.
  + now eapply guarded_does_no_output in lts__p.
Qed.

#[global] Program Instance CCS_Name_label : Label name := MkLabel _ _ _.

Fixpoint encode_proc (p: proc) : gen_tree (nat + (name + name)) :=
  match p with
  | pr_output a => GenLeaf (inr $ inl $ a)
  | pr_par p q => GenNode 0 [encode_proc p; encode_proc q]
  | g gp => GenNode 1 [encode_gproc gp]
  | pr_var x => GenNode 2 [GenLeaf $ inl x]
  | pr_rec x q => GenNode 3 [GenLeaf $ inl x; encode_proc q]
  end
with
encode_gproc (gp: gproc) : gen_tree (nat + (name + name)) :=
  match gp with
  | gpr_success => GenNode 0 []
  | gpr_nil => GenNode 1 []
  | gpr_input a p => GenNode 2 [GenLeaf (inr $ inr a); encode_proc p]
  | gpr_tau q => GenNode 3 [encode_proc q]
  | gpr_choice gp gq => GenNode 4 [encode_gproc gp; encode_gproc gq]
  end.
Fixpoint decode_proc (t: gen_tree (nat + (name + name))) : proc :=
  match t with
  | GenLeaf (inr ( inl a)) => pr_output a
  | GenNode 0 [ep; eq] => pr_par (decode_proc ep) (decode_proc eq)
  | GenNode 1 [egp] => g $ decode_gproc egp
  | GenNode 2 [GenLeaf (inl x)] => pr_var x
  | GenNode 3 [GenLeaf (inl x); egq] => pr_rec x (decode_proc egq)
  | _ => g gpr_success (* arbitrary *)
  end
with
decode_gproc (t: gen_tree (nat + (name + name))): gproc :=
  match t with
  | GenNode 0 [] => gpr_success
  | GenNode 1 [] => gpr_nil
  | GenNode 2 [GenLeaf (inr (inr a)); ep] => gpr_input a (decode_proc ep)
  | GenNode 3 [eq] => gpr_tau (decode_proc eq)
  | GenNode 4 [egp; egq] => gpr_choice (decode_gproc egp) (decode_gproc egq)
  | _ => gpr_success (* arbitrary *)
  end.

Require Import ssreflect.

Lemma encode_decide_procs p : decode_proc (encode_proc p) = p
with encode_decide_gprocs p : decode_gproc (encode_gproc p) = p.
Proof. all: case p =>//= *; f_equal=>//. Qed.

#[global] Instance proc_countable: Countable proc.
Proof.
  refine (inj_countable' encode_proc decode_proc _).
  apply encode_decide_procs.
Qed.

Lemma gset_nempty_ex (g : gset proc) : g ≠ ∅ -> {p | p ∈ g}.
Proof.
  intro n. destruct (elements g) eqn:eq.
  + destruct n. eapply elements_empty_iff in eq. set_solver.
  + exists p. eapply elem_of_elements. rewrite eq. set_solver.
Qed.

Definition name_eqb a b :=
  match name_eq_dec a b with
  | left eq => true
  | right neq => false
  end.

Lemma name_eqb_spec0 a b : name_eqb a b = true <-> a = b.
Proof. unfold name_eqb. split; destruct (name_eq_dec a b); eauto. inversion 1. Qed.

Lemma name_eqb_spec1 a b : name_eqb a b = false <-> a ≠ b.
Proof. unfold name_eqb. split; destruct (name_eq_dec a b); eauto. contradiction. Qed.

Fixpoint lts_set_output p a : gset proc :=
  match p with
  | g _ | pr_var _ | pr_rec _ _ => ∅
  | pr_output b => if name_eqb a b then {[ pr_nil ]} else ∅
  | pr_par p1 p2 =>
      let ps1 := lts_set_output p1 a in
      let ps2 := lts_set_output p2 a in
      (* fixme: find a way to map over sets. *)
      list_to_set (map (fun p => p & p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 & p) (elements ps2))
  end.

Fixpoint lts_set_input_g g a : gset proc :=
  match g with
  | gpr_input b p => if name_eqb a b then {[ p ]} else ∅
  | gpr_choice g1 g2 => lts_set_input_g g1 a ∪ lts_set_input_g g2 a
  | gpr_nil | gpr_success | gpr_tau _ => ∅
  end.

Fixpoint lts_set_input p a : gset proc :=
  match p with
  | g gp => lts_set_input_g gp a
  | pr_rec _ _ | pr_output _ | pr_var _ => ∅
  | pr_par p1 p2 =>
      let ps1 := lts_set_input p1 a in
      let ps2 := lts_set_input p2 a in
      list_to_set (map (fun p => p & p2) (elements ps1)) ∪ list_to_set (map (fun p => p1 & p) (elements ps2))
  end.

Fixpoint lts_set_tau_g gp : gset proc :=
  match gp with
  | gpr_nil | gpr_input _ _ | gpr_success => ∅
  | gpr_tau p => {[ p ]}
  | gpr_choice gp1 gp2 => lts_set_tau_g gp1 ∪ lts_set_tau_g gp2
  end.

Fixpoint lts_set_tau p : gset proc :=
  match p with
  | g gp => lts_set_tau_g gp
  | pr_var _ | pr_output _ => ∅
  | pr_rec x p => {[ pr_subst x p (pr_rec x p) ]}
  | pr_par p1 p2 =>
      let ps1_tau : gset proc := list_to_set (map (fun p => p & p2) (elements $ lts_set_tau p1)) in
      let ps2_tau : gset proc := list_to_set (map (fun p => p1 & p) (elements $ lts_set_tau p2)) in
      let ps_tau := ps1_tau ∪ ps2_tau in
      let acts1 := outputs_of p1 in
      let acts2 := outputs_of p2 in
      let ps1 :=
        flat_map (fun a =>
                    map
                      (fun '(p1 , p2) => p1 & p2)
                      (list_prod (elements $ lts_set_output p1 a) (elements $ lts_set_input p2 a)))
        (elements $ outputs_of p1) in
      let ps2 :=
        flat_map
          (fun a =>
             map
               (fun '(p1 , p2) => p1 & p2)
               (list_prod (elements $ lts_set_input p1 a) (elements $ lts_set_output p2 a)))
          (elements $ outputs_of p2)
      in
      ps_tau ∪ list_to_set ps1 ∪ list_to_set ps2
  end.

Lemma lts_set_output_spec0 p a q : q ∈ lts_set_output p a -> lts p (ActExt $ ActOut a) q.
Proof.
  intro mem.
  dependent induction p; simpl in mem; try now inversion mem.
  - case (name_eq_dec a n) in mem.
    + rewrite e. eapply name_eqb_spec0 in e. rewrite e in mem.
      replace q with pr_nil by multiset_solver. eauto with ccs.
    + eapply name_eqb_spec1 in n0. rewrite n0 in mem. inversion mem.
  - eapply elem_of_union in mem as [mem | mem];
      eapply elem_of_list_to_set, elem_of_list_fmap in mem as (q' & eq & mem); subst;
      rewrite elem_of_elements in mem; eauto with ccs.
Qed.

Lemma lts_set_output_spec1 p a q : lts p (ActExt $ ActOut a) q -> q ∈ lts_set_output p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. case name_eqb eqn:eq. set_solver. eapply name_eqb_spec1 in eq. contradiction.
Qed.

Lemma lts_set_input_spec0 p a q : q ∈ lts_set_input p a -> lts p (ActExt $ ActIn a) q.
  intro mem.
  dependent induction p; simpl in mem; try set_solver.
  + eapply elem_of_union in mem. destruct mem.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
    ++ eapply elem_of_list_to_set in H.
       eapply elem_of_list_fmap in H as (q' & eq & mem). subst.
       rewrite elem_of_elements in mem. eauto with ccs.
  + dependent induction g0; simpl in mem; try set_solver.
      ++ destruct (name_eq_dec a n).
         +++ subst. case name_eqb in mem.
             ++++ eapply elem_of_singleton_1 in mem. subst. eauto with ccs.
             ++++ inversion mem.
         +++ eapply name_eqb_spec1 in n0. rewrite n0 in mem. inversion mem.
      ++ eapply elem_of_union in mem. destruct mem; eauto with ccs.
Qed.

Lemma lts_set_input_spec1 p a q : lts p (ActExt $ ActIn a) q -> q ∈ lts_set_input p a.
Proof.
  intro l. dependent induction l; try set_solver.
  simpl. case name_eqb eqn:eq. set_solver. eapply name_eqb_spec1 in eq. contradiction.
Qed.

Lemma lts_set_tau_spec0 p q : q ∈ lts_set_tau p -> lts p τ q.
Proof.
  - intro mem.
    dependent induction p; simpl in mem.
    + set_solver.
    + eapply elem_of_union in mem. destruct mem as [mem1 | mem2].
      ++ eapply elem_of_union in mem1.
         destruct mem1.
         eapply elem_of_union in H as [mem1 | mem2].
         eapply elem_of_list_to_set, elem_of_list_fmap in mem1 as (t & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, elem_of_list_fmap in mem2 as (t & eq & h); subst.
         rewrite elem_of_elements in h. eauto with ccs.
         eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in H as (t & eq & h); subst.
         eapply elem_of_list_In, elem_of_list_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply elem_of_list_In, in_prod_iff in h' as (mem1 & mem2).
         eapply elem_of_list_In in mem1. rewrite elem_of_elements in mem1.
         eapply elem_of_list_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_output_spec0 in mem1.
         eapply lts_set_input_spec0 in mem2. eauto with ccs.
      ++ eapply elem_of_list_to_set, elem_of_list_In, in_flat_map in mem2 as (t & eq & h); subst.
         eapply elem_of_list_In, elem_of_list_fmap in h as ((t1 & t2) & eq' & h'). subst.
         eapply elem_of_list_In, in_prod_iff in h' as (mem1 & mem2).
         eapply elem_of_list_In in mem1. rewrite elem_of_elements in mem1.
         eapply elem_of_list_In in mem2. rewrite elem_of_elements in mem2.
         eapply lts_set_input_spec0 in mem1.
         eapply lts_set_output_spec0 in mem2. eauto with ccs.
    + inversion mem.
    + eapply elem_of_singleton_1 in mem. subst; eauto with ccs.
    + dependent induction g0; simpl in mem; try set_solver;
        try eapply elem_of_singleton_1 in mem; subst; eauto with ccs.
      eapply elem_of_union in mem as [mem1 | mem2]; eauto with ccs.
Qed.

Lemma lts_set_tau_spec1 p q : lts p τ q -> q ∈ lts_set_tau p.
  intro l. dependent induction l; simpl; try set_solver.
  destruct μ.
  - eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite elem_of_list_In in_flat_map.
    exists a. split.
    + eapply elem_of_list_In, elem_of_elements.
      eapply outputs_of_spec2. eauto.
    + eapply elem_of_list_In, elem_of_list_fmap.
      exists (p2 , q2). split.
      ++ reflexivity.
      ++ eapply elem_of_list_In, in_prod_iff; split; eapply elem_of_list_In, elem_of_elements.
         eapply lts_set_input_spec1; eauto with ccs.
         eapply lts_set_output_spec1; eauto with ccs.
  - eapply elem_of_union. left.
    eapply elem_of_union. right.
    eapply elem_of_list_to_set.
    rewrite elem_of_list_In in_flat_map.
    exists a. split.
    + eapply elem_of_list_In, elem_of_elements.
      eapply outputs_of_spec2. eauto.
    + eapply elem_of_list_In, elem_of_list_fmap.
      exists (p2 , q2). split.
      ++ reflexivity.
      ++ eapply elem_of_list_In, in_prod_iff; split; eapply elem_of_list_In, elem_of_elements.
         eapply lts_set_output_spec1; eauto with ccs.
         eapply lts_set_input_spec1; eauto with ccs.
Qed.

Definition lts_set (p : proc) (α : Act name): gset proc :=
  match α with
  | τ => lts_set_tau p
  | ActExt (ActIn a) => lts_set_input p a
  | ActExt (ActOut a) => lts_set_output p a
  end.

Lemma lts_set_spec0 p α q : q ∈ lts_set p α -> lts p α q.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec0.
  - now eapply lts_set_output_spec0.
  - now eapply lts_set_tau_spec0.
Qed.

Lemma lts_set_spec1 p α q : lts p α q -> q ∈ lts_set p α.
Proof.
  destruct α as [[a|a]|].
  - now eapply lts_set_input_spec1.
  - now eapply lts_set_output_spec1.
  - now eapply lts_set_tau_spec1.
Qed.

Definition proc_stable p α := lts_set p α = ∅.

Lemma lts_dec p α q : { lts p α q } + { ~ lts p α q }.
Proof.
  destruct (decide (q ∈ lts_set p α)).
  - eapply lts_set_spec0 in e. eauto.
  - right. intro l. now eapply lts_set_spec1 in l.
Qed.

Lemma proc_stable_dec p α : Decision (proc_stable p α).
Proof. destruct (decide (lts_set p α = ∅)); [ left | right ]; eauto. Qed.

(* same as in ProcInstances *)
#[global] Program Instance CCS_lts : Lts proc name := {|
    lts_step x ℓ y  := lts x ℓ y;
    lts_stable p := proc_stable p;
    lts_outputs := outputs_of;
    |}.
Next Obligation. apply lts_dec. Qed.
Next Obligation.
  move=> /= ????. apply outputs_of_spec2. eauto.
Qed.
Next Obligation.
  intros. simpl. now eapply outputs_of_spec1 in H.
Qed.
Next Obligation. exact (proc_stable_dec). Qed.
Next Obligation.
  intros p [[a|a]|]; intro hs; eapply gset_nempty_ex in hs as (r & l); exists r; now eapply lts_set_spec0.
Qed.
Next Obligation.
  intros p [[a|a]|]; intros (q & mem); intro eq; eapply lts_set_spec1 in mem; set_solver.
Qed.

#[global] Instance CCS_finite : FiniteLts proc name.
Proof.
  constructor; [apply _|]. intros p ℓ. unfold dsig.
  destruct ℓ as [[a|a]|].
  - eapply (in_list_finite (elements (lts_set_input p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_input_spec1.
  - eapply (in_list_finite (elements (lts_set_output p a))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_output_spec1.
  - eapply (in_list_finite (elements (lts_set_tau p))).
    intros q Htrans%bool_decide_unpack.
    now eapply elem_of_elements, lts_set_tau_spec1.
Qed.

Require Import Relations.

Inductive cgr_step : proc -> proc -> Prop :=
| cgr_refl : forall p, cgr_step p p
| cgr_par : forall p q r t,
    cgr_step p q ->
    cgr_step r t ->
    cgr_step (pr_par p r) (pr_par q t)
| cgr_par_nil : forall p,
    cgr_step (pr_par p pr_nil) p
| cgr_par_nil_rev : forall p,
    cgr_step p (pr_par p pr_nil)
| cgr_par_com : forall p q,
    cgr_step (pr_par p q) (pr_par q p)
| cgr_par_ass : forall p q r,
    cgr_step (pr_par (pr_par p q) r) (pr_par p (pr_par q r))
| cgr_par_ass_rev : forall p q r,
    cgr_step (pr_par p (pr_par q r)) (pr_par (pr_par p q) r)
| cgr_rec : forall x p q,
    cgr_step p q -> cgr_step (pr_rec x p) (pr_rec x q)
| cgr_tau : forall p q,
    cgr_step p q ->
    cgr_step (pr_tau p) (pr_tau q)
| cgr_input : forall a p q,
    cgr_step p q ->
    cgr_step (pr_input a p) (pr_input a q)
| cgr_choice : forall p1 q1 p2 q2,
    cgr_step (g p1) (g q1) -> cgr_step (g p2) (g q2) ->
    cgr_step (pr_choice p1 p2) (pr_choice q1 q2)
| cgr_choice_nil : forall p,
    cgr_step (pr_choice p gpr_nil) (g p)
| cgr_choice_nil_rev : forall p,
    cgr_step (g p) (pr_choice p gpr_nil)
| cgr_choice_com : forall p q,
    cgr_step (pr_choice p q) (pr_choice q p)
| cgr_choice_ass : forall p q r,
    cgr_step
      (pr_choice (gpr_choice p q) r)
      (pr_choice p (gpr_choice q r))
| cgr_choice_ass_rev : forall p q r,
    cgr_step
      (pr_choice p (gpr_choice q r))
      (pr_choice (gpr_choice p q) r)
.

#[global] Hint Constructors cgr_step:ccs.


Infix "≡" := cgr_step (at level 70).

Definition cgr := (clos_trans proc cgr_step).

Infix "≡*" := cgr (at level 70).

#[global] Instance cgr_step_refl : Reflexive cgr_step.
Proof. eauto with ccs. Qed.

#[global] Instance cgr_step_symm : Symmetric cgr_step.
Proof. intros p q hcgr. induction hcgr; eauto with ccs. Qed.

#[global] Instance cgr_symm : Symmetric cgr.
Proof. intros p q hcgr. induction hcgr. constructor. now apply cgr_step_symm. eapply t_trans; eauto. Qed.

#[global] Instance cgr_trans : Transitive cgr.
Proof. intros p q r hcgr1 hcgr2. eapply t_trans; eauto. Qed.

#[global] Hint Resolve cgr_step_refl cgr_step_symm cgr_trans:ccs.

#[global] Instance cgr_is_eq_rel  : Equivalence cgr.
Proof. repeat split.
       + now constructor; eauto with ccs.
       + eapply cgr_symm.
       + eapply cgr_trans.
Qed.

Require Import Coq.Wellfounded.Inverse_Image.

Lemma cgr_step_subst1 (p : proc) : forall q q' x, q ≡ q' → pr_subst x p q ≡ pr_subst x p q'.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  destruct p; subst; simpl; intros; eauto with ccs.
  - eapply cgr_par; eapply Hp; simpl; [lia | eassumption | lia | eassumption].
  - destruct (decide (x = n)); subst; simpl; eauto with ccs.
  - destruct (decide (x = n)); subst; simpl; eauto with ccs.
  - destruct g0; subst; simpl; eauto with ccs.
    eapply cgr_choice.
    set (h := Hp (g g0_1) ltac:(simpl; lia) q q' x H). eauto.
    set (h := Hp (g g0_2) ltac:(simpl; lia) q q' x H). eauto.
Qed.

Lemma cgr_subst1 p q q' x : q ≡* q' → pr_subst x p q ≡* pr_subst x p q'.
Proof. intros hcgr. induction hcgr. constructor. now eapply cgr_step_subst1. eauto with ccs. Qed.

Lemma cgr_step_subst2 : forall p p' q x, p ≡ p' → pr_subst x p q ≡ pr_subst x p' q.
Proof.
  induction p as (p & Hp) using
    (well_founded_induction (wf_inverse_image _ nat _ size Nat.lt_wf_0)).
  intros p' q n hcgr. inversion hcgr; subst; simpl; eauto with ccs.
  - eapply cgr_par; eapply Hp; simpl; [lia | eassumption | lia | eassumption].
  - destruct (decide (n = x)); subst; eauto with ccs.
  - eapply cgr_choice.
    set (h := Hp (g p1) ltac:(simpl; lia) (g q1) q n H). eauto.
    set (h := Hp (g p2) ltac:(simpl; lia) (g q2) q n H0). eauto.
Qed.

Lemma cgr_subst2 q p p' x : p ≡* p' → pr_subst x p q ≡* pr_subst x p' q.
Proof. intros hcgr. induction hcgr. constructor. now eapply cgr_step_subst2. eauto with ccs. Qed.

Lemma cgr_subst p q x : p ≡ q -> pr_subst x p (pr_rec x p) ≡* pr_subst x q (pr_rec x q).
Proof.
  intro heq.
  etrans.
  eapply cgr_subst2. constructor. eassumption.
  eapply cgr_subst1. constructor. now eapply cgr_rec.
Qed.

#[global] Hint Resolve cgr_is_eq_rel: ccs.
#[global] Hint Constructors clos_trans:ccs.
#[global] Hint Unfold cgr:ccs.

Lemma cgr_par_left p1 p2 q : p1 ≡* p2 -> p1 & q ≡* p2 & q.
Proof. induction 1; eauto with ccs. Qed.

Lemma cgr_par_right p q1 q2 : q1 ≡* q2 -> p & q1 ≡* p & q2.
Proof. induction 1; eauto with ccs. Qed.

Lemma harmony_cgr : forall p q α, (exists r, p ≡* r /\ lts r α q) -> (exists r, lts p α r /\ r ≡* q).
Proof.
  intros p q α (p' & hcgr & l).
  revert q α l.
  dependent induction hcgr.
  - dependent induction H.
    + eauto with ccs.
    + intros u α l. dependent induction l.
      ++ destruct (IHcgr_step1 _ _ l1) as (? & ? & ?); eauto with ccs.
         destruct (IHcgr_step2 _ _ l2) as (? & ? & ?); eauto with ccs.
         exists (x & x0). split. eauto with ccs.
         etrans. eapply cgr_par_left. eassumption.
         etrans. eapply cgr_par_right. eassumption.
         reflexivity.
      ++ destruct (IHcgr_step1 _ _ l) as (? & ? & ?); eauto with ccs.
         exists (x & r). split. eauto with ccs.
         etrans. eapply cgr_par_left. eassumption.
         eapply cgr_par_right. now constructor.
      ++ destruct (IHcgr_step2 _ _ l) as (? & ? & ?); eauto with ccs.
         exists (p & x). split. eauto with ccs.
         etrans. eapply cgr_par_right. eassumption.
         eapply cgr_par_left. now constructor.
    + intros q α l. eexists. eauto with ccs.
    + intros q α l. inversion l; subst.
      inversion H4. eexists. eauto with ccs. inversion H3.
    + intros t α l. dependent induction l.
      ++ eexists. split; [eapply lts_com|]; eauto with ccs. now rewrite co_involution.
      ++ exists (p & p2). eauto with ccs.
      ++ exists (q2 & q). eauto with ccs.
    + intros t α l. dependent induction l.
      ++ dependent induction l2; eexists; split; eauto with ccs.
      ++ eexists. split; eauto with ccs.
      ++ dependent induction l; eexists; split; eauto with ccs.
    + intros t α l. dependent induction l.
      ++ dependent induction l1; eexists; split; eauto with ccs.
      ++ dependent induction l; eexists; split; eauto with ccs.
      ++ eexists. split; eauto with ccs.
    + intros t α l. inversion l; subst.
      exists (pr_subst x p (pr_rec x p)). split. eauto with ccs. now eapply cgr_subst.
    + intros t α l. inversion l; subst; eexists; split; eauto with ccs.
    + intros t α l. inversion l; subst; eexists; split; eauto with ccs.
    + intros t α l. dependent induction l.
      ++ destruct (IHcgr_step1 _ _ l) as (? & ? & ?); eauto with ccs.
      ++ destruct (IHcgr_step2 _ _ l) as (? & ? & ?); eauto with ccs.
    + intros t α l. inversion l; subst; eexists; split; eauto with ccs.
    + intros t α l. inversion l; subst. eexists; split; eauto with ccs. inversion H3.
    + intros t α l. dependent induction l; inversion l; subst; eexists; eauto with ccs.
    + intros t α l. inversion l; subst.
      ++ exists t. split; eauto with ccs.
      ++ inversion H3; subst; exists t; split; eauto with ccs.
    + intros t α l. inversion l; subst.
      ++ inversion H3; subst; exists t; split; eauto with ccs.
      ++ exists t. split; eauto with ccs.
  - intros t α l.
    eapply IHhcgr2 in l as (r & l3 & hcgr3).
    eapply IHhcgr1 in l3 as (u & l4 & hcgr4).
    eauto with ccs.
Qed.

#[global] Program Instance CCS_EqLTS : LtsEq proc name :=
  {|
    eq_rel p q  := cgr p q;
    eq_symm p q := cgr_symm p q;
    eq_trans p q r := cgr_trans p q r;
    eq_spec p q α := harmony_cgr p q α;
  |}.
Next Obligation. reflexivity. Qed.

Lemma output_shape p q a :
  lts p (ActExt $ ActOut a) q -> pr_par (pr_output a) q ≡* p.
Proof.
  intros l.
  dependent induction l.
  + eauto with ccs.
  + eapply t_trans.
    constructor. eapply cgr_par_ass_rev.
    eapply cgr_par_left. eauto.
  + transitivity (! a & (q2 & p)). eauto with ccs.
    transitivity ((! a & q2) & p). eauto with ccs.
    symmetry. etrans. constructor. eapply cgr_par_com.
    symmetry. eapply cgr_par_left. eauto with ccs.
  + edestruct guarded_does_no_output; eauto.
  + edestruct guarded_does_no_output; eauto.
Qed.

Definition lts_eq p α q := exists r, lts p α r /\ cgr r q.

Lemma aux0 (p q r : proc) (a : name) (α : Act name) :
  lts p (ActExt (ActOut a)) q -> lts q α r ->
  (exists t, lts p α t /\ lts_eq t (ActExt (ActOut a)) r).
Proof.
  intros l1 l2.
  eapply output_shape in l1.
  edestruct (harmony_cgr p (!a & r) α) as (t & l3 & l4).
  exists (! a & q). split. now symmetry. eapply lts_parR. eassumption.
  exists t. split. eassumption.
  edestruct (harmony_cgr t (pr_nil & r) (ActExt (ActOut a))) as (u & l5 & l6).
  exists (!a & r). split. eassumption. eapply lts_parL, lts_output.
  exists u. split; eauto with ccs.
  etrans; eauto with ccs.
Qed.

Lemma aux1 (p q1 q2 : proc) (a : name) (μ : ExtAct name) :
  μ ≠ ActOut a →
  lts p (ActExt $ ActOut a) q1 →
  lts p (ActExt μ) q2 →
  ∃ r : proc, lts q1 (ActExt μ) r ∧ lts_eq q2 (ActExt $ ActOut a) r.
Proof.
  intros.
  eapply output_shape in H0.
  edestruct (harmony_cgr (!a & q1) q2 (ActExt μ)) as (t & l3 & l4). eauto.
  inversion l3; subst.
  inversion H6. subst. now destruct H.
  exists q3. split. eassumption.
  edestruct (harmony_cgr q2 (pr_nil & q3) (ActExt $ ActOut a)) as (r & l5 & l6).
  exists (!a & q3). split. symmetry. eassumption. eapply lts_parL, lts_output.
  exists r. split. eassumption. etrans; eauto with ccs.
Qed.

Lemma aux2 (p q1 q2 : proc) (a : name) :
  lts p (ActExt $ ActOut a) q1 → lts p τ q2 →
  (∃ t : proc, lts q1 τ t ∧ lts_eq q2 (ActExt $ ActOut a) t) ∨ lts_eq q1 (ActExt $ ActIn a) q2.
Proof.
  intros l1 l2.
  eapply output_shape in l1.
  edestruct (harmony_cgr (!a & q1) q2 τ) as (t & l & heq). eauto with ccs.
  dependent induction l.
  - inversion l0; subst. right.
    exists q0. split. eassumption.
    etrans. constructor. eapply cgr_par_nil_rev.
    etrans. constructor. eapply cgr_par_com. eassumption.
  - inversion l.
  - left. exists q0. split. eassumption.
    edestruct (harmony_cgr q2 (pr_nil & q0) (ActExt $ ActOut a)) as (t' & l' & heq').
    exists (!a & q0). split. now symmetry. eapply lts_parL. eapply lts_output.
    exists t'. split; eauto with ccs.
    symmetry. etrans. constructor. eapply cgr_par_nil_rev.
    etrans. constructor. eapply cgr_par_com.
    now symmetry.
Qed.

Lemma aux3 p1 p2 p3 a : lts p1 (ActExt $ ActOut a) p2 → lts p1 (ActExt $ ActOut a) p3 -> p2 ≡* p3.
Proof.
  intros l1 l2. revert p3 l2.
  dependent induction l1; intros.
  - inversion l2; subst. eauto with ccs.
  - inversion l2; subst.
    + eapply IHl1 in H3; eauto with ccs. now eapply cgr_par_left.
    + eapply output_shape in H3. eapply output_shape in l1.
      etrans. eapply cgr_par_right. symmetry. eapply H3.
      symmetry.
      etrans. eapply cgr_par_left. symmetry. eapply l1.
      etrans. constructor. eapply cgr_par. eapply cgr_par_com. reflexivity.
      eauto with ccs.
  - inversion l2; subst.
    + eapply output_shape in H3. eapply output_shape in l1.
      etrans. eapply cgr_par_left. symmetry. eapply H3.
      symmetry. etrans. eapply cgr_par_right. symmetry. eapply l1.
      etrans. constructor. eapply cgr_par_ass_rev. eauto with ccs.
    + eapply IHl1 in H3; eauto with ccs. now eapply cgr_par_right.
  - exfalso. eapply guarded_does_no_output. eassumption.
  - exfalso. eapply guarded_does_no_output. eassumption.
Qed.

Lemma eq_spec_inv p1 p2 q1 q2 a :
  lts p1 (ActExt $ ActOut a) q1 -> lts p2 (ActExt $ ActOut a) q2 -> q1 ≡* q2 -> p1 ≡* p2.
Proof.
  intros l1 l2 heq. eapply output_shape in l1. eapply output_shape in l2.
  etrans. symmetry. eassumption.
  symmetry. etrans. symmetry. eassumption.
  eapply cgr_par_right. now symmetry.
Qed.

Lemma mo_equiv_spec_step : forall {p q}, p ≡ q -> moutputs_of p = moutputs_of q.
Proof. intros. dependent induction H; multiset_solver. Qed.

Lemma mo_equiv_spec : forall {p q}, p ≡* q -> moutputs_of p = moutputs_of q.
Proof.
  intros p q hcgr.
  induction hcgr. now eapply mo_equiv_spec_step.
  etrans; eauto.
Qed.

Lemma mo_spec p a q : p ⟶[ActOut a] q -> moutputs_of p = {[+ a +]} ⊎ moutputs_of q.
Proof.
  intros l. eapply output_shape, mo_equiv_spec in l. simpl in l. eauto.
Qed.

#[global] Program Instance CCS_ltsOba : LtsOba proc name :=
  {| lts_oba_mo p := moutputs_of p |}.
Next Obligation.
  intros. simpl. unfold outputs_of.
  now rewrite gmultiset_elem_of_dom.
Qed.
Next Obligation.
  intros. simpl. unfold outputs_of.
  now eapply mo_spec.
Qed.
Next Obligation. eapply aux0. Qed.
Next Obligation. eapply aux1. Qed.
Next Obligation. eapply aux2. Qed.
Next Obligation. eapply aux3. Qed.
Next Obligation. exact (eq_spec_inv). Qed.

#[global] Program Instance ACCS_ltsObaFB : @LtsObaFB proc name _ CCS_lts CCS_EqLTS CCS_ltsOba.
Next Obligation.
  intros p1 p2 p3 a l1 l2.
  eapply output_shape in l1.
  edestruct (harmony_cgr p1 (pr_nil & p3) τ) as (t & l & heq).
  exists (!a & p2). split. now symmetry.
  eapply lts_com. eapply lts_output. simpl in l2. eapply l2.
  exists t. split. eassumption.
  etrans. eassumption.
  etrans. constructor. eapply cgr_par_com.
  symmetry. etrans. constructor. eapply cgr_par_nil_rev. reflexivity.
Qed.

Inductive good : proc -> Prop :=
| good_success : good pr_success
| good_par : forall p q, good p \/ good q -> good (pr_par p q)
| good_choice : forall p q, good (g p) \/ good (g q) -> good (pr_choice p q).

#[global] Hint Constructors good:ccs.

#[global] Instance good_decidable e : Decision $ good e.
Proof.
  dependent induction e; try (now right; inversion 1).
  - destruct IHe1; destruct IHe2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
  - dependent induction g0; try (now right; inversion 1); try (now left; eauto with ccs).
    destruct IHg0_1; destruct IHg0_2; try (now left; eauto with ccs).
    right. inversion 1; naive_solver.
Qed.

Lemma good_preserved_by_cgr_step p q : good p -> p ≡ q -> good q.
Proof.
  intros hg hcgr.
  dependent induction hcgr;
    try (inversion hg; subst; destruct H0);
    try (inversion H; subst; destruct H1);
    eauto with ccs.
Qed.

Lemma good_preserved_by_cgr p q : good p -> p ≡* q -> good q.
Proof.
  intros hg hcgr.
  dependent induction hcgr; [eapply good_preserved_by_cgr_step|]; eauto.
Qed.

Lemma good_preserved_by_output p q a : good p -> lts p (ActExt $ ActOut a) q -> good q.
Proof.
  intros hhp hl.
  eapply output_shape in hl.
  eapply (good_preserved_by_cgr p (!a & q)) in hhp; eauto with ccs.
  inversion hhp; subst. destruct H0; eauto with ccs. inversion H.
  now symmetry.
Qed.

Lemma good_preserved_by_lts_output_converse p q a : lts p (ActExt $ ActOut a) q -> good q -> good p.
Proof.
  intros hl hhq.
  eapply output_shape in hl.
  eapply good_preserved_by_cgr.
  eapply good_par. right.
  eauto with ccs. eauto with ccs.
Qed.

#[global] Program Instance CCS_Good : @Good proc name good CCS_Name_label CCS_lts CCS_EqLTS.
Next Obligation. intros. eapply good_preserved_by_cgr; eassumption. Qed.
Next Obligation. intros. eapply good_preserved_by_output; eassumption. Qed.
Next Obligation. intros. eapply good_preserved_by_lts_output_converse; eassumption. Qed.

Fixpoint gen_test s p :=
  match s with
  | [] => p
  | ActIn a :: s' => ! a & gen_test s' p
  | ActOut a :: s' => gpr_input a (gen_test s' p) ⊕ gpr_tau pr_success
  end.

Lemma gen_test_lts_mu μ s p :
  lts_eq (gen_test (μ :: s) p) (ActExt (co μ)) (gen_test s p).
Proof. intros. destruct μ; simpl; eexists; split; eauto with ccs. Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex s p :
  (exists q, lts p τ q) -> exists e, lts (gen_test s p) τ e.
Proof.
  intros hq. induction s.
  + eauto with ccs.
  + destruct a; subst; simpl; [destruct IHs|]; eexists; eauto with ccs.
Qed.

Lemma gen_test_gen_spec_out_lts_tau_ex_inst a s p :
  exists e', lts (gen_test (ActOut a :: s) p) τ e'.
Proof. simpl. eauto with ccs. Qed.

Lemma gen_test_ungood_if p : ¬ good p -> forall s, ¬ good (gen_test s p).
Proof.
  intros nhp s nhg.
  induction s as [|μ s']; simpl in *.
  - contradiction.
  - destruct μ.
    + inversion nhg; subst. destruct H0. inversion H. contradiction.
    + inversion nhg; subst. destruct H0; inversion H.
Qed.

Lemma gen_test_gen_spec_out_lts_tau_good a s e p :
  lts (gen_test (ActOut a :: s) p) τ e -> good e.
Proof.
  inversion 1; subst; inversion H4; subst; eauto with ccs.
Qed.

Lemma gen_test_gen_spec_out_lts_mu_uniq e a μ s p :
  lts (gen_test (ActOut a :: s) p) (ActExt $ μ) e -> e = gen_test s p /\ μ = ActIn a.
Proof.
  intros. inversion H; subst; inversion H4; subst; eauto.
Qed.

Definition gen_conv s := gen_test s (pr_tau pr_success).

#[global] Program Instance gen_conv_gen_test_inst : gen_spec gen_conv.
Next Obligation.
  intros. eapply gen_test_ungood_if; try eassumption. inversion 1.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. eapply gen_test_gen_spec_out_lts_tau_ex_inst.
Qed.
Next Obligation.
  intros. eapply gen_test_gen_spec_out_lts_tau_good. eassumption.
Qed.
Next Obligation.
  intros. eapply gen_test_gen_spec_out_lts_mu_uniq. eassumption.
Qed.

#[global] Program Instance gen_conv_gen_spec_conv_inst : gen_spec_conv gen_conv.
Next Obligation.
  intros [a|a]; simpl; unfold proc_stable; cbn; eauto.
Qed.
Next Obligation. cbn. eauto with ccs. Qed.
Next Obligation. intros e l. cbn in l. inversion l; subst; simpl; eauto with ccs. Qed.

Fixpoint unroll_fw (xs : list name) : proc :=
  match xs with
  | [] => pr_nil
  | x :: xs' => pr_input x pr_success & unroll_fw xs'
  end.

Definition gen_acc (g : gset name) s := gen_test s (unroll_fw (elements g)).

Lemma unroll_a_eq_perm (xs ys : list name) : xs ≡ₚ ys -> unroll_fw xs ≡* unroll_fw ys.
Proof.
  intro hperm. dependent induction hperm; simpl; eauto with ccs.
  - eapply cgr_par_right; eauto with ccs.
  - transitivity ((pr_input y pr_success & pr_input x pr_success) & unroll_fw l).
    eauto with ccs.
    transitivity ((pr_input x pr_success & pr_input y pr_success) & unroll_fw l).
    eauto with ccs. eauto with ccs.
Qed.

#[global] Program Instance gen_acc_gen_test_inst g : gen_spec (fun s => gen_acc g s).
Next Obligation.
  intros g s hh. eapply gen_test_ungood_if; try eassumption.
  intro hh0. induction (elements g).
  - cbn in hh0. inversion hh0.
  - inversion hh0; subst. destruct H0.
    + inversion H.
    + contradiction.
Qed.
Next Obligation.
  intros. eapply gen_test_lts_mu.
Qed.
Next Obligation.
  intros. eapply gen_test_gen_spec_out_lts_tau_ex_inst.
Qed.
Next Obligation.
  intros. eapply gen_test_gen_spec_out_lts_tau_good. simpl in H. eassumption.
Qed.
Next Obligation.
  intros. eapply gen_test_gen_spec_out_lts_mu_uniq. eassumption.
Qed.

Lemma gen_acc_does_not_output : forall g t a, ~ lts (unroll_fw g) (ActExt $ ActOut a) t.
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros t a R. inversion R.
  - cbn. intros t a R. inversion R; subst.
    + inversion H3.
    + eapply IHg', H3.
Qed.

Lemma gen_acc_does_not_tau : forall g t, ~ lts (unroll_fw g) τ t.
Proof.
  intros g.
  induction g as [| b g'].
  - cbn. intros t R. inversion R.
  - cbn. intros t R.
    inversion R; subst.
    + inversion H1; subst. cbn in H2.
      eapply gen_acc_does_not_output. eassumption.
    + inversion H3.
    + eapply IHg'. eassumption.
Qed.

Lemma gen_acc_gen_spec_acc_nil_mem_lts_inp g a : a ∈ g -> exists r, lts (gen_acc g []) (ActExt $ ActIn a) r.
Proof.
  remember g. revert g0 Heqg0.
  induction g using set_ind_L; intros g0 Heqg0 mem.
  - subst. inversion mem.
  - assert (hn : {[x]} ## X) by set_solver.
    destruct (decide (x = a)).
    + subst.
      set (h := elements_disj_union {[a]} X hn).
      cbn. assert (exists t, lts (unroll_fw (a :: elements X)) (ActExt $ ActIn a) t).
      simpl. eauto with ccs.
      destruct H0 as (r & hl).
      edestruct
        (@eq_spec proc name CCS_Name_label CCS_lts CCS_EqLTS
           (unroll_fw (elements ({[a]} ∪ X))) r (ActExt $ ActIn a)) as (t & hlt & heqt).
      exists (unroll_fw (a :: elements X)).
      split. eapply unroll_a_eq_perm.
      replace (elements {[a]}) with [a] in h. eauto.
      now rewrite elements_singleton.
      simpl in *. eapply hl. eauto.
    + assert (mem' : a ∈ X) by set_solver.
      edestruct (IHg X eq_refl mem') as (r & hlr); eauto.
      edestruct
        (@eq_spec proc name CCS_Name_label CCS_lts CCS_EqLTS
           (unroll_fw (elements ({[x]} ∪ X)))
           (pr_par (pr_input x pr_success) r) (ActExt $ ActIn a)) as (t & hlt & heqt).
      exists (unroll_fw (x :: elements X)).
      split. eapply unroll_a_eq_perm.
      set (h := elements_disj_union {[x]} X hn).
      replace (elements {[x]}) with [x] in h. eauto.
      now rewrite elements_singleton.
      simpl in *. eauto with ccs. subst. eauto.
Qed.

#[global] Program Instance gen_acc_gen_spec_acc_inst : gen_spec_acc gen_acc.
Next Obligation.
  intros g. simpl. unfold proc_stable. cbn.
  remember (lts_set_tau (unroll_fw (elements g))) as ps.
  destruct ps using set_ind_L; eauto.
  assert (mem : x ∈ lts_set_tau (unroll_fw (elements g))) by set_solver.
  eapply lts_set_tau_spec0 in mem.
  now eapply gen_acc_does_not_tau in mem.
Qed.
Next Obligation.
  intros g a. simpl. unfold proc_stable. cbn.
  remember (lts_set_output (unroll_fw (elements g)) a) as ps.
  destruct ps using set_ind_L; eauto.
  assert (mem : x ∈ lts_set_output (unroll_fw (elements g)) a) by set_solver.
  eapply lts_set_output_spec0 in mem.
  now eapply gen_acc_does_not_output in mem.
Qed.
Next Obligation.
  intros g.
  induction g using set_ind_L; intros.
  - inversion H.
  - edestruct
      (@eq_spec proc name CCS_Name_label CCS_lts CCS_EqLTS
         (unroll_fw (x :: elements X)) e (ActExt (ActIn a))) as (t & hlt & heqt).
    ++ exists (gen_acc ({[x]} ∪ X) []).
       split.
       +++ eapply unroll_a_eq_perm.
           assert (hn : {[x]} ## X) by set_solver.
           set (h := elements_disj_union {[x]} X hn).
           replace (elements {[x]}) with [x] in h. symmetry. eauto.
           now rewrite elements_singleton.
       +++ eassumption.
    ++ cbn in hlt. inversion hlt; subst.
       +++ inversion H5; subst. set_solver.
       +++ set_solver.
Qed.
Next Obligation.
  intros. eapply gen_acc_gen_spec_acc_nil_mem_lts_inp; eauto.
Qed.
Next Obligation.
  intros a e' g. revert a e'.
  induction g using set_ind_L; intros a e' hl.
  - inversion hl.
  - edestruct
      (@eq_spec proc name CCS_Name_label CCS_lts CCS_EqLTS
         (unroll_fw (x :: elements X)) e' (ActExt a)) as (t & hlt & heqt).
    ++ exists (gen_acc ({[x]} ∪ X) []).
       split; eauto.
       eapply unroll_a_eq_perm.
       assert (hn : {[x]} ## X) by set_solver.
       set (h := elements_disj_union {[x]} X hn).
       replace (elements {[x]}) with [x] in h
           by now rewrite elements_singleton.
       symmetry. eauto.
    ++ simpl in hlt. inversion hlt; subst.
       +++ inversion H4; subst.
           eapply good_preserved_by_cgr; try eassumption. eauto with ccs.
       +++ eapply good_preserved_by_cgr; try eassumption. eauto with ccs.
Qed.

From Must Require Import Equivalence.

Corollary bhv_iff_ctx_ACCS (p q : proc) : p ⊑ q <-> p ▷ ∅ ≼ q ▷ ∅.
Proof.
  split.
  intros hm%pre_extensional_eq. now eapply equivalence_bhv_acc_ctx.
  intros hm. now eapply pre_extensional_eq, equivalence_bhv_acc_ctx.
Qed.
