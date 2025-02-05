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

Require ssreflect.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Wellfounded.Inverse_Image.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf Setoid.
Require Import Coq.Program.Equality.
From Coq.Logic Require Import ProofIrrelevance.

From stdpp Require Import base countable list decidable finite gmap.

Lemma sig_eq {A} (P : A → Prop) (x y : sig P) :
  proj1_sig x = proj1_sig y → x = y.
Proof.
  destruct x as [x Px]; simpl.
  destruct y as [y Py]; simpl.
  intros ->.
  rewrite (proof_irrelevance _ Px Py); trivial.
Qed.

Section in_list_finite.
  Context `{!EqDecision A}.
  Context {P : A → Prop} `{!∀ x : A, ProofIrrel (P x)} `{∀ x, Decision (P x)}.

  Program Fixpoint Forall_to_sig (l : list A) : Forall P l → list (sig P) :=
    match l as u return Forall P u → list (sig P) with
    | [] => λ _, []
    | a :: l' => λ Hal, (exist P a _) :: Forall_to_sig l' _
    end.
  Next Obligation. intros ??? Hal. inversion Hal. by simplify_eq. Qed.
  Next Obligation. intros ??? Hal. by inversion Hal; simplify_eq. Qed.

  Lemma elem_of_Forall_to_sig_1 l HPl x : x ∈ Forall_to_sig l HPl → `x ∈ l.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - apply elem_of_cons; apply elem_of_cons in Hx as [->|]; simpl in *; eauto.
  Qed.


  Lemma elem_of_Forall_to_sig_2 l HPl x :
    x ∈ l → ∃ Hx, x ↾ Hx ∈ Forall_to_sig l HPl.
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl; intros HPl Hx.
    - by apply elem_of_nil in Hx.
    - inversion HPl as [|? ? Ha HPl']; simplify_eq.
      apply elem_of_cons in Hx as [->|]; simpl in *.
      + exists Ha; apply elem_of_cons; left; apply sig_eq; done.
      + edestruct IHl as [Hx Hxl]; first done.
        exists Hx; apply elem_of_cons; eauto.
  Qed.

  Lemma Forall_to_sig_NoDup l HPl : NoDup l → NoDup (Forall_to_sig l HPl).
  Proof.
    revert HPl; induction l as [|a l IHl]; simpl;
      intros HPl; first by constructor.
    inversion 1; inversion HPl; simplify_eq.
    constructor; last by apply IHl.
    intros ?%elem_of_Forall_to_sig_1; done.
  Qed.

  Lemma in_list_finite (l : list A) : (∀ x, P x → x ∈ l) → Finite {x : A | P x}.
  Proof.
    intros Hl.
    assert (Forall P (filter P (remove_dups l))) as Hels.
    { apply Forall_forall. intros ?; rewrite elem_of_list_filter; tauto. }
    refine {| enum := Forall_to_sig (filter P (remove_dups l)) Hels |}.
    - apply Forall_to_sig_NoDup. apply NoDup_filter, NoDup_remove_dups.
    - intros x.
      edestruct (elem_of_Forall_to_sig_2 _ Hels) as [Hx' ?].
      { apply elem_of_list_filter; split; first apply (proj2_sig x).
        apply elem_of_remove_dups, Hl; apply (proj2_sig x). }
      replace x with (`x ↾ Hx'); last by apply sig_eq.
      done.
  Qed.
End in_list_finite.

From stdpp Require Import gmultiset. (* fixme *)

(** Multiset helpers. *)

Lemma gmultiset_eq_drop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m1 ⊎ m2 = m1 ⊎ m3 -> m2 = m3.
Proof. by multiset_solver. Qed.

Lemma gmultiset_eq_pop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m2 = m3 -> m1 ⊎ m2 = m1 ⊎ m3.
Proof. by multiset_solver. Qed.

Lemma gmultiset_neq_s `{Countable A} (m : gmultiset A) a : m ≠ {[+ a +]} ⊎ m.
Proof. by multiset_solver. Qed.

Lemma gmultiset_mono `{Countable A} (m : gmultiset A) a b : {[+ a +]} ⊎ m = {[+ b +]} ⊎ m -> a = b.
Proof. intros. eapply gmultiset_singleton_subseteq. multiset_solver. Qed.

Lemma gmultiset_elements_singleton_inv `{Countable A} (m : gmultiset A) a :
  elements m = [a] -> m = {[+ a +]}.
Proof.                          (* fixme: find a better way to do this *)
  intros eq.
  induction m using gmultiset_ind.
  + multiset_solver.
  + induction m using gmultiset_ind.
    ++ replace ({[+ x +]} ⊎ ∅) with ({[+ x +]} : gmultiset A) in *.
       assert (a = x); subst.
       eapply gmultiset_elem_of_singleton.
       eapply gmultiset_elem_of_elements. rewrite eq. set_solver.
       set_solver. multiset_solver.
    ++ exfalso.
       assert (length (elements ({[+ x +]} ⊎ ({[+ x0 +]} ⊎ m))) = length [a]) by now rewrite eq.
       rewrite 2 gmultiset_elements_disj_union in H0.
       rewrite 2 gmultiset_elements_singleton in H0.
       simpl in H0. lia.
Qed.

(** Actions  *)

Inductive ExtAct (A: Type) :=
| ActIn (a : A)
| ActOut (a : A)
.
Arguments ActIn {_} _.
Arguments ActOut {_} _.

Definition ext_act_match {A} (l1 l2: ExtAct A) :=
  match l1, l2 with
  | ActIn x, ActOut y => x = y
  | ActOut x, ActIn y => x = y
  | _, _ => False
  end.

Inductive Act (A: Type) :=
| ActExt (μ: ExtAct A)
| τ
.
Arguments ActExt {_} _.
Arguments τ {_}.

Definition act_match {A} (l1 l2: Act A) :=
  match l1, l2 with
  | ActExt x, ActExt y => ext_act_match x y
  | _, _ => False
  end.

Definition co {A} (l: ExtAct A) :=
  match l with
  | ActIn x => ActOut x
  | ActOut x => ActIn x
  end.

(* fixme: Involution does not hold anymore in the context of pi-calculus. *)

Lemma co_involution {A} (l: ExtAct A) : co (co l) = l.
Proof. destruct l; eauto. Qed.

Definition act_match_commutative {A} (l1 l2: Act A):
  act_match l1 l2 -> act_match l2 l1.
Proof. by destruct l1 as [[?|?]|], l2 as [[?|?]|]; eauto; intros ->. Qed.

#[global] Instance actext_eqdec `{EqDecision L} : EqDecision (ExtAct L).
Proof. solve_decision. Defined.
#[global] Instance act_eqdec `{EqDecision L} : EqDecision (Act L).
Proof. solve_decision. Defined.
#[global] Instance ext_act_match_dec `{EqDecision L} : ∀ (ℓ1 ℓ2: ExtAct L), Decision (ext_act_match ℓ1 ℓ2).
Proof.
  intros [l1|l1] [l2|l2]; [by right; intros ? | | | by right; intros ?];
    destruct (decide (l1 = l2)); eauto.
Defined.

#[global] Instance act_match_dec `{EqDecision L} : ∀ (ℓ1 ℓ2: Act L), Decision (act_match ℓ1 ℓ2).
Proof. intros [l1|] [l2|]; try by (right; eauto). simpl. apply _. Defined.

Definition trace L := list (ExtAct L).

Definition is_input {A} (μ : ExtAct A) := ∃ a, μ = ActIn a.

Definition are_inputs {A} (s : trace A) := Forall is_input s.

Definition is_output {A} (μ : ExtAct A) := ∃ a, μ = ActOut a.

Definition are_outputs {A} (s : trace A) := Forall is_output s.

Class Label (L: Type) :=
  MkLabel {
      label_eqdec: EqDecision L;
      label_countable: Countable L;
    }.
#[global] Existing Instance label_eqdec.
#[global] Existing Instance label_countable.

Class Lts (A L : Type) `{Label L} :=
  MkLts {
      lts_step: A → Act L → A → Prop;
      lts_state_eqdec: EqDecision A;

      lts_step_decidable a α b : Decision (lts_step a α b);

      lts_outputs : A -> gset L;
      lts_outputs_spec1 p1 x p2 : lts_step p1 (ActExt (ActOut x)) p2 -> x ∈ lts_outputs p1;
      lts_outputs_spec2 p1 x : x ∈ lts_outputs p1 -> {p2 | lts_step p1 (ActExt (ActOut x)) p2};

      lts_stable: A → Act L → Prop;
      lts_stable_decidable p α : Decision (lts_stable p α);
      lts_stable_spec1 p α : ¬ lts_stable p α → { q | lts_step p α q };
      lts_stable_spec2 p α : { q | lts_step p α q } → ¬ lts_stable p α;
    }.
#[global] Existing Instance lts_state_eqdec.
#[global] Existing Instance lts_step_decidable.
#[global] Existing Instance lts_stable_decidable.

Notation "p ⟶ q"      := (lts_step p τ q) (at level 30, format "p  ⟶  q").
Notation "p ⟶{ α } q" := (lts_step p α q) (at level 30, format "p  ⟶{ α }  q").
Notation "p ⟶[ μ ] q" := (lts_step p (ActExt μ) q) (at level 30, format "p  ⟶[ μ ]  q").

Notation "p ↛"      := (lts_stable p τ) (at level 30, format "p  ↛").
Notation "p ↛{ α }" := (lts_stable p α) (at level 30, format "p  ↛{ α }").
Notation "p ↛[ μ ]" := (lts_stable p (ActExt μ)) (at level 30, format "p  ↛[ μ ]").

Class FiniteLts A L `{Lts A L} :=
  MkFlts {
      folts_states_countable: Countable A;
      folts_next_states_finite p α : Finite (dsig (fun q => lts_step p α q));
}.

#[global] Existing Instance folts_states_countable.
#[global] Existing Instance folts_next_states_finite.

Class LtsEq (A L : Type) `{Lts A L} := {
    (* todo: use Equivalence *)
    eq_rel : A -> A -> Prop;
    eq_rel_refl p : eq_rel p p;
    eq_symm p q : eq_rel p q -> eq_rel q p;
    eq_trans p q r : eq_rel p q -> eq_rel q r -> eq_rel p r;
    (* reference: L 1.4.15 p.51 Sangiorgi pi-book *)
    eq_spec p q (α : Act L) : (exists r, eq_rel p r /\ r ⟶{α} q) -> (exists r, p ⟶{α} r /\ eq_rel r q);
  }.

Add Parametric Relation `{Lts A L, ! LtsEq A L} : A eq_rel
    reflexivity proved by (eq_rel_refl)
    symmetry proved by (eq_symm)
    transitivity proved by (eq_trans)
    as sc_proc_rel.

Infix "⋍" := eq_rel (at level 70).

Definition lts_sc `{Lts A L, !LtsEq A L} p α q := exists r, p ⟶{α} r /\ r ⋍ q.

Notation "p ⟶⋍ q" := (lts_sc p τ q) (at level 30, format "p  ⟶⋍  q").
Notation "p ⟶⋍{ α } q" := (lts_sc p α q) (at level 30, format "p  ⟶⋍{ α }  q").
Notation "p ⟶⋍[ μ ] q" := (lts_sc p (ActExt μ) q) (at level 30, format "p  ⟶⋍[ μ ]  q").

Class LtsOba (A L : Type) `{Lts A L, !LtsEq A L} :=
  MkOBA {
      (* Multiset of outputs *)
      lts_oba_mo p : gmultiset L;
      lts_oba_mo_spec1 p a : a ∈ lts_oba_mo p <-> a ∈ lts_outputs p;
      lts_oba_mo_spec2 p a : forall q, p ⟶[ActOut a] q -> lts_oba_mo p = {[+ a +]} ⊎ lts_oba_mo q;
      (* Selinger axioms. *)
      lts_oba_output_commutativity {p q r a α} :
      p ⟶[ActOut a] q -> q ⟶{α} r -> (∃ t, p ⟶{α} t /\ t ⟶⋍[ActOut a] r) ;
      lts_oba_output_confluence {p q1 q2 a μ} :
      μ ≠ ActOut a -> p ⟶[ActOut a] q1 -> p ⟶[μ] q2 ->
      ∃ r, q1 ⟶[μ] r /\ q2 ⟶⋍[ActOut a] r ;
      lts_oba_output_tau {p q1 q2 a} :
      p ⟶[ActOut a] q1 -> p ⟶ q2 -> (∃ t, q1 ⟶ t /\ q2 ⟶⋍[ActOut a] t) \/ q1 ⟶⋍[ActIn a] q2 ;
      lts_oba_output_deter {p1 p2 p3 a} :
      p1 ⟶[ActOut a] p2 -> p1 ⟶[ActOut a] p3 -> p2 ⋍ p3 ;
      (* Extra axiom, it would be nice to remove it, not used that much. *)
      lts_oba_output_deter_inv {p1 p2 q1 q2} a :
      p1 ⟶[ActOut a] q1 -> p2 ⟶[ActOut a] q2 -> q1 ⋍ q2 -> p1 ⋍ p2
    }.

Class LtsObaFB (A L: Type) `{LtsOba A L} :=
  MkLtsObaFB {
      lts_oba_fb_feedback {p1 p2 p3 a} : p1 ⟶[ActOut a] p2 -> p2 ⟶[ActIn a] p3 -> p1 ⟶⋍ p3
    }.

Class LtsObaFW (A L : Type) `{LtsOba A L} :=
  MkLtsObaFW {
      lts_oba_fw_forward p1 a : ∃ p2, p1 ⟶[ActIn a] p2 /\ p2 ⟶[ActOut a] p1 ;
      lts_oba_fw_feedback {p1 p2 p3 a} : p1 ⟶[ActOut a] p2 -> p2 ⟶[ActIn a] p3 -> p1 ⟶⋍ p3 \/ p1 ⋍ p3 ;
    }.

(* Inductive definition of terminate. *)

Reserved Notation "p ⤓" (at level 60).

Inductive terminate `{Lts A L} (p : A) : Prop :=
| tstep : (forall q, p ⟶ q -> terminate q) -> terminate p

where "p ⤓" := (terminate p).

Global Hint Constructors terminate:mdb.

Lemma terminate_if_stable `{Lts A L} p : p ↛ -> p ⤓.
Proof. intro st. constructor. intros q l. exfalso. eapply lts_stable_spec2; eauto. Qed.

Lemma terminate_preserved_by_lts_tau `{Lts A L} p q : p ⤓ -> p ⟶ q -> q ⤓.
Proof. by inversion 1; eauto. Qed.

Lemma terminate_preserved_by_eq `{LtsEq A L} {p q} : p ⤓ -> p ⋍ q -> q ⤓.
Proof.
  intros ht. revert q.
  induction ht. intros.
  eapply tstep.
  intros q' l.
  edestruct eq_spec as (r & h2 & h3). eauto.
  eapply H3; eauto.
Qed.

Lemma terminate_preserved_by_eq2 `{LtsEq A L} {p q} : p ⋍ q -> p ⤓ -> q ⤓.
Proof. intros. eapply terminate_preserved_by_eq; eauto. Qed.

Lemma terminate_preserved_by_lts_output `{LtsOba A L} {p q a} : p ⟶[ActOut a] q -> p ⤓ -> q ⤓.
Proof.
  intros l ht. revert q a l.
  dependent induction ht; intros q a l1.
  eapply tstep. intros q' l2.
  destruct (lts_oba_output_commutativity l1 l2) as (t & l3 & l4); eauto.
  destruct l4 as (q0 & l0 & eq0).
  eapply terminate_preserved_by_eq.
  eapply H3. eapply l3. eapply l0. eassumption.
Qed.

Lemma stable_tau_preserved_by_lts_output `{LtsOba A L} p q a : p ↛ -> p ⟶[ActOut a] q -> q ↛.
Proof.
  intros st l.
  case (lts_stable_decidable q τ); eauto.
  intro nst. eapply lts_stable_spec1 in nst as (t & l').
  destruct (lts_oba_output_commutativity l l') as (r & l1 & l2).
  edestruct (lts_stable_spec2 p τ); eauto with mdb.
Qed.

Lemma lts_input_preserved_by_lts_output `{LtsOba A L} p q a b :
  (exists t, p ⟶[ActIn b] t) -> p ⟶[ActOut a] q -> (exists t, q ⟶[ActIn b] t).
Proof.
  intros (t & hl1) hl2.
  assert (neq : ActIn b ≠ ActOut a) by (now inversion 1).
  edestruct (lts_oba_output_confluence neq hl2 hl1) as (r & l1 & l2). eauto.
Qed.

Lemma stable_input_preserved_by_lts_output `{LtsOba A L} p q a b :
  p ↛[ActIn b] -> p ⟶[ActOut a] q -> q ↛[ActIn b] .
Proof.
  intros st l.
  case (lts_stable_decidable q (ActExt $ ActIn b)); eauto.
  intro nst. eapply lts_stable_spec1 in nst as (t & l').
  destruct (lts_oba_output_commutativity l l') as (r & l1 & l2).
  edestruct (lts_stable_spec2 p (ActExt $ ActIn b)); eauto with mdb.
Qed.

(* Weak transitions *)

Inductive wt `{Lts A L} : A -> trace L -> A -> Prop :=
| wt_nil p : wt p [] p
| wt_tau s p q t (l : p ⟶ q) (w : wt q s t) : wt p s t
| wt_act μ s p q t (l : p ⟶[μ] q) (w : wt q s t) : wt p (μ :: s) t
.

Global Hint Constructors wt:mdb.

Notation "p ⟹ q" := (wt p [] q) (at level 30).
Notation "p ⟹{ μ } q" := (wt p [μ] q) (at level 30, format "p  ⟹{ μ }  q").
Notation "p ⟹[ s ] q" := (wt p s q) (at level 30, format "p  ⟹[ s ]  q").

Definition wt_sc `{Lts A L, !LtsEq A L} p s q := ∃ r, p ⟹[s] r /\ r ⋍ q.

Notation "p ⟹⋍ q" := (wt_sc p [] q) (at level 30, format "p  ⟹⋍  q").
Notation "p ⟹⋍{ μ } q" := (wt_sc p [μ] q) (at level 30, format "p  ⟹⋍{ μ }  q").
Notation "p ⟹⋍[ s ] q" := (wt_sc p s q) (at level 30, format "p  ⟹⋍[ s ]  q").

Lemma wt_pop `{Lts A L} p q μ s : p ⟹[μ :: s] q -> ∃ t, p ⟹{μ} t /\ t ⟹[s] q.
Proof.
  intro w.
  dependent induction w; eauto with mdb.
  destruct (IHw μ s JMeq_refl) as (r & w1 & w2).
  exists r. eauto with mdb.
Qed.

Lemma wt_concat `{Lts A L} p q r s1 s2 :
  p ⟹[s1] q -> q ⟹[s2] r -> p ⟹[s1 ++ s2] r.
Proof. intros w1 w2. dependent induction w1; simpl; eauto with mdb. Qed.

Lemma wt_push_left `{Lts A L} {p q r μ s} :
  p ⟹{μ} q -> q ⟹[s] r -> p ⟹[μ :: s] r.
Proof.
  intros w1 w2.
  replace (μ :: s) with ([μ] ++ s) by eauto.
  eapply wt_concat; eauto.
Qed.

Lemma wt_split `{Lts A L} p q s1 s2 :
  p ⟹[s1 ++ s2] q -> ∃ r, p ⟹[s1] r /\ r ⟹[s2] q.
Proof.
  revert p q.
  dependent induction s1; intros p q w.
  - eauto with mdb.
  - simpl in w. eapply wt_pop in w as (r & w1 & w2).
    eapply IHs1 in w2 as (r' & w2 & w3).
    exists r'. split. eapply wt_push_left; eauto. assumption.
Qed.

Lemma wt_push_nil_left `{Lts A L} {p q r s} : p ⟹ q -> q ⟹[s] r -> p ⟹[s] r.
Proof. by intros w1 w2; dependent induction w1; eauto with mdb. Qed.

Lemma wt_push_nil_right `{Lts A L} p q r s : p ⟹[s] q -> q ⟹ r -> p ⟹[s] r.
Proof.
  intros w1 w2. replace s with (s ++ ([] : trace L)).
  eapply wt_concat; eauto. symmetry. eapply app_nil_end.
Qed.

Lemma wt_push_right `{Lts A L} p q r μ s :
  p ⟹[s] q -> q ⟹{μ} r -> p ⟹[s ++ [μ]] r.
Proof. intros w1 w2. eapply wt_concat; eauto. Qed.

Lemma wt_decomp_one `{Lts A L} {μ p q} : p ⟹{μ} q -> ∃ r1 r2, p ⟹ r1 ∧ r1 ⟶[μ] r2 ∧ r2 ⟹ q.
Proof.
  intro w.
  dependent induction w; eauto with mdb.
  destruct (IHw μ JMeq_refl) as (r1 & r2 & w1 & l' & w2).
  exists r1, r2. eauto with mdb.
Qed.

Lemma stable_tau_preserved_by_wt_output `{LtsOba A L} p q s :
  are_outputs s -> p ↛ -> p ⟹[s] q -> q ↛.
Proof.
  intros s_spec hst hw.
  induction hw; eauto.
  - eapply lts_stable_spec2 in hst. now exfalso. eauto.
  - destruct μ as [a|a]. inversion s_spec; subst.
    + inversion H4. inversion H2.
    + inversion s_spec; subst.
      eapply IHhw. eassumption. eapply stable_tau_preserved_by_lts_output; eauto.
Qed.

Lemma stable_tau_input_preserved_by_wt_output `{LtsOba A L} p q s a :
  are_outputs s -> p ↛ -> p ↛[ActIn a] -> p ⟹[s] q -> q ↛[ActIn a].
Proof.
  intros s_spec hst_tau hst_inp hw.
  induction hw; eauto.
  - eapply lts_stable_spec2 in hst_tau. now exfalso. eauto.
  - destruct μ as [b|b]. inversion s_spec; subst.
    + inversion H4. inversion H2.
    + inversion s_spec; subst.
      eapply IHhw. eassumption.
      eapply stable_tau_preserved_by_lts_output; eauto.
      eapply stable_input_preserved_by_lts_output; eauto.
Qed.

Lemma lts_input_preserved_by_wt_output `{LtsOba A L} p q s a :
  are_outputs s -> p ↛ -> (exists t, p ⟶[ActIn a] t) -> p ⟹[s] q -> (exists t, q ⟶[ActIn a] t).
Proof.
  intros s_spec hst_tau hst_inp hw.
  induction hw; eauto.
  - eapply lts_stable_spec2 in hst_tau. now exfalso. eauto.
  - destruct μ as [b|b]. inversion s_spec; subst.
    + inversion H4. inversion H2.
    + inversion s_spec; subst.
      eapply IHhw. eassumption.
      eapply stable_tau_preserved_by_lts_output; eauto.
      eapply lts_input_preserved_by_lts_output; eauto.
Qed.


(* Convergence *)

Reserved Notation "p ⇓ s" (at level 70).

Inductive cnv `{Lts A L} : A -> trace L -> Prop :=
| cnv_nil p : p ⤓ -> p ⇓ []
| cnv_act p μ s : p ⤓ -> (forall q, p ⟹{μ} q -> q ⇓ s) -> p ⇓ μ :: s

where "p ⇓ s" := (cnv p s).

Global Hint Constructors cnv:mdb.

Lemma cnv_terminate `{M : Lts A L} p s : p ⇓ s -> p ⤓.
Proof. by intros hcnv; now inversion hcnv. Qed.

Lemma cnv_preserved_by_lts_tau `{M : Lts A L} s p : p ⇓ s -> forall q, p ⟶ q -> q ⇓ s.
Proof.
  intros hcnv q l.
  inversion hcnv; subst.
  - eapply cnv_nil. inversion H0; eauto.
  - eapply cnv_act.
    + inversion H0; eauto.
    + eauto with mdb.
Qed.

Lemma cnv_preserved_by_wt_nil `{M : Lts A L} s p :
  p ⇓ s -> forall q, p ⟹ q -> q ⇓ s.
Proof.
  intros hcnv q w.
  dependent induction w; eauto with mdb.
  eapply IHw. eapply cnv_preserved_by_lts_tau; eauto. reflexivity.
Qed.

Lemma cnv_preserved_by_wt_act `{M: Lts A L} s p μ :
  p ⇓ μ :: s -> forall q, p ⟹{μ} q -> q ⇓ s.
Proof. by intros hcnv; inversion hcnv; eauto with mdb. Qed.

Lemma cnv_iff_prefix_terminate_l `{M: Lts A L} p s :
  p ⇓ s -> (forall t q, t `prefix_of` s -> p ⟹[t] q -> q ⤓).
Proof.
  intros hcnv t q hpre w.
  revert s p q hcnv hpre w.
  dependent induction t; intros.
  - eapply cnv_terminate, cnv_preserved_by_wt_nil; eassumption.
  - eapply wt_pop in w as (p' & w0 & w1).
    inversion hpre; subst. simpl in hcnv.
    eapply (IHt (t ++ x) p' q).
    eapply cnv_preserved_by_wt_act; eauto.
    now eapply prefix_cons_inv_2 in hpre.
    eassumption.
Qed.

Lemma cnv_iff_prefix_terminate_r `{M: Lts A L} p s :
  (forall t q, t `prefix_of` s -> p ⟹[t] q -> q ⤓) -> p ⇓ s.
Proof.
  intros h.
  revert p h.
  dependent induction s; intros; eauto with mdb.
  eapply cnv_act; eauto with mdb.
  eapply (h []) ; eauto with mdb; eapply prefix_nil.
  intros q w. eapply IHs.
  intros t r hpre w1.
  eapply (h (a :: t)); eauto with mdb. eapply prefix_cons. eassumption.
  eapply wt_push_left; eassumption.
Qed.

Corollary cnv_iff_prefix_terminate `{M: Lts A L} p s :
  p ⇓ s <-> (forall s0 q, s0 `prefix_of` s -> p ⟹[s0] q -> q ⤓).
Proof.
  split; [eapply cnv_iff_prefix_terminate_l|eapply cnv_iff_prefix_terminate_r].
Qed.

Lemma cnv_wt_prefix `{M: Lts A L} s1 s2 p :
  p ⇓ s1 ++ s2 -> forall q, p ⟹[s1] q -> q ⇓ s2.
Proof.
  revert s2 p.
  dependent induction s1; intros s2 p hcnv q w.
  - eapply cnv_preserved_by_wt_nil; eauto with mdb.
  - eapply wt_pop in w as (p' & w0 & w1).
    inversion hcnv; eauto with mdb.
Qed.

Lemma terminate_preserved_by_wt_nil `{M: Lts A L} p : p ⤓ -> forall q, p ⟹ q -> q ⤓.
Proof.
  intros hcnv q w.
  dependent induction w; eauto with mdb.
  eapply IHw. eapply terminate_preserved_by_lts_tau; eauto. reflexivity.
Qed.

Lemma terminate_preserved_by_wt_output `{M: LtsOba A L} p q a : p ⤓ -> p ⟹{ActOut a} q -> q ⤓.
Proof.
  intros ht w.
  dependent induction w.
  - eapply IHw; eauto. eapply terminate_preserved_by_lts_tau; eauto.
  - eapply terminate_preserved_by_wt_nil.
    eapply terminate_preserved_by_lts_output; eauto. assumption.
Qed.


Definition lts_tau_set `{FiniteLts A L} p : list A :=
  map proj1_sig (enum $ dsig (lts_step p τ)).

Lemma lts_tau_set_spec : forall `{FiniteLts A L} p q, q ∈ lts_tau_set p <-> p ⟶ q.
Proof.
  intros. split.
  intro mem. unfold lts_tau_set in mem.
  eapply elem_of_list_fmap in mem as ((r & l) & eq & mem). subst.
  eapply bool_decide_unpack. eassumption.
  intro. eapply elem_of_list_fmap.
  exists (dexist q H2). split.
  eauto. eapply elem_of_enum.
Qed.

Lemma lts_ht_input_ex `{LtsObaFW A L} (p : A) :
  forall a, exists p', lts_step p (ActExt (ActIn a)) p'.
Proof. intro a. destruct (lts_oba_fw_forward p a) as (t & l1 & l2). eauto. Qed.

Inductive parallel_step `{M1: Lts A L, M2: Lts B L}: A * B → Act L → A * B → Prop :=
| ParLeft α a1 a2 b (l : a1 ⟶{α} a2) : parallel_step (a1, b) α (a2, b)
| ParRight α a b1 b2 (l : b1 ⟶{α} b2) : parallel_step (a, b1) α (a, b2)
| ParSync α1 α2 a1 a2 b1 b2 (eq : act_match α1 α2) (l1 : a1 ⟶{α1} a2) (l2 : b1 ⟶{α2} b2) : parallel_step (a1, b1) τ (a2, b2)
.

Global Hint Constructors parallel_step:mdb.

Lemma eq_spec_wt `{LtsEq A L} p p' : p ⋍ p' -> forall q s, p ⟹[s] q -> p' ⟹⋍[s] q.
Proof.
  intros heq q s w.
  revert p' heq.
  dependent induction w; intros.
  + exists p'; split. eauto with mdb. now symmetry.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
  + edestruct eq_spec as (t' & hlt' & heqt').
    exists p. split; [symmetry|]; eassumption.
    destruct (IHw t' (symmetry heqt')) as (u & hlu' & hequ').
    exists u. eauto with mdb.
Qed.

(* fixme: ugly - remove in the caller ? *)
Lemma mk_lts_eq `{LtsEq A L} {p α q} : lts_step p α q -> lts_sc p α q.
Proof. intro. exists q; split. eauto with mdb. reflexivity. Qed.

Lemma delay_wt_output_nil `{LtsObaFW A L} {p q r a} :
  p ⟶⋍[ActOut a] q ->
  q ⟹ r ->
  exists t, p ⟹ t /\ t ⟶⋍[ActOut a] r.
Proof.
  intros l w.
  revert p a l.
  dependent induction w; intros p0 a (p' & hl & heq); eauto with mdb.
  - exists p0. split; eauto with mdb. exists p'. split; eauto with mdb.
  - destruct (eq_spec p' q τ) as (r & hlr & heqr); eauto with mdb.
    destruct (lts_oba_output_commutativity hl hlr) as (r' & l1 & (t' & l2 & heqt')).
    edestruct (IHw JMeq_refl r' a) as (r0 & w0 & (r1 & l1' & heq1)).
    exists t'. split. eassumption. etrans; eassumption.
    exists r0. split. eapply wt_tau; eassumption. exists r1. eauto with mdb.
Qed.

Lemma delay_wt_output `{LtsObaFW A L} {p q r a s} :
  p ⟶⋍[ActOut a] q -> q ⟹[s] r ->
  exists t, p ⟹[s] t /\ t ⟶⋍[ActOut a] r.
Proof.
  revert p q r a.
  induction s as [|μ s']; intros p q r a l w.
  - eapply delay_wt_output_nil; eauto.
  - eapply wt_pop in w as (q' & w0 & w1).
    destruct (wt_decomp_one w0) as (q0 & q1 & w2 & l' & w3).
    destruct (delay_wt_output_nil l w2) as (t & w4 & (q0' & l1' & heq')).
    destruct (eq_spec q0' q1 (ActExt μ)) as (r' & hr' & heqr'). eauto with mdb.
    destruct (lts_oba_output_commutativity l1' hr') as (u & l2 & l3).
    edestruct (eq_spec_wt q1 r' (symmetry heqr') r) as (t1 & w5 & l4); eauto with mdb.
    eapply wt_push_nil_left; eassumption.
    edestruct (IHs' u r') as (t2 & w6 & l5); eauto with mdb.
    exists t2. split.
    eapply wt_push_left; [eapply wt_push_nil_left|]; eauto with mdb.
    destruct l5 as (t1' & hlt1' & heqt1'). exists t1'. split; eauto with mdb.
    etrans; eassumption.
Qed.

Lemma cnv_preserved_by_eq `{LtsEq A L} p q s : p ⋍ q -> p ⇓ s -> q ⇓ s.
Proof.
  intros heq hcnv. revert q heq.
  induction hcnv; intros.
  - eapply cnv_nil.
    eapply (terminate_preserved_by_eq H2 heq).
  - eapply cnv_act.
    + eapply (terminate_preserved_by_eq H2 heq).
    + intros t w.
      destruct (eq_spec_wt q p (symmetry heq) t [μ] w) as (t' & hlt' & heqt').
      eapply (H4 t' hlt' t heqt').
Qed.

Lemma cnv_preserved_by_lts_output `{LtsObaFW A L} p q a s :
  p ⇓ s -> p ⟶[ActOut a] q -> q ⇓ s.
Proof.
  revert p q a.
  induction s as [|μ s']; intros p q a hacnv l.
  - eapply cnv_nil. inversion hacnv. subst.
    eapply terminate_preserved_by_lts_output; eassumption.
  - inversion hacnv. subst.
    eapply cnv_act.
    + eapply terminate_preserved_by_lts_output; eassumption.
    + intros r w.
      destruct (delay_wt_output (mk_lts_eq l) w) as (t & w0 & l1).
      destruct l1 as (r' & l2 & heq).
      eapply cnv_preserved_by_eq. eassumption.
      eapply IHs'. eapply H7, w0.
      eassumption.
Qed.

Lemma cnv_preserved_by_wt_output `{LtsObaFW A L} p q a s :
  p ⇓ s -> p ⟹{ActOut a} q -> q ⇓ s.
Proof.
  intros hcnv w.
  destruct (wt_decomp_one w) as (r1 & r2 & w1 & l0 & w2).
  eapply (cnv_preserved_by_wt_nil _ r2); eauto.
  eapply (cnv_preserved_by_lts_output r1); eauto.
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.

Lemma cnv_drop_input_hd `{LtsObaFW A L} p a s :
  p ⇓ ActIn a :: s -> p ⇓ s.
Proof.
  intro hacnv.
  inversion hacnv. subst.
  destruct (lts_oba_fw_forward p a) as (r & l1 & l2).
  eapply cnv_preserved_by_lts_output.
  eapply H7. eapply wt_act. eassumption. eapply wt_nil. eapply l2.
Qed.

(* fixme: it should be enought to have ltsOBA + one of the feedback *)
Lemma cnv_retract_lts_output `{LtsObaFW A L} p q a s :
  p ⇓ s -> p ⟶[ActOut a] q -> q ⇓ ActIn a :: s.
Proof.
  intros hcnv l.
  eapply cnv_act.
  - inversion hcnv; eapply terminate_preserved_by_lts_output; eassumption.
  - intros q' w.
    destruct (wt_decomp_one w) as (r1 & r2 & w1 & l0 & w2).
    destruct (delay_wt_output (mk_lts_eq l) w1) as (t & w0 & l1).
    destruct l1 as (r' & l1 & heq).
    edestruct (eq_spec r' r2) as (r & hlr & heqr). exists r1. eauto.
    eapply (cnv_preserved_by_wt_nil _ r2); eauto.
    eapply cnv_preserved_by_eq. eassumption.
    destruct (lts_oba_fw_feedback l1 hlr) as [(t0 & hlt0 & heqt0)|].
    eapply cnv_preserved_by_eq. eassumption.
    eapply cnv_preserved_by_lts_tau.
    eapply (cnv_preserved_by_wt_nil _ p); eauto. eassumption.
    eapply cnv_preserved_by_eq. eassumption.
    eapply (cnv_preserved_by_wt_nil _ p); eauto.
Qed.

Lemma cnv_retract_wt_output `{LtsObaFW A L} p q a s :
  p ⇓ s -> p ⟹{ActOut a} q -> q ⇓ ActIn a :: s.
Proof.
  intros hcnv w.
  eapply wt_decomp_one in w as (t1 & t2 & w1 & l & w2).
  eapply cnv_preserved_by_wt_nil; eauto.
  eapply (cnv_retract_lts_output t1); eauto.
  eapply cnv_preserved_by_wt_nil; eauto.
Qed.

(* fixme: naming clash join/concat/push etc *)
Lemma wt_join_nil `{Lts A L} {p q r} : p ⟹ q -> q ⟹ r -> p ⟹ r.
Proof. intros w1 w2. dependent induction w1; eauto with mdb. Qed.

Lemma wt_join_nil_eq `{LtsEq A L} {p q r} : p ⟹⋍ q -> q ⟹⋍ r -> p ⟹⋍ r.
Proof.
  intros (q' & hwq' & heqq') (r' & hwr' & heqr').
  destruct (eq_spec_wt _ _ (symmetry heqq') r' [] hwr') as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (wt_push_nil_left hwq' hwr1). etrans; eassumption.
Qed.

Lemma wt_join_nil_eq_l `{LtsEq A L} {p q r s} : p ⟹⋍ q -> q ⟹[s] r -> p ⟹⋍[s] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_wt _ _ (symmetry heqq') r s w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply (wt_push_nil_left hwq' hwr1). eassumption.
Qed.

Lemma wt_join_nil_eq_r `{LtsEq A L} {p q r s} : p ⟹[s] q -> q ⟹⋍ r -> p ⟹⋍[s] r.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply wt_push_nil_right; eauto. eassumption.
Qed.

Lemma wt_join_eq `{LtsEq A L} {p q r s1 s2} : p ⟹⋍[s1] q -> q ⟹⋍[s2] r -> p ⟹⋍[s1 ++ s2] r.
  revert p q r s2.
  induction s1; intros p q r s2 (q' & hwq' & heqq') w2; simpl in *.
  - destruct w2 as  (r' & hwr' & heqr').
    destruct (eq_spec_wt _ _ (symmetry heqq') r' s2 hwr') as (r1 & hwr1 & heqr1).
    exists r1. split. eapply (wt_push_nil_left hwq' hwr1). etrans; eassumption.
  - eapply wt_pop in hwq' as (p0 & w0 & w1).
    edestruct IHs1 as (t' & hwt' & heqt').
    exists q'. split; eassumption. eassumption.
    exists t'. split. eapply (wt_push_left w0 hwt'). eassumption.
Qed.

Lemma wt_join_eq_l `{LtsEq A L} {p q r s1 s2} : p ⟹⋍[s1] q -> q ⟹[s2] r -> p ⟹⋍[s1 ++ s2] r.
Proof.
  intros (q' & hwq' & heqq') w2.
  destruct (eq_spec_wt _ _ (symmetry heqq') r s2 w2) as (r1 & hwr1 & heqr1).
  exists r1. split. eapply wt_concat; eassumption. eassumption.
Qed.

Lemma wt_join_eq_r `{LtsEq A L} {p q r s1 s2} : p ⟹[s1] q -> q ⟹⋍[s2] r -> p ⟹⋍[s1 ++ s2] r.
Proof.
  intros w1 (r' & hwr' & heqr').
  exists r'. split. eapply wt_concat; eassumption. eassumption.
Qed.

Lemma wt_annhil `{LtsObaFW A L} p q a : p ⟹[[ActOut a ; ActIn a]] q -> p ⟹⋍ q.
Proof.
  intros w.
  destruct (wt_pop p q (ActOut a) [ActIn a] w) as (u & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  eapply (wt_join_nil_eq_r w3).
  destruct (delay_wt_output_nil (mk_lts_eq l1) (wt_join_nil w4 w5)) as (v & w0 & (v' & hlv' & heqv')).
  eapply (wt_join_nil_eq_r w0).
  destruct (eq_spec v' r2 (ActExt $ ActIn a)) as (r2' & hlr2' & heqr2'); eauto with mdb.
  edestruct (lts_oba_fw_feedback hlv' hlr2') as [(t & hlt & heqt)|].
  - eapply wt_join_nil_eq.
    exists t. split. eapply wt_tau; eauto with mdb. eassumption.
    eapply wt_join_nil_eq_r. eapply wt_nil.
    eapply eq_spec_wt. etrans. eapply (symmetry heqr2'). now symmetry. eassumption.
  - eapply eq_spec_wt. etrans. eapply (symmetry heqr2'). symmetry. now rewrite H3.
    eassumption.
Qed.

Lemma lts_to_wt `{Lts A L} {p q μ} : p ⟶[μ] q -> p ⟹{μ} q.
Proof. eauto with mdb. Qed.

Lemma are_inputs_preserved_by_perm {L} (s1 s2 : trace L) :
  s1 ≡ₚ s2 -> are_inputs s1 -> are_inputs s2.
Proof. intros hp his. eapply Permutation_Forall; eauto. Qed.

Lemma are_outputs_preserved_by_perm {L} (s1 s2 : trace L) :
  s1 ≡ₚ s2 -> are_outputs s1 -> are_outputs s2.
Proof. intros hp hos. eapply Permutation_Forall; eauto. Qed.

Lemma wt_output_swap `{LtsObaFW A L} p q a b : p ⟹[[ActOut a ; ActOut b]] q -> p ⟹⋍[[ActOut b; ActOut a]] q.
Proof.
  intro w.
  destruct (wt_pop p q (ActOut a) [ActOut b] w) as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  assert (h : t2 ⟹ r1) by (eapply wt_push_nil_left; eassumption).
  destruct (delay_wt_output (mk_lts_eq l1) h) as (r & w7 & (r1' & hlr1' & heqr1')).
  destruct (eq_spec r1' r2 (ActExt $ ActOut b)) as (t' & hlt' & heqt'). eauto with mdb.
  destruct (lts_oba_output_commutativity hlr1' hlt') as (u & hlu & (t0 & hlt0 & heqt0)); eauto.
  eapply wt_join_nil_eq_r.
  eapply (wt_push_nil_left w3).
  eapply (wt_push_nil_left w7).
  eapply (wt_act _ _ _ _ _ hlu), (wt_act _ _ _ _ _ hlt0), wt_nil.
  eapply eq_spec_wt. symmetry. etrans. eapply heqt0. eapply heqt'. eapply w6.
Qed.

Lemma wt_input_swap `{LtsObaFW A L} p q a b : p ⟹[[ActIn a ; ActIn b]] q -> p ⟹⋍[[ActIn b; ActIn a]] q.
Proof.
  intro w.
  destruct (wt_pop p q (ActIn a) [ActIn b] w) as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l1 & w4).
  eapply wt_decomp_one in w2 as (r1 & r2 & w5 & l2 & w6).
  destruct (lts_oba_fw_forward t1 b) as (t1' & l3 & l4).
  replace [ActIn b; ActIn a] with ([ActIn b] ++ [ActIn a]) by eauto.
  destruct (delay_wt_output (mk_lts_eq l4) (lts_to_wt l1)) as (r & l5 & l6).
  eapply wt_join_nil_eq_r.
  eapply (wt_push_nil_left w3).
  eapply (wt_act _ _ _ _ _ l3).
  eapply wt_decomp_one in l5 as (u1 & u2 & w7 & l7 & w8).
  eapply (wt_push_nil_left w7).
  eapply (wt_act _ _ _ _ _ l7 w8).
  assert (h : t2 ⟹ r1) by (eapply wt_push_nil_left; eassumption).
  destruct (delay_wt_output l6 h) as (v & wv & (v' & lv & heqv)).
  destruct (eq_spec v' r2 (ActExt $ ActIn b)) as (t' & hlt' & heqt'); eauto with mdb.
  eapply (wt_join_nil_eq_r wv).
  destruct (lts_oba_fw_feedback lv hlt') as [(t3 & hlt3 & heqt3)|]; subst; eauto with mdb.
  - eapply wt_join_nil_eq.
    exists t3. split; eauto with mdb.
    edestruct (eq_spec_wt r2 t') as (q' & hwq' & heqq').
    etrans. symmetry. eapply heqt'. now symmetry. eapply w6. exists q'. split; eauto with mdb.
  - edestruct (eq_spec_wt r2 v) as (q' & hwq' & heqq').
    etrans. symmetry. eassumption. now symmetry. eassumption.
    exists q'. split; eauto with mdb.
Qed.

Lemma cnv_input_swap `{LtsObaFW A L} p a b s :
  p ⇓ ActIn a :: ActIn b :: s -> p ⇓ ActIn b :: ActIn a :: s.
Proof.
  intros hcnv.
  destruct (lts_oba_fw_forward p a) as (t0 & l1 & l2).
  destruct (lts_oba_fw_forward t0 b) as (t1 & l3 & l4).
  inversion hcnv; subst.
  eapply cnv_act; eauto.
  intros q w1. eapply cnv_act.
  - destruct (delay_wt_output (mk_lts_eq l2) w1) as (t' & w2 & (t2 & hlt2 & heqt2)).
    eapply (terminate_preserved_by_eq2 heqt2).
    eapply (terminate_preserved_by_lts_output hlt2).
    eapply (cnv_terminate t' s).
    eapply cnv_preserved_by_wt_act; eauto with mdb.
  - intros r w2.
    edestruct (wt_input_swap) as (t & w' & heq').
    eapply wt_push_left. eapply w1. eapply w2.
    eapply cnv_preserved_by_eq.
    eapply heq'.
    eapply (cnv_wt_prefix [ActIn a ; ActIn b]); eauto.
Qed.

Lemma cnv_input_perm `{LtsObaFW A L} p s1 s2 :
  are_inputs s1 -> s1 ≡ₚ s2 -> p ⇓ s1 -> p ⇓ s2.
Proof.
  intros his hp hcnv.
  revert p his hcnv.
  induction hp; intros; eauto with mdb.
  - inversion hcnv; subst.
    eapply cnv_act; eauto with mdb.
    intros q w. eapply IHhp; eauto with mdb.
    now inversion his.
  - inversion his. inversion H6.
    destruct H5, H9. subst.
    now eapply cnv_input_swap.
  - eapply IHhp2. eapply are_inputs_preserved_by_perm; eauto.
    eapply IHhp1. eapply are_inputs_preserved_by_perm; eauto.
    eassumption.
Qed.

Lemma cnv_output_swap `{LtsObaFW A L} p a b s :
  p ⇓ ActOut a :: ActOut b :: s -> p ⇓ ActOut b :: ActOut a :: s.
Proof.
  intros hcnv.
  eapply cnv_act.
  - now inversion hcnv.
  - intros q hw1.
    eapply cnv_act.
    eapply (cnv_terminate q []).
    eapply cnv_preserved_by_wt_output; eauto. eapply cnv_nil. now inversion hcnv.
    intros t hw2.
    replace (ActOut a :: ActOut b :: s) with ([ActOut a ; ActOut b] ++ s) in hcnv.
    set (hw3 := wt_concat _ _ _ _ _ hw1 hw2). simpl in hw3.
    eapply wt_output_swap in hw3 as (t' & hw4 & eq').
    eapply cnv_preserved_by_eq. eassumption.
    eapply cnv_wt_prefix. eauto. eassumption.
    now simpl.
Qed.

Lemma cnv_output_perm `{LtsObaFW A L} p s1 s2 :
  are_outputs s1 -> s1 ≡ₚ s2 -> p ⇓ s1 -> p ⇓ s2.
Proof.
  intros hos hp hcnv.
  revert p hos hcnv.
  induction hp; intros; eauto with mdb.
  - inversion hcnv; subst.
    eapply cnv_act; eauto with mdb.
    intros q w. eapply IHhp; eauto with mdb.
    now inversion hos.
  - inversion hos. inversion H6.
    destruct H5, H9. subst.
    now eapply cnv_output_swap.
  - eapply IHhp2.
    eapply Permutation_Forall; eassumption.
    eapply IHhp1.
    eapply Permutation_Forall. now symmetry. eassumption.
    eassumption.
Qed.

Lemma wt_input_perm `{LtsObaFW A L} {p q} s1 s2 :
  are_inputs s1 -> s1 ≡ₚ s2 -> p ⟹[s1] q -> p ⟹⋍[s2] q.
Proof.
  intros his hp w.
  revert p q his w.
  dependent induction hp; intros; eauto.
  - exists q. split. eassumption. reflexivity.
  - eapply wt_pop in w as (p' & w0 & w1).
    replace (x :: l') with ([x] ++ l') by eauto.
    eapply wt_join_eq_r. eassumption.
    eapply IHhp. now inversion his. eassumption.
  - inversion his. inversion H6.
    destruct H5, H9. subst.
    replace (ActIn x3 :: ActIn x2 :: l) with ([ActIn x3 ; ActIn x2] ++ l) by eauto.
    replace (ActIn x2 :: ActIn x3 :: l) with ([ActIn x2 ; ActIn x3] ++ l) in w by eauto.
    eapply wt_split in w as (p' & w1 & w2).
    eapply wt_join_eq_l.
    eapply wt_input_swap. eassumption. eassumption.
  - eapply IHhp1 in w as (q' & hw' & heq'); eauto.
    eapply IHhp2 in hw' as (q'' & hw'' & heq''); eauto.
    exists q''. split; eauto. etrans; eauto.
    eapply are_inputs_preserved_by_perm; eauto.
Qed.

Lemma wt_output_perm `{LtsObaFW A L} {p q} s1 s2 :
  are_outputs s1 -> s1 ≡ₚ s2 -> p ⟹[s1] q -> p ⟹⋍[s2] q.
Proof.
  intros hos hp w.
  revert p q hos w.
  dependent induction hp; intros; eauto.
  - exists q. split. eassumption. reflexivity.
  - eapply wt_pop in w as (p' & w0 & w1).
    replace (x :: l') with ([x] ++ l') by eauto.
    eapply wt_join_eq_r. eassumption.
    eapply IHhp. now inversion hos. eassumption.
  - inversion hos. inversion H6.
    destruct H5, H9. subst.
    replace (ActOut x3 :: ActOut x2 :: l) with ([ActOut x3 ; ActOut x2] ++ l) by eauto.
    replace (ActOut x2 :: ActOut x3 :: l) with ([ActOut x2 ; ActOut x3] ++ l) in w by eauto.
    eapply wt_split in w as (p' & w1 & w2).
    eapply wt_join_eq_l.
    eapply wt_output_swap. eassumption. eassumption.
  - eapply IHhp1 in w as (q' & hw' & heq'); eauto.
    eapply IHhp2 in hw' as (q'' & hw'' & heq''); eauto.
    exists q''. split; eauto. etrans; eauto.
    eapply are_outputs_preserved_by_perm; eauto.
Qed.

Lemma push_wt_output `{LtsObaFW A L} {p q a s} :
  p ⟹[ActOut a :: s] q ->
  p ⟹⋍[s ++ [ActOut a]] q.
Proof.
  intro w.
  eapply wt_pop in w as (t & w1 & w2).
  eapply wt_decomp_one in w1 as (t1 & t2 & w3 & l & w4).
  set (w5 := wt_push_nil_left w4 w2).
  destruct (delay_wt_output (mk_lts_eq l) w5) as (r & w6 & w7).
  eapply wt_join_eq.
  exists r. split.
  eapply wt_push_nil_left; eassumption. reflexivity.
  destruct w7 as (u & hwu & hequ).
  exists u. split. eapply wt_act. eassumption. eapply wt_nil. eassumption.
Qed.

Lemma map_co_are_inputs_are_outputs {L} (s : trace L) : are_inputs s -> are_outputs (map co s).
Proof.
  induction s; intros his.
  - now eapply Forall_nil.
  - inversion his. destruct H1. subst. simpl.
    eapply Forall_cons. eexists. reflexivity. eapply IHs. eauto.
Qed.

Lemma cnv_retract `{LtsObaFW A L} p q s1 s2 :
  are_outputs s1 -> p ⇓ s2 -> p ⟹[s1] q -> q ⇓ map co s1 ++ s2.
Proof.
  revert s2 p q.
  induction s1; intros s2 p q hos hcnv w.
  - eapply cnv_preserved_by_wt_nil; eauto.
  - inversion hos. destruct H5. subst. simpl.
    eapply push_wt_output in w as (q' & hwq' & heqq').
    eapply wt_split in hwq' as (t & w1 & w2).
    eapply cnv_preserved_by_eq. eassumption.
    eapply cnv_retract_wt_output.
    eapply (IHs1 s2 p t H6 hcnv w1). eassumption.
Qed.

Lemma forward_s `{LtsObaFW A L} p s :
  are_inputs s -> exists t, p ⟹[s] t /\ t ⟹⋍[map co s] p.
Proof.
  intros his. revert p his. dependent induction s; intros.
  - exists p. simpl. split; eauto with mdb.
    exists p. split; eauto with mdb. reflexivity.
  - inversion his. destruct H5. subst.
    simpl.
    destruct (lts_oba_fw_forward p x0) as (q & l0 & l1).
    destruct (IHs q H6) as (q' & w1 & w2).
    exists q'. split.
    + eauto with mdb.
    + assert (q' ⟹⋍[map co s ++ [ActOut x0]] p).
      eapply wt_join_eq.
      eassumption. (* destruct l1 as (p' & hlp' & heqp'). *)
      exists p. split. eauto with mdb. reflexivity.
      destruct H3 as (p' & hwp' & heqp').
      eapply (wt_output_perm (map co s ++ [ActOut x0])) in hwp' as (p0 & hwp0 & heqp0).
      exists p0. split. eassumption. etrans; eassumption.
      eapply Forall_app. split.
      now eapply map_co_are_inputs_are_outputs.
      eapply Forall_cons. eauto. eexists. reflexivity. eauto.
      symmetry. eapply Permutation_cons_append.
Qed.

Lemma map_co_involution {L} (s : trace L) : map co (map co s) = s.
Proof. induction s; cbn; eauto. now rewrite co_involution, IHs. Qed.

Lemma cnv_drop_output_in_the_middle `{LtsObaFW A L} p s1 s2 a :
  are_inputs s1 ->
  p ⇓ s1 ++ [ActOut a] ++ s2 ->
  forall r, p ⟶[ActOut a] r -> r ⇓ s1 ++ s2.
Proof.
  intros his hcnv r l.
  destruct (forward_s r s1 his) as (t & w1 & w2).
  destruct (delay_wt_output (mk_lts_eq l) w1) as (t' & w3 & l4).
  replace s1 with (map co (map co s1)) by eapply map_co_involution.
  destruct l4 as (t0 & hlt0 & heqt0).
  destruct w2 as (t1 & hwt1 & heqt1).
  set (h := eq_spec_wt t t0 (symmetry heqt0) t1 _ hwt1).
  destruct h as (t2 & hwt2 & heqt2).
  eapply cnv_preserved_by_eq. etrans. eapply heqt2. eassumption.
  eapply (cnv_retract t0); eauto.
  eapply map_co_are_inputs_are_outputs. eassumption.
  eapply (cnv_wt_prefix (s1 ++ [ActOut a]) _ p).
  now rewrite <- app_assoc. eapply wt_concat; eauto with mdb.
Qed.

Lemma cnv_drop_input_in_the_middle `{LtsObaFW A L} p s1 s2 a :
  are_inputs s1 ->
  p ⇓ s1 ++ [ActIn a] ++ s2 ->
  forall r, p ⟶[ActIn a] r -> r ⇓ s1 ++ s2.
Proof.
  intros his hcnv r l.
  destruct (forward_s r s1 his) as (t & w1 & w2).
  replace s1 with (map co (map co s1)) by eapply map_co_involution.
  destruct w2 as (r' & hwr' & heqr').
  assert (p ⟹⋍[s1 ++ [ActIn a]] t).
  eapply (wt_input_perm (ActIn a :: s1)).
  eapply Forall_cons. eexists. reflexivity.  eassumption.
  eapply Permutation_cons_append.
  eapply wt_act; eassumption.
  destruct H3 as (t' & hwt' & heqt').
  eapply cnv_preserved_by_eq. eapply heqr'.
  eapply (cnv_retract t); eauto.
  eapply map_co_are_inputs_are_outputs. eassumption.
  eapply cnv_preserved_by_eq. eassumption.
  eapply (cnv_wt_prefix (s1 ++ [ActIn a]) _ p).
  now rewrite <- app_assoc.
  eassumption.
Qed.

Lemma cnv_drop_in_the_middle `{LtsObaFW A L} p s1 s2 μ :
  are_inputs s1 -> p ⇓ s1 ++ [μ] ++ s2 -> forall r, p ⟶[μ] r -> r ⇓ s1 ++ s2.
Proof.
  intros his hcnv r l.
  destruct μ; [eapply cnv_drop_input_in_the_middle | eapply cnv_drop_output_in_the_middle]; eauto.
Qed.

Lemma cnv_annhil `{LtsObaFW A L} p a s1 s2 s3 :
  are_inputs s1 -> are_inputs s2 ->
  p ⇓ s1 ++ [ActIn a] ++ s2 ++ [ActOut a] ++ s3 ->
  p ⇓ s1 ++ s2 ++ s3.
Proof.
  intros his1 his2 hcnv.
  edestruct (forward_s p (s1 ++ [ActIn a] ++ s2)) as (t & w1 & w2).
  eapply Forall_app. split; eauto.
  eapply Forall_app. split; eauto.
  eapply Forall_cons. eexists. reflexivity. now eapply Forall_nil.
  rewrite 2 map_app in w2. simpl in w2.
  destruct w2 as (r & hwr & heqr).
  eapply (wt_output_perm _ ([ActOut a] ++ map co s1 ++ map co s2)) in hwr as (r0 & hwr0 & heqr0).
  eapply wt_split in hwr0 as (r1 & hwr0 & hwr1).
  rewrite <- map_app in hwr1.
  rewrite app_assoc.
  replace ((s1 ++ s2) ++ s3) with (map co (map co (s1 ++ s2)) ++ s3).
  eapply cnv_preserved_by_eq. etrans. eapply heqr0. eapply heqr.
  eapply cnv_retract.
  eapply map_co_are_inputs_are_outputs. eapply Forall_app. split; assumption.
  eapply cnv_wt_prefix. rewrite 3 app_assoc in hcnv.
  eassumption.
  eapply wt_concat. rewrite <- app_assoc. eassumption. eassumption.
  eassumption.
  now rewrite map_co_involution.
  eapply Forall_app. split.
  eapply map_co_are_inputs_are_outputs. assumption.
  eapply Forall_cons. eexists. reflexivity.
  eapply map_co_are_inputs_are_outputs. assumption.
  symmetry. eapply Permutation_app_swap_app.
Qed.

Lemma parallel_step_commutative `{M1: Lts A L, M2: Lts B L} (s1 s'1: A) (s2 s'2: B) ℓ:
  parallel_step (s1, s2) ℓ (s'1, s'2) → parallel_step (s2, s1) ℓ (s'2, s'1).
Proof.
  intros Hstep. inversion Hstep; simplify_eq; [by econstructor|by econstructor|].
  eapply act_match_commutative in eq.
  eapply (ParSync _ _ _ _ _ _ eq l2 l1); eauto.
Qed.

Fixpoint search_steps {S1 S2 L: Type} `{Label L} (M1: Lts S1 L) (M2: Lts S2 L) (s1: S1) (s2: S2) s'1 s'2 candidates :=
  match candidates with
  | [] => None
  | x::xs =>
      if decide (lts_step s1 (ActExt (ActOut x)) s'1 ∧ lts_step s2 (ActExt (ActIn x)) s'2) then
        Some x
      else
        search_steps M1 M2 s1 s2 s'1 s'2 xs
  end.

Lemma search_steps_spec_helper {S1 S2 L: Type} `{Label L} lnot (M1: Lts S1 L) (M2: Lts S2 L) s1 s2 s'1 s'2 l:
  (elements $ lts_outputs s1) = lnot ++ l →
  (∀ x, x ∈ lnot → ¬ (s1 ⟶[ActOut x] s'1 ∧ s2 ⟶[ActIn x] s'2)) →
  is_Some $ search_steps M1 M2 s1 s2 s'1 s'2 l <->
  ∃ x, s1 ⟶[ActOut x] s'1 ∧ s2 ⟶[ActIn x] s'2.
Proof.
  revert lnot. induction l; intros lnot.
  { simpl. intros Hels Hnots. split; [intros Hc; inversion Hc; done |]. intros (?&Hstep&?). exfalso.
    specialize (lts_outputs_spec1 _ _ _ Hstep) as ?. simplify_list_eq. set_solver. }
  intros Helems Hnots. simpl.
  destruct (decide (s1 ⟶[ActOut a] s'1 ∧ s2 ⟶[ActIn a] s'2)); [by split; eauto|].
  apply (IHl (lnot ++ [a])); [by simplify_list_eq|].
  intros x [Hin | Hin%elem_of_list_singleton]%elem_of_app; simplify_eq; eauto.
Qed.

Lemma search_steps_spec_1 {S1 S2 L: Type} `{Label L} (M1: Lts S1 L) (M2: Lts S2 L) s1 s2 s'1 s'2:
  is_Some $ search_steps M1 M2 s1 s2 s'1 s'2 (elements $ lts_outputs s1) <->
  ∃ x, (s1 ⟶[ActOut x] s'1 ∧ s2 ⟶[ActIn x] s'2).
Proof. apply (search_steps_spec_helper []); [done| intros ??; set_solver]. Qed.

Lemma search_steps_spec_2 {S1 S2 L: Type} `{Label L} x (M1: Lts S1 L) (M2: Lts S2 L) s1 s2 s'1 s'2 l:
  search_steps M1 M2 s1 s2 s'1 s'2 l = Some x →
  (s1 ⟶[ActOut x] s'1 ∧ s2 ⟶[ActIn x] s'2).
Proof.
  induction l; [done|]. simpl.
  destruct (decide (s1 ⟶[ActOut a] s'1 ∧ s2 ⟶[ActIn a] s'2)); [|eauto].
  intros ?. simplify_eq. done.
Qed.

Definition decide_parallel_step {S1 S2 L: Type} `{Label L} (M1: Lts S1 L) (M2: Lts S2 L) (s1: S1) (s2: S2) ℓ s'1 s'2:
  Decision (parallel_step (s1, s2) ℓ (s'1, s'2)).
Proof.
  destruct (decide (M1.(lts_step) s1 ℓ s'1 ∧ s2 = s'2)) as [[??]|Hnot1].
  { simplify_eq. left. by constructor. }
  destruct (decide (M2.(lts_step) s2 ℓ s'2 ∧ s1 = s'1)) as [[??]|Hnot2].
  { simplify_eq. left. by constructor. }
  destruct ℓ.
  { right. intros contra; inversion contra; simplify_eq; eauto. }
  destruct (search_steps _ _ s1 s2 s'1 s'2 (elements $ lts_outputs s1)) as [x|] eqn:Hpar1.
  { apply search_steps_spec_2 in Hpar1 as [??]. left; eapply ParSync; eauto. done. }
  destruct (search_steps _ _ s2 s1 s'2 s'1 (elements $ lts_outputs s2)) as [x|] eqn:Hpar2.
  { apply search_steps_spec_2 in Hpar2 as [??]. left; eapply ParSync; eauto. done. }
  right; intros contra; inversion contra; simplify_eq; eauto.
  destruct α1 as [a|], α2 as [b|]; eauto.
  destruct a, b; eauto; simpl in *; simplify_eq.
  - assert (is_Some $ search_steps _ _ s2 s1 s'2 s'1 (elements (lts_outputs s2))) as Hc; [|].
    apply search_steps_spec_1. eexists; split; eauto.
    rewrite Hpar2 in Hc. by inversion Hc.
  - assert (is_Some $ search_steps _ _ s1 s2 s'1 s'2 (elements (lts_outputs s1))) as Hc; [|].
    apply search_steps_spec_1. eexists; split; eauto.
    rewrite Hpar1 in Hc. by inversion Hc.
Qed.


Fixpoint parallel_lts_stable_helper {S1 S2 L: Type} `{Label L} {M1: Lts S1 L} {M2: Lts S2 L}
  (s1: S1) (s2: S2) (l: list L) : bool :=
  match l with
  | [] => true
  | a::bs =>
      if decide (¬lts_stable s1 (ActExt $ ActOut a) ∧ ¬lts_stable s2 (ActExt $ ActIn a)) then
        false else parallel_lts_stable_helper s1 s2 bs
  end.

Lemma parallel_sts_stable_helper_spec_1 {S1 S2 L: Type} `{Label L} {M1: Lts S1 L} {M2: Lts S2 L}
  (s1: S1) (s2: S2) (l: list L) :
  parallel_lts_stable_helper s1 s2 l = false → {s' | parallel_step (s1, s2) τ s'}.
Proof.
  induction l; [done|].
  simpl. destruct (decide (¬lts_stable s1 (ActExt (ActOut a)) ∧ ¬lts_stable s2 (ActExt (ActIn a))))
    as [[Hs1 Hs2]|]; eauto. intros _.
  apply lts_stable_spec1 in Hs1 as [s'1 ?].
  apply lts_stable_spec1 in Hs2 as [s'2 ?].
  refine ((s'1, s'2) ↾ _). econstructor 3; eauto. done.
Qed.

Lemma parallel_sts_stable_helper_spec_2 {S1 S2 L: Type} `{Label L} {M1: Lts S1 L} {M2: Lts S2 L}
  (s1: S1) (s2: S2) a s'1 s'2 :
  s1 ⟶[ActOut a] s'1 → s2 ⟶[ActIn a] s'2 →
  parallel_lts_stable_helper s1 s2 (elements $ lts_outputs s1) = false.
Proof.
  intros Hs1 Hs2.
  assert (∀ l rest,
             (elements $ lts_outputs s1) = rest ++ l →
             (∀ x, x ∈ rest → ¬ (s1 ⟶[ActOut x] s'1 ∧ s2 ⟶[ActIn x] s'2)) →
             parallel_lts_stable_helper s1 s2 l = false) as Hccl.
  induction l as [| b l IHl].
  - intros rest Hrest Hnots. pose proof (lts_outputs_spec1 _ _ _ Hs1) as Hin. simplify_list_eq.
    exfalso. eapply Hnots; eauto. set_solver.
  - intros rest Hrest Hnots. simplify_list_eq.
    destruct (decide (¬ lts_stable s1 (ActExt (ActOut b)) ∧ ¬ lts_stable s2 (ActExt (ActIn b)))); [auto|].
    eapply (IHl (rest ++ [b])); [by simplify_list_eq|].
    intros x [Hin | ->%elem_of_list_singleton]%elem_of_app; [eauto|].
    intros [Hstep1 Hstep2].
    pose proof (lts_stable_spec2 _ _ (_ ↾ Hstep1)). pose proof (lts_stable_spec2 _ _ (_ ↾ Hstep2)). eauto.
  - apply (Hccl _ []); eauto. set_solver.
Qed.

Definition parallel_lts_stable {S1 S2 L: Type} `{Label L} (M1: Lts S1 L) (M2: Lts S2 L)
  (s1: S1) (s2: S2) (ℓ : Act L): Prop :=
  lts_stable s1 ℓ ∧ lts_stable s2 ℓ ∧
    match ℓ with
    | τ => parallel_lts_stable_helper s1 s2 (elements $ lts_outputs s1)
        ∧ parallel_lts_stable_helper s2 s1 (elements $ lts_outputs s2)
    | _ => True
    end.

#[global]
Instance parallel_lts {S1 S2 L: Type} `{Label L} (M1: Lts S1 L) (M2: Lts S2 L):
  Lts (S1 * S2) L.
Proof.
  refine (MkLts _ _ _ parallel_step _ _
            (λ s, M1.(lts_outputs) s.1 ∪  M2.(lts_outputs) s.2) _
            _
            (λ s, parallel_lts_stable M1 M2 s.1 s.2) _ _ _).
  - intros [s1 s2] ℓ [s'1 s'2]. apply decide_parallel_step.
  - intros s1 x s2 Hstep. inversion Hstep; simplify_eq.
    + pose proof M1.(lts_outputs_spec1). set_solver.
    + pose proof M2.(lts_outputs_spec1). set_solver.
  - intros (s1, s2) x mem.
    destruct (decide (x ∈ lts_outputs s1)).
    eapply lts_outputs_spec2 in e as (s' & hl').
    exists (s', s2). now eapply ParLeft.
    destruct (decide (x ∈ lts_outputs s2)).
    eapply lts_outputs_spec2 in e as (s' & hl').
    exists (s1, s'). now eapply ParRight.
    exfalso. set_solver.
  - intros ??. unfold parallel_lts_stable.
    apply and_dec; [apply _|apply and_dec; [apply _|]]. destruct α; apply _.
  - intros [a b] ℓ Hns. simpl in Hns. unfold parallel_lts_stable in Hns.
    destruct (decide (lts_stable a ℓ)) as [|Hns1]; cycle 1.
    { apply lts_stable_spec1 in Hns1 as [s' ?]. refine ((s', b) ↾ _). by constructor. }
    destruct (decide (lts_stable b ℓ)) as [|Hns2]; cycle 1.
    { apply lts_stable_spec1 in Hns2 as [s' ?]. refine ((a, s') ↾ _). by constructor. }
    destruct ℓ as [n|]; [exfalso; by apply Hns|].
    destruct (parallel_lts_stable_helper a b (elements (lts_outputs a))) eqn:Hs1; cycle 1.
    { by apply parallel_sts_stable_helper_spec_1 in Hs1. }
    destruct (parallel_lts_stable_helper b a (elements (lts_outputs b))) eqn:Hs2; cycle 1.
    { apply parallel_sts_stable_helper_spec_1 in Hs2 as [[??] Hstep%parallel_step_commutative].
      exact (_ ↾ Hstep). }
    exfalso. apply Hns; eauto.
  - intros [s1 s2] ℓ [[s'1 s'2] Hstep].
    unfold parallel_lts_stable. rewrite !not_and_l.
    inversion Hstep; simplify_eq; simpl.
    + pose proof (lts_stable_spec2 _ _ (s'1 ↾ l)). eauto.
    + pose proof (lts_stable_spec2 _ _ (s'2 ↾ l)). eauto.
    + destruct α1 as [a|], α2 as [b|]; eauto.
      destruct a as [a|a], b as [b|b]; eauto;
        simpl in *; simplify_eq.
      * assert (parallel_lts_stable_helper s2 s1 (elements $ lts_outputs s2) = false) as Hccl; cycle 1.
        { right; right. intros [??]. by rewrite Hccl in *. }
        eapply parallel_sts_stable_helper_spec_2; eauto.
      * assert (parallel_lts_stable_helper s1 s2 (elements $ lts_outputs s1) = false) as Hccl; cycle 1.
        { right; right. intros [??]. by rewrite Hccl in *. }
        eapply parallel_sts_stable_helper_spec_2; eauto.
Defined.

Class Sts (A: Type) := MkSts {
    sts_step: A → A → Prop;
    sts_state_eqdec: EqDecision A;
    sts_step_decidable: RelDecision sts_step;

    sts_stable: A → Prop;
    sts_stable_decidable p : Decision (sts_stable p);
    sts_stable_spec1 p : ¬ sts_stable p -> { q | sts_step p q };
    sts_stable_spec2 p : { q | sts_step p q } → ¬ sts_stable p;
}.
#[global] Existing Instance sts_state_eqdec.
#[global] Existing Instance sts_step_decidable.
#[global] Existing Instance sts_stable_decidable.

Definition istep `{Lts L} p q := lts_step p τ q.

#[global]
Program Instance sts_of_lts {A L} `{Label L} (M: Lts A L): Sts A :=
  {|
    sts_step := istep;
    sts_stable s := lts_stable s τ;
  |}.
Next Obligation. intros ??????. apply _. Defined.
Next Obligation. intros ??????. by apply lts_stable_spec1. Qed.
Next Obligation. intros ??????. by apply lts_stable_spec2. Qed.

Section sts_executions.
  Context `{Sts A}.

  CoInductive max_exec_from: A -> Type :=
  | MExStop x (Hstable: sts_stable x): max_exec_from x
  | MExStep x x' (Hstep: sts_step x x') (η: max_exec_from x'): max_exec_from x.

  CoInductive iexec_from: A -> Type :=
  | IExStep x x' (Hstep: sts_step x x') (η: iexec_from x'): iexec_from x.

  Inductive finexec_from: A -> Type :=
  | FExSingl x : finexec_from x
  | FExStep x x' (Hstep: bool_decide (sts_step x x')) (η: finexec_from x'): finexec_from x.

  Definition iexec_from_first {x:A} (η: iexec_from x) :=
    match η with IExStep x _ _ _ => x end.

  Record iexec := MkExec {
    iex_start: A;
    iex: iexec_from iex_start;
  }.

  Definition ex_cons x η (Hstep: sts_step x η.(iex_start)) : iexec :=
    MkExec x (IExStep _ _ Hstep η.(iex)).

  Inductive finexec :=
  | FinExNil: finexec
  | FinExNonNil x (ρ: finexec_from x): finexec.

  Definition fex_cons x p :=
    match p with
    | FinExNil => Some $ FinExNonNil x (FExSingl x)
    | FinExNonNil y p =>
        match decide (sts_step x y) with
        | right _ => None
        | left Hstep => Some $ FinExNonNil _ $ FExStep x y (bool_decide_pack _ Hstep) p
        end
    end.

  Fixpoint iex_take_from (n: nat) {x} (η: iexec_from x) : finexec_from x :=
    match n with
    | 0 => FExSingl x
    | S n => match η with IExStep x x' Hstep η' =>
             let p' := iex_take_from n η' in
             FExStep x x' (bool_decide_pack _ Hstep) p'
            end
    end.

  Fixpoint mex_take_from (n: nat) {x} (η: max_exec_from x) : option (finexec_from x) :=
    match n with
    | 0 => Some $ FExSingl x
    | S n => match η with
            | MExStop x Hstable => None
            | MExStep x x' Hstep η' =>
                let p' := mex_take_from n η' in
                (λ p', FExStep x x' (bool_decide_pack _ Hstep) p') <$> p'
            end
    end.

  Definition iex_take (n: nat) (η: iexec) : finexec :=
    match n with
    | 0 => FinExNil
    | S n => FinExNonNil η.(iex_start) (iex_take_from n η.(iex))
    end.

  Lemma iex_fex_take_from n {x y η} Hstep:
    iex_take_from (1+n) (IExStep x y Hstep η) = FExStep x y (bool_decide_pack _ Hstep) (iex_take_from n η).
  Proof. revert x y η Hstep. induction n as [|n IHn]; intros x y η Hstep; easy. Qed.

  Lemma iex_fex_take n {x η} Hstep:
    Some $ iex_take (1+n) (ex_cons x η Hstep) = fex_cons x (iex_take n η).
  Proof.
    case n; simpl; [easy|].
    intros ?. destruct (decide (sts_step x (iex_start η))); [|easy].
    do 3 f_equal. assert (ProofIrrel $ bool_decide (sts_step x (iex_start η))) by apply _. naive_solver.
  Qed.

  Fixpoint iex_snoc_from x (ex1: finexec_from x) (a: A) : option (finexec_from x) :=
    match ex1 with
    | FExSingl x =>
        if decide (sts_step x a)
        then Some (FExStep x _ ltac:(eauto) (FExSingl a))
        else None
    | FExStep x x' Hstep η =>
        match iex_snoc_from x' η a with
        | None => None
        | Some p => Some(FExStep x x' Hstep p)
        end
    end.

  Definition iex_snoc (ex1: finexec) (a: A) : option finexec :=
    match ex1 with
    | FinExNil => Some (FinExNonNil _ (FExSingl a))
    | FinExNonNil x η =>
        match iex_snoc_from x η a with
        | None => None
        | Some η => Some (FinExNonNil x η)
        end
    end.

  Fixpoint fex_from_last {x} (p: finexec_from x) : A :=
    match p with
    | FExSingl y => y
    | FExStep _ y _ p' => fex_from_last p'
    end.

  Definition fex_last (p: finexec) : option A :=
    match p with
    | FinExNil => None
    | FinExNonNil _ p' => Some $ fex_from_last p'
    end.

  Definition fex_first (p: finexec) : option A :=
    match p with
    | FinExNil => None
    | FinExNonNil x _ => Some x
    end.

  Lemma fex_snoc_from_valid_last x z ρ:
    sts_step (fex_from_last ρ) z →
    is_Some (iex_snoc_from x ρ z).
  Proof.
    revert z. induction ρ as [| y t Hbstep ρ IH]; intros z Hstep; simpl in *.
    - by destruct (decide (sts_step x z)).
    - by destruct (IH _ Hstep) as [? ->].
  Qed.

  Lemma fex_snoc_valid_last ex y z:
    fex_last ex = Some y →
    sts_step y z →
    is_Some (iex_snoc ex z).
  Proof.
    case ex; [easy|]. simpl. intros ??? Hstep. simplify_eq.
    by destruct (fex_snoc_from_valid_last _ _ _ Hstep) as [? ->].
  Qed.

  Definition finex_singl x := FinExNonNil x (FExSingl x).

  Definition iexec_from_tail {x:A} (η: iexec_from x) : iexec :=
    match η with IExStep x x' _ η => MkExec x' η end.

  Lemma iex_snoc_step x η1 η2 a:
    iex_snoc_from x η1 a = Some η2 →
    fex_from_last η2 = a ∧ sts_step (fex_from_last η1) (fex_from_last η2).
  Proof.
    revert η2 a; induction η1 as [|b c Hstep η1 IHη]; intros η2 a.
    - simpl. destruct (decide (sts_step x a)); [injection 1; intros ?; simplify_eq|]; easy.
    - simpl. destruct (iex_snoc_from c η1 a) as [p|] eqn:Heq;
        [injection 1; intros ?; simplify_eq|easy].
      simpl. by destruct (IHη _ _ Heq) as [??].
  Qed.
End sts_executions.

Class CountableSts A `{Sts A} := MkCsts {
    csts_states_countable: Countable A;
    csts_next_states_countable: ∀ x, Countable (dsig (fun y => sts_step x y));
}.
#[global] Existing Instance csts_states_countable.
#[global] Existing Instance csts_next_states_countable.

Class CountableLts A L `{Lts A L} := MkClts {
    clts_states_countable: Countable A;
    clts_next_states_countable: ∀ x ℓ, Countable (dsig (fun y => lts_step x ℓ y));
}.
#[global] Existing Instance clts_states_countable.
#[global] Existing Instance clts_next_states_countable.

#[global]
Instance csts_of_clts {A L} `{Lts A L} (M: CountableLts A L): CountableSts A.
Proof.
  apply MkCsts.
  - exact clts_states_countable.
  - intros ?. apply clts_next_states_countable.
Defined.

#[global]
Instance parallel_clts {S1 S2 L: Type} `{Label L} `{!Lts S1 L} `{!Lts S2 L} `{M1: !CountableLts S1 L} `{M2: !CountableLts S2 L}:
  CountableLts (S1 * S2) L.
Proof.
  apply MkClts.
  - eapply prod_countable.
  - intros x ℓ. apply countable_sig. intros y.
    destruct (decide (bool_decide (x ⟶{ℓ} y))); [left | right]; done.
Qed.

#[global] Instance finite_countable_lts `{FiniteLts A L} : CountableLts A L.
Proof. constructor; first apply _. intros *; apply finite_countable. Qed.

(** A mailbox is a multiset of names. *)

Definition mb (L : Type) `{Label L} := gmultiset L.

(** Lts extended with forwarders. *)

Inductive lts_fw_step {A L : Type} `{Lts A L} : A * mb L -> Act L -> A * mb L -> Prop :=
| lts_fw_p p q m α:
  lts_step p α q -> lts_fw_step (p, m) α (q, m)
| lts_fw_out_mb m p a :
  lts_fw_step (p, {[+ a +]} ⊎ m) (ActExt $ ActOut a) (p, m)
| lts_fw_inp_mb m p a :
  lts_fw_step (p, m) (ActExt $ ActIn a) (p, {[+ a +]} ⊎ m)
| lts_fw_com m p a q :
  lts_step p (ActExt $ ActIn a) q ->
  lts_fw_step (p, {[+ a +]} ⊎ m) τ (q, m)
.

Global Hint Constructors lts_fw_step:mdb.

(** Stout reduction. *)

Reserved Notation "p ⟿{ m } q" (at level 30, format "p  ⟿{ m }  q").

Inductive strip `{Lts A L} : A -> gmultiset L -> A -> Prop :=
| strip_nil p : p ⟿{∅} p
| strip_step p1 p2 p3 a m :
  p1 ⟶[ActOut a] p2 -> p2 ⟿{m} p3 -> p1 ⟿{{[+ a +]} ⊎ m} p3

where "p ⟿{ m } q" := (strip p m q).

(** Equivalence between forwarders. *)

Definition fw_eq `{LtsOba A L} (p : A * mb L) (q : A * mb L) :=
  forall (p' q' : A),
    p.1 ⟿{lts_oba_mo p.1} p' ->
    q.1 ⟿{lts_oba_mo q.1} q' ->
    p' ⋍ q' /\ lts_oba_mo p.1 ⊎ p.2 = lts_oba_mo q.1 ⊎ q.2.

Infix "≐" := fw_eq (at level 70).

Lemma strip_eq_sim_ex `{LtsOba A L} {e e' m} :
  e ⟿{m} e' -> forall r, r ⋍ e -> exists r', r ⟿{m} r' /\ r' ⋍ e'.
Proof.
  intro w.
  dependent induction w; intros r heq.
  - exists r. split. constructor. assumption.
  - destruct (eq_spec r p2 (ActExt $ ActOut a)) as (r0 & l0 & heq0). eauto.
    destruct (IHw r0 heq0) as (r' & hwo' & heq').
    exists r'. split. eapply strip_step; eassumption. eassumption.
Qed.

Lemma strip_mem_ex `{LtsOba A L} {p1 p2 m a} :
  p1 ⟿{{[+ a +]} ⊎ m} p2 -> exists p', p1 ⟶[ActOut a] p'.
Proof.
  intros hw.
  dependent induction hw.
  - multiset_solver.
  - assert (mem : a ∈ {[+ a0 +]} ⊎ m0). rewrite x. multiset_solver.
    eapply gmultiset_elem_of_disj_union in mem as [here | there].
    + eapply gmultiset_elem_of_singleton in here. subst. firstorder.
    + edestruct IHhw; eauto.
      eapply gmultiset_disj_union_difference' in there; eassumption.
      edestruct (lts_oba_output_commutativity H2 H3) as (u & l2 & l3).
      eauto.
Qed.

Lemma strip_eq_step `{@LtsOba A L IL LA LOA} {e e' m a} :
  e ⟿{{[+ a +]} ⊎ m} e' -> forall r, e ⟶[ActOut a] r -> exists t, r ⟿{m} t /\ t ⋍ e'.
Proof.
  intro w.
  dependent induction w.
  - multiset_solver.
  - intros r l.
    destruct (decide (a = a0)); subst.
    + assert (eq_rel p2 r) by (eapply lts_oba_output_deter; eassumption).
      eapply gmultiset_disj_union_inj_1 in x. subst.
      eapply strip_eq_sim_ex. eassumption. symmetry. assumption.
    + assert (m0 = {[+ a +]} ⊎ m ∖ {[+ a0 +]}) by multiset_solver.
      assert (ActOut a ≠ ActOut a0) by set_solver.
      edestruct (lts_oba_output_confluence H2 H0 l)
        as (t0 & l0 & (r1 & l1 & heq1)).
      eapply IHw in H1 as (t & hwo & heq); eauto.
      assert (mem : a0 ∈ m) by multiset_solver.
      eapply gmultiset_disj_union_difference' in mem. rewrite mem.
      edestruct (strip_eq_sim_ex hwo r1 heq1) as (t2 & hw2 & heq2).
      exists t2. split. eapply strip_step. eassumption. eassumption.
      etrans; eassumption.
Qed.

Lemma strip_m_deter `{LtsOba A L} {m p p1 p2} :
  p ⟿{m} p1 -> p ⟿{m} p2 -> p1 ⋍ p2.
Proof.
  revert p p1 p2.
  induction m using gmultiset_ind; intros p p1 p2 hw1 hw2.
  - inversion hw1; inversion hw2; subst; multiset_solver.
  - destruct (strip_mem_ex hw1) as (t1 & lt1).
    destruct (strip_mem_ex hw2) as (t2 & lt2).
    eapply strip_eq_step in hw1 as (r1 & hwr1 & heqr1); eauto.
    eapply strip_eq_step in hw2 as (r2 & hwr2 & heqr2); eauto.
    etrans. symmetry. eassumption.
    symmetry. etrans. symmetry. eassumption. eauto.
Qed.

Lemma strip_eq_sim `{LtsOba A L} {p q p' q' m} :
  p ⋍ q -> strip p m p' -> strip q m q' -> p' ⋍ q'.
Proof.
  intros heq hsp hsq.
  edestruct (strip_eq_sim_ex hsq) as (r & hsp' & heqr); eauto.
  transitivity r. eapply strip_m_deter; eauto. eassumption.
Qed.

Lemma fw_eq_refl `{LtsOba A L} : Reflexive fw_eq.
Proof.
  intros p p1 q2 hw1 hw2. split; [eapply strip_m_deter|]; eauto.
Qed.

Global Hint Resolve fw_eq_refl:mdb.

Lemma lts_oba_mo_eq `{LtsOba A L} {p q} : p ⋍ q -> lts_oba_mo p = lts_oba_mo q.
Proof.
  remember (lts_oba_mo p) as hmo.
  revert p q Heqhmo.
  induction hmo using gmultiset_ind; intros p q Heqhmo heq.
  - eapply leibniz_equiv. intros a.
    rewrite multiplicity_empty.
    destruct (lts_stable_decidable q (ActExt $ ActOut a)).
    + destruct (decide (a ∈ lts_oba_mo q)).
      ++ eapply lts_oba_mo_spec1, lts_outputs_spec2 in e as (t & hl).
         eapply lts_stable_spec2 in l; now eauto.
      ++ destruct (multiplicity a (lts_oba_mo q)) eqn:eq; multiset_solver.
    + eapply lts_stable_spec1 in n as (t & hl).
      edestruct (eq_spec p t (ActExt $ ActOut a)) as (u & hlu & hequ); eauto with mdb.
      eapply lts_outputs_spec1, lts_oba_mo_spec1 in hlu. multiset_solver.
  - assert {t | p ⟶[ActOut x] t} as (t & hlt).
    eapply lts_outputs_spec2, lts_oba_mo_spec1. multiset_solver.
    edestruct (eq_spec q t (ActExt $ ActOut x)) as (u & hlu & hequ).
    exists p. split. now symmetry. assumption.
    eapply lts_oba_mo_spec2 in hlu, hlt.
    assert (x ∈ lts_oba_mo q) by multiset_solver.
    eapply gmultiset_disj_union_difference' in H2.
    rewrite hlu.
    assert (hmo = lts_oba_mo t).
    eapply gmultiset_disj_union_inj_1. etrans; eassumption.
    eapply gmultiset_eq_pop_l. eapply IHhmo. eassumption. now symmetry.
Qed.

Lemma fw_eq_id_mb `{LtsOba A L} p q m : p ⋍ q -> fw_eq (p, m) (q, m).
Proof.
  intros heq p' q' hwp hwq. simpl in *.
  set (h := lts_oba_mo_eq heq).
  split. rewrite <- h in hwq. eapply (strip_eq_sim heq hwp hwq).
  multiset_solver.
Qed.

(** The structural congruence is symmetric. *)

Lemma fw_eq_symm `{LtsOba A L} : Symmetric fw_eq.
Proof.
  intros p q heq.
  intros q2 p2 hw1 hw2.
  destruct (heq p2 q2 hw2 hw1) as (heq2 & hmo2). naive_solver.
Qed.

Global Hint Resolve fw_eq_symm:mdb.

(** Lemmas about strip. *)

Lemma lts_oba_mo_strip `{LtsOba A L} (p : A) : exists (q : A), strip p (lts_oba_mo p) q.
Proof.
  remember (lts_oba_mo p) as ns.
  revert p Heqns.
  induction ns using gmultiset_ind; intros.
  - exists p. constructor.
  - assert (mem : x ∈ lts_oba_mo p) by multiset_solver.
    assert (exists q, p ⟶[ActOut x] q) as (q & l).
    eapply lts_oba_mo_spec1, lts_outputs_spec2 in mem as (q & l); eauto.
    set (h := lts_oba_mo_spec2 p x q l) in mem.
    assert (ns = lts_oba_mo q). rewrite <- Heqns in h. multiset_solver.
    eapply IHns in H2 as (q0 & hw).
    exists q0. eapply strip_step; eassumption.
Qed.

(** The structural congruence is transitive. *)

Lemma fw_eq_trans `{LtsOba A L} : Transitive fw_eq.
Proof.
  intros p q t.
  intros heq1 heq2 p2 t2 hwp hwt.
  edestruct (lts_oba_mo_strip q.1) as (q2 & hwq).
  destruct (heq1 p2 q2 hwp hwq) as (heq3 & heq4).
  destruct (heq2 q2 t2 hwq hwt) as (heq5 & heq6).
  split. etrans; naive_solver. multiset_solver.
Qed.

Global Hint Resolve fw_eq_trans:mdb.

(** Congruence is an Equivalence. *)

Lemma fw_eq_equiv `{LtsOba A L} : Equivalence fw_eq.
Proof. constructor; eauto with mdb. Qed.

Global Hint Resolve fw_eq_equiv:mdb.

(** LtsObaFw : lts_fw instance. *)

Definition lts_fw_stable `{Label L, Lts A L} (p : A * mb L) (ℓ : Act L) : Prop :=
  match ℓ with
  | ActExt (ActIn a) => False
  | τ => lts_stable p.1 τ /\ forall a, a ∈ p.2 -> p.1 ↛[ActIn a]
  | ActExt (ActOut a) => a ∉ lts_outputs p.1 /\ a ∉ p.2
  end.

Lemma lts_com_ex_xs `{Lts A L} (p : A) (m : list L) :
  {a | a ∈ m /\ ¬ lts_stable p (ActExt $ ActIn a) }
  + {forall a, a ∈ m -> lts_stable p (ActExt $ ActIn a)}.
Proof.
  induction m.
  - right. inversion 1.
  - destruct IHm as [(b & mem & hnst)|].
    + left. exists b. set_solver.
    + destruct (lts_stable_decidable p (ActExt $ ActIn a)).
      ++ right. intros. inversion H1; set_solver.
      ++ left. exists a. set_solver.
Qed.

Lemma lts_com_ex `{Lts A L} (p : A) (m : mb L) :
  {a | a ∈ m /\ ¬ lts_stable p (ActExt $ ActIn a)}
  + {forall a, a ∈ m -> lts_stable p (ActExt $ ActIn a)}.
Proof.
  destruct (lts_com_ex_xs p (elements m)) as [(b & mem & hnst)|].
  + left. exists b. split. now eapply gmultiset_elem_of_elements. eassumption.
  + right. intros. eapply gmultiset_elem_of_elements in H1. eauto.
Qed.


Lemma lts_com_ex_dec_ `{Countable A} (m1 : gmultiset A) (m2 : gmultiset A) :
  {a | m2 = {[+ a +]} ⊎ m1} + {forall a, m2 ≠ {[+ a +]} ⊎ m1}.
Proof.
  set (d := m2 ∖ m1).
  set (xs := elements d).
  destruct xs eqn:eq.
  + eapply gmultiset_elements_empty_iff in eq. right. multiset_solver.
  + destruct l.
    ++ eapply gmultiset_elements_singleton_inv in eq.
       destruct (decide (m1 ⊆ m2)).
       +++ left. exists a.
           replace ({[+ a +]} ⊎ m1) with (m1 ⊎ {[+ a +]}) by multiset_solver.
           rewrite <- eq. multiset_solver.
       +++ right. multiset_solver.
    ++ right. intros b eq'.
       replace xs with (elements (m2 ∖ m1)) in eq; eauto.
       rewrite eq' in eq.
       replace (({[+ b +]} ⊎ m1) ∖ m1) with ({[+ b +]} ⊎ (m1 ∖ m1)) in eq by multiset_solver.
       rewrite gmultiset_difference_diag in eq.
       replace ({[+ b +]} ⊎ ∅) with ({[+ b +]} : gmultiset A) in eq.
       rewrite gmultiset_elements_singleton in eq.
       multiset_solver.
       multiset_solver.
Qed.

Lemma decision_lts_fw_step_input `{Lts A L} p1 m1 p2 m2 a :
  Decision (lts_fw_step (p1, m1) (ActExt $ ActIn a) (p2, m2)).
Proof.
  destruct (lts_step_decidable p1 (ActExt (ActIn a)) p2).
  + destruct (decide (m1 = m2)); subst.
    ++ left. eauto with mdb.
    ++ destruct (decide (m2 = {[+ a +]} ⊎ m1)); subst.
       +++ destruct (decide (p1 = p2)); subst.
           left. eauto with mdb.
           right. inversion 1; subst; contradiction.
       +++ right. inversion 1; subst; contradiction.
  + destruct (decide (m2 = {[+ a +]} ⊎ m1)); subst.
    +++ destruct (decide (p1 = p2)); subst.
        left. eauto with mdb.
        right. inversion 1; subst; contradiction.
    +++ right. inversion 1; subst; contradiction.
Qed.

Lemma decision_lts_fw_step_tau `{Lts A L} p1 m1 p2 m2 :
  Decision (lts_fw_step (p1, m1) τ (p2, m2)).
Proof.
  destruct (decide (m1 = m2)).
  + destruct (lts_step_decidable p1 τ p2).
    ++ subst. left. eauto with mdb.
    ++ right. inversion 1; subst; try contradiction; eapply gmultiset_neq_s; eauto.
  + destruct (lts_com_ex_dec_ m2 m1) as [(a, eq)| neq]; subst.
    ++ destruct (lts_step_decidable p1 (ActExt $ ActIn a) p2).
       left. subst. eauto with mdb.
       right. inversion 1; subst.
       +++ contradiction.
       +++ cut (a = a0); intros; subst; [|eapply gmultiset_mono]; eauto.
    ++ right. inversion 1; multiset_solver.
Qed.

Lemma decision_lts_fw_step_output `{Lts A L} p1 m1 p2 m2 a :
  Decision (lts_fw_step (p1, m1) (ActExt $ ActOut a) (p2, m2)).
Proof.
  destruct (decide (m1 = {[+ a +]} ⊎ m2)); subst.
  destruct (decide (p1 = p2)); subst.
  + left. eauto with mdb.
  + right. inversion 1; subst.
    ++ symmetry in H7. now eapply gmultiset_neq_s in H7.
    ++ contradiction.
  + destruct (lts_step_decidable p1 (ActExt $ ActOut a) p2).
    ++ destruct (decide (m1 = m2)); subst.
       left. eauto with mdb.
       right. inversion 1; subst; contradiction.
    ++ right. inversion 1; subst; contradiction.
Qed.


#[global] Program Instance MbLts {L : Type} `{Lts A L} : Lts (A * mb L) L :=
  {|
    lts_step p α q  := lts_fw_step p α q ;
    lts_stable p := lts_fw_stable p;
    lts_outputs p := lts_outputs p.1 ∪ dom p.2;
  |}.
Next Obligation.
Proof.
  intros ? ? ? ? (p1, m1) α (p2, m2).
  destruct α as [[|]|].
  - eapply decision_lts_fw_step_input.
  - eapply decision_lts_fw_step_output.
  - eapply decision_lts_fw_step_tau.
Qed.
Next Obligation.
  intros. destruct p1 as (p1, m1), p2 as (p2, m2).
  eapply elem_of_union. inversion H1; subst; simpl in *.
  - left. eapply lts_outputs_spec1. eassumption.
  - right. eapply gmultiset_elem_of_dom. multiset_solver.
Qed.
Next Obligation.
  intros.
  destruct p1 as (p1, m1). simpl in *.
  destruct (decide (x ∈ lts_outputs p1)).
  eapply lts_outputs_spec2 in e as (p0 & l0).
  exists (p0, m1). eauto with mdb.
  destruct (decide (x ∈ dom m1)).
  exists (p1, m1 ∖ {[+ x +]}).
  eapply gmultiset_elem_of_dom, gmultiset_disj_union_difference' in e.
  rewrite e at 1. eapply lts_fw_out_mb.
  exfalso. eapply elem_of_union in H1. destruct H1; eauto.
Qed.
Next Obligation.
  intros. simpl in *. destruct α as [[|]|].
  - right. simpl. intro. now exfalso.
  - simpl. destruct (decide (a ∈ p.2)).
    + right. intro. destruct H1. contradiction.
    + destruct (decide (a ∈ lts_outputs p.1)).
      ++ right. destruct 1. contradiction.
      ++ left. split; eassumption.
  - destruct p as (p, m); simpl in *;
      destruct (decide (lts_stable p τ)); simpl in *; firstorder.
    destruct (lts_com_ex p m) as [(b & mem & hnst)|].
    right. set_solver.
    left. set_solver.
Qed.
Next Obligation.
  intros ? ? ? ? (p, m) [[a|a]|] hnst.
  - exists (p, {[+ a +]} ⊎ m). eauto with mdb.
  - destruct (decide (a ∈ m)).
    eapply gmultiset_disj_union_difference' in e.
    exists (p, m ∖ {[+ a +]}). rewrite e at 1. eauto with mdb.
    destruct (decide (a ∈ lts_outputs p)).
    eapply lts_outputs_spec2 in e as (q & l). eauto with mdb.
    exfalso. now eapply hnst.
  - destruct (decide (lts_stable p τ)).
    destruct (lts_com_ex p m) as [(b & mem & hnst')|].
    + eapply lts_stable_spec1 in hnst' as (p' & l').
      eapply gmultiset_disj_union_difference' in mem.
      exists (p', m ∖ {[+ b +]}). rewrite mem at 1.
      eauto with mdb.
    + exfalso. now eapply hnst.
    + eapply lts_stable_spec1 in n as (p' & l'). eauto with mdb.
Qed.
Next Obligation.
  intros ? ? ? ? (p, m) [[a|a]|] ((p2,m2), l) hst; simpl in hst; eauto.
  inversion l; subst.
  - eapply lts_outputs_spec1 in H4. naive_solver.
  - multiset_solver.
  - destruct hst as (hstp & hstm).
    inversion l; subst.
    + eapply lts_stable_spec2 in hstp; eauto.
    + set (hsti := hstm a ltac:(multiset_solver)).
      eapply lts_stable_spec2 in hsti; eauto.
Qed.

Definition lts_fw_sc `{LtsOba A L} (p : A * mb L) α (q : A * mb L) :=
  exists r, lts_fw_step p α r /\ r ≐ q.

Notation "p ⟶≐ q" := (lts_fw_sc p τ q) (at level 90, format "p  ⟶≐  q").
Notation "p ⟶≐{ α } q" := (lts_fw_sc p α q) (at level 90, format "p  ⟶≐{ α }  q").
Notation "p ⟶≐[ μ ] q" := (lts_fw_sc p (ActExt μ) q) (at level 90, format "p  ⟶≐[ μ ]  q").

Lemma strip_retract_act `{LtsOba A L}
  {p q m t α} : p ⟿{m} q -> q ⟶{α} t -> exists r t', p ⟶{α} r /\ r ⟿{m} t' /\ t ⋍ t'.
Proof.
  intros. induction H2; eauto.
  exists t, t. repeat split; eauto. constructor. reflexivity.
  eapply IHstrip in H3 as (r & t' & l & hwo & heq).
  edestruct (lts_oba_output_commutativity H2 l) as (u & l1 & (r' & lr' & heqr')).
  edestruct (strip_eq_sim_ex hwo _ heqr') as (t0 & hwo0 & heq0).
  exists u, t0. repeat split; eauto. eapply strip_step; eassumption.
  etrans. eassumption. now symmetry.
Qed.

Lemma strip_delay_inp `{LtsOba A L} {p q m t a} :
  p ⟿{m} q -> p ⟶[ActIn a] t -> exists r, q ⟶[ActIn a] r.
Proof.
  intros. revert t H3.
  induction H2; eauto; intros.
  assert (neq : ActIn a ≠ ActOut a0) by now inversion 1.
  edestruct (lts_oba_output_confluence neq H2 H4) as (r & l1 & l2). eauto.
Qed.

Lemma strip_delay_inp3 `{LtsOba A L} {p q m t a} :
  p ⟿{m} q -> p ⟶[ActIn a] t -> exists r, t ⟿{m} r.
Proof.
  intros hwp hlp. revert p q t a hwp hlp.
  induction m using gmultiset_ind; intros.
  - inversion hwp.
    + subst. exists t. eapply strip_nil.
    + multiset_solver.
  - eapply strip_mem_ex in hwp as h0.
    destruct h0 as (e & hle).
    assert (neq : ActIn a ≠ ActOut x) by now inversion 1.
    edestruct (lts_oba_output_confluence neq hle hlp) as (u & l2 & l3).
    destruct l3 as (v & hlv & heqv).
    eapply strip_eq_step in hle as h1; eauto. destruct h1 as (r & hwr & heqr).
    destruct (IHm _ _ _ _ hwr l2) as (r0 & hwu).
    edestruct (strip_eq_sim_ex hwu v heqv) as (w & hww & heqw).
    exists w. eapply strip_step; eauto.
Qed.

Lemma strip_after `{LtsOba A L} {p q m} :
  strip p m q -> lts_oba_mo p = m ⊎ lts_oba_mo q.
Proof.
  intros hwp. revert p q hwp.
  induction m using gmultiset_ind; intros.
  - inversion hwp; multiset_solver.
  - eapply strip_mem_ex in hwp as h0.
    destruct h0 as (e & hle).
    eapply strip_eq_step in hle as h1; eauto. destruct h1 as (r & hwr & heqr).
    eapply lts_oba_mo_spec2 in hle.
    rewrite hle. eapply IHm in hwr.
    rewrite hwr.
    rewrite gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l.
    eapply lts_oba_mo_eq. eassumption.
Qed.

Lemma strip_aux1 `{LtsOba A L} {p q t m1 m2} :
  strip p m1 t -> strip p (m1 ⊎ m2) q -> exists r, strip t m2 r /\ r ⋍ q.
Proof.
  intros hwp1 hwp. revert q m2 hwp.
  dependent induction hwp1; intros.
  - rewrite gmultiset_disj_union_left_id in hwp.
    exists q. split. eassumption. reflexivity.
  - rewrite <- gmultiset_disj_union_assoc in hwp.
    eapply strip_eq_step in hwp as (r1 & hwr1 & heqr1); eauto.
    destruct (IHhwp1 _ _ hwr1) as (u & hwp3 & hequ).
    exists u. split. eassumption. transitivity r1; eauto.
Qed.

Lemma strip_delay_inp4 `{LtsOba A L} {p q t a} :
  p ⟶[ActIn a] t -> strip t (lts_oba_mo p) q -> exists r, strip p (lts_oba_mo p) r /\ r ⟶⋍[ActIn a] q.
Proof.
  intros hlp hwt.
  remember (lts_oba_mo p) as pmo.
  revert p q t a hwt hlp Heqpmo.
  induction pmo using gmultiset_ind; intros.
  - inversion hwt.
    + subst. exists p. split. eapply strip_nil. exists q. split. assumption. reflexivity.
    + multiset_solver.
  - assert (mem : x ∈ lts_oba_mo p) by multiset_solver.
    eapply lts_oba_mo_spec1, lts_outputs_spec2 in mem as (p1 & hlp1).
    assert (neq : ActIn a ≠ ActOut x) by now inversion 1.
    edestruct (lts_oba_output_confluence neq hlp1 hlp) as (u & l2 & l3).
    destruct l3 as (u' & hlu & hequ).
    eapply strip_eq_step in hlu as h1; eauto. destruct h1 as (r & hwr & heqr).
    edestruct (strip_eq_sim_ex hwr u (symmetry hequ)) as (r' & hwu & heqr').
    eapply lts_oba_mo_spec2 in hlp1 as hmop.
    assert (hmoeq : pmo = lts_oba_mo p1) by multiset_solver.
    destruct (IHpmo p1 r' u a hwu l2 hmoeq) as (pt & hwpt & hlpt).
    exists pt. split. eapply strip_step; eauto.
    destruct hlpt as (r0 & hlpt & heqt0).
    exists r0. split. eassumption.
    transitivity r'. eassumption.
    transitivity r. eassumption. eassumption.
Qed.

Notation "p ▷ m" := (p, m) (at level 60).

Lemma fw_eq_input_simulation `{LtsOba A L} {p q mp mq a q'} :
  p ▷ mp ≐ q ▷ mq -> q ⟶[ActIn a] q' ->
  exists p', p ⟶[ActIn a] p' /\ p' ▷ mp ≐ q' ▷ mq.
Proof.
  intros heq hlq.
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (heq p0 q0) as (heqp0 & heqm); eauto. simpl in *.
  edestruct (strip_delay_inp3 hwq hlq) as (q1 & hwq').
  edestruct (strip_delay_inp4 hlq hwq') as (q2 & hwq2 & hlq2).
  assert (q0 ⋍ q2) by (eapply strip_m_deter; eauto).
  destruct hlq2 as (r & hlr & heqr).
  edestruct (eq_spec p0 r (ActExt $ ActIn a)) as (p0' & hlp0' & heqp0').
  exists q2. split; eauto. transitivity q0; eauto.
  edestruct (strip_retract_act hwp hlp0' ) as (p' & p1 & wp' & hwp' & heqp').
  exists p'. split. eassumption.
  intros pt qt hwpt hwqt. simpl in *.
  assert (heq1 : lts_oba_mo p' = lts_oba_mo p ⊎ lts_oba_mo p1).
  eapply strip_after; eauto.
  assert (heq2 : lts_oba_mo q' = lts_oba_mo q ⊎ lts_oba_mo q1).
  eapply strip_after; eauto.
  assert (heq3 : lts_oba_mo p1 = lts_oba_mo q1).
  eapply lts_oba_mo_eq. transitivity p0'. now symmetry. transitivity r; eauto.
  split.
  - rewrite heq1 in hwpt.
    rewrite heq2 in hwqt.
    eapply strip_aux1 in hwpt as (pt' & hwp1 & heqpt'); eauto.
    eapply strip_aux1 in hwqt as (qt' & hwq1 & heqqt'); eauto.
    transitivity pt'. now symmetry.
    transitivity qt'.
    assert (heq0 : p1 ⋍ q1).
    transitivity p0'. now symmetry. transitivity r; eauto.
    eapply (strip_eq_sim heq0); eauto.
    now rewrite heq3. assumption.
  - multiset_solver.
Qed.

Lemma strip_delay_tau `{LtsOba A L} {p q m t} :
  p ⟿{m} q -> p ⟶ t ->
  (exists a r, p ⟶[ActOut a] r /\ r ⟶⋍[ActIn a] t) \/ (exists r w, q ⟶ r /\ t ⟿{m} w /\ w ⋍ r).
Proof.
  intros hr hl. revert t hl.
  induction hr; intros.
  + right. exists t, t. repeat split; eauto. eapply strip_nil. reflexivity.
  + edestruct (lts_oba_output_tau H2 hl) as [(r & l1 & l2)|].
    ++ eapply IHhr in l1 as [(b & r' & l3 & l4) |(u, (w, (hu & hw & heq)))].
       +++ edestruct (lts_oba_output_commutativity H2 l3) as (z & l6 & l7).
           left. exists b, z. split. assumption.
           destruct l7 as (t0 & hlt0 & eqt0).
           destruct l4 as (t1 & hlt1 & eqt1).
           destruct (eq_spec t0 t1 (ActExt $ ActIn b)) as (t2 & hlt2 & eqt2); eauto.
           edestruct (lts_oba_output_commutativity hlt0 hlt2) as (w & lw1 & lw2).
           exists w. split. assumption.
           destruct l2 as (v1 & hlv1 & heqv1).
           destruct lw2 as (u1 & hlu1 & hequ1).
           eapply lts_oba_output_deter_inv; try eassumption.
           etrans. eassumption.
           etrans. eassumption.
           etrans. eassumption.
           now symmetry.
       +++ right.
           destruct l2 as (r' & hlr' & heqr').
           destruct (strip_eq_sim_ex hw _ heqr') as (w' & hww' & heqw').
           exists u, w'. repeat split. assumption. eapply strip_step; eauto.
           etrans; eauto.
    ++ destruct H3 as (r & hlr & heq).
       left. exists a. exists p2. split; eauto. exists r. eauto.
Qed.

Lemma lts_fw_eq_spec_left_tau `{LtsObaFB A L} p q q' mp mq :
  p ▷ mp ≐ q ▷ mq -> q ⟶ q' -> p ▷ mp ⟶≐ q' ▷ mq.
Proof.
  intros heq l.
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (heq p0 q0) as (heq0 & heqm0); eauto. simpl in *.
  destruct (strip_delay_tau hwq l) as
    [(a & q1 & l1 & l2) | (qt & q1 & hltqt & hwq1 & heq1)].
  - destruct l2 as (q'' & hlq1 & heq'').
    edestruct (lts_oba_output_commutativity l1 hlq1) as (q2 & hlq & hlq2).
    edestruct (fw_eq_input_simulation heq hlq) as (p2 & hlp_inp & heqp2).
    assert (mem : a ∈ lts_oba_mo p ⊎ mp)
      by (eapply lts_outputs_spec1, lts_oba_mo_spec1 in l1; multiset_solver).
    eapply gmultiset_elem_of_disj_union in mem as [hleft | hright].
    + assert {p1 | p ⟶[ActOut a] p1} as (p1 & hlp_out)
          by now eapply lts_outputs_spec2, lts_oba_mo_spec1.
      (* p ->[!a] p1 *)
      assert (neq : ActIn a ≠ ActOut a) by now inversion 1.
      edestruct (lts_oba_output_confluence neq hlp_out hlp_inp)
        as (p'' & hlp1 & hlp2).
      (* p1 ->[a] p''   p2 ->[!a] p'' *)
      destruct (lts_oba_fb_feedback hlp_out hlp1)
        as (p' & hlp_tau & heqp').
      exists (p', mp). split. eauto with mdb.
      intros pt qt hwpt hwqt. simpl in *.
      edestruct (lts_oba_mo_strip p2) as (pt' & hwpt').
      edestruct (lts_oba_mo_strip q2) as (qt' & hwqt').
      edestruct heqp2 as (heqpqt' & heqmpt'); eauto; simpl in *.
      destruct hlp2 as (p''' & hlp2 & heqp'').
      assert (heqm1 : lts_oba_mo p2 = {[+ a +]} ⊎ lts_oba_mo p').
      replace (lts_oba_mo p') with (lts_oba_mo p''').
      now eapply lts_oba_mo_spec2.
      eapply lts_oba_mo_eq. etrans. eapply heqp''. now symmetry.
      destruct hlq2 as (q''' & hlq2 & heqq'').
      assert (heqm2 : lts_oba_mo q2 = {[+ a +]} ⊎ lts_oba_mo q').
      replace (lts_oba_mo q') with (lts_oba_mo q''').
      now eapply lts_oba_mo_spec2.
      eapply lts_oba_mo_eq. etrans. eapply heqq''. now symmetry.
      split.
      ++ rewrite heqm1 in hwpt'. rewrite heqm2 in hwqt'.
         eapply strip_eq_step in hwpt' as (pr & hwpr & heqpr); eauto.
         eapply strip_eq_step in hwqt' as (qr & hwqr & heqqr); eauto.
         etrans. eapply strip_eq_sim.
         etrans. eapply heqp'. symmetry.
         eapply heqp''. eassumption. eassumption.
         symmetry.
         etrans. eapply strip_eq_sim.
         etrans. symmetry. eapply heq''. symmetry.
         eapply heqq''. eassumption. eassumption.
         symmetry. etrans. apply heqpr. etrans. apply heqpqt'. now symmetry.
      ++ multiset_solver.
    + exists (p2, mp ∖ {[+ a +]}). split.
      ++ eapply gmultiset_disj_union_difference' in hright.
         rewrite hright at 1. eauto with mdb.
      ++ destruct hlq2 as (q''' & hlq2 & heqq'').
         assert (heqm2 : lts_oba_mo q2 = {[+ a +]} ⊎ lts_oba_mo q').
         replace (lts_oba_mo q') with (lts_oba_mo q''').
         now eapply lts_oba_mo_spec2.
         eapply lts_oba_mo_eq. etrans. eapply heqq''. now symmetry.
         intros pt qt hwpt hwqt. simpl in *.
         assert (heq' : q''' ⋍ q') by (etrans; eassumption).
         edestruct (strip_eq_sim_ex hwqt _ heq') as (qt' & hwqt' & heqqt').
         edestruct heqp2 as (heqpqt' & heqmpt'); eauto; simpl in *.
         rewrite heqm2. eapply strip_step; eassumption.
         split.
         symmetry. etrans. symmetry. eapply heqqt'. now symmetry.
         eapply (gmultiset_disj_union_inj_1 {[+ a +]}).
         replace ({[+ a +]} ⊎ (lts_oba_mo q' ⊎ mq)) with
           ({[+ a +]} ⊎ lts_oba_mo q' ⊎ mq) by multiset_solver.
         rewrite <- heqm2.
         rewrite <- heqmpt'.
         rewrite gmultiset_disj_union_assoc.
         replace ({[+ a +]} ⊎ lts_oba_mo p2 ⊎ mp ∖ {[+ a +]})
           with (lts_oba_mo p2 ⊎ {[+ a +]} ⊎ mp ∖ {[+ a +]})
           by multiset_solver.
         rewrite <- gmultiset_disj_union_assoc.
         eapply gmultiset_disj_union_difference' in hright.
         now rewrite <- hright at 1.
  - edestruct (eq_spec p0 qt τ) as (pt & hlpt & heqpt); eauto.
    edestruct (strip_retract_act hwp hlpt )
      as (p' & p1 & wp' & hwp' & heqpr0).
    exists (p', mp). split. eauto with mdb.
    intros pr qr hwpr hwqr. simpl in *.
    assert (heqr1 : lts_oba_mo p' = lts_oba_mo p ⊎ lts_oba_mo p1).
    eapply strip_after; eauto.
    assert (heqr2 : lts_oba_mo q' = lts_oba_mo q ⊎ lts_oba_mo q1).
    eapply strip_after; eauto.
    assert (heqr3 : lts_oba_mo p1 = lts_oba_mo q1).
    eapply lts_oba_mo_eq.
    transitivity pt. now symmetry. transitivity qt; eauto. now symmetry.
    split.
    + rewrite heqr1 in hwpr. rewrite heqr2 in hwqr.
      eapply strip_aux1 in hwpr as (pt' & hwp1' & heqpt'); eauto.
      eapply strip_aux1 in hwqr as (qt' & hwq1' & heqqt'); eauto.
      transitivity pt'. now symmetry. transitivity qt'.
      assert (heqr0 : p1 ⋍ q1).
      transitivity pt. now symmetry.
      transitivity qt; eauto. now symmetry.
      eapply (strip_eq_sim heqr0); eauto.
      now rewrite heqr3. assumption.
    + multiset_solver.
Qed.

Lemma lts_fw_eq_spec_left_output `{LtsObaFB A L} p q q' mp mq a :
  p ▷ mp ≐ q ▷ mq -> q ⟶[ActOut a] q' -> p ▷ mp ⟶≐[ActOut a] q' ▷ mq.
Proof.
  intros heq l.
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  set (h0 := lts_outputs_spec1 _ _ _ l).
  eapply lts_oba_mo_spec1 in h0.
  edestruct (heq p0 q0) as (heq0 & heqm0); eauto. simpl in *.
  assert (h1 : a ∈ lts_oba_mo p ⊎ mp) by multiset_solver.
  eapply gmultiset_elem_of_disj_union in h1 as [hleft|hright].
  ++ eapply gmultiset_disj_union_difference' in hleft as heqmop.
     eapply lts_oba_mo_spec1, lts_outputs_spec2 in hleft as (p' & hl').
     rewrite heqmop in hwp.
     eapply strip_eq_step in hwp as (p0' & hwop0' & heqp0'); eauto.
     set (h2 := lts_outputs_spec1 _ _ _ l). eapply lts_oba_mo_spec1 in h2.
     eapply gmultiset_disj_union_difference' in h2 as heqmoq.
     rewrite heqmoq in hwq.
     eapply strip_eq_step in hwq as (q0' & hwoq0' & heqq0'); eauto.
     exists (p', mp). split; eauto with mdb.
     intros pt qt hwopt hwoqt. simpl in *.
     eapply lts_oba_mo_spec2 in hl', l.
     assert (heq1 : lts_oba_mo q' = lts_oba_mo q ∖ {[+ a +]})
       by multiset_solver.
     assert (heq2 : lts_oba_mo p' = lts_oba_mo p ∖ {[+ a +]})
       by multiset_solver.
     rewrite heq1 in hwoqt. rewrite heq2 in hwopt.
     split.
     +++ transitivity p0'. eapply strip_m_deter; eauto.
         transitivity p0. assumption.
         transitivity q0. assumption.
         transitivity q0'. now symmetry.
         eapply strip_m_deter; eauto.
     +++ multiset_solver.
  ++ eapply gmultiset_disj_union_difference' in hright.
     rewrite hright.
     eexists. split. eauto with mdb.
     intros pt qt hwopt hwoqt. simpl in *.
     split.
     +++ edestruct (heq pt q0) as (heq1 & heqm1); eauto. simpl in *.
         transitivity q0. assumption.
         eapply gmultiset_disj_union_difference' in h0 as heqmoq.
         rewrite heqmoq in hwq.
         eapply strip_eq_step in hwq as (q0' & hwoq0' & heqq0'); eauto.
         transitivity q0'. now symmetry.
         eapply lts_oba_mo_spec2 in l.
         assert (heq2 : lts_oba_mo q' = lts_oba_mo q ∖ {[+ a +]})
           by multiset_solver.
         rewrite heq2 in hwoqt. eapply strip_m_deter; eauto.
     +++ eapply lts_oba_mo_spec2 in l. multiset_solver.
Qed.

Lemma lts_fw_eq_spec_left_input `{LtsObaFB A L} p q q' mp mq a :
  p ▷ mp ≐ q ▷ mq -> q ⟶[ActIn a] q' -> p ▷ mp ⟶≐[ActIn a] q' ▷ mq.
Proof.
  intros heq l.
  edestruct (fw_eq_input_simulation heq l) as (p' & hl' & heq').
  exists (p' ▷ mp). eauto with mdb.
Qed.

Lemma lts_fw_eq_spec_left `{LtsObaFB A L} p q q' α mp mq :
  p ▷ mp ≐ q ▷ mq -> q ⟶{α} q' -> p ▷ mp ⟶≐{α} q' ▷ mq.
Proof.
  intros heq l. destruct α as [[a|a]|].
  + eapply lts_fw_eq_spec_left_input; eauto.
  + eapply lts_fw_eq_spec_left_output; eauto.
  + eapply lts_fw_eq_spec_left_tau; eauto.
Qed.

Lemma lts_fw_eq_spec_right `{LtsObaFB A L} p q mp mq a :
  p ▷ mp ≐ q ▷ {[+ a +]} ⊎ mq -> p ▷ mp ⟶≐[ActOut a] (q, mq).
Proof.
  intros heq.
  destruct (decide (a ∈ mp)).
  + exists (p, mp ∖ {[+ a +]}). split.
    eapply gmultiset_disj_union_difference' in e. rewrite e at 1. eauto with mdb.
    intros p' q' hw1 hw2. simpl in *.
    edestruct (heq p' q'); eauto; simpl in *.
    split. eassumption.
    eapply gmultiset_disj_union_difference' in e.
    eapply (gmultiset_disj_union_inj_1 {[+ a +]}).
    symmetry.
    transitivity (lts_oba_mo q ⊎ ({[+ a +]} ⊎ mq)).
    rewrite 1 gmultiset_disj_union_comm.
    rewrite <- gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l. now rewrite 1 gmultiset_disj_union_comm.
    etrans. symmetry. eassumption.
    rewrite e at 1.
    rewrite 2 gmultiset_disj_union_assoc.
    symmetry.
    rewrite <- 1 gmultiset_disj_union_assoc.
    rewrite 1 gmultiset_disj_union_comm.
    rewrite <- 2 gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l.
    rewrite 1 gmultiset_disj_union_comm. reflexivity.
  + edestruct (lts_oba_mo_strip p) as (p' & hwp).
    assert (a ∈ lts_oba_mo p).
    edestruct (lts_oba_mo_strip q) as (q' & hwq).
    destruct (heq p' q' hwp hwq) as (heq' & heqmo). simpl in *.
    assert (a ∈ lts_oba_mo p ⊎ mp). rewrite heqmo. multiset_solver.
    eapply gmultiset_elem_of_disj_union in H3 as [hleft | hright]; multiset_solver.
    eapply lts_oba_mo_spec1, lts_outputs_spec2 in H3 as (p0 & hl0).
    exists (p0, mp). split. eauto with mdb.
    intros p1 q1 hw1 hw2. simpl in *. split.
    edestruct (heq p' q1); eauto; simpl in *.
    set (heqmo := lts_oba_mo_spec2 _ _ _ hl0).
    rewrite heqmo in hwp.
    eapply strip_eq_step in hwp as (p4 & hwo4 & heq4); eauto.
    set (h := strip_m_deter hw1 hwo4).
    etrans. eassumption. etrans; eassumption.
    set (heqmo := lts_oba_mo_spec2 _ _ _ hl0).
    edestruct (heq p' q1); eauto; simpl in *.
    rewrite heqmo in H4.
    replace (lts_oba_mo q ⊎ ({[+ a +]} ⊎ mq))
      with ({[+ a +]} ⊎ lts_oba_mo q ⊎ mq) in H4.
    eapply (gmultiset_disj_union_inj_1 ({[+ a +]})). multiset_solver.
    rewrite <- gmultiset_disj_union_assoc.
    rewrite gmultiset_disj_union_comm.
    rewrite <- gmultiset_disj_union_assoc.
    eapply gmultiset_eq_pop_l.
    now rewrite gmultiset_disj_union_comm.
Qed.

Lemma lts_fw_com_eq_spec `{LtsObaFB A L} p q q' mp mq a :
  p ▷ mp ≐ q ▷ {[+ a +]} ⊎ mq -> q ⟶[ActIn a] q' -> p ▷ mp ⟶≐ q' ▷ mq.
Proof.
  intros heq hl.
  edestruct (fw_eq_input_simulation heq hl) as (p' & hl' & heq').
  edestruct (lts_oba_mo_strip p) as (p0 & hwp).
  edestruct (lts_oba_mo_strip q) as (q0 & hwq).
  edestruct (heq p0 q0) as (heqp0 & heqm); eauto. simpl in *.
  assert (mem : a ∈ lts_oba_mo p ⊎ mp) by (now rewrite heqm; multiset_solver).
  eapply gmultiset_elem_of_disj_union in mem as [hleft | hright].
  - eapply lts_oba_mo_spec1, lts_outputs_spec2 in hleft as (p1 & hl1).
    assert (neq : ActIn a ≠ ActOut a) by now inversion 1.
    edestruct (lts_oba_output_confluence neq hl1 hl') as (p2 & hlp1 & hlp').
    edestruct (lts_oba_fb_feedback hl1 hlp1) as (p3 & hlp & heqp3).
    exists (p3, mp). split.
    + eauto with mdb.
    + intros ph qh hsph hsqh. simpl in *.
      destruct hlp' as (p2' & hlp2' & heqp2').
      destruct (lts_oba_mo_strip p') as (ph' & hsph').
      destruct (heq' ph' qh) as (heqt0 & heqmt); eauto. simpl in *.
      eapply lts_oba_mo_spec2 in hlp2' as hmeqp2'.
      assert (heqmu : lts_oba_mo p2' = lts_oba_mo p' ∖ {[+ a +]}) by multiset_solver.
      split.
      ++ eapply lts_outputs_spec1 in hlp2' as hmem.
         eapply lts_oba_mo_spec1, gmultiset_disj_union_difference' in hmem.
         rewrite hmem in hsph'.
         eapply strip_eq_step in hsph' as h1; eauto.
         destruct h1 as (p4 & hsu & heqp4).
         symmetry. transitivity ph'. now symmetry. transitivity p4. now symmetry.
         eapply (@strip_eq_sim _ _ _ _ _ _ p2' p3). transitivity p2. assumption. now symmetry.
         eassumption.
         replace (lts_oba_mo p' ∖ {[+ a +]}) with (lts_oba_mo p3). assumption.
         rewrite <- heqmu. eapply lts_oba_mo_eq. transitivity p2. assumption. now symmetry.
      ++ eapply (gmultiset_disj_union_inj_1 {[+ a +]}).
         replace (lts_oba_mo p3) with (lts_oba_mo p2'). rewrite heqmu.
         replace ({[+ a +]} ⊎ (lts_oba_mo q' ⊎ mq)) with (lts_oba_mo q' ⊎ ({[+ a +]} ⊎ mq)).
         rewrite <- heqmu. multiset_solver.
         rewrite 2 gmultiset_disj_union_assoc.
         replace (lts_oba_mo q' ⊎ {[+ a +]}) with ({[+ a +]} ⊎ lts_oba_mo q')
           by multiset_solver.
         reflexivity. eapply lts_oba_mo_eq.
         transitivity p2. assumption. now symmetry.
  - eapply gmultiset_disj_union_difference' in hright.
    exists (p' ▷ mp ∖ {[+ a +]}).
    split. rewrite hright at 1. eauto with mdb.
    intros pt qt hw1 hw2. simpl in *.
    edestruct (heq' pt qt) as (heqt0 & heqmt); eauto.
    split; simpl in *; eauto.
    eapply (gmultiset_disj_union_inj_1 {[+ a +]}).
    symmetry.
    transitivity (({[+ a +]} ⊎ lts_oba_mo q') ⊎ mq). multiset_solver.
    transitivity ((lts_oba_mo q' ⊎ {[+ a +]}) ⊎ mq). multiset_solver.
    transitivity (lts_oba_mo p' ⊎ mp).
    by now rewrite <- gmultiset_disj_union_assoc.
    symmetry.
    transitivity (lts_oba_mo p' ⊎ {[+ a +]} ⊎  mp ∖ {[+ a +]}). multiset_solver.
    rewrite <- gmultiset_disj_union_assoc.
    now replace (({[+ a +]} ⊎ mp ∖ {[+ a +]})) with mp.
Qed.

Lemma lts_fw_eq_spec `{LtsObaFB A L} p q t mp mq mt α :
  p ▷ mp ≐ t ▷ mt -> (t ▷ mt) ⟶{α} (q ▷ mq) -> p ▷ mp ⟶≐{α} q ▷ mq.
Proof.
  intros heq hl. inversion hl; subst.
  - eapply lts_fw_eq_spec_left; eauto.
  - eapply lts_fw_eq_spec_right; eauto.
  - exists (p, {[+ a +]} ⊎ mp). split.
    ++ eauto with mdb.
    ++ intros p1 q1 hw1 hw2. edestruct (heq p1 q1); multiset_solver.
  - eapply lts_fw_com_eq_spec; eauto.
Qed.

#[global] Program Instance MbLtsEq {L : Type} `{LtsObaFB A L} : LtsEq (A * mb L) L :=
  {| eq_rel := fw_eq |}.
Next Obligation. intros. eapply fw_eq_refl. Qed.
Next Obligation. intros. eapply fw_eq_symm; eauto. Qed.
Next Obligation. intros. eapply fw_eq_trans; eauto. Qed.
Next Obligation.
  intros ? ? ? ? ? ? ? (p, mp) (q, mq) α ((t, mt) & heq & hl).
  eapply lts_fw_eq_spec; eauto.
Qed.

#[global] Program Instance LtsMBOba `{LtsObaFB A L} : LtsOba (A * mb L) L :=
  {| lts_oba_mo p := lts_oba_mo p.1 ⊎ p.2 |}.
Next Obligation.
  intros; simpl in *.
  rewrite gmultiset_elem_of_disj_union, elem_of_union.
  now rewrite gmultiset_elem_of_dom, lts_oba_mo_spec1.
Qed.
Next Obligation.
  intros; simpl in *.
  inversion H3; subst; simpl in *.
  - eapply lts_oba_mo_spec2 in H4. multiset_solver.
  - rewrite gmultiset_disj_union_comm, <- gmultiset_disj_union_assoc.
    now replace (m ⊎ lts_oba_mo p0) with (lts_oba_mo p0 ⊎ m) by eapply gmultiset_disj_union_comm.
Qed.
Next Obligation.
  intros. destruct p as (p, mp), q as (q, mq), r as (r, mr).
  inversion H3; inversion H4; subst.
  - destruct (lts_oba_output_commutativity H8 H14) as (t & hlt0 & (r0 & hlr0 & heqr0)).
    exists (t, mr). split; simpl in *. eauto with mdb.
    exists (r0, mr). split. simpl in *. eauto with mdb.
    now eapply fw_eq_id_mb.
  - exists (p, mr). split; simpl in *. eauto with mdb.
    exists (r, mr). split. simpl in *. eauto with mdb. reflexivity.
  - exists (p, {[+ a0 +]} ⊎ mq). split; simpl in *. eauto with mdb.
    exists (r, {[+ a0 +]} ⊎ mq). split. simpl in *. eauto with mdb. reflexivity.
  - destruct (lts_oba_output_commutativity H8 H14) as (t & hlt0 & (r0 & hlr0 & heqr0)).
    exists (t, mr). split. simpl in *. eauto with mdb.
    exists (r0, mr). split. simpl in *. eauto with mdb.
    now eapply fw_eq_id_mb.
  - exists (r, {[+ a +]} ⊎ mr).
    split. simpl in *. eauto with mdb.
    exists (r, mr). split. simpl in *. eauto with mdb. reflexivity.
  - replace ({[+ a +]} ⊎ ({[+ a1 +]} ⊎ mr))
      with ({[+ a1 +]} ⊎ ({[+ a +]} ⊎ mr)) by multiset_solver.
    exists (r, {[+ a +]} ⊎ mr).
    split. simpl in *. eauto with mdb.
    exists (r, mr). split. simpl in *. eauto with mdb. reflexivity.
  - exists (r, {[+ a1 +]} ⊎ ({[+ a +]} ⊎ mq)).
    split. simpl in *. eauto with mdb.
    replace ({[+ a1 +]} ⊎ ({[+ a +]} ⊎ mq))
      with ({[+ a +]} ⊎ ({[+ a1 +]} ⊎ mq)) by multiset_solver.
    eexists. split. simpl in *. eauto with mdb. reflexivity.
  - replace ({[+ a +]} ⊎ ({[+ a1 +]} ⊎ mr))
      with ({[+ a1 +]} ⊎ ({[+ a +]} ⊎ mr)) by multiset_solver.
    eexists. split.  simpl in *. eauto with mdb.
    eexists. split.  simpl in *. eauto with mdb. reflexivity.
Qed.
Next Obligation.
  intros. destruct p as (p, mp), q1 as (q, mq), q2 as (r, mr).
  inversion H4; subst.
  - inversion H5; subst.
    + edestruct (lts_oba_output_confluence H3 H9 H10) as (t & hlt0 & (r0 & hlr0 & heqr0)).
      exists (t, mr). split; simpl in *. eauto with mdb.
      exists (r0, mr). split. simpl in *. eauto with mdb.
      now eapply fw_eq_id_mb.
    + exists (q, mr). split. simpl in *. eauto with mdb.
      exists (q, mr). split. simpl in *. eauto with mdb. reflexivity.
    + exists (q, {[+ a0 +]} ⊎ mq). split. simpl in *. eauto with mdb.
      exists (q,  {[+ a0 +]} ⊎ mq). split. simpl in *. eauto with mdb. reflexivity.
  - inversion H5; subst.
    + exists (r, mq). split; simpl in *. eauto with mdb.
      exists (r, mq). split. simpl in *. eauto with mdb. reflexivity.
    + assert (neq : a ≠ a0) by naive_solver.
      assert (a0 ∈ mq).
      assert (a0 ∈ {[+ a +]} ⊎ mq).
      rewrite <- H8; multiset_solver. multiset_solver.
      eapply gmultiset_disj_union_difference' in H6.
      rewrite H6.
      exists (r, mq ∖ {[+ a0 +]}). split.
      simpl in *. eauto with mdb.
      assert (a ∈ mr).
      assert (a ∈ {[+ a0 +]} ⊎ mr).
      rewrite H8; multiset_solver. multiset_solver.
      eapply gmultiset_disj_union_difference' in H7.
      assert (mq ∖ {[+ a0 +]} = mr ∖ {[+ a +]})%stdpp.
      eapply (gmultiset_disj_union_inj_1 {[+ a0 +]}).
      replace ({[+ a0 +]} ⊎ mq ∖ {[+ a0 +]}) with mq by eauto.
      eapply (gmultiset_disj_union_inj_1 {[+ a +]}).
      replace ({[+ a +]} ⊎ ({[+ a0 +]} ⊎ mr ∖ {[+ a +]}))
        with (({[+ a0 +]} ⊎ ({[+ a +]} ⊎ mr ∖ {[+ a +]}))) by multiset_solver.
      replace ({[+ a +]} ⊎ mr ∖ {[+ a +]}) with mr by eauto.
      now symmetry.
      rewrite H7. rewrite H9.
      eexists.
      split. simpl in *. eauto with mdb. reflexivity.
    + exists (r, {[+ a0 +]} ⊎ mq). split. simpl in *. eauto with mdb.
      replace ({[+ a0 +]} ⊎ ({[+ a +]} ⊎ mq)) with ({[+ a +]} ⊎ ({[+ a0 +]} ⊎ mq)) by multiset_solver.
      exists (r, ({[+ a0 +]} ⊎ mq)).
      split. simpl in *. eauto with mdb. reflexivity.
Qed.
Next Obligation.
Proof.
  intros ? ? ? ? ? ? ? (p1, m1) (p2, m2) (p3, m3) a l1 l2.
  inversion l1; subst.
  - inversion l2; subst.
    + edestruct (lts_oba_output_tau H6 H7) as
        [(t & hl1 & (t0 & hl0 & heq0)) | (t0 & hl0 & heq0)].
      left. exists (t, m3).
      split. simpl. eauto with mdb.
      exists (t0, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
      right. exists (t0, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
    + assert (neq : ActIn a0 ≠ ActOut a) by now inversion 1.
      edestruct (lts_oba_output_confluence neq H6 H7)
        as (t & hl1 & (t1 & hl2 & heq1)).
      left. exists (t, m3). split. simpl. eauto with mdb.
      exists (t1, m3). split. simpl. eauto with mdb.
      now eapply fw_eq_id_mb.
  - inversion l2; subst.
    + left. exists (p3, m2).
      split. simpl. eauto with mdb.
      exists (p3, m2). split. eapply lts_fw_out_mb. reflexivity.
    + destruct (decide (a0 = a)); subst.
      ++ right.
         eapply gmultiset_disj_union_inj_1 in H5. subst.
         exists (p3, m2). split. simpl. eauto with mdb. reflexivity.
      ++ left.
         assert (a ∈ m3).
         assert (a ∈ {[+ a0 +]} ⊎ m3).
         rewrite H5. multiset_solver.
         multiset_solver.
         assert (a0 ∈ m2).
         assert (a0 ∈ {[+ a +]} ⊎ m2).
         rewrite <- H5. multiset_solver. multiset_solver.
         eapply gmultiset_disj_union_difference' in H3, H4.
         exists (p3, m2 ∖ {[+ a0 +]}).
         split.
         rewrite H4 at 1. simpl. eauto with mdb.
         rewrite H3 at 1.
         assert (m3 ∖ {[+ a +]} = m2 ∖ {[+ a0 +]}).
         multiset_solver.
         rewrite <- H7. eexists. split.
         simpl. eauto with mdb. reflexivity.
Qed.
Next Obligation.
  intros.
  destruct p1 as (p1, mp1), p2 as (p2, mp2), p3 as (p3, mp3).
  intros p2' p3' hwp2 hwp3; simpl in *.
  inversion H3; subst.
  - inversion H4; subst.
    + eapply fw_eq_id_mb; eauto.
      eapply lts_oba_output_deter; eauto.
    + set (he1 := lts_oba_mo_spec2 _ _ _ H8).
      rewrite he1 in hwp3.
      eapply strip_eq_step in hwp3 as (p0 & hw0 & heq0); eauto. split.
      etrans. eapply strip_m_deter; eauto. eassumption.
      rewrite he1.
      rewrite gmultiset_disj_union_comm at 1.
      rewrite <- 2 gmultiset_disj_union_assoc.
      eapply gmultiset_eq_pop_l. multiset_solver.
  - inversion H4; subst.
    + set (he1 := lts_oba_mo_spec2 _ _ _ H8).
      rewrite he1 in hwp2.
      eapply strip_eq_step in hwp2 as (p0 & hw0 & heq0); eauto. split.
      etrans. symmetry. eassumption.
      eapply strip_m_deter; eauto.
      symmetry. rewrite he1.
      rewrite gmultiset_disj_union_comm at 1.
      rewrite <- 2 gmultiset_disj_union_assoc.
      eapply gmultiset_eq_pop_l. multiset_solver.
    + split.  eapply strip_m_deter; eauto. multiset_solver.
Qed.
Next Obligation.
  intros.
  destruct p1 as (p1, mp1), q1 as (q1, mq1), p2 as (p2, mp2), q2 as (q2, mq2).
  inversion H3; subst; intros p1' p2' hwp1 hwp2; simpl in *.
  - eapply lts_oba_mo_spec2 in H9 as hd1.
    edestruct (lts_oba_mo_strip q1) as (q1' & hwq1).
    inversion H4; subst.
    + edestruct (lts_oba_mo_strip q2) as (q2' & hwq2).
      edestruct (H5 q1' q2'); eauto; simpl in *.
      eapply lts_oba_mo_spec2 in H10 as hd2.
      split.
      ++ rewrite hd1 in hwp1. rewrite hd2 in hwp2.
         eapply strip_eq_step in hwp1, hwp2; eauto.
         destruct hwp1 as (t1 & hwq1' & heq1').
         destruct hwp2 as (t2 & hwq2' & heq2').
         set (heq1 := strip_m_deter hwq1 hwq1').
         set (heq2 := strip_m_deter hwq2 hwq2').
         transitivity t1. now symmetry.
         transitivity q1'. now symmetry.
         transitivity q2'. now symmetry.
         transitivity t2. now symmetry. eassumption.
      ++ multiset_solver.
    + edestruct (H5 q1' p2'); eauto; simpl in *.
      split.
      ++ rewrite hd1 in hwp1.
         eapply strip_eq_step in hwp1; eauto.
         destruct hwp1 as (t1 & hwq1' & heq1').
         set (heq1 := strip_m_deter hwq1 hwq1').
         transitivity t1. naive_solver.
         transitivity q1'; naive_solver.
      ++ rewrite hd1. symmetry.
         rewrite gmultiset_disj_union_comm at 1.
         rewrite <- 2 gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l. multiset_solver.
  - inversion H4; subst.
    + eapply lts_oba_mo_spec2 in H9 as hd1.
      edestruct (lts_oba_mo_strip q2) as (q2' & hwq2).
      edestruct (H5 p1' q2'); eauto; simpl in *.
      split.
      ++ rewrite hd1 in hwp2.
         eapply strip_eq_step in hwp2; eauto.
         destruct hwp2 as (t2 & hwq2' & heq2').
         set (heq1 := strip_m_deter hwq2 hwq2').
         transitivity q2'. naive_solver.
         transitivity t2; naive_solver.
      ++ rewrite hd1.
         rewrite gmultiset_disj_union_comm at 1.
         rewrite <- 2 gmultiset_disj_union_assoc.
         eapply gmultiset_eq_pop_l. multiset_solver.
    + edestruct (H5 p1' p2'); eauto; simpl in *.
      multiset_solver.
Qed.

#[global] Program Instance LtsMBObaFW `{LtsObaFB A L} : LtsObaFW (A * mb L) L.
Next Obligation.
  intros.
  destruct p1 as (p, m).
  exists (p, {[+ a +]} ⊎ m). split; eauto with mdb.
  eapply lts_fw_inp_mb.
  eapply lts_fw_out_mb.
Qed.
Next Obligation.
  intros.
  destruct p1 as (p1, m1), p2 as (p2, m2), p3 as (p3, m3).
  inversion H3; subst.
  + inversion H4; subst.
    ++ left. destruct (lts_oba_fb_feedback H8 H9) as (t & l & heq).
       exists (t, m3). split. eapply lts_fw_p. eassumption.
       now eapply fw_eq_id_mb.
    ++ right. simpl. unfold fw_eq.
       intros. simpl in *. set (heq := lts_oba_mo_spec2 _ _ _ H8).
       rewrite heq in H5. rewrite heq. split.
       +++ destruct (strip_mem_ex H5) as (e & l).
           destruct (strip_eq_step H5 e l) as (t & hwo & heq'); eauto.
           set (h := lts_oba_output_deter H8 l).
           etrans. symmetry. eassumption.
           symmetry. eapply strip_eq_sim; eassumption.
       +++ rewrite <- gmultiset_disj_union_assoc.
           rewrite gmultiset_disj_union_comm.
           rewrite <- gmultiset_disj_union_assoc.
           eapply gmultiset_eq_pop_l.
           now rewrite gmultiset_disj_union_comm.
  + inversion H4; subst.
    ++ left. exists (p3, m3). split. simpl. eauto with mdb. reflexivity.
    ++ right. reflexivity.
Qed.

(** Derivatives. *)

Definition lts_fw_input_set `{FiniteLts A L} p (m : mb L) a :=
  (p, {[+ a +]} ⊎ m) :: map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ ActIn a))).

Definition lts_fw_output_set `{FiniteLts A L} (p : A) (m : mb L) a :=
  let ps := map (fun p => (proj1_sig p, m)) (enum $ dsig (lts_step p (ActExt $ ActOut a))) in
  if (decide (a ∈ m)) then (p, m ∖ {[+ a +]}) :: ps else ps.

Definition lts_fw_com_fin `{FiniteLts A L} (p : A) (m : list L) : list (L * list A) :=
  map (fun a => (a, map proj1_sig (enum $ dsig (lts_step p (ActExt $ ActIn a))))) m.

Definition lts_fw_tau_set `{FiniteLts A L} (p : A) (m : mb L) : list (A * mb L) :=
  let xs := map (fun p => (proj1_sig p, m)) (enum $ dsig (fun q => p ⟶ q)) in
  let ys :=
    concat (map
              (fun '(a, ps) => map (fun p => (p, m ∖ {[+ a +]})) ps)
              (lts_fw_com_fin p (elements m)
      )) in
  xs ++ ys.

Lemma lts_fw_input_set_spec1 `{FiniteLts A L} p1 m1 p2 m2 a :
  lts_fw_step (p1, m1) (ActExt (ActIn a)) (p2, m2) ->
  (p2, m2) ∈ lts_fw_input_set p1 m1 a.
Proof.
  intros l.
  inversion l; subst.
  + right. eapply elem_of_list_fmap.
    exists (dexist p2 H5). split. reflexivity. eapply elem_of_enum.
  + left.
Qed.

Lemma lts_fw_output_set_spec1 `{FiniteLts A L} p1 m1 p2 m2 a :
  lts_fw_step (p1, m1) (ActExt (ActOut a)) (p2, m2) ->
  (p2, m2) ∈ lts_fw_output_set p1 m1 a.
Proof.
  intros l.
  inversion l; subst.
  + unfold lts_fw_output_set.
    destruct (decide (a ∈ m2)).
    right. eapply elem_of_list_fmap.
    exists (dexist p2 H5). split. reflexivity. eapply elem_of_enum.
    eapply elem_of_list_fmap.
    exists (dexist p2 H5). split. reflexivity. eapply elem_of_enum.
  + unfold lts_fw_output_set.
    destruct (decide (a ∈ {[+ a +]} ⊎ m2)).
    ++ replace (({[+ a +]} ⊎ m2) ∖ {[+ a +]}) with m2 by multiset_solver.
       left.
    ++ multiset_solver.
Qed.

Lemma lts_fw_tau_set_spec1 `{FiniteLts A L} p1 m1 p2 m2 :
  lts_fw_step (p1, m1) τ (p2, m2) ->
  (p2, m2) ∈ lts_fw_tau_set p1 m1.
Proof.
  intros l.
  inversion l; subst.
  + eapply elem_of_app. left.
    eapply elem_of_list_fmap.
    exists (dexist p2 H5). split. reflexivity. eapply elem_of_enum.
  + eapply elem_of_app. right.
    eapply elem_of_list_In.
    eapply in_concat.
    exists (map (fun p => (p, m2))
         (map proj1_sig (enum $ dsig (lts_step p1 (ActExt $ ActIn a))))
      ).
    split.
    eapply elem_of_list_In.
    eapply elem_of_list_fmap.
    exists (a, map proj1_sig (enum $ dsig (lts_step p1 (ActExt $ ActIn a)))).
    split.
    now replace (({[+ a +]} ⊎ m2) ∖ {[+ a +]}) with m2 by multiset_solver.
    eapply elem_of_list_fmap.
    exists a. split; eauto.
    eapply elem_of_Permutation_proper.
    eapply (gmultiset_elements_disj_union {[+ a +]} m2).
    rewrite gmultiset_elements_singleton. set_solver.
    eapply elem_of_list_In.
    eapply elem_of_list_fmap.
    eexists.  split. reflexivity.
    eapply elem_of_list_fmap.
    exists (dexist p2 H5). split. reflexivity. eapply elem_of_enum.
Qed.

#[global] Program Instance LtsMBFinite {L : Type} `{FiniteLts A L} : FiniteLts (A * mb L) L.
Next Obligation.
  intros ? ? ? ? ? (p, m) [[a|a]|].
  - eapply (in_list_finite (lts_fw_input_set p m a)). simpl in *.
    intros (p0, m0) h%bool_decide_unpack.
    now eapply lts_fw_input_set_spec1.
  - eapply (in_list_finite (lts_fw_output_set p m a));
    intros (p0, m0) h%bool_decide_unpack.
    now eapply lts_fw_output_set_spec1.
  - eapply (in_list_finite (lts_fw_tau_set p m)).
    intros (p0, m0) h%bool_decide_unpack.
    now eapply lts_fw_tau_set_spec1.
Qed.

Definition lts_tau_set_from_pset_spec1 `{Countable A, Lts A L}
  (ps : gset A) (qs : gset A) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟶ q.

Definition lts_tau_set_from_pset_spec2 `{Countable A, Lts A L}
  (ps : gset A) (qs : gset A) :=
  forall p q, p ∈ ps -> p ⟶ q -> q ∈ qs.

Definition lts_tau_set_from_pset_spec `{Countable A, Lts A L}
  (ps : gset A) (qs : gset A) :=
  lts_tau_set_from_pset_spec1 ps qs /\ lts_tau_set_from_pset_spec2 ps qs.

Definition lts_tau_set_from_pset `{FiniteLts A L} (ps : gset A) : gset A :=
  ⋃ (map (fun p => list_to_set (lts_tau_set p)) (elements ps)).

Lemma lts_tau_set_from_pset_ispec `{Lts A L, !FiniteLts A L}
  (ps : gset A) :
  lts_tau_set_from_pset_spec ps (lts_tau_set_from_pset ps).
Proof.
  split.
  - intros a mem.
    eapply elem_of_union_list in mem as (xs & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (p & heq0 & mem1).
    subst.  eapply elem_of_list_to_set in mem2.
    eapply lts_tau_set_spec in mem2. multiset_solver.
  - intros p q mem l.
    eapply elem_of_union_list.
    exists (list_to_set (lts_tau_set p)).
    split.
    + multiset_solver.
    + eapply lts_tau_set_spec in l. multiset_solver.
Qed.

Fixpoint wt_set_nil `{FiniteLts A L} (p : A) (t : terminate p) : gset A :=
  let '(tstep _ f) := t in
  let k q := wt_set_nil (`q) (f (`q) (proj2_dsig q)) in
  {[ p ]} ∪ ⋃ map k (enum $ dsig (lts_step p τ)).

Lemma wt_set_nil_spec1 `{FiniteLts A L} p q (tp : terminate p) :
  q ∈ wt_set_nil p tp -> p ⟹ q.
Proof.
  case tp. induction tp.
  intros t mem. simpl in mem.
  eapply elem_of_union in mem as [here | there].
  + eapply elem_of_singleton_1 in here. subst. eauto with mdb.
  + eapply elem_of_union_list in there as (ps & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (r & mem1 & eq). subst.
    eapply wt_tau; [|destruct (t (`r) (proj2_dsig r)) eqn:eqn0].
    ++ eapply (proj2_dsig r).
    ++ eapply H3. eapply (proj2_dsig r). eassumption.
Qed.

Lemma wt_set_nil_spec2 `{FiniteLts A L} p q : forall (tp : terminate p), p ⟹ q -> q ∈ wt_set_nil p tp.
Proof.
  intros. revert tp. dependent induction H2; intros tp; destruct tp.
  + set_solver.
  + eapply elem_of_union. right.
    eapply elem_of_union_list.
    set (qr := dexist q l).
    exists (wt_set_nil (`qr) (t0 (`qr) (proj2_dsig qr))).
    split. eapply elem_of_list_fmap.
    exists qr. split. reflexivity.
    eapply elem_of_enum. simpl.
    eapply IHwt. eauto.
Qed.

Lemma wt_nil_set_dec `{FiniteLts A L} p (ht : p ⤓) : forall q, Decision (p ⟹ q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set_nil p ht)).
  - left. eapply (wt_set_nil_spec1 _ _ _ e).
  - right. intro wt. eapply n. now eapply wt_set_nil_spec2.
Qed.

Lemma wt_set_nil_fin_aux `{FiniteLts A L}
  (p : A) (ht : terminate p) (d : ∀ q, Decision (p ⟹ q)) : Finite (dsig (fun q => p ⟹ q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set_nil p ht))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_nil_spec2.
Qed.

Definition wt_set_nil_fin `{FiniteLts A L}
  (p : A) (ht : p ⤓) : Finite (dsig (fun q => p ⟹ q)) :=
  wt_set_nil_fin_aux p ht (wt_nil_set_dec p ht).

Lemma wt_push_nil_left_lts `{Lts A L} {p q r μ} : p ⟹ q -> q ⟶[μ] r -> p ⟹{μ} r.
Proof. by intros w1 lts; dependent induction w1; eauto with mdb. Qed.

Definition wt_set_mu
  `{FiniteLts A L} (p : A)
  (μ : ExtAct L) (s : trace L) (hcnv : p ⇓ μ :: s) : gset A :=
  let ht := cnv_terminate p (μ :: s) hcnv in
  let ps0 := @enum (dsig (fun q => p ⟹ q)) _ (wt_set_nil_fin p ht) in
  let f p : list (dsig (lts_step p (ActExt μ))) := enum (dsig (lts_step p (ActExt μ))) in
  ⋃ map (fun t =>
           ⋃ map (fun r =>
                    let w := wt_push_nil_left_lts (proj2_dsig t) (proj2_dsig r) in
                    let hcnv := cnv_preserved_by_wt_act s p μ hcnv (`r) w in
                    let htr := cnv_terminate (`r) s hcnv in
                    let ts := @enum (dsig (fun q => (`r) ⟹ q)) _ (wt_set_nil_fin (`r) htr) in
                    list_to_set (map (fun t => (`t)) ts)
             ) (f (`t))
    ) ps0.

Lemma wt_set_mu_spec1 `{FiniteLts A L}
  (p q : A) (μ : ExtAct L) (s : trace L) (hcnv : p ⇓ μ :: s) :
  q ∈ wt_set_mu p μ s hcnv -> p ⟹{μ} q.
Proof.
  intros mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  eapply elem_of_union_list in mem2 as (g & mem3 & mem4).
  eapply elem_of_list_fmap in mem3 as ((u & hlts) & eq & mem3). subst.
  eapply elem_of_list_to_set, elem_of_list_fmap in mem4 as ((v & hw2) & eq & mem4). subst.
  eapply wt_push_nil_left. eapply bool_decide_unpack. eassumption.
  eapply wt_act. eapply bool_decide_unpack. eassumption.
  eapply bool_decide_unpack. eassumption.
Qed.

Lemma wt_set_mu_spec2 `{FiniteLts A L}
  (p q : A) (μ : ExtAct L) (s : trace L) (hcnv : p ⇓ μ :: s) :
  p ⟹{μ} q -> q ∈ wt_set_mu p μ s hcnv.
Proof.
  intros w.
  eapply wt_decomp_one in w as (p0 & p1 & hw1 & hlts & hw2).
  eapply elem_of_union_list. eexists. split.
  eapply elem_of_list_fmap. exists (dexist p0 hw1). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_union_list. eexists. split.
  eapply elem_of_list_fmap. exists (dexist p1 hlts). split. reflexivity. eapply elem_of_enum.
  eapply elem_of_list_to_set, elem_of_list_fmap.
  exists (dexist q hw2). split. reflexivity. eapply elem_of_enum.
Qed.

Lemma wt_mu_set_dec `{FiniteLts A L} p μ s (hcnv : p ⇓ μ :: s) : forall q, Decision (p ⟹{μ} q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set_mu p μ s hcnv)).
  - left. eapply  (wt_set_mu_spec1 p q μ s hcnv e).
  - right. intro wt. eapply n. now eapply wt_set_mu_spec2.
Qed.

Lemma wt_mu_set_fin_aux `{FiniteLts A L}
  (p : A) μ s (hcnv : p ⇓ μ :: s) (d : ∀ q, Decision (p ⟹{μ} q)) : Finite (dsig (fun q => p ⟹{μ} q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set_mu p μ s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_mu_spec2.
Qed.

Definition wt_set_mu_fin `{FiniteLts A L}
  (p : A) μ s (hcnv : p ⇓ μ :: s) : Finite (dsig (fun q => p ⟹{μ} q)) :=
  wt_mu_set_fin_aux p μ s hcnv (wt_mu_set_dec p μ s hcnv).

Fixpoint wt_set `{FiniteLts A L} (p : A) (s : trace L) (hcnv : cnv p s) : gset A :=
  match s as s0 return cnv p s0 -> gset A with
  | [] =>
      fun _ => wt_set_nil p (cnv_terminate p _ hcnv)
  | μ :: s' =>
      fun f =>
        let ts := @enum (dsig (fun q => p ⟹{μ} q)) _ (wt_set_mu_fin p μ s' f) in
        ⋃ map (fun t =>
                 let hcnv := cnv_preserved_by_wt_act s' p μ f (`t) (proj2_dsig t) in
                 wt_set (`t) s' hcnv
          ) ts
  end hcnv.

Lemma wt_set_spec1 `{FiniteLts A L}
  (p q : A) (s : trace L) (hcnv : p ⇓ s) :
  q ∈ wt_set p s hcnv -> p ⟹[s] q.
Proof.
  revert p q hcnv. induction s; intros p q hcnv mem; simpl in *.
  - eapply wt_set_nil_spec1. eassumption.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    eapply wt_push_left. eapply bool_decide_unpack. eassumption.
    eapply IHs. eassumption.
Defined.

Lemma wt_set_spec2 `{FiniteLts A L}
  (p q : A) (s : trace L) (hcnv : p ⇓ s) :
  p ⟹[s] q -> q ∈ wt_set p s hcnv.
Proof.
  revert p q hcnv.
  induction s as [|μ s']; intros p q hcnv w; simpl in *.
  - eapply wt_set_nil_spec2. eauto with mdb.
  - eapply wt_pop in w as (t & w1 & w2).
    eapply elem_of_union_list.
    eexists. split.
    + eapply elem_of_list_fmap.
      exists (dexist t w1). now split; [|eapply elem_of_enum].
    + now eapply IHs'.
Defined.

Lemma wt_set_dec `{FiniteLts A L} p s (hcnv : p ⇓ s) : forall q, Decision (p ⟹[s] q).
Proof.
  intro q.
  destruct (decide (q ∈ wt_set p s hcnv)).
  - left. eapply  (wt_set_spec1 p q s hcnv e).
  - right. intro wt. eapply n. now eapply wt_set_spec2.
Qed.

Lemma wt_set_fin_aux `{FiniteLts A L}
  (p : A) s (hcnv : p ⇓ s) (d : ∀ q, Decision (p ⟹[s] q)) : Finite (dsig (fun q => p ⟹[s] q)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_set p s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_set_spec2.
Qed.

Definition wt_set_fin `{FiniteLts A L}
  (p : A) s (hcnv : p ⇓ s) : Finite (dsig (fun q => p ⟹[s] q)) :=
  wt_set_fin_aux p s hcnv (wt_set_dec p s hcnv).

Fixpoint wt_nil_stable_set `{FiniteLts A L} (p : A) (ht : p ⤓) : gset A :=
  match lts_stable_decidable p τ with
  | left  _ => {[ p ]}
  | right _ =>
      let '(tstep _ f) := ht in
      let k p := wt_nil_stable_set (`p) (f (`p) (proj2_dsig p)) in
      ⋃ map k (enum (dsig (fun q => p ⟶ q)))
  end.

Lemma wt_nil_stable_set_spec1 `{FiniteLts A L}
  (p q : A) (ht : p ⤓) :
  q ∈ wt_nil_stable_set p ht -> p ⟹ q /\ q ↛.
Proof.
  case ht. induction ht.
  intros ht mem.
  simpl in mem.
  case (lts_stable_decidable p τ) in mem.
  - eapply elem_of_singleton_1 in mem. subst. eauto with mdb.
  - eapply elem_of_union_list in mem as (g & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
    simpl in mem2. case (ht t (proj2_dsig (t ↾ hw1))) eqn:eq.
    edestruct (H3 t). now eapply bool_decide_unpack. eassumption.
    split; eauto with mdb. eapply wt_tau. eapply bool_decide_unpack.
    eassumption. eassumption.
Qed.

Lemma wt_nil_stable_set_spec2 `{FiniteLts A L}
  (p q : A) (ht : p ⤓) :
  (p ⟹ q /\ q ↛) -> q ∈ wt_nil_stable_set p ht.
Proof.
  intros (hw & hst). dependent induction hw; case ht; induction ht; intros ht; simpl.
  - case (lts_stable_decidable p τ); set_solver.
  - case (lts_stable_decidable p τ); intro hst'.
    + exfalso. eapply (lts_stable_spec2 p τ); eauto.
    + eapply elem_of_union_list.
      eexists. split. eapply elem_of_list_fmap.
      exists (dexist q l). split. reflexivity. eapply elem_of_enum. eapply IHhw; eauto.
Qed.

Lemma wt_nil_stable_set_dec `{FiniteLts A L} p (ht : p ⤓) : forall q, Decision (p ⟹ q /\ q ↛).
Proof.
  intro q.
  destruct (decide (q ∈ wt_nil_stable_set p ht)).
  - left. eapply (wt_nil_stable_set_spec1 p q ht e).
  - right. intro wt. eapply n. now eapply wt_nil_stable_set_spec2.
Qed.

Lemma wt_nil_stable_set_fin_aux `{FiniteLts A L}
  (p : A) (ht : p ⤓) (d : ∀ q, Decision (p ⟹ q /\ q ↛)) : Finite (dsig (fun q => p ⟹ q /\ q ↛)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_nil_stable_set p ht))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_nil_stable_set_spec2.
Qed.

Definition wt_nil_stable_set_fin `{FiniteLts A L}
  (p : A) (ht : p ⤓) : Finite (dsig (fun q => p ⟹ q /\ q ↛)) :=
  wt_nil_stable_set_fin_aux p ht (wt_nil_stable_set_dec p ht).

Lemma cnv_wt_s_terminate `{Lts A L}
  (p q : A) s (hcnv : p ⇓ s) : p ⟹[s] q -> q ⤓.
Proof. eapply cnv_iff_prefix_terminate; eauto. Qed.

Definition wt_stable_set `{FiniteLts A L} (p : A) s (hcnv : p ⇓ s) : gset A :=
  let ps := @enum (dsig (fun q => p ⟹[s] q)) _ (wt_set_fin p s hcnv) in
  let k t := wt_nil_stable_set (`t) (cnv_wt_s_terminate p (`t) s hcnv (proj2_dsig t)) in
  ⋃ map k ps.

Lemma wt_stable_set_spec1 `{FiniteLts A L}
  (p q : A) s (hcnv : p ⇓ s) :
  q ∈ wt_stable_set p s hcnv -> p ⟹[s] q /\ q ↛.
Proof.
  intro mem.
  eapply elem_of_union_list in mem as (g & mem1 & mem2).
  eapply elem_of_list_fmap in mem1 as ((t & hw1) & eq & mem1). subst.
  simpl in mem2.
  eapply wt_nil_stable_set_spec1 in mem2.
  split. eapply wt_push_nil_right. eapply bool_decide_unpack. eassumption. firstorder.
  firstorder.
Qed.

Lemma wt_stable_set_spec2 `{FiniteLts A L}
  (p q : A) s (hcnv : p ⇓ s) :
  (p ⟹[s] q /\ q ↛) -> q ∈ wt_stable_set p s hcnv.
Proof.
  intros (hw & hst).
  eapply elem_of_union_list.
  eexists. split. eapply elem_of_list_fmap.
  exists (dexist q hw). split. reflexivity. eapply elem_of_enum.
  simpl. eapply wt_nil_stable_set_spec2. eauto with mdb.
Qed.

Lemma wt_stable_set_fin_aux `{FiniteLts A L}
  (p : A) s (hcnv : p ⇓ s) (d : ∀ q, Decision (p ⟹[s] q /\ q ↛)) : Finite (dsig (fun q => p ⟹[s] q /\ q ↛)).
Proof.
  unfold dsig.
  eapply (in_list_finite (elements (wt_stable_set p s hcnv))).
  intros q Htrans%bool_decide_unpack.
  now eapply elem_of_elements, wt_stable_set_spec2.
Qed.


Lemma wt_stable_set_dec `{FiniteLts A L} p s (hcnv : p ⇓ s) : forall q, Decision (p ⟹[s] q /\ q ↛).
Proof.
  intro q.
  destruct (decide (q ∈ wt_stable_set p s hcnv)).
  - left. eapply (wt_stable_set_spec1 p q s hcnv e).
  - right. intro wt. eapply n. now eapply wt_stable_set_spec2.
Qed.

Definition wt_stable_set_fin `{FiniteLts A L}
  (p : A) s (hcnv : p ⇓ s) : Finite (dsig (fun q => p ⟹[s] q /\ q ↛)) :=
  wt_stable_set_fin_aux p s hcnv (wt_stable_set_dec p s hcnv).

Lemma wt_nil_set_stable `{FiniteLts A L} p hcnv :
  lts_stable p τ -> wt_set p [] hcnv = {[ p ]}.
Proof.
  intros hst.
  eapply leibniz_equiv.
  intro q. split.
  - intro mem.
    eapply wt_set_spec1 in mem.
    inversion mem; subst.
    + set_solver.
    + exfalso. eapply lts_stable_spec2; eauto.
  - intro mem. eapply wt_set_spec2. replace q with p.
    eauto with mdb. set_solver.
Qed.

Lemma wt_stable_set_stable_singleton `{FiniteLts A L} p hcnv :
  lts_stable p τ -> wt_stable_set p [] hcnv = {[ p ]}.
Proof.
  intro hst.
  eapply leibniz_equiv.
  intro q. split; intro mem.
  - eapply wt_stable_set_spec1 in mem as (w & hst').
    inversion w; subst. set_solver. exfalso. eapply lts_stable_spec2; eauto.
  - eapply elem_of_singleton_1 in mem. subst.
    eapply wt_stable_set_spec2. split; eauto with mdb.
Qed.

Fixpoint wt_s_set_from_pset_xs `{Lts A L, !FiniteLts A L}
  (ps : list A) s (hcnv : forall p, p ∈ ps -> p ⇓ s) : gset A :=
  match ps as ps0 return (forall p, p ∈ ps0 -> p ⇓ s) -> gset A with
  | [] => fun _ => ∅
  | p :: ps' =>
      fun ha =>
        let pr := ha p (elem_of_list_here p ps') in
        let ys := wt_set p s pr in
        let ha' := fun q mem => ha q (elem_of_list_further q p ps' mem) in
        ys ∪ wt_s_set_from_pset_xs ps' s ha'
  end hcnv.

Definition wt_set_from_pset_spec1_xs `{FiniteLts A L}
  (ps : list A) (s : trace L) (qs : gset A) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹[s] q.

Definition wt_set_from_pset_spec2_xs `{FiniteLts A L}
  (ps : list A) (s : trace L) (qs : gset A) :=
  forall p q, p ∈ ps -> p ⟹[s] q -> q ∈ qs.

Definition wt_set_from_pset_spec_xs `{FiniteLts A L}
  (ps : list A) (s : trace L) (qs : gset A) :=
  wt_set_from_pset_spec1_xs ps s qs /\ wt_set_from_pset_spec2_xs ps s qs.

Lemma wt_s_set_from_pset_xs_ispec `{Lts A L, !FiniteLts A L}
  (ps : list A) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  wt_set_from_pset_spec_xs ps s (wt_s_set_from_pset_xs ps s hcnv).
Proof.
  split.
  - induction ps as [|p ps].
    intros p mem. set_solver.
    intros p' mem. simpl in *.
    eapply elem_of_union in mem as [hl|hr].
    exists p. split.
    set_solver. now eapply wt_set_spec1 in hl.
    eapply IHps in hr as (p0 & mem & hwp0).
    exists p0. repeat split; set_solver.
  - induction ps as [|p ps].
    + intros p'. set_solver.
    + intros p' q mem hwp'.
      eapply elem_of_union.
      inversion mem; subst.
      ++ left. eapply wt_set_spec2; eauto.
      ++ right. eapply IHps in hwp'; eauto.
Qed.

Lemma lift_cnv_elements `{Lts A L, !FiniteLts A L}
  (ps : gset A) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  forall p, p ∈ (elements ps) -> p ⇓ s.
Proof.
  intros p mem.
  eapply hcnv. now eapply elem_of_elements.
Qed.

Definition wt_s_set_from_pset `{Lts A L, !FiniteLts A L}
  (ps : gset A) s (hcnv : forall p, p ∈ ps -> p ⇓ s) : gset A :=
  wt_s_set_from_pset_xs (elements ps) s (lift_cnv_elements ps s hcnv).

Definition wt_set_from_pset_spec1 `{Countable A, Lts A L}
  (ps : gset A) (s : trace L) (qs : gset A) :=
  forall q, q ∈ qs -> exists p, p ∈ ps /\ p ⟹[s] q.

Definition wt_set_from_pset_spec2 `{FiniteLts A L}
  (ps : gset A) (s : trace L) (qs : gset A) :=
  forall p q, p ∈ ps -> p ⟹[s] q -> q ∈ qs.

Definition wt_set_from_pset_spec `{FiniteLts A L}
  (ps : gset A) (s : trace L) (qs : gset A) :=
  wt_set_from_pset_spec1 ps s qs /\ wt_set_from_pset_spec2 ps s qs.

Lemma wt_s_set_from_pset_ispec `{Lts A L, !FiniteLts A L}
  (ps : gset A) s (hcnv : forall p, p ∈ ps -> p ⇓ s) :
  wt_set_from_pset_spec ps s (wt_s_set_from_pset ps s hcnv).
Proof.
  split.
  - intros p mem.
    eapply wt_s_set_from_pset_xs_ispec in mem as (p' & mem & hwp').
    exists p'. split; set_solver.
  - intros p q mem hwp.
    eapply wt_s_set_from_pset_xs_ispec.
    eapply elem_of_elements; eassumption. eassumption.
Qed.
