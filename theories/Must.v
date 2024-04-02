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
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap.
From Must Require Import TransitionSystems.

Class Good (A L : Type) (good : A -> Prop) `{Lts A L, !LtsEq A L} := {
    good_decidable e : Decision (good e);
    good_preserved_by_eq p q : good p -> p ⋍ q -> good q;
    good_preserved_by_lts_output p q a : p ⟶[ActOut a] q -> good p -> good q;
    good_preserved_by_lts_output_converse p q a : p ⟶[ActOut a] q -> good q -> good p;
}.

Lemma ungood_preserved_by_lts_output `{LtsOba A L, !Good A L good} p q a :
  p ⟶[ActOut a] q -> ~ good p -> ~ good q.
Proof.
  intros l1 hp hq.
  eapply hp. eapply good_preserved_by_lts_output_converse; eauto with mdb.
Qed.

Lemma ungood_preserved_by_wt_output `{LtsOba A L, !Good A L good} r1 r2 s :
  are_outputs s -> r1 ↛ -> ~ good r1 -> r1 ⟹[s] r2 -> ~ good r2.
Proof.
  intros s_spec hst hng hw.
  induction hw; eauto.
  - eapply lts_stable_spec2 in hst. now exfalso. eauto.
  - destruct μ as [a|a]. inversion s_spec; subst.
    + inversion H4. inversion H2.
    + inversion s_spec; subst.
      eapply IHhw. eassumption.
      eapply stable_tau_preserved_by_lts_output; eauto.
      eapply ungood_preserved_by_lts_output; eauto.
Qed.

Inductive must_sts `{Sts (A * B), good : B -> Prop}
  (p : A) (e : B) : Prop :=
| m_sts_now : good e -> must_sts p e
| m_sts_step
    (nh : ¬ good e)
    (nst : ¬ sts_stable (p, e))
    (l : forall p' e', sts_step (p, e) (p', e') -> must_sts p' e')
  : must_sts p e
.

Global Hint Constructors must_sts:mdb.

Inductive must `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good} (p : A) (e : B) : Prop :=
| m_now : good e -> must p e
| m_step
    (nh : ¬ good e)
    (ex : ∃ t, parallel_step (p, e) τ t)
    (pt : forall p', p ⟶ p' -> must p' e)
    (et : forall e', e ⟶ e' -> must p e')
    (com : forall p' e' μ, e ⟶[μ] e' -> p ⟶[co μ] p' -> must p' e')
  : must p e
.

Global Hint Constructors must:mdb.

Lemma must_sts_iff_must
  `{Lts A L, !Lts B L, !LtsEq B L, !Good B L good} (p : A) (e : B) :
  @must_sts A B _ good p e <-> must p e.
Proof.
  split.
  - intro hm. dependent induction hm; eauto with mdb.
    eapply m_step; eauto with mdb.
    + eapply sts_stable_spec1 in nst as ((p', e') & hl).
      exists (p', e'). now simpl in hl.
    + simpl in *; eauto with mdb.
    + simpl in *; eauto with mdb.
    + intros p' e' μ hl1 hl2.
      eapply H1. simpl.
      eapply (ParSync (ActExt (co μ)) (ActExt μ)); eauto.
      destruct μ; simpl; eauto.
  - intro hm. dependent induction hm; eauto with mdb.
    eapply m_sts_step; eauto with mdb.
    + eapply sts_stable_spec2.
      destruct (decide (sts_stable (p, e))).
      ++ exfalso.
         destruct ex as ((p', e'), hl).
         eapply sts_stable_spec2 in s; eauto.
         exists (p', e'). now simpl.
      ++ now eapply sts_stable_spec1 in n.
    + intros p' e' hl.
      inversion hl; subst; eauto with mdb.
      destruct α1 as [[a|a]|]; destruct α2 as [[b|b]|];
        inversion eq; subst; eauto with mdb.
Qed.

Definition ctx_pre `{Lts A L, !Lts C L, ! Lts B L, ! LtsEq B L, !Good B L good} (p : A) (q : C) :=
  forall (e : B), must p e -> must q e.

Global Hint Unfold ctx_pre: mdb.

Notation "p ⊑ q" := (ctx_pre p q) (at level 70).

Definition bhv_pre_cond1 `{Lts A L, Lts B L} (p : A) (q : B) := forall s, p ⇓ s -> q ⇓ s.

Notation "p ≼₁ q" := (bhv_pre_cond1 p q) (at level 70).

Definition bhv_pre_cond2 `{@Lts A L HL, @Lts B L HL} (p : A) (q : B) :=
  forall s q',
    p ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    ∃ p', p ⟹[s] p' /\ p' ↛ /\ lts_outputs p' ⊆ lts_outputs q'.

Notation "p ≼₂ q" := (bhv_pre_cond2 p q) (at level 70).

Definition bhv_pre `{@Lts A L HL, @Lts B L HL} (p : A) (q : B) := p ≼₁ q /\ p ≼₂ q.

Notation "p ≼ q" := (bhv_pre p q) (at level 70).

Lemma must_eq_client `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good} :
  forall (p : A) (q r : B), q ⋍ r -> must p q -> must p r.
Proof.
  intros p q r heq hm.
  revert r heq.
  dependent induction hm; intros.
  - apply m_now. eapply good_preserved_by_eq; eauto.
  - apply m_step; eauto with mdb.
    + intro rh. eapply nh. eapply good_preserved_by_eq; eauto with mdb.
      now symmetry.
    + destruct ex as (t & l).
      inversion l; subst; eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec r b2 τ) as (t & l3 & l4); eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec r b2 α2) as (t & l3 & l4); eauto with mdb.
    + intros r' l.
      edestruct (eq_spec e r' τ) as (t & l3 & l4); eauto with mdb.
    + intros p' r' μ l__r l__p.
      edestruct (eq_spec e r' (ActExt μ)) as (e' & l__e' & eq'); eauto with mdb.
Qed.

Lemma must_eq_server `{Lts A L, ! Lts B L, ! LtsEq A L, ! LtsEq B L, !Good B L good} :
  forall (p q : A) (e : B), p ⋍ q -> must p e -> must q e.
Proof.
  intros p q e heq hm.
  revert q heq.
  dependent induction hm; intros.
  - now apply m_now.
  - apply m_step; eauto with mdb.
    + destruct ex as (t & l).
      inversion l; subst; eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec q a2 τ) as (t & l3 & l4); eauto with mdb.
      ++ symmetry in heq.
         edestruct (eq_spec q a2 α1) as (t & l3 & l4); eauto with mdb.
    + intros q' l.
      edestruct (eq_spec p q' τ) as (t & l3 & l4); eauto with mdb.
    + intros q' e' μ l__e l__q.
      edestruct (eq_spec p q' (ActExt (co μ))) as (p' & l' & heq'); eauto with mdb.
Qed.

Lemma must_preserved_by_lts_tau_srv `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good}
  (p1 p2 : A) (e : B) : must p1 e -> p1 ⟶ p2 -> must p2 e.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_preserved_by_lts_tau_clt `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good}
  (p : A) (e1 e2 : B) : must p e1 -> ¬ good e1 -> e1 ⟶ e2 -> must p e2.
Proof. by inversion 1; eauto with mdb. Qed.

Lemma must_terminate_ungood `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good}
  (p : A) (e : B) : must p e -> ¬ good e -> p ⤓.
Proof. intros hm. dependent induction hm; eauto with mdb. contradiction. Qed.

(** Must sets. *)

Section must_sets.

  (* https://arxiv.org/pdf/1612.03191.pdf *)

  Local Open Scope positive.

  Definition encode_act_ext `{Countable L} (act : ExtAct L) : positive :=
    match act with ActIn a => (encode a)~0 | ActOut a => (encode a)~1 end.

  Definition decode_act_ext `{Countable L} (p : positive) : option (ExtAct L) :=
    match p with 1 => None | p~0 => ActIn <$> decode p | p~1 => ActOut <$> decode p end.

  #[global] Program Instance act_ext_countable `{Countable A} : Countable (ExtAct A) :=
    {| encode := encode_act_ext; decode := decode_act_ext |}.
  Next Obligation. intros ? ? ? [x|y]; simpl; rewrite decode_encode; eauto. Qed.

  Definition MUST `{Lts A L} (p : A) (G : gset (ExtAct L)) :=
    forall p', p ⟹ p' -> exists μ p0, μ ∈ G /\ p' ⟹{μ} p0.

  Definition MUST__s `{FiniteLts A L} (ps : gset A) (G : gset (ExtAct L)) := forall p, p ∈ ps -> MUST p G.

  (* Residuals of a process p AFTER the execution of s. *)

  Definition AFTER `{FiniteLts A L} (p : A) (s : trace L) (hcnv : p ⇓ s) := wt_set p s hcnv.

  Definition bhv_pre_ms_cond2 `{@FiniteLts A L HL LtsA, @FiniteLts B L HL LtsB} (p : A) (q : B) :=
    forall s h1 h2 G, MUST__s (AFTER p s h1) G -> MUST__s (AFTER q s h2) G.

  Definition bhv_pre_ms `{@FiniteLts A L HL LtsA, @FiniteLts B L HL LtsB} (p : A) (q : B) :=
    p ≼₁ q /\ bhv_pre_ms_cond2 p q.

End must_sets.

Global Hint Unfold bhv_pre_ms:mdb.

Notation "p ≾₂ q" := (bhv_pre_ms_cond2 p q) (at level 70).

Notation "p ≾ q" := (bhv_pre_ms p q) (at level 70).

Section failure.

  Definition Failure `{FiniteLts A L} (p : A) (s : trace L) (G : gset (ExtAct L)) :=
    p ⇓ s -> exists p', p ⟹[s] p' /\ forall μ, μ ∈ G -> ¬ exists p0, p' ⟹{μ} p0.

  Definition fail_pre_ms_cond2 `{@FiniteLts A L HL LtsA, @FiniteLts B L HL LtsB} (p : A) (q : B) :=
    forall s G, Failure q s G -> Failure p s G.

  Definition fail_pre_ms `{@FiniteLts A L HL LtsA, @FiniteLts B L HL LtsB} (p : A) (q : B) :=
    p ≼₁ q /\ fail_pre_ms_cond2 p q.

End failure.

Notation "p ⋖ q" := (fail_pre_ms p q) (at level 70).
