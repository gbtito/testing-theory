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

From stdpp Require Import base decidable gmap.
Require Import ssreflect.
Require Import Coq.Program.Equality.

From stdpp Require Import finite.
From Must Require Import TransitionSystems Must Bar Completeness Soundness Lift.

(** Extensional definition of Convergence and its equivalence
    with the inductive definition. *)

Section convergence.

  Context `{Label L}.
  Context `{!Lts A L, !FiniteLts A L}.

  Definition terminate_extensional (p : A) : Prop :=
    forall η : max_exec_from p, exists n fex,
      mex_take_from n η = Some fex /\ lts_stable (fex_from_last fex) τ.

  #[global] Instance conv_bar : Bar A := {| bar_pred p := sts_stable p |}.

  Lemma terminate_intensional_coincide (p : A) :
    intensional_pred p ↔ terminate p.
  Proof.
    split.
    - intros H1. dependent induction H1.
      + rewrite /bar_pred /= in H0. constructor => q l.
        eapply lts_stable_spec2 in H0. contradiction. eauto.
      + constructor => q l. by eauto.
    - intros H1; induction H1.
      destruct (decide (sts_stable p)).
      + constructor 1; rewrite /bar_pred //=.
      + constructor 2 =>//.
  Qed.

  Lemma terminate_ext_pred_iff_terminate_extensional (p : A) :
    extensional_pred p <-> terminate_extensional p.
  Proof. split; intros Hme η; destruct (Hme η) as (?&?&?&?); naive_solver. Qed.

  (* ************************************************** *)

  Lemma terminate_extensional_iff_terminate (p : A) :
    terminate_extensional p <-> terminate p.
  Proof.
    rewrite <- terminate_ext_pred_iff_terminate_extensional.
    rewrite <- terminate_intensional_coincide.
    split.
    - eapply extensional_implies_intensional.
    - eapply intensional_implies_extensional.
  Qed.

  Inductive cnv_extensional : A -> trace L -> Prop :=
  | cnv_ext_nil p : terminate_extensional p -> cnv_extensional p []
  | cnv_ext_act p μ s :
    terminate_extensional p ->
    (forall q, p ⟹{μ} q -> cnv_extensional q s) ->
    cnv_extensional p (μ :: s).

  Lemma cnv_extensional_iff_terminate (p : A) s : cnv_extensional p s <-> cnv p s.
  Proof.
    revert p. induction s as [|μ s].
    - now split; inversion 1; subst; constructor; eapply terminate_extensional_iff_terminate.
    - split; inversion 1; subst; constructor.
      now apply terminate_extensional_iff_terminate.
      firstorder. now eapply terminate_extensional_iff_terminate.
      firstorder.
  Qed.
End convergence.

Section must_set_acc_set.
  Context `{LL : Label L}.
  Context `{LtsA : !Lts A L, !FiniteLts A L}.
  Context `{LtsR : !Lts R L, !FiniteLts R L}.

  Context `{@LtsObaFB A L LL LtsA LtsEqA LtsObaA}.
  Context `{@LtsObaFB R L LL LtsR LtsEqR LtsObaR}.

  (* fixme : use already defined *)
  Definition outputs_acc (p : A * mb L) s (h : p ⇓ s) : gset (ExtAct L) :=
    ⋃ map
      (fun p => set_map ActOut (lts_outputs p) : gset (ExtAct L))
      (elements (wt_stable_set p s h)).

  (* ************************************************** *)

  Lemma either_wperform_mu (p : A * mb L) μ :
    p ⤓ -> (exists q, p ⟹{μ} q) \/ ~ (exists q, p ⟹{μ} q).
  Proof.
    intro ht. induction ht.
    destruct (lts_stable_decidable p (ActExt μ)).
    - assert (∀ x, x ∈ enum (dsig (lts_step p τ)) -> (∃ q0, `x ⟹{μ} q0) \/ ~ (∃ q0, `x ⟹{μ} q0))
        by (intros (x & mem) _; set_solver).
      edestruct (exists_forall_in _ _ _ H3).
      eapply Exists_exists in H4 as ((q' & pr) & mem & (q0 & hw)).
      left. exists q0. eapply wt_tau; eauto. now eapply bool_decide_unpack.
      right. intros (q' & hw). inversion hw; subst.
      ++ contradict H4. intros n. rewrite Forall_forall in n.
         eapply (n (dexist q l0)). eapply elem_of_enum. eauto.
      ++ eapply (@lts_stable_spec2 (A * mb L)); eauto.
    - left. eapply lts_stable_spec1 in n as (q & l). eauto with mdb.
  Qed.

  Lemma either_wperform_mem (p : A * mb L) (G : gset (ExtAct L)) (ht : p ⤓) :
    (exists μ p', μ ∈ G /\ p ⟹{μ} p') \/ (forall μ p', μ ∈ G -> ~ p ⟹{μ} p').
  Proof.
    induction G using set_ind_L; [|destruct IHG, (either_wperform_mu p x)]; set_solver.
  Qed.

  Lemma either_wperform_mem_set (ps : gset (A * mb L)) (G : gset (ExtAct L)) (ht : forall p, p ∈ ps -> p ⤓) :
    (exists p', p' ∈ ps /\ forall μ p0, μ ∈ G -> ~ p' ⟹{μ} p0) \/ (forall p', p' ∈ ps -> exists μ p0, μ ∈ G /\ p' ⟹{μ} p0).
  Proof.
    induction ps using set_ind_L; [|destruct IHps, (either_wperform_mem x G)]; set_solver.
  Qed.

  Lemma either_MUST (p : A * mb L) (G : gset (ExtAct L)) (hcnv : p ⇓ []) : MUST p G \/ ~ MUST p G.
  Proof.
    destruct (either_wperform_mem_set (wt_set p [] hcnv) G).
    - intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
    - right. intro hm. destruct H1 as (p' & mem%wt_set_spec1%hm & nhw). set_solver.
    - left. intros p1 hw%(wt_set_spec2 _ p1 [] hcnv). set_solver.
  Qed.

  Lemma either_ex_nMUST_or_MUST (ps : gset (A * mb L)) G (ht : forall p, p ∈ ps -> p ⇓ []) :
    (exists p, p ∈ ps /\ ~ MUST p G) \/ (forall p, p ∈ ps -> MUST p G).
  Proof.
    induction ps using set_ind_L; [|edestruct IHps, (either_MUST x G)]; set_solver.
  Qed.

  Lemma either_MUST__s (ps : gset (A * mb L)) (G : gset (ExtAct L)) :
    (forall p, p ∈ ps -> p ⇓ []) -> MUST__s ps G \/ ~ MUST__s ps G.
  Proof.
    intros. edestruct (either_ex_nMUST_or_MUST ps G); eauto.
    right. intros hm. destruct H2 as (p0 & mem0%hm & hnm). contradiction.
  Qed.

  Lemma nMusts_ex (ps : gset (A * mb L)) G :
    (forall p, p ∈ ps -> p ⇓ []) -> ~ MUST__s ps G -> exists p, p ∈ ps /\ ~ MUST p G.
  Proof. intros. edestruct (either_ex_nMUST_or_MUST ps G); set_solver. Qed.

  Lemma nMust_ex (p : A * mb L) G (hcnv : p ⇓ []) (hnm : ~ MUST p G) :
    exists p', p ⟹ p' /\ forall μ p0, μ ∈ G -> ~ p' ⟹{μ} p0.
  Proof.
    destruct (either_wperform_mem_set (wt_set p [] hcnv) G).
    - intros p0 mem0%wt_set_spec1. eapply cnv_terminate, cnv_preserved_by_wt_nil; eauto.
    - destruct H1 as (p' & mem'%wt_set_spec1 & nhw). set_solver.
    - edestruct hnm. intros p' mem. eapply H1. eapply wt_set_spec2; eauto.
  Qed.

  Lemma nMusts_nMust (p : A * mb L) G (hcnv : p ⇓ []) (hnm : ~ MUST__s (wt_set p [] hcnv) G) : ¬ MUST p G.
  Proof.
    intro hm. eapply hnm. intros p' mem0%wt_set_spec1.
    intros r hw. eapply hm. eapply wt_push_nil_left; eassumption.
  Qed.

  Lemma nMust_out_acc_ex (p : A * mb L) pt G s hcnv :
    pt ∈ AFTER p s hcnv -> ~ MUST pt (outputs_acc p s hcnv ∖ G) ->
    exists p', pt ⟹ p' /\ p' ↛ /\ set_map ActOut (lts_outputs p') ⊆ G.
  Proof.
    intros mem%wt_set_spec1 hnm.
    eapply nMust_ex in hnm as (p' & hw' & nhw).
    assert (ht': p' ⤓)
      by (eapply (cnv_wt_s_terminate p p' s hcnv), wt_push_nil_right; eauto).
    eapply terminate_then_wt_stable in ht' as (p0 & hw0 & hst).
    exists p0. split. eapply wt_push_nil_left; eauto.
    split; eauto.
    intros μ mem_mu.
    assert (is_output μ) as (a & heq).
    eapply elem_of_map in mem_mu as (a & heq & mem2).
    exists a. assumption. subst.
    destruct (decide (ActOut a ∈ G)); eauto.
    assert (mem0 : ActOut a ∈ outputs_acc p s hcnv).
    eapply elem_of_union_list. eexists. split; eauto.
    eapply elem_of_list_fmap.
    exists p0. repeat split; eauto.
    eapply elem_of_elements, wt_stable_set_spec2; split; eauto.
    eapply wt_push_nil_right, wt_push_nil_right; eauto.
    exfalso.
    edestruct (lts_outputs_spec2 p0 a). set_solver.
    eapply (nhw $ ActOut a); eauto. set_solver.
    eapply wt_push_nil_left; eauto with mdb.
    constructor; eapply (cnv_wt_s_terminate p pt s hcnv); eauto.
  Qed.

  Lemma either_MUST_or_ex (p : A * mb L) G s hcnv :
    MUST__s (AFTER p s hcnv) (outputs_acc p s hcnv ∖ G)
    \/ (exists p', p ⟹[s] p' /\ p' ↛ /\ set_map ActOut (lts_outputs p') ⊆ G).
  Proof.
    assert (h1 : forall p0, p0 ∈ AFTER p s hcnv → p0 ⇓ []).
    intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
    eapply (wt_set_spec1 _ _ _ _ mem0).
    edestruct either_MUST__s; eauto. right.
    eapply nMusts_ex in H1 as (pt & mem & hnm); eauto.
    eapply nMust_out_acc_ex in hnm as (pt' & hw & hst & hsub); eauto.
    exists pt'. split; eauto. eapply wt_push_nil_right; eauto. now eapply wt_set_spec1 in mem.
  Qed.

  Lemma Must_out_acc_npre (p : A * mb L) (q q' : R * mb L) s hcnv :
    q ⇓ s -> q ⟹[s] q' -> q' ↛ ->
    MUST__s (AFTER p s hcnv) (outputs_acc p s hcnv ∖ set_map ActOut (lts_outputs q')) ->
    ~ p ≾₂ q.
  Proof.
    intros hcnv' hw hst hm pre2.
    set (G := outputs_acc p s hcnv ∖ set_map ActOut (lts_outputs q')).
    assert (exists μ t, μ ∈ G /\ q' ⟹{μ} t) as (μ & t & mem & hw').
    eapply (pre2 s hcnv hcnv'); eauto. eapply wt_set_spec2; eauto. eapply wt_nil.
    eapply elem_of_difference in mem as (mem & nmem).
    assert (is_output μ) as (a & heq).
    eapply elem_of_union_list in mem as (X & mem1 & mem2).
    eapply elem_of_list_fmap in mem1 as (r & heq & mem1). subst.
    eapply elem_of_map in mem2 as (a & heq & mem2). exists a. assumption.
    inversion hw'; subst.
    eapply lts_stable_spec2 in hst; eauto.
    eapply nmem. eapply lts_outputs_spec1 in l. set_solver.
  Qed.

  (* ************************************************** *)

  Lemma equivalence_bhv_acc_mst2 (p : A) (q : R) :
    (p, ∅) ≼₁ (q, ∅) -> (p, ∅) ≾₂ (q, ∅) <-> (p, ∅) ≼₂ (q, ∅).
  Proof.
    intro hpre1.
    split.
    - intro hpre2. intros s q' hcnv hw hst.
      edestruct (either_MUST_or_ex (p, ∅) (set_map ActOut (lts_outputs q')) s hcnv).
      + exfalso. eapply Must_out_acc_npre; eauto with mdb.
      + set_solver.
    - intro hpre2.
      intros s hcnv hcnv' G hm q' mem%wt_set_spec1 q0 hw.
      assert (exists r, q0 ⟹ r /\ r ↛) as (qt & hw' & hstq').
      eapply terminate_then_wt_stable, terminate_preserved_by_wt_nil; eauto.
      eapply cnv_wt_s_terminate; eauto.
      edestruct (hpre2 s qt hcnv) as (pt & hwpt & hstpt & hsubpt); eauto.
      eapply wt_push_nil_right; eauto. eapply wt_push_nil_right; eauto.
      assert (exists μ r, μ ∈ G /\ pt ⟹{μ} r) as (μ & p0 & mem0 & hw0).
      eapply hm. eapply wt_set_spec2; eauto. eapply wt_nil.
      exists μ. inversion hw0; subst.
      + exfalso. eapply lts_stable_spec2 in hstpt; eauto.
      + destruct μ.
        ++ edestruct (lts_oba_fw_forward q0 a) as (qr & hl1 & hl2); eauto with mdb.
        ++ eapply lts_outputs_spec1, hsubpt, lts_outputs_spec2 in l as (qr & l).
           exists qr. split; eauto. eapply wt_push_nil_left; eauto with mdb.
  Qed.

  Theorem equivalence_bhv_acc_mst (p : A) (q : R) : (p, ∅) ≾ (q, ∅) <-> (p, ∅) ≼ (q, ∅).
  Proof.
    split; intros (pre1 & pre2); split; eauto; now eapply equivalence_bhv_acc_mst2.
  Qed.

End must_set_acc_set.

(* ************************************************** *)

Section failure_must_set.

  Context `{LL : Label L}.
  Context `{LtsA : !Lts A L, !FiniteLts A L}.
  Context `{LtsR : !Lts R L, !FiniteLts R L}.

  Context `{@LtsObaFB A L LL LtsA LtsEqA LtsObaA}.
  Context `{@LtsObaFB R L LL LtsR LtsEqR LtsObaR}.

  Lemma equivalence_must_set_nfailure
    (p : A) (s : trace L) h1 (G : gset (ExtAct L)) :
    MUST__s (AFTER (p, ∅) s h1) G <-> ¬ Failure (p, ∅) s G.
  Proof.
    split.
    - intros hm (e & hw & hf). eassumption.
      edestruct (hm e) as (μ & p' & mem' & hw'). eapply wt_set_spec2. eauto. eapply wt_nil.
      edestruct (hf μ mem'). eauto.
    - intros hnf.
      destruct (either_MUST__s (AFTER (p, ∅) s h1) G).
      + intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
        eapply (wt_set_spec1 _ _ _ _ mem0).
      + eassumption.
      + eapply nMusts_ex in H1 as (p0 & mem & hnm).
        exfalso. eapply hnf.
        eapply nMust_ex in hnm as (p1 & hw1 & hnp).
        exists p1. split.
        eapply wt_push_nil_right.
        eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
        intros μ mem0 (p' & hw'). eapply hnp. eassumption.
        eassumption.
        eapply cnv_nil, cnv_wt_s_terminate; eauto.
        eapply (wt_set_spec1 _ _ _ _ mem).
        intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
        eapply (wt_set_spec1 _ _ _ _ mem0).
  Qed.

  Lemma equivalence_nmust_set_failure (p : A) (s : trace L) h1 (G : gset (ExtAct L)) :
    ¬ MUST__s (AFTER (p ▷ ∅) s h1) G <-> Failure (p ▷ ∅) s G.
  Proof.
    split.
    - intro hm.
      eapply nMusts_ex in hm as (p0 & mem & hnm).
      eapply nMust_ex in hnm as (p1 & hw1 & hnp).
      exists p1. split.
      eapply wt_push_nil_right.
      eapply (wt_set_spec1 _ _ _ _ mem). eassumption.
      intros μ mem0 (p' & hw'). eapply hnp. eassumption.
      eassumption.
      eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem).
      intros p0 mem0. eapply cnv_nil, cnv_wt_s_terminate; eauto.
      eapply (wt_set_spec1 _ _ _ _ mem0).
    - intros (e & hmem & hf) hm. eassumption.
      unfold MUST__s in hm.
      unfold MUST in hm.
      edestruct (hm e) as (μ & p1 & mem1 & hw1).
      eapply (wt_set_spec2 _ _ _ _ hmem). eapply wt_nil.
      eapply (hf μ mem1). eauto.
  Qed.

End failure_must_set.

Section failure_must_set_pre.
  Context `{LL : Label L}.
  Context `{LtsA : !Lts A L, !FiniteLts A L}.
  Context `{LtsR : !Lts R L, !FiniteLts R L}.

  Context `{@LtsObaFB A L LL LtsA LtsEqA LtsObaA}.
  Context `{@LtsObaFB R L LL LtsR LtsEqR LtsObaR}.

  Theorem equivalence_pre_failure_must_set (p : A) (q : R) : (p ▷ ∅) ≾ (q ▷ ∅) <-> (p ▷ ∅) ⋖ (q ▷ ∅).
  Proof.
    split.
    - intros (hpre1 & hpre2). split; eauto.
      intros s G hf.
      intro hcnv.
      eapply (equivalence_nmust_set_failure p s hcnv).
      intros hm. eapply (hpre2 s hcnv (hpre1 s hcnv)) in hm.
      eapply (equivalence_must_set_nfailure q s (hpre1 s hcnv) G) in hm. contradiction. eassumption.
    - intros (hpre1 & hpre2). split; eauto.
      intros s h1 h2 G hm%equivalence_must_set_nfailure.
      eapply (equivalence_must_set_nfailure q).
      intros hf%hpre2. contradiction.
  Qed.

End failure_must_set_pre.

Section preorder.

  (** Extensional definition of Must *)

  Definition must_extensional `{Sts (A * B), good : B -> Prop} (p : A) (e : B) : Prop :=
    forall η : max_exec_from (p, e), exists n fex, mex_take_from n η = Some fex /\ good (fex_from_last fex).2.

  Definition good_client `{Sts (A * B), good : B -> Prop} (s : (A * B)) := good s.2.

  #[global] Program Instance must_bar `{Sts (A * B)} (good : B -> Prop)
    `{good_decidable : forall e, Decision (good e)}: Bar (A * B) :=
    {| bar_pred '(p, e) := good e |}.
  Next Obligation. intros. destruct x as (p, e). simpl. eauto. Defined.

  Lemma must_intensional_coincide `{Sts (A * B), good : B -> Prop, good_decidable : forall (e : B), Decision (good e)}
    (p : A) (e : B) : @intensional_pred (A * B) _ (must_bar good) (p, e) ↔ @must_sts A B _ good p e.
  Proof.
    split.
    - intros H1. dependent induction H1; subst.
      + rewrite /bar_pred /= in H1. now eapply m_sts_now.
      + destruct (good_decidable e).
        rewrite /bar_pred /= in H1.
        now eapply m_sts_now. eapply m_sts_step; eauto.
    - intros hm; dependent induction hm.
      + constructor 1. rewrite /bar_pred //=.
      + constructor 2.
        * eassumption.
        * intros (q, e') Hstep. apply H0 =>//=.
  Qed.

  Lemma must_ext_pred_iff_must_extensional
    `{Sts (A * B), good : B -> Prop, good_decidable : forall (e : B), Decision (good e)}
    (p : A) (e : B) : @extensional_pred _ _ (must_bar good) (p, e) <-> @must_extensional A  B _ good p e.
  Proof. split; intros Hme η; destruct (Hme η) as (?&?&?&?).
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
         exists x, x0. split. eassumption. simpl. destruct (fex_from_last x0). naive_solver.
  Qed.

  Definition pre_extensional
    `{Sts (A * B), Sts (R * B), good : B -> Prop, good_decidable : forall (e : B), Decision (good e)}
    (p : A) (q : R) : Prop :=
    forall (e : B), @must_extensional A B _ good p e -> @must_extensional R B _ good q e.

  (* ************************************************** *)

  Lemma must_extensional_iff_must_sts
    `{good : B -> Prop, good_decidable : forall (e : B), Decision (good e)}
    `{Lts A L, !Lts B L, !LtsEq B L, !Good B L good, !FiniteLts A L, !FiniteLts B L}
    (p : A) (e : B) : @must_extensional A B _ good p e <-> @must_sts A B _ good p e.
  Proof.
    split.
    - intros hm. destruct Good0.
      eapply must_ext_pred_iff_must_extensional in hm.
      now eapply must_intensional_coincide, extensional_implies_intensional.
    - intros hm. destruct Good0.
      eapply must_intensional_coincide in hm.
      rewrite <- must_ext_pred_iff_must_extensional.
      eapply intensional_implies_extensional. eapply hm.
  Qed.

  Notation "p ⊑ₑ q" := (pre_extensional p q) (at level 70).

  Context `{good : B -> Prop}.
  Context `{good_dec : forall e, Decision (good e)}.
  Context `{LL : Label L}.
  Context `{LtsA : !Lts A L, !FiniteLts A L}.
  Context `{LtsR : !Lts R L, !FiniteLts R L}.

  Context `{LtsB : !Lts B L, !FiniteLts B L, LtsEqB: !LtsEq B L, !Good B L good}.

  (* ************************************************** *)

  Lemma pre_extensional_eq (p : A) (q : R) : @pre_extensional A B _ _ _ good _ p q <-> p ⊑ q.
    unfold pre_extensional, ctx_pre.
    split; intros hpre e.
    - rewrite <- 2 must_sts_iff_must, <- 2 must_extensional_iff_must_sts; eauto.
    - rewrite -> 2 must_extensional_iff_must_sts, -> 2 must_sts_iff_must; eauto.
  Qed.

  Context `{@LtsObaFB A L LL LtsA LtsEqA LtsObaA}.
  Context `{@LtsObaFB R L LL LtsR LtsEqR LtsObaR}.
  Context `{@LtsObaFB B L LL LtsB LtsEqB LtsObaB}.

  Context `{igen_conv : @gen_spec_conv  _ _ _ _ _ good Good0 gen_conv}.
  Context `{igen_acc : @gen_spec_acc _ _ _ _ _ good Good0 gen_acc}.

  (* ************************************************** *)

  (** Equivalence between the extensional definition of the contextual preorder and
      the alternative, inductive characterisation. *)

  Theorem equivalence_bhv_acc_ctx (p : A) (q : R) :
    @pre_extensional A B _ _ _ good _ p q <-> (p, ∅) ≼ (q, ∅).
  Proof.
    split.
    - intros hpre%pre_extensional_eq.
      now eapply lift_fw_ctx_pre, completeness_fw in hpre.
    - intros hpre%soundness_fw.
      now eapply pre_extensional_eq, lift_fw_ctx_pre.
  Qed.

  (* ************************************************** *)


  Corollary equivalence_bhv_mst_ctx
    (p : A) (q : R) : (p, ∅) ≾ (q, ∅) <-> @pre_extensional A B _ _ _ good _ p q.
  Proof.
    rewrite pre_extensional_eq.
    rewrite equivalence_bhv_acc_mst.
    rewrite <- equivalence_bhv_acc_ctx.
    eapply pre_extensional_eq.
  Qed.

End preorder.

From stdpp Require Import gmultiset.

Section application.

  Lemma nil_stable `{LtsOba A L} (q : A) (h : forall α, q ↛{α}) (m : mb L) : (q, m) ↛.
  Proof.
    destruct (decide ((q, m) ↛)); eauto.
    eapply lts_stable_spec1 in n as (q' & l').
    inversion l'; edestruct lts_stable_spec2; eauto.
  Qed.

  Lemma nil_cnv `{LtsOba A L} (q : A) (h : forall α, q ↛{α}) s m : (q, m) ⇓ s.
    dependent induction s.
    - now eapply cnv_nil, terminate_if_stable, nil_stable.
    - eapply cnv_act.
      + now eapply terminate_if_stable, nil_stable.
      + intros (q', m') hw. inversion hw; subst.
        exfalso. eapply (@lts_stable_spec2 (A * mb L)). eauto. now eapply nil_stable.
        inversion l; subst; [edestruct lts_stable_spec2 | |]; try eapply cnv_preserved_by_wt_nil; eauto.
  Qed.

  CoInductive ionly_spec `{LtsOba A L} (p : A) : Prop :=
  | mstep : (forall μ p', p ⟶[μ] p' -> exists a, μ = ActIn a) -> (forall α p', p ⟶{α} p' -> ionly_spec p') -> ionly_spec p.

  Lemma lts_outputs_ionly_spec `{LtsOba A L} (p : A) (pr : ionly_spec p) : lts_outputs p = ∅.
  Proof.
    eapply leibniz_equiv. intro a. split.
    intros mem. eapply lts_outputs_spec2 in mem as (p' & l').
    destruct pr as (h1 & h2). eapply h1 in l' as (b & heq). inversion heq. inversion 1.
  Qed.

  Lemma lts_outputs_ionly_spec_wt_nil_empty_mb `{LtsOba A L} p (pr : ionly_spec p) :
    (p, ∅) ⤓ -> forall t, (p, ∅) ⟹ t -> lts_outputs t = ∅.
  Proof.
    intros hpt p' hw.
    dependent induction hpt. dependent induction hw.
    - simpl. rewrite -> dom_empty_L, union_empty_r_L.
      now eapply lts_outputs_ionly_spec.
    - inversion l; subst.
      + destruct pr as (h1 & h2). eapply H4; eauto.
      + exfalso. eapply (gmultiset_not_elem_of_empty a).
        replace (∅ : gmultiset L) with ({[+ a +]} ⊎ m) by eauto. multiset_solver.
  Qed.

  Lemma lts_outputs_ionly_spec_wt_nil `{LtsOba A L} n p (pr : ionly_spec p) m :
    (p, m) ⤓ -> size m = n -> forall t, (p, m) ⟹ t -> lts_outputs t ⊆ dom m.
  Proof.
    dependent induction n; subst; intro hpt; dependent induction hpt; intros heq p' hw.
    - eapply gmultiset_size_empty_inv in heq. subst.
      replace (lts_outputs p') with (∅ : gset L).
      intros a mem. inversion mem. symmetry. eapply lts_outputs_ionly_spec_wt_nil_empty_mb; eauto with mdb.
    - inversion hw; subst.
      + simpl. replace (lts_outputs p) with (∅ : gset L).
        now rewrite union_empty_l_L. symmetry. now eapply lts_outputs_ionly_spec.
      + destruct pr as (h1 & h2); inversion l; subst; eauto.
        eapply IHn in w; eauto with mdb.
        ++ intros b mem%w%gmultiset_elem_of_dom. eapply gmultiset_elem_of_dom. multiset_solver.
        ++ rewrite gmultiset_size_disj_union in heq. rewrite gmultiset_size_singleton in heq. eauto.
  Qed.

  Lemma ionly_nil_leq2_wt_nil `{LtsOba A L} n p (pr : ionly_spec p) m :
    (p, m) ⤓ -> size m = n -> exists t, (p, m) ⟹ t /\ t ↛ /\ lts_outputs t ⊆ dom m.
  Proof.
    intros ht heq. edestruct @terminate_then_wt_stable as (t & hw & hst); eauto with mdb.
    exists t; split; eauto. split; eauto. eapply lts_outputs_ionly_spec_wt_nil; eauto.
  Qed.

  Lemma ionly_nil_leq2 `{@LtsObaFB A L LL LtsA LtsEqA LtsObaA ,@LtsObaFB B L LL LtsB LtsEqB LtsObaB}
    (p : A) (pr : ionly_spec p) (q : B) m (h : forall α, q ↛{α}) : (p, m) ≼₂ (q, m).
  Proof.
    intros s t hcnv hw hst.
    dependent induction hw.
    - inversion hcnv; subst.
      edestruct ionly_nil_leq2_wt_nil as (p' & hw & hst' & hsub); eauto.
      exists p'. multiset_solver.
    - exfalso. eapply (@lts_stable_spec2 (B * mb L)). eauto. now eapply nil_stable.
    - inversion hcnv; inversion l; subst.
      + exfalso. eapply (@lts_stable_spec2 B); eauto.
      + edestruct (IHhw m0 p B) as (t' & hw' & hst' & hsub'); eauto with mdb.
        eapply H5, wt_act. eapply lts_fw_out_mb. eapply wt_nil.
        exists t'. split. eapply wt_act; eauto. eapply lts_fw_out_mb. now split.
      + edestruct (IHhw ({[+ a +]} ⊎ m) p B) as (t' & hw' & hst' & hsub'); eauto.
        eapply H5, wt_act. eapply lts_fw_inp_mb. eapply wt_nil.
        exists t'. split. eapply wt_act; eauto. eapply lts_fw_inp_mb. now split.
  Qed.

  Lemma input_only_leq_nil
    `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !FiniteLts A L, !FiniteLts B L,
      @LtsObaFB R L IL LR LOR X, !FiniteLts R L, !Good R L good, (∀ e : R, Decision (good e)),
      @gen_spec_conv  _ _ _ _ _ good _ gen_conv, @gen_spec_acc _ _ _ _ _ good _ gen_acc}
    (p : A) (pr : ionly_spec p) (q : B) (h : forall α, q ↛{α}) : @pre_extensional _ _ _ _ _ good _ p q.
  Proof.
    now eapply equivalence_bhv_acc_ctx; split; intros ? ?; [eapply nil_cnv | eapply ionly_nil_leq2].
  Qed.

End application.
