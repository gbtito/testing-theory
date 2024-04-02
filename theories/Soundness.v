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

From Must Require Import TransitionSystems Must.

(* ************************************************************ *)

Inductive mustx
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  (ps : gset A) (e : B) : Prop :=
| mx_now (hh : good e) : mustx ps e
| mx_step
    (nh : ¬ good e)
    (ex : forall (p : A), p ∈ ps -> ∃ t, parallel_step (p, e) τ t)
    (pt : forall ps',
        lts_tau_set_from_pset_spec1 ps ps' -> ps' ≠ ∅ ->
        mustx ps' e)
    (et : forall (e' : B), e ⟶ e' -> mustx ps e')
    (com : forall (e' : B) μ (ps' : gset A),
        lts_step e (ActExt μ) e' ->
        wt_set_from_pset_spec1 ps [co μ] ps' -> ps' ≠ ∅ ->
        mustx ps' e')
  : mustx ps e.

#[global] Hint Constructors mustx:mdb.

Lemma mx_sub `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  ps e : mustx ps e -> forall qs, qs ⊆ ps -> mustx qs e.
Proof.
  intros hmx. dependent induction hmx.
  - eauto with mdb.
  - intros qs sub.
    eapply mx_step; eauto with mdb.
    + intros qs' hs hneq_nil.
      set (ps' := lts_tau_set_from_pset_ispec ps).
      destruct ps'.
      eapply H1; eauto with mdb.
      ++ destruct (set_choose_or_empty qs') as [(q' & l'%hs)|].
         intro eq_nil. destruct l' as (q & mem%sub & l%H5); set_solver.
         set_solver.
      ++ intros p (q & mem%sub & l)%hs. eauto.
    + intros e' μ qs' hle hwqs hneq_nil.
      eapply (H3 e' μ); eauto. intros p' mem%hwqs. set_solver.
Qed.

Lemma mx_mem `{LtsOba A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good} ps e
  : mustx ps e -> forall p, p ∈ ps -> mustx {[ p ]} e.
Proof. intros hmx p mem. eapply mx_sub; set_solver. Qed.

Lemma lem_dec `{Countable A} (X Y Z : gset A) :
    X ⊆ Y ∪ Z -> exists Y' Z', Y' ⊆ Y /\ Z' ⊆ Z /\ (Y' ∪ Z' ≡ X)%stdpp.
Proof.
  induction X using set_ind_L; intros sub.
  - exists ∅, ∅. set_solver.
  - assert (sub0 : X ⊆ Y ∪ Z) by set_solver.
    destruct (IHX sub0) as (Y0 & Z0 & sub1 & sub2 & eq).
    assert (mem_dec : x ∈ Y \/ x ∈ Z). set_solver.
    destruct mem_dec.
    + exists ({[x]} ∪ Y0), Z0. set_solver.
    + exists Y0, ({[x]} ∪ Z0). set_solver.
Qed.

Lemma mustx_terminate_ungood
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  ps e : mustx ps e -> good e \/ forall p, p ∈ ps -> p ⤓.
Proof.
  intros hmx.
  induction hmx.
  - now left.
  - right.
    intros p mem.
    eapply tstep. intros p' l.
    edestruct (H1 {[p']}); [exists p; set_solver| | |]; set_solver.
Qed.

Lemma must_mu_either_good_cnv `{LtsOba A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good} ps e e' :
  mustx ps e -> forall μ p, p ∈ ps -> e ⟶[co μ] e' -> good e \/ p ⇓ [μ].
Proof.
  intros hmx μ p mem l.
  induction hmx.
  - now left.
  - right.
    edestruct mustx_terminate_ungood; eauto with mdb. contradiction.
    eapply cnv_act. eauto.
    intros q w.
    destruct μ.
    + simpl in l.
      assert (h1 : wt_set_from_pset_spec1 ps [co (ActOut a)] {[q]}).
      exists p. split; set_solver.
      assert (h2 : {[q]} ≠ (∅ : gset A)) by set_solver.
      set (hm := com e' (ActOut a) {[ q ]} l h1 h2).
      destruct (mustx_terminate_ungood _ _ hm).
      ++ contradict nh.
         eapply good_preserved_by_lts_output_converse; eassumption.
      ++ eapply cnv_nil. eapply H6. set_solver.
    + eapply cnv_nil.
      eapply terminate_preserved_by_wt_output.
      eapply H5; eassumption. eassumption.
Qed.

Lemma ungood_acnv_mu `{LtsOba A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good} ps e e' :
  mustx ps e -> forall μ p, p ∈ ps -> e ⟶[co μ] e' -> ¬ good e -> p ⇓ [μ].
Proof. intros. edestruct must_mu_either_good_cnv; eauto. contradiction. Qed.

(* to rework *)
Lemma mx_sum
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  ps1 ps2 e : mustx ps1 e -> mustx ps2 e -> mustx (ps1 ∪ ps2) e.
Proof.
  intros hmx1 hmx2. revert ps2 hmx2.
  dependent induction hmx1. eauto with mdb.
  intros ps2 hmx2.
  eapply mx_step.
  - eassumption.
  - intros p mem.
    eapply elem_of_union in mem.
    destruct mem.
    eapply ex; eassumption.
    inversion hmx2; subst. contradiction.
    eapply ex0; eassumption.
  - intros.
    set (Y := lts_tau_set_from_pset ps).
    set (Z := lts_tau_set_from_pset ps2).
    assert (ps' ⊆ lts_tau_set_from_pset ps ∪ lts_tau_set_from_pset ps2).
    intros q mem. eapply H4 in mem as (q0 & mem & l).
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply lts_tau_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply lts_tau_set_from_pset_ispec; eassumption.
    eapply lem_dec in H6 as (Y' & Z' & Y_spec' & Z_spec' & eq).
    remember Y' as Y_'.
    remember Z' as Z_'.
    destruct Y_' using set_ind_L.
    + destruct Z_' using set_ind_L.
      ++ exfalso.
         assert (exists p, p ∈ ps') as (p & mem).
         destruct ps' using set_ind_L. contradiction.
         exists x. set_solver.
         eapply H4 in mem as (p0 & mem & l).
         eapply elem_of_union in mem. destruct mem.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
         eapply lts_tau_set_from_pset_ispec in l; set_solver.
      ++ assert (Y' = ∅) by set_solver.
         assert (Z' = ps') by set_solver. subst.
         inversion hmx2; subst. set_solver.
         eapply pt0. intros t mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
    + destruct Z_' using set_ind_L.
      ++ assert (Y' = ps') by set_solver.
         assert (mustx ps e) by eauto with mdb.
         inversion H8; subst. set_solver.
         eapply pt0. intros t mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
      ++ subst.
         replace ps' with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
         eapply H1.
         intros t mem. apply lts_tau_set_from_pset_ispec. set_solver. set_solver.
         inversion hmx2; subst. now contradiction nh.
         eapply pt0.
         intros t mem. eapply lts_tau_set_from_pset_ispec. set_solver. set_solver.
  - intros e' l. eapply H2; eauto with mdb.
    inversion hmx2; subst; eauto with mdb. contradiction.
  - intros e' μ ps' l ps'_spec neq_nil.
    destruct (good_decidable e'); eauto with mdb.
    assert (HAps : forall p, p ∈ ps -> p ⇓ [co μ]).
    intros p0 mem0.
    eapply cnv_act. edestruct (mustx_terminate_ungood ps); eauto with mdb.
    contradiction.
    intros p' hw. eapply cnv_nil.
    edestruct (mustx_terminate_ungood {[p']}). eapply com; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver. contradiction.
    set_solver.
    set (Y := wt_s_set_from_pset ps [co μ] HAps).
    assert (HAX2 : forall p, p ∈ ps2 -> p ⇓ [co μ]).
    intros p0 mem0.
    eapply cnv_act. edestruct (mustx_terminate_ungood ps2); eauto with mdb.
    contradiction.
    intros p' hw. eapply cnv_nil.
    edestruct (mustx_terminate_ungood {[p']}).
    inversion hmx2; subst. contradiction. eapply com0; eauto.
    intros j memj. eapply elem_of_singleton_1 in memj. subst.
    exists p0. split; eauto. set_solver. contradiction. set_solver.
    set (Z := wt_s_set_from_pset ps2 [co μ] HAX2).
    assert (ps' ⊆ Y ∪ Z).
    intros q mem. eapply ps'_spec in mem as (q0 & mem & l').
    eapply elem_of_union in mem. destruct mem.
    eapply elem_of_union. left. eapply wt_s_set_from_pset_ispec; eassumption.
    eapply elem_of_union. right. eapply wt_s_set_from_pset_ispec; eassumption.
    eapply lem_dec in H4 as (Y0 & Z0 & Y_spec0 & Z_spec0 & eq).
    destruct Y0 using set_ind_L.
    + destruct Z0 using set_ind_L.
      ++ exfalso.
         assert (exists p, p ∈ ps') as (p & mem).
         destruct ps' using set_ind_L. contradiction.
         exists x. set_solver.
         eapply ps'_spec in mem as (p0 & mem & l').
         eapply elem_of_union in mem.
         destruct mem; eapply (wt_s_set_from_pset_ispec ps [co μ] HAps) in l'; set_solver.
      ++ inversion hmx2; subst. now contradict nh.
         eapply com0. eassumption. intros t mem.
         eapply (wt_s_set_from_pset_ispec ps2 [co μ] HAX2).
         set_solver. set_solver.
    + destruct Z0 using set_ind_L.
      ++ inversion hmx2; subst. now contradict nh.
         eapply com. eassumption. intros t mem.
         eapply (wt_s_set_from_pset_ispec ps [co μ] HAps).
         set_solver. set_solver.
      ++ replace ps' with (({[x]} ∪ X) ∪ ({[x0]} ∪ X0)) by set_solver.
         eapply H3; eauto with mdb.
         intros t mem.
         eapply (wt_s_set_from_pset_ispec ps [co μ] HAps).
         set_solver. set_solver.
         inversion hmx2; subst. now contradict nh.
         eapply com0. eassumption.
         intros t mem.
         eapply (wt_s_set_from_pset_ispec ps2 [co μ] HAX2).
         set_solver. set_solver.
Qed.

Lemma mx_forall
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good} ps e :
  ps ≠ ∅ -> (forall p, p ∈ ps -> mustx {[p]} e) -> mustx ps e.
Proof.
  intros neq_nil hm.
  induction ps using set_ind_L.
  - set_solver.
  - destruct (set_choose_or_empty X).
    eapply mx_sum; set_solver.
    assert (X = ∅) by set_solver.
    rewrite H3, union_empty_r_L. set_solver.
Qed.

Lemma wt_nil_mx
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  : forall p1 p2 e, mustx {[ p1 ]} e -> p1 ⟹ p2 -> mustx {[p2]} e.
Proof.
  intros p1 p2 e hmx wt.
  dependent induction wt; subst; eauto with mdb.
  inversion hmx; subst; eauto with mdb.
  eapply IHwt; eauto with mdb.
  eapply pt; eauto with mdb.
  intros p2 mem. replace q with p2 in * by set_solver.
  exists p; set_solver.
  set_solver.
Qed.

Lemma wt_mu_mx
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  p1 p2 e e' μ : ¬ good e -> mustx {[ p1 ]} e -> e ⟶[μ] e' -> p1 ⟹{co μ} p2 -> mustx {[p2]} e'.
Proof.
  intros nh hmx l w.
  inversion hmx; subst.
  - contradiction.
  - eapply com; eauto with mdb. exists p1. set_solver. set_solver.
Qed.

Lemma must_set_if_must
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  (p : A) (e : B) : must p e -> mustx {[ p ]} e.
Proof.
  intro hm. dependent induction hm.
  - eauto with mdb.
  - eapply mx_step.
    + eassumption.
    + set_solver.
    + intros ps' hs hneq_nil.
      unfold lts_tau_set_from_pset_spec1 in hs.
      eapply mx_forall; set_solver.
    + eauto with mdb.
    + intros e' μ X' hle hws hneq_nil.
      unfold wt_set_from_pset_spec1 in hws.
      eapply mx_forall. eassumption.
      intros.
      edestruct hws as (p' & mem%elem_of_singleton_1 & w); subst; eauto.
      inversion w; subst; eauto with mdb.
      eapply wt_mu_mx; eauto with mdb.
      eapply wt_nil_mx; eauto with mdb.
Qed.

Lemma must_if_must_set_helper
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  (ps : gset A) (e : B) : mustx ps e -> forall p, p ∈ ps -> must p e.
Proof.
  intro hm. dependent induction hm.
  - eauto with mdb.
  - intros p mem. eapply m_step.
    + eassumption.
    + set_solver.
    + intros p' hl.
      set (X' := list_to_set (lts_tau_set p) : gset A).
      assert (p' ∈ X').
      eapply lts_tau_set_spec, elem_of_list_to_set in hl; eauto.
      eapply (H1 X'); eauto.
      intros p0 mem0%elem_of_list_to_set%lts_tau_set_spec. set_solver. set_solver.
    + eauto with mdb.
    + intros p' e' μ hle hlp.
      set (X' := list_to_set (
                     map proj1_sig (enum $ dsig (lts_step p (ActExt (co μ))))
                   ) : gset A).
      assert (p' ∈ X').
      eapply elem_of_list_to_set, elem_of_list_fmap; eauto.
      exists (dexist p' hlp). split. eauto. eapply elem_of_enum.
      eapply (H3 e' μ X'). eassumption.
      intros p0 mem0%elem_of_list_to_set.
      eapply elem_of_list_fmap in mem0 as ((r & l) & eq & mem'). subst.
      exists p. split; eauto.
      eapply wt_act.
      eapply bool_decide_unpack. eauto. eapply wt_nil. set_solver. set_solver.
Qed.

Lemma must_if_must_set
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  (p : A) (e : B) : mustx {[ p ]} e -> must p e.
Proof. intros. eapply must_if_must_set_helper; set_solver. Qed.

Lemma must_set_iff_must
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  (p : A) (e : B) : must p e <-> mustx {[ p ]} e.
Proof. split; [eapply must_set_if_must | eapply must_if_must_set]. Qed.

(* To move, also present in Completeness. *)
Lemma must_preserved_by_weak_nil_srv `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good}
  (p q : A) (e : B) : must p e -> p ⟹ q -> must q e.
Proof.
  intros hm w.
  dependent induction w; eauto with mdb.
  eapply IHw; eauto.
  eapply must_preserved_by_lts_tau_srv; eauto.
Qed.

Lemma must_preserved_by_wt_synch_if_notgood
  `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good} (p p' : A) (r r' : B) μ:
  must p r -> ¬ good r -> p ⟹{μ} p' -> r ⟶[co μ] r' -> must p' r'.
Proof.
  intros hm u hwp hwr.
  dependent induction hwp.
  - eapply IHhwp; eauto. eapply must_preserved_by_lts_tau_srv; eauto.
  - eapply must_preserved_by_weak_nil_srv; eauto.
    inversion hm. contradiction. eapply com.
    eassumption. now rewrite co_involution.
Qed.

Lemma must_set_for_all
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  (X : gset A) (e : B) : X ≠ ∅ -> (forall p, p ∈ X -> must p e) -> mustx X e.
Proof.
  intros xneq_nil hm.
  destruct (good_decidable e).
  - now eapply mx_now.
  - eapply mx_step.
    + eassumption.
    + intros p h%hm. inversion h. contradiction. eassumption.
    + intros X' xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & mem%hm & hl)%xspec'. eapply must_set_iff_must.
      inversion mem; eauto with mdb.
    + intros e' hl.
      eapply mx_forall. eassumption.
      intros p' mem%hm. eapply must_set_iff_must.
      inversion mem; eauto with mdb. contradiction.
    + intros e' μ X' hle xspec' xneq_nil'.
      eapply mx_forall. eassumption.
      intros p' (p0 & h%hm & hl)%xspec'. eapply must_set_iff_must.
      eapply must_preserved_by_wt_synch_if_notgood; eauto.
      rewrite co_involution. eassumption.
Qed.

Lemma must_set_iff_must_for_all
  `{Lts A L, !FiniteLts A L, !Lts B L, !LtsEq B L, !Good B L good}
  (X : gset A) (e : B) : X ≠ ∅ -> (forall p, p ∈ X -> must p e) <-> mustx X e.
Proof.
  intros.
  split. now eapply must_set_for_all.
  now eapply must_if_must_set_helper.
Qed.


(* ************************************************************ *)

Definition bhv_pre_cond1__x `{FiniteLts P L, FiniteLts Q L} (ps : gset P) (q : Q) :=
  forall s, (forall p, p ∈ ps -> p ⇓ s) -> q ⇓ s.

Notation "ps ≼ₓ1 q" := (bhv_pre_cond1__x ps q) (at level 70).

Definition bhv_pre_cond2__x
  `{@FiniteLts P L HL LtsP, @FiniteLts Q L HL LtsQ} (ps : gset P) (q : Q) :=
  forall s q',
    q ⟹[s] q' -> q' ↛ ->
    (forall p, p ∈ ps -> p ⇓ s) ->
    exists p, p ∈ ps /\ exists p', p ⟹[s] p' /\ p' ↛ /\ lts_outputs p' ⊆ lts_outputs q'.

Notation "ps ≼ₓ2 q" := (bhv_pre_cond2__x ps q) (at level 70).

#[global] Hint Unfold bhv_pre_cond1__x bhv_pre_cond2__x : mdb.

Notation "ps ≼ₓ q" := (bhv_pre_cond1__x ps q /\ bhv_pre_cond2__x ps q) (at level 70).

Lemma alt_set_singleton_iff `{@FiniteLts P L HL LtsP, @FiniteLts Q L HL LtsQ}
  (p : P) (q : Q) : p ≼ q <-> {[ p ]} ≼ₓ q.
Proof.
  split.
  - intros (hbhv1 & hbhv2). split.
    + intros s mem. eapply hbhv1. set_solver.
    + intros s q' w st hcnv. edestruct hbhv2; set_solver.
  - intros (h1 & h2). split.
    + intros s mem. eapply h1. set_solver.
    + intros s q' w st hcnv. edestruct h2; set_solver.
Qed.

Lemma bhvleqone_preserved_by_tau `{FiniteLts P L, FiniteLts Q L} (ps : gset P) (q q' : Q) :
  ps ≼ₓ1 q -> q ⟶ q' -> ps ≼ₓ1 q'.
Proof. intros halt1 l s mem. eapply cnv_preserved_by_lts_tau; eauto. Qed.

Lemma bhvx_preserved_by_tau `{@FiniteLts P L HL LtsP, @FiniteLts Q L HL LtsQ}
  (ps : gset P) (q q' : Q) : q ⟶ q' -> ps ≼ₓ q -> ps ≼ₓ q'.
Proof.
  intros l (halt1 & halt2).
  split.
  - intros s mem. eapply cnv_preserved_by_lts_tau; eauto.
  - intros s q'' w st hcnv.
    destruct (halt2 s q'') as (p' & mem & p'' & hw & hst & sub0); eauto with mdb.
Qed.

Lemma bhvleqone_mu `{@FiniteLts P L HL LtsP, @FiniteLts Q L HL LtsQ}
  (ps0 ps1 : gset P) μ (q q' : Q) (htp : forall p, p ∈ ps0 -> terminate p) :
  ps0 ≼ₓ1 q -> wt_set_from_pset_spec ps0 [μ] ps1  -> q ⟶[μ] q' -> ps1 ≼ₓ1 q'.
Proof.
  intros hleq hws l s hcnv.
  eapply cnv_preserved_by_wt_act.
  eapply hleq.
  intros p mem'. eapply cnv_act.
  + eapply htp; eauto.
  + intros. eapply hcnv, hws; eassumption.
  + eauto with mdb.
Qed.

Lemma bhvx_preserved_by_mu `{@FiniteLts P L HL LtsP, @FiniteLts Q L HL LtsQ}
  (ps0 : gset P) (q : Q) μ ps1 q' (htp : forall p, p ∈ ps0 -> terminate p) :
  q ⟶[μ] q' -> wt_set_from_pset_spec ps0 [μ] ps1 -> ps0 ≼ₓ q -> ps1 ≼ₓ q'.
Proof.
  intros lts__q ps1_spec (halt1 & halt2). split.
  - eapply bhvleqone_mu; eauto.
  -  intros s q0 wt st hcnv.
     edestruct (halt2 (μ :: s) q0) as (t & mem & p0 & p1 & wta__t & sub); eauto with mdb.
     intros p' mem'. eapply cnv_act; eauto.
     intros p'' mem1. eapply hcnv, ps1_spec; eassumption.
     eapply wt_pop in p1 as (r & w1 & w2).
     exists r. repeat split. eapply ps1_spec; eassumption. eauto.
Qed.

Lemma terminate_then_wt_stable  `{Lts A L} p : p ⤓ -> exists p', p ⟹ p' /\ p' ↛.
Proof.
  intros ht.
  induction ht.
  destruct (lts_stable_decidable p τ).
  - exists p; eauto with mdb.
  - eapply lts_stable_spec1 in n as (p'& l).
    destruct (H2 p' l) as (p0 & w0 & st0).
    exists p0; eauto with mdb.
Qed.

Lemma bhvx_mu_ex `{@FiniteLts P L HL LtsP, @FiniteLts Q L HL LtsQ}
  (ps : gset P) (q q' : Q) μ
  : ps ≼ₓ q -> (forall p, p ∈ ps -> p ⇓ [μ]) ->
    q ⟶[μ] q' -> exists p', wt_set_from_pset_spec1 ps [μ] {[ p' ]}.
Proof.
  intros (h1 & h2) hcnv hl.
  assert (exists q0, q ⟹{μ} q0 /\ q0 ↛) as (q0 & wq0 & stq0).
  assert (hqt : q' ⤓). eapply cnv_terminate, cnv_preserved_by_wt_act.
  eapply h1, hcnv. eauto with mdb.
  eapply terminate_then_wt_stable in hqt as (q0 & w0 & st0).
  exists q0; eauto with mdb.
  destruct (h2 [μ] q0 wq0 stq0 hcnv) as (p1 & mem1 & p0 & wp0 & stp0 & subp0).
  exists p0. intros p1' mem. replace p1' with p0 by set_solver. eauto.
Qed.

Lemma ungood_must_st_nleqx
  `{@LtsObaFW P L Lbl LtsP LtsEqP LtsObaP,
    @LtsObaFW Q L Lbl LtsQ LtsEqQ LtsObaQ,
    !FiniteLts P L, !FiniteLts Q L,
    !Lts B L, !LtsEq B L, !Good B L good}
  (X : gset P) (q : Q) e : ¬ good e -> mustx X e -> (¬ exists t, parallel_step (q, e) τ t) -> ¬ X ≼ₓ2 q.
Proof.
  intros.
  intro hbhv2.
  destruct (lts_stable_decidable q τ).
  - assert (htX : ∀ p : P, p ∈ X → p ⇓ []).
    destruct (mustx_terminate_ungood X e H2) as [|htps]; eauto with mdb. contradiction.
    destruct (hbhv2 [] q (wt_nil q) l htX) as (p & mem & p' & wp & stp' & sub).
    assert (mustx {[ p' ]} e). eapply (wt_nil_mx p). eapply (mx_sub X e H2). set_solver. eassumption.
    destruct H4; eauto.
    edestruct (ex p'). now eapply elem_of_singleton.
    inversion H4; subst.
    eapply lts_stable_spec2 in stp'; eauto.
    destruct (lts_stable_decidable e τ).
    eapply lts_stable_spec2 in l1. eauto. eauto with mdb.
    eapply lts_stable_spec1 in n. eauto. eauto with mdb.
    destruct α1 as [[b|b]|]; destruct α2 as [[c|c]|]; simpl in eq; eauto; subst.
    contradict H3.
    destruct (lts_oba_fw_forward q c) as (q0 & l3 & l4).
    exists (q0, b2). eapply (ParSync (ActExt $ ActIn c) (ActExt $ ActOut c)); simpl; eauto.
    eapply lts_outputs_spec1, sub, lts_outputs_spec2 in l1 as (q0 & l0).
    contradict H3.
    exists (q0, b2). eapply (ParSync (ActExt $ ActOut c) (ActExt $ ActIn c)); simpl; eauto.
  - eapply lts_stable_spec1 in n as (q' & l). eauto with mdb.
Qed.

Lemma stability_nbhvleqtwo
  `{@LtsObaFW P L Lbl LtsP LtsEqP LtsObaP, @LtsObaFW Q L Lbl LtsQ LtsEqQ LtsObaQ,
    !FiniteLts P L, !FiniteLts Q L, !Lts B L, !LtsEq B L, !Good B L good}
  (X : gset P) (q : Q) e : ¬ good e -> mustx X e -> X ≼ₓ2 q -> exists t, (q, e) ⟶{τ} t.
Proof.
  intros nhg hmx hleq.
  destruct (lts_stable_decidable (q, e) τ).
  - exfalso. apply (ungood_must_st_nleqx X q e nhg hmx).
    intros (t & hl). eapply lts_stable_spec2 in l. contradiction. eauto. eassumption.
  - eapply lts_stable_spec1 in n as (t & hl). eauto.
Qed.

Lemma soundnessx `{
    @LtsObaFW A L Lbl LtsA LtsEqA LtsObaA, @LtsObaFW C L Lbl LtsC LtsEqC LtsObaC,
    @LtsObaFB B L Lbl LtsB LtsEqB LtsObaB, !FiniteLts A L, !FiniteLts C L, !FiniteLts B L, !Good B L good}
  (ps : gset A) (e : B) : mustx ps e -> forall (q : C), ps ≼ₓ q -> must q e.
Proof.
  intros hmx q (halt1 & halt2).
  dependent induction hmx.
  - eauto with mdb.
  - destruct (mustx_terminate_ungood ps e ltac:(eauto with mdb)).
    contradiction.
    assert (q_conv : q ⤓).
    eapply cnv_terminate, halt1; intros; eapply cnv_nil.
    destruct (mustx_terminate_ungood ps e); eauto with mdb.
    induction q_conv as [q tq IHq_conv].
    eapply m_step.
    + eassumption.
    + eapply (stability_nbhvleqtwo ps); eauto with mdb.
    + intros q' l. eapply IHq_conv.
      ++ eassumption.
      ++ eapply bhvleqone_preserved_by_tau; eauto.
      ++ eauto with mdb.
    + intros e' hle. eapply H3; eassumption.
    + intros q' e' μ le lq.
      assert (HA : forall p, p ∈ ps -> p ⇓ [co μ]).
      intros; eapply ungood_acnv_mu; eauto with mdb.
      rewrite co_involution. eassumption.
      set (ts := wt_s_set_from_pset ps [co μ] HA).
      set (ts_spec := wt_s_set_from_pset_ispec ps [co μ] HA).
      assert ((exists p, p ∈ ts) \/ ts ≡ ∅)%stdpp as [neq_nil | eq_nil]
          by (eapply set_choose_or_empty).
      eapply H4; eauto with mdb.
      destruct ts_spec. eassumption.
      intro eq_nil. destruct neq_nil as (t & mem).
      replace ts with (wt_s_set_from_pset ps [co μ] HA) in mem; eauto.
      subst. rewrite eq_nil in mem. inversion mem.
      eapply bhvleqone_mu; eauto with mdb.
      eapply bhvx_preserved_by_mu; eauto with mdb.
      exfalso.
      edestruct (bhvx_mu_ex ps q q' (co μ)) as (p' & u); eauto.
      assert (p' ∈ ts) as mem.
      edestruct (u p' ltac:(set_solver)) as (r & mem & hw).
      eapply ts_spec; eauto.
      set_solver.
Qed.

Lemma soundness_fw `{
    @LtsObaFW A L IL LA LOA V,
    @LtsObaFW C L IL LC LOC T,
    @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !FiniteLts C L, !FiniteLts B L, !Good B L good }
  (p : A) (q : C) : p ≼ q -> p ⊑ q.
Proof.
  intros halt e hm.
  eapply (soundnessx {[p]}).
  now eapply must_set_iff_must. now eapply alt_set_singleton_iff.
Qed.

From Must Require Lift.

Lemma soundness
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB C L IL LC LOC T, @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !FiniteLts C L, !FiniteLts B L, !Good B L good }
  (p : A) (q : C) : p ▷ ∅ ≼ q ▷ ∅ -> p ⊑ q.
Proof.
  intros halt e hm.
  eapply Lift.must_iff_must_fw in hm.
  eapply Lift.must_iff_must_fw.
  now eapply (soundness_fw (p ▷ ∅) (q ▷ ∅)).
Qed.
