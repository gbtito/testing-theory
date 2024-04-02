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
From Must Require Import Lift.

(** Test generators specification. *)

Class gen_spec {A L : Type} `{Lts A L, !LtsEq A L, !Good A L good}
  (gen : list (ExtAct L) -> A) := {
    gen_spec_ungood : forall s, ¬ good (gen s) ;
    gen_spec_mu_lts_co μ s : gen (μ :: s) ⟶⋍[co μ] gen s;
    gen_spec_out_lts_tau_ex a s : ∃ e', gen (ActOut a :: s) ⟶ e';
    gen_spec_out_lts_tau_good a s e : gen (ActOut a :: s) ⟶ e -> good e;
    gen_spec_out_lts_mu_uniq {e a μ s} :
    gen (ActOut a :: s) ⟶[μ] e -> e = gen s /\ μ = ActIn a;
  }.

Class gen_spec_conv {A L : Type} `{Lts A L, ! LtsEq A L, !Good A L good}
  (gen_conv : list (ExtAct L) -> A) := {
    gen_conv_spec_gen_spec : gen_spec gen_conv ;
    gen_spec_conv_nil_stable_mu μ : gen_conv [] ↛[μ] ;
    gen_spec_conv_nil_lts_tau_ex : ∃ e', gen_conv [] ⟶ e';
    gen_spec_conv_nil_lts_tau_good e : gen_conv [] ⟶ e -> good e;
  }.

#[global] Existing Instance gen_conv_spec_gen_spec.

Class gen_spec_acc {A : Type} `{Lts A L, ! LtsEq A L, !Good A L good}
  (gen_acc : gset L -> list (ExtAct L) -> A) := {
    gen_acc_spec_gen_spec O : gen_spec (gen_acc O) ;
    gen_spec_acc_nil_stable_tau O : gen_acc O [] ↛ ;
    gen_spec_acc_nil_stable_out O a : gen_acc O [] ↛[ActOut a] ;
    gen_spec_acc_nil_mu_inv O a e : gen_acc O [] ⟶[ActIn a] e -> a ∈ O ;
    gen_spec_acc_nil_mem_lts_inp O a : a ∈ O -> ∃ r, gen_acc O [] ⟶[ActIn a] r ;
    gen_spec_acc_nil_lts_inp_good μ e' O : gen_acc O [] ⟶[μ] e' -> good e' ;
  }.

#[global] Existing Instance gen_acc_spec_gen_spec.

(** Facts about Must *)

Lemma must_preserved_by_weak_nil_srv `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good}
  (p q : A) (e : B) : must p e -> p ⟹ q -> must q e.
Proof.
  intros hm w.
  dependent induction w; eauto with mdb.
  eapply IHw; eauto.
  eapply must_preserved_by_lts_tau_srv; eauto.
Qed.

Lemma must_preserved_by_synch_if_notgood
  `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good} (p p' : A) (r r' : B) μ:
  must p r -> ¬ good r -> p ⟶[μ] p' -> r ⟶[co μ] r' -> must p' r'.
Proof.
  intros hm u l__p l__r.
  inversion hm; subst.
  - contradiction.
  - eapply com; eauto with mdb. now rewrite co_involution.
Qed.

(* Facts about test generators. *)

Lemma gen_conv_always_reduces `{LtsOba A L, !Good A L good, ! gen_spec_conv gen_conv} s :
  ∃ e, gen_conv s ⟶ e.
Proof.
  induction s as [|μ s'].
  - eapply gen_spec_conv_nil_lts_tau_ex.
  - destruct μ.
    + destruct IHs' as (e & l).
      destruct (gen_spec_mu_lts_co (ActIn a) s') as (e' & hl' & heq).
      destruct (eq_spec e' e τ) as (e0 & hl0 & heqe0). eauto with mdb.
      destruct (lts_oba_output_commutativity hl' hl0)
        as (r & l1 & l2); eauto.
    + eapply gen_spec_out_lts_tau_ex.
Qed.

Lemma terminate_must_test_conv_nil
  `{Lts A L, !Lts B L, !LtsEq B L, !Good B L good, !gen_spec_conv gen_conv}
  (p : A) : p ⤓ -> must p (gen_conv []).
Proof.
  intros ht.
  induction ht.
  eapply m_step; eauto with mdb.
  - eapply gen_spec_ungood.
  - destruct gen_spec_conv_nil_lts_tau_ex as (e' & l); eauto with mdb.
  - intros e' l. eapply gen_spec_conv_nil_lts_tau_good in l. eauto with mdb.
  - intros p0 e0 μ l1 l2.
    exfalso. eapply lts_stable_spec2.
    exists e0. eassumption. eapply gen_spec_conv_nil_stable_mu.
Qed.

Lemma must_gen_conv_wta_mu
  `{Lts A L, ! Lts B L, ! LtsEq B L, !Good B L good, ! gen_spec_conv gen_conv}
  μ s (p q : A): must p (gen_conv (μ :: s)) -> p ⟹{μ} q -> must q (gen_conv s).
Proof.
  intros hm w.
  dependent induction w.
  + eapply IHw; eauto with mdb.
    eapply must_preserved_by_lts_tau_srv; eauto.
  + edestruct gen_spec_mu_lts_co as (t' & hlt' & heqt').
    eapply (must_eq_client _ _ _ heqt').
    eapply (must_preserved_by_weak_nil_srv q t); eauto.
    eapply must_preserved_by_synch_if_notgood; eauto with mdb.
    eapply gen_spec_ungood.
Qed.

(** First implication of the first requirement. *)

Lemma cnv_if_must
  `{Lts A L, !Lts B L, !LtsEq B L, !Good B L good, !gen_spec_conv gen_conv}
  s (p : A) : must p (gen_conv s) -> p ⇓ s.
Proof.
  revert p.
  induction s as [|μ s']; intros p hm.
  - eapply cnv_nil.
    eapply (must_terminate_ungood _ _ hm), gen_spec_ungood.
  - eapply cnv_act.
    + eapply (must_terminate_ungood _ _ hm), gen_spec_ungood.
    + intros q w. eapply IHs', must_gen_conv_wta_mu; eauto.
Qed.

Lemma f_gen_lts_mu_in_the_middle
  `{LtsOba A L, !Good A L good, !gen_spec f} s1 s2 μ :
  are_inputs s1 -> f (s1 ++ μ :: s2) ⟶⋍[co μ] f (s1 ++ s2).
Proof.
  revert s2 μ.
  induction s1 as [|ν s']; intros s2 μ his; simpl in *.
  - eapply (gen_spec_mu_lts_co μ).
  - inversion his as [| ? ? (b & eq) his']. subst.
    destruct (IHs' s2 μ his') as (r & hlr & heqr).
    edestruct (gen_spec_mu_lts_co (ActIn b) (s' ++ μ :: s2))
      as (t &  hlt & heqt).
    edestruct (eq_spec t r) as (u & hlu & hequ). eauto with mdb.
    destruct (lts_oba_output_commutativity hlt hlu)
      as (v & l1 & (t' & l2 & heq')).
    exists v. split. eassumption.
    destruct (gen_spec_mu_lts_co (ActIn b) (s' ++ s2)) as (w & hlw & heqw).
    eapply lts_oba_output_deter_inv; try eassumption.
    etrans. eauto. etrans. eauto. etrans. eauto. now symmetry.
Qed.

Lemma inversion_gen_mu
  `{M1 : LtsOba A L, !Good A L good, !gen_spec f} s μ p :
  (forall μ, f [] ↛[μ] \/ (forall e, f [] ⟶[μ] e -> good e)) ->
  f s ⟶[μ] p ->
  good p \/ ∃ s1 s2, s = s1 ++ co μ :: s2 /\ p ⋍ f (s1 ++ s2) /\ are_inputs s1.
Proof.
  revert μ p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros μ p h l.
  - edestruct (h μ); eauto.
    now eapply lts_stable_spec2 in H1; eauto.
  - destruct ν as [b|b].
    + edestruct (gen_spec_mu_lts_co (ActIn b) s') as (r & hlr & heqr).
      destruct (decide (μ = ActOut b)).
      ++ subst.
         right. exists [], s'. repeat split; simpl; eauto with mdb.
         transitivity r; eauto. eapply (lts_oba_output_deter l hlr); eauto.
         now eapply Forall_nil.
      ++ destruct (lts_oba_output_confluence n hlr l)
           as (t & l1 & (t' & l2 & heq)).
         destruct (eq_spec (f s') t (ActExt $ μ)) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         edestruct (Hlength s' ltac:(eauto) μ v h hlv)
           as [hg | (s1' & s2' & eq0 & eq1 & eq2)]; eauto. subst.
         +++ left.
             eapply good_preserved_by_lts_output_converse, good_preserved_by_eq; eauto.
             transitivity t; now symmetry.
         +++ right. exists (ActIn b :: s1'), s2'. repeat split; eauto.
             destruct μ; subst; eauto.
             edestruct (f_gen_lts_mu_in_the_middle (ActIn b :: s1') s2' (ActIn b))
               as (r' & hlr' & heqr').
             eapply Forall_cons. split; eauto. eexists. reflexivity.
             edestruct (gen_spec_mu_lts_co (ActIn b) (s1' ++ s2'))
               as (w & hlw & heqw).
             eapply lts_oba_output_deter_inv; try eassumption.
             transitivity t. eassumption.
             transitivity v. now symmetry.
             transitivity (f (s1' ++ s2')). eassumption. now symmetry.
             eapply Forall_cons. split; eauto. eexists. reflexivity.
    + right.
      destruct (gen_spec_out_lts_mu_uniq l); subst.
      exists [], s'. repeat split; simpl; eauto with mdb.
      reflexivity. now eapply Forall_nil.
Qed.

Lemma inversion_gen_mu_gen_conv
  `{M1 : LtsOba A L, !Good A L good, !gen_spec_conv f} s μ p :
  f s ⟶[μ] p ->
  good p \/ ∃ s1 s2, s = s1 ++ co μ :: s2 /\ p ⋍ f (s1 ++ s2) /\ are_inputs s1.
Proof.
  intros. eapply inversion_gen_mu; eauto.
  intros. left. eapply gen_spec_conv_nil_stable_mu; eauto.
Qed.

Lemma inversion_gen_mu_gen_acc
  `{M1 : LtsOba A L, !Good A L good, !gen_spec_acc f} s μ p O :
  f O s ⟶[μ] p ->
  good p \/ ∃ s1 s2, s = s1 ++ co μ :: s2 /\ p ⋍ f O (s1 ++ s2) /\ are_inputs s1.
Proof.
  intros. eapply inversion_gen_mu; eauto.
  intros. right. intros.
  eapply gen_spec_acc_nil_lts_inp_good; eauto.
Qed.

Lemma inversion_gen_tau
  `{M1 : LtsOba A L, !Good A L good, !gen_spec f} s q :
  (f [] ↛ \/ (forall e, f [] ⟶ e -> good e)) ->
  (forall μ, f [] ↛[μ] \/ (forall e, f [] ⟶[μ] e -> good e)) ->
  f s ⟶ q ->
  good q \/ (∃ μ s1 s2 s3, s = s1 ++ [μ] ++ s2 ++ [co μ] ++ s3
                          /\ q ⋍ f (s1 ++ s2 ++ s3)
                          /\ is_input μ
                          /\ are_inputs s1 /\ are_inputs s2).
Proof.
  revert q. induction s as [|μ s']; intros q h1 h2 l.
  - destruct h1; eauto. now eapply lts_stable_spec2 in H1; eauto.
  - destruct μ.
    + edestruct (gen_spec_mu_lts_co (ActIn a) s') as (r & hlr & heqr).
      destruct (lts_oba_output_tau hlr l) as [(r1 & l1 & (r2 & l2 & heq))|].
      ++ destruct (eq_spec (f s') r1 τ) as (v & hlv & heqv).
         exists r. split; eauto with mdb. now symmetry.
         destruct (IHs' _ h1 h2 hlv).
         +++ left.
             eapply good_preserved_by_lts_output_converse. eassumption.
             eapply good_preserved_by_eq. eassumption.
             etrans. eapply heqv. now symmetry.
         +++ right.
             destruct H1 as (μ & s1 & s2 & s3 & eq0 & eq1 & hi & his1 & his2).
             subst.
             exists μ, (ActIn a :: s1), s2, s3. cbn.
             repeat split; eauto.
             ++++
               edestruct (gen_spec_mu_lts_co (ActIn a)) as (w & hlw & heqw).
               eapply lts_oba_output_deter_inv. eassumption.
               eassumption.
               etrans. eassumption.
               etrans. symmetry. eapply heqv.
               etrans. eassumption.
               now symmetry.
             ++++ eapply Forall_cons; split; eauto. eexists. reflexivity.
      ++ assert (neq : ActIn a <> ActOut a) by inversion 1.
         destruct H1 as (q' & l' & heq).
         edestruct (lts_oba_output_commutativity hlr l')
           as (v & hlv & (t & l4 & heq4)).
         edestruct (lts_oba_output_confluence neq hlr hlv)
           as (r' & l3 & (t' & l4' & heq4')).
         destruct (eq_spec (f s') r' (ActExt $ ActIn a)) as (t0 & hlt0 & heqt0).
         exists r. split. now symmetry. eassumption.
         destruct (inversion_gen_mu _ _ _ h2 hlt0)
           as [hg | (s1 & s2 & eq1 & eq2 & his)]. subst.
         +++ left.
             eapply good_preserved_by_eq. eassumption.
             etrans. eauto.
             transitivity t'. now symmetry.
             symmetry. transitivity t.
             transitivity q'; now symmetry.
             eapply lts_oba_output_deter; eauto.
         +++ right. exists (ActIn a), [], s1, s2. repeat split; simpl; subst; eauto.
             ++++ etrans. symmetry. eassumption.
                  etrans. symmetry. eassumption.
                  symmetry.
                  etrans. symmetry. eassumption.
                  etrans. eapply heqt0.
                  etrans. symmetry. eapply heq4'.
                  eapply lts_oba_output_deter; eassumption.
             ++++ eexists. reflexivity.
             ++++ now eapply Forall_nil.
    + left. now eapply gen_spec_out_lts_tau_good in l.
Qed.

Lemma inversion_gen_tau_gen_conv
  `{M1 : LtsOba A L, !Good A L good, !gen_spec_conv f} s q :
  f s ⟶ q ->
  good q \/ (∃ μ s1 s2 s3, s = s1 ++ [μ] ++ s2 ++ [co μ] ++ s3
                          /\ q ⋍ f (s1 ++ s2 ++ s3)
                          /\ is_input μ /\ are_inputs s1 /\ are_inputs s2).
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  right. eapply gen_spec_conv_nil_lts_tau_good.
  intro μ. left. eapply gen_spec_conv_nil_stable_mu.
Qed.

Lemma inversion_gen_tau_gen_acc
  `{M1 : LtsOba A L, !Good A L good, !gen_spec_acc f} s O q :
  f O s ⟶ q ->
  good q \/ (∃ μ s1 s2 s3, s = s1 ++ [μ] ++ s2 ++ [co μ] ++ s3
                          /\ q ⋍ f O (s1 ++ s2 ++ s3)
                          /\ is_input μ /\ are_inputs s1 /\ are_inputs s2).
Proof.
  intros.
  eapply inversion_gen_tau; eauto.
  left. eapply gen_spec_acc_nil_stable_tau.
  intro μ. right.
  intros. eapply gen_spec_acc_nil_lts_inp_good; eauto.
Qed.

(** Converse implication of the first requirement. *)

Lemma must_if_cnv `{
    @LtsObaFW A L IL LA LOA V,
    @LtsObaFB B L IL LB LOB W, !Good B L good,
    !gen_spec_conv gen_conv} s (p : A) :
  p ⇓ s -> must p (gen_conv s).
Proof.
  revert p.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  intros p hcnv.
  induction (cnv_terminate p s hcnv) as [p hp IHtp].
  apply m_step.
  + eapply gen_spec_ungood.
  + edestruct gen_conv_always_reduces. eauto with mdb.
  + intros p' l. eapply IHtp; [|eapply cnv_preserved_by_lts_tau]; eauto.
  + intros e' l.
    destruct (inversion_gen_tau_gen_conv s e' l)
      as [hu | (ν & s1 & s2 & s3 & eq__s & sc & i0 & i1 & i2)]; eauto with mdb.
    eapply must_eq_client. symmetry. eassumption.
    eapply Hlength.
    ++ subst. rewrite 6 app_length. simpl. lia.
    ++ inversion i0. subst. eapply cnv_annhil; eauto.
  + intros p' e' ν hle hlp.
    destruct (inversion_gen_mu_gen_conv s ν e' hle)
      as [hg | (s1 & s2 & heq & sc & his)]; eauto with mdb.
    rewrite heq in hle.
    eapply (cnv_drop_in_the_middle p s1 s2) in hlp; subst; eauto with mdb.
    eapply must_eq_client. symmetry. eassumption.
    eapply Hlength; subst; eauto with mdb.
    rewrite 2 app_length. simpl. lia.
Qed.

Lemma must_iff_cnv
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !Good B L good, !gen_spec_conv gen_conv}
  (p : A) s : must p (gen_conv s) <-> p ⇓ s.
Proof. split; [eapply cnv_if_must | eapply must_if_cnv]; eauto. Qed.

Lemma completeness1 `{
    @LtsObaFW A L IL LA LOA V,
    @LtsObaFW C L IL LC LOC T,
    @LtsObaFB B L IL LB LOB W, !Good B L good,
    ! gen_spec_conv gen_conv}
  (p : A) (q : C) : p ⊑ q -> p ≼₁ q.
Proof. intros hleq s hcnv. now eapply must_iff_cnv, hleq, must_iff_cnv. Qed.

(** Second requirement for completeness *)

Definition oas `{FiniteLts A L} (p : A) (s : list (ExtAct L)) (hcnv : p ⇓ s) : gset L :=
  let ps : list A := elements (wt_stable_set p s hcnv) in
  ⋃ map lts_outputs ps.

Lemma exists_forall_in {B} (ps : list B) (P : B -> Prop) (Q : B -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : Exists P ps \/ Forall Q ps.
Proof.
  induction ps as [|p ?]. eauto.
  destruct IHps; destruct (h p); eauto; set_solver.
Qed.

Lemma exists_forall_in_gset `{Countable B} (ps : gset B) (P : B -> Prop) (Q : B -> Prop)
  (h : forall p, p ∈ ps -> P p \/ Q p) : (exists p, p ∈ ps /\ P p)\/ (forall p, p ∈ ps -> Q p).
Proof.
  induction ps using set_ind_L. set_solver.
  destruct IHps; destruct (h x); eauto; set_solver.
Qed.

Lemma wt_outputs_subseteq
  `{FiniteLts A L} μ s p q hacnv1 hacnv2 :
  p ⟹{μ} q ->
  map lts_outputs (elements (wt_stable_set q s hacnv1)) ⊆
    map lts_outputs (elements (wt_stable_set p (μ :: s) hacnv2)).
Proof.
  intros.
  intros a in__a.
  assert (wt_stable_set q s hacnv1 ⊆ wt_stable_set p (μ :: s) hacnv2).
  intros t in__t.
  eapply wt_stable_set_spec2.
  eapply wt_stable_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  eapply wt_push_left; eauto.
  set_solver.
Qed.

Lemma lts_tau_outputs_subseteq `{FiniteLts A L} s p q hacnv1 hacnv2 :
  p ⟶ q ->
  map lts_outputs (elements $ wt_stable_set q s hacnv1) ⊆
    map lts_outputs (elements $ wt_stable_set p s hacnv2).
Proof.
  intros.
  intros a in__a.
  assert (wt_stable_set q s hacnv1 ⊆ wt_stable_set p s hacnv2).
  intros t in__t.
  eapply wt_stable_set_spec2.
  eapply wt_stable_set_spec1 in in__t.
  destruct in__t. split; eauto with mdb.
  set_solver.
Qed.

Lemma union_wt_outputs_subseteq `{FiniteLts A L} μ s p q h1 h2 :
    p ⟹{μ} q -> oas q s h1 ⊆ oas p (μ :: s) h2.
Proof.
  intros hw a (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply wt_outputs_subseteq; eauto.
Qed.

Lemma union_outputs_lts_tau_subseteq `{FiniteLts A L} s p q h1 h2 :
  p ⟶ q -> oas q s h1 ⊆ oas p s h2.
Proof.
  intros l a (O & mem1 & mem2)%elem_of_union_list.
  eapply elem_of_union_list.
  exists O. split; eauto. eapply lts_tau_outputs_subseteq; eauto.
Qed.

Lemma aft_output_must_gen_acc
  `{@LtsOba A L IL LA LOA, @LtsOba B L IL LB LOB, !Good B L good, !gen_spec_acc gen_acc}
  (p : A) a s O :
  p ⤓ -> (forall q, p ⟹{ActOut a} q -> must q (gen_acc O s)) -> must p (gen_acc O (ActOut a :: s) : B).
Proof.
  intros tp hmq. induction tp.
  eapply m_step.
  - eapply gen_spec_ungood.
  - edestruct (@gen_spec_out_lts_tau_ex B L); eauto with mdb.
    now destruct gen_spec_acc0.
  - intros. eapply H2. eassumption. intros.
    eauto with mdb.
  - intros e' l. eapply m_now.
    apply (gen_spec_out_lts_tau_good a s e'). eassumption.
  - intros p' e' μ l0 l1.
    eapply gen_spec_out_lts_mu_uniq in l0 as (h1 & h2). subst.
    eapply hmq. eauto with mdb.
Qed.

Lemma gen_acc_tau_ex
  `{M1 : LtsObaFB A L, !Good A L good, !gen_spec_acc f} s1 s2 s3 μ O :
  is_input μ -> are_inputs s1 -> are_inputs s2 ->
  f O (s1 ++ [μ] ++ s2 ++ [co μ] ++ s3) ⟶⋍ f O (s1 ++ s2 ++ s3).
Proof.
  intros.
  assert (f O (s1 ++ [μ] ++ s2 ++ [co μ] ++ s3) ⟶⋍[co μ]
            f O (s1 ++ s2 ++ [co μ] ++ s3)) as (e1 & l1 & heq1).
  eapply (@f_gen_lts_mu_in_the_middle A L _ _ _ _ _ _ (f O) _
            s1 (s2 ++ [co μ] ++ s3) μ); simpl in *; eauto.
  assert (f O (s1 ++ s2 ++ [co μ] ++ s3) ⟶⋍[co (co μ)]
            f O ((s1 ++ s2) ++ s3)) as (e2 & l2 & heq2).
  replace (s1 ++ s2 ++ [co μ] ++ s3) with ((s1 ++ s2) ++ [co μ] ++ s3).
  eapply (@f_gen_lts_mu_in_the_middle A L _ _ _ _ _ _ (f O) _
            (s1 ++ s2) s3 (co μ)); simpl in *; eauto.
  unfold are_inputs. eapply Forall_app; eauto.
  now rewrite <- app_assoc.
  rewrite co_involution in l2.
  destruct H2 as (a & eq). subst. simpl in *.
  edestruct (eq_spec e1 e2) as (e' & l' & heq'). eauto.
  destruct (lts_oba_fb_feedback l1 l') as (t & lt & heqt); eauto.
  exists t. split; eauto.
  rewrite <- app_assoc in heq2.
  transitivity e'. eauto.
  transitivity e2; eauto.
Qed.

Lemma must_f_gen_a_subseteq_output
  `{@LtsObaFB B L IL LB LOB W, !Good B L good, !gen_spec_acc gen_acc} s e a O1 :
  gen_acc O1 s ⟶[ActOut a] e -> forall O2, O1 ⊆ O2 -> exists t, gen_acc O2 s ⟶[ActOut a] t.
Proof.
  revert e O1.
  induction s as [|μ s']; intros e O1 l O2 hsub.
  + exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_out. eauto.
  + destruct μ as [b|b].
    ++ edestruct
        (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O1) _ (ActIn b) s')
        as (e1 & hle1 & heqe1). simpl in hle1.
       edestruct
         (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActIn b) s')
         as (e2 & hle2 & heqe2). simpl in hle2.
       destruct (decide (a = b)); subst; eauto.
       assert (neq : ActOut a ≠ ActOut b) by now inversion 1.
       destruct (lts_oba_output_confluence neq hle1 l) as
         (r1 & l1 & r2 & l2 & heq).
       edestruct (eq_spec (gen_acc O1 s') r1) as (e' & hle' & heqe').
       symmetry in heqe1. eauto.
       eapply IHs' in hle' as (t & hlt).
       edestruct (eq_spec e2 t) as (e2' & hle2' & heqe2'). eauto.
       edestruct (lts_oba_output_commutativity hle2 hle2') as (v & l3 & l4).
       eauto with mdb. eassumption.
    ++ edestruct
         (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActOut b) s')
         as (r' & hl' & heqr').
       edestruct (gen_spec_out_lts_mu_uniq l); set_solver.
Qed.

Lemma must_f_gen_a_subseteq_input
  `{@LtsObaFB B L IL LB LOB W, !Good B L good, !gen_spec_acc gen_acc} s e a O1 :
  gen_acc O1 s ⟶[ActIn a] e -> forall O2, O1 ⊆ O2 -> exists t, gen_acc O2 s ⟶[ActIn a] t.
Proof.
  revert e O1.
  induction s as [|μ s']; intros e O1 l O2 hsub.
  + now eapply gen_spec_acc_nil_mu_inv, hsub, gen_spec_acc_nil_mem_lts_inp in l.
  + destruct μ as [b|b].
    ++ edestruct
        (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O1) _ (ActIn b) s')
        as (r & hl & heqr). simpl in hl.
       assert (neq : ActIn a ≠ ActOut b) by now inversion 1.
       destruct (lts_oba_output_confluence neq hl l) as
         (r1 & l1 & r2 & l2 & heq).
       edestruct (eq_spec (gen_acc O1 s') r1) as (e' & hle' & heqe').
       symmetry in heqr. eauto.
       eapply IHs' in hle' as (t & hlt).
       edestruct
         (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActIn b) s')
         as (r' & hl' & heqr'). simpl in hl'.
       edestruct (eq_spec r' t) as (e2 & hle2 & heqe2). eauto.
       edestruct (lts_oba_output_commutativity hl' hle2) as (v & l3 & l4).
       eauto with mdb. eassumption.
    ++ edestruct
         (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActOut b) s')
         as (r' & hl' & heqr').
       edestruct (gen_spec_out_lts_mu_uniq l); eauto. subst.
       assert (a = b) by now inversion H1. subst. eauto.
Qed.

Lemma must_f_gen_a_subseteq_tau
  `{@LtsObaFB B L IL LB LOB W, !Good B L good, !gen_spec_acc gen_acc}
  s e O1 : gen_acc O1 s ⟶ e -> forall O2, O1 ⊆ O2 -> exists t, gen_acc O2 s ⟶ t.
Proof.
  revert e O1.
  induction s as [|μ s']; intros e O1 l O2 hsub.
  + exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
  + destruct μ as [a|a].
    ++ edestruct
        (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O1) _ (ActIn a) s')
        as (r & hl & heqr). simpl in hl.
       destruct (lts_oba_output_tau hl l) as [(r1 & l1 & (r2 & l2 & heq))|].
       +++ edestruct (eq_spec (gen_acc O1 s') r1) as (e' & hle' & heqe').
           symmetry in heqr. eauto.
           eapply IHs' in hle' as (t & hlt).
           edestruct
             (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActIn a) s')
             as (r' & hl' & heqr'). simpl in hl'.
           edestruct (eq_spec r' t) as (e2 & hle2 & heqe2). eauto.
           edestruct (lts_oba_output_commutativity hl' hle2) as (v & l3 & l4).
           eauto with mdb. eassumption.
       +++ edestruct H0 as (r' & hl' & heq').
           edestruct (eq_spec (gen_acc O1 s') r') as (t & hlt & heqt).
           symmetry in heqr. eauto.
           edestruct (must_f_gen_a_subseteq_input s' t a O1 hlt O2 hsub).
           edestruct
             (@gen_spec_mu_lts_co B L _ _ _ _ _ (gen_acc O2) _ (ActIn a) s')
             as (u & hlu & hequ).
           edestruct (eq_spec u x) as (t' & hlt' & heqt'). eauto.
           edestruct (lts_oba_fb_feedback hlu hlt'); eauto.
           firstorder.
    ++ eapply gen_spec_out_lts_tau_ex.
Qed.

Lemma must_f_gen_a_subseteq_nil
  `{@Lts A L IL, @LtsObaFB B L IL LB LOB W, !Good B L good, !gen_spec_acc gen_acc}
  (p : A) O1 : must p (gen_acc O1 []) -> forall O2, O1 ⊆ O2 -> must p (gen_acc O2 []).
Proof.
  intros hm.
  assert (hpt : p ⤓)
    by now (eapply must_terminate_ungood, gen_spec_ungood; eauto).
  induction hpt. dependent induction hm; intros O2 hsub.
  - now eapply gen_spec_ungood in H1.
  - eapply m_step; eauto with mdb.
    + eapply gen_spec_ungood.
    + destruct ex as ((p' & e') & l').
      inversion l'; subst.
      +++ eauto with mdb.
      +++ exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
      +++ destruct α1 as [[b|b]|]; destruct α2 as [[a|a]|]; inversion eq; subst.
          exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_out; eauto.
          eapply gen_spec_acc_nil_mu_inv, hsub, gen_spec_acc_nil_mem_lts_inp
            in l2 as (e & l).
          eauto with mdb.
    + intros e l.
      exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
    + intros p' e' μ l1 l2.
      eapply gen_spec_acc_nil_lts_inp_good in l1. eauto with mdb.
Qed.

Lemma must_f_gen_a_subseteq
  `{@Lts A L IL,
    @LtsObaFB B L IL LB LOB W, !Good B L good,
    !gen_spec_acc gen_acc} s (p : A) O1 :
  must p (gen_acc O1 s) -> forall O2, O1 ⊆ O2 -> must p (gen_acc O2 s).
Proof.
  revert p O1.
  induction s
    as (s & Hlength) using
         (well_founded_induction (wf_inverse_image _ nat _ length Nat.lt_wf_0)).
  destruct s as [|ν s']; intros p O1 hm O2 hsub; subst.
  - eapply must_f_gen_a_subseteq_nil; eauto.
  - assert (htp : p ⤓) by (eapply must_terminate_ungood, gen_spec_ungood; eauto).
    induction htp.
    inversion hm. now eapply gen_spec_ungood in H3.
    eapply m_step; eauto with mdb.
    + eapply gen_spec_ungood.
    + destruct ex as (t & l). inversion l; subst; eauto with mdb.
      ++ eapply must_f_gen_a_subseteq_tau in l0 as (e & hle); eauto with mdb.
      ++ destruct α1 as [[b|b]|]; destruct α2 as [[a|a]|]; inversion eq; subst.
         eapply must_f_gen_a_subseteq_output in l2 as (t & hl); eauto with mdb.
         eapply must_f_gen_a_subseteq_input in l2 as (t & hl); eauto with mdb.
    + intros e' l.
      edestruct inversion_gen_tau_gen_acc as [|H3]; eauto with mdb.
      destruct H3 as (μ & s1 & s2 & s3 & heqs & sc & himu & his1 & his2).
      eapply (must_eq_client p (gen_acc O2 (s1 ++ s2 ++ s3))). now symmetry.
      edestruct (gen_acc_tau_ex s1 s2 s3 μ O1) as (t & hlt & heqt); eauto.
      eapply Hlength; eauto.
      ++ rewrite heqs, 6 app_length. simpl. lia.
      ++ eapply must_eq_client. eapply heqt. eapply et. now rewrite heqs.
    + intros p' e' μ l1 l2.
      edestruct inversion_gen_mu_gen_acc as [|H3]; eauto with mdb.
      destruct H3 as (s1 & s2 & heqs & heq & his1).
      eapply must_eq_client. symmetry. eassumption.
      edestruct @f_gen_lts_mu_in_the_middle as (t & l & heq'); eauto.
      now destruct gen_spec_acc0.
      eapply Hlength. rewrite heqs.
      rewrite 2 app_length. simpl. lia.
      eapply must_eq_client. eapply heq'.
      eapply com. rewrite heqs. eassumption.
      now rewrite co_involution. eassumption.
Qed.

Lemma must_gen_acc_stable
  `{@LtsOba A L IL LA LOA, @LtsOba B L IL LB LOB, !Good B L good, !gen_spec_acc gen_acc}
  (p : A) O : p ↛ -> must p (gen_acc (lts_outputs p ∖ O) []) \/ lts_outputs p ⊆ O.
Proof.
  intros.
  remember (lts_outputs p ∖ O) as D.
  destruct D as [|a D'] using set_ind_L.
  + right. set_solver.
  + left.
    eapply m_step.
    ++ now eapply gen_spec_ungood.
    ++ edestruct (gen_spec_acc_nil_mem_lts_inp ({[a]} ∪ D') a)
         as (t & l0). set_solver.
       assert (mem : a ∈ lts_outputs p). set_solver.
       eapply lts_outputs_spec2 in mem as (r & l).
       exists (r, t).
       eapply (ParSync (ActExt $ ActOut a) (ActExt $ ActIn a)); simpl; eauto.
    ++ intros p' l'. exfalso. eapply (@lts_stable_spec2 A); eauto with mdb.
    ++ intros e' l'. exfalso.
       eapply (@lts_stable_spec2 B L _ _ (gen_acc ({[a]} ∪ D') []) τ); eauto with mdb.
       eapply gen_spec_acc_nil_stable_tau.
    ++ intros p' e' μ l0 l1.
       destruct μ.
       eapply gen_spec_acc_nil_lts_inp_good in l0. eauto with mdb.
       exfalso.
       eapply (@lts_stable_spec2 B); eauto with mdb.
       eapply gen_spec_acc_nil_stable_out.
Qed.

Lemma must_gen_a_with_nil
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !Good B L good,
    !gen_spec_acc gen_acc} (p : A) (hcnv : p ⇓ []) O :
  (exists p', p ⟹ p' /\ lts_stable p' τ /\ lts_outputs p' ⊆ O)
  \/ must p (gen_acc (oas p [] hcnv ∖ O) []).
Proof.
  induction (cnv_terminate p [] hcnv) as (p, hpt, ihhp).
  destruct (decide (lts_stable p τ)) as [st | (p' & l)%lts_stable_spec1].
  - destruct (must_gen_acc_stable p O st).
    + right. unfold oas.
      rewrite wt_stable_set_stable_singleton, elements_singleton; eauto.
      simpl. rewrite union_empty_r_L. set_solver.
    + left. eauto with mdb.
  - assert
      (h : ∀ q,
          q ∈ lts_tau_set p ->
          (exists p', q ⟹ p' ∧ lts_stable p' τ ∧ lts_outputs p' ⊆ O) ∨
            (exists h, must q (gen_acc (oas q [] h ∖ O) []))).
    intros q l'%lts_tau_set_spec.
    destruct (hpt q l') as (hq).
    edestruct (ihhp q l') as [hl | hr].
    now left. right. exists (cnv_nil _ (tstep q hq)). eauto.
    destruct (@exists_forall_in A (lts_tau_set p) _ _ h).
    + eapply Exists_exists in H1 as (t & l'%lts_tau_set_spec & t' & w & st & sub).
      left. exists t'. eauto with mdb.
    + right. eapply m_step.
      ++ eapply gen_spec_ungood.
      ++ eauto with mdb.
      ++ intros p0 l0%lts_tau_set_spec.
         eapply Forall_forall in H1 as (h0 & hm).
         eapply must_f_gen_a_subseteq; eauto.
         eapply difference_mono_r, union_outputs_lts_tau_subseteq; eauto.
         now eapply lts_tau_set_spec. eassumption.
      ++ intros e' l'. exfalso.
         eapply (@lts_stable_spec2 B). eauto. eapply gen_spec_acc_nil_stable_tau.
      ++ intros p0 e0 μ le%gen_spec_acc_nil_lts_inp_good lp; eauto with mdb.
Qed.

Lemma must_gen_a_with_s
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !Good B L good, !gen_spec_acc gen_acc} s (p : A) (hcnv : p ⇓ s) O :
  (exists p', p ⟹[s] p' /\ lts_stable p' τ /\ lts_outputs p' ⊆ O) \/ must p (gen_acc (oas p s hcnv ∖ O) s).
Proof.
  revert p hcnv O.
  induction s as [|μ s'].
  - eapply must_gen_a_with_nil.
  - intros p hcnv O.
    set (ps := wt_set_mu p μ s' hcnv).
    inversion hcnv; subst.
    assert (hcnv0 : forall p', p' ∈ ps -> p' ⇓ s') by (intros ? mem%wt_set_mu_spec1; eauto).
    assert (he : ∀ p', p' ∈ ps ->
                      (exists pr p0, p0 ∈ wt_stable_set p' s' pr ∧ lts_outputs p0 ⊆ O)
                      ∨ (exists h, must p' (gen_acc (oas p' s' h ∖ O) s'))).
    intros p' mem.
    destruct (IHs' p' (hcnv0 _ mem) O) as [(r & w & st & sub)| hm].
    left. eapply wt_set_mu_spec1 in mem.
    exists (H5 _ mem), r. split; [eapply wt_stable_set_spec2 |]; eauto.
    right. eauto.
    destruct (exists_forall_in_gset ps _ _ he).
    + left. destruct H1
        as (p1 & ?%wt_set_mu_spec1 & ? & r & (? & ?)%wt_stable_set_spec1 & ?).
      exists r. repeat split; eauto. eapply wt_push_left; eauto.
    + right. destruct μ. inversion hcnv; subst.
      ++ destruct (lts_oba_fw_forward p a) as (p' & l0 & l1).
         assert (gen_acc (oas p (ActIn a :: s') hcnv ∖ O) (ActIn a :: s')
                   ⟶⋍[co $ ActIn a] gen_acc (oas p (ActIn a :: s') hcnv ∖ O) s')
           as (e' & hle' & heqe') by eapply gen_spec_mu_lts_co.
         eapply must_output_swap_l_fw. eauto. eauto.
         eapply (must_eq_client _ _ _ (symmetry heqe')).
         edestruct (H1 p') as (? & hm).
         eapply wt_set_mu_spec2; eauto with mdb.
         eapply must_f_gen_a_subseteq, difference_mono_r, union_wt_outputs_subseteq; eauto with mdb.
      ++ eapply aft_output_must_gen_acc; eauto.
         intros p' hw. edestruct (H1 p') as (? & hm).
         eapply wt_set_mu_spec2; eauto.
         eapply must_f_gen_a_subseteq, difference_mono_r, union_wt_outputs_subseteq; eauto with mdb.
Qed.

Lemma not_must_gen_a_without_required_output
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    !Good B L good, !gen_spec_acc gen_acc} (q q' : A) s O :
  q ⟹[s] q' -> q' ↛ -> ¬ must q (gen_acc (O ∖ lts_outputs q') s).
Proof.
  intros wt hst.
  dependent induction wt; intros hm.
  - inversion hm; subst.
    ++ contradict H1. eapply gen_spec_ungood.
    ++ destruct ex as (t & l). inversion l; subst.
       +++ eapply (lts_stable_spec2 p τ); eauto with mdb.
       +++ exfalso. eapply lts_stable_spec2, gen_spec_acc_nil_stable_tau; eauto.
       +++ destruct α1 as [[b|b]|]; destruct α2 as [[a|a]|]; inversion eq; subst.
           eapply lts_stable_spec2, gen_spec_acc_nil_stable_out; eauto.
           eapply gen_spec_acc_nil_mu_inv in l2.
           eapply lts_outputs_spec1 in l1. set_solver.
  - eapply (IHwt hst), (must_preserved_by_lts_tau_srv p q _ hm l).
  - eapply (IHwt hst).
    assert (gen_acc (O ∖ lts_outputs t) (μ :: s) ⟶⋍[co μ]
              gen_acc (O ∖ lts_outputs t) s) as (e' & hle' & heqe').
    by eapply gen_spec_mu_lts_co.
    eapply must_eq_client; eauto.
    inversion hm; subst. now eapply gen_spec_ungood in H1. destruct μ; eauto.
Qed.

Lemma completeness2
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    @LtsObaFW C L IL LC LOC VC,
    !FiniteLts A L, !FiniteLts C L, !Good B L good, !gen_spec_acc gen_acc}
  (p : A) (q : C) : p ⊑ q -> p ≼₂ q.
Proof.
  intros hpre s q' hacnv w st.
  destruct (must_gen_a_with_s s p hacnv (lts_outputs q')) as [|hm] ; eauto.
  eapply hpre in hm. contradict hm.
  eapply not_must_gen_a_without_required_output; set_solver.
Qed.

Lemma completeness_fw
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFW B L IL LB LOB W, @LtsObaFB C L IL LC LOC VC,
    !FiniteLts A L, !FiniteLts B L, !FiniteLts C L, !Good C L good,
    !gen_spec_conv gen_conv, !gen_spec_acc gen_acc}
  (p : A) (q : B) : p ⊑ q -> p ≼ q.
Proof. intros. split. now apply completeness1. now apply completeness2. Qed.

Lemma completeness
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, @LtsObaFB C L IL LC LOC VC,
    !FiniteLts A L, !FiniteLts B L, !FiniteLts C L, !Good C L good,
    !gen_spec_conv gen_conv, !gen_spec_acc gen_acc}
  (p : A) (q : B) : p ⊑ q -> p ▷ ∅ ≼ q ▷ ∅.
Proof.
  intros hctx.
  eapply completeness_fw.
  now rewrite <- Lift.lift_fw_ctx_pre.
Qed.
