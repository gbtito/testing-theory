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

Require Import Coq.Program.Equality.
From stdpp Require Import base countable finite gmap list finite base decidable finite gmap gmultiset.
From Must Require Import TransitionSystems Must.

Lemma woutpout_preserves_good `{LtsObaFB B L, !Good B L good }
  e m e': good e -> strip e m e' -> good e'.
Proof.
  intros. induction H4; eauto.
  eapply IHstrip. eapply good_preserved_by_lts_output; eauto.
Qed.

Lemma woutpout_preserves_good_converse `{LtsObaFB B L, !Good B L good }
  e m e': good e' -> strip e m e' -> good e.
Proof.
  intros. induction H4; eauto.
  eapply good_preserved_by_lts_output_converse. eassumption.
  now eapply IHstrip.
Qed.

Lemma strip_eq `{@LtsOba A L IL LA LOA} {e e' m} :
  strip e m e' -> forall r, eq_rel r e -> exists r', strip r m r' /\ eq_rel r' e'.
Proof.
  intro w.
  dependent induction w; intros r heq.
  - exists r. split. constructor. assumption.
  - destruct (eq_spec r p2 (ActExt $ ActOut a)) as (r0 & l0 & heq0). eauto.
    destruct (IHw r0 heq0) as (r' & hwo' & heq').
    exists r'. split. eapply strip_step; eassumption. eassumption.
Qed.

Lemma woutpout_preserves_mu `{LtsOba A L}
  {p q m t α} : strip p m q -> q ⟶{α} t -> exists r t', p ⟶{α} r /\ strip r m t' /\ eq_rel t t'.
Proof.
  intros. induction H2; eauto.
  exists t, t. repeat split; eauto. constructor. reflexivity.
  eapply IHstrip in H3 as (r & t' & l & hwo & heq).
  edestruct (lts_oba_output_commutativity H2 l) as (u & l1 & (r' & lr' & heqr')).
  edestruct (strip_eq hwo _ heqr') as (t0 & hwo0 & heq0).
  exists u, t0. repeat split; eauto. eapply strip_step; eassumption.
  etrans. eassumption. now symmetry.
Qed.


Lemma woutpout_delay_inp `{LtsOba A L} {p q m t a} : strip p m q -> p ⟶[ActIn a] t -> exists r, q ⟶[ActIn a] r.
Proof.
  intros. revert t H3.
  induction H2; eauto; intros.
  assert (neq : ActIn a ≠ ActOut a0) by now inversion 1.
  edestruct (lts_oba_output_confluence neq H2 H4) as (r & l1 & l2). eauto.
Qed.

Lemma woutpout_delay_tau `{LtsOba A L} {p q m t} :
  strip p m q -> p ⟶ t -> (exists a r t, p ⟶[ActOut a] r /\ q ⟶[ActIn a] t) \/ (exists r, q ⟶ r).
Proof.
  intros. revert t H3.
  induction H2; eauto; intros.
  edestruct (lts_oba_output_tau H2 H4) as [(r & l1 & l2)|].
  + eapply IHstrip in l1 as [(b & t' & r' & l3 & l4)|].
    edestruct (lts_oba_output_commutativity H2 l3) as (z & l6 & l7).
    left. eauto. right. eauto.
  +
  destruct H5 as (r & hlr & heq).
  left. exists a. eapply woutpout_delay_inp in hlr as (u & lu); eauto.
Qed.

Lemma conv `{Lts A L} (p : A) : p ⤓ -> (p, ∅) ⤓.
Proof.
  intro ht.
  induction ht.
  destruct (lts_stable_decidable (p, ∅) τ).
  - eapply tstep. intros (p', m') l'.
    apply lts_stable_spec2 in l. now exfalso. eauto with mdb.
  - eapply tstep. intros (p', m') l'.
    inversion l'; subst.
    + eapply H2; eauto.
    + exfalso. eapply (gmultiset_elem_of_empty a).
      replace ∅ with ({[+ a +]} ⊎ m'). multiset_solver.
Qed.

Lemma neq_multi_nil `{Countable A} (m : gmultiset A) a : {[+ a +]} ⊎ m ≠ ∅.
Proof. multiset_solver. Qed.

Lemma gmultiset_not_elem_of_multiplicity `{Countable A} x (g : gmultiset A) :
  x ∉ g <-> multiplicity x g = 0.
Proof. multiset_solver. Qed.

Lemma aux0 `{LtsOba A L} {e e' m} :
  forall a, a ∈ m -> strip e m e' -> exists e', e ⟶[ActOut a] e'.
Proof.
  intros a mem w.
  dependent induction w.
  - multiset_solver.
  - eapply gmultiset_elem_of_disj_union in mem as [here | there].
    + eapply gmultiset_elem_of_singleton in here. subst. firstorder.
    + eapply IHw in there as (q & l).
      edestruct (lts_oba_output_commutativity H2 l) as (u & l2 & l3). eauto.
Qed.

Lemma gmultiset_eq_drop_l `{Countable A} (m1 m2 m3 : gmultiset A) : m1 ⊎ m2 = m1 ⊎ m3 -> m2 = m3.
Proof. by multiset_solver. Qed.

Lemma aux3_ `{@LtsOba A L IL LA LOA} {e e' m a} :
  strip e ({[+ a +]} ⊎ m) e' -> forall r, e ⟶[ActOut a] r -> exists t, strip r m t /\ eq_rel t e'.
Proof.
  intro w.
  dependent induction w.
  - multiset_solver.
  - intros r l.
    destruct (decide (a = a0)); subst.
    + assert (eq_rel p2 r) by (eapply lts_oba_output_deter; eassumption).
      eapply gmultiset_eq_drop_l in x. subst.
      eapply strip_eq. eassumption. symmetry. assumption.
    + assert (m0 = {[+ a +]} ⊎ m ∖ {[+ a0 +]}) by multiset_solver.
      assert (ActOut a ≠ ActOut a0) by set_solver.
      edestruct (lts_oba_output_confluence H2 H0 l) as (t0 & l0 & (r1 & l1 & heq1)).
      eapply IHw in H1 as (t & hwo & heq); eauto.
      assert (mem : a0 ∈ m) by multiset_solver.
      eapply gmultiset_disj_union_difference' in mem. rewrite mem.
      edestruct (strip_eq hwo r1 heq1) as (t2 & hw2 & heq2).
      exists t2. split. eapply strip_step. eassumption. eassumption.
      etrans; eassumption.
Qed.

Lemma must_output_swap_l_fw_eq
  `{@LtsObaFW A L LB R M K, @LtsObaFB B L LB T Y V, !Good B L good}
  (p1 p2 : A) (e1 e2 : B) (a : L) :
  p1 ⟶⋍[ActOut a] p2 -> e1 ⟶⋍[ActOut a] e2 -> must p1 e2 -> must p2 e1.
Proof.
  intros lp le hm. revert e1 p2 lp le.
  induction hm as [|p1 e2 nh ex Hpt IHpt Het IHet Hcom IHcom]; intros e1 p2 lp le.
  - eapply m_now.
    destruct le as (e' & hle' & heqe').
    eapply good_preserved_by_lts_output_converse. eassumption.
    eapply good_preserved_by_eq. eapply H1. now symmetry.
  - eapply m_step.
    + intro h.
      destruct le as (e' & hle' & heqe').
      eapply nh, (good_preserved_by_eq e' e2); eauto.
      eapply good_preserved_by_lts_output; eauto.
    + destruct ex as ((p' & e') & l).
      inversion l; subst.
      destruct lp as (p0 & hlp0 & heqp0).
      ++ destruct (lts_oba_output_tau hlp0 l0) as [(t & l1 & l2) | m].
         +++ edestruct (eq_spec p2 t τ) as (p2' & hlp2' & heqp2').
             exists p0. split. now symmetry. eassumption.
             exists (p2', e1). eauto with mdb.
         +++ destruct m as (p2' & hl & heq).
             destruct le as (e0 & hle0 & heqe0).
             edestruct (eq_spec p2 p2' (ActExt $ ActIn a)) as (p3 & hlp3 & heqp3).
             exists p0. split. now symmetry. eassumption.
             exists (p3, e0). eapply ParSync; try eassumption. now simpl.
      ++ destruct le as (e0 & hle0 & heqe0).
         edestruct (eq_spec e0 e' τ) as (e3 & hle3 & heqe3).
         exists e2. split. now symmetry. eassumption.
         destruct (lts_oba_output_commutativity hle0 hle3) as (t & l1 & l2).
         destruct lp as (p0 & hlp0 & heqp0).
         eauto with mdb.
      ++ destruct α1 as [μ |].
         +++ destruct (decide (μ = ActOut a)); subst.
             ++++ destruct lp as (p0 & hlp0 & heqp0), le as (e0 & hle0 & heqe0).
                  subst. destruct α2. destruct μ.
                  simpl in eq. subst.
                  edestruct (eq_spec e0 e' (ActExt $ ActIn a0)) as (e3 & hle3 & heqe3).
                  exists e2. split. now symmetry. eassumption.
                  destruct (lts_oba_fb_feedback hle0 hle3) as (e4 & hle4 & heqe4).
                  eauto with mdb. now exfalso. now exfalso.
             ++++ destruct lp as (p0 & hlp0 & heqp0).
                  destruct le as (e0 & hle0 & heqe0).
                  destruct (lts_oba_output_confluence n hlp0 l1) as (t & l3 & l4).
                  edestruct (eq_spec e0 e' (α2)) as (e3 & hle3 & heqe3).
                  exists e2. split. now symmetry. eassumption.
                  destruct (lts_oba_output_commutativity hle0 hle3) as (r & l5 & l6).
                  edestruct (eq_spec p2 t (ActExt μ)) as (p3 & hlp3 & heqp3).
                  exists p0. split. now symmetry. eassumption.
                  eauto with mdb.
         +++ now exfalso.
    + intros p' l.
      destruct lp as (p0 & hlp0 & heqp0).
      edestruct (eq_spec p0 p' τ) as (p3 & hlp3 & heqp3).
      by (exists p2; split; [now symmetry | eassumption]).
      destruct (lts_oba_output_commutativity hlp0 hlp3) as (t & l1 & l2).
      destruct l2 as (p4 & hlp4 & heqp4).
      eapply must_eq_server. etrans. eapply heqp4. eassumption.
      eapply IHpt; eauto with mdb. exists p4. split. eassumption. reflexivity.
    + intros e' l.
      destruct le as (e0 & hle0 & heqe0).
      destruct (lts_oba_output_tau hle0 l) as [(t & l0 & l1)|].
      ++ destruct (eq_spec e2 t τ) as (v & hlv & heqv).
         exists e0. split; eauto. now symmetry.
         eapply IHet. eassumption. eassumption.
         destruct l1 as (e3 & hle3 & heqe3).
         exists e3. split; eauto. etrans. eassumption. now symmetry.
      ++ destruct H1 as (u & hlu & hequ).
         destruct (eq_spec e2 u (ActExt $ ActIn a)) as (v & hlv & heqv).
         exists e0. split. now symmetry. eassumption.
         eapply must_eq_client. etrans. eapply heqv. eassumption.
         destruct lp as (p0 & hlp0 & heqp0).
         eapply must_eq_server. eassumption.
         eapply Hcom; eassumption.
    + intros p' e' μ l1 l2.
      destruct lp as (p0 & hlp0 & heqp0).
      destruct le as (e0 & hle0 & heqe0).
      destruct (decide (μ = ActOut a)); subst; simpl in l2.
      ++ edestruct (eq_spec p0 p' (ActExt $ ActIn a)) as (p3 & hlp3 & heqp3).
         exists p2. split. now symmetry. eassumption.
         assert (heqe' : e0 ⋍ e'). eapply lts_oba_output_deter; eassumption.
         destruct (lts_oba_fw_feedback hlp0 hlp3) as [(p3' & hlp3' & heqp3')|].
         +++ eapply must_eq_client. eassumption.
             eapply must_eq_client. symmetry. eapply heqe0.
             eapply must_eq_server. transitivity p3; eassumption.
             eapply Hpt. eassumption.
         +++ eapply (must_eq_client _ e0 e'). eassumption.
             eapply (must_eq_client _ e2 e0). eapply (symmetry heqe0).
             eapply must_eq_server. transitivity p3; eassumption.
             eauto with mdb.
      ++ destruct (lts_oba_output_confluence n hle0 l1) as (t & l3 & l4).
         edestruct (eq_spec p0 p' (ActExt (co μ))) as (p3 & hlp3 & heqp3). eauto with mdb.
         destruct (lts_oba_output_commutativity hlp0 hlp3) as (r & l5 & l6).
         edestruct (eq_spec e2 t (ActExt μ)) as (e3 & hle3 & heqe3).
         exists e0. split. now symmetry. eassumption.
         eapply IHcom. eassumption. eassumption.
         destruct l6 as (p4 & hlp4 & heqp4).
         exists p4. split. eassumption. etrans. eapply heqp4. eassumption.
         destruct l4 as (e4 & hle4 & heqe4).
         exists e4. split. eassumption. etrans. eapply heqe4. now symmetry.
Qed.

Lemma must_output_swap_r_fw_eq
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !Good B L good}
  (p1 p2 : A) (e1 e2 : B) (a : L) :
  p1 ⟶⋍[ActOut a] p2 -> e1 ⟶⋍[ActOut a] e2 -> must p2 e1 -> must p1 e2.
Proof.
  intros lp le hm. revert e2 p1 le lp.
  induction hm as [|p2 e1 nh ex Hpt IHpt Het IHet Hcom IHcom]; intros e2 p1 le lp.
  - eapply m_now.
    destruct le as (e' & hle' & heqe').
    eapply good_preserved_by_eq.
    eapply good_preserved_by_lts_output; eassumption.
    eassumption.
  - destruct lp as (p0 & hlp0 & heqp0).
    destruct le as (e0 & hle0 & heqe0).
    eapply m_step.
    + intro h. eapply nh.
      eapply good_preserved_by_lts_output_converse; eauto.
      eapply good_preserved_by_eq. eapply h. now symmetry.
    + destruct ex as ((p' & e') & l).
      inversion l; subst.
      ++ edestruct (eq_spec p0 p' τ) as (p3 & hlp3 & heqp3).
         exists p2. split. now symmetry. eassumption.
         destruct (lts_oba_output_commutativity hlp0 hlp3) as (t & l1 & l2).
         eauto with mdb.
      ++ destruct (lts_oba_output_tau hle0 l0) as [(t & l1 & l2) | m].
         +++ edestruct (eq_spec e2 t τ) as (e2' & hle2' & heqe2').
             exists e0. split. now symmetry. eassumption.
             exists (p1, e2'). eauto with mdb.
         +++ destruct m as (e2' & hl & heq).
             edestruct (eq_spec e2 e2' (ActExt $ ActIn a)) as (e3 & hle3 & heqe3).
             exists e0. split. now symmetry. eassumption.
             exists (p0, e3). eapply ParSync; try eassumption. now simpl.
      ++ destruct α2.
         +++ destruct (decide (μ = ActOut a)).
             ++++ subst.
                  assert (e0 ⋍ e') by (eapply (lts_oba_output_deter hle0 l2); eauto).
                  destruct α1.
                  destruct μ.
                  simpl in eq. subst.
                  edestruct (eq_spec p0 p' (ActExt $ ActIn a)) as (p3 & hlp3 & heqp3).
                  exists p2. split. now symmetry. eassumption.
                  destruct (lts_oba_fw_feedback hlp0 hlp3) as [(t & hlt & heqt)|]; subst; eauto with mdb.
                  assert (hm : must p' e0) by eauto with mdb.
                  eapply (must_eq_client p' e0 e2) in hm.
                  eapply (must_eq_server p' p1 e2) in hm.
                  assert (¬ good e2).
                  intro hh. eapply nh. eapply good_preserved_by_lts_output_converse.
                  eassumption. eapply good_preserved_by_eq. eassumption.
                  etrans. symmetry. eassumption. eassumption.
                  inversion hm; subst. contradiction. eassumption.
                  etrans. symmetry. eassumption. now symmetry. eassumption.
                  +++++ now exfalso.
                  +++++ now exfalso.
             ++++ destruct (lts_oba_output_confluence n hle0 l2)
                    as (t & l3 & l4).
                  edestruct (eq_spec p0 p' α1) as (p3 & hlp3 & heqp3).
                  exists p2. split. now symmetry. eassumption.
                  destruct (lts_oba_output_commutativity hlp0 hlp3)
                    as (r & l5 & l6).
                  edestruct (eq_spec e2 t (ActExt μ)) as (e3 & hle3 & heqe3).
                  exists e0. split. now symmetry. eassumption.
                  eauto with mdb.
         +++ now destruct α1; exfalso.
    + intros p' l.
      destruct (lts_oba_output_tau hlp0 l) as [(t & l0 & l1)|].
      ++ destruct (lts_oba_output_commutativity hlp0 l0) as (r & hl2 & hl3).
         destruct l1 as (e3 & hle3 & heqe3).
         destruct hl3 as (u & hlu & hequ).
         assert (heq : r ⋍ p'). eapply lts_oba_output_deter_inv; try eassumption.
         etrans. eassumption. now symmetry.
         destruct (eq_spec p' u (ActExt $ ActOut a)) as (v & hlv & heqv).
         exists r. split. now symmetry. eassumption.
         eapply (must_eq_server _ _ _ heq).
         edestruct (eq_spec p2 t τ) as (p3 & hlp3 & heqp3).
         exists p0. split. now symmetry. eassumption.
         eapply IHpt; eauto.
         exists e0. eauto with mdb.
         exists u. split. eassumption. etrans. eapply hequ. now symmetry.
      ++ destruct H1 as (u & hlu & hequ).
         destruct (lts_oba_output_commutativity hlp0 hlu) as (r & hl2 & hl3).
         destruct (eq_spec p2 u (ActExt $ ActIn a)) as (v & hlv & heqv).
         exists p0. split. now symmetry. eassumption.
         eapply must_eq_server. etrans. eapply heqv. eassumption.
         eapply must_eq_client. eassumption.
         eapply Hcom. eassumption. eassumption.
    + intros e' l.
      edestruct (eq_spec e0 e' τ) as (e3 & hle3 & heqe3).
      exists e2. split. now symmetry. eassumption.
      destruct (lts_oba_output_commutativity hle0 hle3) as (t & l1 & l2).
      destruct l2 as (e4 & hle4 & heqe4).
      eapply must_eq_client. etrans. eapply heqe4. eassumption.
      eapply IHet. eassumption. exists e4. split. eassumption. reflexivity.
      exists p0. split. eassumption. eassumption.
    + intros p' e' μ l1 l2.
      destruct (decide (μ = ActIn a)).
      ++ subst. simpl in l2.
         edestruct (eq_spec e0 e' (ActExt $ ActIn a)) as (e3 & hle3 & heqe3).
         exists e2. split. now symmetry. eassumption.
         destruct (lts_oba_fb_feedback hle0 hle3) as (e3' & hle3' & heqe3').
         assert (heqe' : p0 ⋍ p'). eapply lts_oba_output_deter; eassumption.
         eapply must_eq_server. eassumption.
         eapply must_eq_server. symmetry. eapply heqp0.
         eapply must_eq_client. etrans. eapply heqe3'. eassumption.
         eapply Het. eassumption.
      ++ assert (n2 : co μ ≠ ActOut a).
         intro h. eapply n. eapply (f_equal co) in h. simpl in h.
         now rewrite co_involution in h.
         destruct (lts_oba_output_confluence n2 hlp0 l2) as (t & l3 & l4).
         edestruct (eq_spec e0 e' (ActExt μ)) as (e3 & hle3 & heqe3); eauto.
         destruct (lts_oba_output_commutativity hle0 hle3) as (r & l5 & l6).
         edestruct (eq_spec p2 t (ActExt (co μ))) as (p3 & hlp3 & heqp3).
         exists p0. split. now symmetry. eassumption.
         eapply IHcom. eassumption. eassumption.
         destruct l6 as (e4 & hle4 & heqe4).
         exists e4. split. eassumption. etrans. eapply heqe4. eassumption.
         destruct l4 as (p4 & hlp4 & heqp4).
         exists p4. split. eassumption. etrans. eapply heqp4. now symmetry.
Qed.

Lemma must_output_swap_l_fw
  `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !Good B L good}
  (p1 p2 : A) (e1 e2 : B) (a : L) :
  p1 ⟶[ActOut a] p2 -> e1 ⟶[ActOut a] e2 -> must p1 e2 -> must p2 e1.
Proof.
  intros. eapply must_output_swap_l_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma must_output_swap_r_fw
    `{@LtsObaFW A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !Good B L good}
  (p1 p2 : A) (e1 e2 : B) (a : L) :
  p1 ⟶[ActOut a] p2 -> e1 ⟶[ActOut a] e2 -> must p2 e1 -> must p1 e2.
Proof.
  intros.
  eapply must_output_swap_r_fw_eq; eauto; eexists; split; eauto; reflexivity.
Qed.

Lemma nf_must_fw_l
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !FiniteLts A L, !Good B L good}
  m1 m2 (p : A) (e e' : B) : e ⟿{m1} e' -> must (p, m1 ⊎ m2) e' -> must (p, m2) e.
Proof.
  revert p e e' m2.
  induction m1 using gmultiset_ind; intros p e e' m2 hmo hm.
  - inversion hmo; subst.
    now rewrite gmultiset_disj_union_left_id in hm.
    multiset_solver.
  - assert (x ∈ {[+ x +]} ⊎ m1) by multiset_solver.
    eapply aux0 in H1 as (e0 & l0); eauto.
    eapply (aux3_) in hmo as (t & hwo & heq); eauto.
    eapply must_output_swap_l_fw_eq.
    eexists. split. eapply lts_fw_out_mb. reflexivity. exists e0. split. eassumption. reflexivity.
    eapply IHm1. eassumption. eapply must_eq_client. symmetry. eassumption.
    now replace (m1 ⊎ ({[+ x +]} ⊎ m2)) with ({[+ x +]} ⊎ m1 ⊎ m2) by multiset_solver.
Qed.

Lemma nf_must_fw_r
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !FiniteLts A L, !Good B L good}
  (p : A) (e e' : B) m1 m2 : strip e m1 e' -> must (p, m2) e -> must (p, m1 ⊎ m2) e'.
Proof.
  intro hwo. revert p m2.
  dependent induction hwo; intros q m2 hm.
  rename p into e, q into p.
  - rewrite gmultiset_disj_union_left_id. assumption.
  - assert (must (q, {[+ a +]} ⊎ m2) p2).
    inversion hm; subst.
    eapply m_now. eapply good_preserved_by_lts_output; eassumption.
    eapply com. eassumption. simpl. eauto with mdb.
    replace ({[+ a +]} ⊎ m ⊎ m2) with (m ⊎ ({[+ a +]} ⊎ m2)) by multiset_solver.
    eapply IHhwo. eassumption.
Qed.

Lemma nf_must_fw
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !FiniteLts A L, !Good B L good}
  (p : A) (e e' : B) m : strip e m e' -> must (p, m) e' <-> must (p, ∅) e.
Proof.
  intros. split; intro hm.
  - eapply nf_must_fw_l; eauto; now rewrite gmultiset_disj_union_right_id.
  - rewrite <- gmultiset_disj_union_right_id. eapply nf_must_fw_r; eassumption.
Qed.

Lemma lts_oba_mo_strip `{LtsOba A L} p : exists q , strip p (lts_oba_mo p) q.
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

Lemma lts_oba_mo_strip_stable `{LtsOba A L} p q : strip p (lts_oba_mo p) q -> forall a, q ↛[ActOut a].
Proof.
  intros w.
  dependent induction w.
  - intros a.
    destruct (lts_stable_decidable p (ActExt $ ActOut a)); eauto.
    eapply lts_stable_spec1 in n as (q & l).
    eapply lts_outputs_spec1, lts_oba_mo_spec1 in l. multiset_solver.
  - eapply lts_oba_mo_spec2 in H2. rewrite <- x in H2.
    eapply gmultiset_eq_drop_l in H2. eauto.
Qed.

Lemma must_to_must_fw
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !FiniteLts A L,
    !Good B L good}
  (p : A) (e : B) m :
  must p e -> m = lts_oba_mo e -> forall e', strip e m e' -> must (p, m) e'.
Proof.
  intros hm. revert m.
  dependent induction hm; intros m heq e' hmo.
  - eapply m_now. eapply woutpout_preserves_good; eauto.
  - eapply m_step; eauto with mdb.
    + intro hh. destruct nh. eapply woutpout_preserves_good_converse; eauto.
    + destruct ex as (t & l). inversion l; subst.
      ++ exists ((a2, lts_oba_mo e), e'). now eapply ParLeft, lts_fw_p.
      ++ edestruct (woutpout_delay_tau hmo l0).
         destruct H4 as (a & r & t & l1 & l2).
         eapply (lts_outputs_spec1, lts_oba_mo_spec2) in l1.
         exists (p, lts_oba_mo r, t).
         eapply (ParSync (ActExt $ ActOut a) (ActExt $ ActIn a)); simpl; eauto.
         rewrite l1. eapply lts_fw_out_mb; eauto.
         destruct H4 as (r & l1). eauto with mdb.
      ++ destruct α1 as [[b|b]|]; destruct α2 as [[a|a]|]; inversion eq; subst.
         eapply lts_oba_mo_spec2 in l2 as h.
         exists (a2, lts_oba_mo b2, e'). eapply ParLeft.
         rewrite h. eapply lts_fw_com; eauto.
         edestruct (woutpout_delay_inp hmo l2) as (e3 & l3).
         exists (a2, lts_oba_mo e, e3).
         eapply (ParSync (ActExt $ ActOut a) (ActExt $ ActIn a)); simpl; eauto.
         now eapply lts_fw_p.
    + intros (p', m') l.
      inversion l; subst; eauto with mdb.
      assert (mem : a ∈ ({[+ a +]} ⊎ m')) by multiset_solver.
      rewrite <- H6 in hmo.
      eapply (aux0 a) in mem as (e0, l0); eauto.
      eapply (aux3_) in hmo as (t & hwo & heq); eauto.
      eapply must_eq_client. eassumption.
      eapply H3. eassumption. eassumption.
      eapply lts_oba_mo_spec2 in l0.
      eapply (gmultiset_eq_drop_l {[+ a +]}). now rewrite <- l0.
      eassumption.
    + intros e0 l0.
      edestruct (woutpout_preserves_mu hmo l0) as (e1 & t & l & hwo1 & heq1).
      eapply must_eq_client. symmetry. eassumption.
      rewrite <- gmultiset_disj_union_right_id.
      eapply nf_must_fw_r. eassumption.
      destruct (lts_oba_mo_strip e1) as (e2 & hwo2).
      eapply nf_must_fw_l. eapply hwo2.
      rewrite gmultiset_disj_union_right_id.
      eapply H2; eauto with mdb.
    + intros (p', m') e0 μ l1 l2.
      destruct μ; simpl in *.
      ++ inversion l2; subst.
         +++ rewrite <- gmultiset_disj_union_right_id.
             edestruct (woutpout_preserves_mu hmo l1) as (e3 & t & l3 & hwo1 & heq1).
             eapply must_eq_client. symmetry. eassumption.
             eapply nf_must_fw_r. eassumption.
             destruct (lts_oba_mo_strip e3) as (e3' & hwo3').
             eapply nf_must_fw_l. eapply hwo3'.
             rewrite gmultiset_disj_union_right_id.
             eapply H3; eauto with mdb.
         +++ assert (mem : a ∈ lts_oba_mo e). rewrite <- H6. multiset_solver.
             eapply lts_oba_mo_spec1, lts_outputs_spec2 in mem as (u & l).
             set (h := lts_oba_mo_spec2 _ _ _ l).
             rewrite <- H6 in hmo.
             destruct (aux3_ hmo _ l) as (e1' & hwoe1' & heqe1').
             destruct (eq_spec e1' e0 (ActExt $ ActIn a)) as (r & l4 & heq4). eauto.
             edestruct (woutpout_preserves_mu hwoe1' l4) as (e2 & u' & le2 & hwoe2 & hequ').
             destruct (lts_oba_fb_feedback l le2) as (t & hlt & heqt).
             eapply must_eq_client. eassumption.
             rewrite <- gmultiset_disj_union_right_id.
             eapply must_eq_client. symmetry. eassumption.
             eapply nf_must_fw_r. eassumption.
             eapply must_eq_client. eassumption.
             edestruct (strip_eq hwoe2 t heqt) as (w & wmo & weq).
             edestruct (lts_oba_mo_strip t) as (x & hwot).
             eapply nf_must_fw_l. eassumption.
             rewrite gmultiset_disj_union_right_id.
             eapply H2. eassumption. reflexivity. eassumption.
      ++ exfalso. subst.
         eapply lts_stable_spec2.
         exists e0. eassumption. eapply lts_oba_mo_strip_stable. eassumption.
Qed.

Lemma must_fw_to_must
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !Good B L good }
  (p : A) (e : B) : must (p, ∅) e -> must p e.
Proof.
  intro hm.
  dependent induction hm; eauto with mdb.
  eapply m_step; eauto with mdb.
  - edestruct (lts_oba_mo_strip e) as (e' & hwo).
    assert (must (p, lts_oba_mo e) e'). eapply nf_must_fw; eauto with mdb.
    inversion H1; subst.
    + exfalso. eapply woutpout_preserves_good_converse in H5; eauto.
    + destruct ex0 as (((p0, m0), e0) & l).
      inversion l; subst.
      ++ inversion l0; subst.
         +++ eauto with mdb.
         +++ assert (a ∈ lts_oba_mo e). rewrite <- H7. set_solver.
             eapply lts_oba_mo_spec1, lts_outputs_spec2 in H5 as (e2 & l2).
             exists (p0, e2). eapply (ParSync (ActExt $ ActIn a) (ActExt $ ActOut a)); eauto. now simpl.
      ++ eapply woutpout_preserves_mu in l0 as (r0 & r1 & l0 & _); eauto.
         eauto with mdb.
      ++ destruct α1 as [[a|a]|]; destruct α2 as [[b|b]|]; simpl in eq; subst; try now exfalso.
         exfalso. eapply (@lts_stable_spec2 B). exists e0; eauto.
         eapply lts_oba_mo_strip_stable. eassumption.
         eapply woutpout_preserves_mu in l2 as (r0 & r1 & l0 & _); eauto.
         inversion l1; subst.
         +++ exists (p0, r0). eapply (ParSync (ActExt $ ActOut b) (ActExt $ ActIn b)); eauto. now simpl.
         +++ assert (b ∈ lts_oba_mo e). rewrite <- H7. set_solver.
             eapply lts_oba_mo_spec1, lts_outputs_spec2 in H5 as (e2 & l2).
             assert (neq : ActIn b ≠ ActOut b) by now inversion 1.
             edestruct (lts_oba_output_confluence neq l2 l0) as (e3 & l3 & l4).
             destruct (lts_oba_fb_feedback l2 l3) as (e4 & l6 & _).
             eauto with mdb.
  - intros p' l. eapply H4; eauto with mdb. now eapply lts_fw_p.
  - intros p' e' μ l1 l2. eapply H2; eauto with mdb. now eapply lts_fw_p.
Qed.

Lemma must_iff_must_fw
  `{@LtsObaFB A L IL LA LOA V, @LtsObaFB B L IL LB LOB W, !FiniteLts A L, !Good B L good }
  (p : A) (e : B) :
  must p e <-> must (p, ∅) e.
Proof.
  split; intro hm.
  - edestruct (lts_oba_mo_strip e) as (e' & hmo).
    eapply nf_must_fw_l. eassumption.
    rewrite gmultiset_disj_union_right_id.
    eapply must_to_must_fw. eassumption. reflexivity. eassumption.
  - now eapply must_fw_to_must.
Qed.

Lemma lift_fw_ctx_pre
  `{@LtsObaFB A L IL LA LOA V,
    @LtsObaFB B L IL LB LOB W,
    !FiniteLts A L, !FiniteLts B L,
    @LtsObaFB C L IL LC LOC Y,
    !Good C L good}
  (p : A) (q : B) : p ⊑ q <-> (p, ∅) ⊑ (q, ∅).
Proof.
  split; intros hctx e hm%must_iff_must_fw.
  - rewrite <- must_iff_must_fw. eauto.
  - rewrite must_iff_must_fw. eauto.
Qed.
