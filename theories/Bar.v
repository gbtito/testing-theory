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
From Must Require Import TransitionSystems.

From stdpp Require Import base countable gmap list.

(* For proving that Bar-induction is admissible *)
Require Coq.Logic.ClassicalEpsilon.

CoInductive infinite_stream A: Type :=
   | S_Step : A -> infinite_stream A -> infinite_stream A.

Fixpoint take {A} n (π : infinite_stream A) :=
  match n with
  | 0 => []
  | S n => match π with S_Step _ a π' => a :: take n π' end
  end.

Definition inf_first {A} (π: infinite_stream A) := match π with S_Step _ x _ => x end.
Definition inf_tail {A} (π: infinite_stream A) := match π with S_Step _ _ π => π end.

Section actual_bar_induction.
  Variable P: list positive -> Prop.
  Variable Q: list positive -> Prop.


  CoInductive C (p: list positive) :=
  | CONS (a: positive) (ρ: C (p ++ [a])) (Hnot: ¬ P (p)): C p.

  CoFixpoint C_to_stream p (ρ: C p) : infinite_stream positive :=
    match ρ with
    | CONS _ a ρ' Hnot => S_Step _ a (C_to_stream _ ρ')
    end.

  Lemma C_counterexample p (ρ : C p):
    ∀ n, ¬ P (p ++ take n (C_to_stream _ ρ)).
  Proof.
    intros n. revert n p ρ. induction n. { intros. simpl. destruct ρ. by list_simplifier. }
    intros. simpl. destruct ρ as [a ρ ?]. specialize (IHn _ ρ). by list_simplifier.
  Qed.

  (* Hypothesis of decidable Bar induction *)
  Variable P_is_decidable: ∀ p, P p ∨ ¬ P p.
  Variable eventually_P: ∀ π, ∃ n, P (take n π).
  Variable P_implies_Q: ∀ p, P p -> Q p.
  Variable Q_hereditary: ∀ p, (∀ a, Q (p ++ [a])) → Q p.

  Lemma contrapositive (A B: Prop): (A → B) → (¬ B) → ¬ A.
  Proof. intros Hh Hn Ha. apply Hn, Hh. exact Ha. Qed.

  Lemma not_exists p: ¬ Q p → ∃ a, ¬ Q (p ++ [a]).
  Proof.
    Import ClassicalEpsilon.
    intros Hn.
    pose proof (Q_hereditary p) as Hh.
    apply contrapositive in Hh; last assumption.
    apply not_all_ex_not in Hh.
    exact Hh.
  Qed.

  Definition not_exists_set p: ¬ Q p → { a | ¬ Q (p ++ [a]) } := λ Hn,
    exist _ _ (epsilon_spec (inhabits xH) _ (not_exists _ Hn)).

  Lemma nP_implies_nQ : ∀ p, (¬ Q p) → (¬ P p).
  Proof. intros p. apply contrapositive. apply P_implies_Q. Qed.

  CoFixpoint build_path p (Hn: ¬ Q p) : C p :=
    let ce := not_exists_set _ Hn in
    let here := nP_implies_nQ _ Hn in
    let ρ := build_path (p ++ [(`ce)]) (proj2_sig ce) in
    CONS p (`ce) ρ here.

  (* We prove the principle of Bar induction using the classical axiom of
  Classical Epsilon to be sure that the Bar-induction principle we are using is
  admissible wrt to Coq's logic. Classical expsilon states that if [∃ x, P x]
  then we can choose a witness using a choice function [ϵ]. If [H] is a proof of
  [∃ x, P x], we know that [P (ϵ H)].

  It implies excluded middle, since [A ∨ ¬ A] is equivalent to [∃ (b:bool), if b
  then A else ¬ A]. Hence the Coq standard library reexports [classical] from
  [ClassicalEpsilon], hence there are two axioms used in the theorem below:
  constructive_indefinite_description and classical
   *)
  Theorem actual_bar_induction: Q [].
  Proof using eventually_P Q_hereditary P_is_decidable P_implies_Q P.
    Import ClassicalEpsilon.
    destruct (excluded_middle_informative (Q [])) as [|Hn]; first assumption. exfalso.
    apply build_path in Hn as ρ.
    destruct (eventually_P (C_to_stream _ ρ)).
    eapply (C_counterexample []). by list_simplifier.
  Qed.
End actual_bar_induction.
(* Print Assumptions actual_bar_induction. *)

Class SurCountable A := {
    surdecode: positive -> A;
    surjectivity: ∀ a, ∃ n, surdecode n = a;
}.

Class CompleteCountableSts `(Sts A) := {
    ccsts_states_surcountable: SurCountable A;
    ccsts_next_states_surcountable: ∀ x, SurCountable (dsig (fun y => sts_step x y));
}.
#[global] Existing Instance ccsts_states_surcountable.
#[global] Existing Instance ccsts_next_states_surcountable.

Section sts_bar_induction.
  Context `{CompleteCountableSts A}.

  CoFixpoint decode_choice_seq_from x0 (π: infinite_stream positive):
    iexec_from x0 :=
    let x := (ccsts_next_states_surcountable x0).(surdecode) (inf_first π) in
    let η := decode_choice_seq_from (`x) (inf_tail π) in
    IExStep x0 (`x) (proj2_dsig x) η.
  Definition decode_choice_seq π : iexec :=
    let x := ccsts_states_surcountable.(surdecode) (inf_first π) in
    let η := decode_choice_seq_from x (inf_tail π) in
    MkExec x η.

  Fixpoint decode_fin_choice_seq_from x0 (p: list positive):
    finexec_from x0 :=
    match p with
    | n::p' =>
        let x := (ccsts_next_states_surcountable x0).(surdecode) n in
        let t := decode_fin_choice_seq_from (`x) p' in
        FExStep x0 (`x) (bool_decide_pack _ $ proj2_dsig x) t
    | [] => FExSingl x0
    end.
  Definition decode_fin_choice_seq p : finexec :=
    match p with
    | [] => FinExNil
    | n::p' =>
        let x := ccsts_states_surcountable.(surdecode) n in
        let η := decode_fin_choice_seq_from x p' in
        FinExNonNil x η
    end.

  Lemma take_from_decode_commutes n x π:
    iex_take_from n (decode_choice_seq_from x π) =
      decode_fin_choice_seq_from x (take n π).
  Proof.
    revert π x; induction n; intros π x; [easy|].
    destruct π; simpl. f_equal. by rewrite IHn.
  Qed.
  Lemma take_decode_commutes n π:
    iex_take n (decode_choice_seq π) = decode_fin_choice_seq (take n π).
  Proof. destruct n; [easy|destruct π; simpl; f_equal; apply take_from_decode_commutes]. Qed.

  Lemma decode_from_snoc_surjective_helper (x: A) s a p' n Hstep:
    iex_snoc_from x (decode_fin_choice_seq_from x s) a = Some p' →
    (ccsts_next_states_surcountable (fex_from_last (decode_fin_choice_seq_from x s))).(surdecode) n =
      dexist (fex_from_last p') Hstep →
    decode_fin_choice_seq_from x (s ++ [n]) = p'.
  Proof.
    revert x p' Hstep n a. induction s as [|m s IHs]; intros x p' Hstep n a.
    - simpl. destruct (decide (sts_step x a)); [|easy]. injection 1. intros ? Hdec. subst.
      simpl in Hdec. rewrite Hdec. simpl. f_equal.
      assert (ProofIrrel $ bool_decide (sts_step x a)) by apply _. naive_solver.
    - simpl. match goal with
      | |- context[iex_snoc_from ?a ?b ?c] =>
            destruct (iex_snoc_from a b c) as [q|] eqn:Hsnoc; [|easy]
      end.
      intros ?. simplify_eq. simpl. intros Hdec. f_equal.
      destruct (iex_snoc_step _ _ _ _ Hsnoc) as [Hlast Hstep'].
      apply (IHs _ _ Hstep' _ a); [easy|].
      rewrite Hdec. unfold dexist. f_equal.
      assert (ProofIrrel $ bool_decide (sts_step x a)) by apply _.
      match goal with
      | |- context[bool_decide_pack ?step _] =>
          assert (ProofIrrel $ bool_decide step) by apply _; naive_solver
      end.
  Qed.

  Lemma decode_from_snoc_surjective x s a η:
    iex_snoc_from x (decode_fin_choice_seq_from x s) a = Some η →
    ∃ n', decode_fin_choice_seq_from x (s ++ [n']) = η.
  Proof.
    revert x a η; case s as [|n s]; intros x a η; simpl.
    - destruct (decide (sts_step x a)) as [Hstep |]; [|easy].
      injection 1; intros ?; subst.
      destruct (((ccsts_next_states_surcountable x)).(surjectivity) (dexist _ Hstep)) as [n1 Hn1].
      exists n1. rewrite Hn1. f_equal.
      assert (ProofIrrel $ bool_decide (sts_step x a)) by apply _. naive_solver.
    - match goal with
      | |- context[iex_snoc_from ?a ?b ?c] =>
            destruct (iex_snoc_from a b c) as [p'|] eqn:Hsnoc; [|easy]
      end.
      intros ?. simplify_eq.

      destruct (iex_snoc_step _ _ _ _ Hsnoc) as [Hlast Hstep].

      pose (decode_fin_choice_seq_from x (n::s)) as p.

      destruct (((ccsts_next_states_surcountable (fex_from_last p))).(surjectivity) (dexist _ Hstep)) as [n1 Hn1].
      exists n1. f_equal. eapply decode_from_snoc_surjective_helper; eauto.
  Qed.

  Lemma decode_snoc_surjective s a p:
    iex_snoc (decode_fin_choice_seq s) a = Some p ->
    ∃ n', decode_fin_choice_seq (s ++ [n']) = p.
  Proof.
    destruct s as [|n s']; simpl.
    - intros ?. destruct (ccsts_states_surcountable.(surjectivity) a) as [x Hx].
      exists x. simpl. rewrite Hx. congruence.
    - destruct (iex_snoc_from (surdecode n) (decode_fin_choice_seq_from (surdecode n) s') a) as [η|] eqn:Heq; [|easy].
      injection 1. intros Hp. subst.
      destruct (decode_from_snoc_surjective _ _ _ _ Heq) as [n' ?]. exists n'. by subst.
  Qed.

  Variable P: finexec -> Prop.
  Variable Q: finexec -> Prop.

  (* Hypothesis of Bar induction *)
  Variable P_is_decidable: ∀ p, P p ∨ ¬ P p.
  Variable eventually_P: ∀ π, ∃ n, P (iex_take n π).
  Variable P_implies_Q: ∀ p, P p -> Q p.
  Variable Q_wf: ∀ p, (∀ a p', iex_snoc p a = Some p' -> Q p') → Q p.

  Local Definition Q' (p: list positive) := Q (decode_fin_choice_seq p).
  Local Definition P' (p: list positive) := P (decode_fin_choice_seq p).

  Theorem bar_induction: Q FinExNil.
  Proof.
    cut (Q' []); try easy.
    eapply (actual_bar_induction P' Q').
    - intros p. apply P_is_decidable.
    - intros π. pose proof (eventually_P (decode_choice_seq π)) as [n ?].
      exists n. unfold P'. by rewrite <-take_decode_commutes.
    - intros p. unfold P', Q'. auto.
    - intros s Hher. apply Q_wf. intros a p' Hp.
      destruct (decode_snoc_surjective s a p') as [n']; eauto.
      specialize (Hher n') as HQ'. unfold Q' in HQ'. by subst.
  Qed.
End sts_bar_induction.

Section stss.
  Instance surcountable_countable A `{EqDecision A} :
    Inhabited A -> Countable A → SurCountable A.
  Proof.
    intros Hinh Hcount. refine {| surdecode n := match decode n with
                                              | Some x => x
                                              | None => inhabitant
                                              end |}.
    intros x. destruct (@decode A _ _ $ @encode A _ _ x) as [a|] eqn:Heq.
    - exists (encode a). rewrite decode_encode in *. congruence.
    - rewrite decode_encode in *. congruence.
  Qed.

  Inductive add_sink A :=
  | Orig (a: A)
  | Sink.
  #[global] Arguments Orig {_}.
  #[global] Arguments Sink {_}.

  Instance add_sink_inhabited A : Inhabited (add_sink A) := {| inhabitant := Sink |}.

  #[global] Instance add_sink_eqdec A:
    EqDecision A → EqDecision (add_sink A).
  Proof. solve_decision. Qed.

  Inductive add_sink_step A `{Sts A}: add_sink A → add_sink A → Prop :=
  | StepOrig a b: sts_step a b -> add_sink_step A (Orig a) (Orig b)
  | StepSinkSink : add_sink_step A Sink Sink
  | StepStableSink a: (sts_stable a) → add_sink_step A (Orig a) Sink
  .

  Lemma add_sink_orig_step `{Sts A} {x x'}:
    add_sink_step _ (Orig x) (Orig x') → sts_step x x'.
  Proof. by inversion 1. Qed.

  Lemma add_sink_step_sink `{Sts A} {x}:
    add_sink_step _ (Orig x) Sink → sts_stable x.
  Proof. by inversion 1. Qed.

  #[global] Instance add_sink_step_decision A `{Sts A}:
    RelDecision (add_sink_step A).
  Proof.
    intros x y. destruct x as [x|]; destruct y as [y|].
    - destruct (decide $ sts_step x y); [by left; constructor|right].
      intros contra. inversion contra. congruence.
    - destruct (decide (sts_stable x)); [by left; constructor|right].
      intros contra. inversion contra. congruence.
    - right; intros contra. inversion contra.
    - left; constructor.
  Qed.

  Definition add_sink_stable A `{Sts A} (x: add_sink A) := False.

  #[global] Instance add_sink_stable_decision A `{Sts A}:
     ∀ x : add_sink A, Decision (add_sink_stable _ x).
  Proof. intros [x|]; apply _. Qed.

  #[global] Instance add_sink_sts A (X: Sts A):
    Sts (add_sink A).
  Proof.
    refine {|
        sts_step := add_sink_step A;
        sts_stable := add_sink_stable A;
      |}.
    - intros [x|] _.
      + destruct (decide (sts_stable x)) as [|Hns].
        * refine (Sink ↾ _). by constructor.
        * destruct (sts_stable_spec1 _ Hns) as [y ?].
          refine (Orig y ↾ _). by constructor.
      + refine (Sink ↾ _). by constructor.
    - unfold add_sink_stable. tauto.
  Defined.

  Instance add_sink_step_inhabited `{Sts A}:
    ∀ x : add_sink A, Inhabited (dsig (λ y : add_sink A, sts_step x y)).
  Proof.
    intros [x|].
    - destruct (decide (sts_stable x)) as [|Hnstable].
      + refine (populate $ exist _ Sink _). apply bool_decide_spec. by constructor.
      + destruct (sts_stable_spec1 _ Hnstable) as [y ?].
        refine (populate $ exist _ (Orig y) _). apply bool_decide_spec. by constructor.
    - refine (populate $ exist _ Sink _). apply bool_decide_spec. constructor.
  Qed.

  Instance add_sink_state_countable `{CountableSts A}:
    Countable (add_sink A).
  Proof.
    pose (f (x: add_sink A) := match x with Orig x => Some x | Sink => None end).
    pose (g (x: option A) := match x with Some x => Orig x | None => Sink end).
    apply (inj_countable' f g). by intros [|].
  Qed.

  #[global] Instance add_sink_countable_sts (A: Type) `{sts: Sts A}:
    CountableSts A → CompleteCountableSts (add_sink_sts A sts).
  Proof.
    intros Hc. constructor.
    - eapply surcountable_countable; by apply _.
    - intros x. eapply surcountable_countable; [apply _|].
      destruct x as [|]; apply countable_sig; intros ?; apply _.
  Qed.
End stss.

Class Bar A `{Sts A} := {
    bar_pred: A → Prop;
    bar_decidable: ∀ x, Decision (bar_pred x);
  }.
#[global] Existing Instance bar_decidable.

#[global] Instance add_sink_bar A `{Bar A}: Bar (add_sink A).
Proof.
  refine ({|
    bar_pred a := match a with Orig x => bar_pred x | Sink => False end;
  |}).
  intros [|]; by apply _.
Defined.

Section barred_sts.
  Definition extensional_pred `{Bar A} (a: A): Prop :=
    forall η: max_exec_from a, exists n p, mex_take_from n η = Some p ∧ bar_pred $ fex_from_last p.

  Definition infinite_extensional_pred `{Bar A} (a: A) `{Sts A} : Prop :=
    forall η: iexec_from a, exists n, bar_pred $ fex_from_last $ iex_take_from n η.

  CoFixpoint add_sink_Ω `{Sts A}: iexec_from (Sink : add_sink A) :=
    IExStep Sink Sink (StepSinkSink _) add_sink_Ω.

  CoFixpoint add_sink_max_to_iexec `{Sts A} {x: A} (η: max_exec_from x): iexec_from (Orig x) :=
    match η in max_exec_from a return iexec_from (Orig a) with
    | MExStop y Hstable => IExStep (Orig y) Sink (StepStableSink A y Hstable) add_sink_Ω
    | MExStep y x' Hstep η => IExStep (Orig y) (Orig x') (StepOrig A y x' Hstep) (add_sink_max_to_iexec η)
    end.

  (* FIXME:  Horrible :/ *)
  CoFixpoint add_sink_iexec_to_max `{sts: Sts A} {x: A} (η: iexec_from (Orig x)): max_exec_from x.
  Proof.
    inversion η as [y y' Hstep η']. simplify_eq.
    destruct y'.
    - exact (MExStep _ _ (add_sink_orig_step Hstep) (add_sink_iexec_to_max _ _ _ η')).
    - exact (MExStop _ (add_sink_step_sink Hstep)).
  Defined.

  Lemma add_sink_iexec_to_max_last `{Sts A} (a: A) n (p: finexec_from a) η :
    mex_take_from n (add_sink_iexec_to_max η) = Some p →
    fex_from_last (iex_take_from n η) = Orig (fex_from_last p).
  Proof.
    revert a p η; induction n as [|n IH]; intros a p η.
    - cbn. intros; by simplify_eq.
    - inversion η as [y y' Hstep η1]; simplify_eq. cbn.
      match goal with
      | [|- match ?km with _ => _ end = _ → _] => destruct km as [| T R E η'] eqn:Hkm; [done|]
      end.
      cbn; intros Heq.
      destruct (mex_take_from n η') as [p'|] eqn:Hmtf; [cbn in Heq; simplify_eq|done].
      dependent destruction η; simplify_eq. cbn.
      cbn in Hkm. destruct x'; try done. simplify_eq.
      by apply IH.
  Qed.

  Lemma add_sink_preserves_extensional_pred `{Bar A} (a: A):
    extensional_pred a → infinite_extensional_pred (Orig a).
  Proof.
    intros Hexter η. unfold extensional_pred in Hexter.
    destruct (Hexter (add_sink_iexec_to_max η)) as (n & p & Heq & Hstable).
    exists n. by rewrite (add_sink_iexec_to_max_last _ _ _ _ Heq).
  Qed.

  Inductive complete_intensional_pred `{Bar A}: A -> Prop :=
  | CIntDone p: bar_pred p -> complete_intensional_pred p
  | CIntHer p:  (∀ p', sts_step p p' -> complete_intensional_pred p') -> complete_intensional_pred p.

  Inductive intensional_pred `{Bar A}: A -> Prop :=
  | IntDone p: bar_pred p -> intensional_pred p
  | IntHer p: ¬(sts_stable p) → (∀ p', sts_step p p' -> intensional_pred p') -> intensional_pred p.

  Lemma sink_no_hope `{Bar A}: ¬ complete_intensional_pred (@Sink A).
  Proof.
    intros Hp. dependent induction Hp. done.
    apply (H4 Sink ltac:(constructor) _ _ _ eq_refl); done.
  Qed.

  Lemma add_sink_preserves_intensional_pred `{Bar A} (a: A):
    complete_intensional_pred (Orig a) → intensional_pred a.
  Proof.
    intros Hc.
    dependent induction Hc; [constructor 1; done|].
    (* TODO: don't use autogen'd names *)

    destruct (decide (sts_stable a)) as [Hs|].
    { specialize (H3 _ (StepStableSink _ _ Hs)). by exfalso; apply sink_no_hope. }
    constructor 2; [done|]. intros p' Hstep. eapply H4; try done. by constructor.
  Qed.
End barred_sts.

Section bar_helper.
  Context `{Hsts: Sts A, @CompleteCountableSts A Hsts}.
  Context `{@Bar A Hsts}.

  Definition P start (p: finexec) :=
    match fex_cons start p with
    | None => True
    | Some p' => match fex_last p' with
                | None => False
                | Some x => bar_pred x
                end
    end.
  Definition Q start (p: finexec) :=
      match fex_cons start p with
      | None => True
      | Some p' => match fex_last p' with
                  | None => False
                  | Some x => complete_intensional_pred x
                  end
      end.

  Proposition extensional_implies_intensional_helper x:
    infinite_extensional_pred x -> complete_intensional_pred x.
  Proof.
    intros Hconv.
    cut (Q x FinExNil).
    { by unfold Q. }
    apply (@bar_induction _ _ _ (P x) (Q x)).
    - intros q. unfold P. destruct (fex_cons x q); [|by auto].
      destruct (fex_last f) as [a|]; [|by right; auto]. destruct (bar_decidable a); eauto.
    - intros η. unfold P. destruct (decide (sts_step x (η.(iex_start)))) as [Hstep|Hstep];
        [|exists 1; simpl; by destruct (decide (sts_step x (iex_start η)))].
      destruct (Hconv (IExStep _ _ Hstep η.(iex))) as [n Hstable].
       exists n. destruct (fex_cons x (iex_take n η)) as [p'|] eqn:Hcons; [|easy].
        rewrite <- (iex_fex_take _ Hstep) in Hcons. injection Hcons. by intros <-.
    - intros q; unfold P, Q.
      destruct (fex_cons x q) as [q'|] eqn:Hcons; [|easy].
      destruct (fex_last q') as [y|]; [|easy].
      intros Hbar. by constructor 1.
    - intros p Hher. unfold Q.
      destruct (fex_cons x p) as [ex|] eqn:Hcons; [|easy].
      destruct (fex_last ex) as [y|] eqn:Hlast; [|].
      2: { destruct ex; [|easy]. destruct p as [|y]; [easy|]. simpl in Hcons.
           by destruct (decide (sts_step x y)). }
      constructor 2. intros z Hstep.
      destruct (fex_snoc_valid_last ex y z Hlast Hstep) as [t Hsnoc].
      destruct p as [|x' p'].
      + simpl in *.
        specialize (Hher z (finex_singl z) ltac:(easy)). unfold Q in Hher.
        simplify_eq. simpl in Hlast. simplify_eq.
        simpl in Hher. destruct (decide (sts_step y z)); easy.
      + simpl in Hcons. destruct (decide (sts_step x x')) as [Hstep'|]; [|easy].
        simplify_eq. simpl in Hlast, Hsnoc. simplify_eq.
        destruct (iex_snoc_from x' p' z) eqn:Hsnoc'; [|easy]. simplify_eq.
        specialize (Hher z (FinExNonNil _ f)).
        simpl in Hher; rewrite Hsnoc' in Hher. specialize (Hher ltac:(eauto)).
        unfold Q in Hher. simpl in Hher. destruct (decide (sts_step x x')); [|easy].
        by destruct (iex_snoc_step _ _ _ z Hsnoc') as [<- ?].
  Qed.
End bar_helper.

Section bar_int_ext.
  Context `{Hsts: Sts A, @CountableSts A Hsts}.
  Context `{@Bar A Hsts}.

  Theorem intensional_implies_extensional x:
     intensional_pred x → extensional_pred x.
  Proof.
    induction 1 as [p | p Hns Hint IH].
    - intros η. by exists 0, (FExSingl p).
    - intros η. destruct η as [| p q Hq]; first done.
      destruct (IH _ Hq η) as (n&ζ&Heq&?).
      exists (S n), (FExStep p q ltac:(eauto) ζ). split; last naive_solver.
      by simpl; rewrite Heq.
  Qed.

  Theorem extensional_implies_intensional x:
    extensional_pred x -> intensional_pred x.
  Proof.
    intros Hex%add_sink_preserves_extensional_pred.
    apply add_sink_preserves_intensional_pred.
    by apply extensional_implies_intensional_helper.
  Qed.
End bar_int_ext.
