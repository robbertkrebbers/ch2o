(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on abstract rewriting systems.
These are particularly useful as we define the operational semantics as a
small step semantics. This file defines a hint database [ars] containing
some theorems on abstract rewriting systems. *)
Require Import Wf_nat.
Require Export tactics base.

(** * Definitions *)
Section definitions.
  Context `(R : relation A).

  (** An element is reducible if a step is possible. *)
  Definition red (x : A) := ∃ y, R x y.

  (** An element is in normal form if no further steps are possible. *)
  Definition nf (x : A) := ¬red x.

  (** The reflexive transitive closure. *)
  Inductive rtc : relation A :=
    | rtc_refl x : rtc x x
    | rtc_l x y z : R x y → rtc y z → rtc x z.

  (** Reductions of exactly [n] steps. *)
  Inductive nsteps : nat → relation A :=
    | nsteps_O x : nsteps 0 x x
    | nsteps_l n x y z : R x y → nsteps n y z → nsteps (S n) x z.

  (** Reduction of at most [n] steps. *)
  Inductive bsteps : nat → relation A :=
    | bsteps_refl n x : bsteps n x x
    | bsteps_l n x y z : R x y → bsteps n y z → bsteps (S n) x z.

  (** The transitive closure. *)
  Inductive tc : relation A :=
    | tc_once x y : R x y → tc x y
    | tc_l x y z : R x y → tc y z → tc x z.

  (** An element [x] is looping if all paths starting at [x] are infinite. *)
  CoInductive looping : A → Prop :=
    | looping_do_step x : red x → (∀ y, R x y → looping y) → looping x.
End definitions.

Hint Constructors rtc nsteps bsteps tc : ars.

(** * General theorems *)
Section rtc.
  Context `{R : relation A}.

  Global Instance rtc_reflexive: Reflexive (rtc R).
  Proof. red. apply rtc_refl. Qed.
  Global Instance rtc_transitive: Transitive (rtc R).
  Proof. red. induction 1; eauto with ars. Qed.
  Lemma rtc_once x y : R x y → rtc R x y.
  Proof. eauto with ars. Qed.
  Instance rtc_once_subrel: subrelation R (rtc R).
  Proof. exact @rtc_once. Qed.
  Lemma rtc_r x y z : rtc R x y → R y z → rtc R x z.
  Proof. intros. etransitivity; eauto with ars. Qed.

  Lemma rtc_inv x z : rtc R x z → x = z ∨ ∃ y, R x y ∧ rtc R y z.
  Proof. inversion_clear 1; eauto. Qed.

  Lemma rtc_ind_r (P : A → A → Prop)
    (Prefl : ∀ x, P x x)
    (Pstep : ∀ x y z, rtc R x y → R y z → P x y → P x z) :
    ∀ x z, rtc R x z → P x z.
  Proof.
    cut (∀ y z, rtc R y z → ∀ x, rtc R x y → P x y → P x z).
    { eauto using rtc_refl. }
    induction 1; eauto using rtc_r.
  Qed.

  Lemma rtc_inv_r x z : rtc R x z → x = z ∨ ∃ y, rtc R x y ∧ R y z.
  Proof. revert x z. apply rtc_ind_r; eauto. Qed.

  Lemma nsteps_once x y : R x y → nsteps R 1 x y.
  Proof. eauto with ars. Qed.
  Lemma nsteps_trans n m x y z :
    nsteps R n x y → nsteps R m y z → nsteps R (n + m) x z.
  Proof. induction 1; simpl; eauto with ars. Qed.
  Lemma nsteps_r n x y z : nsteps R n x y → R y z → nsteps R (S n) x z.
  Proof. induction 1; eauto with ars. Qed.
  Lemma nsteps_rtc n x y : nsteps R n x y → rtc R x y.
  Proof. induction 1; eauto with ars. Qed.
  Lemma rtc_nsteps x y : rtc R x y → ∃ n, nsteps R n x y.
  Proof. induction 1; firstorder eauto with ars. Qed.

  Lemma bsteps_once n x y : R x y → bsteps R (S n) x y.
  Proof. eauto with ars. Qed.
  Lemma bsteps_plus_r n m x y :
    bsteps R n x y → bsteps R (n + m) x y.
  Proof. induction 1; simpl; eauto with ars. Qed.
  Lemma bsteps_weaken n m x y :
    n ≤ m → bsteps R n x y → bsteps R m x y.
  Proof.
    intros. rewrite (Minus.le_plus_minus n m); auto using bsteps_plus_r.
  Qed.
  Lemma bsteps_plus_l n m x y :
    bsteps R n x y → bsteps R (m + n) x y.
  Proof. apply bsteps_weaken. auto with arith. Qed.
  Lemma bsteps_S n x y :  bsteps R n x y → bsteps R (S n) x y.
  Proof. apply bsteps_weaken. lia. Qed.
  Lemma bsteps_trans n m x y z :
    bsteps R n x y → bsteps R m y z → bsteps R (n + m) x z.
  Proof. induction 1; simpl; eauto using bsteps_plus_l with ars. Qed.
  Lemma bsteps_r n x y z : bsteps R n x y → R y z → bsteps R (S n) x z.
  Proof. induction 1; eauto with ars. Qed.
  Lemma bsteps_rtc n x y : bsteps R n x y → rtc R x y.
  Proof. induction 1; eauto with ars. Qed.
  Lemma rtc_bsteps x y : rtc R x y → ∃ n, bsteps R n x y.
  Proof.
    induction 1.
    * exists 0. constructor.
    * naive_solver eauto with ars.
  Qed.

  Lemma bsteps_ind_r (P : nat → A → Prop) (x : A)
    (Prefl : ∀ n, P n x)
    (Pstep : ∀ n y z, bsteps R n x y → R y z → P n y → P (S n) z) :
    ∀ n z, bsteps R n x z → P n z.
  Proof.
    cut (∀ m y z, bsteps R m y z → ∀ n,
      bsteps R n x y →
      (∀ m', n ≤ m' ∧ m' ≤ n + m → P m' y) →
      P (n + m) z).
    { intros help ?. change n with (0 + n). eauto with ars. }
    induction 1 as [|m x' y z p2 p3 IH]; [by eauto with arith|].
    intros n p1 H. rewrite <-plus_n_Sm.
    apply (IH (S n)); [by eauto using bsteps_r |].
    intros [|m'] [??]; [lia |].
    apply Pstep with x'.
    * apply bsteps_weaken with n; intuition lia.
    * done.
    * apply H; intuition lia.
  Qed.

  Global Instance tc_trans: Transitive (tc R).
  Proof. red; induction 1; eauto with ars. Qed.
  Lemma tc_r x y z : tc R x y → R y z → tc R x z.
  Proof. intros. etransitivity; eauto with ars. Qed.
  Lemma tc_rtc x y : tc R x y → rtc R x y.
  Proof. induction 1; eauto with ars. Qed.
  Instance tc_once_subrel: subrelation (tc R) (rtc R).
  Proof. exact @tc_rtc. Qed.

  Lemma looping_red x : looping R x → red R x.
  Proof. destruct 1; auto. Qed.
  Lemma looping_step x y : looping R x → R x y → looping R y.
  Proof. destruct 1; auto. Qed.
  Lemma looping_rtc x y : looping R x → rtc R x y → looping R y.
  Proof. induction 2; eauto using looping_step. Qed.

  Lemma looping_alt x :
    looping R x ↔ ∀ y, rtc R x y → red R y.
  Proof.
    split.
    * eauto using looping_red, looping_rtc.
    * intros H. cut (∀ z, rtc R x z → looping R z).
      { eauto with ars. }
      cofix FIX. constructor; eauto using rtc_r with ars.
  Qed.
End rtc.

(* Avoid too eager type class resolution *)
Hint Extern 5 (subrelation _ (rtc _)) =>
  eapply @rtc_once_subrel : typeclass_instances.
Hint Extern 5 (subrelation _ (tc _)) =>
  eapply @tc_once_subrel : typeclass_instances.

Hint Resolve
  rtc_once rtc_r
  tc_r
  bsteps_once bsteps_r bsteps_refl bsteps_trans : ars.

(** * Theorems on sub relations *)
Section subrel.
  Context {A} (R1 R2 : relation A) (Hsub : subrelation R1 R2).

  Lemma red_subrel x : red R1 x → red R2 x.
  Proof. intros [y ?]. exists y. by apply Hsub. Qed.
  Lemma nf_subrel x : nf R2 x → nf R1 x.
  Proof. intros H1 H2. destruct H1. by apply red_subrel. Qed.

  Instance rtc_subrel: subrelation (rtc R1) (rtc R2).
  Proof. induction 1; [left|eright]; eauto; by apply Hsub. Qed.
  Instance nsteps_subrel: subrelation (nsteps R1 n) (nsteps R2 n).
  Proof. induction 1; [left|eright]; eauto; by apply Hsub. Qed.
  Instance bsteps_subrel: subrelation (bsteps R1 n) (bsteps R2 n).
  Proof. induction 1; [left|eright]; eauto; by apply Hsub. Qed.
  Instance tc_subrel: subrelation (tc R1) (tc R2).
  Proof. induction 1; [left|eright]; eauto; by apply Hsub. Qed.
End subrel.

Hint Extern 5 (subrelation (rtc _) (rtc _)) =>
  eapply @rtc_subrel : typeclass_instances.
Hint Extern 5 (subrelation (nsteps _) (nsteps _)) =>
  eapply @nsteps_subrel : typeclass_instances.
Hint Extern 5 (subrelation (bsteps _) (bsteps _)) =>
  eapply @bsteps_subrel : typeclass_instances.
Hint Extern 5 (subrelation (tc _) (tc _)) =>
  eapply @tc_subrel : typeclass_instances.

Notation wf := well_founded.

Section wf.
  Context `{R : relation A}.

  (** A trick by Thomas Braibant to compute with well-founded recursions:
  it lazily adds [2^n] [Acc_intro] constructors in front of a well foundedness
  proof, so that the actual proof is never reached in practise. *)
  Fixpoint wf_guard (n : nat) (wfR : wf R) : wf R :=
    match n with
    | 0 => wfR
    | S n => λ x, Acc_intro x (λ y _, wf_guard n (wf_guard n wfR) y)
    end.

  Lemma wf_projected `(R2 : relation B) (f : A → B) :
    (∀ x y, R x y → R2 (f x) (f y)) →
    wf R2 → wf R.
  Proof.
    intros Hf Hwf.
    cut (∀ y, Acc R2 y → ∀ x, y = f x → Acc R x).
    { intros aux x. apply (aux (f x)); auto. }
    induction 1 as [y _ IH]. intros x ?. subst.
    constructor. intros. apply (IH (f y)); auto.
  Qed.
End wf.

(* Generally we do not want [wf_guard] to be expanded (neither by tactics,
nor by conversion tests in the kernel), but in some cases we do need it for
computation (that is, we cannot make it opaque). We use the [Strategy]
command to make its expanding behavior less eager. *)
Strategy 100 [wf_guard].
