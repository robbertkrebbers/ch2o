(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export prelude.

(** Some useful type classes to get nice overloaded notations for the different
kinds of values that we will consider. *)
Class Valid (E A : Type) := valid: E → A → Prop.
#[global] Instance: Params (@valid) 4 := {}.
Notation "✓{ Γ }" := (valid Γ) (at level 1, format "✓{ Γ }") : C_scope.
Notation "✓{ Γ }*" := (Forall (✓{Γ})) (at level 1, format "✓{ Γ }*") : C_scope.
Notation "✓{ Γ }**" := (Forall (✓{Γ}*))
  (at level 1, format "✓{ Γ }**") : C_scope.
Notation "✓{ Γ }2**" := (Forall (✓{Γ}* ∘ snd))
  (at level 1, format "✓{ Γ }2**") : C_scope.
Notation "✓{ Γ1 , Γ2 , .. , Γ3 }" := (valid (pair .. (Γ1, Γ2) .. Γ3))
  (at level 1, format "✓{ Γ1 , Γ2 , .. , Γ3 }") : C_scope.
Notation "✓{ Γ1 , Γ2 , .. , Γ3 }*" := (Forall (✓{pair .. (Γ1, Γ2) .. Γ3}))
  (at level 1, format "✓{ Γ1 ,  Γ2 , .. , Γ3 }*") : C_scope.
Notation "✓{ Γ1 , Γ2 , .. , Γ3 }**" := (Forall (✓{pair .. (Γ1, Γ2) .. Γ3}*))
  (at level 1, format "✓{ Γ1 ,  Γ2 , .. , Γ3 }**") : C_scope.
Notation "✓{ Γ1 , Γ2 , .. , Γ3 }2**" :=
  (Forall (✓{pair .. (Γ1, Γ2) .. Γ3}* ∘ snd))
  (at level 1, format "✓{ Γ1 ,  Γ2 , .. , Γ3 }2**") : C_scope.
Notation "✓" := (valid ()) (at level 1) : C_scope.
Notation "✓*" := (Forall ✓) : C_scope.

Class Typed (E T V : Type) := typed: E → V → T → Prop.
Notation "Γ ⊢ v : τ" := (typed Γ v τ)
  (at level 74, v at next level, τ at next level) : C_scope.
Notation "Γ ⊢* vs :* τs" := (Forall2 (typed Γ) vs τs)
  (at level 74, vs at next level) : C_scope.
Notation "Γ ⊢1* vs :* τs" := (Forall2 (typed Γ ∘ fst) vs τs)
  (at level 74, vs at next level) : C_scope.
Notation "Γ ⊢* vs : τ" := (Forall (λ v, Γ ⊢ v : τ) vs)
  (at level 74, vs at next level) : C_scope.
#[global] Instance: Params (@typed) 4 := {}.

Class PathTyped (E T1 T2 V : Type) := path_typed: E → V → T1 → T2 → Prop.
Notation "Γ ⊢ v : τ ↣ σ" := (path_typed Γ v τ σ)
  (at level 74, v at next level, τ at next level, σ at next level) : C_scope.
#[global] Instance: Params (@path_typed) 5 := {}.

Class TypeCheck (E T V : Type) := type_check: E → V → option T.
Arguments type_check {_ _ _ _} _ !_ / : simpl nomatch.
Class TypeCheckSpec (E T V : Type) (P : E → Prop)
    `{Typed E T V} `{TypeCheck E T V} :=
  type_check_correct Γ x τ : P Γ → type_check Γ x = Some τ ↔ Γ ⊢ x : τ.

Class TypeOf (T V : Type) := type_of: V → T.
Arguments type_of {_ _ _} !_ / : simpl nomatch.
Class TypeOfSpec (E T V : Type) `{Typed E T V, TypeOf T V} :=
  type_of_correct Γ x τ : Γ ⊢ x : τ → type_of x = τ.
Class PathTypeCheckSpec (E T1 T2 R : Type) (P : E → Prop)
    `{PathTyped E T1 T2 R, LookupE E R T2 T1} :=
  path_type_check_correct Γ p τ σ : P Γ → τ !!{Γ} p = Some σ ↔ Γ ⊢ p : τ ↣ σ.

Class PathTypeCheckSpecUnique (E T1 T2 R : Type) (P : E → Prop)
    `{PathTyped E T1 T2 R, LookupE E R T2 T1} := {
  path_typed_unique_spec :> PathTypeCheckSpec E T1 T2 R P;
  path_typed_unique_l Γ r τ1 τ2 σ :
    P Γ → Γ ⊢ r : τ1 ↣ σ → Γ ⊢ r : τ2 ↣ σ → τ1 = τ2
}.

Ltac valid_constructor :=
  intros; match goal with
  | |- valid (Valid:=?T) ?Γ ?x =>
    let T' := eval hnf in (T Γ) in
    econstructor; change T' with (valid (Valid:=T) Γ)
  end.  
Ltac typed_constructor :=
  intros; match goal with
  | |- typed (Typed:=?T) ?Γ _ _ =>
    let T' := eval hnf in (T Γ) in
    econstructor; change T' with (typed (Typed:=T) Γ)
  | |- path_typed (PathTyped:=?T) ?Γ _ _ _ =>
    let T' := eval hnf in (T Γ) in
    econstructor; change T' with (path_typed (PathTyped:=T) Γ)
  end.
Ltac valid_inversion H :=
  match type of H with
  | valid (Valid:=?T) ?Γ _ =>
    let T' := eval hnf in (T Γ) in
    inversion H; clear H; simplify_equality';
    try change T' with (valid (Valid:=T) Γ) in *
  end.
Ltac typed_inversion H :=
  match type of H with
  | typed (Typed:=?T) ?Γ _ _ =>
    let T' := eval hnf in (T Γ) in
    inversion H; clear H; simplify_equality';
    try change T' with (typed (Typed:=T) Γ) in *
  | path_typed (PathTyped:=?T) ?Γ _ _ _ =>
    let T' := eval hnf in (T Γ) in
    inversion H; clear H; simplify_equality';
    try change T' with (path_typed (PathTyped:=T) Γ) in *
  end.
Ltac typed_inversion_all :=
  repeat match goal with
  | H : _ ⊢ ?x : _ |- _ =>
     first [is_var x; fail 1|typed_inversion H; [idtac]|by typed_inversion H]
  | H : _ ⊢ ?x : _ ↣ _ |- _ =>
     first [is_var x; fail 1|typed_inversion H; [idtac]|by typed_inversion H]
  end.

Section typed.
  Context `{Typed E T V}.
  Lemma Forall2_Forall_typed Γ vs τs τ :
    Γ ⊢* vs :* τs → Forall (τ =.) τs → Γ ⊢* vs : τ.
  Proof. induction 1; inversion 1; subst; eauto. Qed.
End typed.

Section type_check.
  Context `{TypeCheckSpec E T V P}.
  Lemma type_check_None Γ x τ : P Γ → type_check Γ x = None → ¬Γ ⊢ x : τ.
  Proof. intro. rewrite <-type_check_correct by done. congruence. Qed.
  Lemma type_check_sound Γ x τ : P Γ → type_check Γ x = Some τ → Γ ⊢ x : τ.
  Proof. intro. by rewrite type_check_correct by done. Qed.
  Lemma type_check_complete Γ x τ : P Γ → Γ ⊢ x : τ → type_check Γ x = Some τ.
  Proof. intro. by rewrite type_check_correct by done. Qed.
  Lemma typed_unique Γ x τ1 τ2 : P Γ → Γ ⊢ x : τ1 → Γ ⊢ x : τ2 → τ1 = τ2.
  Proof. intro. rewrite <-!type_check_correct by done. congruence. Qed.
  Lemma mapM_type_check_sound Γ xs τs :
    P Γ → mapM (type_check Γ) xs = Some τs → Γ ⊢* xs :* τs.
  Proof. rewrite mapM_Some. induction 2; eauto using type_check_sound. Qed.
  Lemma mapM_type_check_complete Γ xs τs :
    P Γ → Γ ⊢* xs :* τs → mapM (type_check Γ) xs = Some τs.
  Proof. rewrite mapM_Some. induction 2; eauto using type_check_complete. Qed.
End type_check.

Section type_of.
  Context `{TypeOfSpec E T V}.
  Lemma type_of_typed Γ x τ : Γ ⊢ x : τ → Γ ⊢ x : type_of x.
  Proof. intros. erewrite type_of_correct; eauto. Qed.
  Lemma typed_unique_alt Γ x τ1 τ2 : Γ ⊢ x : τ1 → Γ ⊢ x : τ2 → τ1 = τ2.
  Proof.
    intros Hτ1 Hτ2. apply type_of_correct in Hτ1. apply type_of_correct in Hτ2.
    congruence.
  Qed.
  Lemma fmap_type_of Γ vs τs : Γ ⊢* vs :* τs → type_of <$> vs = τs.
  Proof. induction 1; f_equal'; eauto using type_of_correct. Qed.
End type_of.

Section path_type_check.
  Context `{PathTypeCheckSpec E T1 T2 R}.
  Lemma path_type_check_None Γ r τ σ : P Γ → τ !!{Γ} r = None → ¬Γ ⊢ r : τ ↣ σ.
  Proof. intros ?. rewrite <-path_type_check_correct by done. congruence. Qed.
  Lemma path_type_check_sound Γ r τ σ : P Γ → τ !!{Γ} r = Some σ → Γ ⊢ r : τ ↣ σ.
  Proof. intros ?. by rewrite path_type_check_correct. Qed.
  Lemma path_type_check_complete Γ r τ σ :
    P Γ → Γ ⊢ r : τ ↣ σ → τ !!{Γ} r = Some σ.
  Proof. intros ?. by rewrite path_type_check_correct. Qed.
  Lemma path_typed_unique_r Γ r τ σ1 σ2 :
    P Γ → Γ ⊢ r : τ ↣ σ1 → Γ ⊢ r : τ ↣ σ2 → σ1 = σ2.
  Proof. intros ?. rewrite <-!path_type_check_correct by done. congruence. Qed.
End path_type_check.

#[global] Instance typed_dec `{TypeCheckSpec E T V (λ _, True)}
  `{EqDecision T} Γ x τ : Decision (Γ ⊢ x : τ).
Proof.
 refine
  match Some_dec (type_check Γ x) with
  | inleft (τ'↾_) => cast_if (decide (τ = τ'))
  | inright _ => right _
  end; abstract (rewrite <-type_check_correct by done; congruence).
Defined.
#[global] Instance path_typed_dec `{PathTypeCheckSpec E T1 T2 R (λ _, True)}
  `{EqDecision T2} Γ p τ σ : Decision (Γ ⊢ p : τ ↣ σ).
Proof.
  refine (cast_if (decide (τ !!{Γ} p = Some σ)));
  by rewrite <-path_type_check_correct by done.
Defined.

Ltac simplify_type_equality := repeat
  match goal with
  | _ => progress simplify_equality
  | H : type_check _ _ = Some _ |- _ => rewrite type_check_correct in H by done
  | H : ?Γ ⊢ ?x : ?τ, H2 : context [ type_of ?x ] |- _ =>
    rewrite !(type_of_correct Γ x τ) in H2 by done
  | H : ?Γ ⊢ ?x : ?τ |- context [ type_of ?x ] =>
    rewrite !(type_of_correct Γ x τ) by done
  | H : type_check ?Γ ?x = None, H2 : ?Γ ⊢ ?x : ?τ |- _ =>
    by destruct (type_check_None Γ x τ)
  | H : ?τ !!{?Γ} ?p = None, H2 : _ ⊢ ?p : (?τ,?σ) |- _ =>
    by destruct (path_type_check_None Γ p τ σ)
  | H : _ ⊢ ?x : ?τ1, H2 : _ ⊢ ?x : ?τ2 |- _ =>
    unless (τ1 = τ2) by done;
    assert (τ2 = τ1) by (by apply (λ HΓ, typed_unique _ x τ2 τ1 HΓ H2 H));
    first [subst τ2 | subst τ1]; clear H2
  | H : _ ⊢ ?x : ?τ1, H2 : _ ⊢ ?x : ?τ2 |- _ =>
    unless (τ1 = τ2) by done;
    pose proof (typed_unique_alt _ x τ1 τ2 H H2);
    first [subst τ2 | subst τ1]; clear H2
  | H : _ ⊢ [] : _ ↣ _ |- _ => inversion H; clear H (* hack *)
  | H : _ !!{_} [] = Some _ |- _ => injection' H (* hack *)
  | H : _ !! [] = Some _ |- _ => injection' H (* hack *)
  | H : _ ⊢ ?p : ?τ ↣ ?σ1, H2 : _ ⊢ ?p : ?τ ↣ ?σ2 |- _ =>
    unless (σ1 = σ2) by done;
    pose proof (path_typed_unique_r _ p τ σ1 σ2 I H H2);
    first [subst σ2 | subst σ1]; clear H2
  | H : _ ⊢ ?p : ?τ1 ↣ ?σ, H2 : _ ⊢ ?p : ?τ2 ↣ ?σ |- _ =>
    unless (τ1 = τ2) by done;
    pose proof (path_typed_unique_l _ p τ1 τ2 σ I H H2);
    first [subst τ2 | subst τ1]; clear H2
  end.
Ltac simplify_type_equality' :=
  repeat (progress csimpl in * || simplify_type_equality).
