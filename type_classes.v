(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export prelude.

(** Some useful type classes to get nice overloaded notations for the different
kinds of values that we will consider. *)
Class Valid (E A : Type) := valid: E → A → Prop.
Instance: Params (@valid) 4.
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
Instance: Params (@typed) 4.

Class PathTyped (E T V : Type) := path_typed: E → V → T → T → Prop.
Notation "Γ ⊢ v : τ ↣ σ" := (path_typed Γ v τ σ)
  (at level 74, v at next level, τ at next level, σ at next level) : C_scope.
Instance: Params (@path_typed) 4.

Class TypeCheck (E T V : Type) := type_check: E → V → option T.
Arguments type_check {_ _ _ _} _ !_ / : simpl nomatch.
Class TypeCheckSpec (E T V : Type) (P : E → Prop)
    `{Typed E T V} `{TypeCheck E T V} :=
  type_check_correct Γ x τ : P Γ → type_check Γ x = Some τ ↔ Γ ⊢ x : τ.

Class TypeOf (T V : Type) := type_of: V → T.
Arguments type_of {_ _ _} !_ / : simpl nomatch.
Class TypeOfSpec (E T V : Type) `{Typed E T V, TypeOf T V} :=
  type_of_correct Γ x τ : Γ ⊢ x : τ → type_of x = τ.
Class PathTypeCheckSpec (E T R : Type)
    `{PathTyped E T R, LookupE E R T T} := {
  path_type_check_correct Γ p τ σ : τ !!{Γ} p = Some σ ↔ Γ ⊢ p : τ ↣ σ;
  path_typed_unique_l Γ r τ1 τ2 σ :
    Γ ⊢ r : τ1 ↣ σ → Γ ⊢ r : τ2 ↣ σ → τ1 = τ2
}.

Section typed.
  Context `{Typed E T V}.
  Lemma Forall2_Forall_typed Γ vs τs τ :
    Γ ⊢* vs :* τs → Forall (τ =) τs → Γ ⊢* vs : τ.
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
  Proof. induction 1; simpl; f_equal; eauto using type_of_correct. Qed.
End type_of.

Section path_type_check.
  Context `{PathTypeCheckSpec E T R}.

  Lemma path_type_check_None Γ r τ σ : τ !!{Γ} r = None → ¬Γ ⊢ r : τ ↣ σ.
  Proof. rewrite <-path_type_check_correct. congruence. Qed.
  Lemma path_type_check_sound Γ r τ σ : τ !!{Γ} r = Some σ → Γ ⊢ r : τ ↣ σ.
  Proof. by rewrite path_type_check_correct. Qed.
  Lemma path_type_check_complete Γ r τ σ : Γ ⊢ r : τ ↣ σ → τ !!{Γ} r = Some σ.
  Proof. by rewrite path_type_check_correct. Qed.
  Lemma path_typed_unique_r Γ r τ σ1 σ2 :
    Γ ⊢ r : τ ↣ σ1 → Γ ⊢ r : τ ↣ σ2 → σ1 = σ2.
  Proof. rewrite <-!path_type_check_correct. congruence. Qed.

  Inductive list_typed' (Γ : E) : list R → T → T → Prop :=
    | nil_typed_2 τ : list_typed' Γ [] τ τ
    | cons_typed_2 r rs τ1 τ2 τ3 :
       Γ ⊢ rs : τ2 ↣ τ3 → list_typed' Γ r τ1 τ2 →
       list_typed' Γ (rs :: r) τ1 τ3.
  Instance list_typed : PathTyped E T (list R) := list_typed'.

  Section list_typed_ind.
    Context (Γ : E) (P : list R → T → T → Prop).
    Context (Pnil : ∀ τ, P [] τ τ).
    Context (Pcons : ∀ r rs τ1 τ2 τ3,
      Γ ⊢ rs : τ2 ↣ τ3 → Γ ⊢ r : τ1 ↣ τ2 → P r τ1 τ2 → P (rs :: r) τ1 τ3).
    Lemma list_typed_ind r τ σ : list_typed' Γ r τ σ → P r τ σ.
    Proof. induction 1; eauto. Qed. 
  End list_typed_ind.

  Instance list_path_lookup: LookupE E (list R) T T :=
    fix go Γ r τ := let _ : LookupE _ _ _ _ := @go in
    match r with [] => Some τ | rs :: r => τ !!{Γ} r ≫= lookupE Γ rs end.

  Lemma list_typed_nil Γ τ1 τ2 : Γ ⊢ @nil R : τ1 ↣ τ2 ↔ τ1 = τ2.
  Proof.
    split. by inversion 1; simplify_list_equality. intros <-. constructor.
  Qed.
  Lemma list_typed_cons Γ rs r τ1 τ3 :
    Γ ⊢ rs :: r : τ1 ↣ τ3 ↔ ∃ τ2, Γ ⊢ r : τ1 ↣ τ2 ∧ Γ ⊢ rs : τ2 ↣ τ3.
  Proof.
    unfold path_typed at 1 2, list_typed; simpl. split.
    * inversion 1; subst; eauto.
    * intros (?&?&?). econstructor; eauto.
  Qed.
  Lemma list_typed_app Γ r1 r2 τ1 τ3 :
    Γ ⊢ r1 ++ r2 : τ1 ↣ τ3 ↔ ∃ τ2, Γ ⊢ r2 : τ1 ↣ τ2 ∧ Γ ⊢ r1 : τ2 ↣ τ3.
  Proof.
    revert τ1 τ3. induction r1; simpl; intros.
    * setoid_rewrite list_typed_nil. naive_solver.
    * setoid_rewrite list_typed_cons. naive_solver.
  Qed.
  Lemma list_typed_singleton Γ rs τ1 τ2 : Γ ⊢ [rs] : τ1 ↣ τ2 ↔ Γ ⊢ rs : τ1 ↣ τ2.
  Proof.
    rewrite list_typed_cons. setoid_rewrite list_typed_nil. naive_solver.
  Qed.
  Lemma list_typed_snoc Γ r rs τ1 τ3 :
    Γ ⊢ r ++ [rs] : τ1 ↣ τ3 ↔ ∃ τ2, Γ ⊢ rs : τ1 ↣ τ2 ∧ Γ ⊢ r : τ2 ↣ τ3.
  Proof.
    setoid_rewrite list_typed_app. by setoid_rewrite list_typed_singleton.
  Qed.
  Lemma list_typed_snoc_2 Γ r rs τ1 τ2 τ3 :
    Γ ⊢ rs : τ1 ↣ τ2 ∧ Γ ⊢ r : τ2 ↣ τ3 → Γ ⊢ r ++ [rs] : τ1 ↣ τ3.
  Proof. rewrite list_typed_snoc; eauto. Qed.
  Lemma list_path_lookup_nil Γ : lookupE Γ (@nil R) = Some.
  Proof. done. Qed.
  Lemma list_path_lookup_cons Γ rs r :
    lookupE Γ (rs :: r) = λ τ, τ !!{Γ} r ≫= lookupE Γ rs.
  Proof. done. Qed.
  Lemma list_path_lookup_singleton Γ rs : lookupE Γ [rs] = lookupE Γ rs.
  Proof. done. Qed.

  Lemma list_path_lookup_app Γ r1 r2 τ :
    τ !!{Γ} (r1 ++ r2) = (τ !!{Γ} r2) ≫= lookupE Γ r1.
  Proof.
    induction r1 as [|rs1 r1 IH]; simpl; [by destruct (τ !!{_} r2)|].
    by rewrite list_path_lookup_cons, IH, option_bind_assoc.
  Qed.
  Lemma list_path_lookup_snoc Γ r rs τ :
    τ !!{Γ} (r ++ [rs]) = (τ !!{Γ} rs) ≫= lookupE Γ r.
  Proof. apply list_path_lookup_app. Qed.
  Global Instance: PathTypeCheckSpec E T (list R).
  Proof.
    split.
    * intros Γ r τ σ. split.
      + revert σ. induction r; intros σ;
          [intros;simplify_equality; constructor|].
        rewrite list_path_lookup_cons, list_typed_cons.
        intros. simplify_option_equality.
        eexists; split; eauto. by apply path_type_check_correct.
      + induction 1; [done|rewrite list_path_lookup_cons].
        simplify_option_equality. by apply path_type_check_complete.
    * intros Γ r τ1 τ2 σ Hr. revert τ2.
      induction Hr as [|r rs σ1 σ2 σ3 ?? IH] using list_typed_ind; intros τ1.
      { by rewrite list_typed_nil. }
      rewrite list_typed_cons; intros (τ2&?&?); apply IH.
      by rewrite (path_typed_unique_l Γ rs σ2 τ2 σ3) by done.
  Qed.
End path_type_check.

Hint Extern 0 (PathTyped _ _ (list _)) =>
  eapply @list_typed : typeclass_instances.
Hint Extern 0 (LookupE _ (list _) _ _) =>
  eapply @list_path_lookup : typeclass_instances.

Instance typed_dec `{TypeCheckSpec E T V (λ _, True)}
  `{∀ τ1 τ2 : T, Decision (τ1 = τ2)} Γ x τ : Decision (Γ ⊢ x : τ).
Proof.
 refine (
  match Some_dec (type_check Γ x) with
  | inleft (τ'↾_) => cast_if (decide (τ = τ'))
  | inright _ => right _
  end); abstract (rewrite <-type_check_correct by done; congruence).
Defined.
Instance path_typed_dec `{PathTypeCheckSpec E T R}
  `{∀ τ1 τ2 : T, Decision (τ1 = τ2)} Γ p τ σ : Decision (Γ ⊢ p : τ ↣ σ).
Proof.
 refine (cast_if (decide (τ !!{Γ} p = Some σ)));
  abstract by rewrite <-path_type_check_correct by done.
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
    unless (τ2 = τ1) by done; pose proof (typed_unique _ x τ2 τ1 H2 H)
  | H : _ ⊢ ?x : ?τ1, H2 : _ ⊢ ?x : ?τ2 |- _ =>
    unless (τ2 = τ1) by done; pose proof (typed_unique_alt _ x τ2 τ1 H2 H)
  | H : _ ⊢ [] : _ ↣ _ |- _ => rewrite list_typed_nil in H
  | H : _ ⊢ ?p : ?τ ↣ ?σ1, H2 : _ ⊢ ?p : ?τ ↣ ?σ2 |- _ =>
    unless (σ2 = σ1) by done; pose proof (path_typed_unique_r _ p τ σ2 σ1 H2 H)
  | H : _ ⊢ ?p : ?τ1 ↣ ?σ, H2 : _ ⊢ ?p : ?τ2 ↣ ?σ |- _ =>
    unless (τ2 = τ1) by done; pose proof (path_typed_unique_l _ p τ2 τ1 σ H2 H)
  end.
Ltac simplify_type_equality' :=
  repeat (progress simpl in * || simplify_type_equality).
