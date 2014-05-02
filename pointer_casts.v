(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_environment.
Local Open Scope ctype_scope.

(** * Pointer casts *)
Reserved Infix ">*>" (at level 70).
Inductive castable `{IntEnv Ti, PtrEnv Ti} : type Ti → type Ti → Prop :=
  | castable_void τ : τ >*> voidT
  | castable_uchar τ : τ >*> ucharT
  | castable_refl τ : τ >*> τ
where "τ >*> σ" := (@castable _ _ _ τ σ) : C_scope.
Notation "(>*>)" := castable (only parsing) : C_scope.
Hint Extern 0 (_ >*> _) => reflexivity.

Section castable.
  Context `{EnvSpec Ti}.

  Lemma castable_alt τ1 τ2 : τ1 >*> τ2 ↔ τ1 = τ2 ∨ τ2 = ucharT ∨ τ2 = voidT.
  Proof. split. destruct 1; auto. intros [-> |[->| ->]]; constructor. Qed.
  Global Instance castable_dec (τ1 τ2 : type Ti) : Decision (τ1 >*> τ2).
  Proof.
   refine (cast_if (decide (τ1 = τ2 ∨ τ2 = ucharT ∨ τ2 = voidT)));
    abstract by rewrite castable_alt.
  Defined.
  Global Instance: Reflexive (>*>).
  Proof. constructor. Qed.

  Lemma castable_divide Γ τ1 τ2 : τ1 >*> τ2 → (size_of Γ τ2 | size_of Γ τ1).
  Proof.
    rewrite castable_alt. intros [->|[->| ->]]; rewrite ?size_of_void,
      ?size_of_int, ?int_size_char; auto using Nat.divide_1_l.
  Qed.
  Lemma castable_type_valid Γ τ σ : ✓{Γ} τ → τ >*> σ → ✓{Γ} σ ∨ σ = voidT.
  Proof. destruct 2; auto; left; repeat constructor. Qed.
  Lemma castable_ptr_type_valid Γ τ σ :
    ptr_type_valid Γ τ → τ >*> σ → ptr_type_valid Γ σ.
  Proof. destruct 2; auto; repeat constructor. Qed.

  Lemma castable_size_of Γ τ σ :
    ✓ Γ → ✓{Γ} τ → τ >*> σ → size_of Γ σ ≤ size_of Γ τ.
  Proof.
    intros HΓ Hτ. pose proof (size_of_pos _ _ HΓ Hτ). rewrite castable_alt.
    intros [?|[?|?]]; subst; auto.
    * rewrite size_of_int, int_size_char; lia.
    * rewrite size_of_void; lia.
  Qed.
  Lemma castable_size_of_pos Γ τ σ :
    ✓ Γ → ✓{Γ} τ → τ >*> σ → 0 < size_of Γ σ.
  Proof.
    intros. destruct (castable_type_valid Γ τ σ) as [?|?]; subst;
      auto using size_of_pos. rewrite size_of_void; lia.
  Qed.
  Lemma castable_size_of_ne_0 Γ τ σ :
    ✓ Γ → ✓{Γ} τ → τ >*> σ → size_of Γ σ ≠ 0.
  Proof. intros. eapply Nat.neq_0_lt_0, castable_size_of_pos; eauto. Qed.
End castable.
