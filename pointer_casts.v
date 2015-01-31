(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_environment.
Local Open Scope ctype_scope.

(** * Pointer casts *)
Reserved Infix ">*>" (at level 70).
Inductive castable `{Env Ti} : type Ti → ptr_type Ti → Prop :=
  | castable_None τ : τ >*> None
  | castable_uchar τ : τ >*> Some ucharT
  | castable_Some τ : τ >*> Some τ
where "τ >*> τp" := (@castable _ _ τ τp) : C_scope.
Notation "(>*>)" := castable (only parsing) : C_scope.
Hint Extern 0 (_ >*> _) => reflexivity.

Section castable.
Context `{EnvSpec Ti}.
Global Instance castable_dec (τ : type Ti) τp : Decision (τ >*> τp).
Proof.
 refine
  match τp with
  | None => left _ | Some τ' => cast_if (decide (τ' = ucharT ∨ τ = τ'))
  end; abstract (try inversion 1; naive_solver constructor).
Defined.
Lemma size_of_castable Γ τ τp : τ >*> τp → (ptr_size_of Γ τp | size_of Γ τ).
Proof. destruct 1; simpl; rewrite ?size_of_char; auto using Nat.divide_1_l. Qed.
Lemma align_of_castable Γ τ1 τ2 :
  ✓ Γ → τ1 >*> Some τ2 → (align_of Γ τ2 | align_of Γ τ1).
Proof.
  inversion_clear 2; rewrite ?align_of_char; auto using Nat.divide_1_l.
Qed.
Lemma bit_align_of_castable Γ τ1 τ2 :
  ✓ Γ → τ1 >*> Some τ2 → (bit_align_of Γ τ2 | bit_align_of Γ τ1).
Proof. eauto using Nat.mul_divide_mono_r, align_of_castable. Qed.
Lemma castable_type_valid Γ τ1 τ2 : ✓{Γ} τ1 → τ1 >*> Some τ2 → ✓{Γ} τ2.
Proof. by inversion 2; subst; repeat constructor. Qed.
Lemma castable_ptr_type_valid Γ τp1 τp2 : ✓{Γ} τp1 → τp1 >*> τp2 → ✓{Γ} τp2.
Proof.
  destruct 2; repeat constructor; auto using type_valid_ptr_type_valid.
Qed.
End castable.
