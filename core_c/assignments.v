(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory operations.
Local Open Scope ctype_scope.

Inductive assign :=
  | Assign (**i ordinary assignment *)
  | PreOp : binop → assign (**i assignment operators and prefix increment,
     decrement, etc. *)
  | PostOp : binop → assign (**i postfix increment, decrement, etc. *).

(** * Semantics of assignments *)
(** The judgment [assign_sem Γ m a v ass va' v'] describes the resulting value
[v'] of an assignment [%{Ω1} a ::={ass} #{Ω2} v], and the value [va'] that needs
to be stored at [a] in [m]. *)
Inductive assign_sem `{Env K} (Γ : env K) (m : mem K)
     (a : addr K) (v : val K) : assign → val K → val K → Prop :=
  | Assign_sem v' :
     val_cast_ok Γ m (type_of a) v →
     v' = val_cast (type_of a) v →
     assign_sem Γ m a v Assign v' v'
  | PreOp_sem op va v' :
     m !!{Γ} a = Some va → val_binop_ok Γ m op va v →
     val_cast_ok Γ m (type_of a) (val_binop Γ op va v) →
     v' = val_cast (type_of a) (val_binop Γ op va v) →
     assign_sem Γ m a v (PreOp op) v' v'
  | PostOp_sem op va v' :
     m !!{Γ} a = Some va → val_binop_ok Γ m op va v →
     val_cast_ok Γ m (type_of a) (val_binop Γ op va v) →
     v' = val_cast (type_of a) (val_binop Γ op va v) →
     assign_sem Γ m a v (PostOp op) v' va.

Inductive assign_typed `{Env K} (τ1 : type K) : type K → assign → Prop :=
  | Assign_typed τ2 : cast_typed τ2 τ1 → assign_typed τ1 τ2 Assign
  | PreOp_typed op τ2 σ :
     binop_typed op τ1 τ2 σ → cast_typed σ τ1 →
     assign_typed τ1 τ2 (PreOp op)
  | PostOp_typed op τ2 σ :
     binop_typed op τ1 τ2 σ → cast_typed σ τ1 →
     assign_typed τ1 τ2 (PostOp op).

Section assignments.
Context `{EnvSpec K}.

Lemma assign_typed_type_valid Γ ass τ1 τ2 :
  assign_typed τ1 τ2 ass → ✓{Γ} (TType τ1) → ✓{Γ} τ2 → ✓{Γ} τ1.
Proof.
  destruct 1; eauto using cast_typed_type_valid,
    binop_typed_type_valid, type_valid_ptr_type_valid.
Qed.
Lemma assign_sem_erase Γ m a v ass va v' :
  assign_sem Γ (cmap_erase m) a v ass va v' ↔ assign_sem Γ m a v ass va v'.
Proof.
  split.
  * destruct 1; econstructor; rewrite <-1?val_binop_ok_erase,
      <-1?val_cast_ok_erase, <-1?mem_lookup_erase; eauto.
  * destruct 1; econstructor; rewrite ?val_binop_ok_erase,
      ?val_cast_ok_erase, ?mem_lookup_erase; eauto.
Qed.
Lemma assign_sem_deterministic Γ m a v ass va1 va2 v1 v2 :
  assign_sem Γ m a v ass va1 v1 → assign_sem Γ m a v ass va2 v2 →
  va1 = va2 ∧ v1 = v2.
Proof. by destruct 1; inversion 1; simplify_option_eq. Qed.
Lemma assign_preservation Γ Δ m ass a v va' v' τ1 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → assign_typed τ1 τ2 ass →
  (Γ,Δ) ⊢ a : TType τ1 → (Γ,Δ) ⊢ v : τ2 →
  assign_sem Γ m a v ass va' v' → (Γ,Δ) ⊢ va' : τ1 ∧ (Γ,Δ) ⊢ v' : τ1.
Proof.
  destruct 3; inversion 3; simplify_type_equality'; split; eauto using
    val_cast_typed, val_binop_typed, mem_lookup_typed, addr_typed_type_valid.
Qed.
Lemma assign_preservation_1 Γ Δ m ass a v va' v' τ1 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → assign_typed τ1 τ2 ass →
  (Γ,Δ) ⊢ a : TType τ1 → (Γ,Δ) ⊢ v : τ2 →
  assign_sem Γ m a v ass va' v' → (Γ,Δ) ⊢ va' : τ1.
Proof. eapply assign_preservation. Qed.
Lemma assign_preservation_2 Γ Δ m ass a v va' v' τ1 τ2 :
  ✓ Γ → ✓{Γ,Δ} m → assign_typed τ1 τ2 ass →
  (Γ,Δ) ⊢ a : TType τ1 → (Γ,Δ) ⊢ v : τ2 →
  assign_sem Γ m a v ass va' v' → (Γ,Δ) ⊢ v' : τ1.
Proof. eapply assign_preservation. Qed.
End assignments.
