(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import memory_separation assignments.

Lemma assign_sem_subseteq `{EnvSpec K} Γ Δ m1 m2 a v ass va v' τ1 τ2 :
  ✓ Γ → ✓{Γ,Δ} m1 → assign_typed τ1 τ2 ass →
  (Γ,Δ) ⊢ a : TType τ1 → (Γ,Δ) ⊢ v : τ2 →
  assign_sem Γ m1 a v ass va v' → m1 ⊆ m2 → assign_sem Γ m2 a v ass va v'.
Proof.
 destruct 3; inversion 3; econstructor; simplify_type_equality'; eauto 8 using
   mem_lookup_subseteq, val_cast_ok_weaken, val_binop_ok_weaken,
   cmap_subseteq_index_alive, mem_lookup_typed, val_binop_typed.
Qed.