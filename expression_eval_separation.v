(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_separation expression_eval.

Lemma expr_eval_subseteq `{EnvSpec K} Γ Δ ρ m1 m2 e ν τlr :
  ✓ Γ → ✓{Γ,Δ} m1 → ✓{Δ}* ρ → (Γ,Δ,ρ.*2) ⊢ e : τlr →
  ⟦ e ⟧ Γ ρ m1 = Some ν → m1 ⊆ m2 → ⟦ e ⟧ Γ ρ m2 = Some ν.
Proof.
  intros. eapply expr_eval_weaken; eauto using cmap_subseteq_index_alive,
    mem_lookup_subseteq, mem_forced_subseteq.
Qed.
