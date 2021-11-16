(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export axiomatic.
Require Import axiomatic_graph type_preservation.

Local Hint Extern 1 (## _) => solve_mem_disjoint: core.
Local Hint Extern 1 (sep_valid _) => solve_mem_disjoint: core.
Local Hint Extern 1 (_ ≤ _) => lia: core.

(** * Adequacy *)
(** We prove that the Hoare judgment indeed implies partial program
correctness. *)
Lemma ax_stmt_adequate `{EnvSpec K} Γ δ Q s m S' cmτ :
  ✓ Γ → ✓{Γ,'{m}} δ → ✓{Γ} m → mem_locks m = ∅ → (Γ,'{m},[]) ⊢ s : cmτ →
  Γ\ δ ⊨ₛ {{ assert_eq_mem (cmap_erase m) }} s {{ Q }} →
  Γ\ δ ⊢ₛ State [] (Stmt ↘ s) m ⇒* S' →
  (**i 1.) *) (∃ n' m',
    S' = State [] (Stmt ↗ s) m' ∧
    assert_holds (Q voidV) Γ '{m'} δ [] n' (cmap_erase m')) ∨
  (**i 2.) *) (∃ n' m' v,
    S' = State [] (Stmt (⇈ v) s) m' ∧
    assert_holds (Q v) Γ '{m'} δ [] n' (cmap_erase m')) ∨
  (**i 3.) *) red (cstep Γ δ) S'.
Proof.
  intros ?. revert m S'. cut (∀ P n1 n2 k φ m S' τf,
    ✓{Γ,'{m} } δ →
    (Γ,'{m},(locals k).*2) ⊢ φ : τf → (Γ,'{m}) ⊢ k : τf ↣ Stmt_type cmτ →
    ✓{Γ} m → maybe Undef φ = None → focus_locks_valid φ m →
    ax_graph ax_disjoint_cond (ax_stmt_post (dassert_pack_top P Q) s cmτ)
      Γ δ '{m} [] (n1 + n2) k φ m →
    Γ\ δ\ [] ⊢ₛ State k φ m ⇒^n1 S' → ∃ k' φ' m',
      S' = State k' φ' m' ∧
      maybe Undef φ' = None ∧ focus_locks_valid φ' m' ∧ ✓{Γ} m' ∧
      ax_graph ax_disjoint_cond (ax_stmt_post (dassert_pack_top P Q) s cmτ)
        Γ δ '{m'} [] n2 k' φ' m').
  { intros help m S' ???? Hax p.
    apply csteps_rcsteps, rtc_bsteps in p; destruct p as [n p].
    destruct (help (assert_eq_mem (cmap_erase m)) n 1 [] (Stmt ↘ s) m S'
      (Stmt_type cmτ)) as (k'&φ'&m'&->&?&?&?&Hax'); done || eauto.
    { by repeat typed_constructor. }
    { typed_constructor. }
    { by apply Hax. }
    inversion Hax' as [|??? [d' ????]|???? Hred]; clear Hax'; subst.
    { destruct d'; naive_solver. }
    do 2 right; apply (red_subrel (rcstep Γ δ [])); auto using rcstep_cstep.
    apply (Hred '{m'} 0 _ ∅); auto.
    split; rewrite ?sep_right_id by auto;
      eauto using cmap_valid_memenv_valid, cmap_empty_valid. }
  intros P n1 n2; induction n1 as [n1 IH] using lt_wf_ind.
  intros k φ m S' τf ?????? Hax p.
  inv_rcsteps p as [|n' ? S ? p1 p2]; eauto 10 using mk_ax_next, ax_weaken.
  assert (ax_next ax_disjoint_cond (ax_stmt_post (dassert_pack_top P Q) s cmτ)
    Γ δ '{m} [] (n' + n2) ∅ S) as Hnext.
  { eapply ax_step; eauto.
    + split; rewrite ?sep_right_id by auto;
        eauto using cmap_valid_memenv_valid, cmap_empty_valid.
    + rewrite cmap_dom_memenv_of; set_solver. }
  inversion Hnext as [Δ2 k2 ? φ2 m2 m2' mf (Hm2'&?) ????? Hax'];
    rewrite sep_right_id in Hm2' by auto; subst.
  assert (Γ ⊢ State k2 φ2 m2 : Stmt_type cmτ ∧ '{m} ⇒ₘ '{m2}) as [(τf2&?&?&?)].
  { eapply (cstep_preservation _ _ (State _ _ _) (State _ _ _));
      eauto using rcstep_cstep; exists τf; eauto. }
  cut (Δ2 = '{m2}); [intros ->; eauto using funenv_valid_weaken|].
  apply (anti_symm memenv_forward);
    eauto using memenv_subseteq_forward, cmap_memenv_of_subseteq.
Qed.