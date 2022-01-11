(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export tactics smallstep executable.

Section soundness.
Context `{EnvSpec K}.

Lemma assign_exec_correct Γ m a v ass va' v' :
  assign_exec Γ m a v ass = Some (va',v') ↔ assign_sem Γ m a v ass va' v'.
Proof.
  split; [|by destruct 1; simplify_option_eq].
  intros. destruct ass; simplify_option_eq; econstructor; eauto.
Qed.
Lemma ctx_lookup_correct (k : ctx K) i : ctx_lookup i k = locals k !! i.
Proof.
  revert i.
  induction k as [|[]]; intros [|x]; f_equal'; rewrite ?list_lookup_fmap; auto.
Qed.
Lemma ehexec_sound Γ k m1 m2 e1 e2 :
  (e2,m2) ∈ ehexec Γ k e1 m1 → Γ\ locals k ⊢ₕ e1, m1 ⇒ e2, m2.
Proof.
  intros. destruct e1;
    repeat match goal with
    | H : assign_exec _ _ _ _ _ = Some _ |- _ =>
      apply assign_exec_correct in H
    | _ => progress decompose_elem_of
    | H : ctx_lookup _ _ = _ |- _ => rewrite ctx_lookup_correct in H
    | _ => progress simplify_equality'
    | _ => case_match
    end; do_ehstep.
Qed.
Lemma ehexec_weak_complete Γ k e1 m1 e2 m2 :
  ehexec Γ k e1 m1 ≡ ∅ → 
  ¬Γ\ locals k ⊢ₕ e1, m1 ⇒ e2, m2.
Proof.
  destruct 2; 
    repeat match goal with
    | H : assign_sem _ _ _ _ _ _ _ |- _ =>
      apply assign_exec_correct in H
    | H : is_Some _ |- _ => destruct H as [??]
    | _ => progress decompose_empty
    | H : locals _ !! _ = Some _ |- _ => rewrite <-ctx_lookup_correct in H
    | H : option_to_set ?o ≫= _ ≡ _, Ho : ?o = Some _ |- _ =>
       rewrite Ho in H; csimpl in H; rewrite set_bind_singleton in H
    | _ => progress simplify_option_eq
    | _ => case_match
    | H : mguard (_) (_) ≡ ∅ |- _ => apply guard_empty in H
    | H : _ ∨ _ |- _ => destruct H
    end; eauto.
Qed.
Lemma ehstep_dec Γ ρ e1 m1 :
  (∃ e2 m2, Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2) ∨ ∀ e2 m2, ¬Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2.
Proof.
  set (k:=(λ oτ, CLocal (oτ.1) (oτ.2)) <$> ρ).
  replace ρ with (locals k) by (induction ρ as [|[]]; f_equal'; auto).
  destruct (set_choose_or_empty (ehexec Γ k e1 m1)) as [[[e2 m2]?]|];
    eauto using ehexec_sound, ehexec_weak_complete.
Qed.
Lemma cexec_sound Γ δ S1 S2 : Γ\ δ ⊢ₛ S1 ⇒ₑ S2 → Γ\ δ ⊢ₛ S1 ⇒ S2.
Proof.
  intros. assert (
    ∀ (k : ctx K) e m,
      ehexec Γ k e m ≡ ∅ → 
      maybe_ECall_redex e = None →
      is_redex e → 
      ¬Γ\ locals k ⊢ₕ safe e, m
  ).
  { intros k e m He. rewrite eq_None_not_Some.
    intros Hmaybe Hred Hsafe; apply Hmaybe; destruct Hsafe.
    * eexists; apply maybe_ECall_redex_Some; eauto.
    * edestruct ehexec_weak_complete; eauto. }
  destruct S1;
    repeat match goal with
    | H : _ ∈ ehexec _ _ _ _ |- _ => apply ehexec_sound in H
    | H : _ ∈ expr_redexes _ |- _ =>
      apply expr_redexes_correct in H; destruct H
    | H : maybe VBase ?vb = _ |- _ => is_var vb; destruct vb
    | H : maybe_ECall_redex _ = Some _ |- _ =>
      apply maybe_ECall_redex_Some in H; destruct H
    | _ => progress decompose_elem_of
    | _ => case_decide
    | _ => case_match
    | _ => progress simplify_equality'
    | H : maybe2 _ ?e = Some _ |- _ => is_var e; destruct e
    end; do_cstep.
Qed.
Lemma cexecs_sound Γ δ S1 S2 : Γ\ δ ⊢ₛ S1 ⇒ₑ* S2 → Γ\ δ ⊢ₛ S1 ⇒* S2.
Proof. induction 1; econstructor; eauto using cexec_sound. Qed.
Lemma cexec_ex_loop Γ δ S :
  ex_loop (λ S1 S2, Γ\ δ ⊢ₛ S1 ⇒ₑ S2) S → ex_loop (cstep Γ δ) S.
Proof.
  revert S; cofix COH; intros S; destruct 1 as [S1 S2 p].
  econstructor; eauto using cexec_sound.
Qed.
End soundness.
