(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** We prove some correspondence results between the denotation semantics for
pure expressions and the small step operational semantics. *)
From stdpp Require Import fin_maps.
Require Export restricted_smallstep expression_eval.

Section expression_eval.
Context `{EnvSpec K}.
Implicit Types e : expr K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types E : ectx K.

Lemma expr_eval_ehstep Γ ρ e1 m ν :
  ⟦ e1 ⟧ Γ ρ m = Some ν → is_redex e1 →
  ∃ e2, Γ\ ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ e2 ⟧ Γ ρ m = Some ν.
Proof.
  revert e1 ν. assert (∀ a v,
    mem_forced Γ a m → m !!{Γ} a = Some v →
    Γ\ ρ ⊢ₕ load (% (Ptr a)), m ⇒ #v, m).
  { intros a v Hm ?. rewrite <-Hm at 2. do_ehstep. }
  apply (expr_eval_ind Γ ρ m (λ e _, is_redex e → (_:Prop))); intros;
    repeat match goal with
    | H : is_redex _ |- _ => inversion H; clear H
    | H : is_nf _ |- _ => inversion H; clear H
    | H : Forall is_nf ?es |- _ => erewrite (help es) by eauto; clear H
    | _ => progress simplify_option_eq
    | _ => by eexists; split; [do_ehstep|]
    end.
Qed.
Lemma expr_eval_subst_ehstep Γ ρ m E e1 ν :
  ⟦ subst E e1 ⟧ Γ ρ m = Some ν → is_redex e1 →
  ∃ e2, Γ\ ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ subst E e2 ⟧ Γ ρ m = Some ν.
Proof.
  rewrite expr_eval_subst; intros (ν'&Heval'&<-) ?.
  destruct (expr_eval_ehstep _ _ _ _ _ Heval') as (e2&?&?); trivial.
  exists e2; split; auto using subst_preserves_expr_eval.
Qed.
Lemma expr_eval_sound Γ δ m ρ e ν :
  ⟦ e ⟧ Γ ρ m = Some ν →
  Γ\ δ\ ρ ⊢ₛ State [] (Expr e) m ⇒* State [] (Expr (%# ν)) m.
Proof.
  induction e as [e IH] using expr_wf_ind; intros He.
  destruct (is_nf_or_redex e) as [He'|(E&e1&?&->)].
  { by destruct He'; simplify_option_eq. }
  destruct (expr_eval_subst_ehstep Γ ρ m E e1 ν)
    as (e2&?&?); simplify_map_eq; auto.
  econstructor; [do_cstep|]. apply IH; auto.
  rewrite !ectx_subst_size, <-Nat.add_lt_mono_l; eauto using ehstep_size.
Qed.
Lemma ehstep_expr_eval_locks Γ ρ m1 m2 e1 e2 ν :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → ⟦ e1 ⟧ Γ ρ m1 = Some ν →
  locks e1 = empty → locks e2 = ∅.
Proof. destruct 1; intros; simplify_option_eq; set_solver. Qed.
Lemma ehstep_expr_eval Γ ρ m1 m1' m2 e1 e2 ν :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → ⟦ e1 ⟧ Γ ρ m1 = Some ν →
  ⟦ e1 ⟧ Γ ρ m1' = Some ν → ⟦ e2 ⟧ Γ ρ m1' = Some ν.
Proof. destruct 1; intros; simplify_option_eq; set_solver. Qed.
Lemma ehstep_expr_eval_mem Γ ρ m1 m2 e1 e2 ν :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → ⟦ e1 ⟧ Γ ρ m1 = Some ν → m1 = m2.
Proof.
  destruct 1; intros; simplify_option_eq; eauto;
    rewrite ?mem_unlock_empty;
    try destruct (val_true_false_dec _ _) as [[[??]|[??]]|[??]];
    set_solver.
Qed.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor: core.
Lemma ehstep_expr_eval_typed Γ Δ ρ m1 m2 e1 e2 ν τlr :
  ✓ Γ → Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  ✓{Γ,Δ} m1 → ⟦ e1 ⟧ Γ ρ m1 = Some ν → ✓{Δ}* ρ →
  (Γ,Δ,ρ.*2) ⊢ e1 : τlr → (Γ,Δ,ρ.*2) ⊢ e2 : τlr.
Proof.
  destruct 2; intros; simplify_option_eq;
    typed_inversion_all; decompose_Forall_hyps;
    repeat match goal with
    | H : ?ρ.*2 !! ?i = Some ?τ1, H2 : ?ρ !! _ = Some (_,?τ2) |- _ =>
       rewrite list_lookup_fmap, H2 in H; decompose_Forall_hyps
    end; try typed_constructor; eauto using
      val_unop_typed, val_binop_typed, val_cast_typed, addr_top_typed,
      cmap_index_typed_valid, addr_top_strict, lockset_empty_valid,
      addr_elt_typed, addr_elt_strict, addr_elt_typed, addr_elt_strict,
      val_lookup_seg_typed, val_alter_const_typed, mem_lookup_typed.
Qed.
Lemma ehstep_pure_expr_eval Γ ρ m1 m2 e1 e2 :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure e1 → ⟦ e1 ⟧ Γ ρ m1 = ⟦ e2 ⟧ Γ ρ m1.
Proof.
  destruct 1; inversion 1;
    by repeat match goal with
    | H : is_pure (%#{_} _) |- _ => inversion H; clear H
    | _ => progress simplify_option_eq
    end || set_solver.
Qed.
Lemma expr_eval_complete Γ δ m1 m2 ρ e ν :
  Γ\ δ\ ρ ⊢ₛ State [] (Expr e) m1 ⇒* State [] (Expr (%# ν)) m2 →
  is_pure e → ⟦ e ⟧ Γ ρ m1 = Some ν ∧ m1 = m2.
Proof.
  remember (State [] (Expr e) m1) as S eqn:He; intros p; revert S p m1 e He.
  refine (rtc_ind_l _ _ _ _); [naive_solver|].
  intros S1 S2 p p' IH m1 e -> Hsafe; revert p' Hsafe IH. pattern S2.
  apply (rcstep_focus_inv _ _ _ _ _ _ p); clear p; try done.
  * intros E e1 e2 m1' -> p' p Hpure IH.
    assert (is_pure e1) as Hpure' by eauto using ectx_is_pure.
    assert (m1' = m1) by eauto using ehstep_pure_mem, eq_sym; subst.
    destruct (IH m1 (subst E e2)) as [<- ->]; eauto using ehstep_pure_mem,
      eq_sym, f_equal, ectx_subst_is_pure, ehstep_pure_pure.
    eauto using subst_preserves_expr_eval, ehstep_pure_expr_eval.
  * intros E Ω f τs τ Ωs vs -> _ _ Hsafe.
    apply ectx_is_pure in Hsafe; inversion Hsafe.
  * intros E e1 -> ?? p'. inv_rcsteps p'; inv_rcstep.
Qed.
Lemma expr_eval_subst_ehsafe Γ ρ m E e ν :
  ⟦ subst E e ⟧ Γ ρ m = Some ν → is_redex e → Γ\ ρ ⊢ₕ safe e, m.
Proof.
  intros. destruct (expr_eval_subst_ehstep Γ ρ m E e ν)
    as (e2&?&?); eauto using ehsafe_step.
Qed.
End expression_eval.
