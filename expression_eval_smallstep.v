(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** We prove some correspondence results between the denotation semantics for
pure expressions and the small step operational semantics. *)
Require Export smallstep expression_eval.

Section expression_eval.
Context `{EnvSpec Ti}.
Implicit Types e : expr Ti.
Implicit Types a : addr Ti.
Implicit Types v : val Ti.
Implicit Types av : addr Ti + val Ti.
Implicit Types E : ectx Ti.

Lemma ehstep_expr_eval Γ fs ρ e1 m av :
  ⟦ e1 ⟧ Γ fs ρ m = Some av → is_redex e1 →
  (**i 1). *) (∃ e2, Γ\ ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ e2 ⟧ Γ fs ρ m = Some av) ∨
  (**i 2). *) (∃ f F Ωs vs v, e1 = (call f @ #{Ωs}* vs)%E ∧ av = inr v ∧
                  length Ωs = length vs ∧ fs !! f = Some F ∧ F vs = Some v).
Proof.
  revert e1 av. assert (∀ es vs,
    Forall2 (λ e v, ⟦ e ⟧ Γ fs ρ m = Some (inr v)) es vs →
    Forall is_nf es → es = (#{locks <$> es}* vs)%E) as help.
  { induction 1; intros; decompose_Forall_hyps;
      repeat match goal with H : is_nf _ |- _ => destruct H end;
      simplify_option_equality; f_equal; auto. }
  apply (expr_eval_ind Γ fs ρ m (λ e _, is_redex e → (_:Prop))); intros;
    repeat match goal with
    | H : is_redex _ |- _ => inversion H; clear H
    | H : is_nf _ |- _ => inversion H; clear H
    | H : Forall is_nf ?es |- _ => erewrite (help es) by eauto; clear H
    | _ => progress simplify_option_equality
    | _ => by left; eexists; split; [do_ehstep|]
    end.
  right; eexists _,_,_,_,_; split_ands; eauto.
  rewrite fmap_length; eauto using Forall2_length.
Qed.
Lemma ehstep_expr_eval_subst Γ fs ρ m E e1 av :
  ⟦ subst E e1 ⟧ Γ fs ρ m = Some av → is_redex e1 →
  (**i 1). *) (∃ e2,
                  Γ\ ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ subst E e2 ⟧ Γ fs ρ m = Some av) ∨
  (**i 2). *) (∃ f F Ωs vs v, e1 = (call f @ zip_with EVal Ωs vs)%E ∧
                  length Ωs = length vs ∧ fs !! f = Some F ∧ F vs = Some v ∧
                  ⟦ subst E (# v)%E ⟧ Γ fs ρ m = Some av).
Proof.
  rewrite expr_eval_subst; intros (av'&Heval'&<-) ?.
  destruct (ehstep_expr_eval _ _ _ _ _ _ Heval')
    as [(e2&?&?)|(f&F&Ωs&vs&v&->&->&?&?&?)]; trivial.
  * left; exists e2; split; auto. apply subst_preserves_expr_eval.
    by rewrite expr_eval_lrval.
  * right; eexists f, F, Ωs, vs, v; eauto.
Qed.
Lemma ehsafe_expr_eval_subst Γ fs ρ m E e av :
  ⟦ subst E e ⟧ Γ fs ρ m = Some av → is_redex e → Γ\ ρ ⊢ₕ safe e, m.
Proof.
  intros Heval ?. destruct (ehstep_expr_eval_subst Γ fs ρ m E e av)
    as [(e2&?&?)|(f&F&Ωs&vs&v&->&?&?&?&?)]; trivial.
  * eauto using ehsafe_step.
  * by constructor.
Qed.
Lemma cred_expr_eval Γ fs δ e k m av :
  ⟦ e ⟧ Γ fs (get_stack k) m = Some av → ¬is_nf e →
  red (cstep_in_ctx Γ δ k) (State k (Expr e) m).
Proof.
  intros Heval He. destruct (is_nf_is_redex _ He) as (E'&e'&?&->).
  destruct (ehstep_expr_eval_subst _ _ _ _ _ _ _ Heval)
    as [(e2&?&?)|(f&F&Ωs&vs&v&->&?&?&?&?)]; trivial; solve_cred.
Qed.
End expression_eval.
