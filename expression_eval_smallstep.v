(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** We prove some correspondence results between the denotation semantics for
pure expressions and the small step operational semantics. *)
Require Export smallstep expression_eval.

Section expression_eval.
Context `{EnvSpec K}.
Implicit Types e : expr K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types av : lrval K.
Implicit Types E : ectx K.

Lemma expr_eval_ehstep Γ fs ρ e1 m av :
  ⟦ e1 ⟧ Γ fs ρ m = Some av → is_redex e1 →
  (**i 1). *) (∃ e2, Γ\ ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ e2 ⟧ Γ fs ρ m = Some av) ∨
  (**i 2). *) (∃ Ω f τs τ F Ωs vs v,
    e1 = (call #{Ω} (ptrV (FunPtr f τs τ)) @ #{Ωs}* vs)%E ∧ av = inr v ∧
    length Ωs = length vs ∧ fs !! f = Some F ∧ F vs = Some v).
Proof.
  revert e1 av. assert (∀ a v,
    mem_forced Γ a m → m !!{Γ} a = Some v → Γ\ ρ ⊢ₕ load (%a), m ⇒ #v, m).
  { intros a v Hm ?. rewrite <-Hm at 2. do_ehstep. }
  assert (∀ es vs,
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
  right; eexists _,_,_,_,_,_,_,_; split_ands; eauto.
  rewrite fmap_length; eauto using Forall2_length.
Qed.
Lemma expr_eval_subst_ehstep Γ fs ρ m E e1 av :
  ⟦ subst E e1 ⟧ Γ fs ρ m = Some av → is_redex e1 →
  (**i 1). *) (∃ e2,
    Γ\ ρ ⊢ₕ e1, m ⇒ e2, m ∧ ⟦ subst E e2 ⟧ Γ fs ρ m = Some av) ∨
  (**i 2). *) (∃ Ω f τs τ F Ωs vs v,
    e1 = (call #{Ω} (ptrV (FunPtr f τs τ)) @ #{Ωs}* vs)%E ∧
    length Ωs = length vs ∧ fs !! f = Some F ∧ F vs = Some v ∧
    ⟦ subst E (# v)%E ⟧ Γ fs ρ m = Some av).
Proof.
  rewrite expr_eval_subst; intros (av'&Heval'&<-) ?.
  destruct (expr_eval_ehstep _ _ _ _ _ _ Heval')
    as [(e2&?&?)|(Ω&f&τs&τ&F&Ωs&vs&v&->&->&?&?&?)]; trivial.
  * left; exists e2; split; auto. apply subst_preserves_expr_eval.
    by rewrite expr_eval_lrval.
  * right; eexists Ω, f, τs, τ, F, Ωs, vs, v; eauto.
Qed.
Lemma expr_eval_sound Γ δ m k e av :
  ⟦ e ⟧ Γ ∅ (get_stack k) m = Some av →
  Γ\ δ ⊢ₛ State k (Expr e) m ⇒{k}* State k (Expr (%# av)) m.
Proof.
  induction e as [e IH] using expr_wf_ind; intros He.
  destruct (is_nf_or_redex e) as [He'|(E&e1&?&->)].
  { by destruct He'; simplify_option_equality. }
  destruct (expr_eval_subst_ehstep Γ ∅ (get_stack k) m E e1 av)
    as [(e2&?&?)|(?&?&?&?&?&?&?&?&?&?&?&?&?)]; simplify_map_equality; auto.
  econstructor; [do_cstep|]. apply IH; auto.
  rewrite !ectx_subst_size, <-Nat.add_lt_mono_l; eauto using ehstep_size.
Qed.
Lemma ehstep_expr_eval Γ ρ m1 m2 e1 e2 :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure e1 → ⟦ e1 ⟧ Γ ∅ ρ m1 = ⟦ e2 ⟧ Γ ∅ ρ m1.
Proof.
  destruct 1; inversion 1;
    by repeat match goal with
    | H : is_pure (#{_} _) |- _ => inversion H; clear H
    | _ => destruct (val_true_false_dec _ _) as [[[??]|[??]]|[??]]
    | _ => progress simplify_option_equality
    end || solve_elem_of.
Qed.
Lemma expr_eval_complete Γ δ m1 m2 k e av :
  Γ\ δ ⊢ₛ State k (Expr e) m1 ⇒{k}* State k (Expr (%# av)) m2 →
  is_pure e → ⟦ e ⟧ Γ ∅ (get_stack k) m1 = Some av ∧ m1 = m2.
Proof.
  remember (State k (Expr e) m1) as S eqn:He; intros p; revert S p m1 e He.
  refine (rtc_ind_l _ _ _ _); [naive_solver eauto using expr_eval_lrval|].
  intros S1 S2 [p Hk] p' IH m1 e -> Hsafe. revert p' Hk Hsafe IH. pattern S2.
  apply (cstep_focus_inv _ _ _ _ _ p); try (intros; solve_suffix_of); clear p.
  * intros E e1 e2 m1' -> p' p _ Hpure IH.
    assert (is_pure e1) as Hpure' by eauto using ectx_is_pure.
    assert (m1' = m1) by eauto using ehstep_pure_mem, eq_sym; subst.
    destruct (IH m1 (subst E e2)) as [<- ->]; eauto using ehstep_pure_mem,
      eq_sym, f_equal, ectx_subst_is_pure, ehstep_pure_pure.
    eauto using subst_preserves_expr_eval, ehstep_expr_eval.
  * intros E Ω f τs τ Ωs vs -> _ _ _ Hsafe.
    apply ectx_is_pure in Hsafe; inversion Hsafe.
  * intros E e1 -> ?? p'. inv_csteps p'; inv_cstep.
Qed.
Lemma expr_eval_subst_ehsafe Γ fs ρ m E e av :
  ⟦ subst E e ⟧ Γ fs ρ m = Some av → is_redex e → Γ\ ρ ⊢ₕ safe e, m.
Proof.
  intros Heval ?. destruct (expr_eval_subst_ehstep Γ fs ρ m E e av)
    as [(e2&?&?)|(Ω&f&τs&τ&F&Ωs&vs&v&->&?&?&?&?)]; trivial.
  * eauto using ehsafe_step.
  * by constructor.
Qed.
Lemma expr_eval_cred Γ fs δ e k m av :
  ⟦ e ⟧ Γ fs (get_stack k) m = Some av → ¬is_nf e →
  red (cstep_in_ctx Γ δ k) (State k (Expr e) m).
Proof.
  intros Heval He. destruct (is_nf_is_redex _ He) as (E'&e'&?&->).
  destruct (expr_eval_subst_ehstep _ _ _ _ _ _ _ Heval)
    as [(e2&?&?)|(Ω&f&τs&τ&F&Ωs&vs&v&->&?&?&?&?)]; trivial; solve_cred.
Qed.
End expression_eval.
