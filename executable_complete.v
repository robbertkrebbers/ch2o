(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export refinement_system executable_sound.
Require Import type_preservation refinement_preservation.

Section executable_complete.
Context `{EnvSpec Ti}.
Local Opaque singleton.

Ltac solve_length := simplify_equality'; repeat
  match goal with H : Forall2 _ _ _ |- _ => apply Forall2_length in H end; lia.
Hint Resolve cmap_refine_memenv_refine.
Hint Immediate meminj_extend_reflexive.
Hint Immediate ctx_typed_stack_typed.
Hint Resolve (elem_of_singleton_2 (C:=listset (state Ti))).

Lemma ehexec_complete Γ Γf m1 m2 k τs e1 e2 τlr :
  ✓ Γ → ✓{Γ} m1 → '{m1} ⊢* get_stack k :* τs → (Γ,Γf,'{m1},τs) ⊢ e1 : τlr →
  Γ\ get_stack k ⊢ₕ e1, m1 ⇒ e2, m2 → ∃ f e2' m2',
  (**i 1.) *) (e2', m2') ∈ ehexec Γ k e1 m1 ∧
  (**i 2.) *) e2' ⊑{(Γ,Γf,τs),false,f@'{m2'}↦'{m2}} e2 : τlr ∧
  (**i 3.) *) m2' ⊑{Γ,false,f} m2 ∧
  (**i 4.) *) meminj_extend meminj_id f ('{m1}) ('{m1}).
Proof.
  intros ? Hm1 Hρ He1 p. destruct (ehstep_preservation Γ Γf m1 m2
    (get_stack k) τs e1 e2 τlr) as (Hm2&He2&Hm); auto.
  revert Hm1 Hρ He1 Hm2 He2 Hm. case p; clear p; try by (
    intros; eexists meminj_id, _, _; repeat match goal with
    | H : assign_sem _ _ _ _ _ _ _ |- _ =>
       apply assign_exec_correct in H
    | _ => destruct (val_true_false_dec _ _) as [[[??]|[??]]|[??]]; try done
    | H : ?o = Some _ |- context [of_option ?o] => rewrite H
    | _ => rewrite ctx_lookup_correct
    | _ => progress simplify_equality'
    | _ => rewrite collection_bind_singleton
    | _ => rewrite elem_of_singleton
    | _ => rewrite elem_of_union
    | _ => rewrite collection_guard_True by done
    | _ => case_match; [|done]
    end; split_ands; eauto using cmap_refine_id', expr_refine_id).
  intros m Ω o τi τ n ??????? s ?; typed_inversion_all.
  set (o' := fresh (dom indexset m)) in *.
  assert (mem_allocable o' m) by (apply mem_allocable_fresh).
  edestruct (λ τ, mem_alloc_new_refine' Γ false meminj_id m m
    (fresh (dom indexset m)) o true perm_full (τ.[Z.to_nat n])) as (f&?&?&?);
    eauto using cmap_refine_id', perm_full_unshared, perm_full_mapped.
  eexists f, _, _; split_ands; [solve_elem_of| | |]; eauto.
  refine_constructor; eauto using lockset_valid_weaken, mem_alloc_new_forward'.
  * eapply locks_refine_weaken with false meminj_id ('{m}) ('{m});
      eauto using locks_refine_id, mem_alloc_new_forward', option_eq_1.
  * do 3 refine_constructor.
    eapply addr_top_array_refine; eauto using mem_alloc_new_index_typed'.
Qed.
Lemma cexec_complete Γ Γf δ S1 S2 g :
  ✓ Γ → (Γ,'{SMem S1}) ⊢ δ : Γf → (Γ,Γf) ⊢ S1 : g → Γ\ δ ⊢ₛ S1 ⇒ S2 → ∃ f S2',
  (**i 1.) *) Γ\ δ ⊢ₛ S1 ⇒ₑ S2' ∧
  (**i 2.) *) S2' ⊑{(Γ,Γf),false,f} S2 : g ∧
  (**i 3.) *) meminj_extend meminj_id f ('{SMem S1}) ('{SMem S1}).
Proof.
  intros ? Hδ1 HS1 p.
  destruct (cstep_preservation Γ Γf δ S1 S2 g) as [HS2 Hδ2]; auto.
  revert Hδ1 HS1 Hδ2 HS2. case p; clear p; try by (
    intros; simpl; repeat match goal with
    | _ => destruct (val_true_false_dec _ _) as [[[??]|[??]]|[??]]; try done
    end; eexists meminj_id, _; split_ands; eauto using state_refine_id).
  * intros m k Ei e ????.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
    destruct Ei; simpl; eauto.
  * intros m1 m2 k E e1 e2 ?? (τlr&Heτlr&?&?) ? _; simpl in *.
    typed_inversion Heτlr; edestruct (ectx_subst_typed_rev Γ Γf ('{m1})
      (get_stack_types k) E e1) as (τlr&?&?); eauto.
    edestruct (ehexec_complete Γ Γf m1 m2 k (get_stack_types k)
      e1 e2) as (f&e2'&m2'&?&?&?&?); eauto using ctx_typed_stack_typed.
    exists f (State k (Expr (subst E e2')) m2'); split_ands; auto.
    { assert (is_redex e1) as He1 by eauto using ehstep_is_redex.
      assert (maybe2 EVal (subst E e1) = None) as ->.
      { destruct E as [|Ei] using rev_ind; [by destruct He1|].
        by destruct Ei; by rewrite ?subst_app. }
      apply elem_of_bind; exists (E, e1).
      split; eauto using expr_redexes_complete.
      rewrite decide_False by esolve_elem_of.
      apply elem_of_bind; eexists; split; eauto; esolve_elem_of. }
    eleft; split_ands; repeat refine_constructor; eauto.
    + eapply ectx_subst_refine; eauto 10 using ectx_refine_weaken,
        ectx_refine_id, ehstep_forward, ehexec_sound.
    + eauto 10 using ctx_refine_weaken,
        ctx_refine_id, ehstep_forward, ehexec_sound.
  * intros m k f E Ωs vs ?????; simpl.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
    assert (maybe2 EVal (subst E (call f @ #{Ωs}* vs)%E) = None) as ->.
    { by destruct E as [|[] E] using rev_ind; rewrite ?subst_app. }
    apply elem_of_bind; exists (E, call f @ #{Ωs}* vs)%E.
    split; [|apply expr_redexes_complete; constructor; apply EVals_nf]; simpl.
    rewrite maybe_ECall_redex_Some_2 by done; eauto.
  * intros m k E e He Hsafe ????; simpl.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
    assert (maybe2 EVal (subst E e) = None) as ->.
    { destruct E as [|Ei] using rev_ind; [by destruct He|].
      by destruct Ei; by rewrite ?subst_app. }
    apply elem_of_bind; exists (E, e); split; [|by apply expr_redexes_complete].
    destruct (collection_choose_or_empty (ehexec Γ k e m)) as [[[e2 m2]?]|].
    { destruct Hsafe; econstructor (eauto using ehexec_sound). }
    rewrite decide_True by done.
    destruct (maybe_ECall_redex e) as [[[f Ωs] vs]|] eqn:Hcall; eauto.
    apply maybe_ECall_redex_Some in Hcall; destruct Hcall as [-> ?].
    by destruct Hsafe; constructor.
  * intros m k h s os vs ???? (τf&?&?&?) _ _; simpl in *; typed_inversion_all.
    set (os' := fresh_list (length vs) (dom indexset m)) in *.
    assert (mem_allocable_list m os') by (by apply mem_allocable_list_fresh).
    assert (length os' = length vs) by (by apply fresh_list_length).
    edestruct (funenv_lookup Γ ('{m}) Γf δ h)
      as (?&?&?&?&?&?&?&?&?); eauto; simplify_equality'.
    edestruct (mem_alloc_list_refine' Γ false meminj_id m m os' os vs vs) as
      (f&?&?&?); eauto using cmap_refine_id', vals_refine_id.
    exists f (State (CParams h (zip os' (type_of <$> vs)) :: k)
      (Stmt ↘ s) (mem_alloc_list Γ (zip os' vs) m)).
    split_ands; auto.
    { unfold of_option; simplify_option_equality; esolve_elem_of. }
    erewrite fmap_type_of by eauto.
    eleft; split_ands; simpl; repeat refine_constructor;
      eauto using mem_alloc_list_index_typed.
    + rewrite snd_zip by solve_length.
      eapply (stmt_refine_weaken _ _ false false meminj_id _ ('{m}));
        eauto using stmt_refine_id, mem_alloc_list_forward.
    + eauto 8 using ctx_refine_weaken, ctx_refine_id, mem_alloc_list_forward.
  * intros m k l ????; simpl; rewrite decide_True by solve_elem_of.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
  * intros m k Es l s ?????; simpl.
    rewrite sctx_item_subst_labels, decide_True by solve_elem_of.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
    destruct Es; simpl; solve_elem_of.
  * intros m k Es l s ?????; simpl; rewrite decide_False by done.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
  * intros m k Es l s ?????; simpl; rewrite decide_False by done.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
  * intros m k d o τ s ??? (τf&?&?&?) _ _; typed_inversion_all.
    destruct (mem_alloc_new_refine' Γ false meminj_id m m
      (fresh (dom indexset m)) o false perm_full τ) as (f&?&?&?);
      auto using cmap_refine_id', mem_allocable_fresh,
      perm_full_unshared, perm_full_mapped.
    eexists f, (State (CLocal (fresh (dom indexset m)) τ :: k) (Stmt d s)
      (mem_alloc Γ (fresh (dom indexset m)) false perm_full (val_new Γ τ) m)).
    split_ands; auto.
    { by destruct d; simplify_option_equality; try case_match; eauto. }
    eleft; split_ands; simpl; repeat refine_constructor;
      eauto using mem_alloc_new_index_typed'.
    + eapply (stmt_refine_weaken _ _ false false meminj_id _ ('{m}));
        eauto using stmt_refine_id, mem_alloc_new_forward', mem_allocable_fresh.
    + eapply (direction_refine_weaken _ false false meminj_id _ ('{m}));
        eauto using direction_refine_id,
        mem_alloc_new_forward', mem_allocable_fresh.
    + eauto 8 using ctx_refine_weaken, ctx_refine_id,
        mem_alloc_new_forward', mem_allocable_fresh.
  * intros m k d o τ s ?????.
    eexists meminj_id, _; split_ands; eauto using state_refine_id.
    by destruct d; simplify_option_equality; try case_match; eauto.
Qed.
Lemma cexec_complete_steps Γ Γf δ S1 S2 g :
  ✓ Γ → (Γ,'{SMem S1}) ⊢ δ : Γf → (Γ,Γf) ⊢ S1 : g → Γ\ δ ⊢ₛ S1 ⇒* S2 →
  ∃ f S2',
  (**i 1.) *) Γ\ δ ⊢ₛ S1 ⇒ₑ* S2' ∧
  (**i 2.) *) S2' ⊑{(Γ,Γf),false,f} S2 : g ∧
  (**i 3.) *) meminj_extend meminj_id f ('{SMem S1}) ('{SMem S1}).
Proof.
  intros ???; revert S2. apply rtc_ind_r.
  { eexists meminj_id, S1.
    repeat constructor (by eauto using state_refine_id). }
  intros S2' S3' ?? (f&S2&?&?&?).
  destruct (csteps_preservation Γ Γf δ S1 S2 g),
    (csteps_preservation Γ Γf δ S1 S2' g); auto using cexecs_sound.
  assert (¬is_undef_state S2).
  { intros ?. destruct (cnf_undef_state Γ δ S2');
      eauto using state_refine_undef, state_refine_inverse. }
  destruct (cstep_refine Γ Γf δ δ false f S2 S2' S3' g)
    as (f'&S3&?&?&?); auto.
  { eauto using funenv_refine_weaken, funenv_refine_id, state_refine_mem. }
  destruct (cexec_complete Γ Γf δ S2 S3 g) as (f''&S3''&?&?&?);
    eauto using state_refine_typed_l, funenv_typed_weaken.
  exists (f' ◎ f'') S3''. rewrite <-(orb_diag false).
  split_ands; eauto using state_refine_compose,
    rtc_r, meminj_extend_compose, meminj_extend_transitive.
Qed.
End executable_complete.
