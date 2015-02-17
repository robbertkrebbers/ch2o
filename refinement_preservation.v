(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export refinement_system smallstep.
Require Import executable_sound type_preservation operations_refine.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section refinement_preservation.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types α : bool.
Implicit Types o : index.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.

Ltac solve_length := simplify_equality'; repeat
  match goal with H : Forall2 _ _ _ |- _ => apply Forall2_length in H end; lia.

Hint Extern 0 (_ ⊑{_,_,_} _ : _) => refine_constructor.
Hint Extern 0 (_ ⊑{_,_,_@_↦_} _ : _) => refine_constructor.
Hint Extern 0 (_ ⊑{_,_,_@_↦_} _ : _ ↣ _) => refine_constructor.
Hint Resolve cmap_refine_memenv_refine'.
Hint Resolve addr_alive_refine addr_strict_refine mem_writable_refine.
Hint Resolve val_unop_ok_refine val_binop_ok_refine val_cast_ok_refine.
Hint Resolve val_true_refine val_false_refine mem_freeable_refine.
Hint Resolve val_lookup_is_Some_refine.
Hint Immediate cmap_refine_valid_l' cmap_refine_valid_l.
Hint Immediate cmap_refine_valid_r' cmap_refine_valid_r.
Hint Immediate addr_refine_typed_l val_refine_typed_l.
Hint Immediate addr_refine_typed_r val_refine_typed_r.
Hint Immediate expr_refine_typed_l expr_refine_typed_r.
Hint Immediate ctx_refine_stack_typed_r ctx_refine_stack_typed_l.
Hint Immediate ctx_refine_typed_l ctx_refine_typed_r.
Hint Immediate ectx_refine_typed_l ectx_refine_typed_r.
Hint Immediate vals_refine_typed_l vals_refine_typed_r.
Hint Immediate locks_refine_valid_l locks_refine_valid_r.
Hint Immediate stmt_refine_typed_l stmt_refine_typed_r.
Hint Resolve direction_out_refine_r direction_in_refine_r.
Hint Resolve sctx_item_catch_refine.
Hint Immediate meminj_extend_reflexive.
Hint Immediate sctx_item_subst_refine.
Hint Resolve meminj_extend_inverse cmap_refine_inverse'.
Hint Immediate addr_alive_refine'.
Hint Extern 0 (is_undef_state (State _ (Undef ?Su) _)) => by exists Su.

Lemma assign_refine Γ α f m1 m2 ass a1 a2 v1 v2 v1' va1' τ τ' σ :
  ✓ Γ → m1 ⊑{Γ,α,f} m2 → assign_typed Γ τ τ' ass σ →
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : TType τ → v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ' →
  assign_sem Γ m1 a1 v1 ass v1' va1' → ∃ v2' va2',
    assign_sem Γ m2 a2 v2 ass v2' va2' ∧
    v1' ⊑{Γ,α,f@'{m1}↦'{m2}} v2' : σ ∧ va1' ⊑{Γ,α,f@'{m1}↦'{m2}} va2' : τ.
Proof.
  destruct 3 as [τ'|op τ' σ|op τ' σ];
    inversion 3 as [|? va1|? va1]; simplify_equality';
    repeat match goal with
    | H : context [type_of _] |- _ =>
       erewrite addr_refine_type_of_l in H by eauto
    | |- _ => erewrite addr_refine_type_of_l by eauto
    end.
  * exists (val_cast (type_of a2) v2) (val_cast (type_of a2) v2);
      repeat constructor; erewrite ?addr_refine_type_of_r by eauto;
      eauto using val_cast_refine, val_cast_ok_refine.
  * destruct (mem_lookup_refine Γ α f ('{m1}) ('{m2}) m1 m2 a1 a2 va1 τ)
      as (va2&?&?); eauto.
    set (v2':=val_cast (type_of a2) (val_binop Γ op va2 v2)).
    exists v2' v2'; unfold v2';
      repeat constructor; erewrite ?addr_refine_type_of_r by eauto;
      eauto using val_binop_ok_refine, val_cast_ok_refine,
      val_binop_refine, val_cast_refine.
  * destruct (mem_lookup_refine Γ α f ('{m1}) ('{m2}) m1 m2 a1 a2 v1' τ)
      as (v2'&?&?); eauto.
    set (v2'':=val_cast (type_of a2) (val_binop Γ op v2' v2)).
    exists v2' v2''; unfold v2'';
      repeat constructor; erewrite ?addr_refine_type_of_r by eauto;
      eauto using val_binop_ok_refine, val_cast_ok_refine,
      val_binop_refine, val_cast_refine.
Qed.
Ltac go f := eexists f, _, _; split_ands; [do_ehstep| | |by auto].
Lemma ehstep_refine_forward Γ α f m1 m2 m1' ρ1 ρ2 τs e1 e2 e1' τlr :
  ✓ Γ → Γ\ ρ1 ⊢ₕ e1, m1 ⇒ e1', m1' →
  m1 ⊑{Γ,α,f} m2 → e1 ⊑{(Γ,τs),α,f@'{m1}↦'{m2}} e2 : τlr →
  '{m1} ⊢* ρ1 :* τs → '{m2} ⊢* ρ2 :* τs →
  Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) ρ1 ρ2 → ∃ f' m2' e2',
  (**i 1.) *) Γ\ ρ2 ⊢ₕ e2, m2 ⇒ e2', m2' ∧
  (**i 2.) *) m1' ⊑{Γ,α,f'} m2' ∧
  (**i 3.) *) e1' ⊑{(Γ,τs),α,f'@'{m1'}↦'{m2'}} e2' : τlr ∧
  (**i 4.) *) meminj_extend f f' ('{m1}) ('{m2}).
Proof.
  destruct 2; intros.
  * refine_inversion_all; decompose_Forall_hyps.
    go f; auto.
    refine_constructor; eauto using addr_top_strict, addr_top_refine,
      cmap_index_typed_valid, cmap_index_typed_representable,
      locks_empty_refine.
  * refine_inversion_all; [go f; auto|].
    exfalso; eauto using index_alive_1'.
  * refine_inversion_all; go f; eauto.
  * refine_inversion_all.
    edestruct assign_refine as (?&?&?&?&?); eauto.
    go f.
    + eapply mem_lock_refine'; eauto using mem_insert_refine',
        mem_insert_writable, addr_refine_weaken, mem_insert_forward.
    + erewrite !mem_lock_memenv_of, !mem_insert_memenv_of
        by eauto using mem_insert_writable, mem_insert_valid'.
      refine_constructor; eauto using locks_union_refine, lock_singleton_refine.
  * refine_inversion_all.
    edestruct mem_lookup_refine as (?&?&?); eauto; simplify_equality.
    go f; eauto using mem_force_refine'.
    erewrite !mem_force_memenv_of by eauto; eauto.
  * refine_inversion_all; go f; eauto.
    refine_constructor; eauto using addr_elt_strict, addr_elt_refine.
  * refine_inversion_all.
    edestruct val_lookup_seg_refine_alt as (?&?&?); eauto; simplify_equality.
    go f; eauto.
  * refine_inversion_all; go f; eauto 10 using type_valid_ptr_type_valid.
  * refine_inversion_all.
    edestruct (λ Γ f m1 m2 o1 o2 τ n, mem_alloc_new_refine' Γ α f m1 m2 o1 o2
      true perm_full (τ.[n])) as (f'&?&?&?); eauto using mem_allocable_fresh,
      index_typed_representable, TArray_valid, perm_full_mapped,
      perm_full_unshared.
    { by rewrite size_of_array, Nat2Z.inj_mul, Z2Nat.id
        by auto using Z_to_nat_neq_0_nonneg. }
    go f'; eauto.
    refine_constructor; eauto 8 using addr_top_array_refine,
      mem_alloc_new_index_typed', addr_top_array_strict, TArray_valid.
    eapply locks_refine_weaken; eauto using mem_alloc_new_forward',
      TArray_valid, option_eq_1, mem_allocable_fresh. 
  * refine_inversion_all; go f.
    + eauto using mem_free_refine', mem_freeable_index_refine.
    + repeat refine_constructor; eauto 10 using locks_refine_weaken,
        mem_free_forward', mem_free_refine', mem_freeable_index_refine.
  * refine_inversion_all; go f; eauto.
    refine_constructor; eauto using val_unop_refine.
  * refine_inversion_all; go f; eauto.
    refine_constructor; eauto using val_binop_refine, locks_union_refine.
  * refine_inversion_all; go f;
      eauto 10 using mem_unlock_refine', expr_refine_weaken, mem_unlock_forward.
  * refine_inversion_all; go f;
      eauto 10 using mem_unlock_refine', expr_refine_weaken, mem_unlock_forward.
  * refine_inversion_all; go f;
      eauto 10 using mem_unlock_refine', expr_refine_weaken, mem_unlock_forward.
  * refine_inversion_all; go f; eauto.
    refine_constructor; eauto using val_cast_refine.
  * refine_inversion_all; go f; eauto.
    refine_constructor; eauto using locks_union_refine,ctree_alter_const_refine.
Qed.
Lemma ehstep_refine_backward Γ α f m1 m2 m2' ρ1 ρ2 τs e1 e2 e2' τlr :
  ✓ Γ → Γ\ ρ2 ⊢ₕ e2, m2 ⇒ e2', m2' →
  m1 ⊑{Γ,α,f} m2 → e1 ⊑{(Γ,τs),α,f@'{m1}↦'{m2}} e2 : τlr →
  '{m1} ⊢* ρ1 :* τs → '{m2} ⊢* ρ2 :* τs →
  Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) ρ1 ρ2 →
  (∃ f' m1' e1',
    (**i 1.) *) Γ\ ρ1 ⊢ₕ e1, m1 ⇒ e1', m1' ∧
    (**i 2.) *) m1' ⊑{Γ,α,f'} m2' ∧
    (**i 3.) *) e1' ⊑{(Γ,τs),α,f'@'{m1'}↦'{m2'}} e2' : τlr ∧
    (**i 4.) *) meminj_extend f f' ('{m1}) ('{m2}))
  ∨ is_redex e1 ∧ ¬Γ \ ρ1 ⊢ₕ safe e1, m1.
Proof.
  intros. destruct (Some_dec (maybe2 EAlloc e2)) as [[[τ e]?]|].
  { simplify_option_equality; refine_inversion_all; inv_ehstep;
      refine_inversion_all;
      try by (right; repeat constructor; inversion 1; inv_ehstep).
    { left; go f; eauto 10 using type_valid_ptr_type_valid. }
    edestruct (λ Γ f m1 m2 o1 o2 τ n, mem_alloc_new_refine' Γ α f m1 m2 o1 o2
      true perm_full (τ.[n])) as (f'&?&?&?); eauto using mem_allocable_fresh,
      index_typed_representable, TArray_valid, perm_full_mapped,
      perm_full_unshared.
    { by rewrite size_of_array, Nat2Z.inj_mul, Z2Nat.id
        by auto using Z_to_nat_neq_0_nonneg. }
    left; go f'; eauto.
    refine_constructor; eauto 8 using addr_top_array_refine,
      mem_alloc_new_index_typed', addr_top_array_strict, TArray_valid.
    eapply locks_refine_weaken; eauto using mem_alloc_new_forward',
      TArray_valid, option_eq_1, mem_allocable_fresh. }
  destruct (ehstep_dec Γ ρ1 e1 m1) as [(e1'&m1'&?)|?].
  * left. destruct (ehstep_refine_forward Γ α f
      m1 m2 m1' ρ1 ρ2 τs e1 e2 e1' τlr) as (f'&m2''&e2''&?&?&?&?); auto.
    destruct (ehstep_deterministic Γ ρ2 e2 m2 e2' m2' e2'' m2'');
      simplify_equality; eauto 10.
  * right; split; eauto using expr_refine_redex_inv, ehstep_is_redex.
    destruct 1; [refine_inversion_all; inv_ehstep|naive_solver].
Qed.
Lemma ehsafe_refine Γ α f m1 m2 ρ1 ρ2 τs e1 e2 τlr :
  ✓ Γ → Γ\ ρ1 ⊢ₕ safe e1, m1 → m1 ⊑{Γ,α,f} m2 →
  e1 ⊑{(Γ,τs),α,f@'{m1}↦'{m2}} e2 : τlr →
  '{m1} ⊢* ρ1 :* τs → '{m2} ⊢* ρ2 :* τs →
  Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) ρ1 ρ2 → Γ\ ρ2 ⊢ₕ safe e2, m2.
Proof.
  destruct 2 as [|e1 m1 e1' m1'].
  * intros; refine_inversion_all; [|done].
    edestruct EVal_refine_inv_l as (?&?&?&?&?&?); eauto. subst.
    by constructor.
  * intros. destruct (ehstep_refine_forward Γ α f m1 m2 m1' ρ1 ρ2 τs
      e1 e2 e1' τlr) as (?&?&?&?&?&?&?&?); auto; econstructor; eauto.
Qed.
Ltac invert :=
  repeat match goal with
  | _ => progress simplify_equality'
  | H : _ ∈ labels _ |- _ => erewrite <-stmt_refine_labels in H by eauto
  | H : _ ∉ labels _ |- _ => erewrite <-stmt_refine_labels in H by eauto
  | H : _ ⊑{_,_,_@_↦_}* #{_}* _ :* _ |- _ =>
     apply EVal_refine_inv_r in H; [|auto]; destruct H as (?&?&->&?&?&?)
  | H : ?X ⊑{_,_,_@_↦_} subst _ _ : _ |- _ =>
     apply esctx_item_subst_refine_inv_r in H; destruct H as (?&?&?&->&?&?&?&?)
  | H : ?X ⊑{_,_,_@_↦_} subst _ _ : _ |- _ =>
     apply ectx_subst_refine_inv_r in H; destruct H as (?&?&?&->&?&?)
  | H : ?X ⊑{_,_,_@_↦_} subst _ _ : _ |- _ =>
     apply sctx_item_subst_refine_inv_r in H; destruct H as (?&?&?&->&?&?)
  | H : ?X ⊑{_,_,_} ?Y : _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  | H : ?X ⊑{_,_,_@_↦_} ?Y : _ |- _ =>
     first [is_var X; is_var Y; fail 1
     |refine_inversion H; try done; [idtac]||by refine_inversion H]
  | H : ?X ⊑{_,_,_@_↦_} ?Y : _ ↣ _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  end.
Ltac go f ::= eexists f, _; split_ands; [do_cstep| |by auto].
Lemma cstep_refine_fun_cases Γ f α m1 m2 ρ Ω vb1 Ωs vs h τs τ σs σ :
  ✓ Γ → vb1 ⊑{Γ,α,f @'{m1}↦'{m2}} (ptrV (FunPtr h τs τ))%B : ((σs ~> σ).*)%BT →
  vb1 = (ptrV (FunPtr h τs τ))%B ∨
  α ∧ ¬Γ \ ρ ⊢ₕ safe (call #{Ω} (VBase vb1) @ #{Ωs}* vs), m1 ∧
    is_redex (call #{Ω} (VBase vb1) @ #{Ωs}* vs).
Proof.
  intros; destruct vb1 as [| | |[]|]; refine_inversion_all; first [left; done
  | right; split_ands; [done|inversion 1; inv_ehstep
                       |repeat constructor; auto using EVals_nf]].
Qed.
Lemma cstep_refine Γ δ1 δ2 α f S1 S2 S2' g :
  ✓ Γ → Γ\ δ2 ⊢ₛ S2 ⇒ S2' → ¬is_undef_state S1 →
  S1 ⊑{Γ,α,f} S2 : g →
  δ1 ⊑{Γ,α,f@'{SMem S1}↦'{SMem S2}} δ2 → ∃ f' S1',
  (**i 1.) *) Γ\ δ1 ⊢ₛ S1 ⇒ S1' ∧
  (**i 2.) *) S1' ⊑{Γ,α,f'} S2' : g ∧
  (**i 3.) *) meminj_extend f f' ('{SMem S1}) ('{SMem S2}).
Proof.
  intros ? p Hundef HS Hδ.
  destruct (cstep_preservation Γ δ2 S2 S2' g) as [HS2' _];
    eauto 2 using state_refine_typed_r, funenv_refine_typed_r.
  revert Hundef HS HS2' Hδ. case p; clear p.
  * intros m k ????; invert. go f; eauto.
  * intros m k l ????; invert. go f; eauto.
  * intros m k n ????; invert. go f; eauto.
  * intros m k l ????; invert. go f; eauto.
  * intros m k E e ????; invert. go f; eauto.
  * intros m1 m2 k E e1 e2 ?????; invert. destruct α.
    { edestruct ehstep_refine_backward as [(f'&?&?&?&?&?&?)|[??]];
        eauto using ctx_refine_stack.
      { go f'. repeat refine_constructor; eauto 9 using ctx_refine_weaken,
         ehstep_forward, ectx_subst_refine, ectx_refine_weaken. }
      go f. right; auto.
      eexists; split_ands; repeat typed_constructor; eauto. }
    edestruct ehstep_refine_forward as (f'&?&?&?&?&?&?);
      eauto using ctx_refine_stack, expr_refine_inverse, ctx_refine_inverse.
    eexists (meminj_inverse f'), _; split_ands; [do_cstep| |].
    { repeat refine_constructor; eauto.
      * eapply ectx_subst_refine; eauto using expr_refine_inverse.
        eapply ectx_refine_weaken; eauto 7 using ehstep_forward.
      * eapply ctx_refine_weaken; eauto 7 using ehstep_forward. }
    eauto 7 using ehstep_forward.
  * intros m k Ω h τs τ E Ωs vs; simpl; intros; invert.
    edestruct cstep_refine_fun_cases as [|(?&?&?)]; eauto.
    + invert. go f. 
      repeat refine_constructor; eauto 8 using mem_unlock_refine',
        locks_union_refine, locks_union_list_refine,
        ectx_refine_weaken, vals_refine_weaken,
        ctx_refine_weaken, mem_unlock_forward, option_eq_1_alt.
    + go f. right; auto. eexists; split_ands; eauto.
      repeat typed_constructor; eauto using base_val_refine_typed_l,
        EVals_typed, vals_refine_typed_l, locks_list_refine_valid_l.
  * intros; invert. eexists f, _; split_ands; [| |auto].
    { apply cstep_expr_undef; eauto 10 using ehsafe_refine,
        ctx_refine_stack, expr_refine_redex_inv. }
    repeat refine_constructor; eauto using mem_unlock_refine',
      expr_refine_weaken, ctx_refine_weaken, mem_unlock_forward.
  * intros; invert. go f.
    repeat refine_constructor; eauto using mem_unlock_forward,val_refine_weaken,
      expr_refine_weaken, ctx_refine_weaken, mem_unlock_refine'.
  * intros; invert. go f.
    repeat refine_constructor; eauto using mem_unlock_forward,val_refine_weaken,
      expr_refine_weaken, ctx_refine_weaken, mem_unlock_refine'.
  * intros; invert. edestruct val_true_refine_inv as [|(?&?&?)]; eauto.
    + go f. repeat refine_constructor;
        eauto using mem_unlock_refine', ctx_refine_weaken,
        expr_refine_weaken, stmt_refine_weaken, mem_unlock_forward.
    + go f. right; auto.
      eexists; split_ands; eauto; repeat typed_constructor; eauto.
  * intros; invert. edestruct val_false_refine_inv as [|(?&?&?)]; eauto.
    + go f. repeat refine_constructor;
        eauto using mem_unlock_refine', ctx_refine_weaken,
        expr_refine_weaken, stmt_refine_weaken, mem_unlock_forward.
    + go f. right; auto.
      eexists; split_ands; eauto; repeat typed_constructor; eauto.
  * intros; invert. go f; eauto.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
    repeat refine_constructor; eauto. by rewrite andb_false_r.
  * intros m k h s os vs ???????; invert.
    edestruct funenv_lookup_refine_r as (?&?&?&?&?&?&?&?&?&?&?); eauto 2.
    simplify_equality.
    edestruct (λ m1 m2 os2 vs1, mem_alloc_list_refine' Γ α f m1 m2
      (fresh_list (length vs1) (dom indexset m1)) os2 vs1) as (f'&?&?&?);
      eauto 2 using fresh_list_length, mem_allocable_list_fresh.
    go f'. erewrite !fmap_type_of by eauto.
    repeat refine_constructor; eauto 8 using mem_alloc_list_index_typed,
      mem_allocable_list_fresh, fresh_list_length,
      ctx_refine_weaken, mem_alloc_list_forward; simpl.
    rewrite snd_zip by (rewrite fresh_list_length;
      eauto using eq_sym, Nat.eq_le_incl, Forall3_length_lr).
    eauto 7 using stmt_refine_weaken, mem_alloc_list_refine',
      mem_alloc_list_forward, mem_allocable_list_fresh, fresh_list_length.
  * intros m k h oσs s ????; invert; case_match; simplify_equality'; try done.
    go f. rewrite !fst_zip by solve_length.
    repeat refine_constructor; eauto using ctx_refine_weaken,
      mem_foldr_free_forward, mem_foldr_free_refine.
  * intros m k h oσs s ????; invert; case_match; simplify_equality'; try done.
    go f. rewrite !fst_zip by solve_length.
    repeat refine_constructor; eauto using ctx_refine_weaken,
      val_refine_weaken, mem_foldr_free_forward, mem_foldr_free_refine.
  * intros; invert. go f.
    eauto 10 using ectx_subst_refine, locks_empty_refine.
  * intros; invert; go f; eauto 10.
  * intros; invert; go f; eauto 10.
  * intros; invert; go f; eauto 10.
  * intros; invert; go f; eauto 10.
  * intros m k Es ??????; invert; go f. edestruct sctx_item_typed_Some_l;
      naive_solver eauto using sctx_item_refine_typed_l.
  * intros; invert; go f; eauto 10.
  * intros; invert; go f; eauto 10.
  * intros m k d o τ s ??????; invert.
    edestruct (λ m1 m2 o2 τ, mem_alloc_new_refine' Γ α f m1 m2
      (fresh (dom _ m1)) o2 false perm_full τ) as (f'&?&?&?); eauto 1 using
      mem_allocable_fresh, perm_full_mapped, perm_full_unshared.
    go f'. repeat refine_constructor; eauto 7 using
      mem_alloc_new_index_typed', direction_refine_weaken, stmt_refine_weaken,
      ctx_refine_weaken, mem_alloc_new_forward',mem_allocable_fresh,option_eq_1_alt.
  * intros m k d o τ s ?????; invert. go f.
    repeat refine_constructor; eauto 7 using
      direction_refine_weaken, mem_free_refine',
      ctx_refine_weaken, mem_free_forward', option_eq_1_alt,
      cmap_index_typed_representable, cmap_index_typed_valid.
    eapply stmt_refine_weaken; eauto using mem_free_forward', mem_free_refine'.
Qed.
End refinement_preservation.
