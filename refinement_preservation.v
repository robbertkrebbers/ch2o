(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export refinement_system smallstep.
Require Import executable type_preservation.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section refinement_preservation.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γf : funtypes Ti.
Implicit Types o : index.
Implicit Types m : mem Ti.
Implicit Types e : expr Ti.
Implicit Types τ σ : type Ti.
Implicit Types a : addr Ti.
Implicit Types v : val Ti.

Ltac solve_length := simplify_equality'; repeat
  match goal with H : Forall2 _ _ _ |- _ => apply Forall2_length in H end; lia.

Hint Extern 0 (_ ⊑{_,_} _ : _) => refine_constructor.
Hint Extern 0 (_ ⊑{_,_@_↦_} _ : _) => refine_constructor.
Hint Extern 0 (_ ⊑{_,_@_↦_} _ : _ ↣ _) => refine_constructor.
Hint Resolve cmap_refine_memenv_refine'.
Hint Resolve addr_alive_refine addr_strict_refine mem_writable_refine.
Hint Resolve val_unop_ok_refine val_binop_ok_refine val_cast_ok_refine.
Hint Resolve val_true_refine val_false_refine mem_freeable_refine.
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
Hint Resolve sctx_item_breakto_refine.
Hint Immediate Undef_undef.
Hint Immediate meminj_extend_reflexive.
Hint Immediate sctx_item_subst_refine.

Lemma assign_refine_1 Γ f m1 m2 ass a1 a2 v1 v2 v1' va1' τ τ' σ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → assign_typed Γ τ τ' ass σ →
  a1 ⊑{Γ,f@'{m1}↦'{m2}} a2 : τ → v1 ⊑{Γ,f@'{m1}↦'{m2}} v2 : τ' →
  assign_sem Γ m1 a1 v1 ass v1' va1' → ∃ v2' va2',
    assign_sem Γ m2 a2 v2 ass v2' va2' ∧
    v1' ⊑{Γ,f@'{m1}↦'{m2}} v2' : σ ∧ va1' ⊑{Γ,f@'{m1}↦'{m2}} va2' : τ.
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
  * destruct (mem_lookup_refine Γ f ('{m1}) ('{m2}) m1 m2 a1 a2 va1 τ)
      as (va2&?&?); eauto.
    set (v2':=val_cast (type_of a2) (val_binop Γ op va2 v2)).
    exists v2' v2'; unfold v2';
      repeat constructor; erewrite ?addr_refine_type_of_r by eauto;
      eauto using val_binop_ok_refine, val_cast_ok_refine,
      val_binop_refine, val_cast_refine.
  * destruct (mem_lookup_refine Γ f ('{m1}) ('{m2}) m1 m2 a1 a2 v1' τ)
      as (v2'&?&?); eauto.
    set (v2'':=val_cast (type_of a2) (val_binop Γ op v2' v2)).
    exists v2' v2''; unfold v2'';
      repeat constructor; erewrite ?addr_refine_type_of_r by eauto;
      eauto using val_binop_ok_refine, val_cast_ok_refine,
      val_binop_refine, val_cast_refine.
Qed.
Lemma assign_refine Γ f m1 m2 ass a1 a2 v1 v2 v1' v2' va1' va2' τ τ' σ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → assign_typed Γ τ τ' ass σ →
  a1 ⊑{Γ,f@'{m1}↦'{m2}} a2 : τ → v1 ⊑{Γ,f@'{m1}↦'{m2}} v2 : τ' →
  assign_sem Γ m1 a1 v1 ass v1' va1' → assign_sem Γ m2 a2 v2 ass v2' va2' →
  v1' ⊑{Γ,f@'{m1}↦'{m2}} v2' : σ ∧ va1' ⊑{Γ,f@'{m1}↦'{m2}} va2' : τ.
Proof.
  intros ?????? Hass2. destruct (assign_refine_1 Γ f m1 m2
    ass a1 a2 v1 v2 v1' va1' τ τ' σ) as (?&?&Hass2'&?); auto.
  by rewrite <-assign_exec_correct in Hass2, Hass2'; simplify_equality.
Qed.
Lemma ehstep_refine Γ Γf f m1 m2 m1' m2' ρ1 ρ2 τs e1 e2 e1' e2' τlr :
  ✓ Γ → Γ\ ρ1 ⊢ₕ e1, m1 ⇒ e1', m1' → Γ\ ρ2 ⊢ₕ e2, m2 ⇒ e2', m2' →
  m1 ⊑{Γ,f} m2 → e1 ⊑{(Γ,Γf,τs),f@'{m1}↦'{m2}} e2 : τlr →
  '{m1} ⊢* ρ1 :* τs → '{m2} ⊢* ρ2 :* τs →
  Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) ρ1 ρ2 → ∃ f',
  (**i 1.) *) m1' ⊑{Γ,f'} m2' ∧
  (**i 2.) *) e1' ⊑{(Γ,Γf,τs),f'@'{m1'}↦'{m2'}} e2' : τlr ∧
  (**i 3.) *) meminj_extend f f' ('{m1}) ('{m2}).
Proof.
  intros ? [] p2 ?????.
  * refine_inversion_all; inv_ehstep; decompose_Forall_hyps.
    exists f; split_ands; eauto.
    refine_constructor; eauto using addr_top_strict, addr_top_refine,
      index_typed_valid, index_typed_representable, locks_empty_refine.
  * refine_inversion_all; inv_ehstep. exists f; eauto.
  * refine_inversion_all; inv_ehstep; exists f; eauto 10.
  * refine_inversion_all; inv_ehstep. edestruct assign_refine; eauto.
    exists f; split_ands; eauto.
    + eapply mem_lock_refine'; eauto using mem_insert_refine',
        mem_insert_writable, addr_refine_weaken, mem_insert_extend.
    + erewrite !mem_lock_memenv_of, !mem_insert_memenv_of
        by eauto using mem_insert_writable, mem_insert_valid'.
      refine_constructor; eauto using locks_union_refine, lock_singleton_refine.
  * refine_inversion_all; inv_ehstep.
    edestruct mem_lookup_refine as (?&?&?); eauto; simplify_equality.
    exists f; split_ands; eauto using mem_force_refine'.
    erewrite !mem_force_memenv_of by eauto; eauto.
  * refine_inversion_all; inv_ehstep. exists f; split_ands; eauto.
    refine_constructor; eauto using addr_elt_strict, addr_elt_refine.
  * refine_inversion_all; inv_ehstep.
     edestruct val_lookup_seg_refine_alt as (?&?&?); eauto; simplify_equality.
    exists f; eauto.
  * refine_inversion_all; inv_ehstep.
    edestruct (λ Γ f m1 m2 τ n, mem_alloc_refine' Γ f m1 m2 true (τ.[n]))
      as (f'&?&?&?); eauto using index_typed_representable, TArray_valid.
    { by rewrite size_of_array, Nat2Z.inj_mul, Z2Nat.id
        by auto using Z_to_nat_neq_0_nonneg. }
    exists f'; split_ands; eauto.
    refine_constructor; eauto using addr_top_array_refine,
      mem_alloc_index_typed', addr_top_array_strict, TArray_valid.
    eapply locks_refine_weaken;
      eauto using mem_alloc_extend', TArray_valid, option_eq_1.
  * refine_inversion_all; inv_ehstep. exists f; split_ands; eauto.
    + eauto using mem_free_refine', mem_freeable_index_refine.
    + repeat refine_constructor; eauto 10 using locks_refine_weaken,
        mem_free_extend', mem_free_refine', mem_freeable_index_refine.
  * refine_inversion_all; inv_ehstep. exists f; split_ands; eauto.
    refine_constructor; eauto using val_unop_refine.
  * refine_inversion_all; inv_ehstep. exists f; split_ands; eauto.
    refine_constructor; eauto using val_binop_refine, locks_union_refine.
  * refine_inversion_all; inv_ehstep.
    + exists f; eauto 10 using mem_unlock_refine',
        expr_refine_weaken, mem_unlock_extend.
    + exfalso; eauto using val_true_false_refine.
  * refine_inversion_all; inv_ehstep.
    + exfalso; eauto using val_false_true_refine.
    + exists f; eauto 10 using mem_unlock_refine',
        expr_refine_weaken, mem_unlock_extend.
  * refine_inversion_all; inv_ehstep. exists f;
      eauto 10 using mem_unlock_refine', expr_refine_weaken, mem_unlock_extend.
  * refine_inversion_all; inv_ehstep. exists f; split_ands; eauto.
    refine_constructor; eauto using val_cast_refine.
Qed.
Lemma ehstep_refine_l Γ Γf f m1 m2 m1' ρ1 ρ2 τs e1 e2 e1' τlr :
  ✓ Γ → Γ\ ρ1 ⊢ₕ e1, m1 ⇒ e1', m1' →
  m1 ⊑{Γ,f} m2 → e1 ⊑{(Γ,Γf,τs),f@'{m1}↦'{m2}} e2 : τlr →
  '{m1} ⊢* ρ1 :* τs → '{m2} ⊢* ρ2 :* τs →
  Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) ρ1 ρ2 → ∃ f' m2' e2',
  (**i 1.) *) Γ\ ρ2 ⊢ₕ e2, m2 ⇒ e2', m2' ∧
  (**i 2.) *) m1' ⊑{Γ,f'} m2' ∧
  (**i 3.) *) e1' ⊑{(Γ,Γf,τs),f'@'{m1'}↦'{m2'}} e2' : τlr ∧
  (**i 4.) *) meminj_extend f f' ('{m1}) ('{m2}).
Proof.
  intros ? p ?????. cut (∃ m2' e2', Γ\ ρ2 ⊢ₕ e2, m2 ⇒ e2', m2').
  { intros (m2'&e2'&?). destruct (ehstep_refine Γ Γf f m1 m2 m1' m2'
      ρ1 ρ2 τs e1 e2 e1' e2' τlr); naive_solver. }
  destruct p; refine_inversion_all; decompose_Forall_hyps;
    try by (eexists _, _; do_ehstep).
  * edestruct assign_refine_1 as (?&?&?&?&?); eauto. eexists _, _; do_ehstep.
  * edestruct mem_lookup_refine as (?&?&?); eauto. eexists _, _; do_ehstep.
  * edestruct val_lookup_seg_refine_alt as (?&?&?); eauto.
    eexists _, _; do_ehstep.
Qed.
Lemma ehstep_refine_r Γ Γf f m1 m2 m2' ρ1 ρ2 τs e1 e2 e2' τlr :
  ✓ Γ → Γ\ ρ2 ⊢ₕ e2, m2 ⇒ e2', m2' →
  m1 ⊑{Γ,f} m2 → e1 ⊑{(Γ,Γf,τs),f@'{m1}↦'{m2}} e2 : τlr →
  '{m1} ⊢* ρ1 :* τs → '{m2} ⊢* ρ2 :* τs →
  Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) ρ1 ρ2 →
  (∃ f' m1' e1',
    (**i 1.) *) Γ\ ρ1 ⊢ₕ e1, m1 ⇒ e1', m1' ∧
    (**i 2.) *) m1' ⊑{Γ,f'} m2' ∧
    (**i 3.) *) e1' ⊑{(Γ,Γf,τs),f'@'{m1'}↦'{m2'}} e2' : τlr ∧
    (**i 4.) *) meminj_extend f f' ('{m1}) ('{m2}))
  ∨ is_redex e1 ∧ ¬Γ \ ρ1 ⊢ₕ safe e1, m1.
Proof.
  intros ? p ?????. destruct (ehexec Γ ρ1 e1 m1) as [[e1' m1']|] eqn:p'.
  * left. eapply ehexec_sound in p'; eauto. destruct (ehstep_refine Γ Γf f
      m1 m2 m1' m2' ρ1 ρ2 τs e1 e2 e1' e2' τlr); naive_solver.
  * right; split.
    { destruct p; refine_inversion_all; repeat constructor. }
    destruct 1; [refine_inversion_all; inv_ehstep|].
    edestruct ehexec_weak_complete; eauto.
Qed.
Lemma ehsafe_refine Γ Γf f m1 m2 ρ1 ρ2 τs e1 e2 τlr :
  ✓ Γ → Γ\ ρ1 ⊢ₕ safe e1, m1 → m1 ⊑{Γ,f} m2 →
  e1 ⊑{(Γ,Γf,τs),f@'{m1}↦'{m2}} e2 : τlr →
  '{m1} ⊢* ρ1 :* τs → '{m2} ⊢* ρ2 :* τs →
  Forall2 (λ o1 o2, f !! o1 = Some (o2,[])) ρ1 ρ2 → Γ\ ρ2 ⊢ₕ safe e2, m2.
Proof.
  destruct 2 as [|e1 m1 e1' m1'].
  * intros; refine_inversion_all.
    edestruct EVal_refine_inv_l as (?&?&?&?&?&?); eauto. subst.
    by constructor.
  * intros. destruct (ehstep_refine_l Γ Γf f m1 m2 m1' ρ1 ρ2 τs
      e1 e2 e1' τlr) as (?&?&?&?&?&?&?&?); auto; econstructor; eauto.
Qed.
Ltac invert :=
  repeat match goal with
  | H : _ ∈ labels _ |- _ => erewrite <-stmt_refine_labels in H by eauto
  | H : _ ∉ labels _ |- _ => erewrite <-stmt_refine_labels in H by eauto
  | H : _ ⊑{_,_@_↦_}* #{_}* _ :* _ |- _ =>
     apply EVal_refine_inv_r in H; [|auto]; destruct H as (?&?&->&?&?&?)
  | H : ?X ⊑{_,_@_↦_} subst _ _ : _ |- _ =>
     apply esctx_item_subst_refine_inv_r in H; destruct H as (?&?&?&->&?&?)
  | H : ?X ⊑{_,_@_↦_} subst _ _ : _ |- _ =>
     apply ectx_subst_refine_inv_r in H; destruct H as (?&?&?&->&?&?)
  | H : ?X ⊑{_,_@_↦_} subst _ _ : _ |- _ =>
     apply sctx_item_subst_refine_inv_r in H; destruct H as (?&?&?&->&?&?)
  | H : ?X ⊑{_,_} ?Y : _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  | H : ?X ⊑{_,_@_↦_} ?Y : _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  | H : ?X ⊑{_,_@_↦_} ?Y : _ ↣ _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  end.
Ltac go f := eexists f, _; split_ands; [do_cstep| |by auto].
Lemma cstep_refine_r Γ Γf δ1 δ2 f S1 S2 S2' g :
  ✓ Γ → Γ\ δ2 ⊢ₛ S2 ⇒ S2' → ¬is_undef_state S1 → S1 ⊑{(Γ,Γf),f} S2 : g →
  δ1 ⊑{Γ,f@'{SMem S1}↦'{SMem S2}} δ2 : Γf → ∃ f' S1',
  (**i 1.) *) Γ\ δ1 ⊢ₛ S1 ⇒ S1' ∧
  (**i 2.) *) S1' ⊑{(Γ,Γf),f'} S2' : g ∧
  (**i 3.) *) meminj_extend f f' ('{SMem S1}) ('{SMem S2}).
Proof.
  intros ? p Hundef HS Hδ.
  destruct (cstep_preservation Γ Γf δ2 S2 S2' g) as [HS2' _];
    eauto 2 using state_refine_typed_r, funenv_refine_typed_r.
  revert Hundef HS HS2' Hδ. case p; clear p.
  * intros m k ????; invert. go f; eauto.
  * intros m k l ????; invert. go f; eauto.
  * intros m k n ????; invert. go f; eauto.
  * intros m k l ????; invert. go f; eauto.
  * intros m k E e ????; invert. go f; eauto.
  * intros m1 m2 k E e1 e2 ?????; invert.
    edestruct ehstep_refine_r as [(f'&?&?&?&?&?&?)|[??]];
      eauto using ctx_refine_stack.
    { go f'. repeat refine_constructor; eauto 9 using ctx_refine_weaken,
       ehstep_extend, ectx_subst_refine, ectx_refine_weaken. }
    go f. right; auto. eexists; split_ands; repeat typed_constructor; eauto.
  * intros m k h E Ωs vs ?????; invert. go f.
    repeat refine_constructor; eauto 8 using mem_unlock_refine',
      locks_union_list_refine, ectx_refine_weaken, vals_refine_weaken,
      ctx_refine_weaken, mem_unlock_extend, option_eq_1_alt.
  * intros; invert. eexists f, _; split_ands; [| |auto].
    { apply cstep_expr_undef; eauto 10 using ehsafe_refine,
        ctx_refine_stack, expr_refine_redex_inv. }
    repeat refine_constructor; eauto using mem_unlock_refine',
      expr_refine_weaken, ctx_refine_weaken, mem_unlock_extend.
  * intros; invert. go f.
    repeat refine_constructor; eauto using mem_unlock_extend, val_refine_weaken,
      expr_refine_weaken, ctx_refine_weaken, mem_unlock_refine'.
  * intros; invert. go f.
    repeat refine_constructor; eauto using mem_unlock_extend, val_refine_weaken,
      expr_refine_weaken, ctx_refine_weaken, mem_unlock_refine'.
  * intros; invert. edestruct val_true_refine_inv as [|[??]]; eauto.
    + go f. repeat refine_constructor;
        eauto using mem_unlock_refine', ctx_refine_weaken,
        expr_refine_weaken, stmt_refine_weaken, mem_unlock_extend.
    + go f. right; auto.
      eexists; split_ands; eauto; repeat typed_constructor; eauto.
  * intros; invert. edestruct val_false_refine_inv as [|[??]]; eauto.
    + go f. repeat refine_constructor;
        eauto using mem_unlock_refine', ctx_refine_weaken,
        expr_refine_weaken, stmt_refine_weaken, mem_unlock_extend.
    + go f. right; auto.
      eexists; split_ands; eauto; repeat typed_constructor; eauto.
  * intros; invert. go f; eauto.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert; go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
  * intros; invert. go f; eauto 10.
    repeat refine_constructor; eauto. by rewrite andb_false_r.
  * intros m k h s os vs ???????; invert.
    edestruct funenv_lookup_refine_r as (?&?&?&?&?&?&?&?&?&?&?&?); eauto 2.
    simplify_equality.
    edestruct (λ m1 m2 os2 vs1, mem_alloc_val_list_refine' Γ f m1 m2
      (fresh_list (length vs1) (dom indexset m1)) os2 vs1) as (f'&?&?&?);
      eauto 2 using fresh_list_length, mem_allocable_list_fresh.
    go f'. erewrite !fmap_type_of by eauto.
    repeat refine_constructor; eauto 8 using mem_alloc_val_list_index_typed,
      mem_allocable_list_fresh, fresh_list_length,
      ctx_refine_weaken, mem_alloc_val_list_extend; simpl.
    rewrite snd_zip by (rewrite fresh_list_length;
      eauto using eq_sym, Nat.eq_le_incl, Forall3_length_lr).
    erewrite Fun_type_stack_types, (right_id_L [] (++)) by eauto.
    eauto 7 using stmt_refine_weaken, mem_alloc_val_list_refine',
      mem_alloc_val_list_extend, mem_allocable_list_fresh, fresh_list_length.
  * intros m k h oσs s ????; invert; case_match; simplify_equality'; try done.
    go f. rewrite !fst_zip by solve_length.
    repeat refine_constructor; eauto using ctx_refine_weaken,
      mem_foldr_free_extend, mem_foldr_free_refine.
  * intros m k h oσs s ????; invert; case_match; simplify_equality'; try done.
    go f. rewrite !fst_zip by solve_length.
    repeat refine_constructor; eauto using ctx_refine_weaken,
      val_refine_weaken, mem_foldr_free_extend, mem_foldr_free_refine.
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
    edestruct (λ m1 m2 τ, mem_alloc_refine' Γ f m1 m2 false τ
      (fresh (dom _ m1))) as (f'&?&?&?); eauto 1 using mem_allocable_fresh.
    go f'. repeat refine_constructor; eauto 7 using
      mem_alloc_index_typed', direction_refine_weaken, stmt_refine_weaken,
      ctx_refine_weaken, mem_alloc_extend', mem_allocable_fresh,option_eq_1_alt.
  * intros m k d o τ s ?????; invert. go f.
    repeat refine_constructor; eauto 7 using
      direction_refine_weaken, mem_free_refine',
      ctx_refine_weaken, mem_free_extend', option_eq_1_alt,
      index_typed_representable, index_typed_valid.
    eapply stmt_refine_weaken; eauto using mem_free_extend', mem_free_refine'.
Qed.
End refinement_preservation.
