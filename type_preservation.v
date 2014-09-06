(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system smallstep.
Require Import executable.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section type_preservation.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γf : funtypes Ti.
Implicit Types o : index.
Implicit Types m : mem Ti.
Implicit Types e : expr Ti.
Implicit Types τ σ : type Ti.
Implicit Types a : addr Ti.
Implicit Types v : val Ti.

Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.
Hint Extern 0 (_ ⊢ _ : _ ↣ _) => typed_constructor.

Lemma initial_state_typed Γ Γf δ m f vs σs σ :
  ✓{Γ} m → (Γ,'{m}) ⊢ δ : Γf → Γf !! f = Some (σs,σ) →
  (Γ,'{m}) ⊢* vs :* σs → (Γ,Γf) ⊢ initial_state m f vs : f.
Proof. eexists (Fun_type f); simpl; eauto. Qed.
Lemma assign_preservation_1 Γ m ass a v v' va' τ1 τ2 σ :
  ✓ Γ → ✓{Γ} m → assign_typed Γ τ1 τ2 ass σ →
  (Γ,'{m}) ⊢ a : τ1 → (Γ,'{m}) ⊢ v : τ2 →
  assign_sem Γ m a v ass v' va' → (Γ,'{m}) ⊢ v' : σ.
Proof.
  destruct 3; inversion 3; simplify_type_equality';
    eauto using val_cast_typed, val_binop_typed, mem_lookup_typed.
Qed.
Lemma assign_preservation_2 Γ m ass a v v' va' τ1 τ2 σ :
  ✓ Γ → ✓{Γ} m → assign_typed Γ τ1 τ2 ass σ →
  (Γ,'{m}) ⊢ a : τ1 → (Γ,'{m}) ⊢ v : τ2 →
  assign_sem Γ m a v ass v' va' → (Γ,'{m}) ⊢ va' : τ1.
Proof.
  destruct 3; inversion 3; simplify_type_equality';
    eauto using val_cast_typed, val_binop_typed, mem_lookup_typed.
Qed.
Lemma ehstep_preservation Γ Γf m1 m2 ρ τs e1 e2 τlr :
  ✓ Γ → Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  ✓{Γ} m1 → (Γ,Γf,'{m1},τs) ⊢ e1 : τlr → '{m1} ⊢* ρ :* τs →
  (**i 1.) *) ✓{Γ} m2 ∧
  (**i 2.) *) (Γ,Γf,'{m2},τs) ⊢ e2 : τlr ∧
  (**i 3.) *) '{m1} ⊆{⇒} '{m2}.
Proof.
  intros ? [] ???.
  * typed_inversion_all; decompose_Forall_hyps; split_ands; auto.
    typed_constructor; eauto using addr_top_typed, addr_top_strict,
      index_typed_valid, index_typed_representable, lockset_empty_valid.
  * typed_inversion_all; auto.
  * typed_inversion_all; auto 7.
  * typed_inversion_all.
    rewrite <-and_assoc; apply and_wlog_l; intros; split_ands.
    + eapply mem_lock_valid'; eauto using mem_insert_writable,
        mem_insert_valid', assign_preservation_2.
    + typed_constructor; eauto using lockset_union_valid, lockset_valid_weaken,
        lock_singleton_valid, val_typed_weaken, assign_preservation_1.
    + intros. erewrite mem_lock_memenv_of by eauto using mem_insert_writable,
        mem_insert_valid', assign_preservation_2.
      eauto using mem_insert_extend, assign_preservation_2.
  * typed_inversion_all.
    rewrite <-and_assoc; apply and_wlog_l; intros; split_ands.
    + eauto using mem_force_valid'.
    + typed_constructor; eauto using lockset_valid_weaken,
        val_typed_weaken,  mem_lookup_typed.
    + eauto using mem_lookup_typed, mem_force_extend.
  * typed_inversion_all.
    split_ands; eauto 7 using addr_elt_typed, addr_elt_strict.
  * typed_inversion_all; split_ands; eauto using val_lookup_seg_typed.
  * typed_inversion_all.
    rewrite <-and_assoc; apply and_wlog_l; intros; split_ands.
    + eapply mem_alloc_valid'; eauto using TArray_valid.
      by rewrite size_of_array, Nat2Z.inj_mul, Z2Nat.id
        by auto using Z_to_nat_neq_0_nonneg.
    + typed_constructor; eauto using addr_top_array_strict, TArray_valid,
        addr_top_array_typed, mem_alloc_index_typed', lockset_valid_weaken.
    + eauto using mem_alloc_extend', TArray_valid.
  * typed_inversion_all; split_ands; eauto using
      lockset_valid_weaken, mem_free_valid', mem_free_extend'.
  * typed_inversion_all;
      repeat match goal with H : unop_typed _ _ _ |- _ => by inversion H end;
      split_ands; eauto using val_unop_typed.
  * typed_inversion_all;
      repeat match goal with H : binop_typed _ _ _ _ |- _ => by inversion H end;
      split_ands; eauto using val_binop_typed, lockset_union_valid.
  * typed_inversion_all; split_ands; eauto using mem_unlock_valid',
      expr_typed_weaken, mem_unlock_extend.
  * typed_inversion_all; split_ands; eauto using mem_unlock_valid',
      expr_typed_weaken, mem_unlock_extend.
  * typed_inversion_all; split_ands; eauto using mem_unlock_valid',
      expr_typed_weaken, mem_unlock_extend.
  * typed_inversion_all;
      repeat match goal with H : cast_typed _ _ _ |- _ => by inversion H end;
      split_ands; eauto using val_cast_typed.
Qed.
Lemma ehstep_extend Γ Γf m1 m2 ρ τs e1 e2 τlr :
  ✓ Γ → Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → ✓{Γ} m1 → (Γ,Γf,'{m1},τs) ⊢ e1 : τlr →
  '{m1} ⊢* ρ :* τs → '{m1} ⊆{⇒} '{m2}.
Proof. intros. eapply ehstep_preservation; eauto. Qed.
Lemma cstep_preservation Γ Γf δ S1 S2 f :
  ✓ Γ → Γ\ δ ⊢ₛ S1 ⇒ S2 → (Γ,Γf) ⊢ S1 : f → (Γ,'{SMem S1}) ⊢ δ : Γf →
  (Γ,Γf) ⊢ S2 : f ∧ '{SMem S1} ⊆{⇒} '{SMem S2}.
Proof.
  intros ? p. case p; clear p.
  * intros m k (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k Ee e (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (esctx_item_subst_typed_rev Γ Γf ('{m})
      (get_stack_types k) Ee e) as (σ&?&?); eauto.
    exists (Expr_type σ); simpl; split_ands; repeat typed_constructor; eauto.
  * intros m1 m2 k E e1 e2 ? (τf&HS&?&?) ?; typed_inversion HS.
    edestruct (ectx_subst_typed_rev Γ Γf ('{m1})
      (get_stack_types k) E e1) as (τrl&?&?); eauto.
    destruct (ehstep_preservation Γ Γf m1 m2 (get_stack k) (get_stack_types k)
      e1 e2 τrl) as (?&?&?); eauto using ctx_typed_stack_typed.
    split; [|eauto using funenv_typed_weaken].
    eexists; simpl; split_ands; eauto using ctx_typed_weaken,
      ectx_subst_typed, ectx_typed_weaken.
  * intros m k f' E Ωs vs ? (τf&HS&?&?) ?; typed_inversion HS.
    edestruct (ectx_subst_typed_rev Γ Γf ('{m})
      (get_stack_types k) E (call f' @ #{Ωs}* vs)) as (τrl&Hcall&?); eauto.
    typed_inversion Hcall.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    eexists (Fun_type f'); simpl; split_ands; eauto using mem_unlock_valid'.
    + typed_constructor; eauto.
      eapply (EVals_typed_inv Γ Γf _ (get_stack_types k));
        eauto using funenv_typed_funtypes_valid, funtypes_valid_args_valid,
        Forall2_impl, expr_typed_weaken, mem_unlock_extend.
    + repeat typed_constructor;
        eauto using ectx_typed_weaken, ctx_typed_weaken, mem_unlock_extend.
  * intros m k E e ?? (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (ectx_subst_typed_rev Γ Γf ('{m})
      (get_stack_types k) E e) as (τrl&?&?); eauto.
  * intros m k e Ω v (τf&HS&?&?) ?; typed_inversion HS.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    typed_inversion_all.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, mem_unlock_extend,
      mem_unlock_valid', expr_typed_weaken.
  * intros m k e Ω v (τf&HS&?&?) ?; typed_inversion HS.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    typed_inversion_all.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, mem_unlock_extend, val_typed_weaken,
      mem_unlock_valid', expr_typed_weaken.
  * intros m k e Ω v s ?  (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_extend, mem_unlock_valid'.
  * intros m k e Ω v s ?  (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_extend, mem_unlock_valid'.
  * intros m k e Ω v s ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_extend, mem_unlock_valid.
  * intros m k e Ω v s1 s2 ? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_extend, mem_unlock_valid'.
  * intros m k e Ω v s1 s2 ? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_extend, mem_unlock_valid'.
  * intros m k e Ω v s1 s2 ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_unlock_extend].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_extend, mem_unlock_valid.
  * intros m k s1 s2 (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; eauto; repeat typed_constructor; eauto.
  * intros m k s1 s2 (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k s1 s2 (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k e s (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k e s1 s2 (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k e s1 s2 (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
    by rewrite andb_false_r.
  * intros m k f' s os vs ??? (τf&HS&?&?) ?; typed_inversion_all.
    edestruct (funenv_lookup Γ ('{m}) Γf δ f')
      as (s'&mτ&?&?&?&?&?&?&?); eauto.
    erewrite fmap_type_of by eauto; simplify_equality.
    edestruct (mem_alloc_val_list_valid Γ m) as (?&?&?); eauto.
    split; [|eauto using funenv_typed_weaken].
    eexists; simpl; split_ands;
      repeat typed_constructor; eauto using ctx_typed_weaken.
    erewrite Fun_type_stack_types, (right_id_L [] (++)) by eauto.
    rewrite snd_zip by (erewrite <-Forall2_length by eauto; lia).
    eauto using stmt_typed_weaken.
  * intros m k g oσs s (τf&HS&?&?) ?. typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_foldr_free_extend].
    case_match; simplify_equality; try done.
    eexists; simpl; split_ands; repeat typed_constructor; eauto using
      ctx_typed_weaken, mem_foldr_free_extend, mem_foldr_free_valid.
  * intros m k g oσs v s (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_foldr_free_extend].
    case_match; simplify_equality; try done.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, mem_foldr_free_extend,
      mem_foldr_free_valid, val_typed_weaken.
  * intros m k g E v (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ectx_subst_typed, lockset_empty_valid.
  * intros m k Es v s (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    edestruct (sctx_item_typed_Some_l Γ Γf ('{m})
      (get_stack_types k) Es) as [??]; eauto; simplify_equality'.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using sctx_item_subst_typed.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k Es l s ? (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (sctx_item_subst_typed_rev Γ Γf ('{m})
      (get_stack_types k) Es s) as (mτ&?&?); eauto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k E l s ? (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using sctx_item_subst_typed.
  * intros m k d o τ s ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_alloc_extend'].
    eexists; simpl; split_ands; eauto 6 using
      mem_alloc_valid', stmt_typed_weaken, mem_alloc_extend',
      direction_typed_weaken, ctx_typed_weaken, mem_alloc_index_typed'.
  * intros m k d o τ s ? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, mem_free_extend'].
    eexists; simpl; split_ands; repeat typed_constructor; eauto using
      ctx_typed_weaken, direction_typed_weaken, mem_free_extend',
      mem_free_valid', index_typed_valid, index_typed_representable.
    eapply stmt_typed_weaken; eauto using mem_free_extend'.
Qed.
Lemma csteps_preservation Γ Γf δ S1 S2 f :
  ✓ Γ → Γ\ δ ⊢ₛ S1 ⇒* S2 → (Γ,Γf) ⊢ S1 : f → (Γ,'{SMem S1}) ⊢ δ : Γf →
  (Γ,Γf) ⊢ S2 : f ∧ '{SMem S1} ⊆{⇒} '{SMem S2}.
Proof.
  induction 2 as [|S1 S2 S3 ?? IH]; intros; [done|].
  destruct (cstep_preservation Γ Γf δ S1 S2 f) as (?&?); auto.
  destruct IH as (?&?); split_ands; eauto using funenv_typed_weaken.
  etransitivity; eauto.
Qed.
Lemma csteps_extend Γ Γf δ S1 S2 f :
  ✓ Γ → Γ\ δ ⊢ₛ S1 ⇒* S2 → (Γ,Γf) ⊢ S1 : f → (Γ,'{SMem S1}) ⊢ δ : Γf →
  '{SMem S1} ⊆{⇒} '{SMem S2}.
Proof. intros. eapply csteps_preservation; eauto. Qed.

Ltac ctx_inversion Hk :=
  typed_inversion Hk;
  repeat match goal with
  | H : path_typed (V:=ctx_item _) _ _ _ _ |- _ => typed_inversion H
  | H : path_typed (V:=sctx_item _) _ _ _ _ |- _ => typed_inversion H
  | H : path_typed (V:=esctx_item _) _ _ _ _ |- _ => typed_inversion H
  end.
Lemma cstep_progress Γ Γf δ S f :
  ✓ Γ → (Γ,Γf) ⊢ S : f → (Γ,'{SMem S}) ⊢ δ : Γf →
  (**i 1.) *) red (cstep Γ δ) S ∨
  (**i 2.) *) (∃ v, is_final_state v S) ∨
  (**i 3.) *) is_undef_state S ∨
  (**i 4.) *) (∃ l s, SFoc S = Stmt (↷ l) s ∧ l ∉ labels s ∪ labels (SCtx S)).
Proof.
  destruct S as [k φ m]. intros ? (τf&Hφ&Hk&?) ?; simpl in *.
  destruct Hφ as [d s cmσ Hs Hd|e τ|f' vs σs σ|f' σs σ v| |]; simpl.
  * destruct Hd as [cmτ|mτ|c v τ|l cmτ]; simpl.
    + destruct Hs; left; solve_cred.
    + ctx_inversion Hk; left; solve_cred.
    + ctx_inversion Hk; left; solve_cred.
    + destruct (decide (l ∈ labels s)).
      { destruct Hs; simplify_equality'; decompose_elem_of; left; solve_cred. }
      ctx_inversion Hk; try (left; solve_cred).
      do 3 right; exists l s. erewrite Fun_type_labels by eauto. solve_elem_of.
  * destruct (is_nf_or_redex e) as [Hnf|(E&e'&?&->)].
    { destruct Hnf as [Ω v|]; typed_inversion_all.
      ctx_inversion Hk; left; try solve_cred;
        destruct (val_true_false_dec ('{m}) v)
        as [[[??]|[??]]|[??]]; solve_cred. }
    destruct (ehexec Γ (get_stack k) e' m) as [[e'' m']|] eqn:He''.
    { apply ehexec_sound in He''. left; solve_cred. }
    destruct (maybe_ECall_redex e') as [[[f' Ωs] vs]|] eqn:Hf.
    { apply maybe_ECall_redex_Some in Hf; destruct Hf as [-> ?].
      left; solve_cred. }
    assert (¬Γ \ get_stack k ⊢ₕ safe e', m).
    { rewrite eq_None_not_Some in Hf; contradict Hf; destruct Hf.
      * eexists; apply maybe_ECall_redex_Some; eauto.
      * edestruct ehexec_weak_complete; eauto. }
    left; solve_cred.
  * destruct (funenv_lookup Γ ('{m}) Γf δ f' σs σ) as (s&cmτ&?&_); auto.
    left; solve_cred.
  * ctx_inversion Hk.
    { right; left; exists v. constructor. }
    left; solve_cred.
  * do 2 right; left; constructor.
  * do 2 right; left; constructor.
Qed.
Lemma csteps_initial_progress Γ Γf δ m f vs S σs σ :
  ✓ Γ → ✓{Γ} m → (Γ,'{m}) ⊢ δ : Γf →
  Γf !! f = Some (σs,σ) → (Γ,'{m}) ⊢* vs :* σs →
  Γ\ δ ⊢ₛ initial_state m f vs ⇒* S →
  (**i 1.) *) red (cstep Γ δ) S ∨
  (**i 2.) *) (∃ v, is_final_state v S) ∨
  (**i 3.) *) is_undef_state S.
Proof.
  intros. assert ((Γ,Γf) ⊢ S : f ∧ (Γ,'{SMem S}) ⊢ δ : Γf) as [??].
  { destruct (csteps_preservation Γ Γf δ (initial_state m f vs) S f);
      eauto using initial_state_typed, funenv_typed_weaken. }
  destruct (cstep_progress Γ Γf δ S f) as [?|[[v ?]|[?|(l&s&?&[])]]]; eauto.
  destruct S as [k φ m2]; simplify_equality'.
  eauto using csteps_initial_gotos, funenv_lookup_gotos.
Qed.
End type_preservation.
