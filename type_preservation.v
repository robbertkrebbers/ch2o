(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system smallstep.
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

Lemma assign_preservation_1 Γ m ass a v v' va' τ1 τ2 σ :
  ✓ Γ → ✓{Γ} m → assign_typed Γ τ1 τ2 ass σ →
  (Γ,m) ⊢ a : τ1 → (Γ,m) ⊢ v : τ2 →
  assign_sem Γ m a v ass v' va' → (Γ,m) ⊢ v' : σ.
Proof.
  destruct 3; inversion 3; simplify_type_equality';
    eauto using val_cast_typed, val_binop_typed, mem_lookup_typed.
Qed.
Lemma assign_preservation_2 Γ m ass a v v' va' τ1 τ2 σ :
  ✓ Γ → ✓{Γ} m → assign_typed Γ τ1 τ2 ass σ → (Γ,m) ⊢ a : τ1 → (Γ,m) ⊢ v : τ2 →
  assign_sem Γ m a v ass v' va' → (Γ,m) ⊢ va' : τ1.
Proof.
  destruct 3; inversion 3; simplify_type_equality';
    eauto using val_cast_typed, val_binop_typed, mem_lookup_typed.
Qed.
Lemma ehstep_preservation Γ Γf m1 m2 ρ τs e1 e2 τlr :
  ✓ Γ → Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  ✓{Γ} m1 → (Γ,Γf,m1,τs) ⊢ e1 : τlr → m1 ⊢* ρ :* τs →
  ✓{Γ} m2 ∧ (Γ,Γf,m2,τs) ⊢ e2 : τlr ∧ ∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ.
Proof.
  intros ? [] ???.
  * typed_inversion_all; decompose_Forall_hyps'; split_ands; auto.
    typed_constructor; eauto using addr_top_typed, addr_top_strict,
      index_typed_valid, index_typed_representable.
  * typed_inversion_all; auto.
  * typed_inversion_all; auto 7.
  * typed_inversion_all; split_ands.
    + eapply mem_lock_valid; eauto using mem_insert_writable,
        mem_insert_valid, assign_preservation_2.
    + typed_constructor.
      eapply val_typed_lock; eauto using mem_insert_writable, mem_insert_valid,
        val_typed_insert, assign_preservation_1, assign_preservation_2.
    + intros. eapply index_typed_lock; eauto using mem_insert_writable,
        mem_insert_valid, index_typed_insert, assign_preservation_2.
  * typed_inversion_all; split_ands.
    + eauto using mem_force_valid.
    + eauto using val_typed_force, mem_lookup_typed.
    + eauto using mem_lookup_typed, index_typed_force.
  * typed_inversion_all.
    split_ands; eauto 7 using addr_elt_typed, addr_elt_strict.
  * typed_inversion_all; split_ands.
    + eauto using mem_alloc_valid.
    + eauto using addr_top_typed, addr_top_strict, index_typed_alloc.
    + eauto using index_typed_alloc_free.
  * typed_inversion_all; eauto 7 using mem_free_valid, index_typed_free.
  * typed_inversion_all;
      repeat match goal with H : unop_typed _ _ _ |- _ => by inversion H end;
      eauto using val_unop_typed.
  * typed_inversion_all;
      repeat match goal with H : binop_typed _ _ _ _ |- _ => by inversion H end;
      eauto using val_binop_typed.
  * typed_inversion_all; split_ands;
       eauto using mem_unlock_valid, expr_typed_weaken, index_typed_unlock.
  * typed_inversion_all; split_ands;
       eauto using mem_unlock_valid, expr_typed_weaken, index_typed_unlock.
  * typed_inversion_all; split_ands;
      eauto using mem_unlock_valid, expr_typed_weaken, index_typed_unlock.
  * typed_inversion_all;
      repeat match goal with H : cast_typed _ _ _ |- _ => by inversion H end;
      eauto using val_cast_typed.
  * typed_inversion_all;
      split_ands; eauto using addr_field_typed, addr_field_strict.
Qed.
Lemma cstep_preservation Γ Γf δ S1 S2 :
  ✓ Γ → Γ\ δ ⊢ₛ S1 ⇒ S2 →
  ✓{Γ,Γf} S1 → (Γ,SMem S1) ⊢ δ : Γf → ✓{Γ,Γf} S2 ∧ (Γ,SMem S2) ⊢ δ : Γf.
Proof.
  intros ? p. case p; clear p.
  * intros m k (τf&HS&?&?) ?; typed_inversion_all; split; auto.
     eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k Ee e (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (esctx_item_subst_typed_rev Γ Γf m
      (get_stack_types k) Ee e) as (σ&?&?); eauto.
    exists (Expr_type σ); simpl; split_ands; repeat typed_constructor; eauto.
  * intros m1 m2 k E e1 e2 ? (τf&HS&?&?) ?; typed_inversion HS.
    edestruct (ectx_subst_typed_rev Γ Γf m1
      (get_stack_types k) E e1) as (τrl&?&?); eauto.
    destruct (ehstep_preservation Γ Γf m1 m2 (get_stack k) (get_stack_types k)
      e1 e2 τrl) as (?&?&?); eauto using ctx_typed_stack_typed.
    split; [|eauto using funenv_typed_weaken].
    eexists; simpl; split_ands; eauto using ctx_typed_weaken,
      ectx_subst_typed, ectx_typed_weaken.
  * intros m k f E Ωs vs ? (τf&HS&?&?) ?; typed_inversion HS.
    edestruct (ectx_subst_typed_rev Γ Γf m
      (get_stack_types k) E (call f @ #{Ωs}* vs)) as (τrl&Hcall&?); eauto.
    typed_inversion Hcall.
    split; [|eauto using funenv_typed_weaken, index_typed_unlock].
    eexists (Fun_type f); simpl; split_ands; eauto using mem_unlock_valid.
    + typed_constructor; eauto.
      eapply (EVals_typed_inv Γ Γf _ (get_stack_types k));
        eauto using funenv_lookup_args, Forall2_impl,
        expr_typed_weaken, index_typed_unlock.
    + repeat typed_constructor; eauto using ectx_typed_weaken,
        ctx_typed_weaken, index_typed_unlock.
  * intros m k E e ?? (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    eexists; simpl; split_ands; eauto.
  * intros m k e Ω v (τf&HS&?&?) ?; typed_inversion HS.
    split; [|eauto using funenv_typed_weaken, index_typed_unlock].
    typed_inversion_all.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, index_typed_unlock,
      mem_unlock_valid, expr_typed_weaken, index_typed_unlock.
  * intros m k e Ω v (τf&HS&?&?) ?; typed_inversion HS.
    split; [|eauto using funenv_typed_weaken, index_typed_unlock].
    typed_inversion_all.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, index_typed_unlock, val_typed_unlock,
      mem_unlock_valid, expr_typed_weaken, index_typed_unlock.
  * intros m k e Ω v s ?  (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_unlock].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, index_typed_unlock, mem_unlock_valid.
  * intros m k e Ω v s ?  (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_unlock].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, index_typed_unlock, mem_unlock_valid.
  * intros m k e Ω v s1 s2 ?  (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_unlock].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, index_typed_unlock, mem_unlock_valid.
  * intros m k e Ω v s1 s2 ? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_unlock].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, index_typed_unlock, mem_unlock_valid.
  * intros m k o τ s ? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_alloc_free].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using mem_alloc_valid, index_typed_alloc,
      stmt_typed_weaken, ctx_typed_weaken, index_typed_alloc_free.
  * intros m k s1 s2 (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; eauto; repeat typed_constructor; eauto.
  * intros m k o τ s (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_free].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, index_typed_free, mem_free_valid,
      index_typed_valid, index_typed_representable.
    eapply stmt_typed_weaken; eauto using index_typed_free.
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
  * intros m k f s os vs ??? (τf&HS&?&?) ?; typed_inversion_all.
    edestruct (funenv_lookup Γ m Γf δ f) as (s'&mτ&?&?&?&?&?); eauto.
    erewrite fmap_type_of by eauto; simplify_equality.
    edestruct (mem_alloc_val_list_valid Γ m) as (?&?&?); eauto.
    split; [|eauto using funenv_typed_weaken].
    eexists; simpl; split_ands;
      repeat typed_constructor; eauto using ctx_typed_weaken.
    + erewrite Fun_type_stack_types, (right_id_L [] (++)) by eauto.
      rewrite snd_zip by (erewrite <-Forall2_length by eauto; lia).
      eauto using stmt_typed_weaken.
    + symmetry. erewrite <-(Forall2_length _ vs) by eauto; lia.
  * intros m k oσs s (τf&HS&?&?) ?. typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_foldr_free].
    case_match; simplify_equality; try done.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, index_typed_foldr_free,
      mem_foldr_free_valid.
  * intros m k oσs v s (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_foldr_free].
    case_match; simplify_equality; try done.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, index_typed_foldr_free,
      mem_foldr_free_valid, val_typed_weaken.
  * intros m k E v (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ectx_subst_typed.
  * intros m k o τ v s (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_free].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using ctx_typed_weaken, index_typed_free, mem_free_valid,
      val_typed_free, index_typed_valid, index_typed_representable.
    eapply stmt_typed_weaken; eauto using index_typed_free.
  * intros m k Es v s (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    edestruct (sctx_item_typed_Some_l Γ Γf m
      (get_stack_types k) Es) as [??]; eauto; simplify_equality'.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using sctx_item_subst_typed.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k l o τ s ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_alloc_free].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using mem_alloc_valid, index_typed_alloc,
      stmt_typed_weaken, ctx_typed_weaken, index_typed_alloc_free.
  * intros m k l o τ s ? (τf&HS&?&?) ?; typed_inversion_all.
    split; [|eauto using funenv_typed_weaken, index_typed_free].
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using index_typed_valid, index_typed_representable,
      ctx_typed_weaken, index_typed_free, mem_free_valid.
    eapply stmt_typed_weaken; eauto using index_typed_free.
  * intros m k Es l s ? (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (sctx_item_subst_typed_rev Γ Γf m
      (get_stack_types k) Es s) as (mτ&?&?); eauto.
    eexists; simpl; split_ands; repeat typed_constructor; eauto.
  * intros m k E l s ? (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_ands; repeat typed_constructor;
      eauto using sctx_item_subst_typed.
Qed.
End type_preservation.
