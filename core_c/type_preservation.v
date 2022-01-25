(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system smallstep.
Require Import executable_sound.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.

Section type_preservation.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types k : ctx K.
Implicit Types o : index.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types v : val K.

Hint Extern 0 (_ ⊢ _ : _) => typed_constructor: core.
Hint Extern 0 (_ ⊢ _ : _ ↣ _) => typed_constructor: core.

Lemma initial_state_typed Γ δ m f vs σs σ :
  ✓{Γ} m → ✓{Γ,'{m}} δ → Γ !! f = Some (σs,σ) →
  (Γ,'{m}) ⊢* vs :* σs → Γ ⊢ initial_state m f vs : Fun_type f.
Proof. eexists (Fun_type f); simpl; eauto. Qed.
Lemma ehstep_preservation Γ m1 m2 ρ e1 e2 τlr :
  ✓ Γ → Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  ✓{Γ} m1 → (Γ,'{m1},ρ.*2) ⊢ e1 : τlr → ✓{'{m1}}* ρ →
  (**i 1.) *) ✓{Γ} m2 ∧
  (**i 2.) *) (Γ,'{m2},ρ.*2) ⊢ e2 : τlr ∧
  (**i 3.) *) '{m1} ⇒ₘ '{m2}.
Proof.
  intros ? [] ???.
  * typed_inversion_all; list_simplifier; split_and ?; auto.
    typed_constructor; eauto 8 using addr_top_typed,
      cmap_index_typed_valid, lockset_empty_valid.
  * typed_inversion_all; auto.
  * typed_inversion_all; auto 10.
  * typed_inversion_all.
    rewrite <-Coq.Init.Logic.and_assoc; apply and_wlog_l; intros; split_and ?.
    + eapply mem_lock_valid'; eauto using mem_insert_writable,
        mem_insert_valid', assign_preservation_1.
    + typed_constructor; eauto 6 using lockset_union_valid,
        lockset_valid_weaken, lock_singleton_valid, val_typed_weaken,
        assign_preservation_2, mem_writable_strict.
    + intros. erewrite mem_lock_memenv_of by eauto using mem_insert_writable,
        mem_insert_valid', assign_preservation_1.
      eauto using mem_insert_forward, assign_preservation_1.
  * typed_inversion_all.
    rewrite <-Coq.Init.Logic.and_assoc; apply and_wlog_l; intros; split_and ?.
    + eauto using mem_force_valid'.
    + typed_constructor; eauto using lockset_valid_weaken,
        val_typed_weaken,  mem_lookup_typed.
    + eauto using mem_lookup_typed, mem_force_forward.
  * typed_inversion_all.
    split_and ?; eauto 7 using addr_elt_typed.
  * typed_inversion_all; split_and ?; eauto using val_lookup_seg_typed.
  * typed_inversion_all; split_and ?; eauto 9 using type_valid_ptr_type_valid.
  * typed_inversion_all.
    rewrite <-Coq.Init.Logic.and_assoc; apply and_wlog_l; intros; split_and ?.
    + eapply mem_alloc_new_valid';
        eauto using TArray_valid, perm_full_valid, perm_full_mapped.
    + typed_constructor; eauto 10 using TArray_valid,
        addr_top_array_typed, mem_alloc_new_index_typed', lockset_valid_weaken.
    + eauto using mem_alloc_new_forward', TArray_valid.
  * typed_inversion_all; split_and ?; eauto using
      lockset_valid_weaken, mem_free_valid', mem_free_forward'.
  * typed_inversion_all;
      repeat match goal with H : unop_typed _ _ _ |- _ => by inversion H end;
      split_and ?; eauto using val_unop_typed.
  * typed_inversion_all;
      repeat match goal with H : binop_typed _ _ _ _ |- _ => by inversion H end;
      split_and ?; eauto using val_binop_typed, lockset_union_valid.
  * typed_inversion_all; split_and ?; eauto using mem_unlock_valid',
      expr_typed_weaken, mem_unlock_forward.
  * typed_inversion_all; split_and ?; eauto using mem_unlock_valid',
      expr_typed_weaken, mem_unlock_forward.
  * typed_inversion_all; split_and ?; eauto using mem_unlock_valid',
      expr_typed_weaken, mem_unlock_forward.
  * typed_inversion_all;
      repeat match goal with H : cast_typed _ _ _ |- _ => by inversion H end;
      split_and ?; eauto using val_cast_typed.
  * typed_inversion_all; split_and ?;
      eauto using lockset_union_valid, val_alter_const_typed.
Qed.
Lemma ehstep_forward Γ m1 m2 ρ e1 e2 τlr :
  ✓ Γ → Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → ✓{Γ} m1 → (Γ,'{m1},ρ.*2) ⊢ e1 : τlr →
  ✓{'{m1}}* ρ → '{m1} ⇒ₘ '{m2}.
Proof. intros. eapply ehstep_preservation; eauto. Qed.
Lemma cstep_preservation Γ δ S1 S2 σf :
  ✓ Γ → Γ\ δ ⊢ₛ S1 ⇒ S2 → Γ ⊢ S1 : σf → ✓{Γ,'{SMem S1}} δ →
  Γ ⊢ S2 : σf ∧ '{SMem S1} ⇒ₘ '{SMem S2}.
Proof.
  intros ? p. case p; clear p.
  * intros m k (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k n (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; split; auto.
  * intros m k Ee e (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (esctx_item_subst_typed_rev Γ '{m}
      ((locals k).*2) Ee e) as (σ&?&?&?); eauto.
    exists (Expr_type σ); simpl; split_and ?; repeat typed_constructor; eauto.
  * intros m1 m2 k E e1 e2 ? (τf&HS&?&?) ?; typed_inversion HS.
    edestruct (ectx_subst_typed_rev Γ '{m1}
      ((locals k).*2) E e1) as (τrl&?&?); eauto.
    destruct (ehstep_preservation Γ m1 m2 (locals k)
      e1 e2 τrl) as (?&?&?); eauto using ctx_typed_locals_valid.
    split; auto. eexists; simpl; split_and ?; eauto using ctx_typed_weaken,
      ectx_subst_typed, ectx_typed_weaken.
  * simpl; intros m k Ω f' τs τ E Ωs vs ? (τf&HS&?&?) ?; typed_inversion HS.
    edestruct (ectx_subst_typed_rev Γ '{m} ((locals k).*2) E
      (call %{Ω} (FunPtr f' τs τ) @ #{Ωs}* vs)) as (τrl&Hcall&?); eauto.
    typed_inversion_all. split; [|eauto using mem_unlock_forward].
    eexists (Fun_type f'); simpl; split_and ?; eauto using mem_unlock_valid'.
    + typed_constructor; eauto.
      eapply (EVals_typed_inv Γ _ ((locals k).*2)); eauto using
        env_valid_args_valid, exprs_typed_weaken, mem_unlock_forward.
    + repeat typed_constructor;
        eauto using ectx_typed_weaken, ctx_typed_weaken, mem_unlock_forward.
  * intros m k E e ?? (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (ectx_subst_typed_rev Γ '{m}
      ((locals k).*2) E e) as (τrl&?&?); eauto.
  * intros m k e Ω v (τf&HS&?&?) ?; typed_inversion HS.
    typed_inversion_all. split; eauto using mem_unlock_forward.
    eexists; simpl; split_and ?; repeat typed_constructor;
      eauto using ctx_typed_weaken, mem_unlock_forward,
      mem_unlock_valid', expr_typed_weaken.
  * intros m k e Ω v (τf&HS&?&?) ?; typed_inversion HS.
    typed_inversion_all. split; eauto using mem_unlock_forward.
    eexists; simpl; split_and ?; repeat typed_constructor;
      eauto using ctx_typed_weaken, mem_unlock_forward, val_typed_weaken,
      mem_unlock_valid', expr_typed_weaken.
  * intros m k e Ω v s1 s2 ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; eauto using mem_unlock_forward.
    eexists; simpl; split_and ?; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_forward, mem_unlock_valid'.
  * intros m k e Ω v s1 s2 ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; eauto using mem_unlock_forward.
    eexists; simpl; split_and ?; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_forward, mem_unlock_valid'.
  * intros m k e Ω v s1 s2 ? (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k e Ω v s1 s2 ? (τf&HS&?&?) ?; typed_inversion_all.
    split; eauto using mem_unlock_forward.
    eexists; simpl; split_and ?; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_forward, mem_unlock_valid'.
  * intros m k e Ω v τi x s ? (τf&HS&?&?) ?; typed_inversion_all.
    split; eauto using mem_unlock_forward.
    eexists; simpl; split_and ?; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_forward, mem_unlock_valid'.
  * intros m k e Ω τi x s ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; eauto using mem_unlock_forward.
    eexists; simpl; split_and ?; repeat typed_constructor;
      eauto using ctx_typed_weaken, expr_typed_weaken,
      stmt_typed_weaken, mem_unlock_forward, mem_unlock_valid'.
  * intros m k e Ω vb s ? (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s1 s2 (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s1 s2 (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s1 s2 (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k e s1 s2 (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k e s1 s2 (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eexists; simpl; split_and ?; repeat typed_constructor; eauto.
    by rewrite andb_false_r.
  * intros m k e s (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k f' s os vs ??? (τf&HS&?&?) ?; typed_inversion_all.
    edestruct (funenv_lookup Γ '{m} δ f') as (s'&cmτ&?&?&?&?&?&?); eauto.
    erewrite fmap_type_of by eauto; simplify_equality.
    edestruct (mem_alloc_list_valid Γ m) as (?&?&?); eauto.
    split; auto. eexists; simpl; split_and ?;
      repeat typed_constructor; eauto using ctx_typed_weaken.
    rewrite snd_zip by (erewrite <-Forall2_length by eauto; lia).
    eauto using stmt_typed_weaken.
  * intros m k f oσs s (τf&HS&?&?) ?.
    typed_inversion_all; match goal with
    | H : rettype_match _ _ |- _ => apply rettype_match_false_inv in H; subst
    end; eauto 10 using mem_foldr_free_forward, ctx_typed_weaken,
      mem_foldr_free_forward, mem_foldr_free_valid.
  * intros m k f oσs v s (τf&HS&?&?) ?; typed_inversion_all.
    typed_inversion_all; match goal with
    | H : rettype_match _ _ |- _ => apply rettype_match_Some_inv in H; subst
    end; eauto 10 using mem_foldr_free_forward, ctx_typed_weaken,
      mem_foldr_free_forward, mem_foldr_free_valid, val_typed_weaken.
  * intros m k f E v (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eauto 10 using ectx_subst_typed, lockset_empty_valid.
  * intros m k l (τf&HS&?&?) ?; typed_inversion_all; auto.
  * intros m k s (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k s n (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k mx (τf&HS&?&?) ?; typed_inversion_all; eauto 10.
  * intros m k Es l s ? (τf&HS&?&?) ?; typed_inversion HS; split; auto.
    edestruct (sctx_item_subst_typed_rev Γ '{m}
      ((locals k).*2) Es s) as (mτ&?&?); eauto 10.
  * intros m k Es mx s ?? (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    edestruct (sctx_item_subst_typed_rev Γ ('{m})
      ((locals k).*2) Es s) as (mτ&?&?); eauto 10.
  * intros m k Es v s (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    edestruct (sctx_item_typed_Some_l Γ '{m}
      ((locals k).*2) Es) as [??]; eauto; simplify_equality'.
    eauto 10 using sctx_item_subst_typed.
  * intros m k Es l s ? (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eauto 10 using sctx_item_subst_typed.
  * intros m k Es n s ? (τf&HS&?&?) ?; typed_inversion_all; split; auto.
    eauto 10 using sctx_item_subst_typed.
  * intros m k d o τ s ?? (τf&HS&?&?) ?; typed_inversion_all.
    split; eauto using mem_alloc_new_forward'.
    eexists; simpl; split_and ?; eauto 8 using
      mem_alloc_new_valid', stmt_typed_weaken, mem_alloc_new_forward',
      direction_typed_weaken, ctx_typed_weaken, mem_alloc_new_index_typed',
      perm_full_valid, perm_full_mapped.
  * intros m k d o τ s ? (τf&HS&?&?) ?; typed_inversion_all.
    split; eauto using mem_free_forward'.
    eexists; simpl; split_and ?; repeat typed_constructor; eauto using
      ctx_typed_weaken, direction_typed_weaken, mem_free_forward',
      mem_free_valid', cmap_index_typed_valid.
    eapply stmt_typed_weaken; eauto using mem_free_forward'.
Qed.
Lemma csteps_preservation Γ δ S1 S2 σf :
  ✓ Γ → Γ\ δ ⊢ₛ S1 ⇒* S2 → Γ ⊢ S1 : σf → ✓{Γ,'{SMem S1}} δ →
  Γ ⊢ S2 : σf ∧ '{SMem S1} ⇒ₘ '{SMem S2}.
Proof.
  induction 2 as [|S1 S2 S3 ?? IH]; intros; [done|].
  destruct (cstep_preservation Γ δ S1 S2 σf) as (?&?); auto.
  destruct IH as (?&?); eauto using funenv_valid_weaken.
Qed.
Lemma csteps_forward Γ δ S1 S2 σf :
  ✓ Γ → Γ\ δ ⊢ₛ S1 ⇒* S2 → Γ ⊢ S1 : σf → ✓{Γ,'{SMem S1}} δ →
  '{SMem S1} ⇒ₘ '{SMem S2}.
Proof. intros. eapply csteps_preservation; eauto. Qed.

Ltac ctx_inversion Hk :=
  typed_inversion Hk;
  repeat match goal with
  | H : path_typed (V:=ctx_item _) _ _ _ _ |- _ => typed_inversion H
  | H : path_typed (V:=sctx_item _) _ _ _ _ |- _ => typed_inversion H
  | H : path_typed (V:=esctx_item _) _ _ _ _ |- _ => typed_inversion H
  end.
Lemma cstep_progress Γ δ S f :
  ✓ Γ → Γ ⊢ S : Fun_type f → ✓{Γ,'{SMem S}} δ →
  (**i 1.) *) red (cstep Γ δ) S ∨
  (**i 2.) *) (∃ v, is_final_state f v S) ∨
  (**i 3.) *) is_undef_state S ∨
  (**i 4.) *) match SFoc S with
              | Stmt (↷ l) s => l ∉ labels s ∪ labels (SCtx S)
              | Stmt (↑ n) s => ¬n < ctx_catches (SCtx S)
              | Stmt (↓ mx) s => mx ∉ cases s
              | _ => False
              end.
Proof.
  destruct S as [k φ m]. intros ? (τf&Hφ&Hk&?) ?; simpl in *.
  destruct Hφ as [d s cmσ Hs Hd|e τ|f' vs σs σ|f' σs σ v| |]; simpl.
  * destruct Hd as [cmτ|mτ|c v τ|l cmτ|n cmτ|mx]; simpl.
    + destruct Hs; left; eexists; do_cstep.
    + ctx_inversion Hk; left; eexists; do_cstep.
    + ctx_inversion Hk; left; eexists; do_cstep.
    + destruct (decide (l ∈ labels s)).
      { destruct Hs; simplify_equality';
          decompose_elem_of; left; eexists; do_cstep. }
      ctx_inversion Hk; try (left; eexists; do_cstep); set_solver.
    + destruct (decide (n < ctx_catches k)); [|by auto].
      left. destruct n; ctx_inversion Hk; try lia || eexists; do_cstep.
    + destruct (decide (mx ∈ cases s)); [|by auto].
      typed_inversion Hs; decompose_elem_of; left; eexists; do_cstep.
  * destruct (is_nf_or_redex e) as [Hnf|(E&e'&?&->)].
    { destruct Hnf as [Ω [v|]]; typed_inversion_all.
      ctx_inversion Hk; left; try (eexists; do_cstep).
      + repeat match goal with
        | H : _ ⊢ _ : baseT _ |- _ => typed_inversion H
        | H : _ ⊢ ?vb : _ |- _ =>
           clear H; destruct (decide (base_val_is_0 vb)),
             (decide (base_val_branchable m vb))
        end; eexists; do_cstep.
      + repeat match goal with
        | H : _ ⊢ _ : baseT _ |- _ => typed_inversion H
        | H : _ ⊢ _ : (intT _)%BT |- _ => typed_inversion H
        | H : int_typed ?x _ |- _ =>
           clear H;
           destruct (decide (Some x ∈ cases s)), (decide (None ∈ cases s))
        end; eexists; do_cstep. }
    destruct (ehstep_dec Γ (locals k) e' m) as [(e''&m''&?)|He''].
    { left; eexists; do_cstep. }
    destruct (maybe_ECall_redex e') as [[[[[[Ω f'] σs] σ] Ωs] vs]|] eqn:Hf.
    { apply maybe_ECall_redex_Some in Hf; destruct Hf as [-> ?].
      left; eexists; do_cstep. }
    assert (¬Γ \ locals k ⊢ₕ safe e', m).
    { rewrite eq_None_not_Some in Hf;
        contradict Hf; destruct Hf; [|naive_solver].
      eexists; apply maybe_ECall_redex_Some; eauto. }
    left; eexists; do_cstep.
  * destruct (funenv_lookup Γ '{m} δ f' σs σ) as (s&cmτ&?&_); auto.
    left; eexists; do_cstep.
  * ctx_inversion Hk; [|left; eexists; do_cstep].
    right; left; by exists v.
  * do 2 right; left. by apply (bool_decide_unpack _).
  * do 2 right; left. by apply (bool_decide_unpack _).
Qed.
Lemma csteps_initial_progress Γ δ m f vs S σs σ :
  ✓ Γ → ✓{Γ} m → ✓{Γ,'{m}} δ →
  Γ !! f = Some (σs,σ) → (Γ,'{m}) ⊢* vs :* σs →
  Γ\ δ ⊢ₛ initial_state m f vs ⇒* S →
  (**i 1.) *) red (cstep Γ δ) S ∨
  (**i 2.) *) (∃ v, is_final_state f v S) ∨
  (**i 3.) *) is_undef_state S.
Proof.
  intros. assert (Γ ⊢ S : Fun_type f ∧ ✓{Γ,'{SMem S}} δ) as [??].
  { destruct (csteps_preservation Γ δ (initial_state m f vs) S (Fun_type f));
      eauto using initial_state_typed, funenv_valid_weaken. }
  destruct (cstep_progress Γ δ S f) as [?|[[v ?]|[?|?]]]; eauto.
  destruct S as [k [[]| | | |] m2]; simplify_equality';
    try naive_solver eauto using csteps_initial_gotos, funenv_lookup_gotos,
    csteps_initial_throws, funenv_lookup_throws, csteps_initial_switch.
Qed.
End type_preservation.
