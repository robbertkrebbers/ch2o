(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** The lemma [ax_expr_compose] is used to prove the structural Hoare rules for
expressions. It is proven by chasing all (interleaved) reduction paths for the
compound expression. This is done step-wise by distinguishing the following
cases:

- All subexpressions are values.
- Some subexpression contains a redex that is not a function call.
- Some subexpression contains a redex that is a function call. In this case we
  use the lemma [ax_call_compose]. *)
Require Import axiomatic axiomatic_graph.

Section axiomatic_expressions_help.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types δ : funenv K.
Implicit Types m : mem K.
Implicit Types e : expr K.
Implicit Types s : stmt K.

Hint Extern 1 (_ ## _) => solve_mem_disjoint: core.
Hint Extern 1 (## _) => solve_mem_disjoint: core.
Hint Extern 1 (sep_valid _) => solve_mem_disjoint: core.
Hint Extern 1 (_ ⊆ _) => etransitivity; [eassumption|]: core.
Hint Extern 1 (_ ≤ _) => lia: core.
Hint Immediate cmap_valid_memenv_valid: core.
Hint Resolve cmap_empty_valid cmap_erased_empty mem_locks_empty: core.
Hint Resolve cmap_union_valid_2 cmap_erase_valid: core.

Lemma ax_expr_post_expr_nf Γ Q Δ δ ρ n m e τlr :
  ax_expr_post' Q τlr Γ Δ δ ρ n (Expr e) m → is_nf e.
Proof. by inversion 1. Qed.
Lemma ax_expr_lrval Γ δ A (P : lrval K → assert K) Δ ρ n ν Ω m τlr :
  ✓{Γ,Δ} m → ax_expr_invariant A Γ Δ δ ρ (S n) m →
  ax_graph (ax_expr_cond ρ A)
    (ax_expr_post P τlr) Γ δ Δ ρ (S n) [] (Expr (%#{Ω} ν)%E) m →
  assert_holds (P ν) Γ Δ δ ρ (S n) (cmap_erase m)
  ∧ mem_locks m = Ω ∧ (Γ,Δ) ⊢ ν : τlr.
Proof.
  intros ? (mA&?&?&?&?&?);
    inversion 1 as [|??? [??????]|???? Hred]; subst; try by auto.
  destruct (Hred Δ n (m ∪ mA) (InExpr ∅ mA)); auto.
  * constructor; eauto using assert_weaken. by rewrite sep_right_id by auto.
  * inv_rcstep.
Qed.
Lemma ax_call_compose Γ δ A P Q (E : ectx K) E' ρ Δ n φ k m1 m2 :
  ✓ Γ → locks E' ⊆ locks E ∪ mem_locks m2 →
  ## [m1; m2] → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 →
  ax_graph (ax_expr_cond ρ A) P Γ δ Δ ρ n (k ++ [CFun E]) φ m1 →
  (∀ Δ' n' m1' e',
    ## [m1'; m2] → ✓{Γ,Δ'} m1' → ✓{Γ,Δ'} m2 →
    locks (subst E e') ⊆ mem_locks m1' →
    ax_expr_invariant A Γ Δ' δ ρ (S n') (m1' ∪ m2) →
    ax_graph (ax_expr_cond ρ A) P Γ δ Δ' ρ n' [] (Expr (subst E e')) m1' →
    Δ ⇒ₘ Δ' → n' ≤ n →
    ax_graph (ax_expr_cond ρ A) Q Γ δ Δ' ρ n' []
      (Expr (subst E' e')) (m1' ∪ m2)) →
  ax_graph (ax_expr_cond ρ A) Q Γ δ Δ ρ n (k ++ [CFun E']) φ (m1 ∪ m2).
Proof.
  intros ? HE; revert Δ k φ m1.
  induction n as [[|n] IH] using lt_wf_ind;
    intros Δ k φ m1 ??? Hax Hnext; [apply ax_O |].
  inversion Hax as [| |???? Hred Hstep];
    clear Hax; subst; try discriminate_list_equality.
  apply ax_further.
  { intros Δ' n' m' a ??? Hframe; inversion_clear Hframe;
      subst; try discriminate_list_equality; simplify_mem_disjoint_hyps.
    destruct (Hred Δ' n' (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))) as [S' p]; auto.
    { rewrite <-sep_associative by auto; constructor; auto.
      intro; discriminate_list_equality. }
    apply (rcstep_call_inv _ _ _ E E' _ _ _ _ _ p); intros; subst; eauto. }
  intros Δ' n' ?? S' ??? Hframe p;
    inversion_clear Hframe as [mA mf|mf]; subst;
    try discriminate_list_equality; simplify_mem_disjoint_hyps.
  pattern S'; apply (rcstep_call_inv _ _ _ _ E _ _ _ _ _ p).
  * intros k' φ' m' p' ?.
    feed inversion (Hstep Δ' n' (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))
      (State (k' ++ [CFun E]) φ' m')) as [Δ'' ?? ? m1' ?? Hunframe];
      subst; trivial.
    { rewrite <-sep_associative by auto. constructor; auto.
      intro; discriminate_list_equality. }
    inversion_clear Hunframe as [|mA| |]; subst;
      try discriminate_list_equality; simplify_mem_disjoint_hyps.
    apply mk_ax_next with Δ'' (m1' ∪ m2), IH;
      eauto 6 using focus_locks_valid_union.
    rewrite sep_associative by auto. constructor; auto.
    intro; discriminate_list_equality.
  * intros f v -> -> p' ?.
    feed inversion (Hstep Δ' n' (m1 ∪ m2 ∪ mf) (InFun (m2 ∪ mf))
      (State [] (Expr (subst E (# v)%E))
      (m1 ∪ m2 ∪ mf))) as [Δ'' ??? m1' ?? Hunframe _ Hlocks];
      subst; trivial.
    { rewrite <-sep_associative by auto. constructor; auto. }
    inversion_clear Hunframe as [|mA ? Hm| |];
      simplify_equality'; simplify_mem_disjoint_hyps.
    assert (m1 = m1' ∪ mA); [|subst; simplify_mem_disjoint_hyps].
    { apply sep_cancel_r with (m2 ∪ mf); auto.
      rewrite <-(sep_associative m1'), (sep_commutative mA) by auto.
      by rewrite sep_associative, (sep_associative m1') by auto. }
    apply mk_ax_next with Δ'' (m1' ∪ m2); auto.
    + apply ax_unframe_fun_to_expr with mA; auto.
      by rewrite !sep_associative in Hm by auto.
    + simpl; rewrite mem_locks_union by auto; revert Hlocks HE; clear.
      rewrite !ectx_subst_locks; set_solver.
    + eapply Hnext; eauto. exists mA; auto.
Qed.
Lemma ax_expr_compose Γ δ {vn} A (Ps : vec (vassert K) vn) (Q : vassert K)
    Δ (E : ectx_full K vn) (es : vec (expr K) vn) (ρ : stack K) n
    (ms : vec (mem K) vn) (τlrs : vec (lrtype K) vn) σlr :
  ✓ Γ → ✓{Γ,Δ} δ → locks E = ∅ → ✓{Δ}* ρ →
  ## ms → (∀ i, ✓{Γ,Δ} (ms !!! i)) →
  ax_expr_invariant A Γ Δ δ ρ n (⋃ ms) →
  (∀ i, locks (es !!! i) ⊆ mem_locks (ms !!! i)) →
  (∀ i, ax_graph (ax_expr_cond ρ A) (ax_expr_post (Ps !!! i) (τlrs !!! i))
      Γ δ Δ ρ n [] (Expr (es !!! i)) (ms !!! i)) →
  (∀ Δ' n' (νs : vec _ vn) (ms' : vec _ vn),
    ## ms' → (∀ i, ✓{Γ,Δ'} (ms' !!! i)) → Δ ⇒ₘ Δ' → n' ≤ n →
    (∀ i, (Γ,Δ') ⊢ νs !!! i : τlrs !!! i) →
    (∀ i, assert_holds ((Ps !!! i) (νs !!! i))
      Γ Δ' δ ρ n' (cmap_erase (ms' !!! i))) →
    ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ' ρ n' [] (Expr
      (depsubst E (vzip_with (λ m ν, %#{mem_locks m} ν) ms' νs)%E)) (⋃ ms')) →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ ρ n []
    (Expr (depsubst E es)) (⋃ ms).
Proof.
  intros ? Hδ HE. revert Δ es ms Hδ.
  induction n as [[|n] IH] using lt_wf_ind; [intros; apply ax_O |].
  intros Δ es ms Hδ Hρ Hms Hms' HA Hes Hax1 Hax2.
  destruct (expr_vec_values es) as [(Ωs&νs&->)|[i Hi]].
  { assert ((∀ i, assert_holds ((Ps !!! i) (νs !!! i))
        Γ Δ δ ρ (S n) (cmap_erase (ms !!! i))) ∧
      (∀ i, mem_locks (ms !!! i) = Ωs !!! i) ∧
      (∀ i, (Γ,Δ) ⊢ νs !!! i : τlrs !!! i)) as (?&?&?).
    { rewrite <-!forall_and_distr; intros i.
      specialize (Hax1 i); rewrite vlookup_zip_with in Hax1.
      eapply ax_expr_lrval; [| |eauto];
        eauto using ax_expr_invariant_weaken, @sep_subseteq_lookup. }
      rewrite (vec_eq (vzip_with EVal Ωs νs)
        (vzip_with (λ m ν, (%#{mem_locks m} ν)%E) ms νs))
        by (intros i; rewrite !vlookup_zip_with; f_equal; auto); auto. }
  apply ax_further_alt.
  intros Δ' n' m' a ??? Hframe; inversion_clear Hframe as [mA mf ??? Hm|];
    simplify_equality'; simplify_mem_disjoint_hyps.
  split; [|intros S' p].
  { rewrite (ectx_full_to_item_correct _ _ i); apply (rcred_ectx _ _ [_]).
    assert (## (ms !!! i :: delete (i:nat) (ms:list _) ++ [mf;mA])).
    { by rewrite app_comm_cons, sep_disjoint_equiv_delete. }
    eapply (ax_red (ax_expr_cond ρ A) (ax_expr_post (Ps !!! i) (τlrs !!! i)))
      with Δ' n' (lookup_total (A := mem K) i ms) (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA).
    { eauto using cmap_union_list_lookup_valid. }
    { econstructor; auto 1.
      { by rewrite sep_associative, sep_union_delete by auto. }
      apply cmap_union_valid_2; auto.
      apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
        eauto using cmap_union_list_lookup_valid. }
    { simpl; contradict Hi; eauto using ax_expr_post_expr_nf. }
    eauto using ax_graph_weaken.  }
  pattern S'; apply (rcstep_expr_depsubst_inv _ _ _ _ _ _ _ _ p); clear p.
  * clear i Hi; intros i e' m2 p' ?.
    assert (## (ms !!! i :: delete (i:nat) (ms:list _) ++ [mf;mA])).
    { by rewrite app_comm_cons, sep_disjoint_equiv_delete. }
    feed inversion (ax_step (ax_expr_cond ρ A)
      (ax_expr_post (Ps !!! i) (τlrs !!! i))
      Γ δ Δ' ρ n' [] (Expr (es !!! i)) (ms !!! i)
      (ms !!! i ∪ ⋃ delete (i:nat) (ms:list _) ∪ mf ∪ mA)
      (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA)
      (State [] (Expr e') m2)) as [Δ'' ? n'' ? m ?? Hunframe _]; subst; auto.
    { eauto using cmap_union_list_lookup_valid. }
    { constructor; rewrite ?sep_associative by auto; auto.
      apply cmap_union_valid_2; auto.
      apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
        eauto using cmap_union_list_lookup_valid. }
    { by rewrite sep_union_delete by done. }
    { by rewrite sep_union_delete by done. }
    { eauto using ax_graph_weaken. }
    clear Hm.
    inversion_clear Hunframe; simplify_equality; simplify_mem_disjoint_hyps.
    apply mk_ax_next with Δ'' (m ∪ ⋃ delete (i:nat) (ms:list _)); simpl; auto.
    { constructor; auto. by rewrite sep_associative by auto. }
    { rewrite ectx_full_subst_locks, HE, (left_id_L ∅ (∪)).
      rewrite <-sep_union_insert by auto.
      rewrite mem_locks_union_list by (rewrite sep_disjoint_equiv_insert; auto).
    
      apply union_list_preserving, Forall2_fmap, Forall2_vlookup.
      intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      by rewrite !vlookup_insert_ne. }
    rewrite <-sep_union_insert by auto.
    assert (## (mf :: mA :: vinsert i m ms)).
    { rewrite sep_disjoint_equiv_insert; auto. }
    apply IH; eauto using indexes_valid_weaken, funenv_valid_weaken.
    + intros j. destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite vlookup_insert_ne by done.
      eauto using cmap_union_list_delete_lookup_valid.
    + exists mA; split_and ?; eauto using assert_weaken, indexes_valid_weaken.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      by rewrite !vlookup_insert_ne.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite !vlookup_insert_ne by done.
      apply ax_graph_weaken with Δ (S n); eauto.
  * clear i Hi. intros i E' Ω f τs τ Ωs vs ? Hesi p ?.
    assert (Ω ∪ ⋃ Ωs ⊆ mem_locks (ms !!! i)) as HΩ.
    { transitivity (locks (es !!! i)); [|done].
      rewrite Hesi, ectx_subst_locks; simpl.
      rewrite fmap_zip_with_l by auto; clear; set_solver. }
    assert (## (mf :: mA :: ms !!! i :: delete (i:nat) (ms:list _))).
    { rewrite sep_disjoint_equiv_delete by auto; auto. }
    assert (## (mf :: mA ::
      mem_unlock (Ω ∪ ⋃ Ωs) (ms !!! i) :: delete (i:nat) (ms:list _))).
    { rewrite <-mem_unlock_disjoint_le by auto; auto. }
    feed inversion (ax_step (ax_expr_cond ρ A)
      (ax_expr_post (Ps !!! i) (τlrs !!! i))
      Γ δ Δ' ρ n' [] (Expr (es !!! i)) (ms !!! i)
      (⋃ ms ∪ mf ∪ mA) (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA)
      (State [CFun E'] (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) (⋃ ms ∪ mf ∪ mA))))
      as [Δ'' ? n'' ? m ?? Hunframe _ ? Hm']; trivial; subst.
    { eauto using cmap_union_list_lookup_valid. }
    { constructor; auto.
      { by rewrite sep_associative, sep_union_delete by auto. }
      apply cmap_union_valid_2; auto.
      apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
        eauto using cmap_union_list_lookup_valid. }
    { eauto using ax_graph_weaken, cmap_union_list_lookup_valid. }
    apply mk_ax_next with Δ''
      (mem_unlock (Ω ∪ ⋃ Ωs) (ms !!! i) ∪ ⋃ delete (i:nat) (ms:list _) ∪ mA);
      simpl; auto.
    { rewrite <-(sep_union_delete ms i), !mem_unlock_union by (by auto
         || rewrite !mem_locks_union by auto; revert HΩ; clear; set_solver).
      eapply ax_unframe_expr_to_fun; eauto. }
    inversion_clear Hunframe as [|m''| |];
      simplify_equality'; simplify_mem_disjoint_hyps.
    assert (mem_unlock (Ω ∪ ⋃ Ωs) (ms !!! i) = m''); subst.
    { apply sep_cancel_r with (⋃ delete (i:nat) (ms:list _) ∪ mf ∪ mA); auto.
      rewrite <-mem_unlock_union, (sep_associative m'') by auto.
      by rewrite !(sep_associative (ms !!! i)), sep_union_delete by auto. }
    rewrite <-(sep_union_delete ms i), !mem_unlock_union in Hm' by
      (by auto || rewrite !mem_locks_union by auto; revert HΩ; set_solver).
    simplify_mem_disjoint_hyps.
    rewrite (sep_commutative _ mA), sep_associative by auto.
    apply ax_call_compose with
      (P:=ax_expr_post (Ps !!! i) (τlrs !!! i)) (k:=[]) (E:=E'); auto.
    { rewrite locks_snoc. apply union_preserving_l.
      rewrite ectx_full_to_item_locks, HE, (left_id_L ∅ (∪)).
      rewrite mem_locks_union_list by solve_mem_disjoint.
      apply union_list_preserving, Forall2_fmap, Forall2_delete.
      apply Forall2_vlookup; auto. }
    { by rewrite (sep_commutative mA) by auto. }
    intros Δ''' n''' m' e' ????? HmA ? Hax; simplify_mem_disjoint_hyps.
    rewrite <-sep_union_insert by auto.
    rewrite subst_snoc, <-ectx_full_to_item_correct_alt.
    apply IH; eauto using funenv_valid_weaken, indexes_valid_weaken.
    + rewrite sep_disjoint_equiv_insert; auto.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite vlookup_insert_ne by done.
      eauto using cmap_union_list_delete_lookup_valid.
    + rewrite sep_union_insert by auto.
      apply ax_expr_invariant_weaken with (S n''')
        (m' ∪ ⋃ delete (i : nat) (ms : list _));
        eauto using indexes_valid_weaken, @sep_reflexive.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      by rewrite !vlookup_insert_ne by done.
    + intros j; destruct (decide (i = j)); subst; [by rewrite !vlookup_insert|].
      rewrite !vlookup_insert_ne by done.
      apply ax_graph_weaken with Δ (S n); eauto.
  * rewrite Forall_vlookup; naive_solver.
  * clear i Hi. intros i E' e ? p ?.
    destruct (ax_step_undef (ax_expr_cond ρ A)
      (ax_expr_post (Ps !!! i) (τlrs !!! i)) Γ δ Δ' ρ n' [] (Expr (es !!! i))
      (ms !!! i) (⋃ ms ∪ mf ∪ mA)
      (InExpr (⋃ delete (i:nat) (ms:list _) ∪ mf) mA) [] (UndefExpr E' e)
      (⋃ ms ∪ mf ∪ mA));
      eauto using cmap_union_list_lookup_valid, ax_graph_weaken.
    assert (## (mf :: mA :: ms !!! i :: delete (i:nat) (ms:list _))).
    { rewrite sep_disjoint_equiv_delete; auto. }
    constructor; auto.
    { by rewrite sep_associative, sep_union_delete by auto. }
    apply cmap_union_valid_2; auto.
    apply cmap_union_list_valid, Forall_delete, Forall_vlookup;
      eauto using cmap_union_list_lookup_valid.
Qed.
Lemma ax_expr_compose_1 Γ δ A P Q Δ (E : ectx_full K 1) e ρ n m τlr σlr :
  ✓ Γ → ✓{Γ,Δ} δ → locks E = ∅ → ✓{Δ}* ρ → ✓{Γ,Δ} m →
  ax_expr_invariant A Γ Δ δ ρ n m →
  locks e ⊆ mem_locks m →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post P τlr) Γ δ Δ ρ n [] (Expr e) m →
  (∀ Δ' n' ν m',
    ✓{Γ,Δ'} m' → Δ ⇒ₘ Δ' → n' ≤ n → (Γ,Δ') ⊢ ν : τlr →
    assert_holds (P ν) Γ Δ' δ ρ n' (cmap_erase m') →
    ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ' ρ n' []
       (Expr (depsubst E [# %#{mem_locks m'} ν]%E)) m') →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ ρ n []
    (Expr (depsubst E [# e])) m.
Proof.
  intros ???????? Hax. rewrite <-(sep_right_id m) by auto.
  apply (ax_expr_compose Γ δ A [# P]%A _ Δ E [# e] ρ n [# m] [# τlr]); simpl;
    rewrite ?sep_right_id by auto; auto; try (by intros; inv_all_vec_fin).
  intros Δ' n' νs ms' ? Hm' ?? Hν Hax'; inv_all_vec_fin; simpl.
  rewrite ?sep_right_id by auto.
  apply Hax; apply (Hm' 0%fin) || apply (Hν 0%fin) || apply (Hax' 0%fin)|| done.
Qed.
Lemma ax_expr_compose_2 Γ δ A P1 P2 Q Δ
    (E : ectx_full K 2) e1 e2 ρ n m1 m2 τlr1 τlr2 σlr :
  ✓ Γ → ✓{Γ,Δ} δ → locks E = ∅ → ✓{Δ}* ρ → ## [m1; m2] → ✓{Γ,Δ} m1 → ✓{Γ,Δ} m2 →
  ax_expr_invariant A Γ Δ δ ρ n (m1 ∪ m2) →
  locks e1 ⊆ mem_locks m1 → locks e2 ⊆ mem_locks m2 →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post P1 τlr1) Γ δ Δ ρ n [] (Expr e1) m1 →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post P2 τlr2) Γ δ Δ ρ n [] (Expr e2) m2 →
  (∀ Δ' n' ν1 ν2 m1' m2',
    ## [m1';m2'] → ✓{Γ,Δ'} m1' → ✓{Γ,Δ'} m2' → Δ ⇒ₘ Δ' → n' ≤ n →
    (Γ,Δ') ⊢ ν1 : τlr1 → (Γ,Δ') ⊢ ν2 : τlr2 →
    assert_holds (P1 ν1) Γ Δ' δ ρ n' (cmap_erase m1') →
    assert_holds (P2 ν2) Γ Δ' δ ρ n' (cmap_erase m2') →
    ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ' ρ n' []
      (Expr (depsubst E [# %#{mem_locks m1'} ν1; %#{mem_locks m2'} ν2]%E))
      (m1' ∪ m2')) →
  ax_graph (ax_expr_cond ρ A) (ax_expr_post Q σlr) Γ δ Δ ρ n []
    (Expr (depsubst E [# e1; e2])) (m1 ∪ m2).
Proof.
  intros ???????????? Hax. rewrite <-(sep_right_id m2) by auto.
  apply (ax_expr_compose Γ δ A [# P1; P2]%A Q Δ E
    [# e1; e2] ρ n [# m1; m2] [# τlr1; τlr2] σlr); simpl;
    rewrite ?sep_right_id by auto; auto; try (by intros; inv_all_vec_fin).
  intros Δ' n' νs ms' ? Hm' ?? Hν Hax'; inv_all_vec_fin; simpl.
  rewrite ?sep_right_id by auto.
  by apply Hax; simpl;
    repeat match goal with
    | H : ∀ _ : fin _, _ |- _ => apply (H 0%fin)
    | H : ∀ _ : fin _, _ |- _ => apply (H 1%fin)
    end.
Qed.
End axiomatic_expressions_help.
