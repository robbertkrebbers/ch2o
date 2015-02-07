(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export permission_bits_separation memory_trees.
Local Open Scope ctype_scope.

Section memory_trees.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types α : bool.
Implicit Types Δ : memenv Ti.
Implicit Types τb : base_type Ti.
Implicit Types τ σ : type Ti.
Implicit Types τs σs : list (type Ti).
Implicit Types o : index.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).
Implicit Types w : mtree Ti.
Implicit Types ws : list (mtree Ti).
Implicit Types wxbs : mtree Ti * list (pbit Ti).
Implicit Types wxbss : list (mtree Ti * list (pbit Ti)).
Implicit Types rs : ref_seg Ti.
Implicit Types r : ref Ti.
Implicit Types g : mtree Ti → mtree Ti.

Local Arguments union _ _ !_ !_ /.
Hint Resolve Forall_take Forall_drop Forall_app_2 Forall_replicate.
Hint Resolve Forall2_take Forall2_drop Forall2_app.
Hint Immediate env_valid_lookup env_valid_lookup_lookup.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).
Hint Immediate ctree_typed_type_valid.
Hint Immediate TArray_valid_inv_type.

Ltac solve_length := simplify_equality'; repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | rewrite type_mask_length by eauto | rewrite replicate_length
  | rewrite bit_size_of_int | rewrite int_width_char | rewrite resize_length
  | rewrite zip_with_length | erewrite sublist_lookup_length by eauto
  | rewrite insert_length | rewrite field_bit_padding_length by done
  | erewrite sublist_alter_length by eauto
  | match goal with
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
        | H : Γ !! ?s = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
          unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) by done;
          assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s))
            by eauto using bit_size_of_union_lookup
        end
    | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
    end ]; first [omega | lia].
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (_ = length _) => solve_length.
Hint Extern 0 (_ ≤ length _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.

Lemma ctree_typed_subseteq Γ Δ w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ w2 : τ → w1 ⊆ w2 → (Γ,Δ) ⊢ w1 : τ.
Proof.
  intros ? Hw2 Hw. revert w1 w2 Hw τ Hw2.
  refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _).
  * intros τb xbs1 xbs2 ?? Hw2; apply (ctree_typed_inv_l _ _ _ _ _ Hw2).
    typed_constructor; eauto using Forall2_length_r, pbits_subseteq_valid.
  * intros τ ws1 ws2 _ IH τ' Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ' Hw2.
    intros ? Hle; typed_constructor; eauto using Forall2_length, eq_sym.
    clear Hle. induction IH; decompose_Forall_hyps; auto.
  * intros s wxbss1 wxbss2 _ IH Hxbss τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    intros τs Hs Hws2 Hxbss2 Hindet Hlen. typed_constructor; eauto.
    + clear Hxbss Hs Hxbss2 Hlen. revert τs Hws2.
      induction IH; intros; decompose_Forall_hyps; auto.
    + clear IH Hws2 Hlen. induction Hxbss; decompose_Forall_hyps;
        eauto using pbits_subseteq_valid.
    + clear Hlen Hws2 IH Hxbss2. induction Hxbss; decompose_Forall_hyps;
        constructor; eauto using pbits_indetified_subseteq.
    + rewrite <-Hlen. clear IH Hws2 Hxbss2 Hlen Hindet.
      induction Hxbss; f_equal'; eauto using Forall2_length.
  * intros s i w1 w2 xbs1 xbs2 ? IH ? Hmap τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    typed_constructor; eauto using pbits_subseteq_valid,
      pbits_indetified_subseteq.
    by erewrite Forall2_length by eauto.
  * intros s xbs1 xbs2 ?? Hw2; apply (ctree_typed_inv_l _ _ _ _ _ Hw2).
    typed_constructor; eauto using Forall2_length_r, pbits_subseteq_valid.
  * intros s i xbs1 w2 xbs2 ??? Hmap τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    intros τs τ ???????. typed_constructor; eauto 1.
    + apply pbits_subseteq_valid with (ctree_flatten w2 ++ xbs2);
        eauto 3 using ctree_flatten_valid.
    + by erewrite Forall2_length, app_length, ctree_flatten_length by eauto.
Qed.
Lemma ctree_disjoint_type_of w1 w2 : w1 ⊥ w2 → type_of w1 = type_of w2.
Proof. destruct 1; f_equal'; eauto using Forall2_length. Qed.
Lemma ctree_union_type_of w1 w2 : w1 ⊥ w2 → type_of (w1 ∪ w2) = type_of w1.
Proof. destruct 1; f_equal'; rewrite zip_with_length; auto. Qed.
Lemma ctree_disjoint_typed_unique Γ Δ1 Δ2 w1 w2 τ1 τ2 :
  w1 ⊥ w2 → (Γ,Δ1) ⊢ w1 : τ1 → (Γ,Δ2) ⊢ w2 : τ2 → τ1 = τ2.
Proof.
  intros. erewrite <-(type_of_correct _ _ τ1), <-(type_of_correct _ _ τ2)
    by eauto; eauto using ctree_disjoint_type_of.
Qed.
Lemma ctree_disjoint_typed Γ Δ w1 w2 τ :
  ✓ Γ → w1 ⊥ w2 → (Γ,Δ) ⊢ w1 : τ → ctree_unmapped w2 → (Γ,Δ) ⊢ w2 : τ.
Proof.
  intros ? Hw. revert w1 w2 Hw τ.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros τb ??? τ Hw; pattern τ; apply (ctree_typed_inv_l _ _ _ _ _ Hw).
    intros; constructor; eauto using pbits_disjoint_valid.
  * intros τ ws1 ws2 _ IH τ' Hw; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ' Hw; intros Hws2 Hlen ?.
    typed_constructor; auto. clear Hlen.
    revert τ Hws2. induction IH; intros; decompose_Forall_hyps; auto.
  * intros s wxbss1 wxbss2 _ IH Hxbs τ' Hw; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ' Hw;
      intros τs Hs Hws2 Hxbs2 ? Hlen ?.
    typed_constructor; eauto.
    + clear Hlen Hxbs2 Hs. revert τs Hws2.
      induction IH; intros; decompose_Forall_hyps; auto.
    + clear Hlen Hs Hws2 IH.
      induction Hxbs; decompose_Forall_hyps; eauto using pbits_disjoint_valid.
    + clear Hlen Hs Hws2 Hxbs2 IH. induction Hxbs;
        decompose_Forall_hyps; eauto using pbits_disjoint_indetified.
    + rewrite <-Hlen. elim Hxbs; intros; f_equal'; auto.
  * intros; decompose_Forall_hyps; naive_solver.
  * intros s ??? τ Hw; pattern τ; apply (ctree_typed_inv_l _ _ _ _ _ Hw).
    intros. typed_constructor; eauto using pbits_disjoint_valid.
  * intros; decompose_Forall_hyps; naive_solver.
  * intros s i w1 xbs1 xbs2 ???? τ Hw; pattern τ;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ Hw; intros τs τ; intros.
    assert (length xbs2 = bit_size_of Γ (unionT s)).
    { erewrite <-Forall2_length by eauto; auto. }
    econstructor; eauto using pbits_disjoint_valid, ctree_flatten_valid.
Qed.
Lemma ctree_unflatten_disjoint Γ τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ →
  xbs1 ⊥* xbs2 → ctree_unflatten Γ τ xbs1 ⊥ ctree_unflatten Γ τ xbs2.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs1 xbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite !ctree_unflatten_base. by constructor.
  * intros τ n _ IH _ xbs1 xbs2 Hxbs. rewrite !ctree_unflatten_array.
    constructor. revert xbs1 xbs2 Hxbs.
    induction n; simpl; intros; constructor; auto.
  * intros [] s τs Hs _ IH _ xbs1 xbs2 Hxbs;
      erewrite !ctree_unflatten_compound by eauto; constructor; auto.
    + revert xbs1 xbs2 Hxbs. clear Hs. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros;
        decompose_Forall_hyps; constructor; simpl; auto.
    + revert xbs1 xbs2 Hxbs. clear Hs IH. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros;
        constructor; simpl; auto using pbits_indetify_disjoint.
Qed.
Lemma ctree_unflatten_union Γ τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ → xbs1 ⊥* xbs2 → ctree_unflatten Γ τ (xbs1 ∪* xbs2)
  = ctree_unflatten Γ τ xbs1 ∪ ctree_unflatten Γ τ xbs2.
Proof.
  intros HΓ Hτ. revert τ Hτ xbs1 xbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. by rewrite !ctree_unflatten_base.
  * intros τ n _ IH _ xbs1 xbs2 Hxbs. rewrite !ctree_unflatten_array; f_equal'.
    revert xbs1 xbs2 Hxbs. induction n; simpl; intros; f_equal';
      rewrite ?zip_with_take, ?zip_with_drop; auto.
  * intros [] s τs Hs _ IH _ xbs1 xbs2 Hxbs;
      erewrite !ctree_unflatten_compound by eauto; f_equal'; auto.
    revert xbs1 xbs2 Hxbs. clear Hs. unfold struct_unflatten.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps; repeat f_equal; simpl;
      rewrite ?fmap_drop, ?zip_with_take, ?pbits_indetify_union,
      ?zip_with_drop; eauto.
Qed.
Lemma ctree_unflatten_subseteq Γ τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ →
  xbs1 ⊆* xbs2 → ctree_unflatten Γ τ xbs1 ⊆ ctree_unflatten Γ τ xbs2.
Proof.
  intros. rewrite <-(seps_union_difference xbs1 xbs2) by done.
  rewrite ctree_unflatten_union; eauto using @seps_disjoint_difference.
  apply ctree_union_subseteq_l, ctree_unflatten_disjoint;
    eauto using @seps_disjoint_difference.
Qed.
Lemma ctree_flatten_unflatten_disjoint Γ Δ w τ ys :
  ✓ Γ → (Γ,Δ) ⊢ w : τ →
  ys ⊥* ctree_flatten w → Forall sep_unmapped ys → ctree_unflatten Γ τ ys ⊥ w.
Proof.
  intros HΓ Hw. revert w τ Hw ys. refine (ctree_typed_ind _ _ _ _ _ _ _ _).
  * by constructor.
  * intros ws τ Hws IH _ ys Hys Hys'.
    rewrite ctree_unflatten_array; simplify_equality'. constructor.
    revert ys Hys Hys'. induction IH; intros; decompose_Forall_hyps;
      rewrite ?take_app_alt, ?drop_app_alt
        by (erewrite Forall2_length by eauto; auto); constructor; auto.
  * intros s wxbss τs Hs Hws IH _ ? Hlen ys Hys Hys';
      erewrite ctree_unflatten_compound by eauto; simplify_equality'.
    clear Hs. constructor; revert dependent wxbss; revert dependent ys;
      unfold field_bit_padding, struct_unflatten;
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
      rewrite ?take_app_alt, ?drop_app_alt
        by (erewrite ?app_length, !Forall2_length by eauto; solve_length);
      rewrite ?pbits_indetify_unmapped by auto; constructor; eauto.
  * intros s i τs w xbs τ ????????  ys Hys Hys';
      erewrite ctree_unflatten_compound by eauto; decompose_Forall_hyps.
    constructor; eauto using ctree_typed_sep_valid.
  * intros. erewrite ctree_unflatten_compound by eauto. by constructor.
Qed.
Lemma ctree_new_disjoint Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → ctree_new Γ ∅ τ ⊥ w.
Proof.
  intros.
  eapply ctree_flatten_unflatten_disjoint; eauto using @sep_unmapped_empty.
  eapply Forall2_replicate_l, Forall_impl; eauto using ctree_flatten_valid.
  eauto using @sep_disjoint_empty_l, pbit_valid_sep_valid.
Qed.
Lemma ctree_new_union Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → ctree_new Γ ∅ τ ∪ w = w.
Proof. eauto using @ctree_left_id, ctree_new_disjoint, ctree_new_Forall. Qed.
Lemma ctree_new_subseteq Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → ctree_new Γ ∅ τ ⊆ w.
Proof.
  intros. erewrite <-(ctree_new_union _ _ w) by eauto.
  eauto using @ctree_union_subseteq_l, ctree_new_disjoint.
Qed.
Lemma ctree_lookup_seg_disjoint Γ Δ1 Δ2 w1 w2 τ rs w1' w2' :
  ✓ Γ → (Γ,Δ1) ⊢ w1 : τ → (Γ,Δ2) ⊢ w2 : τ → w1 ⊥ w2 →
  w1 !!{Γ} rs = Some w1' → w2 !!{Γ} rs = Some w2' → w1' ⊥ w2'.
Proof.
  intros ? Hw1 Hw2 Hw' Hrs1 Hrs2. destruct Hw', rs;
    pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs1); clear Hrs1;
    pattern w2'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs2); clear Hrs2;
    intros; decompose_Forall_hyps;
    eauto using ctree_unflatten_disjoint, @ctree_flatten_disjoint.
  * apply (ctree_typed_inv_l _ _ _ _ _ Hw2); intros; simplify_equality.
    rewrite take_app_alt by (erewrite Forall2_length by eauto; auto).
    eauto using ctree_flatten_unflatten_disjoint.
  * apply (ctree_typed_inv_l _ _ _ _ _ Hw1); intros; simplify_equality.
    rewrite take_app_alt by (erewrite <-Forall2_length by eauto; auto).
    symmetry; eauto using ctree_flatten_unflatten_disjoint.
Qed.
Lemma ctree_lookup_disjoint Γ Δ1 Δ2 w1 w2 τ r w1' w2' :
  ✓ Γ → (Γ,Δ1) ⊢ w1 : τ → (Γ,Δ2) ⊢ w2 : τ → w1 ⊥ w2 →
  w1 !!{Γ} r = Some w1' → w2 !!{Γ} r = Some w2' → w1' ⊥ w2'.
Proof.
  intros ??. revert w1' w2'. induction r as [|rs r]; intros w1'' w2''.
  { by intros; simplify_type_equality'. }
  rewrite !ctree_lookup_cons; intros. destruct (w1 !!{Γ} r) as [w1'|] eqn:?,
    (w2 !!{Γ} r) as [w2'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ Δ1 w1 τ r w1') as (σ1&?&?); auto.
  destruct (ctree_lookup_Some Γ Δ2 w2 τ r w2') as (σ1'&?&?); auto.
  simplify_type_equality; eauto 3 using ctree_lookup_seg_disjoint.
Qed.
Lemma ctree_lookup_seg_subseteq Γ w1 w2 rs w1' :
  ✓ Γ → w1 ⊆ w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_Forall sep_unmapped w1' →
  ∃ w2', w2 !!{Γ} rs = Some w2' ∧ w1' ⊆ w2'.
Proof.
  intros ? Hw' Hrs1. destruct Hw', rs;
    pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs1); clear Hrs1;
    intros; decompose_Forall_hyps; eauto 1.
  * simplify_option_equality; eauto.
  * simplify_option_equality; eauto.
  * simplify_option_equality; eauto.
  * simplify_option_equality by eauto using @seps_unshared_weaken,
      @ctree_unshared_weaken; eexists; split;
      eauto using ctree_unflatten_subseteq, @ctree_flatten_subseteq.
  * simplify_option_equality by eauto using @seps_unshared_weaken;
      eexists; split; eauto; eauto using ctree_unflatten_subseteq.
  * exfalso; naive_solver
      eauto using ctree_unflatten_Forall_le, pbit_unmapped_indetify.
Qed.
Lemma ctree_lookup_subseteq Γ w1 w2 r w1' :
  ✓ Γ → w1 ⊆ w2 → w1 !!{Γ} r = Some w1' → ¬ctree_Forall sep_unmapped w1' →
  ∃ w2', w2 !!{Γ} r = Some w2' ∧ w1' ⊆ w2'.
Proof.
  intros ?. revert w1'. induction r as [|rs r IH]; intros w1'' w2''.
  { intros; simplify_type_equality'. by exists w2. }
  rewrite !ctree_lookup_cons; intros.
  destruct (w1 !!{Γ} r) as [w1'|] eqn:?; simplify_equality'.
  destruct (IH w1') as (?&->&?);
    eauto using ctree_lookup_seg_Forall, pbit_unmapped_indetify; csimpl.
  eauto using ctree_lookup_seg_subseteq.
Qed.
Lemma ctree_alter_seg_disjoint Γ Δ g w1 w2 τ rs w1' :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') → ctree_alter_seg Γ g rs w1 ⊥ w2.
Proof.
  intros ? Hw1 Hw Hw1' Hrs. revert w1 w2 Hw Hw1 Hw1' Hrs.
  refine (ctree_disjoint_ind _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros τ' ws1 ws2 ? _ ? Hrs Hg. destruct rs; simplify_option_equality.
    constructor. apply Forall2_alter_l; auto 1.
    intros; decompose_Forall_hyps; eauto.
  * intros s wxbss1 wxbss2 Hws Hxbss _ Hrs; destruct rs as [|i|];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros w1 xbs -> ? _ ?; simpl; constructor.
    + apply Forall2_alter_l; [elim Hws; constructor; simpl; eauto|].
      intros [??] [??] ??; decompose_Forall_hyps; eauto.
    + apply Forall2_alter_l; [elim Hxbss; constructor; simpl; eauto|].
      intros [??] [??] ??; decompose_Forall_hyps; eauto.
  * intros s i w1 w2 xbs1 xbs2 ? _ ??  Hum ? Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { intros; simplify_option_equality. constructor; naive_solver. }
    intros τs τ' ???????; destruct Hum; simplify_equality'.
    eauto using @seps_unshared_unmapped, @ctree_flatten_disjoint.
  * intros s xbs1 xbs2 ? _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ??????; simplify_option_equality. constructor.
    + rewrite <-(take_drop (bit_size_of Γ τ') xbs2); apply Forall2_app.
      { erewrite <-pbits_indetify_mask_unmapped, <-(ctree_flatten_unflatten_le
          Γ τ') by eauto using @seps_unshared_unmapped.
        eauto using @ctree_flatten_disjoint, ctree_unflatten_disjoint. }
      erewrite <-pbits_indetify_unmapped by eauto using @seps_unshared_unmapped.
      eauto using pbits_indetify_disjoint.
    + eauto using @seps_unshared_unmapped.
    + eapply ctree_disjoint_valid_l;
        eauto using ctree_flatten_disjoint, ctree_unflatten_disjoint.
    + naive_solver.
  * intros s i xbs1 w2 xbs2 ??? Hum _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ????; destruct Hum; simplify_equality.
    rewrite <-Forall_app; eauto using @seps_unshared_unmapped.
  * intros s i w1 xbs1 xbs2 Hxbs2 ??? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs τ ??? _ ? _; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { rewrite Forall2_app_inv_l in Hxbs2;
        destruct Hxbs2 as (xbs2'&xbs2''&?&?&->).
      intros ???? Hw; simplify_option_equality; decompose_Forall_hyps.
      constructor; auto.
      + apply Forall2_app; auto.
        erewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) xbs2'),
          <-(ctree_flatten_unflatten Γ τ xbs2') by
          (erewrite <-?(Forall2_length _ (ctree_flatten _)) by eauto; eauto).
        apply ctree_flatten_disjoint, Hw.
        symmetry; eauto using ctree_flatten_unflatten_disjoint.
      + eapply ctree_disjoint_valid_l, Hw.
        symmetry; eauto using ctree_flatten_unflatten_disjoint.
      + naive_solver. }
    intros ? τ' ?????????; simplify_option_equality. constructor; auto.
    + rewrite <-(take_drop (bit_size_of Γ τ') xbs2); apply Forall2_app; auto.
      { erewrite <-pbits_indetify_mask_unmapped, <-(ctree_flatten_unflatten_le
          Γ τ') by eauto using @seps_unshared_unmapped.
        eauto using @ctree_flatten_disjoint, ctree_unflatten_disjoint. }
      erewrite <-pbits_indetify_unmapped by eauto using @seps_unshared_unmapped.
      eauto using pbits_indetify_disjoint.
    + eapply ctree_disjoint_valid_l;
        eauto using ctree_flatten_disjoint, ctree_unflatten_disjoint.
    + naive_solver.
Qed.
Lemma ctree_alter_disjoint Γ Δ g w1 w2 τ r w1' :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} r = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') → ctree_alter Γ g r w1 ⊥ w2.
Proof.
  intros ??. revert g w1'. induction r as [|rs r]; intros g w1''.
  { intros; simplify_type_equality'; eauto. }
  rewrite !ctree_lookup_cons; intros.
  destruct (w1 !!{Γ} r) as [w1'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ Δ w1 τ r w1') as (σ1&?&?);
    eauto 8 using ctree_alter_lookup_seg_Forall, ctree_alter_seg_disjoint.
Qed.
Lemma ctree_alter_seg_union Γ Δ g w1 w2 τ rs w1' :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') →
  (∀ w2', w1' ⊥ w2' → g (w1' ∪ w2') = g w1' ∪ w2') →
  ctree_alter_seg Γ g rs (w1 ∪ w2) = ctree_alter_seg Γ g rs w1 ∪ w2.
Proof.
  intros ? Hw1 Hw Hw1' Hrs. revert w1 w2 Hw Hw1 Hw1' Hrs.
  refine (ctree_disjoint_ind _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros τ' ws1 ws2 Hws _ Hrs  _ Hg Hg'.
    destruct rs as [i| |]; simplify_option_equality. f_equal. revert i Hrs.
    induction Hws; intros [|?] ?; simplify_equality'; f_equal'; eauto.
  * intros s wxbss1 wxbss2 Hws _ _ Hrs; destruct rs as [|i|];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros w1 xbs -> Hrs _ Hg Hg'; f_equal'. revert i Hrs.
    induction Hws as [|[] []]; intros [|?] ?;
      simplify_equality'; repeat f_equal'; eauto.
  * intros s i w1 w2 xbs1 xbs2 ? _ ??  Hum ? Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { intros; simplify_option_equality; f_equal; auto. }
    intros τs τ' ???????; destruct Hum; simplify_equality'.
    eauto using @seps_unshared_unmapped, @ctree_flatten_disjoint.
  * intros s xbs1 xbs2 ? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs ??? _; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros ?????? Hg Hg'; simplify_option_equality.
    erewrite Forall2_length by (eapply ctree_flatten_disjoint,
      Hg, ctree_unflatten_disjoint; eauto).
    rewrite ctree_flatten_unflatten_le, mask_length, take_length_le by eauto.
    f_equal.
    + by rewrite zip_with_take, ctree_unflatten_union, Hg',
        <-ctree_merge_flatten, ctree_flatten_unflatten_le,
        pbits_indetify_mask_unmapped
        by eauto using ctree_unflatten_Forall_le, ctree_unflatten_disjoint,
          @seps_unshared_unmapped, pbit_unmapped_indetify.
    + by rewrite zip_with_drop, pbits_indetify_union, (pbits_indetify_unmapped
        (drop _ xbs2)) by eauto using @seps_unshared_unmapped.
  * intros s i xbs1 w2 xbs2 ??? Hum _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ????; destruct Hum; simplify_equality.
    rewrite <-Forall_app; eauto using @seps_unshared_unmapped.
  * intros s i w1 xbs1 xbs2 Hxbs2 ??? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs τ ?? Hw1 _ ??; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { rewrite Forall2_app_inv_l in Hxbs2;
        destruct Hxbs2 as (xbs2'&xbs2''&?&?&->).
      intros ???? Hg Hg'; simplify_option_equality; decompose_Forall_hyps.
      assert (length xbs2' = bit_size_of Γ τ).
      { erewrite <-Forall2_length by eauto. solve_length. }
      assert (w1 ⊥ ctree_unflatten Γ τ xbs2').
      { symmetry; eauto using ctree_flatten_unflatten_disjoint. }
      assert (ctree_flatten (g w1) ⊥* xbs2').
      { rewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) xbs2'),
          <-ctree_flatten_unflatten by eauto.
        by apply ctree_flatten_disjoint, Hg. }
      clear Hw1. rewrite !take_app_alt, !drop_app_alt by auto.
      rewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) xbs2'),
        <-ctree_flatten_unflatten, !ctree_merge_flatten
        by eauto using ctree_unflatten_Forall_le, pbit_unmapped_indetify.
      f_equal; auto. }
    intros ? τ' ????????? Hg Hg'; simplify_option_equality.
    assert (length xbs2 = bit_size_of Γ (unionT s)).
    { by erewrite <-Forall2_length by eauto. }
    rewrite ctree_flatten_merge, <-zip_with_app,
      zip_with_take, zip_with_drop, take_drop by done.
    erewrite Forall2_length
      by (eapply ctree_flatten_disjoint, Hg, ctree_unflatten_disjoint; eauto).
    rewrite ctree_flatten_unflatten_le, mask_length, take_length_le by eauto.
    f_equal.
    + by rewrite ctree_unflatten_union, Hg', <-ctree_merge_flatten,
        ctree_flatten_unflatten, pbits_indetify_mask_unmapped
        by eauto using ctree_unflatten_Forall_le, ctree_unflatten_disjoint,
        @seps_unshared_unmapped, pbit_unmapped_indetify.
    + by rewrite pbits_indetify_union,
       (pbits_indetify_unmapped (drop _ xbs2)) by auto.
Qed.
Lemma ctree_alter_union Γ Δ g w1 w2 τ r w1' :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ →
  w1 ⊥ w2 → w1 !!{Γ} r = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ⊥ w2' → g w1' ⊥ w2') →
  (∀ w2', w1' ⊥ w2' → g (w1' ∪ w2') = g w1' ∪ w2') →
  ctree_alter Γ g r (w1 ∪ w2) = ctree_alter Γ g r w1 ∪ w2.
Proof.
  intros ??. revert g w1'. induction r as [|rs r IH]; intros g w1''.
  { intros; simplify_type_equality'; eauto. }
  rewrite !ctree_lookup_cons; intros.
  destruct (w1 !!{Γ} r) as [w1'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_Some Γ Δ w1 τ r w1') as (σ1&?&?); auto.
  eapply IH; eauto using ctree_alter_lookup_seg_Forall,
    ctree_alter_seg_disjoint, ctree_alter_seg_union.
Qed.
Lemma ctree_lookup_byte_disjoint Γ w1 w2 i c1 c2 :
  ✓ Γ → w1 ⊥ w2 → w1 !!{Γ} i = Some c1 → w2 !!{Γ} i = Some c2 → c1 ⊥ c2.
Proof.
  unfold lookupE, ctree_lookup_byte, sublist_lookup; intros;
    simplify_option_equality; auto using ctree_unflatten_disjoint,
    TBase_valid, TInt_valid, @ctree_flatten_disjoint.
Qed.
Lemma ctree_lookup_byte_subseteq Γ w1 w2 i c1 :
  ✓ Γ → w1 ⊆ w2 → w1 !!{Γ} i = Some c1 →
  ∃ c2, w2 !!{Γ} i = Some c2 ∧ c1 ⊆ c2.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w1))
    as [xbs1|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_l (⊆) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    eauto using @ctree_flatten_subseteq.
  exists (ctree_unflatten Γ ucharT xbs2); simplify_option_equality;
    eauto using ctree_unflatten_subseteq, TBase_valid, TInt_valid.
Qed.
Lemma ctree_alter_byte_disjoint Γ Δ g w1 w2 τ i c1 :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ → ctree_unshared w1 → w1 ⊥ w2 → w1 !!{Γ} i = Some c1 →
  (∀ c2, c1 ⊥ c2 → g c1 ⊥ c2) → ctree_alter_byte Γ g i w1 ⊥ w2.
Proof.
  unfold lookupE, ctree_alter_byte, ctree_lookup_byte; intros ???? Hw1 ?.
  destruct (sublist_lookup _ _ _) as [xbs1|] eqn:?; simplify_type_equality'.
  assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,Δ) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2), <-ctree_unflatten_flatten by eauto.
  destruct (Forall2_sublist_lookup_l (⊥) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    eauto using @ctree_flatten_disjoint.
  eapply ctree_unflatten_disjoint, Forall2_sublist_alter_l;
    eauto using @ctree_flatten_disjoint; simpl.
  rewrite <-(mask_false pbit_indetify xbs2 (bit_size_of Γ ucharT)),
    <-type_mask_base, <-ctree_flatten_unflatten
    by eauto using TBase_valid, TInt_valid.
  eauto using @ctree_flatten_disjoint,
    ctree_unflatten_disjoint, TBase_valid, TInt_valid.
Qed.
Lemma ctree_alter_byte_union Γ Δ g w1 w2 τ i c1 :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ → ctree_unshared w1 → w1 ⊥ w2 → w1 !!{Γ} i = Some c1 →
  (∀ c2, c1 ⊥ c2 → g c1 ⊥ c2) → (∀ c2, c1 ⊥ c2 → g (c1 ∪ c2) = g c1 ∪ c2) →
  ctree_alter_byte Γ g i (w1 ∪ w2) = ctree_alter_byte Γ g i w1 ∪ w2.
Proof.
  unfold lookupE, ctree_alter_byte, ctree_lookup_byte; intros ????? Hg Hg'.
  rewrite ctree_union_type_of by done.
  destruct (sublist_lookup _ _ _) as [xbs1|] eqn:?; simplify_type_equality'.
  assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,Δ) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2) at 2 by eauto.
  erewrite <-ctree_unflatten_flatten by eauto.
  destruct (Forall2_sublist_lookup_l (⊥) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    auto using @ctree_flatten_disjoint.
  assert (ctree_flatten (g (ctree_unflatten Γ ucharT xbs1)) ⊥* xbs2).
  { rewrite <-(mask_false pbit_indetify xbs2 (bit_size_of Γ ucharT)),
      <-type_mask_base, <-ctree_flatten_unflatten
      by eauto using TBase_valid, TInt_valid.
    eauto using @ctree_flatten_disjoint,
      ctree_unflatten_disjoint, TBase_valid, TInt_valid. }
  assert (sublist_alter (ctree_flatten ∘ g ∘ ctree_unflatten Γ ucharT)
    (i * char_bits) char_bits (ctree_flatten w1) ⊥* ctree_flatten w2).
  { eapply Forall2_sublist_alter_l; eauto using @ctree_flatten_disjoint. }
  rewrite <-ctree_unflatten_union, ctree_flatten_union by eauto; f_equal.
  symmetry; apply zip_with_sublist_alter with xbs1 xbs2; simpl; auto 1.
  by rewrite ctree_unflatten_union, Hg', ctree_flatten_union,
    ctree_flatten_unflatten, type_mask_base, mask_false by eauto using
    ctree_unflatten_disjoint, TBase_valid, TInt_valid.
Qed.
Lemma ctree_singleton_seg_disjoint Γ τ rs w1 w2 σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ rs : τ ↣ σ → ¬ctree_unmapped w1 → ¬ctree_unmapped w2 →
  w1 ⊥ w2 → ctree_singleton_seg Γ rs w1 ⊥ ctree_singleton_seg Γ rs w2.
Proof.
  intros ?? Hrs ???.
  assert (∀ τ, ✓{Γ} τ → ctree_new Γ ∅ τ ⊥ ctree_new Γ ∅ τ).
  { intros. apply ctree_new_disjoint with ∅;
      eauto using ctree_new_typed, pbit_empty_valid. }
  destruct Hrs as [τ i n _|s i τs τ Hs _|s i]; simplify_option_equality.
  * constructor. apply Forall2_insert; eauto using Forall2_replicate.
  * constructor.
    + apply Forall2_fmap; rewrite !fst_zip by auto.
      eauto using Forall2_insert, Forall2_fmap_2, Forall2_Forall, Forall_impl.
    + apply Forall2_fmap; rewrite !snd_zip by auto.
      apply Forall2_fmap_2, Forall2_Forall, Forall_true; simpl.
      auto using Forall2_replicate, @sep_disjoint_empty_l, @sep_empty_valid.
  * constructor; naive_solver auto using Forall2_replicate,
      @sep_disjoint_empty_l, @sep_empty_valid.
Qed.
Lemma ctree_singleton_disjoint Γ τ r w1 w2 σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ r : τ ↣ σ → ¬ctree_unmapped w1 → ¬ctree_unmapped w2 →
  w1 ⊥ w2 → ctree_singleton Γ r w1 ⊥ ctree_singleton Γ r w2.
Proof.
  intros ?? Hr. revert w1 w2. induction Hr using @ref_typed_ind;
    eauto 10 using ctree_singleton_seg_disjoint, ref_typed_type_valid,
    ctree_singleton_seg_Forall_inv.
Qed.
Lemma ctree_singleton_seg_union Γ τ rs w1 w2 σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ rs : τ ↣ σ →
  ctree_singleton_seg Γ rs (w1 ∪ w2)
  = ctree_singleton_seg Γ rs w1 ∪ ctree_singleton_seg Γ rs w2.
Proof.
  intros ?? Hrs.
  assert (∀ n, replicate n (∅ : pbit Ti) ∪* replicate n ∅ = replicate n ∅).
  { intros. by rewrite zip_with_replicate_l, fmap_replicate by solve_length. }
  assert (∀ τ, ✓{Γ} τ → ctree_new Γ ∅ τ = ctree_new Γ ∅ τ ∪ ctree_new Γ ∅ τ).
  { intros. symmetry. eapply ctree_new_union with ∅;
      eauto using ctree_new_typed, pbit_empty_valid. }
  destruct Hrs as [τ i n _|s i τs τ Hs _|s i]; simplify_option_equality; f_equal.
  * revert i.
    induction (Forall_replicate (ctree_new Γ ∅ τ =) n _ eq_refl)
      as [|w ws ? Hws]; subst; intros [|?]; f_equal'; eauto.
    elim Hws; intros; simplify_equality'; f_equal'; eauto.
  * assert (Forall2 (λ _ τ, ✓{Γ} τ) (field_bit_padding Γ τs) τs) as Hτs.
    { cut (✓{Γ}* τs); [clear Hs|by eauto].
      assert (Forall2 (λ _ _, True) (field_bit_padding Γ τs) τs) as Hτs.
      { apply Forall2_same_length; auto using field_bit_padding_length. }
      induction Hτs; intros; decompose_Forall_hyps; auto. }
    clear Hs. revert i.
    induction Hτs as [|? τ' ? τs ? Hτs]; intros [|i]; repeat f_equal';
      decompose_Forall_hyps; auto.
    elim Hτs; intros; repeat f_equal'; auto.
  * f_equal'; auto.
Qed.
Lemma ctree_singleton_union Γ τ r w1 w2 σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ r : τ ↣ σ →
  ctree_singleton Γ r (w1 ∪ w2)
  = ctree_singleton Γ r w1 ∪ ctree_singleton Γ r w2.
Proof.
  intros ?? Hr; revert w1 w2.
  induction Hr as [|r rs τ1 τ2 τ3] using @ref_typed_ind; intros; simpl; auto.
  erewrite (ctree_singleton_seg_union _ τ2) by eauto using ref_typed_type_valid.
  eauto.
Qed.
End memory_trees.
