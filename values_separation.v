(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export values memory_trees_separation.

Section values.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ : type K.
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types w : mtree K.
Implicit Types v : val K.
Implicit Types vs : list (val K).

Hint Resolve Forall2_take Forall2_drop Forall_take Forall_drop Forall_app_2
  Forall_replicate Forall_resize.
Hint Immediate env_valid_lookup env_valid_lookup_lookup.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit K)).
Local Arguments union _ _ !_ !_ /.

Ltac solve_length := repeat first
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite resize_length | rewrite fmap_length | rewrite replicate_length
  | erewrite ctree_flatten_length by eauto|erewrite val_flatten_length by eauto
  | rewrite zip_with_length | erewrite base_val_flatten_length by eauto
  | match goal with
    | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
      | H : Γ !! ?t = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t))
          by eauto using bit_size_of_union_lookup
      | H : Γ !! ?t = Some [?τ] |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t))
          by eauto using bit_size_of_union_singleton
      end
    end]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (length _ ≠ _) => solve_length.

Lemma to_val_subseteq Γ Δ w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ → w1 ⊆ w2 →
  ctree_Forall (not ∘ sep_unmapped) w1 → to_val Γ w1 = to_val Γ w2.
Proof.
  intros ? Hw1 Hw. revert w1 w2 Hw τ Hw1.
  refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _); simpl.
  * intros; by erewrite pbits_tag_subseteq by eauto.
  * intros τ ws1 ws2 _ IH τ' Hw1; apply (ctree_typed_inv_l _ _ _ _ _ Hw1);
      clear τ' Hw1; intros Hws1 _ ?; f_equal.
    induction IH; decompose_Forall_hyps; f_equal; eauto.
  * intros t wxbs1 wxbs2 _ IH _ τ' Hw1; apply (ctree_typed_inv_l _ _ _ _ _ Hw1);
      clear τ' Hw1; intros τs _ Hws1 _ _ _ ?; f_equal.
    revert τs Hws1; induction IH; intros; decompose_Forall_hyps; f_equal; eauto.
  * intros t i w1 w2 xbs1 xbs2 _ ? _ _ τ' Hw1;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1.
    intros; decompose_Forall_hyps; f_equal'; eauto.
  * intros; by erewrite pbits_tag_subseteq by eauto.
  * intros t i xs1 w2 xs2 _ Hxs _ _ τ' Hw1;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1.
    intros. assert (bit_size_of Γ (unionT t) ≠ 0)
      by eauto using bit_size_of_ne_0, TCompound_valid.
    destruct Hxs; decompose_Forall_hyps.
Qed.
Lemma of_val_disjoint Γ Δ xs1 xs2 v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length xs1 = bit_size_of Γ τ → xs1 ⊥* xs2 →
  Forall (not ∘ sep_unmapped) xs1 → Forall (not ∘ sep_unmapped) xs2 →
  of_val Γ xs1 v ⊥ of_val Γ xs2 v.
Proof.
  intros HΓ Hv. revert v τ Hv xs1 xs2.
  assert (∀ xs (bs : list (bit K)),
    Forall sep_unmapped (zip_with PBit xs bs) →
    length xs ≠ 0 → length bs = length xs → Forall (not ∘ sep_unmapped) xs →
    False).
  { unfold sep_unmapped at 1; simpl.
    intros ????; rewrite <-Forall2_same_length;
      destruct 1; intros; decompose_Forall_hyps; naive_solver. }
  refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * constructor; auto using PBits_disjoint.
  * intros vs τ Hvs IH _ xs1 xs2 Hlen Hxs Hxs1 Hxs2; constructor.
    rewrite bit_size_of_array in Hlen. revert xs1 xs2 Hlen Hxs Hxs1 Hxs2.
    induction IH; decompose_Forall_hyps; simplify_type_equality';
      constructor; rewrite ?zip_with_take,?zip_with_drop; auto.
  * intros t vs τs Ht Hvs IH xs1 xs2 Hlen Hxs Hxs1 Hxs2.
    erewrite bit_size_of_struct in Hlen by eauto; clear Ht.
    erewrite fmap_type_of by eauto; unfold field_bit_padding.
    constructor; revert vs xs1 xs2 Hvs IH Hlen Hxs Hxs1 Hxs2;
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
      simplify_type_equality; constructor; simpl;
      rewrite ?zip_with_drop, ?zip_with_take; auto using PBits_BIndet_disjoint.
  * intros; simplify_type_equality.
    assert (bit_size_of Γ τ ≠ 0) by eauto using bit_size_of_ne_0.
    constructor;
      erewrite ?zip_with_take, ?zip_with_drop, ?ctree_flatten_of_val by eauto;
      auto using PBits_BIndet_disjoint; intros [??]; eauto.
  * constructor; auto using PBits_disjoint.
Qed.
Lemma of_val_union Γ xs1 xs2 v :
  of_val Γ (xs1 ∪* xs2) v = of_val Γ xs1 v ∪ of_val Γ xs2 v.
Proof.
  revert v xs1 xs2. refine (val_ind_alt _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using PBits_union.
  * intros τ vs IH xs1 xs2; f_equal. revert xs1 xs2.
    induction IH; intros; f_equal'; rewrite ?zip_with_take,?zip_with_drop; auto.
  * intros s vs IH xs1 xs2; f_equal. revert xs1 xs2.
    generalize (field_bit_padding Γ (type_of <$> vs)).
    induction IH; intros [|??] ??; repeat f_equal';
      rewrite ?zip_with_drop, ?zip_with_take; auto using PBits_BIndet_union.
  * intros; f_equal;
      rewrite ?zip_with_take, ?zip_with_drop; auto using PBits_BIndet_union.
  * intros; f_equal; auto using PBits_union.
Qed.
Lemma of_val_flatten_disjoint Γ Δ w1 w2 v τ :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ → ctree_unshared w1 →
  ctree_Forall (not ∘ sep_unmapped) w1 → (Γ,Δ) ⊢ v : τ → w1 ⊥ w2 →
  of_val Γ (tagged_perm <$> ctree_flatten w1) v ⊥ w2.
Proof.
  intros. assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,Δ) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2), <-ctree_unflatten_flatten by eauto.
  assert (Forall (not ∘ sep_unmapped) (tagged_perm <$> ctree_flatten w1)).
  { apply pbits_perm_mapped; eauto using
      Forall_impl, ctree_flatten_valid, pbit_valid_sep_valid. }
  symmetry; eapply ctree_flatten_unflatten_disjoint; eauto using
    of_val_typed, pbits_valid_perm_valid, ctree_flatten_valid.
  symmetry; erewrite ctree_flatten_of_val by eauto.
  eauto using PBits_perm_disjoint, @ctree_flatten_disjoint.
Qed.
Lemma ctree_merge_union_of_val Γ Δ xs1 xs2 v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ →
  Forall sep_valid xs1 → Forall (not ∘ sep_unmapped) xs1 →
  length xs1 = bit_size_of Γ τ → of_val Γ (xs1 ∪* xs2) v
  = ctree_merge true (∪) (of_val Γ xs1 v) (flip PBit BIndet <$> xs2).
Proof.
  intros HΓ Hv. revert v τ Hv xs1 xs2.
  refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using PBits_BIndet_union_r.
  * intros vs τ Hvs IH _ xs1 xs2 Hxs1 Hxs1'. rewrite bit_size_of_array.
    intros Hlen; f_equal. revert xs1 xs2 Hxs1 Hxs1' Hlen.
    induction IH; intros; decompose_Forall_hyps; simplify_type_equality; auto.
    erewrite zip_with_take, zip_with_drop, <-fmap_take, <-fmap_drop,
      ctree_flatten_length by eauto using of_val_typed. f_equal; auto.
  * intros t vs τs Ht Hvs IH xs1 xs2 Hxs1 Hxs1'.
    erewrite bit_size_of_struct by eauto; intros Hlen; f_equal.
    unfold field_bit_padding; erewrite fmap_type_of by eauto.
    clear Ht. revert vs xs1 xs2 Hvs IH Hxs1 Hxs1' Hlen.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps; simplify_type_equality; auto.
    erewrite !zip_with_drop, !zip_with_take, <-!fmap_drop, <-!fmap_take,
      ctree_flatten_length, fmap_length, take_length, drop_length,
      Min.min_l, PBits_BIndet_union by (eauto using of_val_typed; lia);
      repeat f_equal; eauto 6.
  * intros t i τs v τ ??? IH xs1 xs2 ???; simplify_type_equality'.
    by erewrite zip_with_take, zip_with_drop, <-fmap_take, <-fmap_drop, IH,
      ctree_flatten_length, PBits_BIndet_union by eauto using of_val_typed.
  * intros; f_equal; auto using PBits_BIndet_union_r.
Qed.
Lemma of_val_flatten_union Γ Δ w1 w2 v τ :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ → ctree_unshared w1 →
  ctree_Forall (not ∘ sep_unmapped) w1 → (Γ,Δ) ⊢ v : τ → w1 ⊥ w2 →
  of_val Γ (tagged_perm <$> ctree_flatten (w1 ∪ w2)) v
  = of_val Γ (tagged_perm <$> ctree_flatten w1) v ∪ w2.
Proof.
  intros. assert (ctree_unmapped w2).
  { eapply seps_unshared_unmapped; eauto using @ctree_flatten_disjoint. }
  assert (Forall (not ∘ sep_unmapped) (tagged_perm <$> ctree_flatten w1)).
  { apply pbits_perm_mapped; eauto using
      Forall_impl, ctree_flatten_valid, pbit_valid_sep_valid. }
  rewrite ctree_flatten_union, pbits_perm_union by done.
  by erewrite ctree_merge_union_of_val, PBits_BIndet_tag, ctree_merge_flatten
    by eauto using of_val_flatten_disjoint,
    pbits_valid_perm_valid, ctree_flatten_valid.
Qed.
End values.
