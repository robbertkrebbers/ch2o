(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export values memory_trees_separation.

Section values.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ : type Ti.
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types w : mtree Ti.
Implicit Types v : val Ti.
Implicit Types vs : list (val Ti).

Hint Resolve Forall_take Forall_drop Forall_app_2
  Forall_replicate Forall_resize.
Hint Immediate env_valid_lookup env_valid_lookup_lookup.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).
Local Arguments union _ _ !_ !_ /.

Ltac solve_length := repeat first
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite resize_length | rewrite fmap_length | rewrite replicate_length
  | erewrite ctree_flatten_length by eauto|erewrite val_flatten_length by eauto
  | rewrite zip_with_length | erewrite base_val_flatten_length by eauto
  | match goal with
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
      | H : Γ !! ?s = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s))
          by eauto using bit_size_of_union_lookup
      | H : Γ !! ?s = Some [?τ] |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s))
          by eauto using bit_size_of_union_singleton
      end
    end]; lia.
Hint Extern 0 (length _ = _) => solve_length.

Lemma to_val_subseteq Γ Γm w1 w2 τ :
  ✓ Γ → (Γ,Γm) ⊢ w1 : τ → w1 ⊆ w2 →
  ctree_Forall (not ∘ sep_unmapped) w1 → to_val Γ w1 = to_val Γ w2.
Proof.
  intros ? Hw1 Hw. revert w1 w2 Hw τ Hw1.
  refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _); simpl.
  * intros; by erewrite pbits_tag_subseteq by eauto.
  * intros τ ws1 ws2 _ IH τ' Hw1; apply (ctree_typed_inv_l _ _ _ _ _ Hw1);
      clear τ' Hw1; intros Hws1 _ ?; f_equal.
    induction IH; decompose_Forall_hyps; f_equal; eauto.
  * intros s wxbs1 wxbs2 _ IH _ τ' Hw1; apply (ctree_typed_inv_l _ _ _ _ _ Hw1);
      clear τ' Hw1; intros τs _ Hws1 _ _ _ ?; f_equal.
    revert τs Hws1; induction IH; intros; decompose_Forall_hyps; f_equal; eauto.
  * intros s i w1 w2 xbs1 xbs2 _ ? _ _ τ' Hw1;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1.
    intros; decompose_Forall_hyps; f_equal'; eauto.
  * intros; by erewrite pbits_tag_subseteq by eauto.
  * intros s i xs1 w2 xs2 _ Hxs _ _ τ' Hw1;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1.
    intros. assert (bit_size_of Γ (unionT s) ≠ 0)
      by eauto using bit_size_of_ne_0, TCompound_valid.
    destruct Hxs; decompose_Forall_hyps.
Qed.
Lemma of_val_disjoint Γ Γm w1 w2 v τ :
  ✓ Γ → (Γ,Γm) ⊢ w1 : τ → ctree_unshared w1 →
  ctree_Forall (not ∘ sep_unmapped) w1 → (Γ,Γm) ⊢ v : τ → w1 ⊥ w2 →
  of_val Γ (tagged_perm <$> ctree_flatten w1) v ⊥ w2.
Proof.
  intros. assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,Γm) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
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
Lemma of_val_union_help Γ Γm xs1 xs2 v τ :
  ✓ Γ → (Γ,Γm) ⊢ v : τ →
  Forall sep_valid xs1 → Forall (not ∘ sep_unmapped) xs1 →
  length xs1 = bit_size_of Γ τ → of_val Γ (xs1 ∪* xs2) v
  = ctree_merge true (∪) (of_val Γ xs1 v) (flip PBit BIndet <$> xs2).
Proof.
  intros HΓ Hv. revert v τ Hv xs1 xs2.
  refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using PBits_union.
  * intros vs τ Hvs IH _ xs1 xs2 Hxs1 Hxs1'. rewrite bit_size_of_array.
    intros Hlen; f_equal. revert xs1 xs2 Hxs1 Hxs1' Hlen.
    induction IH; intros; decompose_Forall_hyps; simplify_type_equality; auto.
    erewrite zip_with_take, zip_with_drop, <-fmap_take, <-fmap_drop,
      ctree_flatten_length by eauto using of_val_typed. f_equal; auto.
  * intros s vs τs Hs Hvs IH xs1 xs2 Hxs1 Hxs1'.
    erewrite bit_size_of_struct by eauto; intros Hlen; f_equal.
    unfold field_bit_padding; erewrite fmap_type_of by eauto.
    clear Hs. revert vs xs1 xs2 Hvs IH Hxs1 Hxs1' Hlen.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps; simplify_type_equality; auto.
    erewrite !zip_with_drop, !zip_with_take, <-!fmap_drop, <-!fmap_take,
      ctree_flatten_length, fmap_length, take_length, drop_length,
      Min.min_l, PBits_BIndet_union by (eauto using of_val_typed; lia);
      repeat f_equal; eauto 6.
  * intros s i τs v τ ??? IH xs1 xs2 ???; simplify_type_equality'.
    by erewrite zip_with_take, zip_with_drop, <-fmap_take, <-fmap_drop, IH,
      ctree_flatten_length, PBits_BIndet_union by eauto using of_val_typed.
  * intros; f_equal; auto using PBits_union.
Qed.
Lemma of_val_union Γ Γm w1 w2 v τ :
  ✓ Γ → (Γ,Γm) ⊢ w1 : τ → ctree_unshared w1 →
  ctree_Forall (not ∘ sep_unmapped) w1 → (Γ,Γm) ⊢ v : τ → w1 ⊥ w2 →
  of_val Γ (tagged_perm <$> ctree_flatten (w1 ∪ w2)) v
  = of_val Γ (tagged_perm <$> ctree_flatten w1) v ∪ w2.
Proof.
  intros. assert (ctree_unmapped w2).
  { eapply seps_unshared_unmapped; eauto using @ctree_flatten_disjoint. }
  assert (Forall (not ∘ sep_unmapped) (tagged_perm <$> ctree_flatten w1)).
  { apply pbits_perm_mapped; eauto using
      Forall_impl, ctree_flatten_valid, pbit_valid_sep_valid. }
  rewrite ctree_flatten_union, pbits_perm_union by done.
  by erewrite of_val_union_help, PBits_BIndet_tag, ctree_merge_flatten
    by eauto using of_val_disjoint, pbits_valid_perm_valid, ctree_flatten_valid.
Qed.
End values.