(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_trees permission_bits_refine.
Local Open Scope ctype_scope.

Inductive ctree_refine' `{Env Ti} (Γ : env Ti) (α : bool) (f : meminj Ti)
     (Γm1 Γm2 : memenv Ti) : mtree Ti → mtree Ti → type Ti → Prop :=
  | MBase_refine τb xbs1 xbs2 :
     ✓{Γ} τb → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     length xbs1 = bit_size_of Γ (baseT τb) →
     ctree_refine' Γ α f Γm1 Γm2 (MBase τb xbs1) (MBase τb xbs2) (baseT τb)
  | MArray_refine τ n ws1 ws2 :
     n = length ws1 →
     Forall2 (λ w1 w2, ctree_refine' Γ α f Γm1 Γm2 w1 w2 τ) ws1 ws2 →
     n ≠ 0 → ctree_refine' Γ α f Γm1 Γm2 (MArray τ ws1) (MArray τ ws2) (τ.[n])
  | MStruct_refine s wxbss1 wxbss2 τs :
     Γ !! s = Some τs → Forall3 (λ wxbs1 wxbs2 τ,
       ctree_refine' Γ α f Γm1 Γm2 (wxbs1.1) (wxbs2.1) τ) wxbss1 wxbss2 τs →
     wxbss1 ⊑{Γ,α,f@Γm1↦Γm2}2** wxbss2 →
     Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss1 →
     Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss2 →
     length ∘ snd <$> wxbss1 = field_bit_padding Γ τs →
     ctree_refine' Γ α f Γm1 Γm2
       (MStruct s wxbss1) (MStruct s wxbss2) (structT s)
  | MUnion_refine s τs i w1 w2 xbs1 xbs2 τ :
     Γ !! s = Some τs → τs !! i = Some τ →
     ctree_refine' Γ α f Γm1 Γm2 w1 w2 τ → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     pbit_indetify <$> xbs1 = xbs1 → pbit_indetify <$> xbs2 = xbs2 →
     bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
     ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
     ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xbs2) →
     ctree_refine' Γ α f Γm1 Γm2
       (MUnion s i w1 xbs1) (MUnion s i w2 xbs2) (unionT s)
  | MUnionAll_refine s τs xbs1 xbs2 :
     Γ !! s = Some τs → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     length xbs1 = bit_size_of Γ (unionT s) →
     ctree_refine' Γ α f Γm1 Γm2
       (MUnionAll s xbs1) (MUnionAll s xbs2) (unionT s)
  | MUnion_MUnionAll_refine s τs i w1 xbs1 xbs2 τ :
     α → Γ !! s = Some τs → τs !! i = Some τ →
     ctree_flatten w1 ++ xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     pbit_indetify <$> xbs1 = xbs1 →
     (Γ,Γm1) ⊢ w1 : τ → Forall sep_unshared xbs2 →
     bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
     ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
     ctree_refine' Γ α f Γm1 Γm2
       (MUnion s i w1 xbs1) (MUnionAll s xbs2) (unionT s).
Instance ctree_refine `{Env Ti} :
  RefineT Ti (env Ti) (type Ti) (mtree Ti) := ctree_refine'.

Lemma ctree_refine_inv_l `{Env Ti} (Γ : env Ti) (α : bool)
    (f : meminj Ti) (Γm1 Γm2 : memenv Ti) (P : mtree Ti → Prop) w1 w2 τ :
  w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ →
  match w1 with
  | MBase τb xbs1 =>
     (∀ xbs2, xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → P (MBase τb xbs2)) → P w2
  | MArray τ ws1 =>
     (∀ ws2, ws1 ⊑{Γ,α,f@Γm1↦Γm2}* ws2 : τ → P (MArray τ ws2)) → P w2
  | MStruct s wxbss1 => (∀ τs wxbss2,
     Γ !! s = Some τs → wxbss1 ⊑{Γ,α,f@Γm1↦Γm2}1* wxbss2 :* τs →
     Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss1 →
     Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss2 →
     wxbss1 ⊑{Γ,α,f@Γm1↦Γm2}2** wxbss2 → P (MStruct s wxbss2)) → P w2
  | MUnion s i w1 xbs1 =>
     (∀ τs w2 xbs2 τ,
       Γ !! s = Some τs → τs !! i = Some τ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ →
       xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → pbit_indetify <$> xbs1 = xbs1 →
       pbit_indetify <$> xbs2 = xbs2 → P (MUnion s i w2 xbs2)) →
     (∀ τs τ xbs2,
       α → Γ !! s = Some τs → τs !! i = Some τ →
       ctree_flatten w1 ++ xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
       Forall sep_unshared xbs2 → P (MUnionAll s xbs2)) → P w2
  | MUnionAll s xbs1 =>
     (∀ xbs2, xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → P (MUnionAll s xbs2)) → P w2
  end.
Proof. destruct 1; eauto. Qed.
Section ctree_refine_ind.
  Context `{Env Ti} (Γ : env Ti) (α : bool) (f : meminj Ti).
  Context (Γm1 Γm2 : memenv Ti) (P : mtree Ti → mtree Ti → type Ti → Prop).
  Context (Pbase : ∀ τb xbs1 xbs2,
    ✓{Γ} τb → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
    length xbs1 = bit_size_of Γ (baseT τb) →
    P (MBase τb xbs1) (MBase τb xbs2) (baseT τb)).
  Context (Parray : ∀ τ n ws1 ws2,
    n = length ws1 → ws1 ⊑{Γ,α,f@Γm1↦Γm2}* ws2 : τ →
    Forall2 (λ w1 w2, P w1 w2 τ) ws1 ws2 →
    n ≠ 0 → P (MArray τ ws1) (MArray τ ws2) (τ.[n])).
  Context (Pstruct : ∀ s τs wxbss1 wxbss2,
    Γ !! s = Some τs → wxbss1 ⊑{Γ,α,f@Γm1↦Γm2}1* wxbss2 :* τs →
    Forall3 (λ wxbs1 wxbs2 τ, P (wxbs1.1) (wxbs2.1) τ) wxbss1 wxbss2 τs →
    wxbss1 ⊑{Γ,α,f@Γm1↦Γm2}2** wxbss2 →
    Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss1 →
    Forall (λ wxbs, pbit_indetify <$> wxbs.2 = wxbs.2) wxbss2 →
    length ∘ snd <$> wxbss1 = field_bit_padding Γ τs →
    P (MStruct s wxbss1) (MStruct s wxbss2) (structT s)).
  Context (Punion : ∀ s τs i w1 w2 xbs1 xbs2 τ,
    Γ !! s = Some τs → τs !! i = Some τ →
    w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → P w1 w2 τ → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
    pbit_indetify <$> xbs1 = xbs1 → pbit_indetify <$> xbs2 = xbs2 →
    bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
    ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
    ¬(ctree_unmapped w2 ∧ Forall sep_unmapped xbs2) →
    P (MUnion s i w1 xbs1) (MUnion s i w2 xbs2) (unionT s)).
  Context (Punion_all : ∀ s τs xbs1 xbs2,
    Γ !! s = Some τs → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
    length xbs1 = bit_size_of Γ (unionT s) →
    P (MUnionAll s xbs1) (MUnionAll s xbs2) (unionT s)).
  Context (Punion_union_all : ∀ s i τs w1 xbs1 xbs2 τ,
    α → Γ !! s = Some τs → τs !! i = Some τ →
    ctree_flatten w1 ++ xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
    pbit_indetify <$> xbs1 = xbs1 →
    (Γ,Γm1) ⊢ w1 : τ → Forall sep_unshared xbs2 →
    bit_size_of Γ (unionT s) = bit_size_of Γ τ + length xbs1 →
    ¬(ctree_unmapped w1 ∧ Forall sep_unmapped xbs1) →
    P (MUnion s i w1 xbs1) (MUnionAll s xbs2) (unionT s)).
  Definition ctree_refine_ind: ∀ w1 w2 τ,
    ctree_refine' Γ α f Γm1 Γm2 w1 w2 τ → P w1 w2 τ.
  Proof. fix 4; destruct 1; eauto using Forall2_impl, Forall3_impl. Qed.
End ctree_refine_ind.

Section memory_trees.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types α : bool.
Implicit Types Γm : memenv Ti.
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
Implicit Types f : meminj Ti.

Hint Resolve Forall_take Forall_drop Forall_app_2 Forall_replicate.
Hint Resolve Forall2_take Forall2_drop Forall2_app.
Hint Immediate env_valid_lookup env_valid_lookup_lookup.

Ltac solve_length := simplify_equality'; repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | rewrite type_mask_length by eauto | rewrite replicate_length
  | rewrite bit_size_of_int | rewrite int_width_char | rewrite resize_length
  | erewrite sublist_lookup_length by eauto
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

Inductive ctree_leaf_refine Γ α f Γm1 Γm2 : relation (mtree Ti) :=
  | MBase_shape τb xbs1 xbs2 :
     xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     ctree_leaf_refine Γ α f Γm1 Γm2 (MBase τb xbs1) (MBase τb xbs2)
  | MArray_shape τ ws1 ws2 :
     Forall2 (ctree_leaf_refine Γ α f Γm1 Γm2) ws1 ws2 →
     ctree_leaf_refine Γ α f Γm1 Γm2 (MArray τ ws1) (MArray τ ws2)
  | MStruct_shape s wxbss1 wxbss2 :
     Forall2 (λ wxbs1 wxbs2,
       ctree_leaf_refine Γ α f Γm1 Γm2 (wxbs1.1) (wxbs2.1)) wxbss1 wxbss2 →
     wxbss1 ⊑{Γ,α,f@Γm1↦Γm2}2** wxbss2 →
     ctree_leaf_refine Γ α f Γm1 Γm2 (MStruct s wxbss1) (MStruct s wxbss2)
  | MUnion_shape s i w1 w2 xbs1 xbs2 :
     ctree_leaf_refine Γ α f Γm1 Γm2 w1 w2 → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     ctree_leaf_refine Γ α f Γm1 Γm2 (MUnion s i w1 xbs1) (MUnion s i w2 xbs2)
  | MUnionAll_shape s xbs1 xbs2 :
     xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     ctree_leaf_refine Γ α f Γm1 Γm2 (MUnionAll s xbs1) (MUnionAll s xbs2)
  | MUnion_MUnionAll_shape s i w1 xbs1 xbs2 :
     α → ctree_flatten w1 ++ xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
     Forall sep_unshared xbs2 →
     ctree_leaf_refine Γ α f Γm1 Γm2 (MUnion s i w1 xbs1) (MUnionAll s xbs2).

Section ctree_leaf_refine.
  Context Γ α f Γm1 Γm2 (P : mtree Ti → mtree Ti → Prop).
  Context (Pbase : ∀ τb xbs1 xbs2,
    xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → P (MBase τb xbs1) (MBase τb xbs2)).
  Context (Parray : ∀ τ ws1 ws2,
    Forall2 (ctree_leaf_refine Γ α f Γm1 Γm2) ws1 ws2 → Forall2 P ws1 ws2 →
    P (MArray τ ws1) (MArray τ ws2)).
  Context (Pstruct : ∀ s wxbss1 wxbss2,
    Forall2 (λ wxbs1 wxbs2,
      ctree_leaf_refine Γ α f Γm1 Γm2 (wxbs1.1) (wxbs2.1)) wxbss1 wxbss2 →
    Forall2 (λ wxbs1 wxbs2, P (wxbs1.1) (wxbs2.1)) wxbss1 wxbss2 →
    wxbss1 ⊑{Γ,α,f@Γm1↦Γm2}2** wxbss2 → P (MStruct s wxbss1) (MStruct s wxbss2)).
  Context (Punion : ∀ s i w1 w2 xbs1 xbs2,
    ctree_leaf_refine Γ α f Γm1 Γm2 w1 w2 → P w1 w2 →
    xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → P (MUnion s i w1 xbs1) (MUnion s i w2 xbs2)).
  Context (Munionall : ∀ s xbs1 xbs2,
    xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → P (MUnionAll s xbs1) (MUnionAll s xbs2)).
  Context (Munionall' : ∀ s i w1 xbs1 xbs2,
    α → ctree_flatten w1 ++ xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → 
    Forall sep_unshared xbs2 → P (MUnion s i w1 xbs1) (MUnionAll s xbs2)).
  Lemma ctree_leaf_refine_ind_alt :
     ∀ w1 w2, ctree_leaf_refine Γ α f Γm1 Γm2 w1 w2 → P w1 w2.
  Proof. fix 3; destruct 1; eauto using Forall2_impl. Qed.
End ctree_leaf_refine.

Lemma ctree_refine_leaf Γ α f Γm1 Γm2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → ctree_leaf_refine Γ α f Γm1 Γm2 w1 w2.
Proof.
  induction 1 as [| |?????? IH| | |] using @ctree_refine_ind; constructor; auto.
  elim IH; auto.
Qed.
Hint Immediate ctree_refine_leaf.
Lemma ctree_leaf_refine_refine Γ α f Γm1 Γm2 w1 w2 τ :
  ✓ Γ → ctree_leaf_refine Γ α f Γm1 Γm2 w1 w2 →
  (Γ,Γm1) ⊢ w1 : τ → (Γ,Γm2) ⊢ w2 : τ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ.
Proof.
  intros ? Hw. revert τ. revert w1 w2 Hw.
  refine (ctree_leaf_refine_ind_alt _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * intros τb xbs1 xbs2 τ ? Hw1 _; apply (ctree_typed_inv_l _ _ _ _ _ Hw1).
    by refine_constructor.
  * intros τ ws1 ws2 _ IH τ' Hw1; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1;
      intros Hws1 Hlen Hw2; apply (ctree_typed_inv _ _ _ _ _ Hw2); clear Hw2;
      intros _ _ Hws2 _; refine_constructor; eauto.
    clear Hlen. induction IH; decompose_Forall_hyps; auto.
  * intros s wxbss1 wxbss2 _ IH Hxbs τ' Hw1; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1;
      intros τs Hs Hws1 Hxbs1 Hindet1 Hlen Hw2;
      apply (ctree_typed_inv _ _ _ _ _ Hw2);
      clear Hw2; intros ? _ ? Hws2 Hxbs2 Hindet2 _; simplify_equality';
      refine_constructor; eauto.
    clear Hs Hxbs1 Hlen Hxbs2 Hindet1 Hindet2 Hxbs. revert τs Hws1 Hws2.
    induction IH; intros; decompose_Forall_hyps; constructor; auto.
  * intros s i w1 w2 xbs1 xbs2 _ ?? τ Hw1; pattern τ;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ Hw1;
      intros τs τ ??????? Hw2; apply (ctree_typed_inv _ _ _ _ _ Hw2);
      intros; decompose_Forall_hyps; refine_constructor; eauto.
  * intros s xbs1 xbs2 τ ? Hw1 _; apply (ctree_typed_inv_l _ _ _ _ _ Hw1).
    refine_constructor; eauto.
  * intros s i w1 xbs1 xbs2 ??? τ Hw1; pattern τ;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); intros ????????? Hw2;
      apply (ctree_typed_inv _ _ _ _ _ Hw2); intros; simplify_equality'.
    refine_constructor; eauto.
Qed.
Lemma ctree_flatten_leaf_refine Γ α f Γm1 Γm2 w1 w2 :
  ctree_leaf_refine Γ α f Γm1 Γm2 w1 w2 →
  ctree_flatten w1 ⊑{Γ,α,f@Γm1↦Γm2}* ctree_flatten w2.
Proof.
  revert w1 w2.
  refine (ctree_leaf_refine_ind_alt _ _ _ _ _ _ _ _ _ _ _ _); simpl; auto 2.
  * eauto using Forall2_bind.
  * intros s wxbss1 wxbss2 _ IH ?. induction IH; decompose_Forall_hyps; auto.
Qed.
Lemma ctree_unflatten_leaf_refine Γ α f Γm1 Γm2 τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 →
  ctree_leaf_refine Γ α f Γm1 Γm2
    (ctree_unflatten Γ τ xbs1) (ctree_unflatten Γ τ xbs2).
Proof.
  intros HΓ Hτ. revert τ Hτ xbs1 xbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite !ctree_unflatten_base. by constructor.
  * intros τ n _ IH _ xbs1 xbs2 Hxbs. rewrite !ctree_unflatten_array.
    constructor. revert xbs1 xbs2 Hxbs. induction n; simpl; auto.
  * intros [] s τs Hs _ IH _ xbs1 xbs2 Hxbs; erewrite
      !ctree_unflatten_compound by eauto; simpl; clear Hs; [|by constructor].
    unfold struct_unflatten; constructor.
    + revert xbs1 xbs2 Hxbs. induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps; constructor; simpl; auto.
    + revert xbs1 xbs2 Hxbs. induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps; constructor; simpl;
        auto using pbits_indetify_refine.
Qed.
Lemma ctree_unflatten_refine Γ α f Γm1 Γm2 τ xbs1 xbs2 :
  ✓ Γ → ✓{Γ} τ → xbs1 ⊑{Γ,α,f@Γm1↦Γm2}* xbs2 → length xbs1 = bit_size_of Γ τ →
  ctree_unflatten Γ τ xbs1 ⊑{Γ,α,f@Γm1↦Γm2} ctree_unflatten Γ τ xbs2 : τ.
Proof.
  intros; apply ctree_leaf_refine_refine; eauto using ctree_unflatten_typed,
    pbits_refine_valid_l, pbits_refine_valid_r, ctree_unflatten_leaf_refine.
Qed.
Lemma ctree_flatten_refine Γ α f Γm1 Γm2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ →
  ctree_flatten w1 ⊑{Γ,α,f@Γm1↦Γm2}* ctree_flatten w2.
Proof. eauto using ctree_flatten_leaf_refine. Qed.
Lemma ctree_refine_typed_l Γ α f Γm1 Γm2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → (Γ,Γm1) ⊢ w1 : τ.
Proof.
  intros ?. revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _).
  * typed_constructor; eauto using pbits_refine_valid_l.
  * intros τ n ws1 ws2 Hn _ IH ?; typed_constructor; auto.
    clear Hn. induction IH; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH Hxbs Hindet _ Hlen.
    typed_constructor; eauto; clear Hs Hlen; induction IH;
      decompose_Forall_hyps; eauto using pbits_refine_valid_l.
  * typed_constructor; eauto using pbits_refine_valid_l.
  * intros; typed_constructor; eauto using pbits_refine_valid_l.
  * intros; decompose_Forall_hyps; typed_constructor;
      eauto using pbits_refine_valid_l.
Qed.
Lemma ctree_refine_typed_r Γ α f Γm1 Γm2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → (Γ,Γm2) ⊢ w2 : τ.
Proof.
  intros ?. revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _).
  * typed_constructor; eauto using Forall2_length_l, pbits_refine_valid_r.
  * intros τ n ws1 ws2 -> _ IH Hn;
      typed_constructor; eauto using Forall2_length.
    clear Hn. induction IH; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH Hxbs _ ? Hlen. typed_constructor; eauto.
    + elim IH; eauto.
    + elim Hxbs; eauto using pbits_refine_valid_r.
    + rewrite <-Hlen; symmetry.
      elim Hxbs; intros; f_equal'; eauto using Forall2_length.
  * intros; typed_constructor; eauto using pbits_refine_valid_r; solve_length.
  * typed_constructor; eauto using Forall2_length_l, pbits_refine_valid_r.
  * typed_constructor; eauto using Forall2_length_l, pbits_refine_valid_r.
Qed.
Hint Immediate ctree_refine_typed_l ctree_refine_typed_r.
Lemma ctree_refine_type_valid_l Γ α f Γm1 Γm2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → ✓{Γ} τ.
Proof. eauto using ctree_typed_type_valid. Qed.
Lemma ctree_refine_type_of_l Γ α f Γm1 Γm2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → type_of w1 = τ.
Proof. destruct 1 using @ctree_refine_ind; simpl; auto. Qed.
Lemma ctree_refine_type_of_r Γ α f Γm1 Γm2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → type_of w2 = τ.
Proof. destruct 1; f_equal'; eauto using Forall2_length_l. Qed.
Lemma ctree_refine_id Γ α Γm w τ : (Γ,Γm) ⊢ w : τ → w ⊑{Γ,α@Γm} w : τ.
Proof.
  revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _);
     try by (intros; refine_constructor; eauto using pbits_refine_id).
  * intros ws τ _ IH Hlen; refine_constructor; auto. elim IH; auto.
  * intros s wxbss τs ? _ IH Hwxbss ??; refine_constructor; eauto.
    + elim IH; constructor; eauto.
    + elim Hwxbss; constructor; eauto using pbits_refine_id.
Qed.
Lemma ctree_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 w1 w2 w3 τ :
  ✓ Γ → w1 ⊑{Γ,α1,f1@Γm1↦Γm2} w2 : τ → w2 ⊑{Γ,α2,f2@Γm2↦Γm3} w3 : τ →
  w1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} w3 : τ.
Proof.
  intros ? Hw Hw3. apply ctree_leaf_refine_refine; eauto.
  revert w1 w2 τ Hw w3 Hw3.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * intros τb xbs1 xbs2 ??? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3).
    constructor; eauto using pbits_refine_compose.
  * intros τ n ws1 ws2 -> _ IH _ w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    intros ws3 Hws3; constructor. revert ws3 Hws3.
    induction IH; intros; decompose_Forall_hyps; constructor; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH Hxbs _ _ _ w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    intros ? wxbss3 ? Hws3 _ _ Hxbs3; simplify_equality; constructor.
    + clear Hs Hxbs3 Hxbs. revert wxbss3 Hws3.
      induction IH; inversion_clear 1; constructor; eauto.
    + clear Hs IH Hws3. revert wxbss3 Hxbs3. induction Hxbs; intros;
        decompose_Forall_hyps; constructor; eauto using pbits_refine_compose.
  * intros s τs i w1 w2 xbs1 xbs2 τ Hs Hτs ? IH ?????? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3;
      intros; decompose_Forall_hyps;
      constructor; eauto using ctree_flatten_refine, pbits_refine_compose.
  * intros s τs xbs1 xbs2 Hs ?? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3).
    constructor; eauto using pbits_refine_compose.
  * intros s i τs w1 xbs1 xbs2 τ ????????? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    constructor; eauto using pbits_refine_compose, pbits_refine_unshared.
Qed.
Lemma ctree_refine_inverse Γ f Γm1 Γm2 w1 w2 τ :
  w1 ⊑{Γ,false,f@Γm1↦Γm2} w2 : τ →
  w2 ⊑{Γ,false,meminj_inverse f@Γm2↦Γm1} w1 : τ.
Proof.
  revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * refine_constructor; eauto using pbits_refine_inverse.
  * refine_constructor; auto. by apply Forall2_flip.
  * intros ?????? IH Hxbss ?? Hlen; refine_constructor; eauto.
    + elim IH; constructor; eauto.
    + elim Hxbss; eauto using pbits_refine_inverse.
    + rewrite <-Hlen. elim Hxbss; intros; f_equal'; auto.
  * refine_constructor; eauto using pbits_refine_inverse; solve_length.
  * refine_constructor; eauto using pbits_refine_inverse.
  * done.
Qed.
Lemma ctree_refine_weaken Γ Γ' α α' f f' Γm1 Γm2 Γm1' Γm2' w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → Γ ⊆ Γ' → (α → α') →
  Γm1' ⊑{Γ',α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → w1 ⊑{Γ',α',f'@Γm1'↦Γm2'} w2 : τ.
Proof.
  intros ? Hw; intros. induction Hw using @ctree_refine_ind;
    refine_constructor; try (eapply Forall2_impl; [eassumption|]); simpl;
    eauto using base_type_valid_weaken,
      @lookup_weaken, pbit_refine_weaken, ctree_typed_weaken;
    erewrite <-?(bit_size_of_weaken Γ Γ'), <-?(field_bit_padding_weaken Γ Γ')
      by eauto using TBase_valid, TCompound_valid; auto.
  simpl; eauto using Forall2_impl, pbit_refine_weaken.
Qed.
Lemma union_free_refine Γ α f Γm1 Γm2 w1 w2 τ :
  union_free w1 → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → union_free w2.
Proof.
  intros Hw1 Hw. revert w1 w2 τ Hw Hw1.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl; try by constructor.
  * intros τ n ws1 ws2 _ _ IH _; inversion_clear 1; constructor.
    induction IH; decompose_Forall_hyps; auto.
  * intros s τs wxbss1 wxnss2 _ _ IH _ _ _ _; inversion_clear 1; constructor.
    induction IH; decompose_Forall_hyps; auto.
  * inversion_clear 11.
Qed.
Lemma union_reset_above Γ f Γm1 Γm2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,true,f@Γm1↦Γm2} w2 : τ →
  ctree_unshared w2 → w1 ⊑{Γ,true,f@Γm1↦Γm2} union_reset w2 : τ.
Proof.
  intros HΓ. revert w1 w2 τ.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * by refine_constructor.
  * intros τ n ws1 ws2 Hn _ IH ??. refine_constructor; auto.
    clear Hn. induction IH; decompose_Forall_hyps; auto.
  * intros s τs wxbss1 wxbss2 Hs _ IH ? Hindet1 Hindet2 Hlen ?;
      refine_constructor; eauto; clear Hs Hlen;
      induction IH; decompose_Forall_hyps; constructor; auto.
  * refine_constructor; eauto using ctree_flatten_refine.
  * refine_constructor; eauto.
  * refine_constructor; eauto.
Qed.
Lemma union_reset_refine Γ α f Γm1 Γm2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ →
  union_reset w1 ⊑{Γ,α,f@Γm1↦Γm2} union_reset w2 : τ.
Proof.
  intros ? Hw. apply ctree_leaf_refine_refine; eauto using union_reset_typed.
  revert w1 w2 τ Hw. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _);
    simpl; try by (intros; constructor; eauto 1).
  * intros τ n ws1 ws2 _ _ IH _; constructor; auto. elim IH; constructor; eauto.
  * intros s τs wxbss1 wxbss2 ? _ IH Hxbs _ _ _. constructor; eauto.
    + elim IH; constructor; eauto.
    + elim Hxbs; constructor; eauto.
  * constructor; eauto using ctree_flatten_refine.
Qed.
Lemma ctree_flatten_unflatten_refine Γ f Γm1 Γm2 w xbs τ :
  ✓ Γ → (Γ,Γm1) ⊢ w : τ → Forall sep_unshared xbs →
  ctree_flatten w ⊑{Γ,true,f@Γm1↦Γm2}* xbs →
  w ⊑{Γ,true,f@Γm1↦Γm2} ctree_unflatten Γ τ xbs : τ.
Proof.
  intros. rewrite <-(right_id_L _ (◎) f), <-(orb_diag true).
  apply ctree_refine_compose
    with Γm1 (ctree_unflatten Γ τ (ctree_flatten w)); auto.
  { erewrite ctree_unflatten_flatten by eauto.
    apply union_reset_above; eauto using ctree_refine_id.
    eauto using pbits_refine_shared. }
  apply ctree_unflatten_refine; eauto using ctree_typed_type_valid.
Qed.
Lemma ctree_lookup_seg_refine Γ α f Γm1 Γm2 w1 w2 τ rs w3 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → w1 !!{Γ} rs = Some w3 →
  ∃ w4, w2 !!{Γ} rs = Some w4 ∧ w3 ⊑{Γ,α,f@Γm1↦Γm2} w4 : type_of w3.
Proof.
  intros ? Hw Hrs.
  cut (∃ w4, w2 !!{Γ} rs = Some w4 ∧ ctree_leaf_refine Γ α f Γm1 Γm2 w3 w4).
  { intros (w4&?&?); exists w4; split; auto.
    destruct (ctree_lookup_seg_Some Γ Γm1 w1 τ rs w3) as (?&?&?),
      (ctree_lookup_seg_Some Γ Γm2 w2 τ rs w4) as (?&?&?); eauto.
    simplify_type_equality; eauto using ctree_leaf_refine_refine. }
  destruct Hw, rs;
    change (ctree_refine' Γ α f Γm1 Γm2) with (refineT Γ α f Γm1 Γm2) in *;
    pattern w3; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); simpl; clear Hrs.
  * intros; simplify_option_equality; decompose_Forall_hyps; eauto.
  * intros; repeat (simplify_option_equality || decompose_Forall_hyps); eauto.
  * intros; simplify_option_equality; eauto.
  * intros; simplify_option_equality by eauto using
      pbits_refine_unshared, ctree_flatten_refine.
    eexists; split; eauto. eapply ctree_refine_leaf;
      eauto using ctree_unflatten_refine, ctree_flatten_refine.
  * intros; simplify_option_equality by eauto using pbits_refine_unshared.
    eexists; eauto using ctree_refine_leaf, ctree_unflatten_refine.
  * intros; destruct α; try done;
      simplify_option_equality; decompose_Forall_hyps.
    rewrite take_app_alt by (by erewrite <-Forall2_length by eauto).
    eexists; eauto using ctree_refine_leaf, ctree_flatten_unflatten_refine.
  * intros; simplify_option_equality.
    eexists; split; eauto. eapply ctree_refine_leaf;
      eauto using ctree_unflatten_refine, ctree_flatten_refine.
Qed.
Lemma ctree_lookup_refine Γ α f Γm1 Γm2 w1 w2 τ r w3 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → w1 !!{Γ} r = Some w3 →
  ∃ w4, w2 !!{Γ} r = Some w4 ∧ w3 ⊑{Γ,α,f@Γm1↦Γm2} w4 : type_of w3.
Proof.
  intros HΓ. revert w1 w2 τ. induction r as [|rs r IH] using rev_ind; simpl.
  { intros. rewrite ctree_lookup_nil. simplify_type_equality.
    erewrite ctree_refine_type_of_l by eauto; eauto. }
  intros w1 w2. rewrite !ctree_lookup_snoc. intros. simplify_option_equality.
  edestruct (ctree_lookup_seg_refine Γ α f Γm1 Γm2 w1 w2 τ rs) as (?&?&?);
    simplify_option_equality; eauto.
Qed.
Lemma ctree_lookup_refine_both Γ α f Γm1 Γm2 w1 w2 τ r w3 w4 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → w1 !!{Γ} r = Some w3 →
  w2 !!{Γ} r = Some w4 → w3 ⊑{Γ,α,f@Γm1↦Γm2} w4 : type_of w3.
Proof.
  intros. destruct (ctree_lookup_refine Γ α f Γm1 Γm2 w1 w2 τ r w3)
    as (?&?&?); simplify_equality'; auto.
Qed.
Lemma ctree_alter_seg_refine Γ α f Γm1 Γm2 g1 g2 w1 w2 τ rs w3 w4 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ →
  w1 !!{Γ} rs = Some w3 → w2 !!{Γ} rs = Some w4 →
  g1 w3 ⊑{Γ,α,f@Γm1↦Γm2} g2 w4 : type_of w3 → ¬ctree_unmapped (g1 w3) →
  ctree_alter_seg Γ g1 rs w1 ⊑{Γ,α,f@Γm1↦Γm2} ctree_alter_seg Γ g2 rs w2 : τ.
Proof.
  intros ? Hw Hw3 Hw4 Hgw. cut (ctree_leaf_refine Γ α f Γm1 Γm2
    (ctree_alter_seg Γ g1 rs w1) (ctree_alter_seg Γ g2 rs w2)).
  { intros. assert ((Γ, Γm2) ⊢ g2 w4 : type_of w4).
    { destruct (ctree_lookup_seg_Some Γ Γm1 w1 τ rs w3) as (τ'&?&?),
        (ctree_lookup_seg_Some Γ Γm2 w2 τ rs w4) as (?&?&?); eauto.
      simplify_type_equality'; eauto. }
    assert (¬ctree_unmapped (g2 w4))
      by eauto using pbits_refine_mapped, ctree_flatten_refine.
    apply ctree_leaf_refine_refine; eauto using ctree_alter_seg_typed. }
  revert Hgw.
  destruct Hw as [|τ n ws1 ws2 ? Hws|s wxbss1 wxbss2?? Hws| | |], rs; simpl;
    change (ctree_refine' Γ α f Γm1 Γm2) with (refineT Γ α f Γm1 Γm2) in *;
    pattern w3; apply (ctree_lookup_seg_inv _ _ _ _ _ Hw3); simpl; clear Hw3;
    pattern w4; apply (ctree_lookup_seg_inv _ _ _ _ _ Hw4); simpl; clear Hw4;
    intros; simplify_option_equality; decompose_Forall_hyps.
  * constructor. apply Forall2_alter; [elim Hws; eauto|].
    intros; simplify_equality; eauto.
  * constructor; [|apply Forall2_alter; auto].
    apply Forall2_alter; [elim Hws; eauto|].
    intros [??] [??] ???; simplify_equality; eauto.
  * constructor; eauto.
  * constructor; eauto using ctree_flatten_refine, pbits_indetify_refine.
  * constructor; eauto using pbits_indetify_refine.
  * constructor; eauto using pbits_indetify_idempotent.
    rewrite drop_app_alt by (by erewrite <-Forall2_length by eauto); eauto.
    match goal with H : pbit_indetify <$> _ = _ |- _ => rewrite <-H end.
    eauto using pbits_indetify_refine.
  * constructor; eauto using pbits_indetify_refine.
Qed.
Lemma ctree_alter_refine Γ α f Γm1 Γm2 g1 g2 w1 w2 τ r w3 w4 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ →
  w1 !!{Γ} r = Some w3 → w2 !!{Γ} r = Some w4 →
  g1 w3 ⊑{Γ,α,f@Γm1↦Γm2} g2 w4 : type_of w3 → ¬ctree_unmapped (g1 w3) →
  ctree_alter Γ g1 r w1 ⊑{Γ,α,f@Γm1↦Γm2} ctree_alter Γ g2 r w2 : τ.
Proof.
  intros ?. revert g1 g2 w1 w2 τ.
  induction r as [|rs r IH] using rev_ind; simpl; intros g1 g2 w1 w2 τ.
  { rewrite !ctree_lookup_nil; intros ???; simplify_equality.
    erewrite ctree_refine_type_of_l by eauto; eauto. }
  rewrite !ctree_lookup_snoc, !ctree_alter_snoc; intros.
  destruct (w1 !!{Γ} rs) as [w1'|] eqn:?; simplify_equality'.
  destruct (w2 !!{Γ} rs) as [w2'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_seg_refine Γ α f Γm1 Γm2 w1 w2 τ rs w1')
    as (?&?&?); auto; simplify_equality'.
  eapply ctree_alter_seg_refine; eauto using ctree_alter_lookup_Forall.
Qed.
Lemma ctree_lookup_byte_refine Γ α f Γm1 Γm2 w1 w2 τ i c1 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → w1 !!{Γ} i = Some c1 →
  ∃ c2, w2 !!{Γ} i = Some c2 ∧ c1 ⊑{Γ,α,f@Γm1↦Γm2} c2 : ucharT.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w1))
    as [xbs1|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_l (refine Γ α f Γm1 Γm2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (xbs2&?&?);
    eauto using ctree_flatten_refine.
  exists (ctree_unflatten Γ ucharT xbs2); simplify_option_equality; split; auto.
  apply ctree_unflatten_refine; auto using TBase_valid, TInt_valid.
Qed.
Lemma ctree_lookup_byte_refine_inv Γ α f Γm1 Γm2 w1 w2 τ i c2 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → w2 !!{Γ} i = Some c2 →
  ∃ c1, w1 !!{Γ} i = Some c1 ∧ c1 ⊑{Γ,α,f@Γm1↦Γm2} c2 : ucharT.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w2))
    as [xbs2|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_r (refine Γ α f Γm1 Γm2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs2) as (xbs1&?&?);
    eauto using ctree_flatten_refine.
  exists (ctree_unflatten Γ ucharT xbs1); simplify_option_equality; split; auto.
  apply ctree_unflatten_refine; auto using TBase_valid, TInt_valid.
Qed.
Lemma ctree_alter_byte_refine Γ α f Γm1 Γm2 g1 g2 w1 w2 τ i c1 c2 :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ → w1 !!{Γ} i = Some c1 → w2 !!{Γ} i = Some c2 →
  g1 c1 ⊑{Γ,α,f@Γm1↦Γm2} g2 c2 : ucharT →
  ctree_alter_byte Γ g1 i w1 ⊑{Γ,α,f@Γm1↦Γm2} ctree_alter_byte Γ g2 i w2 : τ.
Proof.
  unfold lookupE, ctree_lookup_byte, ctree_alter_byte. intros.
  set (G1 := ctree_flatten ∘ g1 ∘ ctree_unflatten Γ ucharT).
  set (G2 := ctree_flatten ∘ g2 ∘ ctree_unflatten Γ ucharT).
  assert ((Γ,Γm1) ⊢ w1 : τ) by eauto; assert ((Γ,Γm2) ⊢ w2 : τ) by eauto.
  destruct (sublist_lookup _ _ (ctree_flatten w1)) as [xbs1|] eqn:?,
    (sublist_lookup _ _ (ctree_flatten w2)) as [xbs2|] eqn:?;
    simplify_type_equality'.
  destruct (Forall2_sublist_lookup_l (refine Γ α f Γm1 Γm2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits xbs1) as (?&?&?);
    eauto 2 using ctree_flatten_refine; simplify_option_equality.
  assert (length (G1 xbs1) = char_bits).
  { unfold G1; simpl. eauto using ctree_refine_typed_l. }
  apply ctree_unflatten_refine; eauto 2 using ctree_typed_type_valid.
  eapply Forall2_sublist_alter; eauto 2 using ctree_flatten_refine.
  apply ctree_flatten_refine with ucharT; simplify_option_equality; auto.
Qed.
Lemma ctree_map_refine Γ α f Γm1 Γm2 h1 h2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Γm1↦Γm2} w2 : τ →
  h1 <$> ctree_flatten w1 ⊑{Γ,α,f@Γm1↦Γm2}* h2 <$> ctree_flatten w2 →
  (∀ xb, sep_unshared xb → sep_unshared (h2 xb)) →
  (∀ xb, pbit_indetify xb = xb → pbit_indetify (h1 xb) = h1 xb) →
  (∀ xb, pbit_indetify xb = xb → pbit_indetify (h2 xb) = h2 xb) →
  ctree_map h1 w1 ⊑{Γ,α,f@Γm1↦Γm2} ctree_map h2 w2 : τ.
Proof.
  intros ? Hw Hw' ? Hh.
  assert (∀ xbs, Forall sep_unshared xbs → Forall sep_unshared (h2 <$> xbs)).
  { induction 1; simpl; auto. }
  cut (ctree_leaf_refine Γ α f Γm1 Γm2 (ctree_map h1 w1) (ctree_map h2 w2)).
  { intros; apply ctree_leaf_refine_refine; eauto using
      ctree_map_typed, pbits_refine_valid_l, pbits_refine_valid_r. }
  clear Hh. revert w1 w2 τ Hw Hw'.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * by constructor.
  * intros τ n ws1 ws2 _ ? IH _ Hws; constructor. revert Hws.
    induction IH; simpl; rewrite ?fmap_app; intros; decompose_Forall_hyps; auto.
  * intros s τs wxbss1 wxbss2 _ Hws' IH Hxbs _ _ _ Hws; constructor.
    + revert Hws' Hxbs Hws. induction IH as [|[][]]; csimpl;
        rewrite ?fmap_app, <-?(associative_L (++));
        do 2 inversion_clear 1; intros; decompose_Forall_hyps; eauto.
    + clear IH. revert Hxbs Hws.
      induction Hws' as [|[][]]; csimpl; rewrite ?fmap_app,
        <-?(associative_L (++)); intros; decompose_Forall_hyps; eauto.
  * intros s τs i w1 w2 xbs1 xbs2 τ; rewrite !fmap_app; intros.
    unfold MUnion'. decompose_Forall_hyps. rewrite !ctree_flatten_map.
    destruct (decide (_ ∧ Forall sep_unmapped (h1 <$> xbs1))) as [[??]|?].
    + rewrite decide_True by intuition eauto using pbits_refine_unmapped.
      constructor; rewrite ?ctree_flatten_map; auto.
    + rewrite decide_False by intuition eauto using pbits_refine_mapped.
      constructor; rewrite ?ctree_flatten_map; auto.
  * by constructor.
  * intros s i τs w1 xbs1 xbs2 τ; rewrite fmap_app; intros.
    unfold MUnion'; case_decide; constructor; rewrite ?ctree_flatten_map; auto.
Qed.
End memory_trees.
