(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_trees permission_bits_refine.
Local Open Scope ctype_scope.

Inductive ctree_refine' `{Env K} (Γ : env K) (α : bool) (f : meminj K)
     (Δ1 Δ2 : memenv K) : mtree K → mtree K → type K → Prop :=
  | MBase_refine τb γbs1 γbs2 :
     ✓{Γ} τb → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     length γbs1 = bit_size_of Γ (baseT τb) →
     ctree_refine' Γ α f Δ1 Δ2 (MBase τb γbs1) (MBase τb γbs2) (baseT τb)
  | MArray_refine τ n ws1 ws2 :
     n = length ws1 →
     Forall2 (λ w1 w2, ctree_refine' Γ α f Δ1 Δ2 w1 w2 τ) ws1 ws2 →
     n ≠ 0 → ctree_refine' Γ α f Δ1 Δ2 (MArray τ ws1) (MArray τ ws2) (τ.[n])
  | MStruct_refine t wγbss1 wγbss2 τs :
     Γ !! t = Some τs → Forall3 (λ wγbs1 wγbs2 τ,
       ctree_refine' Γ α f Δ1 Δ2 (wγbs1.1) (wγbs2.1) τ) wγbss1 wγbss2 τs →
     wγbss1 ⊑{Γ,α,f@Δ1↦Δ2}2** wγbss2 →
     Forall (λ wγbs, pbit_indetify <$> wγbs.2 = wγbs.2) wγbss1 →
     Forall (λ wγbs, pbit_indetify <$> wγbs.2 = wγbs.2) wγbss2 →
     length ∘ snd <$> wγbss1 = field_bit_padding Γ τs →
     ctree_refine' Γ α f Δ1 Δ2
       (MStruct t wγbss1) (MStruct t wγbss2) (structT t)
  | MUnion_refine t τs i w1 w2 γbs1 γbs2 τ :
     Γ !! t = Some τs → τs !! i = Some τ →
     ctree_refine' Γ α f Δ1 Δ2 w1 w2 τ → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     pbit_indetify <$> γbs1 = γbs1 → pbit_indetify <$> γbs2 = γbs2 →
     bit_size_of Γ (unionT t) = bit_size_of Γ τ + length γbs1 →
     ¬(ctree_unmapped w1 ∧ Forall sep_unmapped γbs1) →
     ¬(ctree_unmapped w2 ∧ Forall sep_unmapped γbs2) →
     ctree_refine' Γ α f Δ1 Δ2
       (MUnion t i w1 γbs1) (MUnion t i w2 γbs2) (unionT t)
  | MUnionAll_refine t τs γbs1 γbs2 :
     Γ !! t = Some τs → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     length γbs1 = bit_size_of Γ (unionT t) →
     ctree_refine' Γ α f Δ1 Δ2
       (MUnionAll t γbs1) (MUnionAll t γbs2) (unionT t)
  | MUnion_MUnionAll_refine t τs i w1 γbs1 γbs2 τ :
     α → Γ !! t = Some τs → τs !! i = Some τ →
     ctree_flatten w1 ++ γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     pbit_indetify <$> γbs1 = γbs1 →
     (Γ,Δ1) ⊢ w1 : τ → Forall sep_unshared γbs2 →
     bit_size_of Γ (unionT t) = bit_size_of Γ τ + length γbs1 →
     ¬(ctree_unmapped w1 ∧ Forall sep_unmapped γbs1) →
     ctree_refine' Γ α f Δ1 Δ2
       (MUnion t i w1 γbs1) (MUnionAll t γbs2) (unionT t).
#[global] Instance ctree_refine `{Env K} :
  RefineT K (env K) (type K) (mtree K) := ctree_refine'.

Lemma ctree_refine_inv_l `{Env K} (Γ : env K) (α : bool)
    (f : meminj K) (Δ1 Δ2 : memenv K) (P : mtree K → Prop) w1 w2 τ :
  w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ →
  match w1 with
  | MBase τb γbs1 =>
     (∀ γbs2, γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → P (MBase τb γbs2)) → P w2
  | MArray τ ws1 =>
     (∀ ws2, ws1 ⊑{Γ,α,f@Δ1↦Δ2}* ws2 : τ → P (MArray τ ws2)) → P w2
  | MStruct t wγbss1 => (∀ τs wγbss2,
     Γ !! t = Some τs → wγbss1 ⊑{Γ,α,f@Δ1↦Δ2}1* wγbss2 :* τs →
     Forall (λ wγbs, pbit_indetify <$> wγbs.2 = wγbs.2) wγbss1 →
     Forall (λ wγbs, pbit_indetify <$> wγbs.2 = wγbs.2) wγbss2 →
     wγbss1 ⊑{Γ,α,f@Δ1↦Δ2}2** wγbss2 → P (MStruct t wγbss2)) → P w2
  | MUnion t i w1 γbs1 =>
     (∀ τs w2 γbs2 τ,
       Γ !! t = Some τs → τs !! i = Some τ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ →
       γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → pbit_indetify <$> γbs1 = γbs1 →
       pbit_indetify <$> γbs2 = γbs2 → P (MUnion t i w2 γbs2)) →
     (∀ τs τ γbs2,
       α → Γ !! t = Some τs → τs !! i = Some τ →
       ctree_flatten w1 ++ γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
       Forall sep_unshared γbs2 → P (MUnionAll t γbs2)) → P w2
  | MUnionAll t γbs1 =>
     (∀ γbs2, γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → P (MUnionAll t γbs2)) → P w2
  end.
Proof. destruct 1; eauto. Qed.
Section ctree_refine_ind.
  Context `{Env K} (Γ : env K) (α : bool) (f : meminj K).
  Context (Δ1 Δ2 : memenv K) (P : mtree K → mtree K → type K → Prop).
  Context (Pbase : ∀ τb γbs1 γbs2,
    ✓{Γ} τb → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
    length γbs1 = bit_size_of Γ (baseT τb) →
    P (MBase τb γbs1) (MBase τb γbs2) (baseT τb)).
  Context (Parray : ∀ τ n ws1 ws2,
    n = length ws1 → ws1 ⊑{Γ,α,f@Δ1↦Δ2}* ws2 : τ →
    Forall2 (λ w1 w2, P w1 w2 τ) ws1 ws2 →
    n ≠ 0 → P (MArray τ ws1) (MArray τ ws2) (τ.[n])).
  Context (Pstruct : ∀ t τs wγbss1 wγbss2,
    Γ !! t = Some τs → wγbss1 ⊑{Γ,α,f@Δ1↦Δ2}1* wγbss2 :* τs →
    Forall3 (λ wγbs1 wγbs2 τ, P (wγbs1.1) (wγbs2.1) τ) wγbss1 wγbss2 τs →
    wγbss1 ⊑{Γ,α,f@Δ1↦Δ2}2** wγbss2 →
    Forall (λ wγbs, pbit_indetify <$> wγbs.2 = wγbs.2) wγbss1 →
    Forall (λ wγbs, pbit_indetify <$> wγbs.2 = wγbs.2) wγbss2 →
    length ∘ snd <$> wγbss1 = field_bit_padding Γ τs →
    P (MStruct t wγbss1) (MStruct t wγbss2) (structT t)).
  Context (Punion : ∀ t τs i w1 w2 γbs1 γbs2 τ,
    Γ !! t = Some τs → τs !! i = Some τ →
    w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → P w1 w2 τ → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
    pbit_indetify <$> γbs1 = γbs1 → pbit_indetify <$> γbs2 = γbs2 →
    bit_size_of Γ (unionT t) = bit_size_of Γ τ + length γbs1 →
    ¬(ctree_unmapped w1 ∧ Forall sep_unmapped γbs1) →
    ¬(ctree_unmapped w2 ∧ Forall sep_unmapped γbs2) →
    P (MUnion t i w1 γbs1) (MUnion t i w2 γbs2) (unionT t)).
  Context (Punion_all : ∀ t τs γbs1 γbs2,
    Γ !! t = Some τs → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
    length γbs1 = bit_size_of Γ (unionT t) →
    P (MUnionAll t γbs1) (MUnionAll t γbs2) (unionT t)).
  Context (Punion_union_all : ∀ t i τs w1 γbs1 γbs2 τ,
    α → Γ !! t = Some τs → τs !! i = Some τ →
    ctree_flatten w1 ++ γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
    pbit_indetify <$> γbs1 = γbs1 →
    (Γ,Δ1) ⊢ w1 : τ → Forall sep_unshared γbs2 →
    bit_size_of Γ (unionT t) = bit_size_of Γ τ + length γbs1 →
    ¬(ctree_unmapped w1 ∧ Forall sep_unmapped γbs1) →
    P (MUnion t i w1 γbs1) (MUnionAll t γbs2) (unionT t)).
  Definition ctree_refine_ind: ∀ w1 w2 τ,
    ctree_refine' Γ α f Δ1 Δ2 w1 w2 τ → P w1 w2 τ.
  Proof. fix H'4 4; destruct 1; eauto using Forall2_impl, Forall3_impl. Qed.
End ctree_refine_ind.

Section memory_trees.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types α : bool.
Implicit Types Δ : memenv K.
Implicit Types τb : base_type K.
Implicit Types τ σ : type K.
Implicit Types τs σs : list (type K).
Implicit Types o : index.
Implicit Types γb : pbit K.
Implicit Types γbs : list (pbit K).
Implicit Types w : mtree K.
Implicit Types ws : list (mtree K).
Implicit Types wγbs : mtree K * list (pbit K).
Implicit Types wγbss : list (mtree K * list (pbit K)).
Implicit Types rs : ref_seg K.
Implicit Types r : ref K.
Implicit Types g : mtree K → mtree K.
Implicit Types f : meminj K.

Hint Resolve Forall_take Forall_drop Forall_app_2 Forall_replicate: core.
Hint Resolve Forall2_take Forall2_drop Forall2_app: core.
Hint Immediate env_valid_lookup env_valid_lookup_lookup: core.

Ltac solve_length := simplify_equality'; repeat first 
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite fmap_length | rewrite mask_length | erewrite ctree_flatten_length by eauto
  | rewrite type_mask_length by eauto
  | rewrite insert_length | rewrite replicate_length
  | rewrite bit_size_of_int | rewrite int_width_char | rewrite resize_length
  | erewrite sublist_lookup_length by eauto
  | erewrite sublist_alter_length by eauto
  | match goal with
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
        | H : Γ !! ?t = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
          unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t)) by done;
          assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t))
            by eauto using bit_size_of_union_lookup
        end
    | H : Forall2 _ _ _ |- _ => apply Forall2_length in H
    end ]; lia.
Hint Extern 0 (length _ = _) => solve_length: core.
Hint Extern 0 (_ = length _) => solve_length: core.

Inductive ctree_leaf_refine Γ α f Δ1 Δ2 : relation (mtree K) :=
  | MBase_shape τb γbs1 γbs2 :
     γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     ctree_leaf_refine Γ α f Δ1 Δ2 (MBase τb γbs1) (MBase τb γbs2)
  | MArray_shape τ ws1 ws2 :
     Forall2 (ctree_leaf_refine Γ α f Δ1 Δ2) ws1 ws2 →
     ctree_leaf_refine Γ α f Δ1 Δ2 (MArray τ ws1) (MArray τ ws2)
  | MStruct_shape t wγbss1 wγbss2 :
     Forall2 (λ wγbs1 wγbs2,
       ctree_leaf_refine Γ α f Δ1 Δ2 (wγbs1.1) (wγbs2.1)) wγbss1 wγbss2 →
     wγbss1 ⊑{Γ,α,f@Δ1↦Δ2}2** wγbss2 →
     ctree_leaf_refine Γ α f Δ1 Δ2 (MStruct t wγbss1) (MStruct t wγbss2)
  | MUnion_shape t i w1 w2 γbs1 γbs2 :
     ctree_leaf_refine Γ α f Δ1 Δ2 w1 w2 → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     ctree_leaf_refine Γ α f Δ1 Δ2 (MUnion t i w1 γbs1) (MUnion t i w2 γbs2)
  | MUnionAll_shape t γbs1 γbs2 :
     γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     ctree_leaf_refine Γ α f Δ1 Δ2 (MUnionAll t γbs1) (MUnionAll t γbs2)
  | MUnion_MUnionAll_shape t i w1 γbs1 γbs2 :
     α → ctree_flatten w1 ++ γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
     Forall sep_unshared γbs2 →
     ctree_leaf_refine Γ α f Δ1 Δ2 (MUnion t i w1 γbs1) (MUnionAll t γbs2).

Section ctree_leaf_refine.
  Context Γ α f Δ1 Δ2 (P : mtree K → mtree K → Prop).
  Context (Pbase : ∀ τb γbs1 γbs2,
    γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → P (MBase τb γbs1) (MBase τb γbs2)).
  Context (Parray : ∀ τ ws1 ws2,
    Forall2 (ctree_leaf_refine Γ α f Δ1 Δ2) ws1 ws2 → Forall2 P ws1 ws2 →
    P (MArray τ ws1) (MArray τ ws2)).
  Context (Pstruct : ∀ t wγbss1 wγbss2,
    Forall2 (λ wγbs1 wγbs2,
      ctree_leaf_refine Γ α f Δ1 Δ2 (wγbs1.1) (wγbs2.1)) wγbss1 wγbss2 →
    Forall2 (λ wγbs1 wγbs2, P (wγbs1.1) (wγbs2.1)) wγbss1 wγbss2 →
    wγbss1 ⊑{Γ,α,f@Δ1↦Δ2}2** wγbss2 → P (MStruct t wγbss1) (MStruct t wγbss2)).
  Context (Punion : ∀ t i w1 w2 γbs1 γbs2,
    ctree_leaf_refine Γ α f Δ1 Δ2 w1 w2 → P w1 w2 →
    γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → P (MUnion t i w1 γbs1) (MUnion t i w2 γbs2)).
  Context (Munionall : ∀ t γbs1 γbs2,
    γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → P (MUnionAll t γbs1) (MUnionAll t γbs2)).
  Context (Munionall' : ∀ t i w1 γbs1 γbs2,
    α → ctree_flatten w1 ++ γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → 
    Forall sep_unshared γbs2 → P (MUnion t i w1 γbs1) (MUnionAll t γbs2)).
  Lemma ctree_leaf_refine_ind_alt :
     ∀ w1 w2, ctree_leaf_refine Γ α f Δ1 Δ2 w1 w2 → P w1 w2.
  Proof. fix H'3 3; destruct 1; eauto using Forall2_impl. Qed.
End ctree_leaf_refine.

Lemma ctree_refine_leaf Γ α f Δ1 Δ2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → ctree_leaf_refine Γ α f Δ1 Δ2 w1 w2.
Proof.
  induction 1 as [| |?????? IH| | |] using @ctree_refine_ind; constructor; auto.
  elim IH; auto.
Qed.
Hint Immediate ctree_refine_leaf: core.
Lemma ctree_leaf_refine_refine Γ α f Δ1 Δ2 w1 w2 τ :
  ✓ Γ → ctree_leaf_refine Γ α f Δ1 Δ2 w1 w2 →
  (Γ,Δ1) ⊢ w1 : τ → (Γ,Δ2) ⊢ w2 : τ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ.
Proof.
  intros ? Hw. revert τ. revert w1 w2 Hw.
  refine (ctree_leaf_refine_ind_alt _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * intros τb γbs1 γbs2 τ ? Hw1 _; apply (ctree_typed_inv_l _ _ _ _ _ Hw1).
    by refine_constructor.
  * intros τ ws1 ws2 _ IH τ' Hw1; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1;
      intros Hws1 Hlen Hw2; apply (ctree_typed_inv _ _ _ _ _ Hw2); clear Hw2;
      intros _ _ Hws2 _; refine_constructor; eauto.
    clear Hlen. induction IH; decompose_Forall_hyps; auto.
  * intros t wγbss1 wγbss2 _ IH Hγbs τ' Hw1; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1;
      intros τs Ht Hws1 Hγbs1 Hindet1 Hlen Hw2;
      apply (ctree_typed_inv _ _ _ _ _ Hw2);
      clear Hw2; intros ? _ ? Hws2 Hγbs2 Hindet2 _; simplify_equality';
      refine_constructor; eauto.
    clear Ht Hγbs1 Hlen Hγbs2 Hindet1 Hindet2 Hγbs. revert τs Hws1 Hws2.
    induction IH; intros; decompose_Forall_hyps; constructor; auto.
  * intros t i w1 w2 γbs1 γbs2 _ ?? τ Hw1; pattern τ;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ Hw1;
      intros τs τ ??????? Hw2; apply (ctree_typed_inv _ _ _ _ _ Hw2);
      intros; decompose_Forall_hyps; refine_constructor; eauto.
  * intros t γbs1 γbs2 τ ? Hw1 _; apply (ctree_typed_inv_l _ _ _ _ _ Hw1).
    refine_constructor; eauto.
  * intros t i w1 γbs1 γbs2 ??? τ Hw1; pattern τ;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); intros ????????? Hw2;
      apply (ctree_typed_inv _ _ _ _ _ Hw2); intros; simplify_equality'.
    refine_constructor; eauto.
Qed.
Lemma ctree_flatten_leaf_refine Γ α f Δ1 Δ2 w1 w2 :
  ctree_leaf_refine Γ α f Δ1 Δ2 w1 w2 →
  ctree_flatten w1 ⊑{Γ,α,f@Δ1↦Δ2}* ctree_flatten w2.
Proof.
  revert w1 w2.
  refine (ctree_leaf_refine_ind_alt _ _ _ _ _ _ _ _ _ _ _ _); simpl; auto 2.
  * eauto using Forall2_bind.
  * intros t wγbss1 wγbss2 _ IH ?. induction IH; decompose_Forall_hyps; auto.
Qed.
Lemma ctree_unflatten_leaf_refine Γ α f Δ1 Δ2 τ γbs1 γbs2 :
  ✓ Γ → ✓{Γ} τ → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 →
  ctree_leaf_refine Γ α f Δ1 Δ2
    (ctree_unflatten Γ τ γbs1) (ctree_unflatten Γ τ γbs2).
Proof.
  intros HΓ Hτ. revert τ Hτ γbs1 γbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite !ctree_unflatten_base. by constructor.
  * intros τ n _ IH _ γbs1 γbs2 Hγbs. rewrite !ctree_unflatten_array.
    constructor. revert γbs1 γbs2 Hγbs. induction n; simpl; auto.
  * intros [] t τs Ht _ IH _ γbs1 γbs2 Hγbs; erewrite
      !ctree_unflatten_compound by eauto; simpl; clear Ht; [|by constructor].
    unfold struct_unflatten; constructor.
    + revert γbs1 γbs2 Hγbs. induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps; constructor; simpl; auto.
    + revert γbs1 γbs2 Hγbs. induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps; constructor; simpl;
        auto using pbits_indetify_refine.
Qed.
Lemma ctree_unflatten_refine Γ α f Δ1 Δ2 τ γbs1 γbs2 :
  ✓ Γ → ✓{Γ} τ → γbs1 ⊑{Γ,α,f@Δ1↦Δ2}* γbs2 → length γbs1 = bit_size_of Γ τ →
  ctree_unflatten Γ τ γbs1 ⊑{Γ,α,f@Δ1↦Δ2} ctree_unflatten Γ τ γbs2 : τ.
Proof.
  intros; apply ctree_leaf_refine_refine; eauto using ctree_unflatten_typed,
    pbits_refine_valid_l, pbits_refine_valid_r, ctree_unflatten_leaf_refine.
Qed.
Lemma ctree_flatten_refine Γ α f Δ1 Δ2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ →
  ctree_flatten w1 ⊑{Γ,α,f@Δ1↦Δ2}* ctree_flatten w2.
Proof. eauto using ctree_flatten_leaf_refine. Qed.
Lemma ctree_refine_typed_l Γ α f Δ1 Δ2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → (Γ,Δ1) ⊢ w1 : τ.
Proof.
  intros ?. revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _).
  * typed_constructor; eauto using pbits_refine_valid_l.
  * intros τ n ws1 ws2 Hn _ IH ?; typed_constructor; auto.
    clear Hn. induction IH; auto.
  * intros t τs wγbss1 wγbss2 Ht _ IH Hγbs Hindet _ Hlen.
    typed_constructor; eauto; clear Ht Hlen; induction IH;
      decompose_Forall_hyps; eauto using pbits_refine_valid_l.
  * typed_constructor; eauto using pbits_refine_valid_l.
  * intros; typed_constructor; eauto using pbits_refine_valid_l.
  * intros; decompose_Forall_hyps; typed_constructor;
      eauto using pbits_refine_valid_l.
Qed.
Lemma ctree_refine_typed_r Γ α f Δ1 Δ2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → (Γ,Δ2) ⊢ w2 : τ.
Proof.
  intros ?. revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _).
  * typed_constructor; eauto using Forall2_length_l, pbits_refine_valid_r.
  * intros τ n ws1 ws2 -> _ IH Hn;
      typed_constructor; eauto using Forall2_length.
    clear Hn. induction IH; auto.
  * intros t τs wγbss1 wγbss2 Ht _ IH Hγbs _ ? Hlen. typed_constructor; eauto.
    + elim IH; eauto.
    + elim Hγbs; eauto using pbits_refine_valid_r.
    + rewrite <-Hlen; symmetry.
      elim Hγbs; intros; f_equal'; eauto using Forall2_length.
  * intros; typed_constructor; eauto using pbits_refine_valid_r; solve_length.
  * typed_constructor; eauto using Forall2_length_l, pbits_refine_valid_r.
  * typed_constructor; eauto using Forall2_length_l, pbits_refine_valid_r.
Qed.
Hint Immediate ctree_refine_typed_l ctree_refine_typed_r: core.
Lemma ctree_refine_type_valid_l Γ α f Δ1 Δ2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → ✓{Γ} τ.
Proof. eauto using ctree_typed_type_valid. Qed.
Lemma ctree_refine_type_of_l Γ α f Δ1 Δ2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → type_of w1 = τ.
Proof. destruct 1 using @ctree_refine_ind; simpl; auto. Qed.
Lemma ctree_refine_type_of_r Γ α f Δ1 Δ2 w1 w2 τ :
  w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → type_of w2 = τ.
Proof. destruct 1; f_equal'; eauto using Forall2_length_l. Qed.
Lemma ctree_refine_id Γ α Δ w τ : (Γ,Δ) ⊢ w : τ → w ⊑{Γ,α@Δ} w : τ.
Proof.
  revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _);
     try by (intros; refine_constructor; eauto using pbits_refine_id).
  * intros ws τ _ IH Hlen; refine_constructor; auto. elim IH; auto.
  * intros t wγbss τs ? _ IH Hwγbss ??; refine_constructor; eauto.
    + elim IH; constructor; eauto.
    + elim Hwγbss; constructor; eauto using pbits_refine_id.
Qed.
Lemma ctree_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 w1 w2 w3 τ :
  ✓ Γ → w1 ⊑{Γ,α1,f1@Δ1↦Δ2} w2 : τ → w2 ⊑{Γ,α2,f2@Δ2↦Δ3} w3 : τ →
  w1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} w3 : τ.
Proof.
  intros ? Hw Hw3. apply ctree_leaf_refine_refine; eauto.
  revert w1 w2 τ Hw w3 Hw3.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * intros τb γbs1 γbs2 ??? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3).
    constructor; eauto using pbits_refine_compose.
  * intros τ n ws1 ws2 -> _ IH _ w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    intros ws3 Hws3; constructor. revert ws3 Hws3.
    induction IH; intros; decompose_Forall_hyps; constructor; auto.
  * intros t τs wγbss1 wγbss2 Ht _ IH Hγbs _ _ _ w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    intros ? wγbss3 ? Hws3 _ _ Hγbs3; simplify_equality; constructor.
    + clear Ht Hγbs3 Hγbs. revert wγbss3 Hws3.
      induction IH; inversion_clear 1; constructor; eauto.
    + clear Ht IH Hws3. revert wγbss3 Hγbs3. induction Hγbs; intros;
        decompose_Forall_hyps; constructor; eauto using pbits_refine_compose.
  * intros t τs i w1 w2 γbs1 γbs2 τ Ht Hτs ? IH ?????? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3;
      intros; decompose_Forall_hyps;
      constructor; eauto using ctree_flatten_refine, pbits_refine_compose.
  * intros t τs γbs1 γbs2 Ht ?? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3).
    constructor; eauto using pbits_refine_compose.
  * intros t i τs w1 γbs1 γbs2 τ ????????? w3 Hw3; pattern w3;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ _ Hw3); clear w3 Hw3.
    constructor; eauto using pbits_refine_compose, pbits_refine_unshared.
Qed.
Lemma ctree_refine_inverse Γ f Δ1 Δ2 w1 w2 τ :
  w1 ⊑{Γ,false,f@Δ1↦Δ2} w2 : τ →
  w2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} w1 : τ.
Proof.
  revert w1 w2 τ. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * refine_constructor; eauto using pbits_refine_inverse.
  * refine_constructor; auto. by apply Forall2_flip.
  * intros ?????? IH Hγbss ?? Hlen; refine_constructor; eauto.
    + elim IH; constructor; eauto.
    + elim Hγbss; eauto using pbits_refine_inverse.
    + rewrite <-Hlen. elim Hγbss; intros; f_equal'; auto.
  * refine_constructor; eauto using pbits_refine_inverse; solve_length.
  * refine_constructor; eauto using pbits_refine_inverse.
  * done.
Qed.
Lemma ctree_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → Γ ⊆ Γ' → (α → α') →
  Δ1' ⊑{Γ',α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → w1 ⊑{Γ',α',f'@Δ1'↦Δ2'} w2 : τ.
Proof.
  intros ? Hw; intros. induction Hw using @ctree_refine_ind;
    refine_constructor; try (eapply Forall2_impl; [eassumption|]); simpl;
    eauto using base_type_valid_weaken,
      lookup_compound_weaken, pbit_refine_weaken, ctree_typed_weaken;
    erewrite <-?(bit_size_of_weaken Γ Γ'), <-?(field_bit_padding_weaken Γ Γ')
      by eauto using TBase_valid, TCompound_valid; auto.
  simpl; eauto using Forall2_impl, pbit_refine_weaken.
Qed.
Lemma union_free_refine Γ α f Δ1 Δ2 w1 w2 τ :
  union_free w1 → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → union_free w2.
Proof.
  intros Hw1 Hw. revert w1 w2 τ Hw Hw1.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl; try by constructor.
  * intros τ n ws1 ws2 _ _ IH _; inversion_clear 1; constructor.
    induction IH; decompose_Forall_hyps; auto.
  * intros t τs wγbss1 wxnss2 _ _ IH _ _ _ _; inversion_clear 1; constructor.
    induction IH; decompose_Forall_hyps; auto.
  * inversion_clear 11.
Qed.
Lemma union_reset_above Γ f Δ1 Δ2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,true,f@Δ1↦Δ2} w2 : τ →
  ctree_unshared w2 → w1 ⊑{Γ,true,f@Δ1↦Δ2} union_reset w2 : τ.
Proof.
  intros HΓ. revert w1 w2 τ.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * by refine_constructor.
  * intros τ n ws1 ws2 Hn _ IH ??. refine_constructor; auto.
    clear Hn. induction IH; decompose_Forall_hyps; auto.
  * intros t τs wγbss1 wγbss2 Ht _ IH ? Hindet1 Hindet2 Hlen ?;
      refine_constructor; eauto; clear Ht Hlen;
      induction IH; decompose_Forall_hyps; constructor; auto.
  * refine_constructor; eauto using ctree_flatten_refine.
  * refine_constructor; eauto.
  * refine_constructor; eauto.
Qed.
Lemma union_reset_refine Γ α f Δ1 Δ2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ →
  union_reset w1 ⊑{Γ,α,f@Δ1↦Δ2} union_reset w2 : τ.
Proof.
  intros ? Hw. apply ctree_leaf_refine_refine; eauto using union_reset_typed.
  revert w1 w2 τ Hw. refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _);
    simpl; try by (intros; constructor; eauto 1).
  * intros τ n ws1 ws2 _ _ IH _; constructor; auto. elim IH; constructor; eauto.
  * intros t τs wγbss1 wγbss2 ? _ IH Hγbs _ _ _. constructor; eauto.
    + elim IH; constructor; eauto.
    + elim Hγbs; constructor; eauto.
  * constructor; eauto using ctree_flatten_refine.
Qed.
Lemma ctree_flatten_unflatten_refine Γ f Δ1 Δ2 w γbs τ :
  ✓ Γ → (Γ,Δ1) ⊢ w : τ → Forall sep_unshared γbs →
  ctree_flatten w ⊑{Γ,true,f@Δ1↦Δ2}* γbs →
  w ⊑{Γ,true,f@Δ1↦Δ2} ctree_unflatten Γ τ γbs : τ.
Proof.
  intros. rewrite <-(right_id_L _ (◎) f), <-(orb_diag true).
  apply ctree_refine_compose
    with Δ1 (ctree_unflatten Γ τ (ctree_flatten w)); auto.
  { erewrite ctree_unflatten_flatten by eauto.
    apply union_reset_above; eauto using ctree_refine_id.
    eauto using pbits_refine_shared. }
  apply ctree_unflatten_refine; eauto using ctree_typed_type_valid.
Qed.
Lemma ctree_lookup_seg_refine Γ α f Δ1 Δ2 w1 w2 τ rs w3 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → w1 !!{Γ} rs = Some w3 →
  ∃ w4, w2 !!{Γ} rs = Some w4 ∧ w3 ⊑{Γ,α,f@Δ1↦Δ2} w4 : type_of w3.
Proof.
  intros ? Hw Hrs.
  cut (∃ w4, w2 !!{Γ} rs = Some w4 ∧ ctree_leaf_refine Γ α f Δ1 Δ2 w3 w4).
  { intros (w4&?&?); exists w4; split; auto.
    destruct (ctree_lookup_seg_Some Γ Δ1 w1 τ rs w3) as (?&?&?),
      (ctree_lookup_seg_Some Γ Δ2 w2 τ rs w4) as (?&?&?); eauto.
    simplify_type_equality; eauto using ctree_leaf_refine_refine. }
  destruct Hw, rs;
    change (ctree_refine' Γ α f Δ1 Δ2) with (refineT Γ α f Δ1 Δ2) in *;
    pattern w3; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); simpl; clear Hrs.
  * intros; simplify_option_eq; decompose_Forall_hyps; eauto.
  * intros; repeat (simplify_option_eq || decompose_Forall_hyps); eauto.
  * intros; simplify_option_eq; eauto.
  * intros; simplify_option_eq by eauto using
      pbits_refine_unshared, ctree_flatten_refine.
    eexists; split; eauto. eapply ctree_refine_leaf;
      eauto using ctree_unflatten_refine, ctree_flatten_refine.
  * intros; simplify_option_eq by eauto using pbits_refine_unshared.
    eexists; eauto using ctree_refine_leaf, ctree_unflatten_refine.
  * intros; destruct α; try done;
      simplify_option_eq; decompose_Forall_hyps.
    rewrite take_app_alt by (by erewrite <-Forall2_length by eauto).
    eexists; eauto using ctree_refine_leaf, ctree_flatten_unflatten_refine.
  * intros; simplify_option_eq.
    eexists; split; eauto. eapply ctree_refine_leaf;
      eauto using ctree_unflatten_refine, ctree_flatten_refine.
Qed.
Lemma ctree_lookup_refine Γ α f Δ1 Δ2 w1 w2 τ r w3 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → w1 !!{Γ} r = Some w3 →
  ∃ w4, w2 !!{Γ} r = Some w4 ∧ w3 ⊑{Γ,α,f@Δ1↦Δ2} w4 : type_of w3.
Proof.
  intros HΓ. revert w1 w2 τ. induction r as [|rs r IH] using rev_ind; simpl.
  { intros. rewrite ctree_lookup_nil. simplify_type_equality.
    erewrite ctree_refine_type_of_l by eauto; eauto. }
  intros w1 w2. rewrite !ctree_lookup_snoc. intros. simplify_option_eq.
  edestruct (ctree_lookup_seg_refine Γ α f Δ1 Δ2 w1 w2 τ rs) as (?&?&?);
    simplify_option_eq; eauto.
Qed.
Lemma ctree_lookup_refine_both Γ α f Δ1 Δ2 w1 w2 τ r w3 w4 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → w1 !!{Γ} r = Some w3 →
  w2 !!{Γ} r = Some w4 → w3 ⊑{Γ,α,f@Δ1↦Δ2} w4 : type_of w3.
Proof.
  intros. destruct (ctree_lookup_refine Γ α f Δ1 Δ2 w1 w2 τ r w3)
    as (?&?&?); simplify_equality'; auto.
Qed.
Lemma ctree_alter_seg_refine Γ α f Δ1 Δ2 g1 g2 w1 w2 τ rs w3 w4 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ →
  w1 !!{Γ} rs = Some w3 → w2 !!{Γ} rs = Some w4 →
  g1 w3 ⊑{Γ,α,f@Δ1↦Δ2} g2 w4 : type_of w3 → ¬ctree_unmapped (g1 w3) →
  ctree_alter_seg Γ g1 rs w1 ⊑{Γ,α,f@Δ1↦Δ2} ctree_alter_seg Γ g2 rs w2 : τ.
Proof.
  intros ? Hw Hw3 Hw4 Hgw. cut (ctree_leaf_refine Γ α f Δ1 Δ2
    (ctree_alter_seg Γ g1 rs w1) (ctree_alter_seg Γ g2 rs w2)).
  { intros. assert ((Γ, Δ2) ⊢ g2 w4 : type_of w4).
    { destruct (ctree_lookup_seg_Some Γ Δ1 w1 τ rs w3) as (τ'&?&?),
        (ctree_lookup_seg_Some Γ Δ2 w2 τ rs w4) as (?&?&?); eauto.
      simplify_type_equality'; eauto. }
    assert (¬ctree_unmapped (g2 w4))
      by eauto using pbits_refine_mapped, ctree_flatten_refine.
    apply ctree_leaf_refine_refine; eauto using ctree_alter_seg_typed. }
  revert Hgw.
  destruct Hw as [|τ n ws1 ws2 ? Hws|s wγbss1 wγbss2?? Hws| | |], rs; simpl;
    change (ctree_refine' Γ α f Δ1 Δ2) with (refineT Γ α f Δ1 Δ2) in *;
    pattern w3; apply (ctree_lookup_seg_inv _ _ _ _ _ Hw3); simpl; clear Hw3;
    pattern w4; apply (ctree_lookup_seg_inv _ _ _ _ _ Hw4); simpl; clear Hw4;
    intros; simplify_option_eq; decompose_Forall_hyps.
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
Lemma ctree_alter_refine Γ α f Δ1 Δ2 g1 g2 w1 w2 τ r w3 w4 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ →
  w1 !!{Γ} r = Some w3 → w2 !!{Γ} r = Some w4 →
  g1 w3 ⊑{Γ,α,f@Δ1↦Δ2} g2 w4 : type_of w3 → ¬ctree_unmapped (g1 w3) →
  ctree_alter Γ g1 r w1 ⊑{Γ,α,f@Δ1↦Δ2} ctree_alter Γ g2 r w2 : τ.
Proof.
  intros ?. revert g1 g2 w1 w2 τ.
  induction r as [|rs r IH] using rev_ind; simpl; intros g1 g2 w1 w2 τ.
  { rewrite !ctree_lookup_nil; intros ???; simplify_equality.
    erewrite ctree_refine_type_of_l by eauto; eauto. }
  rewrite !ctree_lookup_snoc, !ctree_alter_snoc; intros.
  destruct (w1 !!{Γ} rs) as [w1'|] eqn:?; simplify_equality'.
  destruct (w2 !!{Γ} rs) as [w2'|] eqn:?; simplify_equality'.
  destruct (ctree_lookup_seg_refine Γ α f Δ1 Δ2 w1 w2 τ rs w1')
    as (?&?&?); auto; simplify_equality'.
  eapply ctree_alter_seg_refine; eauto using ctree_alter_lookup_Forall.
Qed.
Lemma ctree_alter_seg_id_refine Γ Δ w τ rs w' :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → w !!{Γ} rs = Some w' → frozen rs → ¬ctree_unmapped w' →
  ctree_alter_seg Γ id rs w ⊑{Γ,true@Δ} w : τ.
Proof.
  intros ? Hw Hw' ??.
  apply ctree_leaf_refine_refine; eauto using ctree_alter_seg_typed,
    ctree_lookup_seg_Some_type_of.
  destruct Hw as [|?? ws ? Hws|s wγbss τs ? Hws Hγbs| |s τs γbs], rs;
    change (ctree_typed' Γ Δ) with (typed (Γ,Δ)) in *;
    pattern w'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hw'); simpl; clear Hw';
    intros; simplify_option_eq;
    rewrite ?list_alter_id by done; rewrite ?list_alter_id by (by intros []);
    constructor; eauto using pbits_refine_id, ctree_refine_id, ctree_refine_leaf.
  * elim Hws; eauto using ctree_refine_id, ctree_refine_leaf.
  * elim Hws; eauto using ctree_refine_id, ctree_refine_leaf.
  * elim Hγbs; eauto using pbits_refine_id.
  * pattern γbs at 3; rewrite <-(take_drop (bit_size_of Γ τ) γbs),
      ctree_flatten_unflatten by eauto;
      eauto 10 using pbits_indetify_refine_l, pbits_mask_indetify_refine_l.
Qed.
Lemma ctree_alter_id_refine Γ Δ w τ r w' :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → w !!{Γ} r = Some w' → freeze true <$> r = r →
  ¬ctree_unmapped w' → ctree_alter Γ id r w ⊑{Γ,true@Δ} w : τ.
Proof.
  intros ??. revert w'.
  induction r as [|rs r]; intros w3; auto using ctree_refine_id.
  rewrite ctree_lookup_cons,bind_Some; intros (w2&?&?) ? Hw; simplify_equality'.
  eapply (ctree_refine_compose Γ true true meminj_id meminj_id _ Δ);
    eauto 10 using ctree_lookup_seg_Forall, pbit_unmapped_indetify.
  eapply ctree_alter_refine; eauto using ctree_alter_seg_id_refine,
    ctree_refine_id, ctree_alter_lookup_seg_Forall, ctree_lookup_Some_type_of.
  contradict Hw; eapply (ctree_alter_lookup_seg_Forall _ _ id); eauto.
Qed.
Lemma ctree_lookup_byte_refine Γ α f Δ1 Δ2 w1 w2 τ i c1 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → w1 !!{Γ} i = Some c1 →
  ∃ c2, w2 !!{Γ} i = Some c2 ∧ c1 ⊑{Γ,α,f@Δ1↦Δ2} c2 : ucharT.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w1))
    as [γbs1|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_l (refine Γ α f Δ1 Δ2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits γbs1) as (γbs2&?&?);
    eauto using ctree_flatten_refine.
  exists (ctree_unflatten Γ ucharT γbs2); simplify_option_eq; split; auto.
  apply ctree_unflatten_refine; auto using TBase_valid, TInt_valid.
Qed.
Lemma ctree_lookup_byte_refine_inv Γ α f Δ1 Δ2 w1 w2 τ i c2 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → w2 !!{Γ} i = Some c2 →
  ∃ c1, w1 !!{Γ} i = Some c1 ∧ c1 ⊑{Γ,α,f@Δ1↦Δ2} c2 : ucharT.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w2))
    as [γbs2|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_r (refine Γ α f Δ1 Δ2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits γbs2) as (γbs1&?&?);
    eauto using ctree_flatten_refine.
  exists (ctree_unflatten Γ ucharT γbs1); simplify_option_eq; split; auto.
  apply ctree_unflatten_refine; auto using TBase_valid, TInt_valid.
Qed.
Lemma ctree_lookup_byte_alter_refine Γ Δ w τ i :
  ✓ Γ → (Γ,Δ) ⊢ w : ucharT →
  ctree_lookup_byte_after Γ τ i w ⊑{Γ,true@Δ} w : ucharT.
Proof.
  intros. rewrite <-(union_free_reset w) at 2 by eauto using union_free_base.
  erewrite <-ctree_unflatten_flatten by eauto.
  apply ctree_unflatten_refine; eauto using TBase_valid, TInt_valid.
  apply pbits_mask_indetify_refine_l; eauto using ctree_flatten_valid.
Qed.
Lemma ctree_alter_byte_refine Γ α f Δ1 Δ2 g1 g2 w1 w2 τ i c1 c2 :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ → w1 !!{Γ} i = Some c1 → w2 !!{Γ} i = Some c2 →
  g1 c1 ⊑{Γ,α,f@Δ1↦Δ2} g2 c2 : ucharT →
  ctree_alter_byte Γ g1 i w1 ⊑{Γ,α,f@Δ1↦Δ2} ctree_alter_byte Γ g2 i w2 : τ.
Proof.
  unfold lookupE, ctree_lookup_byte, ctree_alter_byte. intros.
  set (G1 := ctree_flatten ∘ g1 ∘ ctree_unflatten Γ ucharT).
  set (G2 := ctree_flatten ∘ g2 ∘ ctree_unflatten Γ ucharT).
  assert ((Γ,Δ1) ⊢ w1 : τ) by eauto; assert ((Γ,Δ2) ⊢ w2 : τ) by eauto.
  destruct (sublist_lookup _ _ (ctree_flatten w1)) as [γbs1|] eqn:?,
    (sublist_lookup _ _ (ctree_flatten w2)) as [γbs2|] eqn:?;
    simplify_type_equality'.
  destruct (Forall2_sublist_lookup_l (refine Γ α f Δ1 Δ2) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits γbs1) as (?&?&?);
    eauto 2 using ctree_flatten_refine; simplify_option_eq.
  assert (length (G1 γbs1) = char_bits).
  { unfold G1; simpl. eauto using ctree_refine_typed_l. }
  apply ctree_unflatten_refine; eauto 2 using ctree_typed_type_valid.
  eapply Forall2_sublist_alter; eauto 2 using ctree_flatten_refine.
Qed.
Lemma ctree_map_refine Γ α f Δ1 Δ2 h1 h2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : τ →
  h1 <$> ctree_flatten w1 ⊑{Γ,α,f@Δ1↦Δ2}* h2 <$> ctree_flatten w2 →
  (∀ γb, sep_unshared γb → sep_unshared (h2 γb)) →
  (∀ γb, ✓{Γ,Δ1} γb → sep_unmapped (h1 γb) → sep_unmapped γb) →
  (∀ γb, ✓{Γ,Δ2} γb → sep_unmapped (h2 γb) → sep_unmapped γb) →
  (∀ γb, pbit_indetify γb = γb → pbit_indetify (h1 γb) = h1 γb) →
  (∀ γb, pbit_indetify γb = γb → pbit_indetify (h2 γb) = h2 γb) →
  ctree_map h1 w1 ⊑{Γ,α,f@Δ1↦Δ2} ctree_map h2 w2 : τ.
Proof.
  intros ? Hw Hw' ? Hh ??.
  assert (∀ γbs, Forall sep_unshared γbs → Forall sep_unshared (h2 <$> γbs)).
  { induction 1; simpl; auto. }
  cut (ctree_leaf_refine Γ α f Δ1 Δ2 (ctree_map h1 w1) (ctree_map h2 w2)).
  { intros; apply ctree_leaf_refine_refine; eauto using
      ctree_map_typed, pbits_refine_valid_l, pbits_refine_valid_r. }
  clear Hh. revert w1 w2 τ Hw Hw'.
  refine (ctree_refine_ind _ _ _ _ _ _ _ _ _ _ _ _); simpl.
  * by constructor.
  * intros τ n ws1 ws2 _ ? IH _ Hws; constructor. revert Hws.
    induction IH; simpl; rewrite ?fmap_app; intros; decompose_Forall_hyps; auto.
  * intros t τs wγbss1 wγbss2 _ Hws' IH Hγbs _ _ _ Hws; constructor.
    + revert Hws' Hγbs Hws. induction IH as [|[][]]; csimpl;
        rewrite ?fmap_app, <-?(assoc_L (++));
        do 2 inversion_clear 1; intros; decompose_Forall_hyps; eauto.
    + clear IH. revert Hγbs Hws.
      induction Hws' as [|[][]]; csimpl; rewrite ?fmap_app,
        <-?(assoc_L (++)); intros; decompose_Forall_hyps; eauto.
  * intros t τs i w1 w2 γbs1 γbs2 τ; rewrite !fmap_app; intros.
    decompose_Forall_hyps; constructor; auto.
  * by constructor.
  * intros t i τs w1 γbs1 γbs2 τ; rewrite fmap_app; intros.
    constructor; rewrite ?ctree_flatten_map; auto.
Qed.
Lemma ctree_singleton_seg_refine Γ α f Δ1 Δ2 τ rs w1 w2 σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : σ →
  ¬ctree_unmapped w1 → ¬ctree_unmapped w2 →
  ctree_singleton_seg Γ rs w1 ⊑{Γ,α,f@Δ1↦Δ2} ctree_singleton_seg Γ rs w2 : τ.
Proof.
  intros ? Hrs ???. apply ctree_leaf_refine_refine; eauto 8 using
    ctree_singleton_seg_typed, pbits_refine_mapped, ctree_flatten_refine.
  destruct Hrs as [τ i n|s i τs|s i ? τs]; simpl.
  * constructor. rewrite !list_insert_alter. apply Forall2_alter; eauto.
    apply Forall2_replicate, ctree_unflatten_leaf_refine;
      eauto using ctree_refine_typed_l, ctree_typed_type_valid.
    apply Forall2_replicate, pbit_empty_refine.
  * assert (length (field_bit_padding Γ τs) = length τs) as Hlen
      by eauto using field_bit_padding_length.
    simplify_option_eq; constructor.
    + apply Forall2_fmap. rewrite !fst_zip, !list_insert_alter by solve_length.
      apply Forall2_alter; [|naive_solver].
      eapply Forall2_fmap, Forall_Forall2_diag, Forall_impl; eauto; intros.
      apply ctree_unflatten_leaf_refine; auto.
      apply Forall2_replicate, pbit_empty_refine.
    + apply Forall2_fmap. rewrite !snd_zip by solve_length.
      apply Forall2_fmap, Forall_Forall2_diag, Forall_true; intros n.
      apply Forall2_replicate, pbit_empty_refine.
  * simplify_option_eq; constructor; eauto.
    apply Forall2_replicate, pbit_empty_refine.
Qed.
Lemma ctree_singleton_refine Γ α f Δ1 Δ2 τ r w1 w2 σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ → w1 ⊑{Γ,α,f@Δ1↦Δ2} w2 : σ →
  ¬ctree_unmapped w1 → ¬ctree_unmapped w2 →
  ctree_singleton Γ r w1 ⊑{Γ,α,f@Δ1↦Δ2} ctree_singleton Γ r w2 : τ.
Proof.
  intros ? Hr. revert w1 w2. induction Hr using @ref_typed_ind;
    eauto 10 using ctree_singleton_seg_refine, ctree_singleton_seg_Forall_inv.
Qed.
End memory_trees.
