(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export list permission_bits_separation memory_trees.
Local Open Scope ctype_scope.

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

Local Arguments union _ _ !_ !_ /.
Local Hint Resolve Forall_take Forall_drop Forall_app_2 Forall_replicate: core.
Local Hint Resolve Forall2_take Forall2_drop Forall2_app: core.
Local Hint Immediate env_valid_lookup env_valid_lookup_lookup: core.
Local Hint Immediate ctree_typed_type_valid: core.
Local Hint Immediate TArray_valid_inv_type: core.

Ltac solve_length := simplify_equality'; repeat first 
  [ rewrite take_length | rewrite drop_length
  | rewrite app_length | rewrite cons_length | rewrite nil_length
  | rewrite fmap_length | erewrite ctree_flatten_length by eauto
  | rewrite type_mask_length by eauto | rewrite replicate_length
  | rewrite bit_size_of_int | rewrite int_width_char | rewrite resize_length
  | rewrite zip_with_length | erewrite sublist_lookup_length by eauto
  | rewrite insert_length | rewrite field_bit_padding_length by done
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
Local Hint Extern 0 (length _ = _) => solve_length: core.
Local Hint Extern 0 (_ = length _) => solve_length: core.
Local Hint Extern 0 (_ ≤ length _) => solve_length: core.
Local Hint Extern 0 (length _ ≤ _) => solve_length: core.

Lemma ctree_typed_subseteq Γ Δ w1 w2 τ :
  ✓ Γ → (Γ,Δ) ⊢ w2 : τ → w1 ⊆ w2 → (Γ,Δ) ⊢ w1 : τ.
Proof.
  intros ? Hw2 Hw. revert w1 w2 Hw τ Hw2.
  refine (ctree_subseteq_ind_alt _ _ _ _ _ _ _).
  * intros τb γbs1 γbs2 ?? Hw2; apply (ctree_typed_inv_l _ _ _ _ _ Hw2).
    typed_constructor; eauto using Forall2_length_r, pbits_subseteq_valid.
  * intros τ ws1 ws2 _ IH τ' Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ' Hw2.
    intros ? Hle; typed_constructor; eauto using Forall2_length, eq_sym.
    clear Hle. induction IH; decompose_Forall_hyps; auto.
  * intros t wγbss1 wγbss2 _ IH Hγbss τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    intros τs Ht Hws2 Hγbss2 Hindet Hlen. typed_constructor; eauto.
    + clear Hγbss Ht Hγbss2 Hlen. revert τs Hws2.
      induction IH; intros; decompose_Forall_hyps; auto.
    + clear IH Hws2 Hlen. induction Hγbss; decompose_Forall_hyps;
        eauto using pbits_subseteq_valid.
    + clear Hlen Hws2 IH Hγbss2. induction Hγbss; decompose_Forall_hyps;
        constructor; eauto using pbits_indetified_subseteq.
    + rewrite <-Hlen. clear IH Hws2 Hγbss2 Hlen Hindet.
      induction Hγbss; f_equal'; eauto using Forall2_length.
  * intros t i w1 w2 γbs1 γbs2 ? IH ? Hmap τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    typed_constructor; eauto using pbits_subseteq_valid,
      pbits_indetified_subseteq.
    by erewrite Forall2_length by eauto.
  * intros t γbs1 γbs2 ?? Hw2; apply (ctree_typed_inv_l _ _ _ _ _ Hw2).
    typed_constructor; eauto using Forall2_length_r, pbits_subseteq_valid.
  * intros t i γbs1 w2 γbs2 ??? Hmap τ Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2); clear τ Hw2.
    intros τs τ ???????. typed_constructor; eauto 1.
    + apply pbits_subseteq_valid with (ctree_flatten w2 ++ γbs2);
        eauto 3 using ctree_flatten_valid.
    + by erewrite Forall2_length, app_length, ctree_flatten_length by eauto.
Qed.
Lemma ctree_merge_typed Γ Δ w γbs τ :
  (Γ,Δ) ⊢ w : τ → ctree_flatten w ##* γbs → ✓{Γ,Δ}* γbs →
  Forall sep_unmapped γbs → (Γ,Δ) ⊢ ctree_merge (∪) w γbs : τ.
Proof.
  intros Hw. revert w τ Hw γbs. refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * typed_constructor; eauto using pbits_union_typed.
  * intros ws τ _ IH Hlen γbs Hγbs Hγbs' Hγbs''.
    typed_constructor; [| |done]; clear Hlen.
    { generalize γbs; elim ws; intros; f_equal'; auto. }
    revert γbs Hγbs Hγbs' Hγbs''; induction IH as [|w ws Hw _ IH]; csimpl; auto.
    intros γbs_; rewrite Forall2_app_inv_l; intros (γbs&γbs'&?&?&->) ??;
      decompose_Forall_hyps; rewrite take_app_alt, drop_app_alt by done; auto.
  * intros t wγbss τs Ht _ IH Hwγbss Hind Hlen γbs Hγbs Hγbs' Hγbs''.
    typed_constructor; eauto.
    + clear Ht Hwγbss Hind Hlen. revert γbs Hγbs Hγbs' Hγbs''.
      induction IH as [|[]]; intros; decompose_Forall_hyps;
        rewrite <-?(assoc_L (++)), ?take_app_alt, ?drop_app_alt,
        ?take_app_alt by done; constructor; simpl; auto.
    + clear Ht IH Hind Hlen Hγbs''. revert γbs Hγbs Hγbs'.
      induction Hwγbss as [|[]]; intros; decompose_Forall_hyps;
        rewrite <-?(assoc_L (++)), ?take_app_alt, ?drop_app_alt,
        ?take_app_alt by done; constructor; simpl; auto using pbits_union_typed.
    + clear Ht IH Hlen Hwγbss Hγbs'. revert γbs Hγbs Hγbs''.
      induction Hind as [|[]]; intros; decompose_Forall_hyps;
        rewrite <-?(assoc_L (++)), ?take_app_alt, ?drop_app_alt,
        ?take_app_alt by done; constructor; simpl; auto.
      rewrite pbits_indetify_union; f_equal; auto using pbits_indetify_unmapped.
    + rewrite <-Hlen; clear τs Ht Hlen Hwγbss Hind Hγbs' Hγbs'' IH.
      revert γbs Hγbs. induction wγbss as [|[]]; intros; decompose_Forall_hyps;
        rewrite <-?(assoc_L (++)), ?take_app_alt, ?drop_app_alt,
        ?take_app_alt by done; f_equal; auto.
  * intros t i τs w γbs1' τ ???????? γbs2_; rewrite Forall2_app_inv_l;
      intros (γbs2&γbs2'&?&?&->) ??; decompose_Forall_hyps.
    rewrite take_app_alt, drop_app_alt by done.
    typed_constructor; eauto using pbits_union_typed.
    + rewrite pbits_indetify_union, (pbits_indetify_unmapped γbs2') by done.
      congruence.
    + solve_length.
    + intuition eauto using @ctree_merge_mapped, @seps_unmapped_union_l.
  * typed_constructor; eauto using pbits_union_typed.
Qed.
Lemma ctree_union_type_of w1 w2 : w1 ## w2 → type_of (w1 ∪ w2) = type_of w1.
Proof. destruct 1; f_equal'; rewrite zip_with_length; auto. Qed.
Lemma ctree_union_typed Γ Δ w1 w2 τ :
  w1 ## w2 → (Γ,Δ) ⊢ w1 : τ → (Γ,Δ) ⊢ w2 : τ → (Γ,Δ) ⊢ w1 ∪ w2 : τ.
Proof.
  intros Hw. revert w1 w2 Hw τ. refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _).
  * intros τb γbs1 γbs2 ? τ Hw1 Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2);
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1).
    intros; typed_constructor; eauto using pbits_union_typed.
  * intros τ ws1 ws2 _ IH τ' Hw1 Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2);
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1 Hw2.
    intros Hws1 _ Hws2 Hlen; typed_constructor; eauto 2; clear Hlen.
    induction IH; decompose_Forall_hyps; eauto.
  * intros t wγbss1 wγbss2 Hws IH Hγbs τ' Hw1 Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2);
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1 Hw2.
    intros τs Ht Hws1 Hγbs1 Hind1 _ ?
      Ht' Hws2 Hγbs2 Hind2 Hlen2; simplify_option_eq.
    typed_constructor; eauto.
    + clear Ht Hws Hγbs Hγbs1 Hγbs2 Hind1 Hind2 Hlen2. revert τs Hws1 Hws2.
      induction IH as [|[] []]; intros; decompose_Forall_hyps; eauto.
    + clear τs Ht Hws IH Hws1 Hws2 Hind1 Hind2 Hlen2.
      induction Hγbs as [|[] []];
        decompose_Forall_hyps; eauto using pbits_union_typed.
    + clear τs Ht Hws IH Hws1 Hws2 Hγbs1 Hγbs2 Hlen2.
      induction Hγbs as [|[] []]; decompose_Forall_hyps; constructor; auto.
      simpl; rewrite pbits_indetify_union; congruence.
    + rewrite <-Hlen2. elim Hγbs; intros; f_equal'; auto.
  * intros t i w1 w2 γbs1 γbs2 ? IH Hγbs ?? τ' Hw1 Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2);
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1 Hw2.
    intros τs τ; intros; simplify_option_eq.
    typed_constructor; eauto using pbits_union_typed.
    + rewrite pbits_indetify_union; congruence.
    + solve_length.
    + intuition eauto using @ctree_unmapped_union_l, @seps_unmapped_union_l.
  * intros t γbs1 γbs2 ? τ Hw1 Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2);
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1).
    intros; typed_constructor; eauto using pbits_union_typed.
  * intros t i ? w2 γbs2; rewrite Forall2_app_inv_r;
      intros (γbs1&γbs1'&?&?&->) ? _ ? τ' Hw1 Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2);
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1 Hw2.
    intros τs ???? τ; intros; simplify_option_eq; decompose_Forall_hyps.
    rewrite take_app_alt, drop_app_alt by solve_length.
    typed_constructor; eauto 10 using pbits_union_typed, ctree_merge_typed.
    + rewrite pbits_indetify_union, (pbits_indetify_unmapped γbs1') by done.
      congruence.
    + solve_length.
    + intuition eauto using @ctree_merge_mapped, @seps_unmapped_union_l.
  * intros t i w1 γbs1' γbs2_; rewrite Forall2_app_inv_l;
      intros (γbs2&γbs2'&?&?&->) ? _ ? τ' Hw1 Hw2;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw2);
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear τ' Hw1 Hw2.
    intros τs ???? τ; intros; simplify_option_eq; decompose_Forall_hyps.
    rewrite take_app_alt, drop_app_alt by solve_length.
    typed_constructor; eauto 10 using pbits_union_typed, ctree_merge_typed.
    + rewrite pbits_indetify_union, (pbits_indetify_unmapped γbs2') by done.
      congruence.
    + solve_length.
    + intuition eauto using @ctree_merge_mapped, @seps_unmapped_union_l.
Qed.
Lemma ctree_disjoint_typed Γ Δ w1 w2 τ :
  ✓ Γ → w1 ## w2 → (Γ,Δ) ⊢ w1 : τ → ctree_unmapped w2 → (Γ,Δ) ⊢ w2 : τ.
Proof.
  intros ? Hw. revert w1 w2 Hw τ.
  refine (ctree_disjoint_ind_alt _ _ _ _ _ _ _ _); simpl.
  * intros τb ??? τ Hw; pattern τ; apply (ctree_typed_inv_l _ _ _ _ _ Hw).
    intros; constructor; eauto using pbits_disjoint_valid.
  * intros τ ws1 ws2 _ IH τ' Hw; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ' Hw; intros Hws2 Hlen ?.
    typed_constructor; auto. clear Hlen.
    revert τ Hws2. induction IH; intros; decompose_Forall_hyps; auto.
  * intros t wγbss1 wγbss2 _ IH Hγbs τ' Hw; pattern τ';
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ' Hw;
      intros τs Ht Hws2 Hγbs2 ? Hlen ?.
    typed_constructor; eauto.
    + clear Hlen Hγbs2 Ht. revert τs Hws2.
      induction IH; intros; decompose_Forall_hyps; auto.
    + clear Hlen Ht Hws2 IH.
      induction Hγbs; decompose_Forall_hyps; eauto using pbits_disjoint_valid.
    + clear Hlen Ht Hws2 Hγbs2 IH. induction Hγbs;
        decompose_Forall_hyps; eauto using pbits_disjoint_indetified.
    + rewrite <-Hlen. elim Hγbs; intros; f_equal'; auto.
  * intros; decompose_Forall_hyps; naive_solver.
  * intros t ??? τ Hw; pattern τ; apply (ctree_typed_inv_l _ _ _ _ _ Hw).
    intros. typed_constructor; eauto using pbits_disjoint_valid.
  * intros; decompose_Forall_hyps; naive_solver.
  * intros t i w1 γbs1 γbs2 ???? τ Hw; pattern τ;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw); clear τ Hw; intros τs τ; intros.
    assert (length γbs2 = bit_size_of Γ (unionT t)).
    { erewrite <-Forall2_length by eauto; auto. }
    econstructor; eauto using pbits_disjoint_valid, ctree_flatten_valid.
Qed.
Lemma ctree_unflatten_disjoint Γ τ γbs1 γbs2 :
  ✓ Γ → ✓{Γ} τ →
  γbs1 ##* γbs2 → ctree_unflatten Γ τ γbs1 ## ctree_unflatten Γ τ γbs2.
Proof.
  intros HΓ Hτ. revert τ Hτ γbs1 γbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite !ctree_unflatten_base. by constructor.
  * intros τ n _ IH _ γbs1 γbs2 Hγbs. rewrite !ctree_unflatten_array.
    constructor. revert γbs1 γbs2 Hγbs.
    induction n; simpl; intros; constructor; auto.
  * intros [] t τs Ht _ IH _ γbs1 γbs2 Hγbs;
      erewrite !ctree_unflatten_compound by eauto; constructor; auto.
    + revert γbs1 γbs2 Hγbs. clear Ht. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros;
        decompose_Forall_hyps; constructor; simpl; auto.
    + revert γbs1 γbs2 Hγbs. clear Ht IH. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros;
        constructor; simpl; auto using pbits_indetify_disjoint.
Qed.
Lemma ctree_unflatten_union Γ τ γbs1 γbs2 :
  ✓ Γ → ✓{Γ} τ → γbs1 ##* γbs2 → ctree_unflatten Γ τ (γbs1 ∪* γbs2)
  = ctree_unflatten Γ τ γbs1 ∪ ctree_unflatten Γ τ γbs2.
Proof.
  intros HΓ Hτ. revert τ Hτ γbs1 γbs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. by rewrite !ctree_unflatten_base.
  * intros τ n _ IH _ γbs1 γbs2 Hγbs. rewrite !ctree_unflatten_array; f_equal'.
    revert γbs1 γbs2 Hγbs. induction n; simpl; intros; f_equal';
      rewrite ?zip_with_take, ?zip_with_drop; auto.
  * intros [] t τs Ht _ IH _ γbs1 γbs2 Hγbs;
      erewrite !ctree_unflatten_compound by eauto; f_equal'; auto.
    revert γbs1 γbs2 Hγbs. clear Ht. unfold struct_unflatten.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps; repeat f_equal; simpl;
      rewrite ?fmap_drop, ?zip_with_take, ?pbits_indetify_union,
      ?zip_with_drop; eauto.
Qed.
Lemma ctree_unflatten_subseteq Γ τ γbs1 γbs2 :
  ✓ Γ → ✓{Γ} τ →
  γbs1 ⊆* γbs2 → ctree_unflatten Γ τ γbs1 ⊆ ctree_unflatten Γ τ γbs2.
Proof.
  intros. rewrite <-(seps_union_difference γbs1 γbs2) by done.
  rewrite ctree_unflatten_union; eauto using @seps_disjoint_difference.
  apply ctree_union_subseteq_l, ctree_unflatten_disjoint;
    eauto using @seps_disjoint_difference.
Qed.
Lemma ctree_flatten_unflatten_disjoint Γ Δ w τ ys :
  ✓ Γ → (Γ,Δ) ⊢ w : τ →
  ys ##* ctree_flatten w → Forall sep_unmapped ys → ctree_unflatten Γ τ ys ## w.
Proof.
  intros HΓ Hw. revert w τ Hw ys. refine (ctree_typed_ind _ _ _ _ _ _ _ _).
  * by constructor.
  * intros ws τ Hws IH _ ys Hys Hys'.
    rewrite ctree_unflatten_array; simplify_equality'. constructor.
    revert ys Hys Hys'. induction IH; intros; decompose_Forall_hyps;
      rewrite ?take_app_alt, ?drop_app_alt
        by (erewrite Forall2_length by eauto; auto); constructor; auto.
  * intros t wγbss τs Ht Hws IH _ ? Hlen ys Hys Hys';
      erewrite ctree_unflatten_compound by eauto; simplify_equality'.
    clear Ht. constructor; revert dependent wγbss; revert dependent ys;
      unfold field_bit_padding, struct_unflatten;
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
      rewrite ?take_app_alt, ?drop_app_alt
        by (erewrite ?app_length, !Forall2_length by eauto; solve_length);
      rewrite ?pbits_indetify_unmapped by auto; constructor; eauto.
  * intros t i τs w γbs τ ????????  ys Hys Hys';
      erewrite ctree_unflatten_compound by eauto; decompose_Forall_hyps.
    constructor; eauto using ctree_typed_sep_valid.
  * intros. erewrite ctree_unflatten_compound by eauto. by constructor.
Qed.
Lemma ctree_new_disjoint_l Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → ctree_new Γ ∅ τ ## w.
Proof.
  intros.
  eapply ctree_flatten_unflatten_disjoint; eauto using @sep_unmapped_empty.
  eapply Forall2_replicate_l, Forall_impl; eauto using ctree_flatten_valid.
  eauto using @sep_disjoint_empty_l, pbit_valid_sep_valid.
Qed.
Lemma ctree_new_disjoint_r Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → w ## ctree_new Γ ∅ τ.
Proof. intros; symmetry; eauto using ctree_new_disjoint_l. Qed.
Lemma ctree_new_union_l Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → ctree_new Γ ∅ τ ∪ w = w.
Proof. eauto using @ctree_left_id, ctree_new_disjoint_l, ctree_new_Forall. Qed.
Lemma ctree_new_union_r Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → w ∪ ctree_new Γ ∅ τ = w.
Proof. eauto using @ctree_right_id, ctree_new_disjoint_r, ctree_new_Forall. Qed.
Lemma ctrees_new_union_l Γ Δ ws τ n :
  ✓ Γ → (Γ,Δ) ⊢* ws : τ → length ws = n →
  replicate n (ctree_new Γ ∅ τ) ∪* ws = ws.
Proof.
  intros ? Hws <-. induction Hws; f_equal'; eauto using ctree_new_union_l.
Qed.
Lemma ctree_new_subseteq Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → ctree_new Γ ∅ τ ⊆ w.
Proof.
  intros. erewrite <-(ctree_new_union_l _ _ w) by eauto.
  eauto using @ctree_union_subseteq_l, ctree_new_disjoint_l.
Qed.
Lemma ctree_lookup_seg_disjoint Γ Δ1 Δ2 w1 w2 τ rs w1' w2' :
  ✓ Γ → (Γ,Δ1) ⊢ w1 : τ → (Γ,Δ2) ⊢ w2 : τ → w1 ## w2 →
  w1 !!{Γ} rs = Some w1' → w2 !!{Γ} rs = Some w2' → w1' ## w2'.
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
  ✓ Γ → (Γ,Δ1) ⊢ w1 : τ → (Γ,Δ2) ⊢ w2 : τ → w1 ## w2 →
  w1 !!{Γ} r = Some w1' → w2 !!{Γ} r = Some w2' → w1' ## w2'.
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
  * simplify_option_eq; eauto.
  * simplify_option_eq; eauto.
  * simplify_option_eq; eauto.
  * simplify_option_eq by eauto using @seps_unshared_weaken,
      @ctree_unshared_weaken; eexists; split;
      eauto using ctree_unflatten_subseteq, @ctree_flatten_subseteq.
  * simplify_option_eq by eauto using @seps_unshared_weaken;
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
  w1 ## w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ## w2' → g w1' ## w2') → ctree_alter_seg Γ g rs w1 ## w2.
Proof.
  intros ? Hw1 Hw Hw1' Hrs. revert w1 w2 Hw Hw1 Hw1' Hrs.
  refine (ctree_disjoint_ind _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros τ' ws1 ws2 ? _ ? Hrs Hg. destruct rs; simplify_option_eq.
    constructor. apply Forall2_alter_l; auto 1.
    intros; decompose_Forall_hyps; eauto.
  * intros t wγbss1 wγbss2 Hws Hγbss _ Hrs; destruct rs as [|i|];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros w1 γbs -> ? _ ?; simpl; constructor.
    + apply Forall2_alter_l; [elim Hws; constructor; simpl; eauto|].
      intros [??] [??] ??; decompose_Forall_hyps; eauto.
    + apply Forall2_alter_l; [elim Hγbss; constructor; simpl; eauto|].
      intros [??] [??] ??; decompose_Forall_hyps; eauto.
  * intros t i w1 w2 γbs1 γbs2 ? _ ??  Hum ? Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { intros; simplify_option_eq. constructor; naive_solver. }
    intros τs τ' ???????; destruct Hum; simplify_equality'.
    eauto using @seps_disjoint_unshared_unmapped, @ctree_flatten_disjoint.
  * intros t γbs1 γbs2 ? _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ??????; simplify_option_eq. constructor.
    + rewrite <-(take_drop (bit_size_of Γ τ') γbs2); apply Forall2_app.
      { erewrite <-pbits_indetify_mask_unmapped, <-(ctree_flatten_unflatten_le
          Γ τ') by eauto using @seps_disjoint_unshared_unmapped.
        eauto using @ctree_flatten_disjoint, ctree_unflatten_disjoint. }
      erewrite <-pbits_indetify_unmapped
        by eauto using @seps_disjoint_unshared_unmapped.
      eauto using pbits_indetify_disjoint.
    + eauto using @seps_disjoint_unshared_unmapped.
    + eapply ctree_disjoint_valid_l;
        eauto using ctree_flatten_disjoint, ctree_unflatten_disjoint.
    + naive_solver.
  * intros t i γbs1 w2 γbs2 ??? Hum _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ????; destruct Hum; simplify_equality.
    rewrite <-Forall_app; eauto using @seps_disjoint_unshared_unmapped.
  * intros t i w1 γbs1 γbs2 Hγbs2 ??? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs τ ??? _ ? _; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { rewrite Forall2_app_inv_l in Hγbs2;
        destruct Hγbs2 as (γbs2'&γbs2''&?&?&->).
      intros ???? Hw; simplify_option_eq; decompose_Forall_hyps.
      constructor; auto.
      + apply Forall2_app; auto.
        erewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) γbs2'),
          <-(ctree_flatten_unflatten Γ τ γbs2') by
          (erewrite <-?(Forall2_length _ (ctree_flatten _)) by eauto; eauto).
        apply ctree_flatten_disjoint, Hw.
        symmetry; eauto using ctree_flatten_unflatten_disjoint.
      + eapply ctree_disjoint_valid_l, Hw.
        symmetry; eauto using ctree_flatten_unflatten_disjoint.
      + naive_solver. }
    intros ? τ' ?????????; simplify_option_eq. constructor; auto.
    + rewrite <-(take_drop (bit_size_of Γ τ') γbs2); apply Forall2_app; auto.
      { erewrite <-pbits_indetify_mask_unmapped, <-(ctree_flatten_unflatten_le
          Γ τ') by eauto using @seps_disjoint_unshared_unmapped.
        eauto using @ctree_flatten_disjoint, ctree_unflatten_disjoint. }
      erewrite <-pbits_indetify_unmapped
        by eauto using @seps_disjoint_unshared_unmapped.
      eauto using pbits_indetify_disjoint.
    + eapply ctree_disjoint_valid_l;
        eauto using ctree_flatten_disjoint, ctree_unflatten_disjoint.
    + naive_solver.
Qed.
Lemma ctree_alter_disjoint Γ Δ g w1 w2 τ r w1' :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ →
  w1 ## w2 → w1 !!{Γ} r = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ## w2' → g w1' ## w2') → ctree_alter Γ g r w1 ## w2.
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
  w1 ## w2 → w1 !!{Γ} rs = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ## w2' → g w1' ## w2') →
  (∀ w2', w1' ## w2' → g (w1' ∪ w2') = g w1' ∪ w2') →
  ctree_alter_seg Γ g rs (w1 ∪ w2) = ctree_alter_seg Γ g rs w1 ∪ w2.
Proof.
  intros ? Hw1 Hw Hw1' Hrs. revert w1 w2 Hw Hw1 Hw1' Hrs.
  refine (ctree_disjoint_ind _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros τ' ws1 ws2 Hws _ Hrs  _ Hg Hg'.
    destruct rs as [i| |]; simplify_option_eq. f_equal. revert i Hrs.
    induction Hws; intros [|?] ?; simplify_equality'; f_equal'; eauto.
  * intros t wγbss1 wγbss2 Hws _ _ Hrs; destruct rs as [|i|];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros w1 γbs -> Hrs _ Hg Hg'; f_equal'. revert i Hrs.
    induction Hws as [|[] []]; intros [|?] ?;
      simplify_equality'; repeat f_equal'; eauto.
  * intros t i w1 w2 γbs1 γbs2 ? _ ??  Hum ? Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { intros; simplify_option_eq; f_equal; auto. }
    intros τs τ' ???????; destruct Hum; simplify_equality'.
    eauto using @seps_disjoint_unshared_unmapped, @ctree_flatten_disjoint.
  * intros t γbs1 γbs2 ? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs ??? _; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros ?????? Hg Hg'; simplify_option_eq.
    erewrite Forall2_length by (eapply ctree_flatten_disjoint,
      Hg, ctree_unflatten_disjoint; eauto).
    rewrite ctree_flatten_unflatten_le, mask_length, take_length_le by eauto.
    f_equal.
    + by rewrite zip_with_take, ctree_unflatten_union, Hg',
        <-ctree_merge_flatten, ctree_flatten_unflatten_le,
        pbits_indetify_mask_unmapped
        by eauto using ctree_unflatten_Forall_le, ctree_unflatten_disjoint,
          @seps_disjoint_unshared_unmapped, pbit_unmapped_indetify.
    + by rewrite zip_with_drop, pbits_indetify_union, (pbits_indetify_unmapped
        (drop _ γbs2)) by eauto using @seps_disjoint_unshared_unmapped.
  * intros t i γbs1 w2 γbs2 ??? Hum _ Hrs; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    intros τs τ' ????; destruct Hum; simplify_equality.
    rewrite <-Forall_app; eauto using @seps_disjoint_unshared_unmapped.
  * intros t i w1 γbs1 γbs2 Hγbs2 ??? Hw1 Hrs;
      apply (ctree_typed_inv_l _ _ _ _ _ Hw1); clear Hw1 τ;
      intros τs τ ?? Hw1 _ ??; destruct rs as [| |i'];
      pattern w1'; apply (ctree_lookup_seg_inv _ _ _ _ _ Hrs); clear Hrs.
    { rewrite Forall2_app_inv_l in Hγbs2;
        destruct Hγbs2 as (γbs2'&γbs2''&?&?&->).
      intros ???? Hg Hg'; simplify_option_eq; decompose_Forall_hyps.
      assert (length γbs2' = bit_size_of Γ τ).
      { erewrite <-Forall2_length by eauto. solve_length. }
      assert (w1 ## ctree_unflatten Γ τ γbs2').
      { symmetry; eauto using ctree_flatten_unflatten_disjoint. }
      assert (ctree_flatten (g w1) ##* γbs2').
      { rewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) γbs2'),
          <-ctree_flatten_unflatten by eauto.
        by apply ctree_flatten_disjoint, Hg. }
      clear Hw1. rewrite !take_app_alt, !drop_app_alt by auto.
      rewrite <-(pbits_indetify_mask_unmapped (type_mask Γ τ) γbs2'),
        <-ctree_flatten_unflatten, !ctree_merge_flatten
        by eauto using ctree_unflatten_Forall_le, pbit_unmapped_indetify.
      f_equal; auto. }
    intros ? τ' ????????? Hg Hg'; simplify_option_eq.
    assert (length γbs2 = bit_size_of Γ (unionT t)).
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
        @seps_disjoint_unshared_unmapped, pbit_unmapped_indetify.
    + by rewrite pbits_indetify_union,
       (pbits_indetify_unmapped (drop _ γbs2)) by auto.
Qed.
Lemma ctree_alter_union Γ Δ g w1 w2 τ r w1' :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ →
  w1 ## w2 → w1 !!{Γ} r = Some w1' → ¬ctree_unmapped (g w1') →
  (∀ w2', w1' ## w2' → g w1' ## w2') →
  (∀ w2', w1' ## w2' → g (w1' ∪ w2') = g w1' ∪ w2') →
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
  ✓ Γ → w1 ## w2 → w1 !!{Γ} i = Some c1 → w2 !!{Γ} i = Some c2 → c1 ## c2.
Proof.
  unfold lookupE, ctree_lookup_byte, sublist_lookup; intros;
    simplify_option_eq; auto using ctree_unflatten_disjoint,
    TBase_valid, TInt_valid, @ctree_flatten_disjoint.
Qed.
Lemma ctree_lookup_byte_subseteq Γ w1 w2 i c1 :
  ✓ Γ → w1 ⊆ w2 → w1 !!{Γ} i = Some c1 →
  ∃ c2, w2 !!{Γ} i = Some c2 ∧ c1 ⊆ c2.
Proof.
  unfold lookupE, ctree_lookup_byte. intros.
  destruct (sublist_lookup _ _ (ctree_flatten w1))
    as [γbs1|] eqn:Hbs1; simplify_equality'.
  destruct (Forall2_sublist_lookup_l (⊆) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits γbs1) as (γbs2&?&?);
    eauto using @ctree_flatten_subseteq.
  exists (ctree_unflatten Γ ucharT γbs2); simplify_option_eq;
    eauto using ctree_unflatten_subseteq, TBase_valid, TInt_valid.
Qed.
Lemma ctree_alter_byte_disjoint Γ Δ g w1 w2 τ i c1 :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ → ctree_unshared w1 → w1 ## w2 → w1 !!{Γ} i = Some c1 →
  (∀ c2, c1 ## c2 → g c1 ## c2) → ctree_alter_byte Γ g i w1 ## w2.
Proof.
  unfold lookupE, ctree_alter_byte, ctree_lookup_byte; intros ???? Hw1 ?.
  destruct (sublist_lookup _ _ _) as [γbs1|] eqn:?; simplify_type_equality'.
  assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,Δ) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2), <-ctree_unflatten_flatten by eauto.
  destruct (Forall2_sublist_lookup_l (##) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits γbs1) as (γbs2&?&?);
    eauto using @ctree_flatten_disjoint.
  eapply ctree_unflatten_disjoint, Forall2_sublist_alter_l;
    eauto using @ctree_flatten_disjoint; simpl.
  rewrite <-(mask_false pbit_indetify γbs2 (bit_size_of Γ ucharT)),
    <-type_mask_base, <-ctree_flatten_unflatten
    by eauto using TBase_valid, TInt_valid.
  eauto using @ctree_flatten_disjoint,
    ctree_unflatten_disjoint, TBase_valid, TInt_valid.
Qed.
Lemma ctree_alter_byte_union Γ Δ g w1 w2 τ i c1 :
  ✓ Γ → (Γ,Δ) ⊢ w1 : τ → ctree_unshared w1 → w1 ## w2 → w1 !!{Γ} i = Some c1 →
  (∀ c2, c1 ## c2 → g c1 ## c2) → (∀ c2, c1 ## c2 → g (c1 ∪ c2) = g c1 ∪ c2) →
  ctree_alter_byte Γ g i (w1 ∪ w2) = ctree_alter_byte Γ g i w1 ∪ w2.
Proof.
  unfold lookupE, ctree_alter_byte, ctree_lookup_byte; intros ????? Hg Hg'.
  rewrite ctree_union_type_of by done.
  destruct (sublist_lookup _ _ _) as [γbs1|] eqn:?; simplify_type_equality'.
  assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,Δ) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2) at 2 by eauto.
  erewrite <-ctree_unflatten_flatten by eauto.
  destruct (Forall2_sublist_lookup_l (##) (ctree_flatten w1)
    (ctree_flatten w2) (i * char_bits) char_bits γbs1) as (γbs2&?&?);
    auto using @ctree_flatten_disjoint.
  assert (ctree_flatten (g (ctree_unflatten Γ ucharT γbs1)) ##* γbs2).
  { rewrite <-(mask_false pbit_indetify γbs2 (bit_size_of Γ ucharT)),
      <-type_mask_base, <-ctree_flatten_unflatten
      by eauto using TBase_valid, TInt_valid.
    eauto using @ctree_flatten_disjoint,
      ctree_unflatten_disjoint, TBase_valid, TInt_valid. }
  assert (sublist_alter (ctree_flatten ∘ g ∘ ctree_unflatten Γ ucharT)
    (i * char_bits) char_bits (ctree_flatten w1) ##* ctree_flatten w2).
  { eapply Forall2_sublist_alter_l; eauto using @ctree_flatten_disjoint. }
  rewrite <-ctree_unflatten_union, ctree_flatten_union by eauto; f_equal.
  symmetry; apply zip_with_sublist_alter with γbs1 γbs2; simpl; auto 1.
  by rewrite ctree_unflatten_union, Hg', ctree_flatten_union,
    ctree_flatten_unflatten, type_mask_base, mask_false by eauto using
    ctree_unflatten_disjoint, TBase_valid, TInt_valid.
Qed.
Lemma ctree_singleton_seg_disjoint Γ Δ τ rs w1 w2 σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ →
  w1 ## w2 → (Γ,Δ) ⊢ w1 : σ → (Γ,Δ) ⊢ w2 : σ →
  ctree_singleton_seg Γ rs w1 ## ctree_singleton_seg Γ rs w2.
Proof.
  intros ? Hrs ???.
  assert (∀ τ, ✓{Γ} τ → ctree_new Γ ∅ τ ## ctree_new Γ ∅ τ).
  { intros. apply ctree_new_disjoint_l with ∅;
      eauto using ctree_new_typed, pbit_empty_valid. }
  destruct Hrs as [τ i n _|s i τs τ Ht _|s i]; simplify_option_eq.
  * constructor. apply Forall2_insert; eauto using Forall2_replicate.
  * constructor.
    + apply Forall2_fmap; rewrite !fst_zip by auto.
      eauto using Forall2_insert, Forall2_fmap_2, Forall_Forall2_diag, Forall_impl.
    + apply Forall2_fmap; rewrite !snd_zip by auto.
      apply Forall2_fmap_2, Forall_Forall2_diag, Forall_true; simpl.
      auto using Forall2_replicate, @sep_disjoint_empty_l, @sep_empty_valid.
  * constructor. eapply Forall2_resize; eauto using
      @ctree_flatten_disjoint, @sep_disjoint_empty_l, @sep_empty_valid.
  * constructor; intuition eauto using ctree_typed_sep_valid,
      Forall_resize, @sep_unmapped_empty.
    erewrite resize_ge, ctree_flatten_length by eauto.
    eauto 10 using Forall2_app, Forall2_replicate,
      @sep_disjoint_empty_l, @sep_empty_valid, @ctree_flatten_disjoint.
  * constructor; intuition eauto using ctree_typed_sep_valid,
      Forall_resize, @sep_unmapped_empty.
    erewrite resize_ge, ctree_flatten_length by eauto.
    eauto 10 using Forall2_app, Forall2_replicate,
      @sep_disjoint_empty_l, @sep_empty_valid, @ctree_flatten_disjoint.
  * constructor; naive_solver auto using Forall2_replicate,
      @sep_disjoint_empty_l, @sep_empty_valid.
Qed.
Lemma ctree_singleton_disjoint Γ Δ τ r w1 w2 σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ →
  w1 ## w2 → (Γ,Δ) ⊢ w1 : σ → (Γ,Δ) ⊢ w2 : σ →
  ctree_singleton Γ r w1 ## ctree_singleton Γ r w2.
Proof.
  intros ? Hr. revert w1 w2.
  induction Hr using @ref_typed_ind; eauto 15 using ref_typed_type_valid,
    ctree_singleton_seg_disjoint, ctree_singleton_seg_typed.
Qed.
Lemma ctree_singleton_seg_disjoint_rev Γ Δ τ rs w1 w2 σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ → (Γ,Δ) ⊢ w1 : σ → (Γ,Δ) ⊢ w2 : σ →
  ctree_singleton_seg Γ rs w1 ## ctree_singleton_seg Γ rs w2 → w1 ## w2.
Proof.
  intros ? Hrs ?? Hw.
  destruct Hrs as [τ i n ?|s i τs τ Ht ?|s i];
    simplify_option_eq; inversion_clear Hw;
    repeat match goal with
    | H : resize _ _ _ ##* _ |- _ => rewrite resize_ge in H by auto
    | H : _ ##* resize _ _ _ |- _ => rewrite resize_ge in H by auto
    | H : _ ##1* _ |- _ => apply Forall2_fmap in H; rewrite !fst_zip in H by auto
    end; decompose_Forall_hyps.
  * eapply Forall2_lookup_lr; eauto using list_lookup_insert.
  * assert (i < length τs) by eauto using lookup_lt_Some.
    eapply Forall2_lookup_lr; eauto using list_lookup_insert.
  * erewrite <-(union_free_reset w1), <-(union_free_reset w2),
      <-!ctree_unflatten_flatten by eauto using union_free_unmapped,
      ctree_typed_sep_valid; eauto using ctree_unflatten_disjoint.
  * erewrite <-(union_free_reset w1), <-ctree_unflatten_flatten
      by eauto using union_free_unmapped, ctree_typed_sep_valid.
    eauto using ctree_flatten_unflatten_disjoint.
  * erewrite <-(union_free_reset w2), <-ctree_unflatten_flatten
      by eauto using union_free_unmapped, ctree_typed_sep_valid.
    symmetry; eauto using ctree_flatten_unflatten_disjoint.
  * done.
Qed.
Lemma ctree_singleton_disjoint_rev Γ Δ τ r w1 w2 σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ → (Γ,Δ) ⊢ w1 : σ → (Γ,Δ) ⊢ w2 : σ →
  ctree_singleton Γ r w1 ## ctree_singleton Γ r w2 → w1 ## w2.
Proof.
  intros ? Hr. revert w1 w2.
  induction Hr using @ref_typed_ind; eauto 15 using ref_typed_type_valid,
    ctree_singleton_seg_disjoint_rev, ctree_singleton_seg_typed.
Qed.
Lemma ctree_singleton_seg_union Γ Δ τ rs w1 w2 σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ →
  w1 ## w2 → (Γ,Δ) ⊢ w1 : σ → (Γ,Δ) ⊢ w2 : σ →
  ctree_singleton_seg Γ rs (w1 ∪ w2)
  = ctree_singleton_seg Γ rs w1 ∪ ctree_singleton_seg Γ rs w2.
Proof.
  intros ? Hrs ???.
  assert (∀ n, replicate n (∅ : pbit K) ∪* replicate n ∅ = replicate n ∅).
  { intros. by rewrite zip_with_replicate_l, fmap_replicate by solve_length. }
  assert (∀ τ, ✓{Γ} τ → ctree_new Γ ∅ τ = ctree_new Γ ∅ τ ∪ ctree_new Γ ∅ τ).
  { intros. symmetry. eapply ctree_new_union_l with ∅;
      eauto using ctree_new_typed, pbit_empty_valid. }
  destruct Hrs as [τ i n _|s i τs τ Ht _|s i];
    simplify_option_eq by (eauto using @ctree_unmapped_union_l,
    @ctree_unmapped_union_r, @ctree_unmapped_union); f_equal.
  * revert i.
    induction (Forall_replicate (ctree_new Γ ∅ τ =.) n _ eq_refl)
      as [|w ws ? Hws]; subst; intros [|?]; f_equal'; eauto.
    elim Hws; intros; simplify_equality'; f_equal'; eauto.
  * assert (Forall2 (λ _ τ, ✓{Γ} τ) (field_bit_padding Γ τs) τs) as Hτs.
    { cut (✓{Γ}* τs); [clear Ht|by eauto].
      assert (Forall2 (λ _ _, True) (field_bit_padding Γ τs) τs) as Hτs.
      { apply Forall2_same_length; auto using field_bit_padding_length. }
      induction Hτs; intros; decompose_Forall_hyps; auto. }
    clear Ht. revert i.
    induction Hτs as [|? τ' ? τs ? Hτs]; intros [|i]; repeat f_equal';
      decompose_Forall_hyps; auto.
    elim Hτs; intros; repeat f_equal'; auto.
  * erewrite ctree_flatten_union, !resize_ge, zip_with_app, zip_with_length_l,
      <-Forall2_length by eauto using @ctree_flatten_disjoint; f_equal; auto.
  * by erewrite resize_ge, take_app_alt,
      ctree_merge_flatten, ctree_commutative by eauto.
  * erewrite <-Forall2_length by eauto using @ctree_flatten_disjoint.
    erewrite resize_ge, drop_app_alt, ctree_flatten_length by eauto; eauto.
  * by erewrite resize_ge, take_app_alt,
      ctree_merge_flatten, ctree_commutative by eauto.
  * erewrite Forall2_length by eauto using @ctree_flatten_disjoint.
    erewrite resize_ge, drop_app_alt, ctree_flatten_length by eauto; eauto.
  * done.
Qed.
Lemma ctree_singleton_union Γ Δ τ r w1 w2 σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ →
  w1 ## w2 → (Γ,Δ) ⊢ w1 : σ → (Γ,Δ) ⊢ w2 : σ →
  ctree_singleton Γ r (w1 ∪ w2)
  = ctree_singleton Γ r w1 ∪ ctree_singleton Γ r w2.
Proof.
  intros ? Hr; revert w1 w2.
  induction Hr as [|r rs τ1 τ2 τ3] using @ref_typed_ind; intros; simpl; auto.
  erewrite (ctree_singleton_seg_union _ _ τ2)
    by eauto using ref_typed_type_valid.
  eauto 15 using ctree_singleton_seg_typed, ctree_singleton_seg_disjoint.
Qed.
Lemma ctree_singleton_seg_array Γ Δ ws τ j n :
  ✓ Γ → (Γ,Δ) ⊢* ws : τ → length ws + j ≤ n →
  foldr (∪) (ctree_new Γ ∅ (τ.[n]))
    (imap_go (λ i, ctree_singleton_seg Γ (RArray i τ n)) j ws)
  = MArray τ (list_inserts j ws (replicate n (ctree_new Γ ∅ τ))).
Proof.
  intros ? Hws. revert j.
  induction Hws as [|w ws Hw Hws IH]; csimpl; intros j Hj.
  { by rewrite ctree_new_array. }
  rewrite IH by lia; clear IH; f_equal'. pattern n at 1 3.
  erewrite <-(insert_replicate _ n j), <-list_insert_inserts_lt,
    <-insert_zip_with, ctree_new_union_r by eauto with lia.
  by erewrite ctrees_new_union_l by (rewrite ?inserts_length; eauto using
   Forall_inserts, Forall_replicate, ctree_new_typed, pbit_empty_valid).
Qed.
End memory_trees.
