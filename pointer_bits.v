(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import fragmented.
Require Export pointers.

Notation ptr_bit Ti := (fragment (ptr Ti)).

Section pointer_bit_operations.
  Context `{Env Ti}.

  Global Instance ptr_bit_valid:
      Valid (env Ti * memenv Ti) (ptr_bit Ti) := λ Γm pb, ∃ τ,
    let (Γ,Γm) := Γm in
    (Γ,Γm) ⊢ frag_item pb : τ ∧
    frozen (frag_item pb) ∧
    frag_index pb < bit_size_of Γ (τ.*).
  Definition ptr_to_bits (Γ : env Ti) (p : ptr Ti) : list (ptr_bit Ti) :=
    to_fragments (bit_size_of Γ (type_of p.*)) (freeze true p).
  Definition ptr_of_bits (Γ : env Ti) (τ : type Ti)
      (pbs : list (ptr_bit Ti)) : option (ptr Ti) :=
    p ← of_fragments (bit_size_of Γ (τ.*)) pbs;
    guard (type_of p = τ); Some p.

  Global Instance ptr_bit_refine:
      Refine Ti (env Ti) (ptr_bit Ti) := λ Γ f Γm1 Γm2 pb1 pb2, ∃ τ,
    frag_item pb1 ⊑{Γ,f@Γm1↦Γm2} frag_item pb2 : τ ∧
    frag_index pb1 = frag_index pb2 ∧
    frozen (frag_item pb1) ∧
    frag_index pb1 < bit_size_of Γ (τ.*).
End pointer_bit_operations.

Section pointer_bits.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ : type Ti.
Implicit Types p : ptr Ti.
Implicit Types pb : ptr_bit Ti.
Implicit Types pbs : list (ptr_bit Ti).

Global Instance ptr_bit_valid_dec ΓΓm (pb : ptr_bit Ti) : Decision (✓{ΓΓm} pb).
Proof.
 refine
  match Some_dec (type_check ΓΓm (frag_item pb)) with
  | inleft (τ↾Hτ) => cast_if_and (decide (frozen (frag_item pb)))
     (decide (frag_index pb < bit_size_of (ΓΓm.1) (τ.*)))
  | inright Hτ => right _
  end; abstract (destruct ΓΓm; first
  [ simplify_type_equality; econstructor; eauto
  | by destruct 1 as (?&?&?&?); simplify_type_equality ]).
Defined.
Lemma ptr_bit_valid_weaken Γ1 Γ2 Γm1 Γm2 pb :
  ✓ Γ1 → ✓{Γ1,Γm1} pb → Γ1 ⊆ Γ2 → Γm1 ⊆{⇒} Γm2 → ✓{Γ2,Γm2} pb.
Proof.
  intros ? (τ&?&?&?) ??. exists τ. erewrite <-bit_size_of_weaken
    by eauto using TBase_valid, TPtr_valid, ptr_typed_type_valid.
  eauto using ptr_typed_weaken.
Qed.
Lemma ptr_to_bits_freeze Γ q p : ptr_to_bits Γ (freeze q p) = ptr_to_bits Γ p.
Proof. unfold ptr_to_bits. by rewrite ptr_freeze_type_of,ptr_freeze_freeze. Qed.
Lemma ptr_to_bits_length_alt Γ p :
  length (ptr_to_bits Γ p) = bit_size_of Γ (type_of p.* ).
Proof. unfold ptr_to_bits. by rewrite (to_fragments_length _). Qed.
Lemma ptr_to_bits_length Γ Γm p τ :
  (Γ,Γm) ⊢ p : τ → length (ptr_to_bits Γ p) = bit_size_of Γ (τ.* ).
Proof. intros. erewrite ptr_to_bits_length_alt, type_of_correct; eauto. Qed.
Lemma ptr_to_bits_valid Γ Γm p τ : (Γ,Γm) ⊢ p : τ → ✓{Γ,Γm}* (ptr_to_bits Γ p).
Proof.
  intros. apply (Forall_to_fragments _).
  intros i. erewrite type_of_correct by eauto. exists τ; simpl.
  rewrite ptr_typed_freeze. unfold frozen. by rewrite ptr_freeze_freeze.
Qed.
Lemma ptr_of_bits_Exists_Forall_typed Γ Γm τ pbs :
  is_Some (ptr_of_bits Γ τ pbs) → Exists ✓{Γ,Γm} pbs → ✓{Γ,Γm}* pbs.
Proof.
  unfold ptr_of_bits; intros [p ?]; simplify_option_equality.
  rewrite <-(of_to_fragments_1 _ p pbs) by eauto; unfold to_fragments at 1.
  rewrite Exists_fmap, Exists_exists.
  intros (i&?&?&?&?&?); simplify_type_equality'.
  apply (Forall_to_fragments _); eexists; eauto.
Qed.
Lemma ptr_of_bits_typed_frozen Γ Γm p τ pbs :
  ptr_of_bits Γ τ pbs = Some p → ✓{Γ,Γm}* pbs → (Γ,Γm) ⊢ p : τ ∧ frozen p.
Proof.
  unfold ptr_of_bits; intros; simplify_option_equality.
  destruct (Forall_of_fragments (bit_size_of Γ (type_of p.* ))
    (✓{Γ,Γm}) p pbs 0) as (?&?&?&?); eauto using type_of_typed.
  by apply Nat.neq_0_lt_0, bit_size_of_base_ne_0.
Qed.
Lemma ptr_of_bits_typed Γ Γm p τ pbs :
  ptr_of_bits Γ τ pbs = Some p → ✓{Γ,Γm}* pbs → (Γ,Γm) ⊢ p : τ.
Proof. intros. eapply ptr_of_bits_typed_frozen; eauto. Qed.
Lemma ptr_of_bits_frozen Γ Γm p τ pbs :
  ptr_of_bits Γ τ pbs = Some p → ✓{Γ,Γm}* pbs → frozen p.
Proof. intros. eapply ptr_of_bits_typed_frozen; eauto. Qed.
Lemma ptr_of_bits_type_of Γ p τ pbs :
  ptr_of_bits Γ τ pbs = Some p → type_of p = τ.
Proof. by unfold ptr_of_bits; intros; simplify_option_equality. Qed.
Lemma ptr_to_of_bits Γ Γm p τ pbs :
  ptr_of_bits Γ τ pbs = Some p → ✓{Γ,Γm}* pbs → ptr_to_bits Γ p = pbs.
Proof.
  intros. assert (frozen p) as Hp by eauto using ptr_of_bits_frozen.
  unfold ptr_of_bits, ptr_to_bits in *.
  destruct (of_fragments _ _) eqn:?; simplify_option_equality.
  by rewrite Hp, (of_to_fragments_1 _ _ pbs) by done.
Qed.
Lemma ptr_of_to_bits Γ p :
  ptr_of_bits Γ (type_of p) (ptr_to_bits Γ p) = Some (freeze true p).
Proof.
  unfold ptr_of_bits, ptr_to_bits. rewrite (of_to_fragments_2 _); csimpl.
  rewrite ptr_freeze_type_of. by simplify_option_equality.
Qed.
Lemma ptr_of_to_bits_typed Γ Γm p τ :
  (Γ,Γm) ⊢ p : τ → ptr_of_bits Γ τ (ptr_to_bits Γ p) = Some (freeze true p).
Proof. intros. by erewrite <-(ptr_of_to_bits Γ), type_of_correct by eauto. Qed.
Lemma ptr_of_bits_length Γ τ pbs p :
  ptr_of_bits Γ τ pbs = Some p → length pbs = bit_size_of Γ (τ.*).
Proof.
  unfold ptr_of_bits. intros. simplify_option_equality.
  by erewrite <-(of_to_fragments_1 _ _ pbs), to_fragments_length by eauto.
Qed.
Lemma ptr_to_bits_weaken Γ1 Γ2 Γm p τ :
  ✓ Γ1 → (Γ1,Γm) ⊢ p : τ → Γ1 ⊆ Γ2 → ptr_to_bits Γ1 p = ptr_to_bits Γ2 p.
Proof.
  intros. unfold ptr_to_bits. by erewrite !type_of_correct, bit_size_of_weaken
    by eauto using TBase_valid, TPtr_valid, ptr_typed_type_valid.
Qed.
Lemma ptr_of_bits_weaken Γ1 Γ2 τ pbs :
  ✓ Γ1 → ptr_type_valid Γ1 τ → Γ1 ⊆ Γ2 →
  ptr_of_bits Γ1 τ pbs = ptr_of_bits Γ2 τ pbs.
Proof.
  intros. unfold ptr_of_bits. by erewrite bit_size_of_weaken
    by eauto using TBase_valid, TPtr_valid.
Qed.
Lemma ptr_to_bits_alive Γ Γm p :
  ptr_alive Γm p →
  Forall (λ pb, ptr_alive Γm (fragmented.frag_item pb)) (ptr_to_bits Γ p).
Proof.
  unfold ptr_to_bits. intros. apply (Forall_to_fragments _).
  intros i _. by destruct p; simpl in *; rewrite ?addr_index_freeze.
Qed.
Lemma ptr_to_bits_dead Γ Γm p :
  ¬ptr_alive Γm p →
  Forall (λ pb, ¬ptr_alive Γm (fragmented.frag_item pb)) (ptr_to_bits Γ p).
Proof.
  unfold ptr_to_bits. intros. apply (Forall_to_fragments _).
  intros i _. by destruct p; simpl in *; rewrite ?addr_index_freeze.
Qed.

(** ** Refinements *)
Lemma ptr_bit_refine_id Γ Γm pb : ✓{Γ,Γm} pb → pb ⊑{Γ@Γm} pb.
Proof. intros (σ&?&?&?); exists σ; eauto using ptr_refine_id. Qed.
Lemma ptr_bit_refine_compose Γ f g Γm1 Γm2 Γm3 pb1 pb2 pb3 :
  ✓ Γ →
  pb1 ⊑{Γ,f@Γm1↦Γm2} pb2 → pb2 ⊑{Γ,g@Γm2↦Γm3} pb3 → pb1 ⊑{Γ,f ◎ g@Γm1↦Γm3} pb3.
Proof.
  intros ? (τ1&?&?&?&?) (τ2&?&?&?&?); exists τ1.
  assert (τ1 = τ2) by (by erewrite <-(ptr_refine_type_of_r _ _ _ _ _ _ τ1),
    <-(ptr_refine_type_of_l _ _ _ _ _ _ τ2) by eauto); subst.
  eauto using ptr_refine_compose with congruence.
Qed.
Lemma ptr_bit_refine_weaken Γ Γ' f f' Γm1 Γm2 Γm1' Γm2' pb1 pb2 :
  ✓ Γ → pb1 ⊑{Γ,f@Γm1↦Γm2} pb2 → Γ ⊆ Γ' → Γ ⊆ Γ' → Γm1' ⊑{Γ',f'} Γm2' →
  Γm1 ⊆{⇒} Γm1' → meminj_extend f f' Γm1 Γm2 → pb1 ⊑{Γ',f'@Γm1'↦Γm2'} pb2.
Proof.
  intros ? (τ&?&?&?&?) ??. exists τ.
  erewrite <-bit_size_of_weaken by eauto using TBase_valid, TPtr_valid,
    ptr_refine_typed_l, ptr_typed_type_valid; eauto using ptr_refine_weaken.
Qed.
Lemma ptr_bit_refine_valid_l Γ f Γm1 Γm2 pb1 pb2 :
  ✓ Γ → pb1 ⊑{Γ,f@Γm1↦Γm2} pb2 → ✓{Γ,Γm1} pb1.
Proof. intros ? (τ&?&?&?&?). exists τ; eauto using ptr_refine_typed_l. Qed.
Lemma ptr_bit_refine_valid_r Γ Γm1 Γm2 f pb1 pb2 :
  ✓ Γ → pb1 ⊑{Γ,f@Γm1↦Γm2} pb2 → ✓{Γ,Γm2} pb2.
Proof.
  intros ? (τ&?&?&?&?); exists τ; erewrite <-ptr_refine_frozen by eauto;
    eauto using ptr_refine_typed_r with congruence.
Qed.
Lemma ptr_bits_refine_valid_l Γ f Γm1 Γm2 pbs1 pbs2 :
  ✓ Γ → pbs1 ⊑{Γ,f@Γm1↦Γm2}* pbs2 → ✓{Γ,Γm1}* pbs1.
Proof. induction 2; eauto using ptr_bit_refine_valid_l. Qed.
Lemma ptr_bits_refine_valid_r Γ f Γm1 Γm2 pbs1 pbs2 :
  ✓ Γ → pbs1 ⊑{Γ,f@Γm1↦Γm2}* pbs2 → ✓{Γ,Γm2}* pbs2.
Proof. induction 2; eauto using ptr_bit_refine_valid_r. Qed.
Lemma ptr_bit_refine_unique Γ f Γm1 Γm2 pb1 pb2 pb3 :
  pb1 ⊑{Γ,f@Γm1↦Γm2} pb2 → pb1 ⊑{Γ,f@Γm1↦Γm2} pb3 → pb2 = pb3.
Proof.
  destruct pb2, pb3; intros (τ1&?&?&?&?) (τ2&?&?&?&?);
    f_equal'; eauto using ptr_refine_unique with congruence.
Qed.
Lemma ptr_bits_refine_unique Γ f Γm1 Γm2 pbs1 pbs2 pbs3 :
  pbs1 ⊑{Γ,f@Γm1↦Γm2}* pbs2 → pbs1 ⊑{Γ,f@Γm1↦Γm2}* pbs3 → pbs2 = pbs3.
Proof.
  intros Hpbs. revert pbs3. induction Hpbs; inversion_clear 1;
    f_equal; eauto using ptr_bit_refine_unique.
Qed.
Lemma ptr_bit_refine_eq Γ Γm pb1 pb2 : pb1 ⊑{Γ@Γm} pb2 → pb1 = pb2.
Proof.
  destruct pb1, pb2; intros (?&?&?&?&?); simplify_equality';
    f_equal; eauto using ptr_refine_eq.
Qed.
Lemma ptr_bits_refine_eq Γ Γm pbs1 pbs2 : pbs1 ⊑{Γ@Γm}* pbs2 → pbs1 = pbs2.
Proof. induction 1; f_equal; eauto using ptr_bit_refine_eq. Qed.
Lemma ptr_to_bits_refine Γ f Γm1 Γm2 p1 p2 σ :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → ptr_to_bits Γ p1 ⊑{Γ,f@Γm1↦Γm2}* ptr_to_bits Γ p2.
Proof.
  intros. unfold ptr_to_bits, to_fragments.
  erewrite ptr_refine_type_of_l, ptr_refine_type_of_r by eauto.
  apply Forall2_fmap, Forall2_Forall, Forall_seq; intros j [??].
  exists σ; simpl; split_ands; unfold frozen; auto using ptr_freeze_freeze.
  by apply ptr_freeze_refine.
Qed.
Lemma ptr_of_bits_refine Γ f Γm1 Γm2 σ pbs1 pbs2 p1 :
  ptr_of_bits Γ σ pbs1 = Some p1 → pbs1 ⊑{Γ,f@Γm1↦Γm2}* pbs2 →
  ∃ p2, ptr_of_bits Γ σ pbs2 = Some p2 ∧ p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ.
Proof.
  revert pbs1 pbs2 p1. assert (∀ p1 p2 pbs1 pbs2,
    p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → frozen p1 → pbs1 ⊑{Γ,f@Γm1↦Γm2}* pbs2 →
    fragmented (bit_size_of Γ (σ.*)) p1 1 pbs1 →
    fragmented (bit_size_of Γ (σ.*)) p2 1 pbs2).
  { intros p1 p2 pbs1 pbs2 ??? ->. apply (ptr_bits_refine_unique Γ f Γm1 Γm2
      (Fragment p1 <$> seq 1 (bit_size_of Γ (σ.*) - 1))); [done|].
    apply Forall2_fmap, Forall2_Forall, Forall_seq; intros j [??].
    exists σ; simpl; split_ands; auto with lia. }
  intros pbs1 pbs2 p1; unfold ptr_of_bits. destruct 2 as
    [|[p1' []] [p2' []] ?? (?&?&?&?&?)]; simplify_option_equality;
    repeat match goal with
    | H : context [type_of ?p] |- _ =>
      erewrite ?ptr_refine_type_of_l, ?ptr_refine_type_of_r in H by eauto
    end; try done.
  * erewrite ptr_refine_type_of_l by eauto; eauto.
  * exfalso; naive_solver.
Qed.
End pointer_bits.
