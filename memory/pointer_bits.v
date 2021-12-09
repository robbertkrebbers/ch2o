(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)

Require Import fragmented.
Require Export pointers.

Notation ptr_bit K := (fragment (ptr K)).

Section pointer_bit_operations.
  Context `{EqDecision K, Env K}.

  Global Instance ptr_bit_valid:
      Valid (env K * memenv K) (ptr_bit K) := λ Δ pb, ∃ τp,
    let (Γ,Δ) := Δ in
    (Γ,Δ) ⊢ frag_item pb : τp ∧
    frozen (frag_item pb) ∧
    frag_index pb < bit_size_of Γ (τp.*).
  Definition ptr_to_bits (Γ : env K) (p : ptr K) : list (ptr_bit K) :=
    to_fragments (bit_size_of Γ (type_of p.*)) (freeze true p).
  Definition ptr_of_bits (Γ : env K) (τp : ptr_type K)
      (pbs : list (ptr_bit K)) : option (ptr K) :=
    p ← of_fragments (bit_size_of Γ (τp.*)) pbs;
    guard (type_of p = τp); Some p.
End pointer_bit_operations.

Section pointer_bits.
Context `{EqDecision K, EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ : type K.
Implicit Types τp : ptr_type K.
Implicit Types p : ptr K.
Implicit Types pb : ptr_bit K.
Implicit Types pbs : list (ptr_bit K).

#[global] Instance ptr_bit_valid_dec ΓΔ (pb : ptr_bit K) : Decision (✓{ΓΔ} pb).
Proof.
 refine
  match Some_dec (type_check ΓΔ (frag_item pb)) with
  | inleft (τ↾Hτ) => cast_if_and (decide (frozen (frag_item pb)))
     (decide (frag_index pb < bit_size_of (ΓΔ.1) (τ.*)))
  | inright Hτ => right _
  end; unfold frozen; auto with typeclass_instances;
  destruct ΓΔ; first
  [ simplify_type_equality; econstructor; eauto
  | by destruct 1 as (?&?&?&?); simplify_type_equality ].
Defined.
Lemma ptr_bit_valid_weaken Γ1 Γ2 Δ1 Δ2 pb :
  ✓ Γ1 → ✓{Γ1,Δ1} pb → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → ✓{Γ2,Δ2} pb.
Proof.
  intros ? (τ&?&?&?) ??. exists τ. erewrite <-bit_size_of_weaken
    by eauto using TBase_valid, TPtr_valid, ptr_typed_type_valid.
  eauto using ptr_typed_weaken.
Qed.
Lemma ptr_to_bits_freeze Γ q p : ptr_to_bits Γ (freeze q p) = ptr_to_bits Γ p.
Proof. unfold ptr_to_bits. by rewrite ptr_type_of_freeze,ptr_freeze_freeze. Qed.
Lemma ptr_to_bits_length_alt Γ p :
  length (ptr_to_bits Γ p) = bit_size_of Γ (type_of p.* ).
Proof. unfold ptr_to_bits. by rewrite (to_fragments_length _). Qed.
Lemma ptr_to_bits_length Γ Δ p τp :
  (Γ,Δ) ⊢ p : τp → length (ptr_to_bits Γ p) = bit_size_of Γ (τp.*).
Proof. intros. erewrite ptr_to_bits_length_alt, type_of_correct; eauto. Qed.
Lemma ptr_to_bits_valid Γ Δ p τp : (Γ,Δ) ⊢ p : τp → ✓{Γ,Δ}* (ptr_to_bits Γ p).
Proof.
  intros. apply (Forall_to_fragments _).
  intros i. erewrite type_of_correct by eauto. exists τp; simpl.
  rewrite ptr_typed_freeze. unfold frozen. by rewrite ptr_freeze_freeze.
Qed.
Lemma ptr_of_bits_Exists_Forall_typed Γ Δ τp pbs :
  is_Some (ptr_of_bits Γ τp pbs) → Exists ✓{Γ,Δ} pbs → ✓{Γ,Δ}* pbs.
Proof.
  unfold ptr_of_bits; intros [p ?]; simplify_option_eq.
  rewrite <-(of_to_fragments_1 _ p pbs) by eauto; unfold to_fragments at 1.
  rewrite Exists_fmap, Exists_exists.
  intros (i&?&?&?&?&?); simplify_type_equality'.
  apply (Forall_to_fragments _); eexists; eauto.
Qed.
Lemma ptr_of_bits_typed_frozen Γ Δ p τp pbs :
  ptr_of_bits Γ τp pbs = Some p → ✓{Γ,Δ}* pbs → (Γ,Δ) ⊢ p : τp ∧ frozen p.
Proof.
  unfold ptr_of_bits; intros; simplify_option_eq.
  destruct (Forall_of_fragments (bit_size_of Γ (type_of p.* ))
    (✓{Γ,Δ}) p pbs 0) as (?&?&?&?); eauto using type_of_typed.
  by apply Nat.neq_0_lt_0, bit_size_of_base_ne_0.
Qed.
Lemma ptr_of_bits_typed Γ Δ p τp pbs :
  ptr_of_bits Γ τp pbs = Some p → ✓{Γ,Δ}* pbs → (Γ,Δ) ⊢ p : τp.
Proof. intros. eapply ptr_of_bits_typed_frozen; eauto. Qed.
Lemma ptr_of_bits_frozen Γ Δ p τp pbs :
  ptr_of_bits Γ τp pbs = Some p → ✓{Γ,Δ}* pbs → frozen p.
Proof. intros. eapply ptr_of_bits_typed_frozen; eauto. Qed.
Lemma ptr_of_bits_type_of Γ p τp pbs :
  ptr_of_bits Γ τp pbs = Some p → type_of p = τp.
Proof. by unfold ptr_of_bits; intros; simplify_option_eq. Qed.
Lemma ptr_to_of_bits Γ Δ p τp pbs :
  ptr_of_bits Γ τp pbs = Some p → ✓{Γ,Δ}* pbs → ptr_to_bits Γ p = pbs.
Proof.
  intros. assert (frozen p) as Hp by eauto using ptr_of_bits_frozen.
  unfold ptr_of_bits, ptr_to_bits in *.
  destruct (of_fragments _ _) eqn:?; simplify_option_eq.
  by rewrite Hp, (of_to_fragments_1 _ _ pbs) by done.
Qed.
Lemma ptr_of_to_bits Γ p :
  ptr_of_bits Γ (type_of p) (ptr_to_bits Γ p) = Some (freeze true p).
Proof.
  unfold ptr_of_bits, ptr_to_bits. rewrite (of_to_fragments_2 _); csimpl.
  rewrite ptr_type_of_freeze. by simplify_option_eq.
Qed.
Lemma ptr_of_to_bits_typed Γ Δ p τp :
  (Γ,Δ) ⊢ p : τp → ptr_of_bits Γ τp (ptr_to_bits Γ p) = Some (freeze true p).
Proof. intros. by erewrite <-(ptr_of_to_bits Γ), type_of_correct by eauto. Qed.
Lemma ptr_of_bits_length Γ τp pbs p :
  ptr_of_bits Γ τp pbs = Some p → length pbs = bit_size_of Γ (τp.*).
Proof.
  unfold ptr_of_bits. intros. simplify_option_eq.
  by erewrite <-(of_to_fragments_1 _ _ pbs), to_fragments_length by eauto.
Qed.
Lemma ptr_to_bits_weaken Γ1 Γ2 Δ p τp :
  ✓ Γ1 → (Γ1,Δ) ⊢ p : τp → Γ1 ⊆ Γ2 → ptr_to_bits Γ1 p = ptr_to_bits Γ2 p.
Proof.
  intros. unfold ptr_to_bits. by erewrite !type_of_correct, bit_size_of_weaken
    by eauto using TBase_valid, TPtr_valid, ptr_typed_type_valid.
Qed.
Lemma ptr_of_bits_weaken Γ1 Γ2 τp pbs :
  ✓ Γ1 → ✓{Γ1} τp → Γ1 ⊆ Γ2 → ptr_of_bits Γ1 τp pbs = ptr_of_bits Γ2 τp pbs.
Proof.
  intros. unfold ptr_of_bits. by erewrite bit_size_of_weaken
    by eauto using TBase_valid, TPtr_valid.
Qed.
Lemma ptr_to_bits_alive Γ Δ p :
  ptr_alive Δ p →
  Forall (λ pb, ptr_alive Δ (fragmented.frag_item pb)) (ptr_to_bits Γ p).
Proof.
  unfold ptr_to_bits. intros. apply (Forall_to_fragments _).
  intros i _. by destruct p; simpl in *; rewrite ?addr_index_freeze.
Qed.
Lemma ptr_to_bits_dead Γ Δ p :
  ¬ptr_alive Δ p →
  Forall (λ pb, ¬ptr_alive Δ (fragmented.frag_item pb)) (ptr_to_bits Γ p).
Proof.
  unfold ptr_to_bits. intros. apply (Forall_to_fragments _).
  intros i _. by destruct p; simpl in *; rewrite ?addr_index_freeze.
Qed.
End pointer_bits.