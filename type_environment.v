(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export abstract_integers types.
Local Open Scope ctype_scope.

(** * Pointers environments *)
Section env.
Local Unset Elimination Schemes.

Class Env (Ti : Set) := {
  env_type_env :> IntEnv Ti;
  size_of : env Ti → type Ti → nat;
  field_sizes : env Ti → list (type Ti) → list nat
}.
Class EnvSpec (Ti : Set) `{Env Ti} := {
  int_env_spec :>> IntEnvSpec Ti;
  size_of_ptr_ne_0 Γ τ : size_of Γ (τ.*) ≠ 0;
  size_of_int Γ τ : size_of Γ (intT τ) = rank_size (rank τ);
  size_of_void Γ : size_of Γ voidT = 1;
  size_of_array Γ τ n : size_of Γ (τ.[n]) = n * size_of Γ τ;
  size_of_struct Γ s τs :
    ✓ Γ → Γ !! s = Some τs →
    size_of Γ (structT s) = sum_list (field_sizes Γ τs);
  size_of_fields Γ τs :
    ✓ Γ → Forall2 (λ τ sz, size_of Γ τ ≤ sz) τs (field_sizes Γ τs);
  size_of_union Γ s τs :
    ✓ Γ → Γ !! s = Some τs →
    Forall (λ τ, size_of Γ τ ≤ size_of Γ (unionT s)) τs;
  size_of_weaken Γ1 Γ2 τ :
    ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → size_of Γ1 τ = size_of Γ2 τ;
  fields_sizes_weaken Γ1 Γ2 τs :
    ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 → field_sizes Γ1 τs = field_sizes Γ2 τs
}.
End env.

Arguments size_of _ _ _ _ : simpl never.
Arguments field_sizes _ _ _ _ : simpl never.

Definition field_offset `{Env Ti} (Γ : env Ti) (τs : list (type Ti))
  (i : nat) : nat := sum_list $ take i $ field_sizes Γ τs.
Definition bit_size_of `{Env Ti} (Γ : env Ti)
  (τ : type Ti) : nat := size_of Γ τ * char_bits.
Definition field_bit_sizes `{Env Ti} (Γ : env Ti)
    (τs : list (type Ti)) : list nat :=
  (λ sz, sz * char_bits) <$> field_sizes Γ τs.
Definition field_bit_padding `{Env Ti}
    (Γ : env Ti) (τs : list (type Ti)) : list nat :=
  zip_with (λ sz τ, sz - bit_size_of Γ τ) (field_bit_sizes Γ τs) τs.
Definition field_bit_offset `{Env Ti}
    (Γ : env Ti) (τs : list (type Ti)) (i : nat) : nat :=
  sum_list $ take i $ field_bit_sizes Γ τs.

Notation size_of' Γ v := (size_of Γ (type_of v)).
Notation bit_size_of' Γ v := (bit_size_of Γ (type_of v)).

Section env_spec.
Context `{EnvSpec Ti}.
Implicit Types τ σ : type Ti.
Implicit Types τs σs : list (type Ti).
Implicit Types Γ : env Ti.

Lemma size_of_uchar Γ : size_of Γ ucharT = 1.
Proof. rewrite size_of_int. by apply rank_size_char. Qed.
Lemma field_sizes_length Γ τs : ✓ Γ → length (field_sizes Γ τs) = length τs.
Proof. symmetry. by eapply Forall2_length, size_of_fields. Qed.
Lemma field_sizes_nil Γ : ✓ Γ → field_sizes Γ [] = [].
Proof. intros. apply nil_length_inv. by rewrite field_sizes_length. Qed.
Lemma size_of_union_lookup Γ s τs i τ :
  ✓ Γ → Γ !! s = Some τs → τs !! i = Some τ →
  size_of Γ τ ≤ size_of Γ (unionT s).
Proof.
  intros. assert (Forall (λ τ, size_of Γ τ ≤ size_of Γ (unionT s)) τs) as Hτs
    by eauto using size_of_union; rewrite Forall_lookup in Hτs. eauto.
Qed.
Lemma size_of_struct_lookup Γ s τs i τ :
  ✓ Γ → Γ !! s = Some τs → τs !! i = Some τ →
  size_of Γ τ ≤ size_of Γ (structT s).
Proof.
  intros HΓ Hs Hτs. erewrite size_of_struct by eauto. clear Hs. revert i Hτs.
  induction (size_of_fields Γ τs HΓ) as [|σ sz σs szs]; intros [|?] ?;
    simplify_equality'; auto with lia.
  transitivity (sum_list szs); eauto with lia.
Qed.
Lemma size_of_union_singleton Γ s τ :
  ✓ Γ → Γ !! s = Some [τ] → size_of Γ τ ≤ size_of Γ (unionT s).
Proof. intros. by apply (size_of_union_lookup Γ s [τ] 0). Qed.
Lemma sizes_of_weaken Γ1 Γ2 τs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  Forall (λ τ', int_typed (size_of Γ1 τ') sptrT) τs →
  Forall (λ τ', int_typed (size_of Γ2 τ') sptrT) τs.
Proof.
  induction 4; decompose_Forall_hyps; constructor; simpl;
    erewrite <-1?size_of_weaken by eauto; eauto.
Qed.

Lemma bit_size_of_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → bit_size_of Γ1 τ = bit_size_of Γ2 τ.
Proof. intros. unfold bit_size_of. f_equal. by apply size_of_weaken. Qed.
Lemma bit_size_of_int Γ τi : bit_size_of Γ (intT τi) = int_width τi.
Proof. unfold bit_size_of. by rewrite size_of_int. Qed.
Lemma bit_size_of_int_same_kind Γ τi1 τi2 :
  rank τi1 = rank τi2 → bit_size_of Γ (intT τi1) = bit_size_of Γ (intT τi2).
Proof.
  destruct τi1, τi2; intros; simplify_equality'. by rewrite !bit_size_of_int.
Qed.
Lemma bit_size_of_void Γ : bit_size_of Γ voidT = char_bits.
Proof. unfold bit_size_of. by rewrite size_of_void, Nat.mul_1_l. Qed.
Lemma bit_size_of_array Γ τ n : bit_size_of Γ (τ.[n]) = n * bit_size_of Γ τ.
Proof. unfold bit_size_of. by rewrite !size_of_array, Nat.mul_assoc. Qed.
Lemma bit_size_of_struct Γ s τs :
  ✓ Γ → Γ !! s = Some τs →
  bit_size_of Γ (structT s) = sum_list (field_bit_sizes Γ τs).
Proof.
  unfold bit_size_of, field_bit_sizes. intros.
  erewrite size_of_struct by eauto.
  elim (field_sizes Γ τs); csimpl; auto with lia.
Qed.
Lemma bit_size_of_fields Γ τs :
  ✓ Γ → Forall2 (λ τ sz, bit_size_of Γ τ ≤ sz) τs (field_bit_sizes Γ τs).
Proof.
  intros HΓ. unfold bit_size_of, field_bit_sizes.
  induction (size_of_fields Γ τs HΓ);
    simpl; constructor; auto using Nat.mul_le_mono_nonneg_r with lia.
Qed.
Lemma bit_size_of_union Γ s τs :
  ✓ Γ → Γ !! s = Some τs →
  Forall (λ τ, bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) τs.
Proof.
  intros ? Hτs. apply size_of_union in Hτs; auto. unfold bit_size_of.
  induction Hτs; constructor; auto using Nat.mul_le_mono_nonneg_r with lia.
Qed.
Lemma bit_size_of_union_lookup Γ s τs i τ :
  ✓ Γ → Γ !! s = Some τs → τs !! i = Some τ →
  bit_size_of Γ τ ≤ bit_size_of Γ (unionT s).
Proof.
  intros. unfold bit_size_of. apply Nat.mul_le_mono_nonneg_r;
    eauto using size_of_union_lookup with lia.
Qed.
Lemma bit_size_of_union_singleton Γ s τ :
  ✓ Γ → Γ !! s = Some [τ] → bit_size_of Γ τ ≤ bit_size_of Γ (unionT s).
Proof. intros. by apply (bit_size_of_union_lookup Γ s [τ] 0). Qed.

Lemma field_bit_sizes_weaken Γ1 Γ2 τs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 → field_bit_sizes Γ1 τs = field_bit_sizes Γ2 τs.
Proof. unfold field_bit_sizes. auto using fields_sizes_weaken with f_equal. Qed.
Lemma field_bit_sizes_length Γ τs :
  ✓ Γ → length (field_bit_sizes Γ τs) = length τs.
Proof. symmetry. by eapply Forall2_length, bit_size_of_fields. Qed.
Lemma field_bit_sizes_nil Γ : ✓ Γ → field_bit_sizes Γ [] = [].
Proof. intros. apply nil_length_inv. by rewrite field_bit_sizes_length. Qed.
Lemma field_bit_padding_weaken Γ1 Γ2 τs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  field_bit_padding Γ1 τs = field_bit_padding Γ2 τs.
Proof.
  intros HΓ1 Hτs ?. unfold field_bit_padding.
  erewrite <-(field_bit_sizes_weaken Γ1 Γ2) by eauto.
  induction (bit_size_of_fields _ τs HΓ1); decompose_Forall_hyps;
    auto using bit_size_of_weaken with f_equal.
Qed.
Lemma field_bit_padding_length Γ τs :
  ✓ Γ → length (field_bit_padding Γ τs) = length τs.
Proof.
  intros. unfold field_bit_padding.
  rewrite zip_with_length, field_bit_sizes_length by done; lia.
Qed.
Lemma field_bit_offset_alt Γ τs i :
  field_bit_offset Γ τs i = field_offset Γ τs i * char_bits.
Proof.
  unfold field_bit_offset, field_offset, field_bit_sizes.
  revert i. induction (field_sizes Γ τs) as [|?? IH];
    intros [|i]; simpl; auto with lia.
  by rewrite IH, Nat.mul_add_distr_r.
Qed.
Lemma field_bit_offset_lt Γ τs i j σ :
  ✓ Γ → τs !! i = Some σ → i < j →
  field_bit_offset Γ τs i + bit_size_of Γ σ ≤ field_bit_offset Γ τs j.
Proof.
  intros HΓ. revert i j σ. unfold field_bit_offset.
  induction (bit_size_of_fields _ τs HΓ) as [|τ sz τs szs ?? IH];
    intros [|i] [|j] σ ??; simplify_equality'; try lia.
  specialize (IH i j σ). intuition lia.
Qed.
Lemma field_bit_offset_size Γ s τs i σ :
  ✓ Γ → Γ !! s = Some τs → τs !! i = Some σ →
  field_bit_offset Γ τs i + bit_size_of Γ σ ≤ bit_size_of Γ (structT s).
Proof.
  intros HΓ Hs. erewrite bit_size_of_struct by eauto; clear Hs.
  revert i σ. unfold field_bit_offset. induction (bit_size_of_fields _ τs HΓ)
    as [|τ sz τs szs ?? IH]; intros [|i] σ ?; simplify_equality'; [lia|].
  specialize (IH i σ). intuition lia.
Qed.

Lemma size_of_base_ne_0 Γ τb : size_of Γ (baseT τb) ≠ 0.
Proof.
  destruct τb.
  * by rewrite size_of_void. 
  * rewrite size_of_int. apply rank_size_ne_0.
  * apply size_of_ptr_ne_0.
Qed.
Lemma bit_size_of_base_ne_0 Γ τb : bit_size_of Γ (baseT τb) ≠ 0.
Proof. apply Nat.neq_mul_0. auto using char_bits_ne_0, size_of_base_ne_0. Qed.
Global Instance: ∀ Γ τb, PropHolds (size_of Γ (baseT τb) ≠ 0).
Proof. apply size_of_base_ne_0. Qed.
Global Instance: ∀ Γ τb, PropHolds (bit_size_of Γ (baseT τb) ≠ 0).
Proof. apply bit_size_of_base_ne_0. Qed.
Lemma size_of_ne_0 Γ τ : ✓ Γ → ✓{Γ} τ → size_of Γ τ ≠ 0.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * auto using size_of_base_ne_0.
  * intros. rewrite size_of_array. by apply Nat.neq_mul_0.
  * intros [] s τs Hs Hτs Hsz Hlen.
    + erewrite size_of_struct by eauto. clear Hs.
      destruct (size_of_fields Γ τs HΓ); decompose_Forall_hyps; auto with lia.
    + apply size_of_union in Hs; auto.
      destruct Hs; decompose_Forall_hyps; auto with lia.
Qed.
Lemma size_of_pos Γ τ : ✓ Γ → ✓{Γ} τ → 0 < size_of Γ τ.
Proof. intros. by apply Nat.neq_0_lt_0, size_of_ne_0. Qed.
Lemma bit_size_of_ne_0 Γ τ : ✓ Γ → ✓{Γ} τ → bit_size_of Γ τ ≠ 0.
Proof. intros. apply Nat.neq_mul_0. auto using char_bits_ne_0,size_of_ne_0. Qed.
Lemma bit_size_of_pos Γ τ : ✓ Γ → ✓{Γ} τ → 0 < bit_size_of Γ τ.
Proof. intros. by apply Nat.neq_0_lt_0, bit_size_of_ne_0. Qed.
End env_spec.
