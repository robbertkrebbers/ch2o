(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export types integer_operations.
Local Open Scope ctype_scope.
Local Unset Elimination Schemes.

Class Env (K : iType) : iType := {
  env_type_env :> IntEnv K;
  size_of : env K → type K → nat;
  align_of : env K → type K → nat;
  field_sizes : env K → list (type K) → list nat;
  alloc_can_fail : bool
}.

Arguments size_of _ _ _ _ : simpl never.
Arguments align_of _ _ _ _ : simpl never.
Arguments field_sizes _ _ _ _ : simpl never.

Definition ptr_size_of `{Env K} (Γ : env K) (τp : ptr_type K) : nat :=
  match τp with TType τ => size_of Γ τ | _ => 1 end.
Definition offset_of `{Env K} (Γ : env K) (τs : list (type K))
  (i : nat) : nat := sum_list $ take i $ field_sizes Γ τs.
Definition bit_size_of `{Env K} (Γ : env K)
  (τ : type K) : nat := size_of Γ τ * char_bits.
Definition bit_align_of `{Env K} (Γ : env K)
  (τ : type K) : nat := align_of Γ τ * char_bits.
Definition ptr_bit_size_of `{Env K} (Γ : env K) (τp : ptr_type K) : nat :=
  match τp with TType τ => bit_size_of Γ τ | _ => char_bits end.
Definition field_bit_sizes `{Env K} (Γ : env K)
    (τs : list (type K)) : list nat :=
  (λ sz, sz * char_bits) <$> field_sizes Γ τs.
Definition field_bit_padding `{Env K}
    (Γ : env K) (τs : list (type K)) : list nat :=
  zip_with (λ sz τ, sz - bit_size_of Γ τ) (field_bit_sizes Γ τs) τs.
Definition bit_offset_of `{Env K}
    (Γ : env K) (τs : list (type K)) (i : nat) : nat :=
  sum_list $ take i $ field_bit_sizes Γ τs.

Class EnvSpec (K : iType) `{Env K} := {
  int_env_spec :> IntEnvSpec K;
  size_of_ptr_ne_0 Γ τp : size_of Γ (τp.*) ≠ 0;
  size_of_int Γ τi : size_of Γ (intT τi) = rank_size (rank τi);
  size_of_void_ne_0 Γ : size_of Γ voidT ≠ 0;
  size_of_array Γ τ n : size_of Γ (τ.[n]) = n * size_of Γ τ;
  size_of_struct Γ t τs :
    ✓ Γ → Γ !! t = Some τs →
    size_of Γ (structT t) = sum_list (field_sizes Γ τs);
  size_of_fields Γ τs :
    ✓ Γ → Forall2 (λ τ sz, size_of Γ τ ≤ sz) τs (field_sizes Γ τs);
  size_of_union Γ t τs :
    ✓ Γ → Γ !! t = Some τs →
    Forall (λ τ, size_of Γ τ ≤ size_of Γ (unionT t)) τs;
  align_of_array Γ τ n : (align_of Γ τ | align_of Γ (τ.[n]));
  align_of_compound Γ c t τs i τ :
    ✓ Γ → Γ !! t = Some τs → τs !! i = Some τ →
    (align_of Γ τ | align_of Γ (compoundT{c} t));
  align_of_divide Γ τ :
    ✓ Γ → ✓{Γ} τ → (align_of Γ τ | size_of Γ τ);
  align_of_offset_of Γ τs i τ :
    ✓ Γ → ✓{Γ}* τs → τs !! i = Some τ → (align_of Γ τ | offset_of Γ τs i);
  size_of_weaken Γ1 Γ2 τ :
    ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → size_of Γ1 τ = size_of Γ2 τ;
  align_of_weaken Γ1 Γ2 τ :
    ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → align_of Γ1 τ = align_of Γ2 τ;
  fields_sizes_weaken Γ1 Γ2 τs :
    ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 → field_sizes Γ1 τs = field_sizes Γ2 τs
}.

Section env_spec.
Context `{EnvSpec K}.
Implicit Types τ σ : type K.
Implicit Types τs σs : list (type K).
Implicit Types Γ : env K.

Lemma size_of_char Γ si : size_of Γ (intT (IntType si char_rank)) = 1.
Proof. rewrite size_of_int. by apply rank_size_char. Qed.
Lemma field_sizes_length Γ τs : ✓ Γ → length (field_sizes Γ τs) = length τs.
Proof. symmetry. by eapply Forall2_length, size_of_fields. Qed.
Lemma field_sizes_nil Γ : ✓ Γ → field_sizes Γ [] = [].
Proof. intros. apply nil_length_inv. by rewrite field_sizes_length. Qed.
Lemma size_of_union_lookup Γ t τs i τ :
  ✓ Γ → Γ !! t = Some τs → τs !! i = Some τ →
  size_of Γ τ ≤ size_of Γ (unionT t).
Proof.
  intros. assert (Forall (λ τ, size_of Γ τ ≤ size_of Γ (unionT t)) τs) as Hτs
    by eauto using size_of_union; rewrite Forall_lookup in Hτs. eauto.
Qed.
Lemma size_of_struct_lookup Γ t τs i τ :
  ✓ Γ → Γ !! t = Some τs → τs !! i = Some τ →
  size_of Γ τ ≤ size_of Γ (structT t).
Proof.
  intros HΓ Ht Hτs. erewrite size_of_struct by eauto. clear Ht. revert i Hτs.
  induction (size_of_fields Γ τs HΓ) as [|σ sz σs szs]; intros [|?] ?;
    simplify_equality'; auto with lia.
  transitivity (sum_list szs); eauto with lia.
Qed.
Lemma size_of_union_singleton Γ t τ :
  ✓ Γ → Γ !! t = Some [τ] → size_of Γ τ ≤ size_of Γ (unionT t).
Proof. intros. by apply (size_of_union_lookup Γ t [τ] 0). Qed.
Lemma sizes_of_weaken P Γ1 Γ2 τs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  Forall (λ τ', P (size_of Γ1 τ')) τs → Forall (λ τ', P (size_of Γ2 τ')) τs.
Proof.
  induction 4; decompose_Forall_hyps; constructor; simpl;
    erewrite <-1?size_of_weaken by eauto; eauto.
Qed.

Lemma bit_size_of_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → bit_size_of Γ1 τ = bit_size_of Γ2 τ.
Proof. intros. unfold bit_size_of. f_equal. by apply size_of_weaken. Qed.
Lemma bit_size_of_int Γ τi : bit_size_of Γ (intT τi) = int_width τi.
Proof. unfold bit_size_of. by rewrite size_of_int. Qed.
Lemma bit_size_of_char Γ si :
  bit_size_of Γ (intT (IntType si char_rank)) = char_bits.
Proof. rewrite bit_size_of_int. by apply int_width_char. Qed.
Lemma bit_size_of_int_same_kind Γ τi1 τi2 :
  rank τi1 = rank τi2 → bit_size_of Γ (intT τi1) = bit_size_of Γ (intT τi2).
Proof.
  destruct τi1, τi2; intros; simplify_equality'. by rewrite !bit_size_of_int.
Qed.
Lemma bit_size_of_array Γ τ n : bit_size_of Γ (τ.[n]) = n * bit_size_of Γ τ.
Proof. unfold bit_size_of. by rewrite !size_of_array, Nat.mul_assoc. Qed.
Lemma bit_size_of_struct Γ t τs :
  ✓ Γ → Γ !! t = Some τs →
  bit_size_of Γ (structT t) = sum_list (field_bit_sizes Γ τs).
Proof.
  unfold bit_size_of, field_bit_sizes. intros.
  erewrite size_of_struct by eauto.
  induction (field_sizes Γ τs); csimpl; auto with lia.
Qed.
Lemma bit_size_of_fields Γ τs :
  ✓ Γ → Forall2 (λ τ sz, bit_size_of Γ τ ≤ sz) τs (field_bit_sizes Γ τs).
Proof.
  intros HΓ. unfold bit_size_of, field_bit_sizes.
  induction (size_of_fields Γ τs HΓ);
    simpl; constructor; auto using Nat.mul_le_mono_nonneg_r with lia.
Qed.
Lemma bit_size_of_union Γ t τs :
  ✓ Γ → Γ !! t = Some τs →
  Forall (λ τ, bit_size_of Γ τ ≤ bit_size_of Γ (unionT t)) τs.
Proof.
  intros ? Hτs. apply size_of_union in Hτs; auto. unfold bit_size_of.
  induction Hτs; constructor; auto using Nat.mul_le_mono_nonneg_r with lia.
Qed.
Lemma bit_size_of_union_lookup Γ t τs i τ :
  ✓ Γ → Γ !! t = Some τs → τs !! i = Some τ →
  bit_size_of Γ τ ≤ bit_size_of Γ (unionT t).
Proof.
  intros. unfold bit_size_of. apply Nat.mul_le_mono_nonneg_r;
    eauto using size_of_union_lookup with lia.
Qed.
Lemma bit_size_of_union_singleton Γ t τ :
  ✓ Γ → Γ !! t = Some [τ] → bit_size_of Γ τ ≤ bit_size_of Γ (unionT t).
Proof. intros. by apply (bit_size_of_union_lookup Γ t [τ] 0). Qed.
Lemma ptr_bit_size_of_alt Γ τp :
  ptr_bit_size_of Γ τp = ptr_size_of Γ τp * char_bits.
Proof. destruct τp; simpl; unfold bit_size_of; lia. Qed.

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
Lemma bit_offset_of_weaken Γ1 Γ2 τs i :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  bit_offset_of Γ1 τs i = bit_offset_of Γ2 τs i.
Proof.
  unfold bit_offset_of. eauto using field_bit_sizes_weaken with f_equal.
Qed.
Lemma bit_offset_of_alt Γ τs i :
  bit_offset_of Γ τs i = offset_of Γ τs i * char_bits.
Proof.
  unfold bit_offset_of, offset_of, field_bit_sizes.
  revert i. induction (field_sizes Γ τs) as [|?? IH];
    intros [|i]; simpl; auto with lia.
  by rewrite IH, Nat.mul_add_distr_r.
Qed.
Lemma bit_offset_of_lt Γ τs i j σ :
  ✓ Γ → τs !! i = Some σ → i < j →
  bit_offset_of Γ τs i + bit_size_of Γ σ ≤ bit_offset_of Γ τs j.
Proof.
  intros HΓ. revert i j σ. unfold bit_offset_of.
  induction (bit_size_of_fields _ τs HΓ) as [|τ sz τs szs ?? IH];
    intros [|i] [|j] σ ??; simplify_equality'; try lia.
  specialize (IH i j σ). intuition lia.
Qed.
Lemma bit_offset_of_size Γ t τs i σ :
  ✓ Γ → Γ !! t = Some τs → τs !! i = Some σ →
  bit_offset_of Γ τs i + bit_size_of Γ σ ≤ bit_size_of Γ (structT t).
Proof.
  intros HΓ Ht. erewrite bit_size_of_struct by eauto; clear Ht.
  revert i σ. unfold bit_offset_of. induction (bit_size_of_fields _ τs HΓ)
    as [|τ sz τs szs ?? IH]; intros [|i] σ ?; simplify_equality'; [lia|].
  specialize (IH i σ). intuition lia.
Qed.

Lemma align_of_char Γ si : ✓ Γ → align_of Γ (intT (IntType si char_rank)) = 1.
Proof.
  intros. apply Nat.divide_1_r; rewrite <-(size_of_char Γ si).
  apply align_of_divide; repeat constructor; auto.
Qed.
Lemma bit_align_of_array Γ τ n : (bit_align_of Γ τ | bit_align_of Γ (τ.[n])).
Proof. apply Nat.mul_divide_mono_r, align_of_array. Qed.
Lemma bit_align_of_compound Γ c t τs i τ :
  ✓ Γ → Γ !! t = Some τs → τs !! i = Some τ →
  (bit_align_of Γ τ | bit_align_of Γ (compoundT{c} t)).
Proof. eauto using Nat.mul_divide_mono_r, align_of_compound. Qed.
Lemma bit_align_of_divide Γ τ :
  ✓ Γ → ✓{Γ} τ → (bit_align_of Γ τ | bit_size_of Γ τ).
Proof. eauto using Nat.mul_divide_mono_r, align_of_divide. Qed.
Lemma bit_align_of_offset_of Γ τs i τ :
  ✓ Γ → ✓{Γ}* τs → τs !! i = Some τ →
  (bit_align_of Γ τ | bit_offset_of Γ τs i).
Proof.
  rewrite bit_offset_of_alt.
  eauto using Nat.mul_divide_mono_r, align_of_offset_of.
Qed.
Lemma bit_align_of_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → bit_align_of Γ1 τ = bit_align_of Γ2 τ.
Proof. unfold bit_align_of; auto using align_of_weaken, f_equal. Qed.

Lemma size_of_base_ne_0 Γ τb : size_of Γ (baseT τb) ≠ 0.
Proof.
  destruct τb; auto using size_of_void_ne_0, size_of_ptr_ne_0.
  rewrite size_of_int. apply rank_size_ne_0.
Qed.
Lemma bit_size_of_base_ne_0 Γ τb : bit_size_of Γ (baseT τb) ≠ 0.
Proof. apply Nat.neq_mul_0. auto using char_bits_ne_0, size_of_base_ne_0. Qed.
#[global] Instance: ∀ Γ τb, PropHolds (size_of Γ (baseT τb) ≠ 0).
Proof. apply size_of_base_ne_0. Qed.
#[global] Instance: ∀ Γ τb, PropHolds (bit_size_of Γ (baseT τb) ≠ 0).
Proof. apply bit_size_of_base_ne_0. Qed.
Lemma size_of_ne_0 Γ τ : ✓ Γ → ✓{Γ} τ → size_of Γ τ ≠ 0.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * auto using size_of_base_ne_0.
  * intros. rewrite size_of_array. by apply Nat.neq_mul_0.
  * intros [] t τs Ht Hτs IH Hlen.
    + erewrite size_of_struct by eauto. clear Ht.
      destruct (size_of_fields Γ τs HΓ); decompose_Forall_hyps; auto with lia.
    + apply size_of_union in Ht; auto.
      destruct Ht; decompose_Forall_hyps; auto with lia.
Qed.
Lemma align_of_ne_0 Γ τ : ✓ Γ → ✓{Γ} τ → align_of Γ τ ≠ 0.
Proof. eauto using Nat_divide_ne_0, size_of_ne_0, align_of_divide. Qed.
Lemma size_of_pos Γ τ : ✓ Γ → ✓{Γ} τ → 0 < size_of Γ τ.
Proof. intros. by apply Nat.neq_0_lt_0, size_of_ne_0. Qed.
Lemma bit_size_of_ne_0 Γ τ : ✓ Γ → ✓{Γ} τ → bit_size_of Γ τ ≠ 0.
Proof. intros. apply Nat.neq_mul_0. auto using char_bits_ne_0,size_of_ne_0. Qed.
Lemma bit_size_of_pos Γ τ : ✓ Γ → ✓{Γ} τ → 0 < bit_size_of Γ τ.
Proof. intros. by apply Nat.neq_0_lt_0, bit_size_of_ne_0. Qed.
End env_spec.
