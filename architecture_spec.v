(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export type_system.
Require Import natural_type_environment.

Record architecture := Architecture {
  big_endian : bool;
  char_bits_minus8 : nat;
  char_signedness : signedness;
  short_bytes_log2 : nat;
  int_bytes_log2 : nat;
  long_bytes_log2 : nat → nat;
  ptr_bytes_log2 : nat;
  align_minus : nat → nat
}.

Inductive irank (A : architecture) : Set := IKind { ibytes_log2 : nat }.
Arguments ibytes_log2 {_} _.
Instance irank_eq_dec {A} (k1 k2 : irank A) : Decision (k1 = k2).
Proof. solve_decision. Defined.

Section architecture.
Context (A : architecture).

Instance: IntCoding (irank A) := {
  char_rank := IKind A 0;
  char_signedness := char_signedness A;
  short_rank := IKind A (short_bytes_log2 A);
  int_rank := IKind A (int_bytes_log2 A);
  long_rank n := IKind A (long_bytes_log2 A n);
  ptr_rank := IKind A (ptr_bytes_log2 A);
  char_bits := char_bits_minus8 A + 8;
  rank_size := λ k, 2 ^ ibytes_log2 k;
  endianize := λ _, if big_endian A then reverse else id;
  deendianize := λ _, if big_endian A then reverse else id
}.
Instance: IntEnv (irank A) := {
  int_arithop_ok op x τ1 y τ2 :=
    let τ' := int_promote τ1 ∪ int_promote τ2 in
    int_pre_arithop_ok op (int_pre_cast τ' x) (int_pre_cast τ' y) τ';
  int_arithop op x τ1 y τ2 :=
    let τ' := int_promote τ1 ∪ int_promote τ2 in
    int_pre_arithop op (int_pre_cast τ' x) (int_pre_cast τ' y) τ';
  int_shiftop_ok op x τ1 y τ2 :=
    let τ' := int_promote τ1 in int_pre_shiftop_ok op (int_pre_cast τ' x) y τ';
  int_shiftop op x τ1 y τ2 :=
    let τ' := int_promote τ1 in int_pre_shiftop op (int_pre_cast τ' x) y τ';
  int_cast_ok := int_pre_cast_ok;
  int_cast := int_pre_cast
}.
Instance: IntCodingSpec (irank A).
Proof.
  split.
  * unfold char_bits; simpl; lia.
  * done.
  * unfold rank_size; simpl. intros. by apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  * unfold rank_size; intros [i] [j] ?; simplify_equality'; f_equal.
    apply Nat.pow_inj_r with 2; lia.
  * intros. unfold endianize; simpl.
    by destruct (big_endian _); simpl; rewrite ?reverse_Permutation.
  * intros. unfold deendianize, endianize; simpl.
    by destruct (big_endian _); simpl; rewrite ?reverse_involutive.
  * intros. unfold deendianize, endianize; simpl.
    by destruct (big_endian _); simpl; rewrite ?reverse_involutive.
Qed.
Instance: IntEnvSpec (irank A).
Proof.
  split.
  * apply _.
  * done.
  * intros. apply int_pre_arithop_typed; auto.
    + apply int_pre_cast_typed; auto.
      by apply int_union_pre_cast_ok_l, int_promote_typed.
    + apply int_pre_cast_typed; auto.
      by apply int_union_pre_cast_ok_r, int_promote_typed.
  * done.
  * done.
  * intros. eapply int_pre_shiftop_typed; eauto.
    apply int_pre_cast_typed; auto.
    by apply int_typed_pre_cast_ok, int_promote_typed.
  * unfold int_shiftop; simpl; intros.
    by rewrite int_typed_pre_cast by auto using int_promote_typed.
  * done.
  * intros. by apply int_pre_cast_typed.
  * done.
Qed.

Let ptr_size (_ : type (irank A)) : nat := 2 ^ ptr_bytes_log2 A.
Let align_base (τb : base_type (irank A)) : nat :=
  match τb with
  | voidT => 1
  | intT τi => let n := ibytes_log2 (rank τi) in 2 ^ (n - align_minus A n)
  | τ.* => let n := ptr_bytes_log2 A in 2 ^ (n - align_minus A n)
  end%BT.
Definition align_of : env (irank A) → type (irank A) → nat :=
  natural_align_of align_base.
Global Instance architecture_env : Env (irank A) :=
  natural_env ptr_size align_base.

Let ptr_size_ne_0 τ : ptr_size τ ≠ 0.
Proof. by apply Nat.pow_nonzero. Qed.
Let align_void : align_base voidT = 1.
Proof. done. Qed.
Let align_int_divide τi : (align_base (intT τi) | rank_size (rank τi)).
Proof.
  unfold rank_size; simpl. set (n:=ibytes_log2 (rank τi)).
  destruct (decide (align_minus A n ≤ n)).
  { rewrite <-(Nat.sub_add (align_minus A n) n) at 3 by done.
    rewrite Nat.pow_add_r. by apply Nat.divide_factor_l. }
  rewrite not_le_minus_0 by done; apply Nat.divide_1_l.
Qed.
Let align_ptr_divide τ : (align_base (τ.*) | ptr_size τ).
Proof.
  unfold ptr_size; simpl. set (n:=ptr_bytes_log2 A).
  destruct (decide (align_minus A n ≤ n)).
  { rewrite <-(Nat.sub_add (align_minus A n) n) at 3 by done.
    rewrite Nat.pow_add_r. by apply Nat.divide_factor_l. }
  rewrite not_le_minus_0 by done; apply Nat.divide_1_l.
Qed.

Global Instance: EnvSpec (irank A).
Proof. by apply natural_env_spec. Qed.
Lemma align_of_divide Γ τ : ✓ Γ → ✓{Γ} τ → (align_of Γ τ | size_of Γ τ).
Proof. by apply natural_align_of_divide. Qed.
Lemma architecture_field_offset Γ τs i τ :
  ✓ Γ → ✓{Γ}* τs → τs !! i = Some τ → (align_of Γ τ | field_offset Γ τs i).
Proof. by apply natural_field_offset. Qed.
End architecture.
