(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import finite.
Require Export type_environment.
Require Import natural_type_environment.

Inductive c_rank : iType :=
  CharRank | ShortRank | IntRank | LongRank | LongLongRank | PtrRank.
#[global] Instance c_rank_subseteq : SubsetEq c_rank := λ k1 k2,
  match k1, k2 return bool with
  | CharRank, _ => true
  | ShortRank, (ShortRank | IntRank | LongRank | PtrRank | LongLongRank) => true
  | IntRank, (IntRank | LongRank | PtrRank | LongLongRank) => true
  | LongRank, (LongRank | PtrRank | LongLongRank) => true
  | PtrRank, (PtrRank | LongLongRank) => true
  | LongLongRank, LongLongRank => true
  | _, _ => false
  end.
#[global] Instance c_rank_eq_dec: EqDecision c_rank.
Proof. solve_decision. Defined.
Program Global Instance c_rank_finite : Finite c_rank := {
  enum := [ CharRank ; ShortRank ; IntRank ; LongRank ; LongLongRank ; PtrRank ]
}.
Next Obligation. by apply (bool_decide_unpack _). Qed.
Next Obligation. by destruct x; apply (bool_decide_unpack _). Qed.
#[global] Instance c_rank_subseteq_dec (k1 k2 : c_rank) : Decision (k1 ⊆ k2).
Proof. solve_decision. Defined.
#[global] Instance c_rank_totalorder : TotalOrder ((⊆) : relation c_rank).
Proof. by repeat split; red; apply (bool_decide_unpack _); vm_compute. Qed.

Record architecture_sizes := ArchitectureSizes {
  arch_char_bits : nat;
  arch_size : c_rank → nat; (* size in bytes *)
  arch_align : c_rank → nat; (* align in bytes *)
  arch_char_bits_ge_8 : 8 ≤ arch_char_bits;
  arch_size_char : arch_size CharRank = 1;
  arch_size_preserving k1 k2 : k1 ⊆ k2 → arch_size k1 ≤ arch_size k2;
  arch_align_size k : (arch_align k | arch_size k)
}.
Record architecture := ArchitectureFlags {
  arch_sizes :> architecture_sizes;
  arch_char_signedness : signedness;
  arch_alloc_can_fail : bool;
  arch_big_endian : bool
}.

Inductive arch_rank (A : architecture) : iType :=
  ARank { arch_rank_car :> c_rank }.
Arguments ARank {_} _.
#[global] Instance arch_rank_eq_dec {A}: EqDecision (arch_rank A).
Proof. solve_decision. Defined.
Program Global Instance arch_rank_finite {A} : Finite (arch_rank A) := {
  enum := ARank <$> enum c_rank
}.
Next Obligation. by intros; apply (bool_decide_unpack _). Qed.
Next Obligation. by destruct x as [rank]; apply (bool_decide_unpack _); destruct rank. Qed.

Section architecture.
Context (A : architecture).

#[local] Instance arch_int_coding: IntCoding (arch_rank A) := {
  char_rank := ARank CharRank;
  char_signedness := arch_char_signedness A;
  short_rank := ARank ShortRank;
  int_rank := ARank IntRank;
  long_rank := ARank LongRank;
  longlong_rank := ARank LongLongRank;
  ptr_rank := ARank PtrRank;
  char_bits := arch_char_bits A;
  rank_size := arch_size A;
  rank_subseteq k1 k2 := (k1:c_rank) ⊆ (k2:c_rank);
  endianize := λ _, if arch_big_endian A then reverse else id;
  deendianize := λ _, if arch_big_endian A then reverse else id
}.
#[local] Instance arch_int_env: IntEnv (arch_rank A) := {
  int_arithop_ok op x τi1 y τi2 :=
    let τi := int_promote τi1 ∪ int_promote τi2 in
    int_pre_arithop_ok op (int_pre_cast τi x) (int_pre_cast τi y) τi;
  int_arithop op x τi1 y τi2 :=
    let τi := int_promote τi1 ∪ int_promote τi2 in
    int_pre_arithop op (int_pre_cast τi x) (int_pre_cast τi y) τi;
  int_shiftop_ok op x τi1 y τi2 :=
    let τi := int_promote τi1 in
    int_pre_shiftop_ok op (int_pre_cast τi x) y τi;
  int_shiftop op x τi1 y τi2 :=
    let τi := int_promote τi1 in
    int_pre_shiftop op (int_pre_cast τi x) y τi;
  int_cast_ok := int_pre_cast_ok;
  int_cast := int_pre_cast
}.
#[local] Instance: IntCodingSpec (arch_rank A).
Proof.
  split.
  * by apply arch_char_bits_ge_8.
  * by apply arch_size_char.
  * intros [k1] [k2] ?. by apply Nat2Z.inj_le, arch_size_preserving.
  * by repeat split; red; apply (bool_decide_unpack _); vm_compute.
  * by intros [].
  * by apply (bool_decide_unpack _).
  * by apply (bool_decide_unpack _).
  * by apply (bool_decide_unpack _).
  * by apply (bool_decide_unpack _).
  * intros. unfold endianize; simpl.
    by destruct (arch_big_endian _); simpl; rewrite ?reverse_Permutation.
  * intros. unfold deendianize, endianize; simpl.
    by destruct (arch_big_endian _); simpl; rewrite ?reverse_involutive.
  * intros. unfold deendianize, endianize; simpl.
    by destruct (arch_big_endian _); simpl; rewrite ?reverse_involutive.
Qed.
#[local] Instance: IntEnvSpec (arch_rank A).
Proof.
  split.
  * apply _.
  * done.
  * intros. apply int_pre_arithop_typed; auto.
    + eapply int_pre_cast_typed, int_pre_cast_ok_subseteq,
        union_subseteq_l; eauto using int_promote_typed.
    + eapply int_pre_cast_typed, int_pre_cast_ok_subseteq,
        union_subseteq_r; eauto using int_promote_typed.
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

Let ptr_size (_ : ptr_type (arch_rank A)) : nat := rank_size ptr_rank.
Let align_base (τb : base_type (arch_rank A)) : nat :=
  match τb with
  | voidT => 1
  | intT τi => arch_align A (rank τi)
  | τp.* => arch_align A (@ARank A PtrRank)
  end%BT.
#[global] Instance arch_env : Env (arch_rank A) :=
  natural_env ptr_size align_base (arch_alloc_can_fail A).

Let ptr_size_ne_0 τ : ptr_size τ ≠ 0.
Proof. apply rank_size_ne_0. Qed.
Let align_void : align_base voidT = 1.
Proof. done. Qed.
Let align_int_divide τi : (align_base (intT τi) | rank_size (rank τi)).
Proof. by apply arch_align_size. Qed.
Let align_ptr_divide τp : (align_base (τp.* ) | ptr_size τp).
Proof. by apply arch_align_size. Qed.
#[global] Instance: EnvSpec (arch_rank A).
Proof. by apply natural_env_spec. Qed.
End architecture.
