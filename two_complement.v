(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a two's complements implementation of the interface for
machine integers. This implementation is parametrized by its endianness and
the number of bits of which a byte consists. This implementation is initial,
that is, it makes as much undefined behavior as possible. *)
Require Import abstract_integers.

(** The data type of integers ranks [irank be Csz] is indexed by a boolean [be]
and a natural [Csz]. The boolean [be] describes whether a big endian (in case
it is [true] or little endian (in case it is [false]) representation should be
used. The natural number [Csz] describes the number of bits of which an
individual byte consists. *)
Inductive irank (be: bool) (Csz: nat) : Set := IKind { ibytes_log2 : nat }.
Arguments ibytes_log2 {_ _} _.

Instance irank_eq_dec {be Csz} (k1 k2 : irank be Csz) : Decision (k1 = k2).
Proof. solve_decision. Defined.

Local Instance: IntCoding (irank be Csz) := {
  char_rank := IKind be Csz 0;
  short_rank := IKind be Csz 1;
  int_rank := IKind be Csz 2;
  long_rank n := IKind be Csz (2 + n);
  ptr_rank := IKind be Csz 3;
  char_bits := Csz;
  rank_size := λ k, 2 ^ ibytes_log2 k;
  endianize := λ _, if be then reverse else id;
  deendianize := λ _, if be then reverse else id
}.
Instance: IntEnv (irank be Csz) := {
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

Local Instance: PropHolds (8 ≤ Csz) → IntCodingSpec (irank be Csz).
Proof.
  intros Csz be. split.
  * done.
  * done.
  * unfold rank_size; simpl. intros. by apply Nat.neq_0_lt_0, Nat.pow_nonzero.
  * unfold rank_size; intros [i] [j] ?; simplify_equality'; f_equal.
    apply Nat.pow_inj_r with 2; lia.
  * intros. unfold endianize; simpl.
    by destruct be; simpl; rewrite ?reverse_Permutation.
  * intros. unfold deendianize, endianize; simpl.
    by destruct be; simpl; rewrite ?reverse_involutive.
  * intros. unfold deendianize, endianize; simpl.
    by destruct be; simpl; rewrite ?reverse_involutive.
Qed.
Instance: PropHolds (8 ≤ Csz) → IntEnvSpec (irank be Csz).
Proof.
  intros Csz be. split.
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
