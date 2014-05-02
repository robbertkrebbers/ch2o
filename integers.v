(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a two's complements implementation of the interface for
machine integers. This implementation is parametrized by its endianness and
the number of bits of which a byte consists. This implementation is convervative
in the sense that it makes as much undefined behavior as possible.  *)
Require Import abstract_integers.

(** The data type of integers [int_ be Csz] is indexed by a boolean [be]
and a natural [Csz]. The boolean [be] describes whether a big endian (in case
it is [true] or little endian (in case it is [false]) representation should be
used. The natural number [Csz] describes the number of bits of which an
individual byte consists. We equip the data type with a boolean proof of being
in range to ensure canonicity. *)
Inductive irank (be: bool) (Csz: nat) : Set := IKind {
  IBytes : nat; IBytes_pos : 0 < IBytes
}.
Arguments IBytes {_ _} _.
Arguments IBytes_pos {_ _} _.

Instance irank_eq_dec {be Csz} (k1 k2 : irank be Csz) : Decision (k1 = k2).
Proof.
 refine
  match k1, k2 with IKind b1 _, IKind b2 _ => cast_if (decide (b1 = b2)) end;
  [subst; f_equal; apply (proof_irrel _) | congruence].
Defined.

Local Instance: IntCoding (irank be Csz) := {
  char_rank := IKind be Csz 1 (bool_decide_unpack (0 < 1) I);
  int_rank := IKind be Csz 4 (bool_decide_unpack (0 < 4) I);
  ptr_rank := IKind be Csz 8 (bool_decide_unpack (0 < 8) I);
  char_bits := Csz;
  rank_size := IBytes;
  endianize := λ _, if be then reverse else id;
  deendianize := λ _, if be then reverse else id
}.
Instance: IntEnv (irank be Csz) := {
  int_binop_ok := int_binop_ok_;
  int_binop := int_binop_;
  int_cast_ok := int_cast_ok_;
  int_cast := int_cast_
}.

Local Instance: PropHolds (8 ≤ Csz) → IntCodingSpec (irank be Csz).
Proof.
  intros Csz be. split.
  * done.
  * done.
  * by intros [??].
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
  * apply int_binop_ok_typed_.
  * done.
  * done.
  * apply int_cast_ok_typed_.
  * done.
Qed.
