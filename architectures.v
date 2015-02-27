(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export architecture_spec.

Definition x86 : architecture.
Proof.
 refine {|
  arch_big_endian := false;
  arch_char_bits := 8;
  arch_size k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank | LongRank => 4
    | LongLongRank => 8
    end;
  arch_align k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank | LongRank => 4
    | LongLongRank => 4
    end;
  arch_ptr_rank := LongRank
 |}; by apply (bool_decide_unpack _); vm_compute.
Defined.

Definition x86_64 : architecture.
Proof.
 refine {|
  arch_big_endian := false;
  arch_char_bits := 8;
  arch_size k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank => 4
    | LongRank | LongLongRank => 8
    end;
  arch_align k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank => 4
    | LongRank | LongLongRank => 8
    end;
  arch_ptr_rank := LongRank
 |}; by apply (bool_decide_unpack _); vm_compute.
Defined.
