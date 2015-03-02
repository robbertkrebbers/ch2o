(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export architecture_spec.

Definition ilp32 : architecture_sizes.
Proof.
 refine {|
  arch_char_bits := 8;
  arch_size k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank | LongRank | PtrRank => 4
    | LongLongRank => 8
    end;
  arch_align k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank | LongRank | PtrRank => 4
    | LongLongRank => 8
    end
 |}; by apply (bool_decide_unpack _); vm_compute.
Defined.

(** See http://en.wikipedia.org/wiki/64-bit_computing#64-bit_data_models *)
(** LLP64 is used by Microsoft Windows (x86-64 and IA-64) *)
Definition llp64 : architecture_sizes.
Proof.
 refine {|
  arch_char_bits := 8;
  arch_size k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank | LongRank => 4
    | PtrRank | LongLongRank => 8
    end;
  arch_align k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank | LongRank => 4
    | PtrRank | LongLongRank => 8
    end
 |}; by apply (bool_decide_unpack _); vm_compute.
Defined.

(** LP64 is used by most Unix and Unix-like systems, e.g. Solaris, Linux, BSD,
and OS X; z/OS *)
Definition lp64 : architecture_sizes.
Proof.
 refine {|
  arch_char_bits := 8;
  arch_size k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank => 4
    | LongRank | PtrRank | LongLongRank => 8
    end;
  arch_align k :=
    match k with
    | CharRank => 1 | ShortRank => 2 | IntRank => 4
    | LongRank | PtrRank | LongLongRank => 8
    end
 |}; by apply (bool_decide_unpack _); vm_compute.
Defined.
