(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export architecture_spec.

Definition x86 := {|
  big_endian := false;
  char_bits_minus8 := 0;
  char_signedness := Signed;
  short_bytes_log2 := 1;
  int_bytes_log2 := 2;
  long_bytes_log2 := 2;
  longlong_bytes_log2 := 3;
  ptr_bytes_log2 := 2;
  align_minus n := n - 2
|}.

Definition x86_64 := {|
  big_endian := false;
  char_bits_minus8 := 0;
  char_signedness := Signed;
  short_bytes_log2 := 1;
  int_bytes_log2 := 2;
  long_bytes_log2 := 2;
  longlong_bytes_log2 := 3;
  ptr_bytes_log2 := 3;
  align_minus n := n - 3
|}.
