(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file instantiates values with a concrete implementation of machine
integers; namely little endian two's complement integers with bytes whose
bit length is 8. *)

Require Export abstract_values.
Require Import integers.

Notation int_type := int_type. (* otherwise it won't be exported *)
Notation int := (int_ false 8).
Notation val := (val_ int).
