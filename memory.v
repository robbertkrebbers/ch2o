(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** The concrete memory model is obtained by instantiating the abstract memory
model with our most expressive implementation of permissions. *)

Require Export permissions abstract_memory.

Notation mem := (amem memperm).

Hint Resolve Freeable__fragment : simpl_mem.
Hint Resolve Writable__fragment : simpl_mem.
Hint Resolve ReadOnly__fragment : simpl_mem.
