(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import interpreter ExtrOcamlBasic ExtrOcamlString architectures.

Extraction Blacklist list.
Extraction "parser/Extracted.ml"
  interpreter.interpreter_all_eval
  interpreter.interpreter_rand_eval
  interpreter.interpreter_initial_eval
  x86 x86_64.
