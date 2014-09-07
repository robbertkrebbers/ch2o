(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import interpreter ExtrOcamlBasic ExtrOcamlString.

Extraction Blacklist list.
Extraction "parser/Extraction.ml"
  interpreter.interpreter_all interpreter.interpreter_rand.
