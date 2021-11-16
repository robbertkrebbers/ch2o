(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files implements an efficient implementation of finite maps whose keys
range over Coq's data type of strings [string]. The implementation uses radix-2
search trees (uncompressed Patricia trees) as implemented in the file [pmap]
and guarantees logarithmic-time operations. *)

Require Export base.
From stdpp Require Export stringmap.

Lemma map_subseteq_inv_L {A} (m1 m2 : stringmap A) : m1 ⊆ m2 → m1 ⊂ m2 ∨ m1 = m2.
Proof.
  intros. destruct (decide (m2 ∖ m1 = ∅)) as [Hm21|(i&x&Hi)%map_choose].
  - right. by rewrite <-(map_difference_union m1 m2), Hm21, (right_id_L _ _).
  - left. apply lookup_difference_Some in Hi as [??].
    apply map_subset_alt; eauto.
Qed.