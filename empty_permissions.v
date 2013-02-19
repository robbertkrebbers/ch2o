(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files shows that the unit type forms a valid trivial permission
system with no permissions at all. The permission kind is [Free] (i.e.
everything is permitted), and all operations are no-ops.*)
Require Export abstract_permissions.

Instance unit_perm_kind: PermKind unit := λ _, Free.
Instance unit_perm_lock: PermLock unit := λ _ _, ().

Inductive unit_subseteq: SubsetEq unit :=
  | tt_subseteq : () ⊆ ().
Existing Instance unit_subseteq.

Inductive unit_disjoint: Disjoint unit := .
Existing Instance unit_disjoint.

Instance unit_union: Union unit := λ _ _, ().
Instance unit_difference: Difference unit := λ _ _, ().

Instance unit_subseteq_dec (u1 u2 : unit) : Decision (u1 ⊆ u2).
Proof. left. by destruct u1, u2. Defined.
Instance unit_disjoint_dec (u1 u2 : unit) : Decision (u1 ⊥ u2).
Proof. right. destruct 1. Defined.

Instance: Permissions unit.
Proof.
  split.
  * repeat split; by repeat intros [].
  * destruct 1.
  * by destruct 1.
  * intros ? [? []].
  * destruct 1.
  * by intros [].
  * by intros [].
  * by intros [].
  * by intros [] [] [].
  * by intros [] [].
  * destruct 1.
  * destruct 1.
  * destruct 1.
  * by intros [] [] [].
  * destruct 1.
  * by intros [] [] [? []].
  * by intros [] [] [? []].
Qed.
