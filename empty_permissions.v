(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files shows that the unit type forms a valid trivial permission
system with no permissions at all. The permission kind is [Free] (i.e.
everything is allowed), and all operations are no-ops.*)
Require Export abstract_permissions.

Instance unit_perm_ops: PermissionsOps unit := {
  perm_kind := λ _, Free;
  perm_lock_ := λ _ _, ();
  perm_subseteq := λ _ _, True;
  perm_disjoint := λ _ _, False;
  perm_union := λ _ _, ();
  perm_difference := λ _ _, ()
}.

Instance: Permissions unit.
Proof.
  split; try done.
  * repeat split; by repeat intros [].
  * by intros [] [].
  * by intros [] [??].
  * by intros [].
  * by intros [].
  * by intros [] [] [? []].
  * by intros [] [] [? []].
Qed.
