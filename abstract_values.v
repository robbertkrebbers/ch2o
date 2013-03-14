(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines pointers and values. A value is either a pointer to a
memory cell, a machine integer, or the special void value (used for
functions without return value and uninitialized memory). *)
Require Import nmap mapset.
Require Export abstract_permissions abstract_integers.

(** * Indexes into the memory *)
(** We define indexes into the memory as binary naturals and use the [Nmap]
implementation to obtain efficient finite maps and finite sets with these
indexes as keys. *)
Definition index := N.
Definition indexmap := Nmap.
Notation indexset := (mapset indexmap).

Instance index_dec: ∀ i1 i2 : index, Decision (i1 = i2) := decide_rel (=).
Instance index_fresh_`{FinCollection index C} : Fresh index C := _.
Instance index_fresh_spec `{FinCollection index C} : FreshSpec index C := _.
Instance index_inhabited: Inhabited index := populate 0%N.

Instance indexmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : indexmap A, Decision (m1 = m2) := decide_rel (=).
Instance indexmap_empty {A} : Empty (indexmap A) := @empty (Nmap A) _.
Instance indexmap_lookup {A} : Lookup index A (indexmap A) :=
  @lookup _ _ (Nmap A) _.
Instance indexmap_partial_alter {A} : PartialAlter index A (indexmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance indexmap_to_list {A} : FinMapToList index A (indexmap A) :=
  @map_to_list _ _ (Nmap A) _.
Instance indexmap_merge: Merge indexmap := @merge Nmap _.
Instance indexmap_fmap: FMap indexmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap index indexmap := _.

Instance indexmap_dom {A} : Dom (indexmap A) indexset := mapset_dom.
Instance: FinMapDom index indexmap indexset := mapset_dom_spec.

Typeclasses Opaque index indexmap.

(** * Locked locations *)
(** In order to model sequence points, we have to keep track of sets of
locations that cannot be written to or read from. We call such locations locked,
and define a type class [Locks] to collect locks in various data structures. *)
Class Locks A := locks: A → indexset.
Arguments locks {_ _} !_ / : simpl nomatch.

Instance list_locks `{Locks A} : Locks (list A) :=
  fix go (l : list A) : indexset :=
  let _ : Locks _ := @go in
  match l with
  | [] => ∅
  | a :: l => locks a ∪ locks l
  end.

Lemma locks_nil `{Locks A} : locks [] = ∅.
Proof. done. Qed.
Lemma locks_app `{Locks A} (l1 l2 : list A) :
  locks (l1 ++ l2) = locks l1 ∪ locks l2.
Proof. apply elem_of_equiv_L. induction l1; esolve_elem_of. Qed.
Lemma locks_snoc `{Locks A} (l1 : list A) a :
  locks (l1 ++ [a]) = locks l1 ∪ locks a.
Proof. rewrite locks_app. simpl. by rewrite (right_id_eq ∅ (∪)). Qed.

(** * Values *)
(** A value is inductively defined to be either a special void value (used for
functions without return value and uninitialized memory), an unbounded integer,
or a pointer represented by an index into the memory. This index is optional
so as to model the NULL pointer. *)
Inductive val_ (Vi : Set) : Set :=
  | VVoid : val_ Vi
  | VInt : Vi → val_ Vi
  | VPtr : option index → val_ Vi.
Arguments VVoid {_}.
Arguments VInt {_} _.
Arguments VPtr {_} _.

Instance val_eq_dec {Vi : Set} `{∀ i1 i2 : Vi, Decision (i1 = i2)} :
  ∀ v1 v2 : val_ Vi, Decision (v1 = v2).
Proof. solve_decision. Defined.
Instance val_inhabited {Vi} : Inhabited (val_ Vi) := populate VVoid.

(** We define better readable notations for values in the scope
[val_scope]. *)
Delimit Scope val_scope with V.
Bind Scope val_scope with val_.
Notation "'voidc'" := VVoid : val_scope.
Notation "'intc' x" := (VInt x) (at level 10) : val_scope.
Notation "'ptrc' b" := (VPtr (Some b)) (at level 10) : val_scope.
Notation "'nullc'" := (VPtr None) : val_scope.

Section values.
Context `{IntEnvSpec Ti Vi}.

(** Truth and falsehood of values is defined in the C-like way. *)
Definition val_true (v : val_ Vi) : Prop :=
  match v with
  | voidc => False
  | intc x => int_to_Z x ≠ 0%Z
  | ptrc b => True
  | nullc => False
  end%V.
Definition val_false (v : val_ Vi) : Prop :=
  match v with
  | voidc => True
  | intc x => int_to_Z x = 0%Z
  | ptrc b => False
  | nullc => True
  end%V.

Definition val_true_false_dec (v : val_ Vi) :
  { val_true v } + { val_false v }.
Proof.
 by refine (
  match v as v return { val_true v } + { val_false v } with
  | voidc => right I
  | intc x => cast_if_not (decide (int_to_Z x = 0%Z))
  | ptrc b => left I
  | nullc => right I
  end%V).
Defined.

Lemma val_true_false (v : val_ Vi) :
  val_true v → val_false v → False.
Proof. by destruct v as [| |[]]. Qed.

Definition maybe_ptr (v : val_ Vi) : option index :=
  match v with
  | ptrc a => Some a
  | _ => None
  end%V.
Lemma maybe_ptr_Some v a : maybe_ptr v = Some a ↔ v = (ptrc a)%V.
Proof.
  split.
  * by destruct v as [| | [?|]]; intro; simplify_equality.
  * intro. by subst.
Qed.

(** * Operations on values *)
Definition eval_unop (op : unop) (v : val_ Vi) : option (val_ Vi) :=
  match v with
  | intc x => i ← int_eval_unop op x; Some (intc i)
  | _ => None
  end%V.
Definition eval_binop (op : binop) (v1 v2 : val_ Vi) : option (val_ Vi) :=
  match v1, v2 with
  | intc x1, intc x2 => i ← int_eval_binop op x1 x2; Some (intc i)
  | ptrc p1, ptrc p2 =>
     match op with
     | EqOp => Some $ intc (int_of_sumbool (decide (p1 = p2)))
     | _ => None
     end
  | _, _ => None
  end%V.
Definition eval_cast (τ : Ti) (v : val_ Vi) : option (val_ Vi) :=
  match v with
  | intc x => i ← int_cast τ x; Some (intc i)
  | _ => None
  end%V.
End values.
