(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines pointers and values. A value is either a pointer to a
memory cell, an unbounded integer, or the special void value (used for
functions without return value and uninitialized memory). *)
Require Import nmap mapset.
Require Export prelude.

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
and define a type class [Locks] to collect locks in various structures. *)
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
Inductive value :=
  | VVoid : value
  | VInt : Z → value
  | VPtr : option index → value.

Instance value_eq_dec (v1 v2 : value) : Decision (v1 = v2).
Proof. solve_decision. Defined.
Instance value_inhabited: Inhabited value := populate VVoid.

(** We define better readable notations for values in the scope
[value_scope]. *)
Delimit Scope value_scope with V.
Bind Scope value_scope with value.
Notation "'void'" := VVoid : value_scope.
Notation "'int' x" := (VInt x) (at level 10) : value_scope.
Notation "'ptr' b" := (VPtr (Some b)) (at level 10) : value_scope.
Notation "'null'" := (VPtr None) : value_scope.

(** Truth and falsehood of values is defined in the C-like way. *)
Definition value_true (v : value) : Prop :=
  match v with
  | void => False
  | int x => x ≠ 0%Z
  | ptr b => True
  | null => False
  end%V.
Definition value_false (v : value) : Prop :=
  match v with
  | void => True
  | int x => x = 0%Z
  | ptr b => False
  | null => True
  end%V.

Definition value_true_false_dec v : { value_true v } + { value_false v }.
Proof.
 by refine (
  match v as v return { value_true v } + { value_false v } with
  | void => right I
  | int x => cast_if_not (decide (x = 0%Z))
  | ptr b => left I
  | null => right I
  end%V).
Defined.

Lemma value_true_false v : value_true v → value_false v → False.
Proof. destruct v as [| |[]]; simpl; auto. Qed.

Definition maybe_ptr (v : value) : option index :=
  match v with
  | ptr a => Some a
  | _ => None
  end%V.
Lemma maybe_ptr_Some v a : maybe_ptr v = Some a ↔ v = (ptr a)%V.
Proof.
  split.
  * by destruct v as [| | [?|]]; intro; simplify_equality.
  * intro. by simplify_equality.
Qed.

(** * Operations on values *)
(** We define a data type of unary and binary operations, and give denotations
for these as partial functions over values. *)
Inductive unop :=
  | NotOp | NegOp.
Inductive binop :=
  | PlusOp | MinusOp | MultOp | DivOp | ModOp
  | LeOp | LtOp | EqOp.

Instance unop_eq_dec (op1 op2 : unop) : Decision (op1 = op2).
Proof. solve_decision. Defined.
Instance binop_eq_dec (op1 op2 : binop) : Decision (op1 = op2).
Proof. solve_decision. Defined.

Definition eval_unop (op : unop) (v : value) : option value :=
  match op, v with
  | NotOp, v =>
    if value_true_false_dec v then Some (int 0) else Some (int 1)
  | NegOp, int x => Some (int (-x))
  | _, _ => None
  end%V.
Definition eval_binop (op : binop) (v1 v2 : value) : option value :=
  match op, v1, v2 with
  | PlusOp, int x1, int x2 => Some (int (x1 + x2))
  | MinusOp, int x1, int x2 => Some (int (x1 - x2))
  | MultOp, int x1, int x2 => Some (int (x1 * x2))
  | DivOp, int x1, int x2 => Some (int (x1 / x2))
  | ModOp, int x1, int x2 => Some (int (Zmod x1 x2))
  | LeOp, int x1, int x2 => Some (int (Z_of_sumbool (decide_rel (≤)%Z x1 x2)))
  | LtOp, int x1, int x2 => Some (int (Z_of_sumbool (decide_rel (<)%Z x1 x2)))
  | EqOp, int x1, int x2 => Some (int (Z_of_sumbool (decide_rel (=) x1 x2)))
  | EqOp, ptr b1, ptr b2 => Some (int (Z_of_sumbool (decide_rel (=) b1 b2)))
  | EqOp, null, null => Some (int 1)
  | EqOp, int _, null => Some (int 0)
  | EqOp, null, int _ => Some (int 0)
  | _, _, _ => None
  end%V.
