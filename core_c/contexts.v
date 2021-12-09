(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This development makes use of contexts to define the semantics of various
constructs. This file collects some general purpose definitions, theorems, and
tactics. *)
Require Export list.
Require Import tactics.

(** * Contexts with one hole *)
(** The most commonly used kind of context is the one with exactly one hole.
A context equipped with a value for its hole is known as a zipper. We define
an operational type class for substitution. The function [subst E x] is
supposed to substitute the value [x] in the hole of the context [E]. *)
Class Subst A B C := subst: A → B → C.
#[global] Instance: Params (@subst) 4 := {}.
Arguments subst {_ _ _ _} !_ _ / : simpl nomatch.

(** We generally define contexts as lists of singular contexts. For example
for binary trees [Inductive tree := leaf | branch : tree → tree → tree], we
would first define
[Inductive tree_ctx := branchL : tree → tree_ctx | branchR : tree → tree_ctx],
and then the actual context is defined as [list tree_ctx]. A pair
[tree * list tree_ctx] is a zipper, where the second projection is a tree
turned inside-out representing a path from the top. *)

(** We define subsitution for contexts as singular contexts in a generic way. *)
#[global] Instance list_subst `{Subst A B B} : Subst (list A) B B :=
  fix go (l : list A) (b : B) : B := let _ : Subst _ _ _ := @go in
  match l with [] => b | a :: l => subst l (subst a b) end.
Lemma subst_nil `{Subst A B B} b : subst [] b = b.
Proof. done. Qed.
Lemma subst_app `{Subst A B B} (l1 l2 : list A) b :
  subst (l1 ++ l2) b = subst l2 (subst l1 b).
Proof. revert b. induction l1; simpl; auto. Qed.
Lemma subst_snoc `{Subst A B B} (l1 : list A) a b :
  subst (l1 ++ [a]) b = subst a (subst l1 b).
Proof. exact (subst_app l1 [a] b). Qed.

#[global] Instance list_subst_injective `{Subst A B B} :
  (∀ a, Inj (=) (=) (subst a)) →
  ∀ l : list A, Inj (=) (=) (subst l).
Proof.
  intros ? l. red. induction l as [|x l IH]; simpl; intros; auto.
  eapply (inj (subst _)), IH; eassumption.
Qed.

(** * Contexts with multiple holes *)
(** Less commonly used kinds of contexts are those with multiple holes. These
can be represented as dependent types indexed by the number of holes. We define
a class [DepSubst] for substitution. The function [depsubst E xs] is supposed to
substitute the values of the vector [xs] in the holes of [E]. *)
Class DepSubst {I} (A : I → Type) (B : I → Type) C :=
  depsubst : ∀ {i}, A i → B i → C.
#[global] Instance: Params (@depsubst) 6 := {}.
Arguments depsubst {_ _ _ _ _ _} !_ _ / : simpl nomatch.

(** * Tactics *)
(** The tactic [simplify_subst_equality H] simplifies an assumption [H] that
is an equality involving [subst]. It repeatedly tries to use injectivity of
[subst], or to perform case analysis on the context. Such case analyses are
only performed for contexts for which an instance of [DestructSubst] is
declared. *)
Class DestructSubst `(Subst A B C) := {}.

Tactic Notation "simplify_subst_equality" hyp(H) :=
  match type of H with
  | subst ?a _ = subst ?a _ => apply (inj a) in H
  | @subst _ _ _ ?sub ?a _ = _ =>
    is_var a; let ssub := constr:(_ : DestructSubst sub) in
    destruct a; first [discriminate H | injection' H]
  | _ = @subst _ _ _ ?sub ?a _ =>
    is_var a; let ssub := constr:(_ : DestructSubst sub) in
    destruct a; first [discriminate H | injection' H]
  end;
  list_simplifier.
Tactic Notation "simplify_subst_equality" :=
  repeat_on_hyps (fun H => simplify_subst_equality H);
  list_simplifier.

(** The tactic [simplify_list_subst_equality] behaves like the previous tactic,
but then for the case of lists as contexts. *)
Tactic Notation "simplify_list_subst_equality" hyp(H) :=
  match type of H with
  | subst ?l _ = subst ?l _ => apply (list_subst_injective _ l) in H
  | @subst _ _ _ list_subst ?l _ = _ =>
     destruct l as [|?? _] using rev_ind;
       [ rewrite subst_nil in H; simplify_equality
       | rewrite subst_snoc in H; simplify_subst_equality H]
  | _ = @subst _ _ _ list_subst ?l _ =>
     destruct l as [|?? _] using rev_ind;
       [ rewrite subst_nil in H; simplify_equality
       | rewrite subst_snoc in H; simplify_subst_equality H]
  | _ => simplify_subst_equality H
  end.
Tactic Notation "simplify_list_subst_equality" :=
  repeat_on_hyps (fun H => simplify_list_subst_equality H);
  list_simplifier.
