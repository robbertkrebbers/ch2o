(** This file collects general purpose definitions and theorems on lists that
are not in the Coq standard library. *)
Require Export base.

Definition imap_go {A B} (f : nat → A → B) : nat → list A → list B :=
  fix go (n : nat) (l : list A) :=
  match l with [] => [] | x :: l => f n x :: go (S n) l end.

(** * Basic tactics on lists *)
(** The tactic [discriminate_list_equality] discharges a goal if it contains
a list equality involving [(::)] and [(++)] of two lists that have a different
length as one of its hypotheses. *)
Tactic Notation "discriminate_list_equality" hyp(H) :=
  apply (f_equal length) in H;
  repeat (csimpl in H || rewrite app_length in H); exfalso; lia.
Tactic Notation "discriminate_list_equality" :=
  match goal with
  | H : @eq (list _) _ _ |- _ => discriminate_list_equality H
  end.

(** The tactic [simplify_list_equality] simplifies hypotheses involving
equalities on lists using injectivity of [(::)] and [(++)]. Also, it simplifies
lookups in singleton lists. *)
Lemma app_injective_1 {A} (l1 k1 l2 k2 : list A) :
  length l1 = length k1 → l1 ++ l2 = k1 ++ k2 → l1 = k1 ∧ l2 = k2.
Proof. revert k1. induction l1; intros [|??]; naive_solver. Qed.