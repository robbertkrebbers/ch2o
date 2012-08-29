(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements the operations on non computable subsets [A → Prop]
over some carrier [A]. *)
Require Export base.

Definition subset A := A → Prop.

Instance subset_elem_of {A} : ElemOf A (subset A) | 100 := λ x P, P x.
Instance subset_empty {A} : Empty (subset A) := λ _, False.
Instance subset_singleton {A} : Singleton A (subset A) := (=).
Instance subset_union {A} : Union (subset A) := λ P Q x, P x ∨ Q x.
Instance subset_intersection {A} : Intersection (subset A) := λ P Q x,
  P x ∧ Q x.
Instance subset_difference {A} : Difference (subset A) := λ P Q x, P x ∧ ¬Q x.
Instance subset_map {A} : Map A (subset A) := λ f P x, ∃ y, f y = x ∧ P y.

Instance subset_container: Collection A (subset A) | 100.
Proof. firstorder try congruence. Qed.
