Require Export base.

Definition subset A := A → Prop.

Instance subset_elem_of {A} : ElemOf A (subset A) | 100 := λ x P, P x.
Instance subset_empty {A} : Empty (subset A) := λ _, False.
Instance subset_singleton {A} : Singleton A (subset A) := (=).
Instance subset_union {A} : Union (subset A) := λ P Q x, P x ∨ Q x.
Instance subset_inter {A} : Intersection (subset A) := λ P Q x, P x ∧ Q x.
Instance subset_diff {A} : Difference (subset A) := λ P Q x, P x ∧ ¬Q x.
Instance subset_map {A} : Map A (subset A) := λ f P x, ∃ y, f y = x ∧ P y.

Instance subset_container: Collection A (subset A) | 100.
Proof. firstorder try congruence. Qed.
