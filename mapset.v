(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files gives an implementation of finite sets using finite maps with
elements of the unit type. Since maps enjoy extensional equality, the
constructed finite sets do so as well. *)
Require Export fin_map_dom.

Record mapset (Mu : Type) := Mapset { mapset_car: Mu }.
Arguments Mapset {_} _.
Arguments mapset_car {_} _.

Section mapset.
Context `{FinMap K M}.

Instance mapset_elem_of: ElemOf K (mapset (M unit)) := λ x X,
  mapset_car X !! x = Some ().
Instance mapset_empty: Empty (mapset (M unit)) := Mapset ∅.
Instance mapset_singleton: Singleton K (mapset (M unit)) := λ x,
  Mapset {[ (x,()) ]}.
Instance mapset_union: Union (mapset (M unit)) := λ X1 X2,
  let (m1) := X1 in let (m2) := X2 in Mapset (m1 ∪ m2).
Instance mapset_intersection: Intersection (mapset (M unit)) := λ X1 X2,
  let (m1) := X1 in let (m2) := X2 in Mapset (m1 ∩ m2).
Instance mapset_difference: Difference (mapset (M unit)) := λ X1 X2,
  let (m1) := X1 in let (m2) := X2 in Mapset (m1 ∖ m2).
Instance mapset_elems: Elements K (mapset (M unit)) := λ X,
  let (m) := X in fst <$> map_to_list m.

Lemma mapset_eq (X1 X2 : mapset (M unit)) : X1 = X2 ↔ ∀ x, x ∈ X1 ↔ x ∈ X2.
Proof.
  split; [by intros ->|].
  destruct X1 as [m1], X2 as [m2]. simpl. intros E.
  f_equal. apply map_eq. intros i. apply option_eq. intros []. by apply E.
Qed.

Global Instance mapset_eq_dec `{∀ m1 m2 : M unit, Decision (m1 = m2)}
  (X1 X2 : mapset (M unit)) : Decision (X1 = X2) | 1.
Proof.
 refine
  match X1, X2 with Mapset m1, Mapset m2 => cast_if (decide (m1 = m2)) end;
  abstract congruence.
Defined.
Global Instance mapset_elem_of_dec x (X : mapset (M unit)) :
  Decision (x ∈ X) | 1.
Proof. solve_decision. Defined.

Instance: Collection K (mapset (M unit)).
Proof.
  split; [split | | ].
  * unfold empty, elem_of, mapset_empty, mapset_elem_of.
    simpl. intros. by simpl_map.
  * unfold singleton, elem_of, mapset_singleton, mapset_elem_of.
    simpl. by split; intros; simplify_map_equality.
  * unfold union, elem_of, mapset_union, mapset_elem_of.
    intros [m1] [m2] ?. simpl. rewrite lookup_union_Some_raw.
    destruct (m1 !! x) as [[]|]; tauto.
  * unfold intersection, elem_of, mapset_intersection, mapset_elem_of.
    intros [m1] [m2] ?. simpl. rewrite lookup_intersection_Some.
    assert (is_Some (m2 !! x) ↔ m2 !! x = Some ()).
    { split; eauto. by intros [[] ?]. }
    naive_solver.
  * unfold difference, elem_of, mapset_difference, mapset_elem_of.
    intros [m1] [m2] ?. simpl. rewrite lookup_difference_Some.
    destruct (m2 !! x) as [[]|]; intuition congruence.
Qed.
Global Instance: PartialOrder (@subseteq (mapset (M unit)) _).
Proof. split; try apply _. intros ????. apply mapset_eq. intuition. Qed.
Global Instance: FinCollection K (mapset (M unit)).
Proof.
  split.
  * apply _.
  * unfold elements, elem_of at 2, mapset_elems, mapset_elem_of.
    intros [m] x. simpl. rewrite elem_of_list_fmap. split.
    + intros ([y []] &?& Hy). subst. by rewrite <-elem_of_map_to_list.
    + intros. exists (x, ()). by rewrite elem_of_map_to_list.
  * unfold elements, mapset_elems. intros [m]. simpl.
    apply NoDup_fst_map_to_list.
Qed.

Definition mapset_map_with {A B} (f: bool → A → B)
    (X : mapset (M unit)) : M A → M B :=
  let (m) := X in merge (λ x y,
    match x, y with
    | Some _, Some a => Some (f true a)
    | None, Some a => Some (f false a)
    | _, None => None
    end) m.
Definition mapset_dom_with {A} (f : A → bool) (m : M A) : mapset (M unit) :=
  Mapset $ merge (λ x _,
    match x with
    | Some a => if f a then Some () else None
    | None => None
    end) m (@empty (M A) _).

Lemma lookup_mapset_map_with {A B} (f : bool → A → B) X m i :
  mapset_map_with f X m !! i = f (bool_decide (i ∈ X)) <$> m !! i.
Proof.
  destruct X as [mX]. unfold mapset_map_with, elem_of, mapset_elem_of.
  rewrite lookup_merge by done. simpl.
  by case_bool_decide; destruct (mX !! i) as [[]|], (m !! i).
Qed.
Lemma elem_of_mapset_dom_with {A} (f : A → bool) m i :
  i ∈ mapset_dom_with f m ↔ ∃ x, m !! i = Some x ∧ f x.
Proof.
  unfold mapset_dom_with, elem_of, mapset_elem_of.
  simpl. rewrite lookup_merge by done. destruct (m !! i) as [a|].
  * destruct (Is_true_reflect (f a)); naive_solver.
  * naive_solver.
Qed.

Instance mapset_dom {A} : Dom (M A) (mapset (M unit)) :=
  mapset_dom_with (λ _, true).
Instance mapset_dom_spec: FinMapDom K M (mapset (M unit)).
Proof.
  split; try apply _. intros. unfold dom, mapset_dom.
  rewrite elem_of_mapset_dom_with. unfold is_Some. naive_solver.
Qed.
End mapset.

(** These instances are declared using [Hint Extern] to avoid too
eager type class search. *)
Hint Extern 1 (ElemOf _ (mapset _)) =>
  eapply @mapset_elem_of : typeclass_instances.
Hint Extern 1 (Empty (mapset _)) =>
  eapply @mapset_empty : typeclass_instances.
Hint Extern 1 (Singleton _ (mapset _)) =>
  eapply @mapset_singleton : typeclass_instances.
Hint Extern 1 (Union (mapset _)) =>
  eapply @mapset_union : typeclass_instances.
Hint Extern 1 (Intersection (mapset _)) =>
  eapply @mapset_intersection : typeclass_instances.
Hint Extern 1 (Difference (mapset _)) =>
  eapply @mapset_difference : typeclass_instances.
Hint Extern 1 (Elements _ (mapset _)) =>
  eapply @mapset_elems : typeclass_instances.
Arguments mapset_eq_dec _ _ _ _ : simpl never.
