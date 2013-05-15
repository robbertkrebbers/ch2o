(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file provides an axiomatization of the domain function of finite
maps. We provide such an axiomatization, instead of implementing the domain
function in a generic way, to allow more efficient implementations. *)
Require Export collections fin_maps.

Class FinMapDom K M D `{!FMap M}
    `{∀ A, Lookup K A (M A)} `{∀ A, Empty (M A)} `{∀ A, PartialAlter K A (M A)}
    `{!Merge M} `{∀ A, FinMapToList K A (M A)}
    `{∀ i j : K, Decision (i = j)}
    `{∀ A, Dom (M A) D} `{ElemOf K D} `{Empty D} `{Singleton K D}
    `{Union D}`{Intersection D} `{Difference D} := {
  finmap_dom_map :>> FinMap K M;
  finmap_dom_collection :>> Collection K D;
  elem_of_dom {A} (m : M A) i : i ∈ dom D m ↔ is_Some (m !! i)
}.

Section fin_map_dom.
Context `{FinMapDom K M D}.

Lemma not_elem_of_dom {A} (m : M A) i : i ∉ dom D m ↔ m !! i = None.
Proof. by rewrite elem_of_dom, eq_None_not_Some. Qed.

Lemma subseteq_dom {A} (m1 m2 : M A) : m1 ⊆ m2 → dom D m1 ⊆ dom D m2.
Proof.
  unfold subseteq, map_subseteq, collection_subseteq.
  intros ??. rewrite !elem_of_dom. inversion 1. eauto.
Qed.
Lemma subset_dom {A} (m1 m2 : M A) : m1 ⊂ m2 → dom D m1 ⊂ dom D m2.
Proof.
  intros [Hss1 Hss2]. split.
  { by apply subseteq_dom. }
  intros Hdom. destruct Hss2. intros i x Hi.
  specialize (Hdom i). rewrite !elem_of_dom in Hdom.
  destruct Hdom; eauto. erewrite (Hss1 i) in Hi by eauto. congruence.
Qed.

Lemma dom_empty {A} : dom D (@empty (M A) _) ≡ ∅.
Proof.
  split; intro.
  * rewrite elem_of_dom, lookup_empty. by inversion 1.
  * solve_elem_of.
Qed.
Lemma dom_empty_inv {A} (m : M A) : dom D m ≡ ∅ → m = ∅.
Proof.
  intros E. apply map_empty. intros. apply not_elem_of_dom.
  rewrite E. solve_elem_of.
Qed.

Lemma dom_insert {A} (m : M A) i x : dom D (<[i:=x]>m) ≡ {[ i ]} ∪ dom D m.
Proof.
  apply elem_of_equiv. intros j. rewrite elem_of_union, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_insert_Some.
  destruct (decide (i = j)); esolve_elem_of.
Qed.
Lemma dom_insert_subseteq {A} (m : M A) i x : dom D m ⊆ dom D (<[i:=x]>m).
Proof. rewrite (dom_insert _). solve_elem_of. Qed.
Lemma dom_insert_subseteq_compat_l {A} (m : M A) i x X :
  X ⊆ dom D m → X ⊆ dom D (<[i:=x]>m).
Proof. intros. transitivity (dom D m); eauto using dom_insert_subseteq. Qed.

Lemma dom_singleton {A} (i : K) (x : A) : dom D {[(i, x)]} ≡ {[ i ]}.
Proof.
  unfold singleton at 1, map_singleton.
  rewrite dom_insert, dom_empty. solve_elem_of.
Qed.

Lemma dom_delete {A} (m : M A) i : dom D (delete i m) ≡ dom D m ∖ {[ i ]}.
Proof.
  apply elem_of_equiv. intros j. rewrite elem_of_difference, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_delete_Some. esolve_elem_of.
Qed.
Lemma delete_partial_alter_dom {A} (m : M A) i f :
  i ∉ dom D m → delete i (partial_alter f i m) = m.
Proof. rewrite not_elem_of_dom. apply delete_partial_alter. Qed.
Lemma delete_insert_dom {A} (m : M A) i x :
  i ∉ dom D m → delete i (<[i:=x]>m) = m.
Proof. rewrite not_elem_of_dom. apply delete_insert. Qed.

Lemma map_disjoint_dom {A} (m1 m2 : M A) : m1 ⊥ m2 ↔ dom D m1 ∩ dom D m2 ≡ ∅.
Proof.
  unfold disjoint, map_disjoint, map_intersection_forall.
  rewrite elem_of_equiv_empty. setoid_rewrite elem_of_intersection.
  setoid_rewrite elem_of_dom. unfold is_Some. naive_solver.
Qed.
Lemma map_disjoint_dom_1 {A} (m1 m2 : M A) : m1 ⊥ m2 → dom D m1 ∩ dom D m2 ≡ ∅.
Proof. apply map_disjoint_dom. Qed.
Lemma map_disjoint_dom_2 {A} (m1 m2 : M A) : dom D m1 ∩ dom D m2 ≡ ∅ → m1 ⊥ m2.
Proof. apply map_disjoint_dom. Qed.

Lemma dom_union {A} (m1 m2 : M A) : dom D (m1 ∪ m2) ≡ dom D m1 ∪ dom D m2.
Proof.
  apply elem_of_equiv. intros i. rewrite elem_of_union, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_union_Some_raw.
  destruct (m1 !! i); naive_solver.
Qed.

Lemma dom_intersection {A} (m1 m2 : M A) :
  dom D (m1 ∩ m2) ≡ dom D m1 ∩ dom D m2.
Proof.
  apply elem_of_equiv. intros i. rewrite elem_of_intersection, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_intersection_Some. naive_solver.
Qed.

Lemma dom_difference {A} (m1 m2 : M A) : dom D (m1 ∖ m2) ≡ dom D m1 ∖ dom D m2.
Proof.
  apply elem_of_equiv. intros i. rewrite elem_of_difference, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_difference_Some.
  destruct (m2 !! i); naive_solver.
Qed.
End fin_map_dom.
