(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import base fin_maps.
Require Export ctrees memory_basics.

(** We pack the memory into a record so as to avoid ambiguity with already
existing type class instances for finite maps. *)
Inductive cmap_elem (K : iType) (A : sType) : iType :=
  | Freed : type K → cmap_elem K A
  | Obj : ctree K A → bool → cmap_elem K A.
Arguments Freed {_ _} _.
Arguments Obj {_ _} _ _.

#[global] Instance maybe_Obj {K A} : Maybe2 (@Obj K A) := λ x,
  match x with Obj w β => Some (w,β) | _ => None end.
Definition cmap_elem_Forall {K A} (P : Prop) (Q : ctree K A → Prop)
    (x : cmap_elem K A) : Prop :=
  match x with Freed _ => P | Obj w _ => Q w end.
Definition cmap_elem_map {K A} (f : ctree K A → ctree K A)
    (x : cmap_elem K A) : cmap_elem K A :=
  match x with Freed τ => Freed τ | Obj w β => Obj (f w) β end.
Definition cmap_elem_relation {K A} (P : Prop)
    (Q : ctree K A → ctree K A → Prop) (x y : cmap_elem K A) : Prop :=
  match x, y with
  | Freed τ1, Freed τ2 => P ∧ τ1 = τ2
  | Obj w1 β1, Obj w2 β2 => Q w1 w2 ∧ β1 = β2
  | _, _ => False
  end.
Definition cmap_elem_map2 {K A} (f : ctree K A → ctree K A → ctree K A)
    (x y : cmap_elem K A) : cmap_elem K A :=
  match x, y with
  | Obj w1 β, Obj w2 _ => Obj (f w1 w2) β
  | Obj w β, _ | _, Obj w β => Obj w β
  | Freed τ, _ => Freed τ
 end.
#[global] Instance cmap_elem_eq_dec {K A} `{EqDecision K, EqDecision A}: EqDecision (cmap_elem K A).
Proof. solve_decision. Defined.
#[global] Instance cmap_elem_Forall_dec {K A} `{Decision P, ∀ w, Decision (Q w)}
  (x : cmap_elem K A) : Decision (cmap_elem_Forall P Q x).
Proof. destruct x; apply _. Defined.
#[global] Instance cmap_elem_relation_dec {K A} `{EqDecision K,
    Decision P, ∀ w1 w2, Decision (Q w1 w2)}
  (x y : cmap_elem K A) : Decision (cmap_elem_relation P Q x y).
Proof. destruct x, y; apply _. Defined.
#[global] Instance: `{Inj (=) (=) (@Freed K A)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj2 (=) (=) (=) (@Obj K A)}.
Proof. by injection 1. Qed.

Record cmap (K : iType) (A : sType) : iType :=
  CMap { cmap_car : indexmap (cmap_elem K A) }.
Arguments CMap {_ _} _.
Arguments cmap_car {_ _} _.
Add Printing Constructor cmap.
#[global] Instance: `{Inj (=) (=) (@CMap K A)}.
Proof. by injection 1. Qed.

#[global, refine] Instance cmap_ops {K : iType} `{EqDecision K,
    SeparationOps A} : SeparationOps (cmap K A) := {
  sep_empty := CMap ∅;
  sep_union m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in
    CMap (union_with (λ x y, Some (cmap_elem_map2 (∪) x y)) m1 m2);
  sep_difference m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in
    CMap (difference_with (λ x y,
      '(w1,β) ← maybe2 Obj x; '(w2,_) ← maybe2 Obj y;
      let w := w1 ∖ w2 in guard (¬ctree_empty w); Some (Obj w β)) m1 m2);
  sep_half m := let (m) := m in CMap (cmap_elem_map (ctree_map half) <$> m);
  sep_valid m :=
    let (m) := m in
    map_Forall (λ _,
      cmap_elem_Forall True (λ w, ctree_valid w ∧ ¬ctree_empty w)) m;
  sep_disjoint m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in map_relation
      (cmap_elem_relation False (λ w1 w2,
        w1 ## w2 ∧ ¬ctree_empty w1 ∧ ¬ctree_empty w2))
      (cmap_elem_Forall True (λ w, ctree_valid w ∧ ¬ctree_empty w))
      (cmap_elem_Forall True (λ w, ctree_valid w ∧ ¬ctree_empty w)) m1 m2;
  sep_splittable m :=
    let (m) := m in
    map_Forall (λ _, cmap_elem_Forall False
      (λ w, ctree_valid w ∧ ¬ctree_empty w ∧ ctree_splittable w)) m;
  sep_subseteq m1 m2 :=
    let (m1) := m1 in let (m2) := m2 in map_relation
      (cmap_elem_relation True (λ w1 w2, w1 ⊆ w2 ∧ ¬ctree_empty w1))
      (λ _, False)
      (cmap_elem_Forall True (λ w, ctree_valid w ∧ ¬ctree_empty w)) m1 m2;
  sep_unmapped m := cmap_car m = ∅;
  sep_unshared m := False
}.
Proof.
  * intros []; apply _.
  * intros [] []; eapply map_relation_dec; apply _.
  * intros [] []; eapply map_relation_dec; apply _.
  * solve_decision.
  * intros []; apply _.
Defined.

#[global] Instance cmap_sep {K : iType} `{EqDecision K, Separation A} :
  Separation (cmap K A).
Proof.
  split.
  * destruct (sep_inhabited A) as (x&?&?).
    generalize (String.EmptyString : tag); intros t.
    eexists (CMap {[ fresh (∅: indexset) := Obj (MUnionAll t [x]) false ]}).
    split; [|by intro]. intros o w ?; simplify_map_eq. split.
    + by constructor; rewrite Forall_singleton.
    + inversion_clear 1; decompose_Forall_hyps; eauto using sep_unmapped_empty.
  * sep_unfold; intros [m1] [m2] Hm o w1; specialize (Hm o); simpl in *.
    intros Hx. rewrite Hx in Hm.
    destruct w1, (m2 !! o) as [[]|]; simpl in *;
      intuition eauto using ctree_disjoint_valid_l.
  * sep_unfold; intros [m1] [m2] Hm o w; specialize (Hm o); simpl in *.
    rewrite lookup_union_with. intros.
    destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|];
      simplify_equality'; intuition eauto
      using ctree_union_valid, ctree_positive_l.
  * sep_unfold. intros [m] Hm o; specialize (Hm o); simplify_map_eq.
    destruct (m !! o) as [[]|]; eauto.
  * sep_unfold; intros [m] ?; f_equal'. by rewrite (left_id_L ∅ _).
  * sep_unfold. intros [m1] [m2] Hm o; specialize (Hm o); simpl in *.
    destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; simpl in *; intuition.
  * sep_unfold; intros [m1] [m2] Hm; f_equal'. apply stdpp.fin_maps.union_with_comm.
    intros o [] [] ??; specialize (Hm o); unfold option_relation in *; simplify_option_eq;
      intuition auto using ctree_commutative with f_equal.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm' o; specialize (Hm o);
      specialize (Hm' o); simpl in *; rewrite lookup_union_with in Hm'.
    destruct (m1 !! o) as [[]|] eqn:?, (m2 !! o) as [[]|],
      (m3 !! o) as [[]|]; simplify_equality';
      intuition eauto using ctree_disjoint_valid_l, ctree_disjoint_ll.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm' o; specialize (Hm o);
      specialize (Hm' o); simpl in *; rewrite lookup_union_with in Hm' |- *.
    destruct (m1 !! o) as [[]|] eqn:?, (m2 !! o) as [[]|],
      (m3 !! o) as [[]|]; simplify_equality';
      intuition eauto using ctree_disjoint_valid_l, ctree_disjoint_move_l,
      ctree_union_valid, ctree_positive_l, ctree_disjoint_lr.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm'; f_equal'.
    apply map_eq; intros o; specialize (Hm o); specialize (Hm' o); simpl in *;
      rewrite !lookup_union_with; rewrite lookup_union_with in Hm'.
    destruct (m1 !! o) as [[]|] eqn:?, (m2 !! o) as [[]|],
      (m3 !! o) as [[]|]; simplify_equality'; eauto;
      f_equal; intuition auto using ctree_associative with f_equal.
  * sep_unfold; intros [m1] [m2] _; rewrite !(inj_iff CMap); intros Hm.
    apply map_eq; intros o. rewrite lookup_empty.
    apply (f_equal (.!! o)) in Hm; rewrite lookup_union_with, lookup_empty in Hm.
    by destruct (m1 !! o), (m2 !! o); simplify_equality'.
  * sep_unfold; intros [m1] [m2] [m3] Hm Hm'; rewrite !(inj_iff CMap);
      intros Hm''; apply map_eq; intros o.
    specialize (Hm o); specialize (Hm' o);
      apply (f_equal (.!! o)) in Hm''; rewrite !lookup_union_with in Hm''.
    destruct (m1 !! o) as [[]|] eqn:?, (m2 !! o) as [[]|],
      (m3 !! o) as [[]|]; simplify_equality'; f_equal;
      try naive_solver eauto using ctree_cancel_l,
        ctree_cancel_empty_l, ctree_cancel_empty_r with f_equal.
  * sep_unfold; intros [m1] [m2] Hm o; specialize (Hm o).
    rewrite lookup_union_with.
    destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; simpl in *;
      intuition auto using ctree_union_subseteq_l, ctree_subseteq_reflexive.
  * sep_unfold; intros [m1] [m2] Hm o; specialize (Hm o).
    rewrite lookup_difference_with.
    destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|]; simplify_option_eq;
      intuition eauto using ctree_disjoint_difference, ctree_disjoint_valid_l.
  * sep_unfold; intros [m1] [m2] Hm; f_equal; apply map_eq; intros o;
      specialize (Hm o); rewrite lookup_union_with, lookup_difference_with.
    destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|];
      simplify_option_eq; f_equal; intuition eauto using
        ctree_union_difference, ctree_difference_empty_rev with f_equal.
  * sep_unfold; intros [m] Hm o w; specialize (Hm o).
    rewrite lookup_union_with; intros.
    destruct (m !! o) as [[]|]; simplify_equality'; intuition eauto using
      ctree_union_valid, ctree_splittable_union, ctree_positive_l.
  * sep_unfold; intros [m1] [m2] Hm Hm' o w1 ?; specialize (Hm o);
      specialize (Hm' o); unfold option_relation in *; simplify_option_eq.
    destruct w1, (m2 !! o) as [[]|]; try naive_solver
      eauto using ctree_disjoint_difference,
      ctree_disjoint_valid_l, seps_splittable_weaken, ctree_flatten_subseteq.
  * sep_unfold; intros [m] Hm o; specialize (Hm o); rewrite lookup_fmap.
    destruct (m !! o) as [[]|]; simpl; rewrite ?ctree_flatten_map;
      naive_solver eauto using seps_half_empty_rev, sep_disjoint_half',
      (ctree_disjoint_map sep_splittable), sep_unmapped_half_1.
  * sep_unfold; intros [m] Hm; f_equal; apply map_eq; intros o;
      specialize (Hm o); rewrite lookup_union_with, lookup_fmap.
    destruct (m !! o) as [[]|]; repeat f_equal'.
    by rewrite ctree_union_map, (ctree_map_id sep_splittable)
      by naive_solver eauto using sep_union_half.
  * sep_unfold; intros [m1] [m2] Hm Hm'; f_equal; apply map_eq; intros o;
      rewrite lookup_fmap, !lookup_union_with, !lookup_fmap;
      specialize (Hm o); specialize (Hm' o); rewrite lookup_union_with in Hm'.
    destruct (m1 !! o) as [[]|], (m2 !! o) as [[]|];
      simplify_equality'; repeat f_equal;
      naive_solver auto using ctree_union_half_distr.
  * sep_unfold; intros [m] ????; simplify_map_eq.
  * done.
  * sep_unfold; intros [m1] [m2] ? Hm; simplify_equality'. apply map_empty.
    intros o. specialize (Hm o); simplify_map_eq. by destruct (m1 !! o).
  * sep_unfold; intros [m1] [m2] ???; simpl in *; subst.
    by rewrite (left_id_L ∅ (union_with _)).
  * sep_unfold; intros [m]. split; [done|].
    intros [? Hm]. destruct (sep_inhabited A) as (x&?&?).
    generalize (String.EmptyString : tag); intros t.
    specialize (Hm (CMap {[fresh (dom indexset m) := Obj (MUnionAll t [x]) false]}));
      feed specialize Hm; [|simplify_map_eq].
    intros o. destruct (m !! o) eqn:Hw; simplify_map_eq.
    { rewrite lookup_singleton_ne; eauto. intros <-.
      eapply (is_fresh (dom indexset m)), fin_map_dom.elem_of_dom_2; eauto. }
    destruct ({[_ := _]} !! _) eqn:?; simplify_map_eq; split.
    + by constructor; rewrite Forall_singleton.
    + inversion_clear 1; decompose_Forall_hyps; eauto using sep_unmapped_empty.
  * done.
Qed.
