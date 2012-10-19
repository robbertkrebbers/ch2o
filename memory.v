(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines values, the memory and some operations on it. The
definitions of values and memory are still rather simple in this version of the
development: the memory is a finite map from naturals to values, and a value is
either a pointer to a memory cell, an unbounded integer, or the special void
value. *)

(** Although the memory is just a finite map, we have defined many operations
directly on the memory instead of generalizing these to finite maps. In future
versions of the development, we will generalize some of this to finite maps,
and develop more specific operations here, as the memory is likely to become
more complex than just a finite map. *)

(** Furthermore, this file defines a hint database [mem] that contains useful
facts on the memory, and defines some tactics to simplify goals involving
propositions on the memory. *)
Require Export nmap.

(** * Values *)
(** We define indexes into the memory as binary naturals and use the [Nmap]
implementation to obtain efficient finite maps with these indexes as keys. *)
Definition index := N.
Definition indexmap := Nmap.

Instance index_dec: ∀ i1 i2 : index, Decision (i1 = i2) := decide_rel (=).
Instance index_fresh_`{FinCollection index C} : Fresh index C := _.
Instance index_fresh_spec `{FinCollection index C} : FreshSpec index C := _.

Instance indexmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : indexmap A, Decision (m1 = m2) := decide_rel (=).
Instance indexmap_empty {A} : Empty (indexmap A) := @empty (Nmap A) _.
Instance indexmap_lookup: Lookup index indexmap := @lookup _ Nmap _.
Instance indexmap_partial_alter: PartialAlter index indexmap :=
  @partial_alter _ Nmap _.
Instance indexmap_dom : Dom index indexmap := @dom _ Nmap _.
Instance indexmap_merge: Merge indexmap := @merge Nmap _.
Instance indexmap_fmap {A B} (f : A → B) : FMap indexmap f :=
  @fmap Nmap _ _ f _.
Instance: FinMap index indexmap := _.

Typeclasses Opaque index indexmap.

(** A value is inductively defined to be either a special void value (used for
functions without return value), an unbounded integer, or a pointer represented
by an index into the memory. This index is optional so as to model the NULL
pointer. *)
Inductive value :=
  | VVoid : value
  | VInt : Z → value
  | VPtr : option index → value.

Instance value_eq_dec (v1 v2 : value) : Decision (v1 = v2).
Proof. solve_decision. Defined.

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
  | int x => (x ≠ 0)%Z
  | ptr b => True
  | null => False
  end%V.
Definition value_false (v : value) : Prop :=
  match v with
  | void => True
  | int x => (x = 0)%Z
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

(** * Definition of the memory *)
(** The memory is defined as follows. *)
Notation mem := (indexmap value).

Hint Resolve (lookup_singleton (M:=indexmap)) : mem.
Hint Resolve (lookup_insert (M:=indexmap)) : mem.

(** * Disjoint memories *)
(** Since the memory is finite, we are able to obtain a witness if two memories
are not disjoint. *)
Lemma not_mem_disjoint (m1 m2 : mem) :
  ¬m1 ⊥ m2 ↔ ∃ b, is_Some (m1 !! b) ∧ is_Some (m2 !! b).
Proof.
  split.
  * intros H.
    destruct (choose (dom _ m1 ∩ dom _ m2 : listset index)) as [b Hb].
    + intros Hdom. destruct H. intros b.
      rewrite <-!(not_elem_of_dom _), <-not_elem_of_intersection.
      rewrite Hdom. by apply not_elem_of_empty.
    + exists b. rewrite <-!(elem_of_dom _).
      solve_elem_of.
  * intros [b [[??] [??]]] H.
    specialize (H b). intuition congruence.
Qed.

(** Some other properties on disjointness. *)
Instance: Symmetric (@disjoint mem _).
Proof. intros ?? H b. destruct (H b); intuition. Qed.
Lemma mem_disjoint_empty_l (m : mem) : ∅ ⊥ m.
Proof. intros ?. simplify_map. auto. Qed.
Lemma mem_disjoint_empty_r (m : mem) : m ⊥ ∅.
Proof. intros ?. simplify_map. auto. Qed.
Hint Resolve mem_disjoint_empty_l mem_disjoint_empty_r : mem.

Lemma mem_disjoint_weaken (m1 m1' m2 m2' : mem) :
  m1' ⊥ m2' →
  m1 ⊆ m1' → m2 ⊆ m2' →
  m1 ⊥ m2.
Proof.
  intros H ?? b.
  destruct (H b); [left | right]; eauto using lookup_weaken_None.
Qed.
Lemma mem_disjoint_weaken_l (m1 m1' m2  : mem) :
  m1' ⊥ m2 → m1 ⊆ m1' → m1 ⊥ m2.
Proof. eauto using mem_disjoint_weaken. Qed.
Lemma mem_disjoint_weaken_r (m1 m2 m2' : mem) :
  m1 ⊥ m2' → m2 ⊆ m2' → m1 ⊥ m2.
Proof. eauto using mem_disjoint_weaken. Qed.

Lemma mem_disjoint_Some_l (m1 m2 : mem) b x:
  m1 ⊥ m2 → m1 !! b = Some x → m2 !! b = None.
Proof. intros H ?. specialize (H b). intuition congruence. Qed.
Lemma mem_disjoint_Some_r (m1 m2 : mem) b x:
  m1 ⊥ m2 → m2 !! b = Some x → m1 !! b = None.
Proof. intros H ?. specialize (H b). intuition congruence. Qed.

Lemma mem_disjoint_singleton_l (m : mem) b v :
  {[(b, v)]} ⊥ m ↔ m !! b = None.
Proof.
  split.
  * intros H. by destruct (H b); simplify_map.
  * intros ? b'.
    destruct (decide (b = b')); simplify_map_equality; auto.
Qed.
Lemma mem_disjoint_singleton_r (m : mem) b v :
  m ⊥ {[(b, v)]} ↔ m !! b = None.
Proof. by rewrite (symmetry_iff (⊥)), mem_disjoint_singleton_l. Qed.

Lemma mem_disjoint_singleton_l_2 (m : mem) b v :
  m !! b = None → {[(b, v)]} ⊥ m.
Proof. by rewrite mem_disjoint_singleton_l. Qed.
Lemma mem_disjoint_singleton_r_2 (m : mem) b v :
  m !! b = None → m ⊥ {[(b, v)]}.
Proof. by rewrite mem_disjoint_singleton_r. Qed.
Hint Resolve mem_disjoint_singleton_l_2 mem_disjoint_singleton_r_2 : mem.

(** We lift the notion of disjointness to lists of memories. *)
Inductive mem_list_disjoint : list mem → Prop :=
  | mem_disjoint_nil :
     mem_list_disjoint []
  | mem_disjoint_cons m ms :
     Forall (⊥ m) ms →
     mem_list_disjoint ms →
     mem_list_disjoint (m :: ms).
Hint Constructors mem_list_disjoint : mem.

Lemma mem_disjoint_cons_inv m ms :
  mem_list_disjoint (m :: ms) →
  Forall (⊥ m) ms ∧ mem_list_disjoint ms.
Proof. by inversion_clear 1. Qed.

(** * The union operation *)
Lemma mem_union_Some (m1 m2 : mem) b x :
  m1 ⊥ m2 →
  (m1 ∪ m2) !! b = Some x ↔ m1 !! b = Some x ∨ m2 !! b = Some x.
Proof.
  intros H. specialize (H b).
  rewrite finmap_union_Some.
  destruct (m1 !! b), (m2 !! b); intuition congruence.
Qed.

Lemma mem_union_Some_l (m1 m2 : mem) b x :
  m1 ⊥ m2 → m1 !! b = Some x → (m1 ∪ m2) !! b = Some x.
Proof. intro. rewrite mem_union_Some; intuition congruence. Qed.
Lemma mem_union_Some_r (m1 m2 : mem) b x :
  m1 ⊥ m2 → m2 !! b = Some x → (m1 ∪ m2) !! b = Some x.
Proof. intro. rewrite mem_union_Some; intuition congruence. Qed.
Hint Resolve mem_union_Some_l mem_union_Some_r : mem.

Lemma mem_union_None (m1 m2 : mem) b :
  (m1 ∪ m2) !! b = None ↔ m1 !! b = None ∧ m2 !! b = None.
Proof. apply finmap_union_None. Qed.

Instance: LeftId (=) ∅ ((∪) : mem → mem → mem) := _.
Instance: RightId (=) ∅ ((∪) : mem → mem → mem) := _.
Instance: Associative (=) ((∪) : mem → mem → mem) := _.
Instance: Idempotent (=) ((∪) : mem → mem → mem) := _.

Lemma mem_union_comm (m1 m2 : mem) :
  m1 ⊥ m2 →
  m1 ∪ m2 = m2 ∪ m1.
Proof.
  intros H. apply (merge_comm (union_with (λ x _, x))).
  intros b. generalize (H b).
  destruct (m1 !! b), (m2 !! b); compute; intuition congruence.
Qed.

Lemma mem_subseteq_union (m1 m2 : mem) :
  m1 ⊆ m2 → m1 ∪ m2 = m2.
Proof.
  intros E. apply finmap_eq. intros b. apply option_eq. intros v.
  specialize (E b). rewrite finmap_union_Some.
  destruct (m1 !! b), (m2 !! b);
    try (einjection E; [| reflexivity ]); intuition (auto; congruence).
Qed.
Lemma mem_subseteq_union_l (m1 m2 : mem) :
  m1 ⊥ m2 → m1 ⊆ m1 ∪ m2.
Proof.
  intros ? b v. rewrite finmap_union_Some. intuition.
Qed.
Lemma mem_subseteq_union_r (m1 m2 : mem) :
  m1 ⊥ m2 → m2 ⊆ m1 ∪ m2.
Proof.
  intros. rewrite mem_union_comm by done.
  by apply mem_subseteq_union_l.
Qed.
Hint Resolve mem_subseteq_union_l mem_subseteq_union_r : mem.

Lemma mem_disjoint_union_l (m1 m2 m3 : mem) :
  m1 ∪ m2 ⊥ m3 ↔ m1 ⊥ m3 ∧ m2 ⊥ m3.
Proof.
  unfold disjoint, finmap_disjoint.
  setoid_rewrite finmap_union_None. firstorder auto.
Qed.
Lemma mem_disjoint_union_r (m1 m2 m3 : mem) :
  m1 ⊥ m2 ∪ m3 ↔ m1 ⊥ m2 ∧ m1 ⊥ m3.
Proof.
  unfold disjoint, finmap_disjoint.
  setoid_rewrite finmap_union_None. firstorder auto.
Qed.

Lemma mem_union_cancel_l (m1 m2 m3 : mem) :
  m1 ⊥ m3 →
  m2 ⊥ m3 →
  m1 ∪ m3 = m2 ∪ m3 →
  m1 = m2.
Proof.
  revert m1 m2 m3.
  cut (∀ (m1 m2 m3 : mem) b v,
    m1 ⊥ m3 →
    m2 ⊥ m3 →
    m1 ∪ m3 = m2 ∪ m3 →
    m1 !! b = Some v → m2 !! b = Some v).
  { intros. apply finmap_eq. intros i.
    apply option_eq. naive_solver. }
  intros m1 m2 m3 b v Hm1m3 Hm2m3 E ?.
  destruct (proj1 (mem_union_Some m2 m3 b v Hm2m3)) as [E2|E2].
  * rewrite <-E. by apply mem_union_Some_l.
  * done.
  * contradict E2. by apply eq_None_ne_Some, mem_disjoint_Some_l with m1 v.
Qed.
Lemma mem_union_cancel_r (m1 m2 m3 : mem) :
  m1 ⊥ m3 →
  m2 ⊥m3 →
  m3 ∪ m1 = m3 ∪ m2 →
  m1 = m2.
Proof.
  intros ??. rewrite !(mem_union_comm m3) by done.
  by apply mem_union_cancel_l.
Qed.

Lemma mem_disjoint_union_l_2 (m1 m2 m3 : mem) :
  m1 ⊥ m3 → m2 ⊥ m3 → m1 ∪ m2 ⊥ m3.
Proof. by rewrite mem_disjoint_union_l. Qed.
Lemma mem_disjoint_union_r_2 (m1 m2 m3 : mem) :
  m1 ⊥ m2 → m1 ⊥ m3 → m1 ⊥ m2 ∪ m3.
Proof. by rewrite mem_disjoint_union_r. Qed.
Hint Resolve mem_disjoint_union_l_2 mem_disjoint_union_r_2 : mem.

Lemma mem_union_singleton_l (m : mem) b v :
  <[b:=v]>m = {[(b,v)]} ∪ m.
Proof.
  apply finmap_eq. intros b'. apply option_eq. intros v'.
  rewrite finmap_union_Some.
  destruct (decide (b = b')); simplify_map_equality; intuition congruence.
Qed.
Lemma mem_union_singleton_r (m : mem) b v :
  m !! b = None →
  <[b:=v]>m = m ∪ {[(b,v)]}.
Proof.
  intro. rewrite mem_union_singleton_l, mem_union_comm; [done |].
  by apply mem_disjoint_singleton_l.
Qed.

Lemma mem_disjoint_insert_l (m1 m2 : mem) b v :
  <[b:=v]>m1 ⊥ m2 ↔ m2 !! b = None ∧ m1 ⊥ m2.
Proof.
  rewrite mem_union_singleton_l.
  by rewrite mem_disjoint_union_l, mem_disjoint_singleton_l.
Qed.
Lemma mem_disjoint_insert_r (m1 m2 : mem) b v :
  m1 ⊥ <[b:=v]>m2 ↔ m1 !! b = None ∧ m1 ⊥ m2.
Proof.
  rewrite mem_union_singleton_l.
  by rewrite mem_disjoint_union_r, mem_disjoint_singleton_r.
Qed.

Lemma mem_disjoint_insert_l_2 (m1 m2 : mem) b v :
  m2 !! b = None → m1 ⊥ m2 → <[b:=v]>m1 ⊥ m2.
Proof. by rewrite mem_disjoint_insert_l. Qed.
Lemma mem_disjoint_insert_r_2 (m1 m2 : mem) b v :
  m1 !! b = None → m1 ⊥ m2 → m1 ⊥ <[b:=v]>m2.
Proof. by rewrite mem_disjoint_insert_r. Qed.
Hint Resolve mem_disjoint_insert_l_2 mem_disjoint_insert_r_2 : mem.

Lemma mem_union_insert_l (m1 m2 : mem) b v :
  <[b:=v]>(m1 ∪ m2) = <[b:=v]>m1 ∪ m2.
Proof. by rewrite !mem_union_singleton_l, (associative (∪)). Qed.
Lemma mem_union_insert_r (m1 m2 : mem) b v :
  m1 !! b = None →
  <[b:=v]>(m1 ∪ m2) = m1 ∪ <[b:=v]>m2.
Proof.
  intro. rewrite !mem_union_singleton_l, !(associative (∪)).
  rewrite (mem_union_comm m1); [done |].
  by apply mem_disjoint_singleton_r.
Qed.

Lemma mem_insert_list_union l (m : mem) :
  insert_list l m = list_to_map l ∪ m.
Proof.
  induction l; simpl.
  * by rewrite (left_id _ _).
  * by rewrite IHl, mem_union_insert_l.
Qed.

Lemma mem_subseteq_insert (m1 m2 : mem) b v :
  m1 !! b = None → m1 ⊆ m2 → m1 ⊆ <[b:=v]>m2.
Proof.
  intros ?? b'. destruct (decide (b' = b)).
  * intros v' ?. congruence.
  * intros. simplify_map. auto.
Qed.

Lemma mem_disjoint_delete_l (m1 m2 : mem) b :
  m1 ⊥ m2 → delete b m1 ⊥ m2.
Proof.
  intros H b'. destruct (H b'); auto.
  rewrite lookup_delete_None. tauto.
Qed.
Lemma mem_disjoint_delete_r (m1 m2 : mem) b :
  m1 ⊥ m2 → m1 ⊥ delete b m2.
Proof. symmetry. by apply mem_disjoint_delete_l. Qed.
Hint Resolve mem_disjoint_delete_l mem_disjoint_delete_r : mem.

Lemma mem_disjoint_delete_list_l (m1 m2 : mem) bs :
  m1 ⊥ m2 → delete_list bs m1 ⊥ m2.
Proof. induction bs; simpl; auto with mem. Qed.
Lemma mem_disjoint_delete_list_r (m1 m2 : mem) bs :
  m1 ⊥ m2 → m1 ⊥ delete_list bs m2.
Proof. induction bs; simpl; auto with mem. Qed.
Hint Resolve mem_disjoint_delete_list_l mem_disjoint_delete_list_r : mem.

Lemma mem_union_delete (m1 m2 : mem) b :
  delete b (m1 ∪ m2) = delete b m1 ∪ delete b m2.
Proof.
  intros. apply finmap_eq. intros b'. apply option_eq. intros v'.
  destruct (decide (b = b')); simplify_map_equality;
   rewrite ?finmap_union_Some; simplify_map; intuition congruence.
Qed.
Lemma mem_union_delete_list (m1 m2 : mem) bs :
  delete_list bs (m1 ∪ m2) = delete_list bs m1 ∪ delete_list bs m2.
Proof. induction bs; simpl; [done |]. by rewrite IHbs, mem_union_delete. Qed.

Lemma mem_disjoint_list_to_map_l l (m : mem) :
  list_to_map l ⊥ m ↔ Forall (λ bv, m !! fst bv = None) l.
Proof.
  split.
  * induction l; simpl; rewrite ?mem_disjoint_insert_l in *;
      constructor; intuition auto.
  * induction 1; simpl.
    + apply mem_disjoint_empty_l.
    + rewrite mem_disjoint_insert_l. auto with mem.
Qed.
Lemma mem_disjoint_list_to_map_r (m : mem) l :
  m ⊥ list_to_map l ↔ Forall (λ bv, m !! fst bv = None) l.
Proof. by rewrite (symmetry_iff (⊥)), mem_disjoint_list_to_map_l. Qed.

Lemma mem_disjoint_list_to_map_zip_l (m : mem) bs vs :
  same_length bs vs →
  list_to_map (zip bs vs) ⊥ m ↔ Forall (λ b, m !! b = None) bs.
Proof.
  intro. rewrite mem_disjoint_list_to_map_l.
  rewrite <-(zip_fst bs vs) at 2 by done.
  by rewrite <-Forall_fmap.
Qed.
Lemma mem_disjoint_list_to_map_zip_r (m : mem) bs vs :
  same_length bs vs →
  m ⊥ list_to_map (zip bs vs) ↔ Forall (λ b, m !! b = None) bs.
Proof.
  intro. by rewrite (symmetry_iff (⊥)), mem_disjoint_list_to_map_zip_l.
Qed.
Lemma mem_disjoint_list_to_map_zip_l_2 (m : mem) bs vs :
  same_length bs vs →
  Forall (λ b, m !! b = None) bs →
  list_to_map (zip bs vs) ⊥ m.
Proof. intro. by rewrite mem_disjoint_list_to_map_zip_l. Qed.
Lemma mem_disjoint_list_to_map_zip_r_2 (m : mem) bs vs :
  same_length bs vs →
  Forall (λ b, m !! b = None) bs →
  m ⊥ list_to_map (zip bs vs).
Proof. intro. by rewrite mem_disjoint_list_to_map_zip_r. Qed.
Hint Resolve mem_disjoint_list_to_map_zip_l_2 mem_disjoint_list_to_map_zip_r_2 : mem.

Lemma mem_disjoint_union_list_l (m : mem) ms :
  ⋃ms ⊥ m ↔ Forall (⊥ m) ms.
Proof.
  split.
  * induction ms; simpl; rewrite ?mem_disjoint_union_l; intuition.
  * induction 1; simpl.
    + apply mem_disjoint_empty_l.
    + by rewrite mem_disjoint_union_l.
Qed.
Lemma mem_disjoint_union_list_r (m : mem) ms :
  m ⊥ ⋃ms ↔ Forall (⊥ m) ms.
Proof. by rewrite (symmetry_iff (⊥)), mem_disjoint_union_list_l. Qed.

Lemma mem_disjoint_union_list_l_2 (m : mem) ms :
  Forall (⊥ m) ms → ⋃ms ⊥ m.
Proof. by rewrite mem_disjoint_union_list_l. Qed.
Lemma mem_disjoint_union_list_r_2 (m : mem) ms :
  Forall (⊥ m) ms → m ⊥ ⋃ms.
Proof. by rewrite mem_disjoint_union_list_r. Qed.
Hint Resolve mem_disjoint_union_list_l_2 mem_disjoint_union_list_r_2 : mem.

(** The tactic [simplify_mem_disjoint] simplifies occurences of [mem_disjoint]
in the conclusion and hypotheses that involve the union, insert, or singleton
operation. *)
Ltac decompose_mem_disjoint := repeat
  match goal with
  | H : _ ∪ _ ⊥ _ |- _ =>
    apply mem_disjoint_union_l in H; destruct H
  | H : _ ⊥ _ ∪ _ |- _ =>
    apply mem_disjoint_union_r in H; destruct H
  | H : {[ _ ]} ⊥ _ |- _ => apply mem_disjoint_singleton_l in H
  | H : _ ⊥ {[ _ ]} |- _ =>  apply mem_disjoint_singleton_r in H
  | H : <[_:=_]>_ ⊥ _ |- _ =>
    apply mem_disjoint_insert_l in H; destruct H
  | H : _ ⊥ <[_:=_]>_ |- _ =>
    apply mem_disjoint_insert_r in H; destruct H
  | H : ⋃ _ ⊥ _ |- _ => apply mem_disjoint_union_list_l in H
  | H : _ ⊥ ⋃ _ |- _ => apply mem_disjoint_union_list_r in H
  | H : ∅ ⊥_ |- _ => clear H
  | H : _ ⊥ ∅ |- _ => clear H
  | H : mem_list_disjoint [] |- _ => clear H
  | H : mem_list_disjoint [_] |- _ => clear H
  | H : mem_list_disjoint (_ :: _) |- _ =>
    apply mem_disjoint_cons_inv in H; destruct H
  | H : Forall (⊥ _) _ |- _ => rewrite Forall_vlookup in H
  | H : Forall (⊥ _) [] |- _ => clear H
  | H : Forall (⊥ _) (_ :: _) |- _ =>
    apply Forall_cons_inv in H; destruct H
  end.
Hint Resolve Forall_vlookup_2 : mem.
Hint Resolve Forall_delete : mem.
Hint Extern 1 (_ ⊥ _) => done : mem.
Ltac solve_mem_disjoint :=
  solve [decompose_mem_disjoint; auto with mem].

Tactic Notation "simplify_mem_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => progress (simplify_map_equality by tac)
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply mem_union_cancel_r in H; [| solve[tac] | solve [tac]]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply mem_union_cancel_l in H; [| solve[tac] | solve [tac]]
  | H : context[ (?m1 ∪ ?m2) !! ?a ] |- _ =>
    let v := fresh in evar (v:value);
    let v' := eval unfold v in v in clear v;
    let Hv := fresh in
    assert ((m1 ∪ m2) !! a = Some v') as Hv
      by (clear H; by eauto with mem);
    rewrite Hv in H; clear Hv
  end.
Tactic Notation "simplify_mem_equality" :=
  simplify_mem_equality by solve_mem_disjoint.

Lemma mem_union_delete_vec {n} (ms : vec mem n) (i : fin n) :
  mem_list_disjoint ms →
  ms !!! i ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms) = ⋃ ms.
Proof.
  induction ms as [|m ? ms]; inversion_clear 1;
    inv_fin i; simpl; [done | intros i].
  rewrite (mem_union_comm m), (associative_eq _ _), IHms.
  * apply mem_union_comm. solve_mem_disjoint.
  * done.
  * by apply mem_disjoint_union_list_r, Forall_delete.
Qed.

Lemma mem_union_insert_vec {n} (ms : vec mem n) (i : fin n) m :
  m ⊥ ⋃ delete (fin_to_nat i) (vec_to_list ms) →
  ⋃ vinsert i m ms = m ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms).
Proof.
  induction ms as [|m' ? ms];
    inv_fin i; simpl; [done | intros i ?].
  rewrite IHms, !(associative_eq (∪)), (mem_union_comm m);
    solve_mem_disjoint.
Qed.

Lemma mem_list_disjoint_delete_vec {n} (ms : vec mem n) (i : fin n) :
  mem_list_disjoint ms →
  Forall (⊥ ms !!! i) (delete (fin_to_nat i) (vec_to_list ms)).
Proof.
  induction ms; inversion_clear 1; inv_fin i; simpl.
  * done.
  * constructor; solve_mem_disjoint.
Qed.
Hint Resolve mem_list_disjoint_delete_vec : mem.

Lemma mem_list_disjoint_insert_vec {n} (ms : vec mem n) (i : fin n) m :
  mem_list_disjoint ms →
  Forall (⊥ m) (delete (fin_to_nat i) (vec_to_list ms)) →
  mem_list_disjoint (vinsert i m ms).
Proof.
  induction ms as [|m' ? ms]; inversion_clear 1; inv_fin i; simpl.
  { constructor; solve_mem_disjoint. }
  intros i. inversion_clear 1. constructor.
  * apply Forall_vlookup_2. intros j.
    destruct (decide (i = j)); subst;
      by rewrite ?vlookup_insert, ?vlookup_insert_ne; solve_mem_disjoint.
  * apply IHms; solve_mem_disjoint.
Qed.
Hint Resolve mem_list_disjoint_insert_vec : mem.

(** * Free indexes in a memory *)
(** A memory index is free if it contains no contents. *)
Definition is_free (m : mem) (b : index) : Prop := m !! b = None.

Lemma is_free_lookup_None m b :
  is_free m b → m !! b = None.
Proof. done. Qed.
Hint Resolve is_free_lookup_None : mem.

Lemma is_free_Forall_lookup_None m bs :
  Forall (is_free m) bs → Forall (λ b, m !! b = None) bs.
Proof. done. Qed.
Hint Resolve is_free_Forall_lookup_None : mem.

Lemma is_free_lookup_Some m b v :
  is_free m b → ¬(m !! b = Some v).
Proof. unfold is_free. congruence. Qed.

Lemma is_free_dom `{Collection index C} m b :
  b ∉ dom C m ↔ is_free m b.
Proof. apply (not_elem_of_dom _). Qed.

Lemma is_free_subseteq (m1 m2 : mem) b :
  is_free m2 b → m1 ⊆ m2 → is_free m1 b.
Proof. apply lookup_weaken_None. Qed.
Hint Immediate is_free_subseteq : mem.

Lemma is_free_union m1 m2 b :
  is_free (m1 ∪ m2) b ↔ is_free m1 b ∧ is_free m2 b.
Proof. apply finmap_union_None. Qed.

Lemma is_free_union_2 m1 m2 b :
  is_free m1 b → is_free m2 b → is_free (m1 ∪ m2) b.
Proof. by rewrite is_free_union. Qed.
Hint Resolve is_free_union_2 : mem.

Lemma is_free_insert m b b' v :
  is_free (<[b':=v]>m) b ↔ is_free m b ∧ b' ≠ b.
Proof. apply lookup_insert_None. Qed.
Lemma is_free_insert_2 b b' v m :
  is_free m b → b' ≠ b → is_free (<[b':=v]>m) b.
Proof. rewrite is_free_insert. auto. Qed.
Hint Resolve is_free_insert_2 : mem.

(** We lift the notion of free indexes to lists of indexes. *)
Inductive is_free_list (m : mem) : list index → Prop :=
  | is_free_nil :
     is_free_list m []
  | is_free_cons b bs :
     ¬In b bs → is_free m b → is_free_list m bs → is_free_list m (b :: bs).
Hint Constructors is_free_list : mem.

(** We prove that the inductive definition [is_free_list m bs] is equivalent
to all [bs] being free, and the list [bs] containing no duplicates. *)
Lemma is_free_list_nodup m bs : is_free_list m bs → NoDup bs.
Proof. induction 1; by constructor. Qed.
Lemma is_free_list_free m bs : is_free_list m bs → Forall (is_free m) bs.
Proof. induction 1; firstorder. Qed.
Hint Resolve is_free_list_nodup is_free_list_free : mem.
Lemma is_free_list_make m bs :
  NoDup bs → Forall (is_free m) bs → is_free_list m bs.
Proof. induction 1; inversion 1; auto with mem. Qed.

Lemma is_free_list_subseteq m1 m2 bs :
  m1 ⊆ m2 → is_free_list m2 bs → is_free_list m1 bs.
Proof. induction 2; eauto with mem. Qed.

Lemma is_free_insert_list m b l :
  ¬In b (fst <$> l) → is_free m b → is_free (insert_list l m) b.
Proof. induction l; simpl; rewrite ?is_free_insert; intuition. Qed.
Hint Resolve is_free_insert_list : mem.

(** A memory cell is writable if it contains contents. In future versions this
notion will also take permissions into account. *)
Definition is_writable (m : mem) (b : index) : Prop := is_Some (m !! b).

(** The following definitions allow to generate fresh memory indexes, or lists
of fresh memory indexes. *)
Definition fresh_index (m : mem) : index := fresh (dom (listset index) m).
Definition fresh_indexes (m : mem) (n : nat) : list index :=
  fresh_list n (dom (listset index) m).

Lemma is_free_fresh_index m : is_free m (fresh_index m).
Proof. unfold fresh_index. apply is_free_dom, is_fresh. Qed.
Hint Resolve is_free_fresh_index : mem.

Lemma fresh_indexes_length m n : length (fresh_indexes m n) = n.
Proof. apply fresh_list_length. Qed.
Lemma is_free_list_fresh_indexes n m : is_free_list m (fresh_indexes m n).
Proof.
  apply is_free_list_make.
  * apply fresh_list_nodup.
  * apply Forall_forall. intro.
    rewrite <-is_free_dom. apply fresh_list_is_fresh.
Qed.
Hint Resolve is_free_list_fresh_indexes : mem.

Lemma is_free_list_union m1 m2 bs :
  is_free_list (m1 ∪ m2) bs ↔ is_free_list m1 bs ∧ is_free_list m2 bs.
Proof.
  induction bs.
  * intuition constructor.
  * split.
    + inversion_clear 1. rewrite is_free_union in *.
      repeat constructor; intuition auto.
    + intros []. do 2 inversion_clear 1.
      constructor; rewrite ?is_free_union; intuition auto.
Qed.
Lemma is_free_list_union_2 m1 m2 bs :
  is_free_list m1 bs ∧ is_free_list m2 bs → is_free_list (m1 ∪ m2) bs.
Proof. by rewrite is_free_list_union. Qed.
Hint Resolve is_free_list_union_2 : mem.

(** The tactic [simplify_is_free] simplifies assumptions of the shape
[is_free] involving the union or insert operation. *)
Ltac decompose_is_free := repeat
  match goal with
  | H : is_free (_ ∪ _) _ |- _ => apply is_free_union in H; destruct H
  | H : is_free (<[_:=_]>_) _ |- _ => apply is_free_insert in H; destruct H
  | H : is_free_list (_ ∪ _) _ |- _ => apply is_free_list_union in H; destruct H
  end.

(** * The difference operation *)
(** The difference operation removes all values from the first memory whose
index contains a value in the second memory as well. *)
Instance mem_difference: Difference mem := difference_with (λ _ _ , None).

Lemma mem_difference_Some (m1 m2 : mem) i x :
  (m1 ∖ m2) !! i = Some x ↔ m1 !! i = Some x ∧ m2 !! i = None.
Proof.
  unfold difference, mem_difference, difference_with, finmap_difference_with.
  rewrite (merge_spec _).
  destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
Qed.

Lemma mem_disjoint_difference_l m1 m2 m3 : m2 ⊆ m3 → m1 ∖ m3 ⊥ m2.
Proof.
  intros E b. specialize (E b).
  unfold difference, mem_difference, difference_with, finmap_difference_with.
  rewrite (merge_spec _).
  destruct (m1 !! b), (m2 !! b), (m3 !! b); compute; try intuition congruence.
  ediscriminate E; eauto.
Qed.
Lemma mem_disjoint_difference_r m1 m2 m3 : m2 ⊆ m3 → m2 ⊥ m1 ∖ m3.
Proof. intros. symmetry. by apply mem_disjoint_difference_l. Qed.
Hint Resolve mem_disjoint_difference_l mem_disjoint_difference_r : mem.

Lemma mem_union_difference m1 m2 : m1 ⊆ m2 → m2 = m1 ∪ m2 ∖ m1.
Proof.
  intro H. apply finmap_eq. intros b.
  apply option_eq. intros v. specialize (H b).
  unfold difference, mem_difference, difference_with, finmap_difference_with.
  rewrite finmap_union_Some, (merge_spec _).
  destruct (m1 !! b) as [v'|], (m2 !! b);
    try specialize (H v'); compute; intuition congruence.
Qed.

(** * Allocation of parameters *)
(** We define allocation of the parameters of a function inductively and prove
that it is equivalent to an alternative formulation that will be used for the
soundness proof of the axiomatic semantics. *)
Inductive alloc_params (m : mem) : list index → list value → mem → Prop :=
  | alloc_params_nil : alloc_params m [] [] m
  | alloc_params_cons b bs v vs m2 :
     is_free m2 b →
     alloc_params m bs vs m2 →
     alloc_params m (b :: bs) (v :: vs) (<[b:=v]>m2).

Lemma alloc_params_same_length m1 bs m2 vs :
  alloc_params m1 bs vs m2 → same_length bs vs.
Proof. induction 1; by constructor. Qed.

Lemma alloc_params_lookup m1 bs vs m2 b v i :
  alloc_params m1 bs vs m2 →
  bs !! i = Some b → vs !! i = Some v → m2 !! b = Some v.
Proof.
  intros Halloc. revert i.
  induction Halloc; intros [|i] ??; simpl; simplify_map_equality; trivial.
  feed pose proof (IHHalloc i); auto.
  rewrite lookup_insert_ne; auto.
  intro. subst. edestruct is_free_lookup_Some; eauto.
Qed.

Lemma alloc_params_subseteq m1 bs vs m2 :
  alloc_params m1 bs vs m2 → m1 ⊆ m2.
Proof. induction 1; eauto using mem_subseteq_insert with mem. Qed.
Lemma alloc_params_is_free m1 bs vs m2 b :
  alloc_params m1 bs vs m2 → is_free m2 b → is_free m1 b.
Proof. eauto using is_free_subseteq, alloc_params_subseteq. Qed.

Lemma alloc_params_free m1 bs vs m2 :
  alloc_params m1 bs vs m2 → is_free_list m1 bs.
Proof.
  induction 1; constructor; simpl; auto with mem.
  * rewrite list_lookup_In. intros [i ?].
    destruct (same_length_lookup bs vs i) as [v' ?];
     eauto using alloc_params_same_length.
    destruct (is_free_lookup_Some m2 b v');
      eauto using alloc_params_lookup.
  * eauto using alloc_params_is_free.
Qed.

Lemma alloc_params_insert_list_1 m1 bs vs m2 :
  alloc_params m1 bs vs m2 → m2 = insert_list (zip bs vs) m1.
Proof. induction 1; simpl; by f_equal. Qed.
Lemma alloc_params_insert_list_2 m bs vs :
  same_length bs vs →
  is_free_list m bs →
  alloc_params m bs vs (insert_list (zip bs vs) m).
Proof.
  induction 1; inversion_clear 1; simpl; constructor; auto.
  apply is_free_insert_list; auto.
  by rewrite zip_fst.
Qed.

Lemma alloc_params_insert_list m1 bs vs m2 :
  alloc_params m1 bs vs m2
   ↔ m2 = insert_list (zip bs vs) m1 ∧ is_free_list m1 bs ∧ same_length bs vs.
Proof.
  split.
  * intuition eauto using alloc_params_insert_list_1,
     alloc_params_free, alloc_params_same_length.
  * intros [?[??]]. subst. by apply alloc_params_insert_list_2.
Qed.

Lemma alloc_params_weaken m1 bs vs m2 m3 :
  m1 ⊥ m3 →
  m2 ⊥ m3 →
  alloc_params (m1 ∪ m3) bs vs (m2 ∪ m3) →
  alloc_params m1 bs vs m2.
Proof.
  rewrite !alloc_params_insert_list, !mem_insert_list_union.
  intuition idtac.
  * apply mem_union_cancel_l with m3.
    + done.
    + decompose_is_free.
      apply mem_disjoint_union_l_2; [|done].
      apply mem_disjoint_list_to_map_zip_l; auto with mem.
    + by rewrite <-(associative_eq (∪)).
  * by decompose_is_free.
Qed.
