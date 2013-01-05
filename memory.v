(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines values, the memory and some operations on it. The
definitions of values and memory are still rather simple in this version of the
development: the memory is a finite map from naturals to values, and a value is
either a pointer to a memory cell, an unbounded integer, or the special void
value. *)

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
Instance indexmap_lookup {A} : Lookup index A (indexmap A) :=
  @lookup _ _ (Nmap A) _.
Instance indexmap_partial_alter {A} : PartialAlter index A (indexmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance indexmap_to_list {A} : FinMapToList index A (indexmap A) :=
  @finmap_to_list _ _ (Nmap A) _.
Instance indexmap_merge {A} : Merge A (indexmap A) := @merge _ (Nmap A) _.
Instance indexmap_fmap: FMap indexmap := λ A B f, @fmap Nmap _ _ f _.
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

Definition is_ptr (v : value) : option index :=
  match v with
  | ptr a => Some a
  | _ => None
  end%V.
Lemma is_ptr_Some v a : is_ptr v = Some a ↔ v = (ptr a)%V.
Proof.
  split.
  * by destruct v as [| | [?|]]; intro; simplify_equality.
  * intro. by simplify_equality.
Qed.

(** * Definition of the memory *)
Notation mem := (indexmap value).

Hint Resolve (lookup_singleton (M:=indexmap)) : mem.
Hint Resolve (lookup_insert (M:=indexmap)) : mem.
Hint Resolve finmap_disjoint_empty_l finmap_disjoint_empty_r : mem.
Hint Resolve finmap_disjoint_singleton_l_2 finmap_disjoint_singleton_r_2 : mem.
Hint Constructors list_disjoint : mem.
Hint Resolve finmap_union_Some_l finmap_union_Some_r : mem.
Hint Resolve finmap_subseteq_union_l finmap_subseteq_union_r : mem.
Hint Resolve finmap_disjoint_union_l_2 finmap_disjoint_union_r_2 : mem.
Hint Resolve finmap_disjoint_insert_l_2 finmap_disjoint_insert_r_2 : mem.
Hint Resolve finmap_disjoint_delete_l finmap_disjoint_delete_r : mem.
Hint Resolve finmap_disjoint_of_list_zip_l_2 finmap_disjoint_of_list_zip_r_2 : mem.
Hint Resolve finmap_disjoint_union_list_l_2 finmap_disjoint_union_list_r_2 : mem.
Hint Resolve finmap_disjoint_delete_list_l finmap_disjoint_delete_list_r : mem.
Hint Resolve finmap_list_disjoint_delete_vec : mem.
Hint Resolve finmap_list_disjoint_insert_vec : mem.
Hint Resolve finmap_disjoint_difference_l finmap_disjoint_difference_r : mem.
Hint Resolve Forall_vlookup_2 : mem.
Hint Resolve Forall_delete : mem.
Hint Extern 1 (_ ⊥ _) => done : mem.

Ltac solve_mem_disjoint :=
  solve [decompose_map_disjoint; auto with mem].

Tactic Notation "simplify_mem_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => progress (simplify_map_equality by tac)
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply finmap_union_cancel_r in H; [| solve[tac] | solve [tac]]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply finmap_union_cancel_l in H; [| solve[tac] | solve [tac]]
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

Lemma is_free_dom C `{Collection index C} m b :
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
     b ∉ bs → is_free m b → is_free_list m bs → is_free_list m (b :: bs).
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
  b ∉ fst <$> l → is_free m b → is_free (insert_list l m) b.
Proof.
  induction l; simpl; [done|].
  * rewrite elem_of_cons, is_free_insert. intuition.
Qed.
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
Proof.
  unfold fresh_index.
  apply (is_free_dom (listset _)). apply is_fresh.
Qed.
Hint Resolve is_free_fresh_index : mem.

Lemma fresh_indexes_length m n : length (fresh_indexes m n) = n.
Proof. apply fresh_list_length. Qed.
Lemma is_free_list_fresh_indexes n m : is_free_list m (fresh_indexes m n).
Proof.
  apply is_free_list_make.
  * apply fresh_list_nodup.
  * apply Forall_forall. intro.
    rewrite <-(is_free_dom (listset _)).
    apply fresh_list_is_fresh.
Qed.
Hint Resolve is_free_list_fresh_indexes : mem.

Lemma is_free_list_union m1 m2 bs :
  is_free_list (m1 ∪ m2) bs ↔ is_free_list m1 bs ∧ is_free_list m2 bs.
Proof.
  induction bs.
  * intuition constructor.
  * split.
    + inversion_clear 1. rewrite is_free_union in *.
      repeat constructor; intuition.
    + intros []. do 2 inversion_clear 1.
      constructor; rewrite ?is_free_union; intuition.
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

(** * Allocation of parameters *)
(** We define allocation of the parameters of a function inductively and prove
that it is equivalent to an alternative formulation that is used for the
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
Proof. induction 1; eauto using finmap_subseteq_insert with mem. Qed.
Lemma alloc_params_is_free m1 bs vs m2 b :
  alloc_params m1 bs vs m2 → is_free m2 b → is_free m1 b.
Proof. eauto using is_free_subseteq, alloc_params_subseteq. Qed.

Lemma alloc_params_free m1 bs vs m2 :
  alloc_params m1 bs vs m2 → is_free_list m1 bs.
Proof.
  induction 1; constructor; simpl; auto with mem.
  * rewrite elem_of_list_lookup. intros [i ?].
    feed inversion (same_length_lookup bs vs i) as [v'];
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
  rewrite !alloc_params_insert_list, !finmap_insert_list_union.
  intuition idtac.
  * apply finmap_union_cancel_l with m3.
    + done.
    + decompose_is_free.
      apply finmap_disjoint_union_l_2; [|done].
      apply finmap_disjoint_of_list_zip_l; auto with mem.
    + by rewrite <-(associative_eq (∪)).
  * by decompose_is_free.
Qed.
