(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines the memory as a finite map from natural numbers to pairs
of values and permissions. The main operations used in the operational semantics
are: look up, insert, alloc, and delete. The main operation for the axiomatic
semantics are: the disjoint union, which combines two memories by lifting the
union operation on permissions to whole memories, and the singleton memory
that consists of exactly one cell. *)

(** Furthermore, this file defines some tactics to simplify occurrences of
operations on the memory. *)
Require Import fin_maps mapset.
Require Export abstract_permissions abstract_values.

(** * Definition of the memory *)
(** We pack the memory into a record so as to avoid ambiguity with already
existing type class instances for finite maps. *)
Record mem_ (Vi P : Set) := Mem { MMap : indexmap (val_ Vi * P) }.
Arguments Mem {_ _} _.
Arguments MMap {_ _} _.

Section mem.
Context `{Permissions P} `{IntEnvSpec Ti Vi}.

Implicit Types b : index.
Implicit Types γ : P.
Implicit Types m : mem_ Vi P.
Implicit Types ms : list (mem_ Vi P).
Implicit Types v w : val_ Vi.

(** * Relations and operations *)
(** A memory [m2] extends [m1] in case [m2] contains more cells than [m1]. If
a cell already exists in [m1], it should have the same value and stronger or
equal permissions than the cell in [m2]. *)
Global Instance mem_subseteq: SubsetEq (mem_ Vi P) := λ m1 m2,
  ∀ b v1 γ1,
    MMap m1 !! b = Some (v1,γ1) → ∃ γ2, γ1 ⊆ γ2 ∧ MMap m2 !! b = Some (v1,γ2).

(** Two memories are disjoint if all overlapping cells have the same value and
disjoint permissions. *)
Definition mem_cell_disjoint (c1 c2 : val_ Vi * P) : Prop :=
  fst c1 = fst c2 ∧ snd c1 ⊥ snd c2.
Arguments mem_cell_disjoint !_ !_ /.
Global Instance mem_disjoint: Disjoint (mem_ Vi P) := λ m1 m2,
  map_intersection_forall mem_cell_disjoint (MMap m1) (MMap m2).

(** The initial memory state. *)
Global Instance mem_empty: Empty (mem_ Vi P) := Mem ∅.

(** The operation [m !! b] reads the value at index [b]. In case the index
[b] has not been allocated, it yields [None]. Also, if the permission at
index [b] does not permit reading, it yields [None]. *)
Global Instance mem_lookup: Lookup index (val_ Vi) (mem_ Vi P) := λ b m,
  c ← MMap m !! b;
  guard (perm_kind (snd c) ≠ Locked);
  Some (fst c).

(** The operation [mem_perm b m] gives the permission of the cell at index
[b]. In case [b] has not been allocated before, it yields [None]. Similarly,
the operation [mem_perm_kind b m] gives the kind of the permission of the cell
at index [b]. *)
Definition mem_perm (b : index) (m : mem_ Vi P) : option P :=
  snd <$> MMap m !! b.
Definition mem_perm_kind (b : index) (m : mem_ Vi P) : option pkind :=
  perm_kind <$> mem_perm b m.

(** The insert operation [<[b:=v]>m] updates a value [v] at index [b] leaving
the permissions of [b] unchanged. The insert operation ignores permissions of
[b], and thus performs an update even if the permissions do not permit to do so.
In case the of an attempt to update unallocated memory, it leaves the memory
unchanged. Hence, in the operational semantics, the insert operation is only
used if the predicate [is_writable m b] holds. *)
Definition is_writable (m : mem_ Vi P) (b : index) : Prop := ∃ γ,
  mem_perm b m = Some γ ∧ Write ⊆ perm_kind γ.
Global Instance mem_insert: Insert index (val_ Vi) (mem_ Vi P) := λ b v m,
  match m with Mem m => Mem $ alter (fst_map (λ _, v)) b m end.

(** The singleton memory [{[ (b,v,γ) ]}] consists of exactly one cell at index
[b] with value [v] and permission [γ]. *)
Global Instance mem_singleton:
    Singleton (index * val_ Vi * P) (mem_ Vi P) := λ bvγ,
  match bvγ with (b,v,γ) => Mem $ {[ (b, (v, γ)) ]} end.

(** The union operation combines two memories by lifting the union operation on
permissions to whole memories. Although the union is defined as a total
function, it only has a useful semantics if the given memories are disjoint.
In case of non disjoint memories it is left biased, i.e. it prefers the left
value over the right. This gives us associativity even in the case of non
disjoint memories, whereas commutativity only holds if the memories are
disjoint. *)
Global Instance mem_union: Union (mem_ Vi P) := λ m1 m2,
  match m1, m2 with
  | Mem m1,Mem m2 =>
     Mem $ union_with (λ c1 c2, Some (fst c1, snd c1 ∪ snd c2)) m1 m2
  end.

(** The difference operation is the opposite of the union operation, and
thus satisfies [m2 ∪ m1 ∖ m2 = m1]. Like the union, difference is a total
function and only has the desired semantics in case [m2 ⊆ m1]. *)
Global Instance mem_difference: Difference (mem_ Vi P) := λ m1 m2,
  match m1, m2 with
  | Mem m1, Mem m2 => Mem $ difference_with (λ c1 c2,
     guard (snd c2 ⊂ snd c1);
     Some (fst c1, snd c1 ∖ snd c2)) m1 m2
  end.

(** The operation [mem_alloc b v γ m] extends the memory [m] with a new cell
at index [b]. It initializes this cell with value [v] and sets its permission
to [γ]. In case [b] has already been allocated, its contents is overwritten.
Hence, in the operational semantics this operation is used for an arbitrary
free index [b] for which the predicate [is_free m b] holds. This operation is
used to allocate block scope and function variables as well as dynamically
allocated memory, but depending on its use, a different permission is used. We
model an infinite memory and allocation therefore never fails. *)
Definition is_free (m : mem_ Vi P) (b : index) : Prop := mem_perm b m = None.
Definition mem_alloc (b : index) (v : val_ Vi) (γ : P)
  (m : mem_ Vi P) : mem_ Vi P := Mem $ <[b:=(v,γ)]>(MMap m).

(** We lift [is_free] and [mem_alloc] to lists. *)
Inductive is_free_list (m : mem_ Vi P) : list index → Prop :=
  | is_free_nil : is_free_list m []
  | is_free_cons b bs :
     b ∉ bs → is_free m b → is_free_list m bs → is_free_list m (b :: bs).
Fixpoint mem_alloc_list (γ : P) (bvs : list (index * val_ Vi))
    (m : mem_ Vi P) : mem_ Vi P :=
  match bvs with
  | [] => m
  | (b,v) :: bvs => mem_alloc b v γ (mem_alloc_list γ bvs m)
  end.

(** The predicate [alloc_params γ m1 bs vs m2] states that [m2] is obtained
by allocating the values [vs] with permission [γ] at disjoint free indexes
[bs] in [m1]. *)
Inductive alloc_params (γ : P) (m : mem_ Vi P) :
      list index → list (val_ Vi) → mem_ Vi P → Prop :=
  | alloc_params_nil : alloc_params γ m [] [] m
  | alloc_params_cons b bs v vs m2 :
     is_free m2 b → alloc_params γ m bs vs m2 →
     alloc_params γ m (b :: bs) (v :: vs) (mem_alloc b v γ m2).

(** The operation [mem_delete b m] deallocates the index [b] in memory [m].
In case [b] has not been allocated, it leaves the memory unchanged. This
operation is used to deallocate automatically as well as dynamically allocated
memory. To free dynamically allocated memory, the operational semantics
requires the predicate [is_freeable m b] to holds. *)
Definition is_freeable (m : mem_ Vi P) (b : index) : Prop := ∃ γ,
  mem_perm b m = Some γ ∧ perm_kind γ = Free.
Global Instance mem_delete: Delete index (mem_ Vi P) := λ b m,
  match m with Mem m => Mem $ delete b m end.

(** The operation [dom m] gives a finite set of indexes that have been
allocated. *)
Global Instance mem_dom: Dom (mem_ Vi P) indexset := λ m,
  match m with Mem m => dom indexset m end.

(** The operation [mem_locks m] gives a finite set of indexes whose
permissions have kind [Locked]. *)
Global Instance mem_locks: Locks (mem_ Vi P) := λ m,
  match m with
  | Mem m => mapset_dom_with (λ vγ, bool_decide (perm_kind (snd vγ) = Locked)) m
  end.

(** The operation [mem_lock b m] changes the permission [γ] at index [b]
to [perm_lock γ] regardless of whether [γ] is already locked. This operation
is used to mark a location that has been written to during a sequence. *)
Definition mem_lock (b : index) (m : mem_ Vi P) : mem_ Vi P :=
  match m with Mem m => Mem $ alter (snd_map perm_lock) b m end.

(** The operation [mem_unlock Ω m] is used to change the each permission [γ]
at index [b ∈ Ω] to [perm_unlock γ]. This operation is used when a sequence
point occurs. *)
Definition mem_unlock (Ω : indexset) (m : mem_ Vi P) : mem_ Vi P :=
  match m with
  | Mem m => Mem $ mapset_map_with (bool_rect _ (snd_map perm_unlock) id) Ω m
  end.
Notation mem_unlock_all m := (mem_unlock (locks m) m).

(** * Properties *)
Global Instance mem_eq_dec (m1 m2 : mem_ Vi P) : Decision (m1 = m2).
Proof. solve_decision. Defined.
Global Instance: Injective (=) (=) (@MMap Vi P).
Proof. intros [?] [?] ?. simpl. by f_equal. Qed.

Lemma mem_lookup_Some_raw m b v :
  m !! b = Some v ↔ ∃ γ, MMap m !! b = Some (v,γ) ∧ perm_kind γ ≠ Locked.
Proof.
  unfold lookup at 1, mem_lookup. destruct (MMap m !! b) as [[??]|];
    simplify_option_equality; naive_solver.
Qed.
Lemma mem_lookup_None_raw m b :
  m !! b = None ↔
   MMap m !! b = None ∨ ∃ v γ, MMap m !! b = Some (v,γ) ∧ perm_kind γ = Locked.
Proof.
  unfold lookup at 1, mem_lookup. destruct (MMap m !! b) as [[??]|];
    simplify_option_equality; naive_solver.
Qed.
Lemma elem_of_mem_dom m b : b ∈ dom indexset m ↔ is_Some (mem_perm b m).
Proof.
  destruct m as [m]. unfold dom, mem_dom, is_free, mem_perm.
  simpl. by rewrite elem_of_dom, fmap_is_Some.
Qed.
Lemma not_elem_of_mem_dom m b : b ∉ dom indexset m ↔ is_free m b.
Proof. by rewrite elem_of_mem_dom, <-eq_None_not_Some. Qed.

(** ** Properties on the order *)
Global Instance: PartialOrder (@subseteq (mem_ Vi P) _).
Proof.
  repeat split.
  * intros m b v γ; simpl. by exists γ.
  * intros m1 m2 m3 Hm12 Hm23 b v1 γ1 ?.
    destruct (Hm12 b v1 γ1) as (γ2 & ? &?); [done |].
    destruct (Hm23 b v1 γ2) as (γ3 & ? &?); [done |].
    exists γ3. split; [|done]. by transitivity γ2.
  * intros m1 m2 Hm12 Hm21. f_equal. apply (injective MMap), map_eq.
    intros b. apply option_eq. intros [v γ]. split; intro.
    + destruct (Hm12 b v γ) as (γ' &?&?); [done |].
      destruct (Hm21 b v γ') as (γ'' &?&?); [done |].
      simplify_map_equality. do 2 f_equal. by apply (anti_symmetric (⊆)).
    + destruct (Hm21 b v γ) as (γ' &?&?); [done |].
      destruct (Hm12 b v γ') as (γ'' &?&?); [done |].
      simplify_map_equality. do 2 f_equal. by apply (anti_symmetric (⊆)).
Qed.
Lemma mem_lookup_weaken m1 m2 b v :
  m1 !! b = Some v → m1 ⊆ m2 → m2 !! b = Some v.
Proof.
  rewrite !mem_lookup_Some_raw. intros [γ1 [??]] Hm12.
  destruct (Hm12 b v γ1) as [γ2 [??]]; eauto.
  exists γ2. eauto using not_Locked_weaken, perm_kind_preserving.
Qed.
Lemma mem_lookup_weaken_is_Some m1 m2 b :
  is_Some (m1 !! b) → m1 ⊆ m2 → is_Some (m2 !! b).
Proof. inversion 1. eauto using mem_lookup_weaken. Qed.
Lemma mem_lookup_weaken_None m1 m2 b :
  m2 !! b = None → m1 ⊆ m2 → m1 !! b = None.
Proof. rewrite !eq_None_not_Some. eauto using mem_lookup_weaken_is_Some. Qed.
Lemma mem_lookup_weaken_inv m1 m2 b v w :
  m1 !! b = Some v → m1 ⊆ m2 → m2 !! b = Some w → v = w.
Proof. intros Hm1 ??. eapply mem_lookup_weaken in Hm1; eauto. congruence. Qed.
Lemma mem_lookup_empty b : @empty (mem_ Vi P) _ !! b = None.
Proof. unfold empty, lookup, mem_empty, mem_lookup. simpl. by simpl_map. Qed.
Lemma mem_subseteq_empty m : ∅ ⊆ m.
Proof. intros ???. by unfold empty; simpl; simpl_map. Qed.

Lemma mem_ind (Q : mem_ Vi P → Prop) :
  Q ∅ → (∀ b v p m, is_free m b → Q m → Q (mem_alloc b v p m)) → ∀ m, Q m.
Proof.
  intros Hemp Halloc [m]. induction m as [|b [v p] m] using map_ind.
  * apply Hemp.
  * by apply (Halloc _ _ _ (Mem m));
      unfold is_free, mem_perm; simplify_option_equality.
Qed.

(** ** Monoidal properties of the [union] operation *)
Global Instance: LeftId (@eq (mem_ Vi P)) ∅ (∪).
Proof.
  intros [m]. unfold empty, mem_empty, union, mem_union.
  f_equal. by rewrite (left_id_L ∅ (union_with _)).
Qed.
Global Instance: RightId (@eq (mem_ Vi P)) ∅ (∪).
Proof.
  intros [m]. unfold empty, mem_empty, union, mem_union.
  f_equal. by rewrite (right_id_L ∅ (union_with _)).
Qed.
Global Instance: Associative (@eq (mem_ Vi P)) (∪).
Proof.
  intros [m1] [m2] [m3]. unfold union, mem_union, union_with, map_union_with.
  f_equal. simpl. apply (merge_associative _). intros b.
  destruct (m1 !! b), (m2 !! b), (m3 !! b); try reflexivity.
  simpl. by rewrite (associative_L (∪)).
Qed.

(** ** Properties on disjoint memories and of the [union] operation *)
Global Instance: Symmetric mem_cell_disjoint.
Proof. intros [v1 γ1] [v2 γ2] [??]. by split. Qed.
Global Instance: Symmetric (@disjoint (mem_ Vi P) _).
Proof. intros ??. unfold disjoint, mem_disjoint. apply symmetry. Qed.

Lemma mem_disjoint_empty_l m : ∅ ⊥ m.
Proof. apply map_intersection_forall_empty_l. Qed.
Lemma mem_disjoint_empty_r m : m ⊥ ∅.
Proof. apply map_intersection_forall_empty_r. Qed.

Lemma mem_disjoint_list_singleton m : ⊥ [m].
Proof.
  rewrite !disjoint_list_cons, disjoint_list_nil. simpl.
  auto using mem_disjoint_empty_r.
Qed.
Lemma mem_disjoint_list_double m1 m2 : ⊥ [m1; m2] ↔ m1 ⊥ m2.
Proof.
  rewrite disjoint_list_cons. simpl. rewrite (right_id_L ∅ (∪)).
  intuition auto using mem_disjoint_list_singleton.
Qed.
Lemma mem_disjoint_list_double_1 m1 m2 : ⊥ [m1; m2] → m1 ⊥ m2.
Proof. by rewrite mem_disjoint_list_double. Qed.
Lemma mem_disjoint_list_double_2 m1 m2 : m1 ⊥ m2 → ⊥ [m1; m2].
Proof. by rewrite mem_disjoint_list_double. Qed.
Lemma mem_disjoint_list_symmetric m1 m2 : ⊥ [m1; m2] → ⊥ [m2; m1].
Proof. by rewrite !mem_disjoint_list_double. Qed.

Hint Extern 0 (_ ⊥ _) => symmetry; assumption.
Hint Extern 0 => eapply mem_disjoint_list_symmetric; eassumption.
Hint Resolve mem_disjoint_list_double_2.

Lemma mem_union_commutative_alt m1 m2 : m1 ⊥ m2 → m1 ∪ m2 = m2 ∪ m1.
Proof.
  destruct m1 as [m1],m2 as [m2]. intros Hm12. unfold union, mem_union.
  f_equal. apply union_with_commutative. intros b [v1 γ1] [v2 γ2] ??.
  destruct (Hm12 b (v1,γ1) (v2,γ2)); auto. simpl in *. subst.
  by rewrite (commutative_L (∪)).
Qed.
Lemma mem_union_commutative m1 m2 : ⊥[m1; m2] → m1 ∪ m2 = m2 ∪ m1.
Proof. rewrite mem_disjoint_list_double. apply mem_union_commutative_alt. Qed.

Lemma mem_disjoint_weaken_l m1 m1' m2 : m1' ⊥ m2 → m1 ⊆ m1' → m1 ⊥ m2.
Proof.
  intros Hm12 Hm12' b [v1 γ1] [v2 γ2] ??. red. simpl in *.
  destruct (Hm12' b v1 γ1) as (γ' &?&?); auto.
  destruct (Hm12 b (v1, γ') (v2, γ2)); auto. simpl in *.
  eauto using perm_disjoint_weaken_l.
Qed.
Lemma mem_disjoint_weaken_r m1 m2 m2' : m1 ⊥ m2' → m2 ⊆ m2' → m1 ⊥ m2.
Proof. rewrite !(symmetry_iff (⊥) m1). apply mem_disjoint_weaken_l. Qed.
Lemma mem_disjoint_weaken m1 m1' m2 m2' :
  m1' ⊥ m2' → m1 ⊆ m1' → m2 ⊆ m2' → m1 ⊥ m2.
Proof. eauto using mem_disjoint_weaken_l, mem_disjoint_weaken_r. Qed.
Global Instance: Proper ((⊆) ==> (⊆) ==> flip impl) (@disjoint (mem_ Vi P) _).
Proof. intros until 3. eauto using mem_disjoint_weaken. Qed.

Lemma mem_union_preserving_r m1 m2 m3 :
  ⊥[m2; m3] → m1 ⊆ m2 → m1 ∪ m3 ⊆ m2 ∪ m3.
Proof.
  rewrite mem_disjoint_list_double.
  destruct m1 as [m1],m2 as [m2], m3 as [m3]. intros Hm13d Hm12 b v γ Hm13.
  simpl in *. rewrite lookup_union_with_Some in Hm13.
  destruct Hm13 as [[??]| [[??]|([v1 γ1]&[v3 γ3]&?&?&?)]]; simpl in *.
  * destruct (Hm12 b v γ) as (γ2&?&?); auto.
    exists γ2. auto using lookup_union_with_Some_l.
  * destruct (m2 !! b) as [[v2 γ2]|] eqn:?.
    + destruct (Hm13d b (v2,γ2) (v,γ)); auto; simpl in *; subst.
      exists (γ2 ∪ γ). split; auto using perm_union_subseteq_r.
      eauto using lookup_union_with_Some_lr.
    + exists γ. eauto using lookup_union_with_Some_r.
  * simplify_equality. destruct (Hm12 b v γ1) as (γ2&?&?); auto.
    exists (γ2 ∪ γ3). split; auto using perm_union_preserving_r.
    eauto using lookup_union_with_Some_lr.
Qed.
Lemma mem_union_preserving_l m1 m2 m3 : ⊥[m3; m2] → m1 ⊆ m2 → m3 ∪ m1 ⊆ m3 ∪ m2.
Proof.
  rewrite mem_disjoint_list_double.
  intros Hm23 ?. rewrite !(mem_union_commutative m3);
    eauto using mem_union_preserving_r, mem_disjoint_weaken_r.
Qed.
Lemma mem_union_preserving m1 m2 m3 m4 :
  ⊥[m2; m4] → m1 ⊆ m2 → m3 ⊆ m4 → m1 ∪ m3 ⊆ m2 ∪ m4.
Proof.
  intros Hm24 Hm12 Hm34. transitivity (m1 ∪ m4).
  * apply mem_union_preserving_l; auto. apply mem_disjoint_list_double.
    eauto using mem_disjoint_weaken_l, mem_disjoint_list_double_1.
  * by apply mem_union_preserving_r.
Qed.

Lemma mem_union_subseteq_l m1 m2 : ⊥[m1; m2] → m1 ⊆ m1 ∪ m2.
Proof.
  intros. transitivity (m1 ∪ ∅); [by rewrite (right_id_L ∅ (∪))|].
  apply mem_union_preserving_l; auto using mem_subseteq_empty.
Qed.
Lemma mem_union_subseteq_r m1 m2 : ⊥[m1; m2] → m2 ⊆ m1 ∪ m2.
Proof.
  intros. rewrite (mem_union_commutative m1) by done.
  by apply mem_union_subseteq_l.
Qed.
Lemma mem_union_subseteq_l_alt m1 m2 m3 : ⊥[m2; m3] → m1 ⊆ m2 → m1 ⊆ m2 ∪ m3.
Proof.
  intros. transitivity (m1 ∪ ∅); [by rewrite (right_id_L ∅ (∪))|].
  apply mem_union_preserving; auto using mem_subseteq_empty.
Qed.
Lemma mem_union_subseteq_r_alt m1 m2 m3 : ⊥[m2; m3] → m1 ⊆ m3 → m1 ⊆ m2 ∪ m3.
Proof.
  intros. transitivity (∅ ∪ m1); [by rewrite (left_id_L ∅ (∪))|].
  apply mem_union_preserving; auto using mem_subseteq_empty.
Qed.

Lemma mem_disjoint_list_preserving ms1 ms2 : ⊥ ms2 → ms1 ⊆* ms2 → ⋃ ms1 ⊆ ⋃ ms2.
Proof.
  intros Hms2. induction 1; simpl; inversion_clear Hms2;
    auto using mem_union_preserving.
Qed.
Global Instance:
  Proper ((⊆*) ==> flip impl) (disjoint_list (A:=mem_ Vi P)).
Proof.
  unfold flip, impl. induction 1; simpl; [by constructor|].
  rewrite !disjoint_list_cons. intros [??].
  eauto using mem_disjoint_list_preserving, mem_disjoint_weaken.
Qed.

Lemma mem_disjoint_lookup m1 m2 b v1 v2 :
  ⊥ [m1; m2] → m1 !! b = Some v1 → m2 !! b = Some v2 → v1 = v2.
Proof.
  rewrite mem_disjoint_list_double, !mem_lookup_Some_raw.
  intros Hm12 (γ1&?&?) (γ2&?&?). by destruct (Hm12 b (v1,γ1) (v2,γ2)).
Qed.

Lemma mem_disjoint_union_ll m1 m2 m3 : m1 ∪ m2 ⊥ m3 → m1 ⊥ m3.
Proof.
  destruct m1 as [m1],m2 as [m2], m3 as [m3]. intros Hm123 b [v1 γ1] [v3 γ3] ??.
  simpl in *. destruct (m2 !! b) as [[v2 γ2]|] eqn:E.
  * destruct (Hm123 b (v1,γ1 ∪ γ2) (v3,γ3)); simpl in *; subst; auto.
    { eapply lookup_union_with_Some_lr; eauto. }
    eauto using perm_disjoint_union_ll.
  * destruct (Hm123 b (v1,γ1) (v3,γ3)); auto.
    simpl. eauto using lookup_union_with_Some_l.
Qed.
Lemma mem_disjoint_union_lr m1 m2 m3 : m1 ⊥ m2 → m1 ∪ m2 ⊥ m3 → m2 ⊥ m3.
Proof.
  intro. rewrite mem_union_commutative_alt by done.
  by apply mem_disjoint_union_ll.
Qed.
Lemma mem_disjoint_union_rl m1 m2 m3 : m1 ⊥ m2 ∪ m3 → m1 ⊥ m2.
Proof. rewrite !(symmetry_iff _ m1). apply mem_disjoint_union_ll. Qed.
Lemma mem_disjoint_union_rr m1 m2 m3 : m2 ⊥ m3 → m1 ⊥ m2 ∪ m3 → m1 ⊥ m3.
Proof.
  intro. rewrite mem_union_commutative_alt by done.
  by apply mem_disjoint_union_rl.
Qed.
Lemma mem_disjoint_union_move_l m1 m2 m3 :
  m1 ⊥ m2 → m1 ∪ m2 ⊥ m3 → m1 ⊥ m2 ∪ m3.
Proof.
  destruct m1 as [m1],m2 as [m2], m3 as [m3].
  intros Hm12 Hm123 b [v1 γ1] [v3 γ3] ? Hm23. simpl in *.
  apply lookup_union_with_Some in Hm23.
  destruct Hm23 as [[??]| [[??] | ( [v2 γ2] & [v3' γ3'] & ?&?&?)]].
  * destruct (Hm12 b (v1,γ1) (v3,γ3)); auto.
  * destruct (Hm123 b (v1,γ1) (v3,γ3)); auto.
    simpl. eauto using lookup_union_with_Some_l.
  * simplify_option_equality. destruct (Hm12 b (v1,γ1) (v3,γ2)); auto; subst.
    destruct (Hm123 b (v1,γ1 ∪ γ2) (v3', γ3')); simpl;
      eauto using lookup_union_with_Some_lr, perm_disjoint_union_move_l.
Qed.
Lemma mem_disjoint_union_move_r m1 m2 m3 :
  m2 ⊥ m3 → m1 ⊥ m2 ∪ m3 → m1 ∪ m2 ⊥ m3.
Proof.
  intros. symmetry.
  rewrite mem_union_commutative_alt; eauto using mem_disjoint_union_rl.
  apply mem_disjoint_union_move_l; [done |].
  by rewrite mem_union_commutative_alt.
Qed.

Lemma mem_union_list_preserving_aux ms1 ms2 :
  ⊥ ms2 → ms1 `contains` ms2 → ⊥ ms1 ∧ ⋃ ms1 ⊆ ⋃ ms2.
Proof.
  intros Hdisjoint Hms. revert Hdisjoint. elim Hms; clear ms1 ms2 Hms; simpl.
  * done.
  * intros m ms1 ms2 ? IH.
    rewrite !disjoint_list_cons, <-!mem_disjoint_list_double. intros (?&?).
    destruct IH as [? Hms12]; split_ands; auto using mem_union_preserving_l.
    by rewrite Hms12.
  * intros m1 m2 ms. rewrite !disjoint_list_cons. simpl. intros (?&?&?).
    split_ands.
    + apply mem_disjoint_union_move_l;
        eauto using mem_disjoint_union_rl, symmetry.
      rewrite mem_union_commutative_alt;
        eauto using mem_disjoint_union_move_r, mem_disjoint_union_rl, symmetry.
    + eauto using mem_disjoint_union_rr.
    + done.
    + by rewrite !(associative_L (∪)), (mem_union_commutative_alt m1)
        by eauto using mem_disjoint_union_rl.
  * intros m ms1 ms2 ? IH. rewrite !disjoint_list_cons. intros (?&?).
    destruct IH; split_ands; auto.
    transitivity (⋃ ms2); auto using mem_union_subseteq_r.
  * intros ms1 ms2 ms3 ? IH1 ? IH2 ?.
    destruct IH2; auto; destruct IH1; split_ands; auto. by transitivity (⋃ ms2).
Qed.
Lemma mem_disjoint_contains ms1 ms2 : ⊥ ms2 → ms1 `contains` ms2 → ⊥ ms1.
Proof. intros. edestruct mem_union_list_preserving_aux; eauto. Qed.
Lemma mem_union_list_preserving ms1 ms2 :
  ⊥ ms2 → ms1 `contains` ms2 → ⋃ ms1 ⊆ ⋃ ms2.
Proof. intros. edestruct mem_union_list_preserving_aux; eauto. Qed.
Global Instance: Proper (@Permutation (mem_ Vi P) ==> iff) disjoint_list.
Proof.
  intros ms1 ms2; split; intros.
  * apply mem_disjoint_contains with ms1; auto.
    apply Permutation_contains. by symmetry.
  * apply mem_disjoint_contains with ms2; auto using Permutation_contains.
Qed.

Lemma mem_disjoint_empty_alt ms : ⊥ (∅ :: ms) ↔ ⊥ ms.
Proof.
  rewrite disjoint_list_cons. intuition auto using mem_disjoint_empty_l.
Qed.
Lemma mem_disjoint_union_alt m1 m2 ms :
  ⊥ (m1 :: m2 :: ms) ↔ m1 ⊥ m2 ∧ ⊥ (m1 ∪ m2 :: ms).
Proof.
  rewrite !disjoint_list_cons. simpl. split; intros (?&?&?).
  * eauto using mem_disjoint_union_rl, mem_disjoint_union_move_r.
  * eauto using mem_disjoint_union_lr, mem_disjoint_union_move_l.
Qed.
Lemma mem_disjoint_union_list_alt ms1 ms2 :
  ⊥ (ms1 ++ ms2) ↔ ⊥ ms1 ∧ ⊥ (⋃ ms1 :: ms2).
Proof.
  revert ms2. induction ms1 as [|m1 ms1 IH]; simpl; intros ms2.
  { rewrite mem_disjoint_empty_alt, disjoint_list_nil. naive_solver. }
  rewrite Permutation_middle, IH, Permutation_swap, mem_disjoint_union_alt.
  rewrite (disjoint_list_cons m1). naive_solver.
Qed.

Lemma mem_union_reflecting_l m1 m2 m3 :
  ⊥[m3; m1] → ⊥[m3; m2] → m3 ∪ m1 ⊆ m3 ∪ m2 → m1 ⊆ m2.
Proof.
  rewrite !mem_disjoint_list_double. destruct m1 as [m1],m2 as [m2], m3 as [m3].
  intros Hm31 Hm32 Hm3132 b v1 γ1 ?. simpl in *.
  destruct (m3 !! b) as [[v3 γ3]|] eqn:?.
  { destruct (Hm31 b (v3,γ3) (v1,γ1)); auto; simpl in *; subst.
    destruct (Hm3132 b v1 (γ3 ∪ γ1)) as (γ' & ?& Hm).
    { simpl. eauto using lookup_union_with_Some_lr. }
    simpl in *. rewrite lookup_union_with_Some in Hm.
    destruct Hm as [[??] | [[??] | ([v3' γ3'] & [v2 γ2] & ?&?&?)]].
    * simplify_map_equality. by destruct (perm_union_subset_l γ3 γ1).
    * congruence.
    * destruct (Hm32 b (v1,γ3) (v2,γ2)); auto.
      simpl in *. simplify_map_equality.
      eauto using perm_union_reflecting_l with f_equal. }
  destruct (Hm3132 b v1 γ1) as (γ' &?& Hm).
  { simpl. eauto using lookup_union_with_Some_r. }
  simpl in *. rewrite lookup_union_with_Some in Hm.
  destruct Hm as [[??]|[[??]|([v3' γ3']&[v2 γ2]&?&?&?)]]; eauto with congruence.
Qed.
Lemma mem_union_reflecting_r m1 m2 m3 :
  ⊥[m1; m3] → ⊥[m2; m3] → m1 ∪ m3 ⊆ m2 ∪ m3 → m1 ⊆ m2.
Proof.
  intros ??. rewrite !(mem_union_commutative _ m3) by done.
  by apply mem_union_reflecting_l.
Qed.

Lemma mem_union_strict_preserving_l m1 m2 m3 :
  ⊥[m3; m1] → ⊥[m3; m2] → m1 ⊂ m2 → m3 ∪ m1 ⊂ m3 ∪ m2.
Proof.
  intros ?? [Hxy1 Hxy2]. split.
  * auto using mem_union_preserving_l.
  * contradict Hxy2. by apply mem_union_reflecting_l with m3.
Qed.
Lemma mem_union_strict_preserving_r m1 m2 m3 :
  ⊥[m1; m3] → ⊥[m2; m3] → m1 ⊂ m2 → m1 ∪ m3 ⊂ m2 ∪ m3.
Proof.
  intros ??. rewrite !(mem_union_commutative _ m3) by done.
  by apply mem_union_strict_preserving_l.
Qed.

Lemma mem_union_strict_reflecting_l m1 m2 m3 :
  ⊥[m3; m1] → ⊥[m3; m2] → m3 ∪ m1 ⊂ m3 ∪ m2 → m1 ⊂ m2.
Proof.
  intros ?? [? Hm]. split.
  * eauto using mem_union_reflecting_l.
  * contradict Hm. by apply mem_union_preserving_l.
Qed.
Lemma mem_union_strict_reflecting_r m1 m2 m3 :
  ⊥[m1; m3] → ⊥[m2; m3] → m1 ∪ m3 ⊂ m2 ∪ m3 → m1 ⊂ m2.
Proof.
  intros ??. rewrite !(mem_union_commutative _ m3) by done.
  by apply mem_union_strict_reflecting_l.
Qed.

Lemma mem_union_cancel_l m1 m2 m3 :
  ⊥[m3; m1] → ⊥[m3; m2] → m3 ∪ m1 = m3 ∪ m2 → m1 = m2.
Proof.
  intros ?? E. by apply (anti_symmetric _);
    apply mem_union_reflecting_l with m3; rewrite ?E.
Qed.
Lemma mem_union_cancel_r m1 m2 m3 :
  ⊥[m1; m3] → ⊥[m2; m3] → m1 ∪ m3 = m2 ∪ m3 → m1 = m2.
Proof.
  intros ?? E. by apply (anti_symmetric _);
    apply mem_union_reflecting_r with m3; rewrite ?E.
Qed.

Lemma mem_lookup_union_Some_l m1 m2 b v :
  ⊥[m1; m2] → m1 !! b = Some v → (m1 ∪ m2) !! b = Some v.
Proof. eauto using mem_lookup_weaken, mem_union_subseteq_l. Qed.
Lemma mem_lookup_union_Some_r m1 m2 b v :
  ⊥[m1; m2] → m2 !! b = Some v → (m1 ∪ m2) !! b = Some v.
Proof. eauto using mem_lookup_weaken, mem_union_subseteq_r. Qed.

Lemma mem_lookup_union_Some m1 m2 b v :
  ⊥[m1; m2] → (m1 ∪ m2) !! b = Some v ↔ m1 !! b = Some v ∨ m2 !! b = Some v.
Proof.
  intros Hm12. split.
  * rewrite mem_disjoint_list_double in Hm12.
    destruct m1 as [m1], m2 as [m2]. unfold union, mem_union.
    rewrite !mem_lookup_Some_raw. intros (γ&Hv&?). simpl in *.
    rewrite lookup_union_with_Some in Hv.
    destruct Hv as [[??]|[[??]|([v1 γ1]&[v2 γ2]&?&?&?)]];
      simpl in *; simplify_equality; eauto.
    left. exists γ1. split; [done |].
    intros Hγ1. destruct (perm_disjoint_locked_l γ1 γ2); eauto.
    by destruct (Hm12 b (v,γ1) (v2,γ2)).
  * intuition auto using mem_lookup_union_Some_l, mem_lookup_union_Some_r.
Qed.

(** ** Memories that behave equivalently with respect to disjointness *)
(** We define a relation [ms1 ≡⊥ ms2] that states that the lists of memories
[ms1] and [ms2] behave equivalently with respect to disjointness. For example,
we have [∅ :: ms ≡⊥ ms] and [m1 ∪ m2 :: ms ≡⊥ m1 :: m2 :: ms]. Since this
relation is an equivalence relation that is respected by the list operations,
it allows us to use Coq's setoid mechanism to conveniently reason about disjoint
memories. Likewise, we define an order [ms1 ⊆⊥ ms2]. *)
Definition mem_disjoint_le : relation (list (mem_ Vi P)) := λ ms1 ms2,
  ∀ m, ⊥ (m :: ms1) → ⊥ (m :: ms2).
Infix "⊆⊥" := mem_disjoint_le (at level 70) : C_scope.
Notation "(⊆⊥)" := mem_disjoint_le (only parsing) : C_scope.

Global Instance: PreOrder (⊆⊥).
Proof. unfold mem_disjoint_le. split; red; naive_solver. Qed.
Global Instance: Proper ((⊆⊥) ==> impl) disjoint_list.
Proof.
  intros ms1 ms2 Hms. red. rewrite <-(mem_disjoint_empty_alt ms1),
    <-(mem_disjoint_empty_alt ms2). by apply (Hms ∅).
Qed.
Global Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (⊆⊥).
Proof.
  unfold mem_disjoint_le, impl. intros ms1 ms2 Hms12 ms3 ms4 Hms34.
  by setoid_rewrite Hms12; setoid_rewrite Hms34.
Qed.
Global Instance: Proper ((=) ==> (⊆⊥) ==> (⊆⊥)) (::).
Proof.
  unfold mem_disjoint_le, impl. intros ? m ? ms1 ms2 Hms12 m'; subst.
  rewrite !mem_disjoint_union_alt. naive_solver.
Qed.
Global Instance: Proper ((⊆⊥) ==> (⊆⊥) ==> (⊆⊥)) (++).
Proof.
  unfold mem_disjoint_le. intros ms1 ms2 Hms12 ms3 ms4 Hms34 m'.
  apply impl_transitive with (⊥ (m' :: ms2 ++ ms3)).
  * rewrite !(commutative (++) _ ms3), !app_comm_cons.
    rewrite !mem_disjoint_union_list_alt. naive_solver.
  * rewrite !app_comm_cons, !mem_disjoint_union_list_alt. naive_solver.
Qed.
Lemma mem_disjoint_cons_le_inj m1 m2 ms : [m1] ⊆⊥ [m2] → m1 :: ms ⊆⊥ m2 :: ms.
Proof. intros. change ([m1] ++ ms ⊆⊥ [m2] ++ ms). by f_equiv. Qed.

Definition mem_disjoint_equiv : relation (list (mem_ Vi P)) := λ ms1 ms2,
  ms1 ⊆⊥ ms2 ∧ ms2 ⊆⊥ ms1.
Infix "≡⊥" := mem_disjoint_equiv (at level 70) : C_scope.
Notation "(≡⊥)" := mem_disjoint_equiv (only parsing) : C_scope.
Lemma mem_disjoint_equiv_alt ms1 ms2 :
  ms1 ≡⊥ ms2 ↔  ∀ m, ⊥ (m :: ms1) ↔ ⊥ (m :: ms2).
Proof. unfold mem_disjoint_equiv, mem_disjoint_le. naive_solver. Qed.
Global Instance: Equivalence (≡⊥).
Proof.
  split.
  * done.
  * by intros ?? [??].
  * by intros m1 m2 m3 [??] [??]; split; transitivity m2.
Qed.
Global Instance: AntiSymmetric (≡⊥) (⊆⊥).
Proof. by split. Qed.
Global Instance: Proper ((≡⊥) ==> iff) disjoint_list.
Proof. intros ?? [Hms1 Hms2]. split. by rewrite Hms1. by rewrite Hms2. Qed.
Global Instance: Proper ((≡⊥) ==> (≡⊥) ==> iff) (⊆⊥).
Proof.
  intros m1 m2 [??] m3 m4 [??]. split; intro.
  * transitivity m1; auto. transitivity m3; auto. 
  * transitivity m2; auto. transitivity m4; auto.
Qed.
Global Instance: Proper ((≡ₚ) ==> (≡ₚ) ==> iff) (≡⊥).
Proof.
  intros ms1 ms2 Hms12 ms3 ms4 Hms34. rewrite !mem_disjoint_equiv_alt.
  by setoid_rewrite Hms12; setoid_rewrite Hms34.
Qed.
Global Instance: Proper ((=) ==> (≡⊥) ==> (≡⊥)) (::).
Proof.
  intros ??? ?? [Hms1 Hms2]; subst. split. by rewrite Hms1. by rewrite Hms2.
Qed.
Global Instance: Proper ((≡⊥) ==> (≡⊥) ==> (≡⊥)) (++).
Proof.
  intros ?? [Hms1 Hms2] ?? [Hms3 Hms4].
  split. by rewrite Hms1, Hms3. by rewrite Hms2, Hms4.
Qed.

Lemma mem_disjoint_cons_inj m1 m2 ms : [m1] ≡⊥ [m2] → m1 :: ms ≡⊥ m2 :: ms.
Proof. intros. change ([m1] ++ ms ≡⊥ [m2] ++ ms). by f_equiv. Qed.
Lemma mem_disjoint_empty ms : ∅ :: ms ≡⊥ ms.
Proof.
  by split; intros m'; rewrite (Permutation_swap _ m'), mem_disjoint_empty_alt.
Qed.
Lemma mem_disjoint_union_le m1 m2 ms : m1 :: m2 :: ms ⊆⊥ m1 ∪ m2 :: ms.
Proof.
  intros m'. rewrite !(Permutation_swap _ m'),
    (mem_disjoint_union_alt m1 m2), <-mem_disjoint_list_double. by intros [??].
Qed.
Lemma mem_disjoint_union m1 m2 ms : ⊥[m1; m2] → m1 ∪ m2 :: ms ≡⊥ m1 :: m2 :: ms.
Proof.
  split; auto using mem_disjoint_union_le.
  intros m'. rewrite !(Permutation_swap _ m'),
    (mem_disjoint_union_alt m1 m2), <-mem_disjoint_list_double. tauto.
Qed.
Lemma mem_disjoint_union_list_le ms1 ms2 : ms1 ++ ms2 ⊆⊥ ⋃ ms1 :: ms2.
Proof.
  intros m'. rewrite !(Permutation_swap _ m'), Permutation_middle,
    mem_disjoint_union_list_alt. tauto.
Qed.
Lemma mem_disjoint_union_list ms1 ms2 : ⊥ ms1 → ⋃ ms1 :: ms2 ≡⊥ ms1 ++ ms2.
Proof.
  split; auto using mem_disjoint_union_list_le.
  intros m'. rewrite !(Permutation_swap _ m'), Permutation_middle,
    mem_disjoint_union_list_alt. tauto.
Qed.
  
(** ** Properties about permissions *)
Lemma mem_perm_Some m b γ :
  mem_perm b m = Some γ ↔ ∃ v, MMap m !! b = Some (v,γ).
Proof.
  unfold mem_perm. split.
  * intros. destruct (MMap m !! b) as [[v γ']|]; [|done].
    exists v. simpl in *. congruence.
  * intros [v Hv]. by rewrite Hv.
Qed.

Lemma mem_perm_kind_Some m b k :
  mem_perm_kind b m = Some k ↔ ∃ γ, mem_perm b m = Some γ ∧ perm_kind γ = k.
Proof.
  unfold mem_perm_kind. naive_solver (simplify_option_equality; eauto).
Qed.
Lemma mem_perm_kind_None m b : mem_perm_kind b m = None ↔ mem_perm b m = None.
Proof.
  unfold mem_perm_kind. naive_solver (simplify_option_equality; eauto).
Qed.

Lemma mem_perm_lookup m b :
  (∃ γ, mem_perm b m = Some γ ∧ perm_kind γ ≠ Locked) ↔ is_Some (m !! b).
Proof.
  unfold is_Some. setoid_rewrite mem_perm_Some.
  setoid_rewrite mem_lookup_Some_raw. naive_solver.
Qed.
Lemma mem_perm_lookup_None m b :
  mem_perm b m = None ∨ (∃ γ, mem_perm b m = Some γ ∧ perm_kind γ = Locked)
    ↔ m !! b = None.
Proof.
  unfold lookup, mem_lookup, mem_perm.
  destruct (MMap m !! b) as [[??]|]; simplify_option_equality; naive_solver.
Qed.

Lemma mem_perm_kind_lookup m b :
  (∃ k, mem_perm_kind b m = Some k ∧ k ≠ Locked) ↔ is_Some (m !! b).
Proof.
  rewrite <-mem_perm_lookup.
  setoid_rewrite mem_perm_kind_Some. naive_solver.
Qed.
Lemma mem_perm_kind_lookup_None m b :
  mem_perm_kind b m = None ∨ (∃ k, mem_perm_kind b m = Some k ∧ k = Locked)
    ↔ m !! b = None.
Proof.
  rewrite <-mem_perm_lookup_None, mem_perm_kind_None.
  setoid_rewrite mem_perm_kind_Some. naive_solver.
Qed.

Lemma mem_perm_weaken m1 m2 b γ :
  mem_perm b m1 = Some γ → m1 ⊆ m2 → ∃ γ', γ ⊆ γ' ∧ mem_perm b m2 = Some γ'.
Proof.
  setoid_rewrite mem_perm_Some. intros [v ?] Hm12.
  destruct (Hm12 b v γ) as [γ2 [??]]; eauto.
Qed.

Lemma mem_perm_kind_weaken m1 m2 b k :
  mem_perm_kind b m1 = Some k → m1 ⊆ m2 →
  ∃ k', k ⊆ k' ∧ mem_perm_kind b m2 = Some k'.
Proof.
  rewrite mem_perm_kind_Some. intros (γ &?&?) ?; subst.
  destruct (mem_perm_weaken m1 m2 b γ) as (γ' &?&?); trivial.
  exists (perm_kind γ'). rewrite mem_perm_kind_Some.
  eauto using perm_kind_preserving.
Qed.

Lemma mem_perm_weaken_is_Some m1 m2 b :
  is_Some (mem_perm b m1) → m1 ⊆ m2 → is_Some (mem_perm b m2).
Proof. inversion 1. intros. edestruct mem_perm_weaken as [?[??]]; eauto. Qed.
Lemma mem_perm_weaken_None m1 m2 b :
  mem_perm b m2 = None → m1 ⊆ m2 → mem_perm b m1 = None.
Proof. rewrite !eq_None_not_Some. eauto using mem_perm_weaken_is_Some. Qed.
Lemma mem_perm_kind_weaken_is_Some m1 m2 b :
  is_Some (mem_perm_kind b m1) → m1 ⊆ m2 → is_Some (mem_perm_kind b m2).
Proof.
  inversion 1. intros. edestruct mem_perm_kind_weaken as [?[??]]; eauto.
Qed.
Lemma mem_perm_kind_weaken_None m1 m2 b :
  mem_perm_kind b m2 = None → m1 ⊆ m2 → mem_perm_kind b m1 = None.
Proof. rewrite !eq_None_not_Some. eauto using mem_perm_kind_weaken_is_Some. Qed.

Lemma mem_perm_disjoint m1 m2 b γ1 γ2 :
  ⊥[m1; m2] → mem_perm b m1 = Some γ1 → mem_perm b m2 = Some γ2 → γ1 ⊥ γ2.
Proof.
  rewrite mem_disjoint_list_double, !mem_perm_Some. intros Hm [v1 ?] [v2 ?].
  by apply (Hm b (v1,γ1) (v2,γ2)).
Qed.
Lemma mem_perm_fragment_l m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m1 = Some γ → ¬perm_fragment γ → mem_perm b m2 = None.
Proof.
  intros ??. destruct (mem_perm b m2) as [γ2|] eqn:?; [|done].
  intros []. exists γ2. eauto using mem_perm_disjoint.
Qed.
Lemma mem_perm_fragment_r m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m2 = Some γ → ¬perm_fragment γ → mem_perm b m1 = None.
Proof. intro. by apply mem_perm_fragment_l. Qed.

Lemma mem_perm_kind_locked_l m1 m2 b :
  ⊥[m1; m2] → mem_perm_kind b m1 = Some Locked → mem_perm_kind b m2 = None.
Proof.
  rewrite mem_perm_kind_Some. unfold mem_perm_kind. intros ? (?&?&?).
  erewrite mem_perm_fragment_l; eauto using perm_fragment_locked.
Qed.
Lemma mem_perm_kind_locked_r m1 m2 b :
  ⊥[m1; m2] → mem_perm_kind b m2 = Some Locked → mem_perm_kind b m1 = None.
Proof. intro. by apply mem_perm_kind_locked_l. Qed.

Lemma mem_perm_empty b : mem_perm b ∅ = None.
Proof. unfold mem_perm. simpl. by simpl_map. Qed.
Lemma mem_perm_kind_empty b : mem_perm_kind b ∅ = None.
Proof. unfold mem_perm_kind. by rewrite mem_perm_empty. Qed.

Lemma mem_perm_union_Some_l m1 m2 b γ :
  mem_perm b m1 = Some γ → mem_perm b m2 = None → mem_perm b (m1 ∪ m2) = Some γ.
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold union, mem_union, mem_perm. intros.
  simplify_option_equality. by erewrite lookup_union_with_Some_l; eauto.
Qed.
Lemma mem_perm_union_Some_r m1 m2 b γ :
  mem_perm b m1 = None → mem_perm b m2 = Some γ → mem_perm b (m1 ∪ m2) = Some γ.
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold union, mem_union, mem_perm. intros.
  simplify_option_equality. by erewrite lookup_union_with_Some_r; eauto.
Qed.
Lemma mem_perm_union_Some_lr m1 m2 b γ1 γ2 :
  mem_perm b m1 = Some γ1 → mem_perm b m2 = Some γ2 →
  mem_perm b (m1 ∪ m2) = Some (γ1 ∪ γ2).
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold union, mem_union, mem_perm. intros.
  simplify_option_equality. by erewrite lookup_union_with_Some_lr; eauto.
Qed.

Lemma mem_perm_union_fragment_l m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m1 = Some γ → ¬perm_fragment γ →
  mem_perm b (m1 ∪ m2) = Some γ.
Proof. eauto using mem_perm_union_Some_l, mem_perm_fragment_l. Qed.
Lemma mem_perm_union_fragment_r m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m2 = Some γ → ¬perm_fragment γ →
  mem_perm b (m1 ∪ m2) = Some γ.
Proof. eauto using mem_perm_union_Some_r, mem_perm_fragment_r. Qed.

Lemma mem_perm_union_Some_raw m1 m2 b γ :
  mem_perm b (m1 ∪ m2) = Some γ ↔
    (∃ γ1 γ2, γ = γ1 ∪ γ2 ∧ mem_perm b m1 = Some γ1 ∧ mem_perm b m2 = Some γ2) ∨
    (mem_perm b m1 = Some γ ∧ mem_perm b m2 = None) ∨
    (mem_perm b m1 = None ∧ mem_perm b m2 = Some γ).
Proof.
  split.
  * destruct m1 as [m1], m2 as [m2]. unfold union at 1, mem_union, mem_perm.
    simpl. intros Hγ. destruct (union_with (λ c1 c2,
      Some (fst c1, snd c1 ∪ snd c2)) m1 m2 !! b)
      as [[v γ']|] eqn:Hγ'; simplify_equality.
    apply lookup_union_with_Some in Hγ'.
    destruct Hγ' as [[??] | [[??] | ([v1 γ1] & [v2 γ2] &?&?&?)]];
      simplify_option_equality; naive_solver.
  * naive_solver eauto using mem_perm_union_Some_l,
      mem_perm_union_Some_r, mem_perm_union_Some_lr.
Qed.
Lemma mem_perm_union_Some m1 m2 b γ :
  ⊥[m1; m2] →
  mem_perm b (m1 ∪ m2) = Some γ ↔
    (∃ γ1 γ2, γ1 ⊥ γ2 ∧ γ = γ1 ∪ γ2 ∧
      mem_perm b m1 = Some γ1 ∧ mem_perm b m2 = Some γ2) ∨
    (mem_perm b m1 = Some γ ∧ mem_perm b m2 = None) ∨
    (mem_perm b m1 = None ∧ mem_perm b m2 = Some γ).
Proof.
  intros. rewrite mem_perm_union_Some_raw.
  naive_solver eauto using mem_perm_disjoint.
Qed.
Lemma mem_perm_union_None m1 m2 b :
  mem_perm b (m1 ∪ m2) = None ↔ mem_perm b m1 = None ∧ mem_perm b m2 = None.
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold mem_perm, union, mem_union; simpl.
  rewrite !fmap_None, lookup_union_with_None. naive_solver.
Qed.
Lemma mem_perm_union_list_None ms b :
  mem_perm b (⋃ ms) = None ↔ Forall (λ m, mem_perm b m = None) ms.
Proof.
  induction ms; simpl.
  * by rewrite mem_perm_empty, Forall_nil.
  * rewrite mem_perm_union_None, Forall_cons. tauto.
Qed.
Lemma mem_perm_kind_union_Some_inv m1 m2 b k :
  ⊥[m1; m2] →
  mem_perm_kind b (m1 ∪ m2) = Some k →
    (k ≠ Locked
      ∧ mem_perm_kind b m1 = Some Read ∧ mem_perm_kind b m2 = Some Read) ∨
    (mem_perm_kind b m1 = Some k ∧ mem_perm_kind b m2 = None) ∨
    (mem_perm_kind b m1 = None ∧ mem_perm_kind b m2 = Some k).
Proof.
  intros Hm12. rewrite !mem_perm_kind_Some, !mem_perm_kind_None.
  intros (γ&Hmbγ&?); subst. rewrite mem_perm_union_Some in Hmbγ by done.
  destruct Hmbγ as [(γ1&γ2&?&?&?&?)|]; subst.
  * left. split_ands.
    + eauto using perm_kind_union_locked.
    + exists γ1. eauto using perm_disjoint_kind_l.
    + exists γ2. eauto using perm_disjoint_kind_r.
  * naive_solver.
Qed.
Lemma mem_perm_kind_union_Some_l m1 m2 b k :
  mem_perm_kind b m1 = Some k → mem_perm_kind b m2 = None →
  mem_perm_kind b (m1 ∪ m2) = Some k.
Proof.
  rewrite !mem_perm_kind_Some, !mem_perm_kind_None.
  naive_solver eauto using mem_perm_union_Some_l.
Qed.
Lemma mem_perm_kind_union_Some_r m1 m2 b k :
  mem_perm_kind b m1 = None → mem_perm_kind b m2 = Some k →
  mem_perm_kind b (m1 ∪ m2) = Some k.
Proof.
  rewrite !mem_perm_kind_Some, !mem_perm_kind_None.
  naive_solver eauto using mem_perm_union_Some_r.
Qed.

Lemma is_writable_union_l m1 m2 b :
  ⊥[m1; m2] → is_writable m1 b → is_writable (m1 ∪ m2) b.
Proof.
  intros Hm12 (γ1 & Hm1 & Hγ1). exists γ1. split; [|done].
  apply mem_perm_union_Some_l; [done |].
  destruct (mem_perm b m2) as [γ2|] eqn:?; [|done].
  rewrite (perm_disjoint_kind_l γ1 γ2) in Hγ1 by eauto using mem_perm_disjoint.
  inversion Hγ1.
Qed.
Lemma is_writable_union_r m1 m2 b :
  ⊥[m1; m2] → is_writable m2 b → is_writable (m1 ∪ m2) b.
Proof.
  intros. rewrite mem_union_commutative by done. by apply is_writable_union_l.
Qed.
Lemma is_freeable_union_l m1 m2 b :
  ⊥[m1; m2] → is_freeable m1 b → is_freeable (m1 ∪ m2) b.
Proof.
  intros Hm12 (γ1 & Hm1 & Hγ1). exists γ1. split; [|done].
  apply mem_perm_union_Some_l; [done |].
  destruct (mem_perm b m2) as [γ2|] eqn:?; [|done].
  by rewrite (perm_disjoint_kind_l γ1 γ2) in Hγ1; eauto using mem_perm_disjoint.
Qed.
Lemma is_freeable_union_r m1 m2 b :
  ⊥[m1; m2] → is_freeable m2 b → is_freeable (m1 ∪ m2) b.
Proof.
  intros. rewrite mem_union_commutative by done. by apply is_freeable_union_l.
Qed.

(** * Free indexes in a memory *)
Lemma is_free_lookup m b : is_free m b → m !! b = None.
Proof. unfold is_free. rewrite <-mem_perm_lookup_None. eauto. Qed.
Lemma is_free_subseteq m1 m2 b : is_free m2 b → m1 ⊆ m2 → is_free m1 b.
Proof. apply mem_perm_weaken_None. Qed.

Lemma is_free_fragment_l m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m1 = Some γ → ¬perm_fragment γ → is_free m2 b.
Proof. apply mem_perm_fragment_l. Qed.
Lemma is_free_fragment_r m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m2 = Some γ → ¬perm_fragment γ → is_free m1 b.
Proof. apply mem_perm_fragment_r. Qed.

Lemma is_free_union m1 m2 b : is_free (m1 ∪ m2) b ↔ is_free m1 b ∧ is_free m2 b.
Proof. apply mem_perm_union_None. Qed.
Lemma is_free_union_list ms b : is_free (⋃ ms) b ↔ Forall (flip is_free b) ms.
Proof. apply mem_perm_union_list_None. Qed.
Lemma is_free_union_2 m1 m2 b :
  is_free m1 b → is_free m2 b → is_free (m1 ∪ m2) b.
Proof. by rewrite is_free_union. Qed.

Lemma is_free_list_nodup m bs : is_free_list m bs → NoDup bs.
Proof. induction 1; by constructor. Qed.
Lemma is_free_list_free m bs : is_free_list m bs → Forall (is_free m) bs.
Proof. by induction 1; constructor. Qed.
Lemma is_free_list_alt m bs :
  is_free_list m bs ↔ NoDup bs ∧ Forall (is_free m) bs.
Proof.
  split.
  * eauto using is_free_list_nodup, is_free_list_free.
  * intros [Hbs Hmbs]. revert Hmbs.
    induction Hbs; inversion_clear 1; constructor; auto.
Qed.

Lemma is_free_list_subseteq m1 m2 bs :
  m1 ⊆ m2 → is_free_list m2 bs → is_free_list m1 bs.
Proof. induction 2; constructor; eauto using is_free_subseteq. Qed.

Lemma is_free_list_union m1 m2 bs :
  is_free_list (m1 ∪ m2) bs ↔ is_free_list m1 bs ∧ is_free_list m2 bs.
Proof.
  split.
  * intros Hbs; split; induction Hbs;
      rewrite ?is_free_union in *; constructor; intuition.
  * intros [Hbs1 Hbs2]. revert Hbs2. induction Hbs1; inversion_clear 1;
      constructor; rewrite ?is_free_union; intuition.
Qed.
Lemma is_free_list_union_2 m1 m2 bs :
  is_free_list m1 bs ∧ is_free_list m2 bs → is_free_list (m1 ∪ m2) bs.
Proof. by rewrite is_free_list_union. Qed.

Lemma is_free_list_fragment_l m1 m2 bs γ :
  ⊥[m1; m2] → NoDup bs → Forall (λ b, mem_perm b m1 = Some γ) bs →
  ¬perm_fragment γ → is_free_list m2 bs.
Proof.
  intros. apply is_free_list_alt; split; [done |].
  eapply Forall_impl; eauto. simpl; eauto using is_free_fragment_l.
Qed.
Lemma is_free_list_fragment_r m1 m2 bs γ :
  ⊥[m1; m2] → NoDup bs → Forall (λ b, mem_perm b m2 = Some γ) bs →
  ¬perm_fragment γ → is_free_list m1 bs.
Proof. intro. by apply is_free_list_fragment_l. Qed.

(** Properties of the [insert] operation *)
Lemma mem_perm_insert m b v b' : mem_perm b' (<[b:=v]>m) = mem_perm b' m.
Proof.
  destruct m as [m]. unfold mem_perm, insert, mem_insert. simpl.
  destruct (decide (b = b')); subst.
  * rewrite lookup_alter. by destruct (m !! b').
  * by rewrite lookup_alter_ne.
Qed.
Lemma mem_perm_kind_insert m b v b' :
  mem_perm_kind b' (<[b:=v]>m) = mem_perm_kind b' m.
Proof. unfold mem_perm_kind. by rewrite mem_perm_insert. Qed.

Lemma is_free_insert m b b' v : is_free (<[b':=v]>m) b ↔ is_free m b.
Proof. unfold is_free. by rewrite mem_perm_insert. Qed.
Lemma is_free_insert_2 b b' v m : is_free m b → is_free (<[b':=v]>m) b.
Proof. rewrite is_free_insert. auto. Qed.

Lemma mem_lookup_insert_None m i j v : <[i:=v]>m !! j = None ↔ m !! j = None.
Proof. by rewrite <-!mem_perm_lookup_None, mem_perm_insert. Qed.
Lemma mem_lookup_insert_None_1 m i j v : <[i:=v]>m !! j = None → m !! j = None.
Proof. by rewrite mem_lookup_insert_None. Qed.
Lemma mem_lookup_insert_None_2 m i j v : m !! j = None → <[i:=v]>m !! j = None.
Proof. by rewrite mem_lookup_insert_None. Qed.

Lemma mem_lookup_insert m b v : is_Some (m !! b) → <[b:=v]>m !! b = Some v.
Proof.
  destruct m as [m]. intros [w ?].
  unfold lookup, mem_lookup, insert, mem_insert in *. simpl in *.
  rewrite lookup_alter. by simplify_option_equality.
Qed.
Lemma mem_lookup_insert_ne m b b' v : b ≠ b' → <[b:=v]>m !! b' = m !! b'.
Proof.
  destruct m as [m]. intros. unfold lookup, mem_lookup, insert, mem_insert.
  simpl. by rewrite lookup_alter_ne.
Qed.
Lemma mem_lookup_insert_rev m b v w : <[b:=v]>m !! b = Some w → v = w.
Proof.
  intros Hb. destruct (m !! b) eqn:?.
  * rewrite mem_lookup_insert in Hb by eauto. congruence.
  * by rewrite mem_lookup_insert_None_2 in Hb.
Qed.
Lemma mem_insert_None m b v : mem_perm b m = None → <[b:=v]>m = m.
Proof.
  destruct m as [m]. unfold mem_perm, insert, mem_insert. simpl.
  rewrite fmap_None. intros. by rewrite alter_None.
Qed.

Lemma mem_disjoint_insert m ms b v γ :
  mem_perm b m = Some γ → ¬perm_fragment γ → <[b:=v]>m :: ms ≡⊥ m :: ms.
Proof.
  cut (∀ m1 m2, ⊥[m1; m2] → ⊥[<[b:=v]>m1; <[b:=v]>m2]).
  { intros help ? Hbγ. apply mem_disjoint_cons_inj. split; intros m'.
  * rewrite !mem_disjoint_list_double. destruct m' as [m1], m as [m2].
    intros Hm12 b' [v1 γ1] [v2 γ2] Hm1 Hm2. unfold mem_perm in *. simpl in *.
    destruct (decide (b = b')); subst.
    + destruct Hbγ. exists γ1. by destruct (Hm12 b' (v1,γ1) (v,γ2));
        simpl; rewrite ?lookup_alter; simplify_option_equality.
    + destruct (Hm12 b' (v1,γ1) (v2,γ2)); simpl in *; subst; auto.
      by rewrite lookup_alter_ne.
  * intros. rewrite <-(mem_insert_None m' b v);
      eauto using mem_perm_fragment_r. }
  intros [m1] [m2]. rewrite !mem_disjoint_list_double.
  intros Hm12 b' [v1 γ1] [v2 γ2] Hm1 Hm2. simpl in *.
  destruct (decide (b = b')); subst.
  * rewrite lookup_alter in Hm1, Hm2. destruct (m1 !! b') as [[v1' γ1']|] eqn:?,
      (m2 !! b') as [[v2' γ2']|] eqn:?; simplify_equality.
    by destruct (Hm12 b' (v1',γ1) (v2',γ2)).
  * rewrite lookup_alter_ne in Hm1, Hm2 by done.
    by destruct (Hm12 b' (v1,γ1) (v2,γ2)).
Qed.

Lemma mem_insert_union m1 m2 b v : <[b:=v]>(m1 ∪ m2) = <[b:=v]>m1 ∪ <[b:=v]>m2.
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold insert, mem_insert, union, mem_union.
  f_equal. by apply alter_union_with.
Qed.
Lemma mem_insert_union_l m1 m2 b v :
  mem_perm b m2 = None → <[b:=v]>(m1 ∪ m2) = <[b:=v]>m1 ∪ m2.
Proof. intros. by rewrite mem_insert_union, (mem_insert_None m2). Qed.
Lemma mem_insert_union_r m1 m2 b v :
  mem_perm b m1 = None → <[b:=v]>(m1 ∪ m2) = m1 ∪ <[b:=v]>m2.
Proof. intros. by rewrite mem_insert_union, (mem_insert_None m1). Qed.
Lemma mem_insert_union_fragment_l m1 m2 b v γ :
  ⊥[m1; m2] → mem_perm b m1 = Some γ → ¬perm_fragment γ →
  <[b:=v]>(m1 ∪ m2) = <[b:=v]>m1 ∪ m2.
Proof. eauto using mem_insert_union_l, mem_perm_fragment_l. Qed.
Lemma mem_insert_union_fragment_r m1 m2 b v γ :
  ⊥[m1; m2] → mem_perm b m2 = Some γ → ¬perm_fragment γ →
  <[b:=v]>(m1 ∪ m2) = m1 ∪ <[b:=v]>m2.
Proof. eauto using mem_insert_union_r, mem_perm_fragment_r. Qed.

(** ** Properties of the [singleton] operation *)
Lemma mem_lookup_singleton_raw b v γ : MMap {[b,v,γ]} !! b = Some (v,γ).
Proof. unfold singleton, mem_singleton. simpl. by simpl_map. Qed.
Lemma mem_lookup_singleton_raw_ne b b' v γ :
  b ≠ b' → MMap {[b,v,γ]} !! b' = None.
Proof. intros. unfold singleton, mem_singleton. simpl. by simpl_map. Qed.

Lemma mem_perm_singleton b v γ : mem_perm b {[b,v,γ]} = Some γ.
Proof. unfold mem_perm. by rewrite mem_lookup_singleton_raw. Qed.
Lemma mem_perm_kind_singleton b v γ :
  mem_perm_kind b {[b,v,γ]} = Some (perm_kind γ).
Proof. unfold mem_perm_kind. by rewrite mem_perm_singleton. Qed.
Lemma mem_perm_singleton_ne b b' v γ : b ≠ b' → mem_perm b' {[b,v,γ]} = None.
Proof. intros. unfold mem_perm. by rewrite mem_lookup_singleton_raw_ne. Qed.
Lemma mem_perm_kind_singleton_ne b b' v γ :
  b ≠ b' → mem_perm_kind b' {[b,v,γ]} = None.
Proof. intros. unfold mem_perm_kind. by rewrite mem_perm_singleton_ne. Qed.

Lemma mem_lookup_singleton b v γ :
  perm_kind γ ≠ Locked → {[b,v,γ]} !! b = Some v.
Proof.
  intros. unfold lookup, mem_lookup. rewrite mem_lookup_singleton_raw.
  by simplify_option_equality.
Qed.
Lemma mem_lookup_singleton_ne b b' v γ : b ≠ b' → {[b,v,γ]} !! b' = None.
Proof.
  intros. unfold lookup, mem_lookup. by rewrite mem_lookup_singleton_raw_ne.
Qed.
Lemma mem_lookup_singleton_locked b b' v γ :
  perm_kind γ = Locked → {[b,v,γ]} !! b = None.
Proof.
  intros. unfold lookup, mem_lookup. rewrite mem_lookup_singleton_raw.
  by simplify_option_equality.
Qed.

Lemma mem_lookup_singleton_Some b b' v w γ :
  {[b,v,γ]} !! b' = Some w ↔ b = b' ∧ v = w ∧ perm_kind γ ≠ Locked.
Proof.
  unfold lookup, mem_lookup. destruct (decide (b = b')); subst.
  * rewrite mem_lookup_singleton_raw. simplify_option_equality; naive_solver.
  * rewrite mem_lookup_singleton_raw_ne; naive_solver.
Qed.
Lemma mem_lookup_singleton_None b b' v γ :
  {[b,v,γ]} !! b' = None ↔ b ≠ b' ∨ perm_kind γ = Locked.
Proof.
  unfold lookup, mem_lookup. destruct (decide (b = b')); subst.
  * rewrite mem_lookup_singleton_raw.
    simplify_option_equality; naive_solver.
  * rewrite mem_lookup_singleton_raw_ne; naive_solver.
Qed.
Lemma mem_insert_singleton b v w γ : <[b:=v]>{[b,w,γ]} = {[b,v,γ]}.
Proof.
  unfold insert, mem_insert, singleton, mem_singleton.
  by rewrite alter_singleton.
Qed.
Lemma mem_insert_singleton_ne b b' v w γ :
  b ≠ b' → <[b:=v]>{[b',w,γ]} = {[b',w,γ]}.
Proof.
  intros. unfold insert, mem_insert, singleton, mem_singleton.
  by rewrite alter_singleton_ne.
Qed.
Lemma mem_disjoint_insert_singleton ms b γ v1 v2 :
  ¬perm_fragment γ → {[b,v1,γ]} :: ms ≡⊥ {[b,v2,γ]} :: ms.
Proof.
  intros. rewrite <-(mem_insert_singleton _ v1 v2).
  by rewrite mem_disjoint_insert with γ; rewrite ?mem_perm_singleton.
Qed.

Lemma mem_disjoint_singleton ms b γ v :
  Forall (flip is_free b) ms → ⊥ ms → ⊥ ({[b,v,γ]} :: ms).
Proof.
  cut (∀ m, is_free m b → {[b,v,γ]} ⊥ m).
  { intros help ?. rewrite disjoint_list_cons. split; auto.
    by apply help, is_free_union_list. }
  intros m ? b' [v1 γ1] [v2 γ2].
  unfold singleton, mem_singleton. simpl. rewrite lookup_singleton_Some.
  unfold is_free, mem_perm in *. intros [??] ?; simplify_option_equality.
Qed.
Lemma mem_disjoint_singleton_inv ms b γ v :
  ⊥ ({[b,v,γ]} :: ms) → ¬perm_fragment γ → Forall (flip is_free b) ms.
Proof.
  rewrite disjoint_list_cons. intros [??] ?.
  eapply is_free_union_list, is_free_fragment_l; eauto.
  by rewrite mem_perm_singleton.
Qed.
Lemma mem_disjoint_singleton_l m b γ v : is_free m b → ⊥[{[b,v,γ]}; m].
Proof.
  intros. apply mem_disjoint_singleton.
  * by repeat constructor.
  * by apply mem_disjoint_list_singleton.
Qed.
Lemma mem_disjoint_singleton_r m b γ v : is_free m b → ⊥[m; {[b,v,γ]}].
Proof. intros. rewrite Permutation_swap. by apply mem_disjoint_singleton_l. Qed.
Lemma mem_disjoint_singleton_l_inv m b γ v :
  ⊥[{[b,v,γ]}; m] → ¬perm_fragment γ → is_free m b.
Proof.
  intros Hm ?. apply mem_disjoint_singleton_inv in Hm; auto.
  by decompose_Forall.
Qed.
Lemma mem_disjoint_singleton_r_inv m b γ v :
  ⊥[m; {[b,v,γ]}] → ¬perm_fragment γ → is_free m b.
Proof. rewrite Permutation_swap. apply mem_disjoint_singleton_l_inv. Qed.

Lemma is_freeable_singleton b v γ :
  perm_kind γ = Free → is_freeable {[b,v,γ]} b.
Proof. intros. exists γ. by rewrite mem_perm_singleton. Qed.
Lemma is_writable_singleton b v γ :
  Write ⊆ perm_kind γ → is_writable {[b,v,γ]} b.
Proof. intros. exists γ. by rewrite mem_perm_singleton. Qed.

Lemma mem_disjoint_double_same b v γ1 γ2 : γ1 ⊥ γ2 → ⊥[{[b,v,γ1]}; {[b,v,γ2]}].
Proof.
  rewrite mem_disjoint_list_double. repeat intro.
  simpl in *. by simplify_map_equality.
Qed.
Lemma mem_disjoint_double_other b1 b2 v1 v2 γ1 γ2 :
  b1 ≠ b2 → ⊥[{[b1,v1,γ1]}; {[b2,v2,γ2]}].
Proof.
  rewrite mem_disjoint_list_double. repeat intro.
  simpl in *. by simplify_map_equality.
Qed.
Lemma mem_disjoint_double b1 v1 γ1 b2 v2 γ2 :
  ⊥[{[b1,v1,γ1]}; {[b2,v2,γ2]}] ↔ b1 ≠ b2 ∨ (b1 = b2 ∧ v1 = v2 ∧ γ1 ⊥ γ2).
Proof.
  split.
  * rewrite mem_disjoint_list_double.
    destruct (decide (b1 = b2)); subst; auto. intros Hdisjoint. right.
    by destruct (Hdisjoint b2 (v1,γ1) (v2,γ2)); simpl; simpl_map.
  * naive_solver eauto using mem_disjoint_double_same,
      mem_disjoint_double_other.
Qed.
Lemma mem_subseteq_double_same b v γ1 γ2 : γ1 ⊆ γ2 → {[b,v,γ1]} ⊆ {[b,v,γ2]}.
Proof. repeat intro. simpl in *. simplify_map_equality. eauto. Qed.
Lemma mem_union_double b v γ1 γ2 : {[(b,v,γ1); (b,v,γ2)]} = {[b,v,γ1 ∪ γ2]}.
Proof.
  unfold union at 1, singleton, mem_union, mem_singleton. simpl. f_equal.
  apply map_eq. intros b'. destruct (decide (b = b')); subst.
  * simpl_map. apply lookup_union_with_Some. simpl_map. naive_solver.
  * simpl_map. apply lookup_union_with_None. simpl_map. eauto.
Qed.

(** ** Properties with respect to vectors *)
Lemma mem_union_delete_vec {n} (ms : vec (mem_ Vi P) n) (i : fin n) :
  ⊥ ms → ms !!! i ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms) = ⋃ ms.
Proof.
  induction ms as [|m ? ms]; inversion_clear 1; inv_fin i; simpl; [done|].
  intros i. rewrite (mem_union_commutative m), (associative_L (∪)), IHms.
  * apply mem_union_commutative; auto.
  * done.
  * rewrite (mem_union_list_preserving _ ms); auto using contains_delete.
Qed.
Lemma mem_union_insert_vec {n} (ms : vec (mem_ Vi P) n) (i : fin n) m :
  ⊥ (m :: delete (fin_to_nat i) (vec_to_list ms)) →
  ⋃ vinsert i m ms = m ∪ ⋃ delete (fin_to_nat i) (vec_to_list ms).
Proof.
  induction ms as [|m' ? ms IH]; inv_fin i; simpl; [done |].
  intros i. rewrite !disjoint_list_cons. simpl. intros (?&?&?).
  rewrite IH, !(associative_L (∪)), (mem_union_commutative m); trivial.
  * apply mem_disjoint_list_double. eauto using mem_disjoint_union_rl.
  * rewrite disjoint_list_cons. eauto using mem_disjoint_union_rr.
Qed.

Lemma mem_disjoint_insert_vec {n} (ms : vec (mem_ Vi P) n) (i : fin n) m :
  vinsert i m ms ≡⊥ m :: delete (fin_to_nat i) (vec_to_list ms).
Proof.
  induction ms as [|m' ? ms IH]; inv_fin i; simpl; [done |].
  intros i. by rewrite Permutation_swap, IH.
Qed.
Lemma mem_disjoint_delete_vec {n} (ms : vec (mem_ Vi P) n) (i : fin n) :
  ms !!! i :: delete (fin_to_nat i) (vec_to_list ms) ≡⊥ ms.
Proof. by rewrite <-mem_disjoint_insert_vec, vlookup_insert_self. Qed.

Lemma mem_subseteq_lookup_vec {n} (ms : vec (mem_ Vi P) n) (i : fin n) :
  ⊥ ms → ms !!! i ⊆ ⋃ ms.
Proof.
  intros. rewrite <-(mem_union_delete_vec _ i) by done.
  apply mem_union_subseteq_l. rewrite <-mem_disjoint_union_list_le.
  by rewrite (right_id_L [] (++)), mem_disjoint_delete_vec.
Qed.

(** ** Properties of the [alloc] and [delete] operation *)
Lemma mem_perm_alloc m b v γ : mem_perm b (mem_alloc b v γ m) = Some γ.
Proof. unfold mem_perm, mem_alloc. simpl. by simpl_map. Qed.
Lemma mem_perm_kind_alloc m b v γ :
  mem_perm_kind b (mem_alloc b v γ m) = Some (perm_kind γ).
Proof. unfold mem_perm_kind. by rewrite mem_perm_alloc. Qed.
Lemma mem_perm_alloc_ne m b γ v b' :
  b ≠ b' → mem_perm b' (mem_alloc b v γ m) = mem_perm b' m.
Proof. unfold mem_perm, insert, mem_insert. intros. simpl. by simpl_map. Qed.
Lemma mem_perm_kind_alloc_ne m b γ v b' :
  b ≠ b' → mem_perm_kind b' (mem_alloc b v γ m) = mem_perm_kind b' m.
Proof. intros. unfold mem_perm_kind. by rewrite mem_perm_alloc_ne. Qed.

Lemma mem_perm_delete m b : mem_perm b (delete b m) = None.
Proof.
  destruct m. unfold delete, mem_delete, mem_perm. simpl. by simpl_map.
Qed.
Lemma mem_perm_kind_delete m b : mem_perm_kind b (delete b m) = None.
Proof. unfold mem_perm_kind. by rewrite mem_perm_delete. Qed.
Lemma mem_perm_delete_ne m b b' :
  b ≠ b' → mem_perm b' (delete b m) = mem_perm b' m.
Proof.
  destruct m. unfold mem_perm, delete, mem_delete. intros. simpl. by simpl_map.
Qed.
Lemma mem_perm_kind_delete_ne m b b' :
  b ≠ b' → mem_perm_kind b' (delete b m) = mem_perm_kind b' m.
Proof. intros. unfold mem_perm_kind. by rewrite mem_perm_delete_ne. Qed.

Lemma is_free_alloc m b γ v b' :
  is_free (mem_alloc b v γ m) b' ↔ b ≠ b' ∧ is_free m b'.
Proof.
  unfold is_free. destruct (decide (b = b')); subst.
  * rewrite mem_perm_alloc. naive_solver.
  * rewrite mem_perm_alloc_ne; naive_solver.
Qed.
Lemma is_free_alloc_list m γ b l :
  is_free (mem_alloc_list γ l m) b ↔ b ∉ fst <$> l ∧ is_free m b.
Proof.
  induction l as [|[b' v'] l IH]; simpl.
  { rewrite elem_of_nil. intuition. }
  rewrite not_elem_of_cons, is_free_alloc. intuition.
Qed.

Lemma mem_delete_singleton b v γ : delete b {[b,v,γ]} = ∅.
Proof.
  unfold singleton, mem_singleton, delete, mem_delete, empty, mem_empty.
  by rewrite delete_singleton.
Qed.

Lemma mem_delete_subseteq m b : delete b m ⊆ m.
Proof.
  destruct m. intros ???. simpl. rewrite lookup_delete_Some. naive_solver.
Qed.
Lemma mem_delete_subseteq_compat m1 m2 b : m1 ⊆ m2 → delete b m1 ⊆ delete b m2.
Proof.
  destruct m1 as [m1], m2 as [m2]. intros Hm12 b' v γ. simpl.
  rewrite lookup_delete_Some. intros [??].
  destruct (Hm12 b' v γ) as [γ' [??]]; eauto.
  exists γ'. by rewrite lookup_delete_ne.
Qed.
Lemma mem_delete_list_subseteq m bs : delete_list bs m ⊆ m.
Proof.
  induction bs as [|b bs IH]; simpl; [done |].
  transitivity (delete_list bs m); auto using mem_delete_subseteq.
Qed.
Lemma mem_delete_list_subseteq_compat m1 m2 bs :
  m1 ⊆ m2 → delete_list bs m1 ⊆ delete_list bs m2.
Proof. induction bs; simpl; auto using mem_delete_subseteq_compat. Qed.

Lemma mem_delete_free m b : is_free m b → delete b m = m.
Proof.
  destruct m as [m]. unfold delete, mem_delete, is_free, mem_perm.
  simpl. intros. by rewrite delete_notin; simplify_option_equality.
Qed.
Lemma mem_delete_list_free m bs : is_free_list m bs → delete_list bs m = m.
Proof.
  induction 1 as [|????? IH]; simpl; [done |]. by rewrite IH, mem_delete_free.
Qed.

Lemma mem_delete_union m1 m2 b : delete b (m1 ∪ m2) = delete b m1 ∪ delete b m2.
Proof.
  destruct m1 as [m1], m2 as [m2]. unfold delete, mem_delete, union, mem_union.
  f_equal. apply delete_union_with.
Qed.
Lemma mem_delete_union_l m1 m2 b γ :
  ⊥ [m1; m2] → mem_perm b m1 = Some γ → ¬perm_fragment γ →
  delete b (m1 ∪ m2) = delete b m1 ∪ m2.
Proof.
  intros. rewrite mem_delete_union, (mem_delete_free m2);
    eauto using is_free_fragment_l.
Qed.
Lemma mem_delete_union_r m1 m2 b γ :
  ⊥ [m1; m2] → mem_perm b m2 = Some γ → ¬perm_fragment γ →
  delete b (m1 ∪ m2) = m1 ∪ delete b m2.
Proof.
  intros. rewrite mem_delete_union, (mem_delete_free m1);
    eauto using is_free_fragment_r.
Qed.
Lemma mem_delete_list_union m1 m2 bs :
  delete_list bs (m1 ∪ m2) = delete_list bs m1 ∪ delete_list bs m2.
Proof. induction bs; simpl; rewrite <-?mem_delete_union; auto with f_equal. Qed.

Lemma mem_disjoint_alloc m ms b v γ :
  Forall (flip is_free b) ms → ⊥ (mem_alloc b v γ m :: ms) ↔ ⊥ (m :: ms).
Proof.
  cut (∀ m1 m2, is_free m2 b → mem_alloc b v γ m1 ⊥ m2 ↔ m1 ⊥ m2).
  { intros help ?. rewrite !disjoint_list_cons, !help; [done |].
    by rewrite is_free_union_list. }
  intros [m1] [m2]. unfold is_free, mem_perm, mem_alloc.
  simpl. rewrite fmap_None. intros Hm2. split.
  * intros Hm12 b' vγ1 vγ2 ??. simpl in *.
    destruct (decide (b = b')); subst; [congruence |].
    by destruct (Hm12 b' vγ1 vγ2); simpl; simpl_map.
  * intros Hm12 b' vγ1 vγ2 ??. simpl in *.
    destruct (decide (b = b')); subst; [congruence |].
    by destruct (Hm12 b' vγ1 vγ2); simpl; simpl_map.
Qed.
Lemma mem_disjoint_alloc_list m ms l γ :
  Forall (λ m, Forall (λ b, is_free m b) (fst <$> l)) ms →
  ⊥ (mem_alloc_list γ l m :: ms) ↔ ⊥ (m :: ms).
Proof.
  rewrite Forall_swap, Forall_fmap.
  induction 1 as [|[b v] l ? IH]; simpl. done. by rewrite mem_disjoint_alloc.
Qed.

Lemma mem_alloc_union_l m1 m2 b v γ :
  is_free m2 b → mem_alloc b v γ (m1 ∪ m2) = mem_alloc b v γ m1 ∪ m2.
Proof.
  destruct m1 as [m1], m2 as [m2].
  unfold is_free, mem_perm, mem_alloc, union, mem_union. intros.
  simpl. by rewrite insert_union_with_l; simplify_option_equality.
Qed.
Lemma mem_alloc_union_r m1 m2 b v γ :
  is_free m1 b → mem_alloc b v γ (m1 ∪ m2) = m1 ∪ mem_alloc b v γ m2.
Proof.
  destruct m1 as [m1], m2 as [m2].
  unfold is_free, mem_perm, mem_alloc, union, mem_union. intros.
  simpl. by rewrite insert_union_with_r; simplify_option_equality.
Qed.
Lemma mem_alloc_list_union_l m1 m2 l γ :
  is_free_list m2 (fst <$> l) →
  mem_alloc_list γ l (m1 ∪ m2) = mem_alloc_list γ l m1 ∪ m2.
Proof.
  induction l as [|[b v] l IH]; simpl; inversion_clear 1; [done |].
  rewrite <-mem_alloc_union_l; auto using f_equal.
Qed.
Lemma mem_alloc_list_union_r m1 m2 l γ :
  is_free_list m1 (fst <$> l) →
  mem_alloc_list γ l (m1 ∪ m2) = m1 ∪ mem_alloc_list γ l m2.
Proof.
  induction l as [|[b v] l IH]; simpl; inversion_clear 1; [done |].
  rewrite <-mem_alloc_union_r; auto using f_equal.
Qed.

Lemma mem_delete_alloc m b v γ : is_free m b → delete b (mem_alloc b v γ m) = m.
Proof.
  destruct m as [m]. intros.
  unfold delete, mem_delete, mem_alloc, is_free, mem_perm in *. simpl.
  f_equal. by rewrite delete_insert; simplify_option_equality.
Qed.
Lemma mem_delete_alloc_ne m b b' v γ :
  b ≠ b' → delete b (mem_alloc b' v γ m) = mem_alloc b' v γ (delete b m).
Proof.
  destruct m as [m]. intros.
  unfold delete, mem_delete, mem_alloc, is_free, mem_perm in *. simpl.
  f_equal. by rewrite delete_insert_ne; simplify_option_equality.
Qed.
Lemma mem_delete_list_alloc_ne m bs b v γ :
  b ∉ bs →
  delete_list bs (mem_alloc b v γ m) = mem_alloc b v γ (delete_list bs m).
Proof.
  induction bs; simpl; [done |].
  rewrite elem_of_cons. intros.
  rewrite IHbs, mem_delete_alloc_ne; intuition.
Qed.

Lemma mem_alloc_singleton b v γ : mem_alloc b v γ ∅ = {[b,v,γ]}.
Proof. done. Qed.
Lemma mem_alloc_singleton_l m b v γ :
  is_free m b → mem_alloc b v γ m = {[b,v,γ]} ∪ m.
Proof.
  intros. rewrite <-(left_id_L ∅ (∪) m) at 1.
  by rewrite mem_alloc_union_l, mem_alloc_singleton.
Qed.
Lemma mem_alloc_singleton_r m b v γ :
  is_free m b → mem_alloc b v γ m = m ∪ {[b,v,γ]}.
Proof.
  intros. rewrite <-(right_id_L ∅ (∪) m) at 1.
  by rewrite mem_alloc_union_r, mem_alloc_singleton.
Qed.

(** * Allocation of parameters *)
(** Allocation of parameters of a function is inductively defined. We prove
that it is equivalent to an alternative formulation that is used for the
soundness proof of the axiomatic semantics. *)
Lemma alloc_params_same_length γ m1 bs m2 vs :
  alloc_params γ m1 bs vs m2 → bs `same_length` vs.
Proof. induction 1; by constructor. Qed.

Lemma alloc_params_perm γ m1 bs vs m2 b :
  alloc_params γ m1 bs vs m2 → b ∈ bs → mem_perm b m2 = Some γ.
Proof.
  induction 1 as [|b' bs]; inversion_clear 1.
  * by rewrite mem_perm_alloc.
  * destruct (decide (b = b')); subst;
      rewrite ?mem_perm_alloc, ?mem_perm_alloc_ne; auto.
Qed.

Lemma alloc_params_is_free γ m1 bs vs m2 b :
  alloc_params γ m1 bs vs m2 → is_free m2 b → is_free m1 b.
Proof.
  intros Halloc. revert b. induction Halloc; [done |].
  intro. rewrite is_free_alloc. naive_solver.
Qed.
Lemma alloc_params_free γ m1 bs vs m2 :
  alloc_params γ m1 bs vs m2 → is_free_list m1 bs.
Proof.
  induction 1; constructor; simpl.
  * intros Hb. unfold is_free in *.
    efeed pose proof alloc_params_perm; eauto. congruence.
  * eauto using alloc_params_is_free.
  * done.
Qed.

Lemma alloc_params_alloc_list_1 γ m1 bs vs m2 :
  alloc_params γ m1 bs vs m2 → m2 = mem_alloc_list γ (zip bs vs) m1.
Proof. induction 1; simpl; by f_equal. Qed.
Lemma alloc_params_alloc_list_2 γ m bs vs :
  bs `same_length` vs → is_free_list m bs →
  alloc_params γ m bs vs (mem_alloc_list γ (zip bs vs) m).
Proof.
  induction 1; inversion_clear 1; simpl; constructor; auto.
  by rewrite is_free_alloc_list, zip_fst.
Qed.
Lemma alloc_params_alloc_list γ m1 bs vs m2 :
  alloc_params γ m1 bs vs m2 ↔
    m2 = mem_alloc_list γ (zip bs vs) m1 ∧
    is_free_list m1 bs ∧ bs `same_length` vs.
Proof.
  split.
  * intuition eauto using alloc_params_alloc_list_1,
     alloc_params_free, alloc_params_same_length.
  * intros [?[??]]. subst. by apply alloc_params_alloc_list_2.
Qed.
Lemma alloc_params_weaken γ m1 bs vs m2 m3 :
  ⊥[m1; m3] → ⊥[m2; m3] → alloc_params γ (m1 ∪ m3) bs vs (m2 ∪ m3) →
  alloc_params γ m1 bs vs m2.
Proof.
  rewrite !alloc_params_alloc_list, is_free_list_union.
  intros ?? (?&[??]&?). split_ands; auto. apply mem_union_cancel_l with m3.
  * done.
  * rewrite Permutation_swap, mem_disjoint_alloc_list; [done|].
    apply Forall_singleton. rewrite zip_fst; eauto using is_free_list_free.
  * rewrite <-mem_alloc_list_union_r by (by rewrite zip_fst).
    by rewrite !(mem_union_commutative m3).
Qed.

(** ** Properties about locks *)
Lemma elem_of_mem_locks m b : b ∈ locks m ↔ mem_perm_kind b m = Some Locked.
Proof.
  destruct m as [m]. unfold locks, mem_locks.
  rewrite elem_of_mapset_dom_with. unfold mem_perm_kind, mem_perm. simpl. split.
  * intros (?&?&?). by case_bool_decide; simplify_option_equality; f_equal.
  * intros. destruct (m !! b) as [vγ|]; [|done].
    exists vγ. by case_bool_decide; simplify_equality.
Qed.

Lemma mem_locks_lookup m b : b ∈ locks m → m !! b = None.
Proof.
  rewrite elem_of_mem_locks, <-mem_perm_kind_lookup_None.
  right. by exists Locked.
Qed.
Lemma mem_locks_disjoint m1 m2 : ⊥[m1; m2] → locks m1 ∩ locks m2 = ∅.
Proof.
  intros Hm12. apply elem_of_equiv_empty_L. intros b.
  rewrite elem_of_intersection, !elem_of_mem_locks, !mem_perm_kind_Some.
  intros [(γ1 & Hbm1 &?) (γ2 & ? & Hbm2)].
  destruct (perm_disjoint_locked_l γ1 γ2); eauto using mem_perm_disjoint.
Qed.
Lemma mem_locks_empty : locks (@empty (mem_ Vi P) _) = ∅.
Proof.
  apply elem_of_equiv_empty_L. intros b.
  by rewrite elem_of_mem_locks, mem_perm_kind_empty.
Qed.
Lemma mem_locks_insert m b v : locks (<[b:=v]>m) = locks m.
Proof.
  apply elem_of_equiv_L. intros b'.
  by rewrite !elem_of_mem_locks, !mem_perm_kind_insert.
Qed.
Lemma mem_locks_union m1 m2 : ⊥[m1; m2] → locks (m1 ∪ m2) = locks m1 ∪ locks m2.
Proof.
  intros. apply elem_of_equiv_L. intros b'.
  rewrite elem_of_union, !elem_of_mem_locks. split.
  { intros Hm12. apply mem_perm_kind_union_Some_inv in Hm12; naive_solver. }
  destruct 1.
  * eapply mem_perm_kind_union_Some_l; eauto using mem_perm_kind_locked_l.
  * eapply mem_perm_kind_union_Some_r; eauto using mem_perm_kind_locked_r.
Qed.
Lemma mem_locks_union_list ms : ⊥ ms → locks (⋃ ms) = ⋃ (locks <$> ms).
Proof.
  induction 1; simpl.
  * by apply mem_locks_empty.
  * rewrite mem_locks_union by auto. congruence.
Qed.

Lemma mem_locks_singleton b v p :
  perm_kind p = Locked → locks {[b,v,p]} = {[ b ]}.
Proof.
  intros. apply elem_of_equiv_L. intros b'.
  rewrite elem_of_mem_locks, elem_of_singleton.
  destruct (decide (b = b')); subst.
  * rewrite mem_perm_kind_singleton. naive_solver congruence.
  * rewrite mem_perm_kind_singleton_ne by done. naive_solver.
Qed.
Lemma mem_locks_singleton_ne b v p :
  perm_kind p ≠ Locked → locks {[b,v,p]} = ∅.
Proof.
  intros. apply elem_of_equiv_empty_L. intros b'.
  rewrite elem_of_mem_locks. destruct (decide (b = b')); subst.
  * rewrite mem_perm_kind_singleton. congruence.
  * by rewrite mem_perm_kind_singleton_ne.
Qed.

Lemma mem_locks_delete m b : locks (delete b m) = locks m ∖ {[ b ]}.
Proof.
  apply elem_of_equiv_L. intros b'.
  rewrite elem_of_difference, !elem_of_mem_locks, elem_of_singleton.
  destruct (decide (b = b')); subst.
  * rewrite mem_perm_kind_delete. naive_solver.
  * rewrite mem_perm_kind_delete_ne by done. naive_solver.
Qed.
Lemma mem_locks_delete_empty m b : locks m = ∅ → locks (delete b m) = ∅.
Proof. intros. rewrite mem_locks_delete. esolve_elem_of. Qed.
Lemma mem_locks_delete_list_empty m bs :
  locks m = ∅ → locks (delete_list bs m) = ∅.
Proof. induction bs; simpl; intros; rewrite ?mem_locks_delete_empty; auto. Qed.

Lemma mem_locks_alloc m b v p :
  is_free m b → perm_kind p ≠ Locked → locks (mem_alloc b v p m) = locks m.
Proof.
  intros. apply elem_of_equiv_L. intros b'.
  rewrite !elem_of_mem_locks. destruct (decide (b = b')); subst.
  * rewrite mem_perm_kind_alloc. unfold mem_perm_kind, is_free in *.
    intuition simplify_option_equality.
  * by rewrite mem_perm_kind_alloc_ne.
Qed.
Lemma mem_locks_alloc_list m l p :
  is_free_list m (fst <$> l) → perm_kind p ≠ Locked →
  locks (mem_alloc_list p l m) = locks m.
Proof.
  intros Hl ?. revert Hl. induction l as [|[??]]; inversion_clear 1; [done |].
  unfold mem_alloc_list; fold mem_alloc_list.
  rewrite mem_locks_alloc; auto. by rewrite is_free_alloc_list.
Qed.

Lemma mem_disjoint_lock m b γ ms :
  mem_perm b m = Some γ → ¬perm_fragment γ → m :: ms ⊆⊥ mem_lock b m :: ms.
Proof.
  cut (∀ m1 m2, ⊥[m1; m2] → mem_perm b m1 = None → m1 ⊥ mem_lock b m2).
  { intros help ? Hγ. apply mem_disjoint_cons_le_inj.
    intros m'. eauto using mem_perm_fragment_r. }
  intros [m1] [m2]. rewrite mem_disjoint_list_double.
  unfold mem_perm, mem_lock. intros Hm12 Hbm b' [v1 γ1] [v2 γ2] ? Hm2.
  simpl in *. rewrite lookup_alter_Some in Hm2.
  destruct Hm2 as [(?& [v1' γ1']&?&?)| [??]]; simplify_option_equality.
  by destruct (Hm12 b' (v1,γ1) (v2,γ2)).
Qed.
Lemma mem_lock_singleton b v γ : mem_lock b {[b,v,γ]} = {[b,v,perm_lock γ]}.
Proof.
  unfold mem_lock, singleton, mem_singleton. f_equal.
  simpl. by rewrite alter_singleton.
Qed.
Lemma mem_lock_insert_singleton b v w γ :
  mem_lock b (<[b:=v]>{[b,w,γ]}) = {[b,v,perm_lock γ]}.
Proof. by rewrite mem_insert_singleton, mem_lock_singleton. Qed.
Lemma mem_disjoint_lock_singleton ms b γ v :
  ¬perm_fragment γ → {[b,v,γ]} :: ms ⊆⊥ {[b,v,perm_lock γ]} :: ms.
Proof.
  intros. rewrite <-mem_lock_singleton.
  by eapply mem_disjoint_lock; rewrite ?mem_perm_singleton.
Qed.
Lemma mem_disjoint_lock_insert_singleton ms b γ v1 v2 :
  ¬perm_fragment γ → {[b,v1,γ]} :: ms ⊆⊥ {[b,v2,perm_lock γ]} :: ms.
Proof.
  intros. by rewrite <-mem_disjoint_lock_singleton,
    mem_disjoint_insert_singleton.
Qed.
Lemma mem_lock_None b m : mem_perm b m = None → mem_lock b m = m.
Proof.
  destruct m as [m]. unfold mem_perm, mem_lock; simpl.
  rewrite fmap_None. intros. f_equal. by rewrite alter_None.
Qed.

Lemma mem_lock_union_l m1 m2 b :
  mem_perm b m2 = None → mem_lock b (m1 ∪ m2) = mem_lock b m1 ∪ m2.
Proof.
  intros ?. destruct m1 as [m1], m2 as [m2].
  unfold mem_lock, mem_perm, union, mem_union in *. f_equal. simpl in *.
  apply alter_union_with_l.
  * intros [v1 γ1] [v2 γ2] ??. simplify_option_equality.
  * intros [v2 γ2]. by simplify_option_equality.
Qed.
Lemma mem_lock_union_r m1 m2 b :
  mem_perm b m1 = None → mem_lock b (m1 ∪ m2) = m1 ∪ mem_lock b m2.
Proof.
  intros ?. destruct m1 as [m1], m2 as [m2].
  unfold mem_lock, mem_perm, union, mem_union in *. f_equal. simpl in *.
  apply alter_union_with_r.
  * intros [v1 γ1] [v2 γ2] ??. simplify_option_equality.
  * intros [v2 γ2]. by simplify_option_equality.
Qed.
Lemma mem_lock_union_fragment_l m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m1 = Some γ → ¬perm_fragment γ →
  mem_lock b (m1 ∪ m2) = mem_lock b m1 ∪ m2.
Proof. eauto using mem_lock_union_l, mem_perm_fragment_l. Qed.
Lemma mem_lock_union_fragment_r m1 m2 b γ :
  ⊥[m1; m2] → mem_perm b m2 = Some γ → ¬perm_fragment γ →
  mem_lock b (m1 ∪ m2) = m1 ∪ mem_lock b m2.
Proof. eauto using mem_lock_union_r, mem_perm_fragment_r. Qed.

Lemma mem_lock_insert_union_l m1 m2 b v:
  ⊥[m1; m2] → mem_perm b m2 = None →
  mem_lock b (<[b:=v]>(m1 ∪ m2)) = mem_lock b (<[b:=v]>m1) ∪ m2.
Proof. intros. by rewrite mem_insert_union_l, mem_lock_union_l. Qed.
Lemma mem_lock_insert_union_r m1 m2 b v :
  ⊥[m1; m2] → mem_perm b m1 = None →
  mem_lock b (<[b:=v]>(m1 ∪ m2)) = m1 ∪ mem_lock b (<[b:=v]>m2).
Proof. intros. by rewrite mem_insert_union_r, mem_lock_union_r. Qed.
Lemma mem_lock_insert_union_fragment_l m1 m2 b v γ :
  ⊥[m1; m2] → mem_perm b m1 = Some γ → ¬perm_fragment γ →
  mem_lock b (<[b:=v]>(m1 ∪ m2)) = mem_lock b (<[b:=v]>m1) ∪ m2.
Proof. eauto using mem_lock_insert_union_l, mem_perm_fragment_l. Qed.
Lemma mem_lock_insert_union_fragment_r m1 m2 b v γ :
  ⊥[m1; m2] → mem_perm b m2 = Some γ → ¬perm_fragment γ →
  mem_lock b (<[b:=v]>(m1 ∪ m2)) = m1 ∪ mem_lock b (<[b:=v]>m2).
Proof. eauto using mem_lock_insert_union_r, mem_perm_fragment_r. Qed.

Global Instance: Proper ((≡) ==> (=) ==> (=)) mem_unlock.
Proof. repeat intro. fold_leibniz. by subst. Qed.

Lemma mem_disjoint_unlock Ω m ms : m :: ms ⊆⊥ mem_unlock Ω m :: ms.
Proof.
  apply mem_disjoint_cons_le_inj. intros m'.
  rewrite !mem_disjoint_list_double. intros Hm12 b [v1 γ1] [v2 γ2] Hm1 Hm2.
  destruct m' as [m1], m as [m2]. simpl in *.
  rewrite lookup_mapset_map_with in Hm2. case_bool_decide.
  * destruct (m2 !! b) as [[v2' γ2']|] eqn:?; simplify_equality.
    destruct (Hm12 b (v1,γ1) (v2,γ2')); trivial; simpl in *.
    eauto using perm_disjoint_unlock_r.
  * rewrite option_fmap_id in Hm2. by destruct (Hm12 b (v1,γ1) (v2,γ2)).
Qed.
Lemma mem_disjoint_unlock_all ms : ms ⊆⊥ (λ m, mem_unlock_all m) <$> ms.
Proof.
  intros. induction ms as [|m ms IH]; simpl; [done|].
  by rewrite <-mem_disjoint_unlock, <-IH.
Qed.
Lemma mem_perm_unlock Ω m b :
  b ∈ Ω → mem_perm b (mem_unlock Ω m) = perm_unlock <$> mem_perm b m.
Proof.
  intros Hb. destruct m as [m]. unfold mem_perm, mem_unlock. simpl.
  rewrite lookup_mapset_map_with. case_bool_decide; [|done].
  by destruct (m !! b).
Qed.
Lemma mem_perm_unlock_ne Ω m b :
  b ∉ Ω → mem_perm b (mem_unlock Ω m) = mem_perm b m.
Proof.
  intros Hb. destruct m as [m]. unfold mem_perm, mem_unlock. simpl.
  rewrite lookup_mapset_map_with. case_bool_decide; [done|].
  by destruct (m !! b).
Qed.
Lemma mem_unlock_weaken Ω1 Ω2 m :
  Ω2 ∩ locks m = ∅ → mem_unlock (Ω1 ∪ Ω2) m = mem_unlock Ω1 m.
Proof.
  intros HΩ. rewrite elem_of_equiv_empty_L in HΩ.
  destruct m as [m]. unfold mem_unlock. f_equal. apply map_eq. intros b.
  rewrite !lookup_mapset_map_with. repeat case_bool_decide.
  * done.
  * destruct (m !! b) as [[v γ]|] eqn:?; [|done].
    destruct (decide (perm_kind γ = Locked)).
    + destruct (HΩ b). rewrite elem_of_intersection, elem_of_mem_locks.
      rewrite mem_perm_kind_Some. unfold mem_perm.
      simplify_option_equality. esolve_elem_of.
    + simpl. by rewrite perm_unlock_other.
  * solve_elem_of.
  * solve_elem_of.
Qed.
Lemma mem_unlock_empty_locks m : mem_unlock ∅ m = m.
Proof.
  destruct m as [m]. unfold mem_unlock. f_equal. apply map_eq.
  intros b. rewrite !lookup_mapset_map_with.
  case_bool_decide. solve_elem_of. by destruct (m !! b).
Qed.
Lemma mem_unlock_unlocked Ω m : Ω ∩ locks m = ∅ → mem_unlock Ω m = m.
Proof.
  intros. by rewrite <-(left_id_L ∅ (∪) Ω),
    mem_unlock_weaken, mem_unlock_empty_locks.
Qed.
Lemma mem_unlock_empty Ω : mem_unlock Ω ∅ = ∅.
Proof.
  apply mem_unlock_unlocked.
  rewrite mem_locks_empty. by rewrite (right_absorb_L ∅ (∪)).
Qed.

Lemma mem_lookup_unlock Ω m b v :
  m !! b = Some v → mem_unlock Ω m !! b = Some v.
Proof.
  destruct m as [m]. unfold lookup, mem_lookup, mem_unlock. simpl.
  intros. rewrite lookup_mapset_map_with.
  case_bool_decide; simplify_option_equality; auto.
  edestruct perm_unlock_kind; eauto.
Qed.

Lemma mem_unlock_locks Ω m : locks (mem_unlock Ω m) = locks m ∖ Ω.
Proof.
  apply elem_of_equiv_L. intros b.
  rewrite elem_of_difference, !elem_of_mem_locks. unfold mem_perm_kind. split.
  * destruct (decide (b ∈ Ω)).
    + rewrite mem_perm_unlock by done. intros.
      simplify_option_equality. edestruct perm_unlock_kind; eauto.
    + by rewrite mem_perm_unlock_ne.
  * intros [??]. by rewrite mem_perm_unlock_ne.
Qed.
Lemma mem_locks_unlock_all m : locks (mem_unlock (locks m) m) = ∅.
Proof. rewrite mem_unlock_locks. solve_elem_of. Qed.

Lemma mem_unlock_union Ω m1 m2 :
  ⊥ [m1; m2] → mem_unlock Ω (m1 ∪ m2) = mem_unlock Ω m1 ∪ mem_unlock Ω m2.
Proof.
  rewrite mem_disjoint_list_double.
  destruct m1 as [m1], m2 as [m2]. intros Hm12.
  unfold mem_unlock, union, mem_union. f_equal. apply map_eq. intros b.
  rewrite lookup_mapset_map_with. apply option_eq. intros [v γ]. split.
  * rewrite fmap_Some. intros ([v' γ'] & Hm &?).
    rewrite lookup_union_with_Some in Hm |- *.
    rewrite !lookup_mapset_map_with.
    case_bool_decide; simplify_equality; [|by rewrite !option_fmap_id].
    destruct Hm as [[??]| [[??] | ([v1 γ1]&[v2 γ2]&?&?&?)]];
      simplify_option_equality; eauto.
    right. right. exists (v', perm_unlock γ1) (v2, perm_unlock γ2). simpl.
    destruct (Hm12 b (v',γ1) (v2,γ2)); auto.
    by rewrite perm_unlock_union.
  * rewrite lookup_union_with_Some, !lookup_mapset_map_with.
    case_bool_decide; [| by rewrite !option_fmap_id, lookup_union_with_Some].
    intros [[??]| [[??] | (vγ1&vγ2&?&?&?)]]; simplify_option_equality.
    + by erewrite lookup_union_with_Some_l; eauto.
    + by erewrite lookup_union_with_Some_r; eauto.
    + erewrite lookup_union_with_Some_lr; eauto.
      simpl. edestruct (Hm12 b); eauto. by rewrite perm_unlock_union.
Qed.

Lemma mem_unlock_union_l Ω m1 m2 :
  ⊥[m1; m2] → Ω ⊆ locks m1 → mem_unlock Ω (m1 ∪ m2) = mem_unlock Ω m1 ∪ m2.
Proof.
  intros Hm12 HΩ. rewrite mem_unlock_union by done.
  rewrite (mem_unlock_unlocked _ m2); [done|].
  eapply mem_locks_disjoint in Hm12. esolve_elem_of.
Qed.
Lemma mem_unlock_union_r Ω m1 m2 :
  ⊥[m1; m2] → Ω ⊆ locks m2 → mem_unlock Ω (m1 ∪ m2) = m1 ∪ mem_unlock Ω m2.
Proof.
  intros Hm12 HΩ. rewrite mem_unlock_union by done.
  rewrite (mem_unlock_unlocked _ m1); [done|].
  eapply mem_locks_disjoint in Hm12. esolve_elem_of.
Qed.
Lemma mem_unlock_all_union m1 m2 :
  ⊥[m1; m2] → mem_unlock_all (m1 ∪ m2) = mem_unlock_all m1 ∪ mem_unlock_all m2.
Proof.
  intros. rewrite mem_unlock_union, !mem_locks_union by done.
  by rewrite (mem_unlock_weaken (locks m1) _ m1), (commutative (∪) (locks m1)),
    (mem_unlock_weaken (locks m2) _ m2) by (by apply mem_locks_disjoint).
Qed.
Lemma mem_unlock_all_union_list ms :
  ⊥ ms → mem_unlock_all (⋃ ms) = ⋃ ((λ m, mem_unlock_all m) <$> ms).
Proof.
  induction 1.
  * by apply mem_unlock_empty.
  * simpl. rewrite mem_unlock_all_union; auto with f_equal.
Qed.

Lemma mem_unlock_singleton Ω b v γ :
  b ∈ Ω → mem_unlock Ω {[b,v,γ]} = {[b,v,perm_unlock γ]}.
Proof.
  intros. unfold mem_unlock, singleton, mem_singleton. f_equal.
  apply map_eq. intros b'. rewrite lookup_mapset_map_with.
  by destruct (decide (b = b')); subst; simpl_map; try case_bool_decide.
Qed.
Lemma mem_unlock_singleton_ne Ω b v γ :
  b ∉ Ω → mem_unlock Ω {[b,v,γ]} = {[b,v,γ]}.
Proof.
  intros. unfold mem_unlock, singleton, mem_singleton. f_equal.
  apply map_eq. intros b'. rewrite lookup_mapset_map_with.
  by destruct (decide (b = b')); subst; simpl_map; try case_bool_decide.
Qed.
Lemma mem_unlock_all_singleton b v γ :
  mem_unlock_all {[b,v,γ]} = {[b,v,perm_unlock γ]}.
Proof.
  destruct (decide (perm_kind γ = Locked)).
  * apply mem_unlock_singleton.
    rewrite elem_of_mem_locks, mem_perm_kind_singleton. by f_equal.
  * rewrite mem_unlock_singleton_ne, perm_unlock_other; auto.
    rewrite elem_of_mem_locks, mem_perm_kind_singleton. congruence.
Qed.

(** ** Properties of the [difference] operator *)
Lemma mem_disjoint_difference_alt m1 m2 : m1 ⊆ m2 → ⊥[m1; m2 ∖ m1].
Proof.
  rewrite mem_disjoint_list_double. destruct m1 as [m1],m2 as [m2].
  intros Hm12 b [v1 γ1] [v2 γ2] ? Hm21. simpl in *.
  destruct (Hm12 b v1 γ1) as (γ2' &?&?); auto. simpl in *.
  destruct (decide (γ1 ⊂ γ2')).
  * erewrite lookup_difference_with_Some_lr in Hm21
      by (by simplify_option_equality; eauto).
    simplify_equality. eauto using perm_disjoint_difference.
  * by erewrite lookup_difference_with_None_lr in Hm21
      by (by simplify_option_equality; eauto).
Qed.
Lemma mem_union_difference m1 m2 : m1 ⊆ m2 → m1 ∪ m2 ∖ m1 = m2.
Proof.
  destruct m1 as [m1],m2 as [m2]. intros Hm12.
  unfold union, difference, mem_union, mem_difference. f_equal.
  apply map_eq. intros b. apply option_eq. intros c; split; revert c.
  { intros [v γ] Hm21. apply lookup_union_with_Some in Hm21.
    destruct Hm21 as [[? Hm21]| [[? Hm21]|([v1 γ1]&[v3 γ3]&?&Hm21&?)]].
    * destruct (Hm12 b v γ) as (γ2 &?&?); auto. simpl in *.
      rewrite lookup_difference_with_None in Hm21.
      destruct Hm21 as [?|([v2' γ2']&[v1' γ1']&?&?&?)];
        simplify_map_equality; simplify_option_equality.
      by edestruct (not_subset_inv_L γ1' γ2'); subst.
    * rewrite lookup_difference_with_Some in Hm21.
      destruct Hm21 as [[??]|(?&?&?&?&?)]; congruence.
    * destruct (Hm12 b v1 γ1) as (γ2 &?&?); auto.
      simpl in *. simplify_equality.
      rewrite lookup_difference_with_Some in Hm21.
      destruct Hm21 as [[??]|([v2' γ2']&[v1' γ1']&?&?&?)];
        simplify_map_equality; simplify_option_equality.
      by rewrite perm_union_difference. }
  intros. destruct (m1 !! b) as [[v1 γ1]|] eqn:?.
  { destruct (Hm12 b v1 γ1) as (γ2 &?&?); auto. simplify_map_equality.
    destruct (subseteq_inv_L γ1 γ2); subst; trivial.
    * eapply lookup_union_with_Some_lr; eauto.
      { eapply lookup_difference_with_Some_lr; eauto.
        by simplify_option_equality. }
      simpl. erewrite perm_union_difference; eauto.
    * eapply lookup_union_with_Some_l; eauto.
      eapply lookup_difference_with_None_lr; eauto.
      simplify_option_equality; auto. by destruct (irreflexivity (⊂) γ2). }
  eapply lookup_union_with_Some_r; eauto.
  eapply lookup_difference_with_Some_l; eauto.
Qed.
Lemma mem_disjoint_difference m1 m2 ms :
  m1 ⊆ m2 → m2 :: ms ≡⊥ m1 :: m2 ∖ m1 :: ms.
Proof.
  intros. change ([m2] ++ ms ≡⊥ [m1; m2 ∖ m1] ++ ms). f_equiv.
  rewrite <-mem_disjoint_union by eauto using mem_disjoint_difference_alt.
  by rewrite mem_union_difference.
Qed.
End mem.

Arguments mem_unlock _ _ _ _ _ : simpl never.
Notation mem_unlock_all m := (mem_unlock (locks m) m).

(** * Tactics *)
(** The tactic [solve_mem_disjoint] solves goals of the shape [⊥ ms]. It
first eliminates all occurences of [∅], [∪], and [⋃] from the hypotheses
using the tactic [simplify_mem_disjoint_hyps]. Then it performs the same
job on the conclusion and finally tries to prove that one of assumptions
implies the conclusion. *)
Ltac solve_simple_mem_disjoint :=
  repeat first
  [ rewrite mem_disjoint_empty
  | rewrite <-mem_disjoint_union_list_le
  | rewrite <-mem_disjoint_union_le ];
  match goal with
  | _ => done
  | |- ⊥ [] => by apply disjoint_list_nil
  | |- ⊥ [_] => by apply mem_disjoint_list_singleton
  | H : ⊥ ?ms2 |- ⊥ ?ms1 => apply (mem_disjoint_contains _ _ H); solve_contains
  end.
Ltac simplify_mem_disjoint_hyps := repeat
  match goal with
  | H : ⊥ [] |- _ => clear H
  | H : ⊥ [_] |- _ => clear H
  | H : ?m1 ⊥ ?m2 |- _ => apply mem_disjoint_list_double in H
  | H : ⊥ ?ms |- _ =>
    progress repeat first
    [ rewrite mem_disjoint_empty in H
    | rewrite mem_disjoint_union_list in H by solve_simple_mem_disjoint
    | rewrite mem_disjoint_union in H by solve_simple_mem_disjoint ]
  end.
Ltac solve_mem_disjoint :=
  match goal with
  | |- ⊥ [] => by apply disjoint_list_nil
  | |- ⊥ [_] => by apply mem_disjoint_list_singleton
  | |- _ ⊥ _ => apply mem_disjoint_list_double
  | |- ⊥ _ => try done
  end;
  simplify_mem_disjoint_hyps; solve_simple_mem_disjoint.

(** The tactic [decompose_is_free] decomposes hypotheses of the shape [is_free].
All simplifications performed are reversible. *)
Ltac decompose_is_free := repeat
  match goal with
  | H : is_free (_ ∪ _) _ |- _ => apply is_free_union in H; destruct H
  | H : is_free (<[_:=_]>_) _ |- _ => apply is_free_insert in H
  | H : is_free_list (_ ∪ _) _ |- _ => apply is_free_list_union in H; destruct H
  end.

(** A variant of [simpl_map] and [simplify_map_equality] for memories. It also
simplifies occurrences of the [mem_perm] operation. *)
Tactic Notation "simpl_mem" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite mem_lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ => rewrite mem_lookup_insert in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite mem_lookup_insert_ne in H by tac
  | H : context[ {[ _ ]} !! _ ] |- _ => rewrite mem_lookup_singleton in H
  | H : context[ {[ _ ]} !! _ ] |- _ =>
    rewrite mem_lookup_singleton_ne in H by tac
  | H : context[ {[ _ ]} !! _ ] |- _ =>
    rewrite mem_lookup_singleton_locked in H by tac
  | H : context[ lookup (M:=mem_ ?Vi _) ?b (?m1 ∪ ?m2) ] |- _ =>
    let v := fresh in evar (v:val_ Vi); let v' := eval unfold v in v in clear v;
    let E := fresh in
    assert ((m1 ∪ m2) !! b = Some v') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite mem_lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] => rewrite mem_lookup_insert
  | |- context[ (<[_:=_]>_) !! _ ] => rewrite mem_lookup_insert_ne by tac
  | |- context[ {[ _ ]} !! _ ] => rewrite mem_lookup_singleton by tac
  | |- context[ {[ _ ]} !! _ ] => rewrite mem_lookup_singleton_ne by tac
  | |- context[ {[ _ ]} !! _ ] => rewrite mem_lookup_singleton_locked by tac
  | |- context [ lookup (M:=mem_ ?Vi _) ?b ?m ] =>
    let v := fresh in evar (v:val_ Vi); let v' := eval unfold v in v in clear v;
    let E := fresh in assert (m !! b = Some v') as E by tac; rewrite E; clear E
  | H : context[ mem_perm _ ∅ ] |- _ => rewrite mem_perm_empty in H
  | H : context[ mem_perm _ (<[_:=_]>_) ] |- _ => rewrite mem_perm_insert in H
  | H : context[ mem_perm _ {[ _ ]} ] |- _ => rewrite mem_perm_singleton in H
  | H : context[ mem_perm _ {[ _ ]} ] |- _ =>
    rewrite mem_perm_singleton_ne in H by tac
  | H : context[ mem_perm (P:=?P) ?b (?m1 ∪ ?m2) ] |- _ =>
    let γ := fresh in evar (γ:P); let γ' := eval unfold γ in γ in clear γ;
    let E := fresh in
    assert (mem_perm b (m1 ∪ m2) = Some γ') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ mem_perm _ ∅ !! _ ] => rewrite mem_perm_empty
  | |- context[ mem_perm _ (<[_:=_]>_) ] => rewrite mem_perm_insert
  | |- context[ mem_perm _ {[ _ ]} ] => rewrite mem_perm_singleton
  | |- context[ mem_perm _ {[ _ ]} ] => rewrite mem_perm_singleton_ne by tac
  | |- context [ mem_perm (P:=?P) ?b ?m ] =>
    let γ := fresh in evar (γ:P); let γ' := eval unfold γ in γ in clear γ;
    let E := fresh in assert (mem_perm b m = Some γ') as E by tac;
    rewrite E; clear E
  end.

Create HintDb simpl_mem.
Tactic Notation "simpl_mem" := simpl_mem by eauto with simpl_mem.
Hint Extern 1200 (⊥ _) => solve_mem_disjoint : simpl_mem.
Hint Extern 80 ((_ ∪ _) !! _ = _) => apply mem_lookup_union_Some_l : simpl_mem.
Hint Extern 81 ((_ ∪ _) !! _ = _) => apply mem_lookup_union_Some_r : simpl_mem.
Hint Extern 80 ({[ _ ]} !! _ = _) => apply mem_lookup_singleton : simpl_mem.
Hint Extern 80 (<[_:=_]> _ !! _ = _) => apply mem_lookup_insert : simpl_mem.
Hint Extern 80 (<[_:=_]> _ !! _ = _) => apply mem_lookup_insert_ne : simpl_mem.
Hint Extern 80 (mem_perm _ (_ ∪ _) = _) =>
  apply mem_perm_union_fragment_l : simpl_mem.
Hint Extern 81 (mem_perm _ (_ ∪ _) = _) =>
  apply mem_perm_union_fragment_r : simpl_mem.
Hint Extern 100 (mem_perm _ (_ ∪ _) = Some _) =>
  apply mem_perm_union_Some_lr : simpl_mem.
Hint Extern 80 (mem_perm _ {[ _ ]} = Some _) =>
  apply mem_perm_singleton : simpl_mem.
Hint Extern 80 (mem_perm _ <[_:=_]> = Some _) =>
  apply mem_perm_insert : simpl_mem.
Hint Extern 1 (¬perm_fragment _) =>
  apply perm_fragment_subseteq_write : simpl_mem.
Hint Extern 1 (¬perm_fragment _) => apply perm_fragment_not_read : simpl_mem.
Hint Extern 1 (¬perm_fragment _) =>
  apply perm_fragment_subseteq_write : simpl_mem.
Hint Extern 1 (¬perm_fragment _) => apply perm_fragment_free : simpl_mem.
Hint Extern 1 (¬perm_fragment _) => apply perm_fragment_locked : simpl_mem.
Hint Extern 1 (perm_kind _ ≠ _) => apply perm_kind_half_locked : simpl_mem.

Tactic Notation "simplify_mem_equality" "by" tactic3(tac) := repeat
  match goal with
  | _ => progress simpl_mem by tac
  | _ => progress simplify_equality
  | H1 : ?o = Some ?x, H2 : ?o = Some ?y |- _ =>
    assert (y = x) by congruence; clear H2
  | H1 : ?o = Some ?x, H2 : ?o = None |- _ => congruence
  | H : {[ _ ]} !! _ = None |- _ => rewrite mem_lookup_singleton_None in H
  | H : {[ _ ]} !! _ = Some _ |- _ =>
    rewrite mem_lookup_singleton_Some in H; destruct H as (?&?&?)
  | H1 : ?m1 !! ?b = Some ?v, H2 : ?m2 !! ?b = Some ?w |- _ =>
    let H3 := fresh in
    feed pose proof (mem_lookup_weaken_inv m1 m2 b v w) as H3;
      [done | by tac | done | ];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in assert (m1 ⊆ m2) as H3 by tac; apply H3 in H1; congruence
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply mem_union_cancel_l in H; [| solve[tac] | solve [tac]]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply mem_union_cancel_r in H; [| solve[tac] | solve [tac]]
  | H1 : ?m1 !! ?b = Some ?v1, H2 : ?m2 !! ?b = Some ?v2, H : ⊥ [?m1; ?m2] |- _ =>
    unless (v1 = v2) by done;
    pose proof (mem_disjoint_lookup m1 m2 b v1 v2 H H1 H2)
  end.
Tactic Notation "simplify_mem_equality" :=
  simplify_mem_equality by eauto with simpl_mem.

Hint Extern 1200 (⊥ _) => solve_mem_disjoint : mem.
Hint Extern 100 (_ !! _ = _) => progress simpl_mem : mem.
Hint Extern 100 (mem_perm _ _ = _) => progress simpl_mem : mem.
Hint Extern 100 (is_writable (_ ∪ _) _) => apply is_writable_union_l : mem.
Hint Extern 100 (is_writable (_ ∪ _) _) => apply is_writable_union_r : mem.
Hint Extern 100 (is_writable {[ _ ]} _) => apply is_writable_singleton : mem.
Hint Extern 100 (is_freeable (_ ∪ _) _) => apply is_freeable_union_l : mem.
Hint Extern 100 (is_freeable (_ ∪ _) _) => apply is_freeable_union_r : mem.
Hint Extern 100 (is_freeable {[ _ ]} _) => apply is_freeable_singleton : mem.
Hint Extern 100 (is_free (_ ∪ _) _) => apply is_free_union_2 : mem.
Hint Extern 98 (∅ ⊆ _) => apply mem_subseteq_empty : mem.
Hint Extern 99 (_ ∪ _ ⊆ _ ∪ _) => apply mem_union_preserving_l : mem.
Hint Extern 99 (_ ∪ _ ⊆ _ ∪ _) => apply mem_union_preserving_r : mem.
Hint Extern 100 (_ ⊆ _ ∪ _) => apply mem_union_subseteq_l_alt : mem.
Hint Extern 100 (_ ⊆ _ ∪ _) => apply mem_union_subseteq_r_alt : mem.
Hint Extern 100 (_ !!! _ ⊆ ⋃ _) => apply mem_subseteq_lookup_vec : mem.
Hint Extern 1 (¬perm_fragment _) => apply perm_fragment_not_read : mem.
Hint Extern 1 (¬perm_fragment _) => apply perm_fragment_subseteq_write : mem.
Hint Extern 1 (¬perm_fragment _) => apply perm_fragment_free : mem.
Hint Extern 1 (¬perm_fragment _) => apply perm_fragment_locked : mem.
