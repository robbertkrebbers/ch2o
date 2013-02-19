(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines an abstract interface for permissions. This interface
will be used in the abstract memory model. The purpose of this interface is to
allow different ways of handling permissions (no permissions at all, simple
free/write/free permissions, fractional permissions, fractional permissions
with locks) without having to hard-wire these into the memory. *)

(** Permissions form a partial order [(⊆)] with a commutative monoid [(∪)]
structure. Although the operation [x ∪ y] is only allowed if [x ⊥ y], we
still treat [(∪)] as a total function to ease formalization. Permissions [x]
and [y] are ordered [x ⊆ y] in case [y] permits more operations to be performed.
The operation [(∪)] is used to define the disjoint union of memories. In case
two memories contain an overlapping cell with permissions [x] and [y]
respectively, and [x ⊥ y], then the permission of the joined cell is [x ∪ y]. *)

(** It is a good idea to keep fractional permissions in mind. There the order
[(⊆)] is just the numerical order on the rationals, [(∪)] is ordinary addition,
and [x ⊥ y] holds if [x + y ≤ 1]. *)
Require Export orders.

(** * Permission kinds *)
(** Since the actual implementation a system of permissions may be very complex,
we do not want to expose that in the interface. Hence, we split permissions up
into four different kinds. These kinds (in increasing order) are:
- A permission whose kind is [Free] allows all operations (read, write, free).
- A permission whose kind is [Write] allows just reading and writing.
- A permission whose kind is [Read] allows solely reading.

Apart from that, we consider permissions whose kind is [Locked]. Permissions
with that kind are temporarily obtained using the [perm_lock] operation after a
write has been performed during a sequence. When a sequence point occurs, the
permission will be unlocked again using the [perm_unlock] operation. *)
Inductive pkind := Free | Write | Read | Locked.

Class PermKind P := perm_kind : P → pkind.
Class PermLock P := perm_lock_ : bool → P → P.
Notation perm_lock := (perm_lock_ true).
Notation perm_unlock := (perm_lock_ false).

(** Permission kinds are ordered with respect to the operations that they
permit. Since read only memory cannot be used for writing (and hence cannot be
locked), the kinds [Locked] and [Read] are independent with respect to this
order. *)
Inductive pkind_subseteq: SubsetEq pkind :=
  | pkind_subseteq_refl k : k ⊆ k
  | Write_subseteq_Free : Write ⊆ Free
  | Read_subseteq_Free : Read ⊆ Free
  | Locked_subseteq_Free : Locked ⊆ Free
  | Read_subseteq_Write : Read ⊆ Write
  | Locked_subseteq_Write : Locked ⊆ Write.
Existing Instance pkind_subseteq.

Instance pkind_dec (k1 k2 : pkind) : Decision (k1 = k2).
Proof. solve_decision. Defined.
Instance pkind_subseteq_dec (k1 k2 : pkind) : Decision (k1 ⊆ k2).
Proof.
 refine
  match k1, k2 with
  | Free, Free => left _
  | Write, Free => left _
  | Read, Free => left _
  | Locked, Free => left _
  | Locked, Locked => left _
  | Locked, Write => left _
  | Read, Read => left _
  | Read, Write => left _
  | Write, Write => left _
  | _, _ => right _
  end; first [by constructor | by inversion 1].
Defined.
Instance: PartialOrder pkind.
Proof.
  repeat split.
  * by intros []; constructor.
  * destruct 1; inversion 1; constructor.
  * destruct 1; inversion 1; constructor.
Qed.

Lemma Read_subseteq k : Read ⊆ k ↔ k = Read ∨ k = Write ∨ k = Free.
Proof. split. destruct 1; eauto. by intros [?|[?|?]]; subst; constructor. Qed.
Lemma Write_subseteq k : Write ⊆ k ↔ k = Write ∨ k = Free.
Proof. split. inversion 1; eauto. by intros [?|?]; subst; constructor. Qed.
Lemma Locked_subseteq k : Locked ⊆ k ↔ k = Locked ∨ k = Write ∨ k = Free.
Proof. split. inversion 1; eauto. by intros [?|[?|?]]; subst; constructor. Qed.
Lemma Free_subseteq k : Free ⊆ k ↔ k = Free.
Proof. split. by inversion 1. by intros; subst. Qed.

Lemma subseteq_Read k : k ⊆ Read ↔ k = Read.
Proof. split. by inversion 1. by intros; subst. Qed.
Lemma subseteq_Write k : k ⊆ Write ↔ k = Read ∨ k = Write ∨ k = Locked.
Proof. split. inversion 1; eauto. by intros [?|[?|?]]; subst; constructor. Qed.
Lemma subseteq_Locked k : k ⊆ Locked ↔ k = Locked.
Proof. split. by inversion 1. by intros; subst. Qed.
Lemma subseteq_Free k : k ⊆ Free.
Proof. destruct k; constructor. Qed.

Lemma not_Read_subseteq k : Read ⊈ k ↔ k = Locked.
Proof. rewrite Read_subseteq. destruct k; naive_solver. Qed.
Lemma not_Write_subseteq k : Write ⊈ k ↔ k = Read ∨ k = Locked.
Proof. rewrite Write_subseteq. destruct k; naive_solver. Qed.
Lemma not_Locked_subseteq k : Locked ⊈ k ↔ k = Read.
Proof. rewrite Locked_subseteq. destruct k; naive_solver. Qed.

Lemma not_Locked_weaken k1 k2 :
  k1 ≠ Locked → k1 ⊆ k2 → k2 ≠ Locked.
Proof. intros Hk1 ?. contradict Hk1. subst. by apply subseteq_Locked. Qed.

(** * The interface for permissions *)
(** The interface for permissions is slightly underspecified so as to allow for
a broad variety of implementations. In particular, we only require the
[mem_unlock] operation to actually unlock the permission, whereas the [mem_lock]
operation is not required to really lock the permission. This is to allow the
unit type, that models a system without permissions, as a satisfying
implementation. *)

(** The laws relating [(⊆)], [(⊥)] and [(∪)] all correspond to their respective
counterpart on the memory that is required to hold for it to be used in a
separation logic. An important property is that only permissions whose kinds is
[Read] can be joined together with another permission. This is to ensure that
given two disjoint memories, only their readable parts may overlap, but their
writable parts do never overlap. *)
Definition perm_fragment `{Disjoint P} (p : P) := ∃ p', p ⊥ p'.

Class Permissions (P : Set)
    `{PermKind P}
    `{PermLock P}
    `{Union P}
    `{Disjoint P}
    `{SubsetEq P}
    `{Difference P}
    `{∀ x y : P, Decision (x = y)}
    `{∀ x y : P, Decision (x ⊥ y)}
    `{∀ x y : P, Decision (x ⊆ y)} : Prop := {
  perm_po :> PartialOrder P;
  perm_sym :> Symmetric (⊥);
  perm_kind_preserving x y :
    x ⊆ y →
    perm_kind x ⊆ perm_kind y;
  perm_fragment_read x :
    perm_fragment x →
    perm_kind x = Read;
  perm_disjoint_weaken_l x x' y :
    x ⊥ y → x' ⊆ x → x' ⊥ y;
  perm_unlock_lock x :
    Write ⊆ perm_kind x →
    perm_unlock (perm_lock x) = x;
  perm_unlock_other x :
    perm_kind x ≠ Locked →
    perm_unlock x = x;
  perm_unlock_kind x :
    perm_kind (perm_unlock x) ≠ Locked;
  perm_assoc :> Associative (=) (∪);
  perm_comm :> Commutative (=) (∪);
  perm_disjoint_union_ll x y z :
    x ∪ y ⊥ z → x ⊥ z;
  perm_disjoint_union_move_l x y z :
    x ∪ y ⊥ z → x ⊥ y ∪ z;
  perm_union_subset_l x y :
    x ⊥ y →
    x ⊂ x ∪ y;
  perm_union_preserving_l x y z :
    x ⊆ y → z ∪ x ⊆ z ∪ y;
  perm_union_reflecting_l x y z :
    z ⊥ x → z ⊥ y →
    z ∪ x ⊆ z ∪ y →
    x ⊆ y;
  perm_difference_disjoint x y :
    x ⊂ y → x ⊥ y ∖ x;
  perm_union_difference x y :
    x ⊂ y →
    x ∪ y ∖ x = y
}.

(** * General properties of permissions *)
(** We prove some derived properties for arbitrary permission implementations.
Many of these properties are just variants of the laws using commutativity of
[(∪)] and symmetry of [(⊥)]. *)
Section permissions.
Context `{Permissions P}.

Lemma perm_disjoint_kind_l x y : x ⊥ y → perm_kind x = Read.
Proof. intros. apply perm_fragment_read. by exists y. Qed.
Lemma perm_disjoint_kind_r x y : x ⊥ y → perm_kind y = Read.
Proof. intros. by apply perm_disjoint_kind_l with x. Qed.
Lemma perm_disjoint_locked_l x y : x ⊥ y → perm_kind x ≠ Locked.
Proof. intros Hxy ?. apply perm_disjoint_kind_l in Hxy. congruence. Qed.
Lemma perm_disjoint_locked_r x y : x ⊥ y → perm_kind y ≠ Locked.
Proof. intros Hxy ?. apply perm_disjoint_kind_r in Hxy. congruence. Qed.
Lemma perm_disjoint_write_l x y : x ⊥ y → perm_kind x ≠ Write.
Proof. intros Hxy ?. apply perm_disjoint_kind_l in Hxy. congruence. Qed.
Lemma perm_disjoint_write_r x y : x ⊥ y → perm_kind y ≠ Write.
Proof. intros Hxy ?. apply perm_disjoint_kind_r in Hxy. congruence. Qed.
Lemma perm_disjoint_free_l x y : x ⊥ y → perm_kind x ≠ Free.
Proof. intros Hxy ?. apply perm_disjoint_kind_l in Hxy. congruence. Qed.
Lemma perm_disjoint_free_r x y : x ⊥ y → perm_kind y ≠ Free.
Proof. intros Hxy ?. apply perm_disjoint_kind_r in Hxy. congruence. Qed.

Lemma perm_fragment_not_read x : perm_kind x ≠ Read → ¬perm_fragment x.
Proof. intuition auto using perm_fragment_read. Qed.
Lemma perm_fragment_write x : perm_kind x = Write → ¬perm_fragment x.
Proof. intros ? Hx. apply perm_fragment_read in Hx. congruence. Qed.
Lemma perm_fragment_free x : perm_kind x = Free → ¬perm_fragment x.
Proof. intros ? Hx. apply perm_fragment_read in Hx. congruence. Qed.
Lemma perm_fragment_subseteq_write x :
  Write ⊆ perm_kind x → ¬perm_fragment x.
Proof.
  rewrite Write_subseteq.
  intros [?|?]; eauto using perm_fragment_write, perm_fragment_free.
Qed.
Lemma perm_fragment_locked x : perm_kind x = Locked → ¬perm_fragment x.
Proof. intros ? Hx. apply perm_fragment_read in Hx. congruence. Qed.

Lemma perm_disjoint_weaken_r x y y' :
  x ⊥ y → y' ⊆ y → x ⊥ y'.
Proof. rewrite !(symmetry_iff _ x). apply perm_disjoint_weaken_l. Qed.
Lemma perm_disjoint_weaken x x' y y' :
  x ⊥ y → x' ⊆ x → y' ⊆ y → x' ⊥ y'.
Proof. eauto using perm_disjoint_weaken_l, perm_disjoint_weaken_r. Qed.

Lemma perm_disjoint_union_lr x y z :
  x ∪ y ⊥ z → y ⊥ z.
Proof. rewrite (commutative _). apply perm_disjoint_union_ll. Qed.
Lemma perm_disjoint_union_rl x y z :
  x ⊥ y ∪ z → x ⊥ y.
Proof. rewrite !(symmetry_iff _ x). apply perm_disjoint_union_ll. Qed.
Lemma perm_disjoint_union_rr x y z :
  x ⊥ y ∪ z → x ⊥ z.
Proof. rewrite (commutative _). apply perm_disjoint_union_rl. Qed.

Lemma perm_disjoint_union_move_r x y z :
  x ⊥ y ∪ z → x ∪ y ⊥ z.
Proof.
  intros. symmetry. rewrite (commutative _).
  apply perm_disjoint_union_move_l. by rewrite (commutative _).
Qed.

Lemma perm_disjoint_union_l x y z :
  x ∪ y ⊥ z → x ⊥ y.
Proof. eauto using perm_disjoint_union_rl, perm_disjoint_union_move_l. Qed.
Lemma perm_disjoint_union_r x y z :
  x ⊥ y ∪ z → y ⊥ z.
Proof. eauto using perm_disjoint_union_lr, perm_disjoint_union_move_r. Qed.

Lemma perm_union_subset_r x y :
  y ⊥ x → x ⊂ y ∪ x.
Proof.
  rewrite (symmetry_iff _), (commutative_eq (∪)).
  by apply perm_union_subset_l.
Qed.
Lemma perm_union_subseteq_l x y :
  x ⊥ y → x ⊆ x ∪ y.
Proof. intros. by apply subset_subseteq, perm_union_subset_l. Qed.
Lemma perm_union_subseteq_r x y :
  y ⊥ x → x ⊆ y ∪ x.
Proof. intros. by apply subset_subseteq, perm_union_subset_r. Qed.
Lemma perm_union_ne_l x y :
  x ⊥ y → x ≠ x ∪ y.
Proof.
  intros ? E. destruct (perm_union_subset_l x y) as [? []]; auto.
  by rewrite <-E.
Qed.
Lemma perm_union_ne_r x y :
  y ⊥ x → x ≠ y ∪ x.
Proof.
  intros ? E. destruct (perm_union_subset_r x y) as [? []]; auto.
  by rewrite <-E.
Qed.

Lemma perm_union_preserving_r x y z :
  x ⊆ y → x ∪ z ⊆ y ∪ z.
Proof. rewrite !(commutative _ _ z). apply perm_union_preserving_l. Qed.
Lemma perm_union_strict_preserving_l x y z :
  z ⊥ x → z ⊥ y →
  x ⊂ y → z ∪ x ⊂ z ∪ y.
Proof.
  intros ?? [Hxy1 Hxy2]. split.
  * auto using perm_union_preserving_l.
  * contradict Hxy2. by apply perm_union_reflecting_l with z.
Qed.
Lemma perm_union_strict_preserving_r x y z :
  x ⊥ z → y ⊥ z →
  x ⊂ y → x ∪ z ⊂ y ∪ z.
Proof.
  intros. rewrite !(commutative_eq (∪) _ z).
  by apply perm_union_strict_preserving_l.
Qed.

Lemma perm_union_reflecting_r x y z :
  x ⊥ z → y ⊥ z →
  x ∪ z ⊆ y ∪ z → x ⊆ y.
Proof.
  intros ??. rewrite !(commutative_eq (∪) _ z).
  by apply perm_union_reflecting_l.
Qed.
Lemma perm_union_strict_reflecting_l x y z :
  z ⊥ x → z ⊥ y →
  z ∪ x ⊂ z ∪ y → x ⊂ y.
Proof.
  intros ?? [Hxy1 Hxy2]. split.
  * eauto using perm_union_reflecting_l.
  * contradict Hxy2. by apply perm_union_preserving_l.
Qed.
Lemma perm_union_strict_reflecting_r x y z :
  x ⊥ z → y ⊥ z →
  x ∪ z ⊂ y ∪ z → x ⊂ y.
Proof.
  rewrite !(commutative_eq (∪) _ z), !(symmetry_iff _ _ z).
  apply perm_union_strict_reflecting_l.
Qed.

Lemma perm_union_cancel_l x y z :
  z ⊥ x → z ⊥ y →
  z ∪ x = z ∪ y → x = y.
Proof.
  intros ?? E. by apply (anti_symmetric _);
    apply perm_union_reflecting_l with z; rewrite ?E.
Qed.
Lemma perm_union_cancel_r x y z :
  x ⊥ z → y ⊥ z →
  x ∪ z = y ∪ z → x = y.
Proof.
  intros ??. rewrite !(commutative_eq (∪) _ z).
  by apply perm_union_cancel_l.
Qed.

Lemma perm_kind_union x y :
  x ⊥ y →
  perm_kind (x ∪ y) ≠ Locked.
Proof.
  intros ? Hxy. feed pose proof (perm_kind_preserving x (x ∪ y))
    as Hxxy; auto using perm_union_subseteq_l.
  rewrite (perm_disjoint_kind_l x y), Hxy in Hxxy by done.
  by inversion Hxxy.
Qed.

Lemma perm_unlock_union x y :
  x ⊥ y →
  perm_unlock (x ∪ y) = perm_unlock x ∪ perm_unlock y.
Proof.
  intros. by rewrite !perm_unlock_other by eauto using perm_kind_union,
     perm_disjoint_locked_l, perm_disjoint_locked_r.
Qed.

Lemma perm_disjoint_unlock_l x y :
  x ⊥ y → perm_unlock x ⊥ y.
Proof.
  destruct (decide (perm_kind x = Locked)).
  * intros. by destruct (perm_disjoint_locked_l x y).
  * by rewrite perm_unlock_other.
Qed.
Lemma perm_disjoint_unlock_r x y :
  x ⊥ y → x ⊥ perm_unlock y.
Proof. intros. symmetry. by apply perm_disjoint_unlock_l. Qed.

Lemma perm_unlock_idempotent x :
  perm_unlock (perm_unlock x) = perm_unlock x.
Proof.
  rewrite (perm_unlock_other (perm_unlock x)); auto using perm_unlock_kind.
Qed.
End permissions.
