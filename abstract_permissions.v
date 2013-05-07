(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines an abstract interface for permissions. This interface
will be used in the abstract memory model. The purpose of this interface is to
allow different ways of handling permissions (no permissions at all, simple
free/write/free permissions, fractional permissions, fractional permissions
with locks) without having to hard-wire these into the memory. *)

(** Permissions form a partial order [(⊆)] with a commutative monoid [(∪)]
structure. Although the operation [x ∪ y] only has to be well defined if
[x ⊥ y], we still treat it as a total function to ease formalization.
Permissions [x] and [y] are ordered [x ⊆ y] in case [y] permits more operations
to be performed. The operation [(∪)] is used to define the disjoint union of
memories. In case two memories contain an overlapping cell with permissions [x]
and [y] respectively, and [x ⊥ y], then the permission of the joined cell is
[x ∪ y]. *)

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

(** Permission kinds are ordered with respect to the operations that they
permit. Since read only memory cannot be used for writing (and hence cannot be
locked), the kinds [Locked] and [Read] are independent from each other with
respect to this order. *)
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
  | _, Free => left _
  | (Locked | Read | Write), Write => left _
  | Locked, Locked => left _
  | Read, Read => left _
  | _, _ => right _
  end; first [by constructor | by inversion 1].
Defined.
Instance: PartialOrder (@subseteq pkind _).
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
Local Unset Elimination Schemes.

(** The interface for permissions is slightly underspecified so as to allow for
a broad variety of implementations. In particular, we only require the
[mem_unlock] operation to actually unlock the permission, whereas the [mem_lock]
operation is not required to really lock the permission. This is to allow an
implementation that does not assign undefined behavior to sequence point
violations. *)

(** The laws relating [(⊆)], [(⊥)] and [(∪)] all correspond to their respective
counterpart on the memory that is required to hold in a separation logic. An
important property is that only permissions whose kinds is [Read] can be joined
together with another permission. This is to ensure that given two disjoint
memories, only their readable parts may overlap, but their writable parts do
never. *)
Class PermissionsOps (P : Set) := {
  perm_kind : P → pkind;
  perm_lock_ : bool → P → P;
  perm_subseteq :> SubsetEq P;
  perm_disjoint :> Disjoint P;
  perm_union :> Union P;
  perm_difference :> Difference P;
  perm_disjoint_dec (x y : P) :> Decision (x ⊥ y);
  perm_eq_dec (x y : P) :> Decision (x = y);
  perm_subseteq_dec (x y : P) :> Decision (x ⊆ y)
}.
Arguments perm_kind _ _ _ : simpl never.
Arguments perm_lock_ _ _ _ _ : simpl never.
Arguments perm_subseteq _ _ _ _ : simpl never.
Arguments perm_disjoint _ _ _ _ : simpl never.
Arguments perm_union _ _ _ _ : simpl never.
Arguments perm_difference _ _ _ _ : simpl never.

Notation perm_lock := (perm_lock_ true).
Notation perm_unlock := (perm_lock_ false).
Definition perm_fragment `{PermissionsOps P} (p : P) := ∃ p', p ⊥ p'.

Class Permissions (P : Set) `{PermissionsOps P} : Prop := {
  perm_po :> PartialOrder (@subseteq P _);
  perm_sym :> Symmetric (@disjoint P _);
  perm_kind_preserving (x y : P) : x ⊆ y → perm_kind x ⊆ perm_kind y;
  perm_fragment_read (x : P) : perm_fragment x → perm_kind x = Read;
  perm_disjoint_weaken_l (x x' y : P) : x ⊥ y → x' ⊆ x → x' ⊥ y;
  perm_unlock_lock (x: P) : Write ⊆ perm_kind x → perm_unlock (perm_lock x) = x;
  perm_unlock_other (x : P) : perm_kind x ≠ Locked → perm_unlock x = x;
  perm_unlock_kind (x : P) : perm_kind (perm_unlock x) ≠ Locked;
  perm_assoc :> Associative (=) (@union P _);
  perm_comm :> Commutative (=) (@union P _);
  perm_disjoint_union_ll (x y z : P) : x ∪ y ⊥ z → x ⊥ z;
  perm_disjoint_union_move_l (x y z : P) : x ∪ y ⊥ z → x ⊥ y ∪ z;
  perm_union_subset_l (x y : P) : x ⊥ y →  x ⊂ x ∪ y;
  perm_union_preserving_l (x y z : P) : x ⊆ y → z ∪ x ⊆ z ∪ y;
  perm_union_reflecting_l (x y z : P) : z ⊥ x → z ⊥ y → z ∪ x ⊆ z ∪ y → x ⊆ y;
  perm_disjoint_difference (x y : P) : x ⊂ y → x ⊥ y ∖ x;
  perm_union_difference (x y : P) : x ⊂ y → x ∪ y ∖ x = y
}.

Class FracPermissions (P : Set) `{PermissionsOps P} `{Half P} : Prop := {
  frac_permissions :> Permissions P;
  perm_disjoint_half (x : P) : perm_kind x ≠ Locked → x.½ ⊥ x.½;
  perm_union_half (x : P) : x.½ ∪ x.½ = x
}.

(** * General properties of fractional permissions *)
(** We prove some derived properties for arbitrary permission implementations.
Many of these properties are just variants of the laws using commutativity of
[(∪)] and symmetry of [(⊥)]. *)
Section permissions.
Context `{Permissions P}.
Implicit Types x y z : P.

Lemma perm_fragment_alt x : perm_fragment x ↔ ∃ y, x ⊂ y.
Proof.
  split.
  * intros [y ?]. exists (x ∪ y). eauto using perm_union_subset_l.
  * intros [y ?]. exists (y ∖ x). eauto using perm_disjoint_difference.
Qed.

Lemma perm_disjoint_kind_l x y : x ⊥ y → perm_kind x = Read.
Proof. intros. apply perm_fragment_read. by exists y. Qed.
Lemma perm_disjoint_kind_r x y :  x ⊥ y → perm_kind y = Read.
Proof. intros. by apply perm_disjoint_kind_l with x. Qed.
Lemma perm_disjoint_locked_l x y :  x ⊥ y → perm_kind x ≠ Locked.
Proof. intros Hxy ?. apply perm_disjoint_kind_l in Hxy. congruence. Qed.
Lemma perm_disjoint_locked_r x y :  x ⊥ y → perm_kind y ≠ Locked.
Proof. intros Hxy ?. apply perm_disjoint_kind_r in Hxy. congruence. Qed.
Lemma perm_disjoint_write_l x y :  x ⊥ y → perm_kind x ≠ Write.
Proof. intros Hxy ?. apply perm_disjoint_kind_l in Hxy. congruence. Qed.
Lemma perm_disjoint_write_r x y :  x ⊥ y → perm_kind y ≠ Write.
Proof. intros Hxy ?. apply perm_disjoint_kind_r in Hxy. congruence. Qed.
Lemma perm_disjoint_free_l x y :  x ⊥ y → perm_kind x ≠ Free.
Proof. intros Hxy ?. apply perm_disjoint_kind_l in Hxy. congruence. Qed.
Lemma perm_disjoint_free_r x y :  x ⊥ y → perm_kind y ≠ Free.
Proof. intros Hxy ?. apply perm_disjoint_kind_r in Hxy. congruence. Qed.

Lemma perm_fragment_not_read x :  perm_kind x ≠ Read → ¬perm_fragment x.
Proof. intuition auto using perm_fragment_read. Qed.
Lemma perm_fragment_write x :  perm_kind x = Write → ¬perm_fragment x.
Proof. intros ? Hx. apply perm_fragment_read in Hx. congruence. Qed.
Lemma perm_fragment_free x :  perm_kind x = Free → ¬perm_fragment x.
Proof. intros ? Hx. apply perm_fragment_read in Hx. congruence. Qed.
Lemma perm_fragment_subseteq_write x : Write ⊆ perm_kind x → ¬perm_fragment x.
Proof.
  rewrite Write_subseteq.
  intros [?|?]; eauto using perm_fragment_write, perm_fragment_free.
Qed.
Lemma perm_fragment_locked x : perm_kind x = Locked → ¬perm_fragment x.
Proof. intros ? Hx. apply perm_fragment_read in Hx. congruence. Qed.

Lemma perm_disjoint_weaken_r x y y' : x ⊥ y → y' ⊆ y → x ⊥ y'.
Proof. rewrite !(symmetry_iff _ x). apply perm_disjoint_weaken_l. Qed.
Lemma perm_disjoint_weaken x x' y y' : x ⊥ y → x' ⊆ x → y' ⊆ y → x' ⊥ y'.
Proof. eauto using perm_disjoint_weaken_l, perm_disjoint_weaken_r. Qed.

Lemma perm_disjoint_union_lr x y z : x ∪ y ⊥ z → y ⊥ z.
Proof. rewrite (commutative_L (∪)). apply perm_disjoint_union_ll. Qed.
Lemma perm_disjoint_union_rl x y z : x ⊥ y ∪ z → x ⊥ y.
Proof. rewrite !(symmetry_iff _ x). apply perm_disjoint_union_ll. Qed.
Lemma perm_disjoint_union_rr x y z : x ⊥ y ∪ z → x ⊥ z.
Proof. rewrite (commutative_L (∪)). apply perm_disjoint_union_rl. Qed.

Lemma perm_disjoint_union_move_r x y z : x ⊥ y ∪ z → x ∪ y ⊥ z.
Proof.
  intros. symmetry. rewrite (commutative_L (∪)).
  apply perm_disjoint_union_move_l. by rewrite (commutative_L (∪)).
Qed.

Lemma perm_disjoint_union_l x y z : x ∪ y ⊥ z → x ⊥ y.
Proof. eauto using perm_disjoint_union_rl, perm_disjoint_union_move_l. Qed.
Lemma perm_disjoint_union_r x y z : x ⊥ y ∪ z → y ⊥ z.
Proof. eauto using perm_disjoint_union_lr, perm_disjoint_union_move_r. Qed.

Lemma perm_union_subset_r x y : y ⊥ x → x ⊂ y ∪ x.
Proof.
  rewrite (symmetry_iff _), (commutative_L (∪)). by apply perm_union_subset_l.
Qed.
Lemma perm_union_subseteq_l x y : x ⊥ y → x ⊆ x ∪ y.
Proof. intros. by apply subset_subseteq, perm_union_subset_l. Qed.
Lemma perm_union_subseteq_r x y : y ⊥ x → x ⊆ y ∪ x.
Proof. intros. by apply subset_subseteq, perm_union_subset_r. Qed.
Lemma perm_union_ne_l x y : x ⊥ y → x ≠ x ∪ y.
Proof.
  intros ? E. destruct (perm_union_subset_l x y) as [? []]; auto.
  by rewrite <-E.
Qed.
Lemma perm_union_ne_r x y : y ⊥ x → x ≠ y ∪ x.
Proof.
  intros ? E. destruct (perm_union_subset_r x y) as [? []]; auto.
  by rewrite <-E.
Qed.

Lemma perm_union_preserving_r x y z : x ⊆ y → x ∪ z ⊆ y ∪ z.
Proof. rewrite !(commutative_L (∪) _ z). apply perm_union_preserving_l. Qed.
Lemma perm_union_strict_preserving_l x y z :
  z ⊥ x → z ⊥ y → x ⊂ y → z ∪ x ⊂ z ∪ y.
Proof.
  intros ?? [Hxy1 Hxy2]. split.
  * auto using perm_union_preserving_l.
  * contradict Hxy2. by apply perm_union_reflecting_l with z.
Qed.
Lemma perm_union_strict_preserving_r x y z :
  x ⊥ z → y ⊥ z → x ⊂ y → x ∪ z ⊂ y ∪ z.
Proof.
  intros. rewrite !(commutative_L (∪) _ z).
  by apply perm_union_strict_preserving_l.
Qed.

Lemma perm_union_reflecting_r x y z : x ⊥ z → y ⊥ z → x ∪ z ⊆ y ∪ z → x ⊆ y.
Proof.
  intros ??. rewrite !(commutative_L (∪) _ z). by apply perm_union_reflecting_l.
Qed.
Lemma perm_union_strict_reflecting_l x y z :
  z ⊥ x → z ⊥ y → z ∪ x ⊂ z ∪ y → x ⊂ y.
Proof.
  intros ?? [Hxy1 Hxy2]. split.
  * eauto using perm_union_reflecting_l.
  * contradict Hxy2. by apply perm_union_preserving_l.
Qed.
Lemma perm_union_strict_reflecting_r x y z :
  x ⊥ z → y ⊥ z → x ∪ z ⊂ y ∪ z → x ⊂ y.
Proof.
  rewrite !(commutative_L (∪) _ z), !(symmetry_iff _ _ z).
  apply perm_union_strict_reflecting_l.
Qed.

Lemma perm_union_cancel_l x y z : z ⊥ x → z ⊥ y → z ∪ x = z ∪ y → x = y.
Proof.
  intros ?? E. by apply (anti_symmetric _);
    apply perm_union_reflecting_l with z; rewrite ?E.
Qed.
Lemma perm_union_cancel_r x y z : x ⊥ z → y ⊥ z → x ∪ z = y ∪ z → x = y.
Proof.
  intros ??. rewrite !(commutative_L (∪) _ z). by apply perm_union_cancel_l.
Qed.

Lemma perm_kind_union_l x y : x ⊥ y → perm_kind x ⊆ perm_kind (x ∪ y).
Proof. intros. by apply perm_kind_preserving, perm_union_subseteq_l. Qed.
Lemma perm_kind_union_r x y : x ⊥ y → perm_kind y ⊆ perm_kind (x ∪ y).
Proof. intros. by apply perm_kind_preserving, perm_union_subseteq_r. Qed.
Lemma perm_kind_union_locked x y : x ⊥ y → perm_kind (x ∪ y) ≠ Locked.
Proof.
  intros Hdisjoint Hxy. pose proof (perm_kind_union_l x y Hdisjoint) as Hxxy.
  rewrite (perm_disjoint_kind_l x y), Hxy in Hxxy by done. by inversion Hxxy.
Qed.

Lemma perm_unlock_union x y :
  x ⊥ y → perm_unlock (x ∪ y) = perm_unlock x ∪ perm_unlock y.
Proof.
  intros. by rewrite !perm_unlock_other by eauto using perm_kind_union_locked,
     perm_disjoint_locked_l, perm_disjoint_locked_r.
Qed.

Lemma perm_disjoint_unlock_l x y : x ⊥ y → perm_unlock x ⊥ y.
Proof.
  destruct (decide (perm_kind x = Locked)).
  * intros. by destruct (perm_disjoint_locked_l x y).
  * by rewrite perm_unlock_other.
Qed.
Lemma perm_disjoint_unlock_r x y : x ⊥ y → x ⊥ perm_unlock y.
Proof. intros. symmetry. by apply perm_disjoint_unlock_l. Qed.

Lemma perm_unlock_idempotent x : perm_unlock (perm_unlock x) = perm_unlock x.
Proof.
  rewrite (perm_unlock_other (perm_unlock x)); auto using perm_unlock_kind.
Qed.
End permissions.

Section frac_permissions.
Context `{FracPermissions P}.

Lemma perm_half_subseteq x : perm_kind x ≠ Locked → x.½ ⊆ x.
Proof.
  intros. rewrite <-(perm_union_half x) at 2.
  by apply perm_union_subseteq_l, perm_disjoint_half.
Qed.

Lemma perm_kind_half x : perm_kind x ≠ Locked → perm_kind (x.½) = Read.
Proof. intros. by eapply perm_disjoint_kind_l, perm_disjoint_half. Qed.
Lemma perm_kind_half_locked x : perm_kind x ≠ Locked → perm_kind (x.½) ≠ Locked.
Proof. intros Hx. apply perm_kind_half in Hx. congruence. Qed.
End frac_permissions.
