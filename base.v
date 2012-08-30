(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects type class interfaces, notations, and general theorems
that are used throughout the whole development. Most importantly it contains
abstract interfaces for ordered structures, collections, and various other data
structures. *)
Global Generalizable All Variables.
Global Set Automatic Coercions Import.
Require Export Morphisms RelationClasses List Bool Utf8 Program Setoid NArith.

(** * General *)
(** The following coercion allows us to use Booleans as propositions. *)
Coercion Is_true : bool >-> Sortclass.

(** Ensure that [simpl] unfolds [id] and [compose] when fully applied. *)
Arguments id _ _/.
Arguments compose _ _ _ _ _ _ /.

(** Change [True] and [False] into notations in order to enable overloading.
We will use this in the file [assertions] to give [True] and [False] a
different interpretation in [assert_scope] used for assertions of our axiomatic
semantics. *)
Notation "'True'" := True : type_scope.
Notation "'False'" := False : type_scope.

(** Throughout this development we use [C_scope] for all general purpose
notations that do not belong to a more specific scope. *)
Delimit Scope C_scope with C.
Global Open Scope C_scope.

(** Introduce some Haskell style like notations. *)
Notation "(=)" := eq (only parsing) : C_scope.
Notation "( x =)" := (eq x) (only parsing) : C_scope.
Notation "(= x )" := (λ y, eq y x) (only parsing) : C_scope.
Notation "(≠)" := (λ x y, x ≠ y) (only parsing) : C_scope.
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing) : C_scope.
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing) : C_scope.

Hint Extern 0 (?x = ?x) => reflexivity.

Notation "(→)" := (λ x y, x → y) (only parsing) : C_scope.
Notation "( T →)" := (λ y, T → y) (only parsing) : C_scope.
Notation "(→ T )" := (λ y, y → T) (only parsing) : C_scope.
Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing) : C_scope.
Infix "∘" := compose : C_scope.
Notation "(∘)" := compose (only parsing) : C_scope.
Notation "( f ∘)" := (compose f) (only parsing) : C_scope.
Notation "(∘ f )" := (λ g, compose g f) (only parsing) : C_scope.

(** Set convenient implicit arguments for [existT] and introduce notations. *)
Arguments existT {_ _} _ _.
Notation "x ↾ p" := (exist _ x p) (at level 20) : C_scope.
Notation "` x" := (proj1_sig x) : C_scope.

(** * Type classes *)
(** ** Provable propositions *)
(** This type class collects provable propositions. It is useful to constraint
type classes by arbitrary propositions. *)
Class PropHolds (P : Prop) := prop_holds: P.

Hint Extern 0 (PropHolds _) => assumption : typeclass_instances.
Instance: Proper (iff ==> iff) PropHolds.
Proof. now repeat intro. Qed.

Ltac solve_propholds :=
  match goal with
  | [ |- PropHolds (?P) ] => apply _
  | [ |- ?P ] => change (PropHolds P); apply _
  end.

(** ** Decidable propositions *)
(** This type class by (Spitters/van der Weegen, 2011) collects decidable
propositions. For example to declare a parameter expressing decidable equality
on a type [A] we write [`{∀ x y : A, Decision (x = y)}] and use it by writing
[decide (x = y)]. *)
Class Decision (P : Prop) := decide : {P} + {¬P}.
Arguments decide _ {_}.

(** ** Setoid equality *)
(** We define an operational type class for setoid equality. This is based on
(Spitters/van der Weegen, 2011). *)
Class Equiv A := equiv: relation A.
Infix "≡" := equiv (at level 70, no associativity) : C_scope.
Notation "(≡)" := equiv (only parsing) : C_scope.
Notation "( x ≡)" := (equiv x) (only parsing) : C_scope.
Notation "(≡ x )" := (λ y, y ≡ x) (only parsing) : C_scope.
Notation "(≢)" := (λ x y, ¬x ≡ y) (only parsing) : C_scope.
Notation "x ≢ y":= (¬x ≡ y) (at level 70, no associativity) : C_scope.
Notation "( x ≢)" := (λ y, x ≢ y) (only parsing) : C_scope.
Notation "(≢ x )" := (λ y, y ≢ x) (only parsing) : C_scope.

(** A [Params f n] instance forces the setoid rewriting mechanism not to
rewrite in the first [n] arguments of the function [f]. We will declare such
instances for all operational type classes in this development. *)
Instance: Params (@equiv) 2.

(** The following instance forces [setoid_replace] to use setoid equality
(for types that have an [Equiv] instance) rather than the standard Leibniz
equality. *)
Instance equiv_default_relation `{Equiv A} : DefaultRelation (≡) | 3.
Hint Extern 0 (?x ≡ ?x) => reflexivity.

(** ** Operations on collections *)
(** We define operational type classes for the standard operations and
relations on collections: the empty collection [∅], the union [(∪)],
intersection [(∩)], difference [(∖)], and the singleton [{[_]}]
operation, and the subset [(⊆)] and element of [(∈)] relation. *)
Class Empty A := empty: A.
Notation "∅" := empty : C_scope.

Class Union A := union: A → A → A.
Instance: Params (@union) 2.
Infix "∪" := union (at level 50, left associativity) : C_scope.
Notation "(∪)" := union (only parsing) : C_scope.
Notation "( x ∪)" := (union x) (only parsing) : C_scope.
Notation "(∪ x )" := (λ y, union y x) (only parsing) : C_scope.

Class Intersection A := intersection: A → A → A.
Instance: Params (@intersection) 2.
Infix "∩" := intersection (at level 40) : C_scope.
Notation "(∩)" := intersection (only parsing) : C_scope.
Notation "( x ∩)" := (intersection x) (only parsing) : C_scope.
Notation "(∩ x )" := (λ y, intersection y x) (only parsing) : C_scope.

Class Difference A := difference: A → A → A.
Instance: Params (@difference) 2.
Infix "∖" := difference (at level 40) : C_scope.
Notation "(∖)" := difference (only parsing) : C_scope.
Notation "( x ∖)" := (difference x) (only parsing) : C_scope.
Notation "(∖ x )" := (λ y, difference y x) (only parsing) : C_scope.

Class Singleton A B := singleton: A → B.
Instance: Params (@singleton) 3.
Notation "{[ x ]}" := (singleton x) : C_scope.
Notation "{[ x ; y ; .. ; z ]}" :=
  (union .. (union (singleton x) (singleton y)) .. (singleton z)) : C_scope.

Class SubsetEq A := subseteq: A → A → Prop.
Instance: Params (@subseteq) 2.
Infix "⊆" := subseteq (at level 70) : C_scope.
Notation "(⊆)" := subseteq (only parsing) : C_scope.
Notation "( X ⊆ )" := (subseteq X) (only parsing) : C_scope.
Notation "( ⊆ X )" := (λ Y, subseteq Y X) (only parsing) : C_scope.
Notation "X ⊈ Y" := (¬X ⊆ Y) (at level 70) : C_scope.
Notation "(⊈)" := (λ X Y, X ⊈ Y) (only parsing) : C_scope.
Notation "( X ⊈ )" := (λ Y, X ⊈ Y) (only parsing) : C_scope.
Notation "( ⊈ X )" := (λ Y, Y ⊈ X) (only parsing) : C_scope.

Hint Extern 0 (?x ⊆ ?x) => reflexivity.

Class ElemOf A B := elem_of: A → B → Prop.
Instance: Params (@elem_of) 3.
Infix "∈" := elem_of (at level 70) : C_scope.
Notation "(∈)" := elem_of (only parsing) : C_scope.
Notation "( x ∈)" := (elem_of x) (only parsing) : C_scope.
Notation "(∈ X )" := (λ x, elem_of x X) (only parsing) : C_scope.
Notation "x ∉ X" := (¬x ∈ X) (at level 80) : C_scope.
Notation "(∉)" := (λ x X, x ∉ X) (only parsing) : C_scope.
Notation "( x ∉)" := (λ X, x ∉ X) (only parsing) : C_scope.
Notation "(∉ X )" := (λ x, x ∉ X) (only parsing) : C_scope.

(** ** Operations on maps *)
(** In this file we will only define operational type classes for the
operations on maps. In the file [fin_maps] we will axiomatize finite maps.
The function lookup [m !! k] should yield the element at key [k] in [m]. *)
Class Lookup K M := lookup: ∀ {A}, K → M A → option A.
Instance: Params (@lookup) 4.

Notation "m !! i" := (lookup i m) (at level 20) : C_scope.
Notation "(!!)" := lookup (only parsing) : C_scope.
Notation "( m !!)" := (λ i, lookup i m) (only parsing) : C_scope.
Notation "(!! i )" := (lookup i) (only parsing) : C_scope.

(** The function insert [<[k:=a]>m] should update the element at key [k] with
value [a] in [m]. *)
Class Insert K M :=
  insert: ∀ {A}, K → A → M A → M A.
Instance: Params (@insert) 4.
Notation "<[ k := a ]>" := (insert k a)
  (at level 5, right associativity, format "<[ k := a ]>") : C_scope.

(** The function delete [delete k m] should deletes the value at key [k] in
[m]. *)
Class Delete K M :=
  delete: K → M → M.
Instance: Params (@delete) 3.

(** The function [alter f k m] should update the value at key [k] using the
function [f], which is called with the original value at key [k]. When [k] is
not a member of [m], the original map should be returned. *)
Class Alter K M :=
  alter: ∀ {A}, (A → A) → K → M A → M A.
Instance: Params (@alter) 4.

(** The function [alter f k m] should update the value at key [k] using the
function [f], which is called with the original value at key [k] or [None] if
[k] is not a member of [m]. The value at [k] should be deleted if [f] yields
[None]. *)
Class PartialAlter K M :=
  partial_alter: ∀ {A}, (option A → option A) → K → M A → M A.
Instance: Params (@partial_alter) 4.

(** The function [dom C m] should yield the domain of [m]. That is a finite
collection of type [C] that contains the keys that are a member of [m]. *)
Class Dom K M :=
  dom: ∀ C `{Empty C} `{Union C} `{Singleton K C}, M → C.
Instance: Params (@dom) 7.

(** The function [merge f m1 m2] should merge the maps [m1] and [m2] by
constructing a new map whose value at key [k] is [f (m1 !! k) (m2 !! k)]
provided that [k] is a member of either [m1] or [m2].*)
Class Merge M :=
  merge: ∀ {A}, (option A → option A → option A) → M A → M A → M A.
Instance: Params (@merge) 3.

(** We lift the insert and delete operation to lists of elements. *)
Definition insert_list `{Insert K M} {A} (l : list (K * A)) (m : M A) : M A :=
  fold_right (λ p, <[ fst p := snd p ]>) m l.
Instance: Params (@insert_list) 4.
Definition delete_list `{Delete K M} (l : list K) (m : M) : M :=
  fold_right delete m l.
Instance: Params (@delete_list) 3.

(** The function [union_with f m1 m2] should yield the union of [m1] and [m2]
using the function [f] to combine values of members that are in both [m1] and
[m2]. *)
Class UnionWith M :=
  union_with: ∀ {A}, (A → A → A) → M A → M A → M A.
Instance: Params (@union_with) 3.

(** Similarly for the intersection and difference. *)
Class IntersectionWith M :=
  intersection_with: ∀ {A}, (A → A → A) → M A → M A → M A.
Instance: Params (@intersection_with) 3.
Class DifferenceWith M :=
  difference_with: ∀ {A}, (A → A → option A) → M A → M A → M A.
Instance: Params (@difference_with) 3.

(** ** Common properties *)
(** These operational type classes allow us to refer to common mathematical
properties in a generic way. For example, for injectivity of [(k ++)] it
allows us to write [injective (k ++)] instead of [app_inv_head k]. *)
Class Injective {A B} R S (f : A → B) :=
  injective: ∀ x y : A, S (f x) (f y) → R x y.
Class Idempotent {A} R (f : A → A → A) :=
  idempotent: ∀ x, R (f x x) x.
Class Commutative {A B} R (f : B → B → A) :=
  commutative: ∀ x y, R (f x y) (f y x).
Class LeftId {A} R (i : A) (f : A → A → A) :=
  left_id: ∀ x, R (f i x) x.
Class RightId {A} R (i : A) (f : A → A → A) :=
  right_id: ∀ x, R (f x i) x.
Class Associative {A} R (f : A → A → A) :=
  associative: ∀ x y z, R (f x (f y z)) (f (f x y) z).

Arguments injective {_ _ _ _} _ {_} _ _ _.
Arguments idempotent {_ _} _ {_} _.
Arguments commutative {_ _ _} _ {_} _ _.
Arguments left_id {_ _} _ _ {_} _.
Arguments right_id {_ _} _ _ {_} _.
Arguments associative {_ _} _ {_} _ _ _.

(** The following lemmas are more specific versions of the projections of the
above type classes. These lemmas allow us to enforce Coq not to use the setoid
rewriting mechanism. *)
Lemma idempotent_eq {A} (f : A → A → A) `{!Idempotent (=) f} x :
  f x x = x.
Proof. auto. Qed.
Lemma commutative_eq {A B} (f : B → B → A) `{!Commutative (=) f} x y :
  f x y = f y x.
Proof. auto. Qed.
Lemma left_id_eq {A} (i : A) (f : A → A → A) `{!LeftId (=) i f} x :
  f i x = x.
Proof. auto. Qed.
Lemma right_id_eq {A} (i : A) (f : A → A → A) `{!RightId (=) i f} x :
  f x i = x.
Proof. auto. Qed.
Lemma associative_eq {A} (f : A → A → A) `{!Associative (=) f} x y z :
  f x (f y z) = f (f x y) z.
Proof. auto. Qed.

(** ** Monadic operations *)
(** We do use the operation type classes for monads merely for convenient
overloading of notations and do not formalize any theory on monads (we do not
define a class with the monad laws). *)
Section monad_ops.
  Context (M : Type → Type).

  Class MRet := mret: ∀ {A}, A → M A.
  Class MBind := mbind: ∀ {A B}, (A → M B) → M A → M B.
  Class MJoin := mjoin: ∀ {A}, M (M A) → M A.
  Class FMap := fmap: ∀ {A B}, (A → B) → M A → M B.
End monad_ops.

Instance: Params (@mret) 3.
Arguments mret {M MRet A} _.
Instance: Params (@mbind) 4.
Arguments mbind {M MBind A B} _ _.
Instance: Params (@mjoin) 3.
Arguments mjoin {M MJoin A} _.
Instance: Params (@fmap) 4.
Arguments fmap {M FMap A B} _ _.

Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : C_scope.
Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 65, next at level 35, right associativity) : C_scope.
Infix "<$>" := fmap (at level 65, right associativity, only parsing) : C_scope.

(** ** Axiomatization of ordered structures *)
(** A pre-order equiped with a smallest element. *)
Class BoundedPreOrder A `{Empty A} `{SubsetEq A} := {
  bounded_preorder :>> PreOrder (⊆);
  subseteq_empty x : ∅ ⊆ x
}.

(** We do not include equality in the following interfaces so as to avoid the
need for proofs that the  relations and operations respect setoid equality.
Instead, we will define setoid equality in a generic way as
[λ X Y, X ⊆ Y ∧ Y ⊆ X]. *)
Class BoundedJoinSemiLattice A `{Empty A} `{SubsetEq A} `{Union A} := {
  jsl_preorder :>> BoundedPreOrder A;
  subseteq_union_l x y : x ⊆ x ∪ y;
  subseteq_union_r x y : y ⊆ x ∪ y;
  union_least x y z : x ⊆ z → y ⊆ z → x ∪ y ⊆ z
}.
Class MeetSemiLattice A `{Empty A} `{SubsetEq A} `{Intersection A} := {
  msl_preorder :>> BoundedPreOrder A;
  subseteq_intersection_l x y : x ∩ y ⊆ x;
  subseteq_intersection_r x y : x ∩ y ⊆ y;
  intersection_greatest x y z : z ⊆ x → z ⊆ y → z ⊆ x ∩ y
}.

(** ** Axiomatization of collections *)
(** The class [Collection A C] axiomatizes a collection of type [C] with
elements of type [A]. Since [C] is not dependent on [A], we use the monomorphic
[Map] type class instead of the polymorphic [FMap]. *)
Class Map A C := map: (A → A) → (C → C).
Instance: Params (@map) 3.
Class Collection A C `{ElemOf A C} `{Empty C} `{Union C}
    `{Intersection C} `{Difference C} `{Singleton A C} `{Map A C} := {
  not_elem_of_empty (x : A) : x ∉ ∅;
  elem_of_singleton (x y : A) : x ∈ {[ y ]} ↔ x = y;
  elem_of_union X Y (x : A) : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y;
  elem_of_intersection X Y (x : A) : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y;
  elem_of_difference X Y (x : A) : x ∈ X ∖ Y ↔ x ∈ X ∧ x ∉ Y;
  elem_of_map f X (x : A) : x ∈ map f X ↔ ∃ y, x = f y ∧ y ∈ X
}.

(** We axiomative a finite collection as a collection whose elements can be
enumerated as a list. These elements, given by the [elements] function, may be
in any order and should not contain duplicates. *)
Class Elements A C := elements: C → list A.
Instance: Params (@elements) 3.
Class FinCollection A C `{Empty C} `{Union C} `{Intersection C} `{Difference C}
    `{Singleton A C} `{ElemOf A C} `{Map A C} `{Elements A C} := {
  fin_collection :>> Collection A C;
  elements_spec X x : x ∈ X ↔ In x (elements X);
  elements_nodup X : NoDup (elements X)
}.
Class Size C := size: C → nat.
Instance: Params (@size) 2.

(** The function [fresh X] yields an element that is not contained in [X]. We
will later prove that [fresh] is [Proper] with respect to the induced setoid
equality on collections. *)
Class Fresh A C := fresh: C → A.
Instance: Params (@fresh) 3.
Class FreshSpec A C `{!Fresh A C} `{!ElemOf A C} := {
  fresh_proper_alt X Y : (∀ x, x ∈ X ↔ x ∈ Y) → fresh X = fresh Y;
  is_fresh (X : C) : fresh X ∉ X
}.

(** * Miscellaneous *)
Lemma proj1_sig_inj {A} (P : A → Prop) x (Px : P x) y (Py : P y) :
  x↾Px = y↾Py → x = y.
Proof. now injection 1. Qed.

Lemma symmetry_iff `(R : relation A) `{!Symmetric R} (x y : A) :
  R x y ↔ R y x.
Proof. intuition. Qed.

(** ** Pointwise relations *)
(** These instances are in Coq trunk since revision 15455, but are not in Coq
8.4 yet. *)
Instance pointwise_reflexive {A} `{R : relation B} :
  Reflexive R → Reflexive (pointwise_relation A R) | 9.
Proof. firstorder. Qed.
Instance pointwise_symmetric {A} `{R : relation B} :
  Symmetric R → Symmetric (pointwise_relation A R) | 9.
Proof. firstorder. Qed.
Instance pointwise_transitive {A} `{R : relation B} :
  Transitive R → Transitive (pointwise_relation A R) | 9.
Proof. firstorder. Qed.

(** ** Products *)
Definition fst_map {A A' B} (f : A → A') (p : A * B) : A' * B :=
  (f (fst p), snd p).
Definition snd_map {A B B'} (f : B → B') (p : A * B) : A * B' :=
  (fst p, f (snd p)).
Definition prod_relation {A B} (R1 : relation A) (R2 : relation B) :
  relation (A * B) := λ x y, R1 (fst x) (fst y) ∧ R2 (snd x) (snd y).

Section prod_relation.
  Context `{R1 : relation A} `{R2 : relation B}.
  Global Instance:
    Reflexive R1 → Reflexive R2 → Reflexive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance:
    Symmetric R1 → Symmetric R2 → Symmetric (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance:
    Transitive R1 → Transitive R2 → Transitive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance:
    Equivalence R1 → Equivalence R2 → Equivalence (prod_relation R1 R2).
  Proof. split; apply _. Qed.
  Global Instance: Proper (R1 ==> R2 ==> prod_relation R1 R2) pair.
  Proof. firstorder eauto. Qed.
  Global Instance: Proper (prod_relation R1 R2 ==> R1) fst.
  Proof. firstorder eauto. Qed.
  Global Instance: Proper (prod_relation R1 R2 ==> R2) snd.
  Proof. firstorder eauto. Qed.
End prod_relation.

(** ** Other *)
Definition lift_relation {A B} (R : relation A)
  (f : B → A) : relation B := λ x y, R (f x) (f y).
Definition lift_relation_equivalence {A B} (R : relation A) (f : B → A) :
  Equivalence R → Equivalence (lift_relation R f).
Proof. unfold lift_relation. firstorder. Qed.
Hint Extern 0 (Equivalence (lift_relation _ _)) =>
  eapply @lift_relation_equivalence : typeclass_instances.

Instance: ∀ A B (x : B), Commutative (=) (λ _ _ : A, x).
Proof. easy. Qed.
Instance: ∀ A (x : A), Associative (=) (λ _ _ : A, x).
Proof. easy. Qed.
Instance: ∀ A, Associative (=) (λ x _ : A, x).
Proof. easy. Qed.
Instance: ∀ A, Associative (=) (λ _ x : A, x).
Proof. easy. Qed.
Instance: ∀ A, Idempotent (=) (λ x _ : A, x).
Proof. easy. Qed.
Instance: ∀ A, Idempotent (=) (λ _ x : A, x).
Proof. easy. Qed.

Instance left_id_propholds {A} (R : relation A) i f :
  LeftId R i f → ∀ x, PropHolds (R (f i x) x).
Proof. easy. Qed.
Instance right_id_propholds {A} (R : relation A) i f :
  RightId R i f → ∀ x, PropHolds (R (f x i) x).
Proof. easy. Qed.
Instance idem_propholds {A} (R : relation A) f :
  Idempotent R f → ∀ x, PropHolds (R (f x x) x).
Proof. easy. Qed.
