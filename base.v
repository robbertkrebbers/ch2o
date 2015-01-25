(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects type class interfaces, notations, and general theorems
that are used throughout the whole development. Most importantly it contains
abstract interfaces for ordered structures, collections, and various other data
structures. *)
Global Generalizable All Variables.
Global Set Automatic Coercions Import.
Require Export Morphisms RelationClasses List Bool Utf8 Program Setoid.

(** * General *)
(** Zipping lists. *)
Definition zip_with {A B C} (f : A → B → C) : list A → list B → list C :=
  fix go l1 l2 :=
  match l1, l2 with x1 :: l1, x2 :: l2 => f x1 x2 :: go l1 l2 | _ , _ => [] end.
Notation zip := (zip_with pair).

(** Ensure that [simpl] unfolds [id], [compose], and [flip] when fully
applied. *)
Arguments id _ _ /.
Arguments compose _ _ _ _ _ _ /.
Arguments flip _ _ _ _ _ _ /.
Arguments const _ _ _ _ /.
Typeclasses Transparent id compose flip const.

(** Change [True] and [False] into notations in order to enable overloading.
We will use this in the file [assertions] to give [True] and [False] a
different interpretation in [assert_scope] used for assertions of our axiomatic
semantics. *)
Notation "'True'" := True : type_scope.
Notation "'False'" := False : type_scope.

Notation curry := prod_curry.
Notation uncurry := prod_uncurry.
Definition curry3 {A B C D} (f : A → B → C → D) (p : A * B * C) : D :=
  let '(a,b,c) := p in f a b c.
Definition curry4 {A B C D E} (f : A → B → C → D → E) (p : A * B * C * D) : E :=
  let '(a,b,c,d) := p in f a b c d.

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
Hint Extern 100 (_ ≠ _) => discriminate.

Notation "(→)" := (λ A B, A → B) (only parsing) : C_scope.
Notation "( A →)" := (λ B, A → B) (only parsing) : C_scope.
Notation "(→ B )" := (λ A, A → B) (only parsing) : C_scope.

Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing) : C_scope.
Notation "($)" := (λ f x, f x) (only parsing) : C_scope.
Notation "($ x )" := (λ f, f x) (only parsing) : C_scope.

Infix "∘" := compose : C_scope.
Notation "(∘)" := compose (only parsing) : C_scope.
Notation "( f ∘)" := (compose f) (only parsing) : C_scope.
Notation "(∘ f )" := (λ g, compose g f) (only parsing) : C_scope.

Notation "(∧)" := and (only parsing) : C_scope.
Notation "( A ∧)" := (and A) (only parsing) : C_scope.
Notation "(∧ B )" := (λ A, A ∧ B) (only parsing) : C_scope.

Notation "(∨)" := or (only parsing) : C_scope.
Notation "( A ∨)" := (or A) (only parsing) : C_scope.
Notation "(∨ B )" := (λ A, A ∨ B) (only parsing) : C_scope.

Notation "(↔)" := iff (only parsing) : C_scope.
Notation "( A ↔)" := (iff A) (only parsing) : C_scope.
Notation "(↔ B )" := (λ A, A ↔ B) (only parsing) : C_scope.

Hint Extern 0 (_ ↔ _) => reflexivity.
Hint Extern 0 (_ ↔ _) => symmetry; assumption.

Notation "( x ,)" := (pair x) (only parsing) : C_scope.
Notation "(, y )" := (λ x, (x,y)) (only parsing) : C_scope.

Notation "p .1" := (fst p) (at level 10, format "p .1").
Notation "p .2" := (snd p) (at level 10, format "p .2").

Definition prod_map {A A' B B'} (f : A → A') (g : B → B')
  (p : A * B) : A' * B' := (f (p.1), g (p.2)).
Arguments prod_map {_ _ _ _} _ _ !_ /.
Definition prod_zip {A A' A'' B B' B''} (f : A → A' → A'') (g : B → B' → B'')
    (p : A * B) (q : A' * B') : A'' * B'' := (f (p.1) (q.1), g (p.2) (q.2)).
Arguments prod_zip {_ _ _ _ _ _} _ _ !_ !_ /.

(** Set convenient implicit arguments for [existT] and introduce notations. *)
Arguments existT {_ _} _ _.
Arguments proj1_sig {_ _} _.
Notation "x ↾ p" := (exist _ x p) (at level 20) : C_scope.
Notation "` x" := (proj1_sig x) (at level 10, format "` x") : C_scope.

(** * Type classes *)
(** ** Provable propositions *)
(** This type class collects provable propositions. It is useful to constraint
type classes by arbitrary propositions. *)
Class PropHolds (P : Prop) := prop_holds: P.

Hint Extern 0 (PropHolds _) => assumption : typeclass_instances.
Instance: Proper (iff ==> iff) PropHolds.
Proof. repeat intro; trivial. Qed.

Ltac solve_propholds :=
  match goal with
  | |- PropHolds (?P) => apply _
  | |- ?P => change (PropHolds P); apply _
  end.

(** ** Decidable propositions *)
(** This type class by (Spitters/van der Weegen, 2011) collects decidable
propositions. For example to declare a parameter expressing decidable equality
on a type [A] we write [`{∀ x y : A, Decision (x = y)}] and use it by writing
[decide (x = y)]. *)
Class Decision (P : Prop) := decide : {P} + {¬P}.
Arguments decide _ {_}.

(** ** Inhabited types *)
(** This type class collects types that are inhabited. *)
Class Inhabited (A : Type) : Prop := populate { _ : A }.
Arguments populate {_} _.

Instance unit_inhabited: Inhabited unit := populate ().
Instance list_inhabited {A} : Inhabited (list A) := populate [].
Instance prod_inhabited {A B} (iA : Inhabited A)
    (iB : Inhabited B) : Inhabited (A * B) :=
  match iA, iB with populate x, populate y => populate (x,y) end.
Instance sum_inhabited_l {A B} (iA : Inhabited A) : Inhabited (A + B) :=
  match iA with populate x => populate (inl x) end.
Instance sum_inhabited_r {A B} (iB : Inhabited A) : Inhabited (A + B) :=
  match iB with populate y => populate (inl y) end.
Instance option_inhabited {A} : Inhabited (option A) := populate None.

(** ** Proof irrelevant types *)
(** This type class collects types that are proof irrelevant. That means, all
elements of the type are equal. We use this notion only used for propositions,
but by universe polymorphism we can generalize it. *)
Class ProofIrrel (A : Type) : Prop := proof_irrel (x y : A) : x = y.

(** ** Setoid equality *)
(** We define an operational type class for setoid equality. This is based on
(Spitters/van der Weegen, 2011). *)
Class Equiv A := equiv: relation A.
Infix "≡" := equiv (at level 70, no associativity) : C_scope.
Notation "(≡)" := equiv (only parsing) : C_scope.
Notation "( X ≡)" := (equiv X) (only parsing) : C_scope.
Notation "(≡ X )" := (λ Y, Y ≡ X) (only parsing) : C_scope.
Notation "(≢)" := (λ X Y, ¬X ≡ Y) (only parsing) : C_scope.
Notation "X ≢ Y":= (¬X ≡ Y) (at level 70, no associativity) : C_scope.
Notation "( X ≢)" := (λ Y, X ≢ Y) (only parsing) : C_scope.
Notation "(≢ X )" := (λ Y, Y ≢ X) (only parsing) : C_scope.

(** The type class [LeibnizEquiv] collects setoid equalities that coincide
with Leibniz equality. We provide the tactic [fold_leibniz] to transform such
setoid equalities into Leibniz equalities, and [unfold_leibniz] for the
reverse. *)
Class LeibnizEquiv A `{Equiv A} := leibniz_equiv x y : x ≡ y ↔ x = y.

Ltac fold_leibniz := repeat
  match goal with
  | H : context [ @equiv ?A _ _ _ ] |- _ =>
    setoid_rewrite (leibniz_equiv (A:=A)) in H
  | |- context [ @equiv ?A _ _ _ ] =>
    setoid_rewrite (leibniz_equiv (A:=A))
  end.
Ltac unfold_leibniz := repeat
  match goal with
  | H : context [ @eq ?A _ _ ] |- _ =>
    setoid_rewrite <-(leibniz_equiv (A:=A)) in H
  | |- context [ @eq ?A _ _ ] =>
    setoid_rewrite <-(leibniz_equiv (A:=A))
  end.

(** A [Params f n] instance forces the setoid rewriting mechanism not to
rewrite in the first [n] arguments of the function [f]. We will declare such
instances for all operational type classes in this development. *)
Instance: Params (@equiv) 2.

(** The following instance forces [setoid_replace] to use setoid equality
(for types that have an [Equiv] instance) rather than the standard Leibniz
equality. *)
Instance equiv_default_relation `{Equiv A} : DefaultRelation (≡) | 3.
Hint Extern 0 (_ ≡ _) => reflexivity.
Hint Extern 0 (_ ≡ _) => symmetry; assumption.

(** ** Operations on collections *)
(** We define operational type classes for the traditional operations and
relations on collections: the empty collection [∅], the union [(∪)],
intersection [(∩)], and difference [(∖)], the singleton [{[_]}], the subset
[(⊆)] and element of [(∈)] relation, and disjointess [(⊥)]. *)
Class Empty A := empty: A.
Notation "∅" := empty : C_scope.

Class Union A := union: A → A → A.
Instance: Params (@union) 2.
Infix "∪" := union (at level 50, left associativity) : C_scope.
Notation "(∪)" := union (only parsing) : C_scope.
Notation "( x ∪)" := (union x) (only parsing) : C_scope.
Notation "(∪ x )" := (λ y, union y x) (only parsing) : C_scope.
Infix "∪*" := (zip_with (∪)) (at level 50, left associativity) : C_scope.
Notation "(∪*)" := (zip_with (∪)) (only parsing) : C_scope.
Infix "∪**" := (zip_with (zip_with (∪)))
  (at level 50, left associativity) : C_scope.
Infix "∪*∪**" := (zip_with (prod_zip (∪) (∪*)))
  (at level 50, left associativity) : C_scope.

Definition union_list `{Empty A} `{Union A} : list A → A := fold_right (∪) ∅.
Arguments union_list _ _ _ !_ /.
Notation "⋃ l" := (union_list l) (at level 20, format "⋃  l") : C_scope.

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
Infix "∖*" := (zip_with (∖)) (at level 40, left associativity) : C_scope.
Notation "(∖*)" := (zip_with (∖)) (only parsing) : C_scope.
Infix "∖**" := (zip_with (zip_with (∖)))
  (at level 40, left associativity) : C_scope.
Infix "∖*∖**" := (zip_with (prod_zip (∖) (∖*)))
  (at level 50, left associativity) : C_scope.

Class Singleton A B := singleton: A → B.
Instance: Params (@singleton) 3.
Notation "{[ x ]}" := (singleton x) (at level 1) : C_scope.
Notation "{[ x ; y ; .. ; z ]}" :=
  (union .. (union (singleton x) (singleton y)) .. (singleton z))
  (at level 1) : C_scope.
Notation "{[ x , y ]}" := (singleton (x,y))
  (at level 1, y at next level) : C_scope.
Notation "{[ x , y , z ]}" := (singleton (x,y,z))
  (at level 1, y at next level, z at next level) : C_scope.

Class SubsetEq A := subseteq: relation A.
Instance: Params (@subseteq) 2.
Infix "⊆" := subseteq (at level 70) : C_scope.
Notation "(⊆)" := subseteq (only parsing) : C_scope.
Notation "( X ⊆ )" := (subseteq X) (only parsing) : C_scope.
Notation "( ⊆ X )" := (λ Y, Y ⊆ X) (only parsing) : C_scope.
Notation "X ⊈ Y" := (¬X ⊆ Y) (at level 70) : C_scope.
Notation "(⊈)" := (λ X Y, X ⊈ Y) (only parsing) : C_scope.
Notation "( X ⊈ )" := (λ Y, X ⊈ Y) (only parsing) : C_scope.
Notation "( ⊈ X )" := (λ Y, Y ⊈ X) (only parsing) : C_scope.
Infix "⊆*" := (Forall2 (⊆)) (at level 70) : C_scope.
Notation "(⊆*)" := (Forall2 (⊆)) (only parsing) : C_scope.
Infix "⊆**" := (Forall2 (⊆*)) (at level 70) : C_scope.
Infix "⊆1*" := (Forall2 (λ p q, p.1 ⊆ q.1)) (at level 70) : C_scope.
Infix "⊆2*" := (Forall2 (λ p q, p.2 ⊆ q.2)) (at level 70) : C_scope.
Infix "⊆1**" := (Forall2 (λ p q, p.1 ⊆* q.1)) (at level 70) : C_scope.
Infix "⊆2**" := (Forall2 (λ p q, p.2 ⊆* q.2)) (at level 70) : C_scope.

Hint Extern 0 (_ ⊆ _) => reflexivity.
Hint Extern 0 (_ ⊆* _) => reflexivity.
Hint Extern 0 (_ ⊆** _) => reflexivity.

Class SubsetEqE E A := subseteqE: E → relation A.
Instance: Params (@subseteqE) 4.
Notation "X ⊆{ Γ } Y" := (subseteqE Γ X Y)
  (at level 70, format "X  ⊆{ Γ }  Y") : C_scope.
Notation "(⊆{ Γ } )" := (subseteqE Γ) (only parsing, Γ at level 1) : C_scope.
Notation "X ⊈{ Γ } Y" := (¬X ⊆{Γ} Y)
  (at level 70, format "X  ⊈{ Γ }  Y") : C_scope.
Notation "(⊈{ Γ } )" := (λ X Y, X ⊈{Γ} Y)
  (only parsing, Γ at level 1) : C_scope.
Notation "Xs ⊆{ Γ }* Ys" := (Forall2 (⊆{Γ}) Xs Ys)
  (at level 70, format "Xs  ⊆{ Γ }*  Ys") : C_scope.
Notation "(⊆{ Γ }* )" := (Forall2 (⊆{Γ}))
  (only parsing, Γ at level 1) : C_scope.
Notation "X ⊆{ Γ1 , Γ2 , .. , Γ3 } Y" :=
  (subseteqE (pair .. (Γ1, Γ2) .. Γ3) X Y)
  (at level 70, format "'[' X  ⊆{ Γ1 , Γ2 , .. , Γ3 }  '/' Y ']'") : C_scope.
Notation "(⊆{ Γ1 , Γ2 , .. , Γ3 } )" := (subseteqE (pair .. (Γ1, Γ2) .. Γ3))
  (only parsing, Γ1 at level 1) : C_scope.
Notation "X ⊈{ Γ1 , Γ2 , .. , Γ3 } Y" := (¬X ⊆{pair .. (Γ1, Γ2) .. Γ3} Y)
  (at level 70, format "X  ⊈{ Γ1 , Γ2 , .. , Γ3 }  Y") : C_scope.
Notation "(⊈{ Γ1 , Γ2 , .. , Γ3 } )" := (λ X Y, X ⊈{pair .. (Γ1, Γ2) .. Γ3} Y)
  (only parsing) : C_scope.
Notation "Xs ⊆{ Γ1 , Γ2 , .. , Γ3 }* Ys" :=
  (Forall2 (⊆{pair .. (Γ1, Γ2) .. Γ3}) Xs Ys)
  (at level 70, format "Xs  ⊆{ Γ1 , Γ2 , .. , Γ3 }*  Ys") : C_scope.
Notation "(⊆{ Γ1 , Γ2 , .. , Γ3 }* )" := (Forall2 (⊆{pair .. (Γ1, Γ2) .. Γ3}))
  (only parsing, Γ1 at level 1) : C_scope.
Hint Extern 0 (_ ⊆{_} _) => reflexivity.

Definition strict {A} (R : relation A) : relation A := λ X Y, R X Y ∧ ¬R Y X.
Instance: Params (@strict) 2.
Infix "⊂" := (strict (⊆)) (at level 70) : C_scope.
Notation "(⊂)" := (strict (⊆)) (only parsing) : C_scope.
Notation "( X ⊂ )" := (strict (⊆) X) (only parsing) : C_scope.
Notation "( ⊂ X )" := (λ Y, Y ⊂ X) (only parsing) : C_scope.
Notation "X ⊄  Y" := (¬X ⊂ Y) (at level 70) : C_scope.
Notation "(⊄)" := (λ X Y, X ⊄ Y) (only parsing) : C_scope.
Notation "( X ⊄ )" := (λ Y, X ⊄ Y) (only parsing) : C_scope.
Notation "( ⊄ X )" := (λ Y, Y ⊄ X) (only parsing) : C_scope.

(** The class [Lexico A] is used for the lexicographic order on [A]. This order
is used to create finite maps, finite sets, etc, and is typically different from
the order [(⊆)]. *)
Class Lexico A := lexico: relation A.

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

Class Disjoint A := disjoint : A → A → Prop.
Instance: Params (@disjoint) 2.
Infix "⊥" := disjoint (at level 70) : C_scope.
Notation "(⊥)" := disjoint (only parsing) : C_scope.
Notation "( X ⊥.)" := (disjoint X) (only parsing) : C_scope.
Notation "(.⊥ X )" := (λ Y, Y ⊥  X) (only parsing) : C_scope.
Infix "⊥*" := (Forall2 (⊥)) (at level 70) : C_scope.
Notation "(⊥*)" := (Forall2 (⊥)) (only parsing) : C_scope.
Infix "⊥**" := (Forall2 (⊥*)) (at level 70) : C_scope.
Infix "⊥1*" := (Forall2 (λ p q, p.1 ⊥ q.1)) (at level 70) : C_scope.
Infix "⊥2*" := (Forall2 (λ p q, p.2 ⊥ q.2)) (at level 70) : C_scope.
Infix "⊥1**" := (Forall2 (λ p q, p.1 ⊥* q.1)) (at level 70) : C_scope.
Infix "⊥2**" := (Forall2 (λ p q, p.2 ⊥* q.2)) (at level 70) : C_scope.
Hint Extern 0 (_ ⊥ _) => symmetry; eassumption.
Hint Extern 0 (_ ⊥* _) => symmetry; eassumption.

Class DisjointE E A := disjointE : E → A → A → Prop.
Instance: Params (@disjointE) 4.
Notation "X ⊥{ Γ } Y" := (disjointE Γ X Y)
  (at level 70, format "X  ⊥{ Γ }  Y") : C_scope.
Notation "(⊥{ Γ } )" := (disjointE Γ) (only parsing, Γ at level 1) : C_scope.
Notation "Xs ⊥{ Γ }* Ys" := (Forall2 (⊥{Γ}) Xs Ys)
  (at level 70, format "Xs  ⊥{ Γ }*  Ys") : C_scope.
Notation "(⊥{ Γ }* )" := (Forall2 (⊥{Γ}))
  (only parsing, Γ at level 1) : C_scope.
Notation "X ⊥{ Γ1 , Γ2 , .. , Γ3 } Y" := (disjoint (pair .. (Γ1, Γ2) .. Γ3) X Y)
  (at level 70, format "X  ⊥{ Γ1 , Γ2 , .. , Γ3 }  Y") : C_scope.
Notation "Xs ⊥{ Γ1 , Γ2 , .. , Γ3 }* Ys" :=
  (Forall2 (disjoint (pair .. (Γ1, Γ2) .. Γ3)) Xs Ys)
  (at level 70, format "Xs  ⊥{ Γ1 ,  Γ2 , .. , Γ3 }*  Ys") : C_scope.
Hint Extern 0 (_ ⊥{_} _) => symmetry; eassumption.

Class DisjointList A := disjoint_list : list A → Prop.
Instance: Params (@disjoint_list) 2.
Notation "⊥ Xs" := (disjoint_list Xs) (at level 20, format "⊥  Xs") : C_scope.

Section disjoint_list.
  Context `{Disjoint A, Union A, Empty A}.
  Inductive disjoint_list_default : DisjointList A :=
    | disjoint_nil_2 : ⊥ (@nil A)
    | disjoint_cons_2 (X : A) (Xs : list A) : X ⊥ ⋃ Xs → ⊥ Xs → ⊥ (X :: Xs).
  Global Existing Instance disjoint_list_default.

  Lemma disjoint_list_nil  : ⊥ @nil A ↔ True.
  Proof. split; constructor. Qed.
  Lemma disjoint_list_cons X Xs : ⊥ (X :: Xs) ↔ X ⊥ ⋃ Xs ∧ ⊥ Xs.
  Proof. split. inversion_clear 1; auto. intros [??]. constructor; auto. Qed.
End disjoint_list.

Class Filter A B := filter: ∀ (P : A → Prop) `{∀ x, Decision (P x)}, B → B.

(** ** Monadic operations *)
(** We define operational type classes for the monadic operations bind, join 
and fmap. We use these type classes merely for convenient overloading of
notations and do not formalize any theory on monads (we do not even define a
class with the monad laws). *)
Class MRet (M : Type → Type) := mret: ∀ {A}, A → M A.
Instance: Params (@mret) 3.
Arguments mret {_ _ _} _.
Class MBind (M : Type → Type) := mbind : ∀ {A B}, (A → M B) → M A → M B.
Arguments mbind {_ _ _ _} _ !_ /.
Instance: Params (@mbind) 5.
Class MJoin (M : Type → Type) := mjoin: ∀ {A}, M (M A) → M A.
Instance: Params (@mjoin) 3.
Arguments mjoin {_ _ _} !_ /.
Class FMap (M : Type → Type) := fmap : ∀ {A B}, (A → B) → M A → M B.
Instance: Params (@fmap) 6.
Arguments fmap {_ _ _ _} _ !_ /.
Class OMap (M : Type → Type) := omap: ∀ {A B}, (A → option B) → M A → M B.
Instance: Params (@omap) 6.
Arguments omap {_ _ _ _} _ !_ /.

Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : C_scope.
Notation "( m ≫=)" := (λ f, mbind f m) (only parsing) : C_scope.
Notation "(≫= f )" := (mbind f) (only parsing) : C_scope.
Notation "(≫=)" := (λ m f, mbind f m) (only parsing) : C_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.
Infix "<$>" := fmap (at level 60, right associativity) : C_scope.
Notation "' ( x1 , x2 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1, x2) := x in z))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3) := x in z))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3  , x4 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4) := x in z))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3  , x4 , x5 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4,x5) := x in z))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3  , x4 , x5 , x6 ) ← y ; z" :=
  (y ≫= (λ x : _, let ' (x1,x2,x3,x4,x5,x6) := x in z))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.

Class MGuard (M : Type → Type) :=
  mguard: ∀ P {dec : Decision P} {A}, (P → M A) → M A.
Arguments mguard _ _ _ !_ _ _ /.
Notation "'guard' P ; o" := (mguard P (λ _, o))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.
Notation "'guard' P 'as' H ; o" := (mguard P (λ H, o))
  (at level 65, next at level 35, only parsing, right associativity) : C_scope.

(** ** Operations on maps *)
(** In this section we define operational type classes for the operations
on maps. In the file [fin_maps] we will axiomatize finite maps.
The function look up [m !! k] should yield the element at key [k] in [m]. *)
Class Lookup (K A M : Type) := lookup: K → M → option A.
Instance: Params (@lookup) 4.
Notation "m !! i" := (lookup i m) (at level 20) : C_scope.
Notation "(!!)" := lookup (only parsing) : C_scope.
Notation "( m !!)" := (λ i, m !! i) (only parsing) : C_scope.
Notation "(!! i )" := (lookup i) (only parsing) : C_scope.
Arguments lookup _ _ _ _ !_ !_ / : simpl nomatch.

(** The function insert [<[k:=a]>m] should update the element at key [k] with
value [a] in [m]. *)
Class Insert (K A M : Type) := insert: K → A → M → M.
Instance: Params (@insert) 4.
Notation "<[ k := a ]>" := (insert k a)
  (at level 5, right associativity, format "<[ k := a ]>") : C_scope.
Arguments insert _ _ _ _ !_ _ !_ / : simpl nomatch.

(** The function delete [delete k m] should delete the value at key [k] in
[m]. If the key [k] is not a member of [m], the original map should be
returned. *)
Class Delete (K M : Type) := delete: K → M → M.
Instance: Params (@delete) 3.
Arguments delete _ _ _ !_ !_ / : simpl nomatch.

(** The function [alter f k m] should update the value at key [k] using the
function [f], which is called with the original value. *)
Class Alter (K A M : Type) := alter: (A → A) → K → M → M.
Instance: Params (@alter) 5.
Arguments alter {_ _ _ _} _ !_ !_ / : simpl nomatch.

(** The function [alter f k m] should update the value at key [k] using the
function [f], which is called with the original value at key [k] or [None]
if [k] is not a member of [m]. The value at [k] should be deleted if [f] 
yields [None]. *)
Class PartialAlter (K A M : Type) :=
  partial_alter: (option A → option A) → K → M → M.
Instance: Params (@partial_alter) 4.
Arguments partial_alter _ _ _ _ _ !_ !_ / : simpl nomatch.

(** The function [dom C m] should yield the domain of [m]. That is a finite
collection of type [C] that contains the keys that are a member of [m]. *)
Class Dom (M C : Type) := dom: M → C.
Instance: Params (@dom) 3.
Arguments dom {_} _ {_} !_ / : simpl nomatch, clear implicits.

(** The function [merge f m1 m2] should merge the maps [m1] and [m2] by
constructing a new map whose value at key [k] is [f (m1 !! k) (m2 !! k)].*)
Class Merge (M : Type → Type) :=
  merge: ∀ {A B C}, (option A → option B → option C) → M A → M B → M C.
Instance: Params (@merge) 4.
Arguments merge _ _ _ _ _ _ !_ !_ / : simpl nomatch.

(** The function [union_with f m1 m2] is supposed to yield the union of [m1]
and [m2] using the function [f] to combine values of members that are in
both [m1] and [m2]. *)
Class UnionWith (A M : Type) :=
  union_with: (A → A → option A) → M → M → M.
Instance: Params (@union_with) 3.
Arguments union_with {_ _ _} _ !_ !_ / : simpl nomatch.

(** Similarly for intersection and difference. *)
Class IntersectionWith (A M : Type) :=
  intersection_with: (A → A → option A) → M → M → M.
Instance: Params (@intersection_with) 3.
Arguments intersection_with {_ _ _} _ !_ !_ / : simpl nomatch.

Class DifferenceWith (A M : Type) :=
  difference_with: (A → A → option A) → M → M → M.
Instance: Params (@difference_with) 3.
Arguments difference_with {_ _ _} _ !_ !_ / : simpl nomatch.

Definition intersection_with_list `{IntersectionWith A M}
  (f : A → A → option A) : M → list M → M := fold_right (intersection_with f).
Arguments intersection_with_list _ _ _ _ _ !_ /.

Class LookupE (E K A M : Type) := lookupE: E → K → M → option A.
Instance: Params (@lookupE) 6.
Notation "m !!{ Γ } i" := (lookupE Γ i m)
  (at level 20, format "m  !!{ Γ }  i") : C_scope.
Notation "(!!{ Γ } )" := (lookupE Γ) (only parsing, Γ at level 1) : C_scope.
Arguments lookupE _ _ _ _ _ _ !_ !_ / : simpl nomatch.

Class InsertE (E K A M : Type) := insertE: E → K → A → M → M.
Instance: Params (@insert) 6.
Notation "<[ k := a ]{ Γ }>" := (insertE Γ k a)
  (at level 5, right associativity, format "<[ k := a ]{ Γ }>") : C_scope.
Arguments insertE _ _ _ _ _ _ !_ _ !_ / : simpl nomatch.

(** ** Common properties *)
(** These operational type classes allow us to refer to common mathematical
properties in a generic way. For example, for injectivity of [(k ++)] it
allows us to write [injective (k ++)] instead of [app_inv_head k]. *)
Class Injective {A B} (R : relation A) (S : relation B) (f : A → B) : Prop :=
  injective: ∀ x y, S (f x) (f y) → R x y.
Class Injective2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  injective2: ∀ x1 x2  y1 y2, S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.
Class Cancel {A B} (S : relation B) (f : A → B) (g : B → A) : Prop :=
  cancel: ∀ x, S (f (g x)) x.
Class Surjective {A B} (R : relation B) (f : A → B) :=
  surjective : ∀ y, ∃ x, R (f x) y.
Class Idempotent {A} (R : relation A) (f : A → A → A) : Prop :=
  idempotent: ∀ x, R (f x x) x.
Class Commutative {A B} (R : relation A) (f : B → B → A) : Prop :=
  commutative: ∀ x y, R (f x y) (f y x).
Class LeftId {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  left_id: ∀ x, R (f i x) x.
Class RightId {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  right_id: ∀ x, R (f x i) x.
Class Associative {A} (R : relation A) (f : A → A → A) : Prop :=
  associative: ∀ x y z, R (f x (f y z)) (f (f x y) z).
Class LeftAbsorb {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  left_absorb: ∀ x, R (f i x) i.
Class RightAbsorb {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  right_absorb: ∀ x, R (f x i) i.
Class LeftDistr {A} (R : relation A) (f g : A → A → A) : Prop :=
  left_distr: ∀ x y z, R (f x (g y z)) (g (f x y) (f x z)).
Class RightDistr {A} (R : relation A) (f g : A → A → A) : Prop :=
  right_distr: ∀ y z x, R (f (g y z) x) (g (f y x) (f z x)).
Class AntiSymmetric {A} (R S : relation A) : Prop :=
  anti_symmetric: ∀ x y, S x y → S y x → R x y.
Class Total {A} (R : relation A) := total x y : R x y ∨ R y x.
Class Trichotomy {A} (R : relation A) :=
  trichotomy : ∀ x y, R x y ∨ x = y ∨ R y x.
Class TrichotomyT {A} (R : relation A) :=
  trichotomyT : ∀ x y, {R x y} + {x = y} + {R y x}.

Arguments irreflexivity {_} _ {_} _ _.
Arguments injective {_ _ _ _} _ {_} _ _ _.
Arguments injective2 {_ _ _ _ _ _} _ {_} _ _ _ _ _.
Arguments cancel {_ _ _} _ _ {_} _.
Arguments surjective {_ _ _} _ {_} _.
Arguments idempotent {_ _} _ {_} _.
Arguments commutative {_ _ _} _ {_} _ _.
Arguments left_id {_ _} _ _ {_} _.
Arguments right_id {_ _} _ _ {_} _.
Arguments associative {_ _} _ {_} _ _ _.
Arguments left_absorb {_ _} _ _ {_} _.
Arguments right_absorb {_ _} _ _ {_} _.
Arguments left_distr {_ _} _ _ {_} _ _ _.
Arguments right_distr {_ _} _ _ {_} _ _ _.
Arguments anti_symmetric {_ _} _ {_} _ _ _ _.
Arguments total {_} _ {_} _ _.
Arguments trichotomy {_} _ {_} _ _.
Arguments trichotomyT {_} _ {_} _ _.

Instance id_injective {A} : Injective (=) (=) (@id A).
Proof. intros ??; auto. Qed.

(** The following lemmas are specific versions of the projections of the above
type classes for Leibniz equality. These lemmas allow us to enforce Coq not to
use the setoid rewriting mechanism. *)
Lemma idempotent_L {A} (f : A → A → A) `{!Idempotent (=) f} x : f x x = x.
Proof. auto. Qed.
Lemma commutative_L {A B} (f : B → B → A) `{!Commutative (=) f} x y :
  f x y = f y x.
Proof. auto. Qed.
Lemma left_id_L {A} (i : A) (f : A → A → A) `{!LeftId (=) i f} x : f i x = x.
Proof. auto. Qed.
Lemma right_id_L {A} (i : A) (f : A → A → A) `{!RightId (=) i f} x : f x i = x.
Proof. auto. Qed.
Lemma associative_L {A} (f : A → A → A) `{!Associative (=) f} x y z :
  f x (f y z) = f (f x y) z.
Proof. auto. Qed.
Lemma left_absorb_L {A} (i : A) (f : A → A → A) `{!LeftAbsorb (=) i f} x :
  f i x = i.
Proof. auto. Qed.
Lemma right_absorb_L {A} (i : A) (f : A → A → A) `{!RightAbsorb (=) i f} x :
  f x i = i.
Proof. auto. Qed.
Lemma left_distr_L {A} (f g : A → A → A) `{!LeftDistr (=) f g} x y z :
  f x (g y z) = g (f x y) (f x z).
Proof. auto. Qed.
Lemma right_distr_L {A} (f g : A → A → A) `{!RightDistr (=) f g} y z x :
  f (g y z) x = g (f y x) (f z x).
Proof. auto. Qed.

(** ** Axiomatization of ordered structures *)
(** The classes [PreOrder], [PartialOrder], and [TotalOrder] use an arbitrary
relation [R] instead of [⊆] to support multiple orders on the same type. *)
Class PartialOrder {A} (R : relation A) : Prop := {
  partial_order_pre :> PreOrder R;
  partial_order_anti_symmetric :> AntiSymmetric (=) R
}.
Class TotalOrder {A} (R : relation A) : Prop := {
  total_order_partial :> PartialOrder R;
  total_order_trichotomy :> Trichotomy (strict R)
}.

(** We do not use a setoid equality in the following interfaces to avoid the
need for proofs that the relations and operations are proper. Instead, we
define setoid equality generically [λ X Y, X ⊆ Y ∧ Y ⊆ X]. *)
Class EmptySpec A `{Empty A, SubsetEq A} : Prop := subseteq_empty X : ∅ ⊆ X.
Class JoinSemiLattice A `{SubsetEq A, Union A} : Prop := {
  join_semi_lattice_pre :>> PreOrder (⊆);
  union_subseteq_l X Y : X ⊆ X ∪ Y;
  union_subseteq_r X Y : Y ⊆ X ∪ Y;
  union_least X Y Z : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z
}.
Class MeetSemiLattice A `{SubsetEq A, Intersection A} : Prop := {
  meet_semi_lattice_pre :>> PreOrder (⊆);
  intersection_subseteq_l X Y : X ∩ Y ⊆ X;
  intersection_subseteq_r X Y : X ∩ Y ⊆ Y;
  intersection_greatest X Y Z : Z ⊆ X → Z ⊆ Y → Z ⊆ X ∩ Y
}.
Class Lattice A `{SubsetEq A, Union A, Intersection A} : Prop := {
  lattice_join :>> JoinSemiLattice A;
  lattice_meet :>> MeetSemiLattice A;
  lattice_distr X Y Z : (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
}.

(** ** Axiomatization of collections *)
(** The class [SimpleCollection A C] axiomatizes a collection of type [C] with
elements of type [A]. *)
Instance: Params (@map) 3.
Class SimpleCollection A C `{ElemOf A C,
    Empty C, Singleton A C, Union C} : Prop := {
  not_elem_of_empty (x : A) : x ∉ ∅;
  elem_of_singleton (x y : A) : x ∈ {[ y ]} ↔ x = y;
  elem_of_union X Y (x : A) : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y
}.
Class Collection A C `{ElemOf A C, Empty C, Singleton A C,
    Union C, Intersection C, Difference C} : Prop := {
  collection_simple :>> SimpleCollection A C;
  elem_of_intersection X Y (x : A) : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y;
  elem_of_difference X Y (x : A) : x ∈ X ∖ Y ↔ x ∈ X ∧ x ∉ Y
}.
Class CollectionOps A C `{ElemOf A C, Empty C, Singleton A C, Union C,
    Intersection C, Difference C, IntersectionWith A C, Filter A C} : Prop := {
  collection_ops :>> Collection A C;
  elem_of_intersection_with (f : A → A → option A) X Y (x : A) :
    x ∈ intersection_with f X Y ↔ ∃ x1 x2, x1 ∈ X ∧ x2 ∈ Y ∧ f x1 x2 = Some x;
  elem_of_filter X P `{∀ x, Decision (P x)} x : x ∈ filter P X ↔ P x ∧ x ∈ X
}.

(** We axiomative a finite collection as a collection whose elements can be
enumerated as a list. These elements, given by the [elements] function, may be
in any order and should not contain duplicates. *)
Class Elements A C := elements: C → list A.
Instance: Params (@elements) 3.

(** We redefine the standard library's [In] and [NoDup] using type classes. *)
Inductive elem_of_list {A} : ElemOf A (list A) :=
  | elem_of_list_here (x : A) l : x ∈ x :: l
  | elem_of_list_further (x y : A) l : x ∈ l → x ∈ y :: l.
Existing Instance elem_of_list.

Inductive NoDup {A} : list A → Prop :=
  | NoDup_nil_2 : NoDup []
  | NoDup_cons_2 x l : x ∉ l → NoDup l → NoDup (x :: l).

(** Decidability of equality of the carrier set is admissible, but we add it
anyway so as to avoid cycles in type class search. *)
Class FinCollection A C `{ElemOf A C, Empty C, Singleton A C,
    Union C, Intersection C, Difference C,
    Elements A C, ∀ x y : A, Decision (x = y)} : Prop := {
  fin_collection :>> Collection A C;
  elem_of_elements X x : x ∈ elements X ↔ x ∈ X;
  NoDup_elements X : NoDup (elements X)
}.
Class Size C := size: C → nat.
Arguments size {_ _} !_ / : simpl nomatch.
Instance: Params (@size) 2.

(** The class [Collection M] axiomatizes a type constructor [M] that can be
used to construct a collection [M A] with elements of type [A]. The advantage
of this class, compared to [Collection], is that it also axiomatizes the
the monadic operations. The disadvantage, is that not many inhabits are
possible (we will only provide an inhabitant using unordered lists without
duplicates removed). More interesting implementations typically need
decidability of equality, or a total order on the elements, which do not fit
in a type constructor of type [Type → Type]. *)
Class CollectionMonad M `{∀ A, ElemOf A (M A),
    ∀ A, Empty (M A), ∀ A, Singleton A (M A), ∀ A, Union (M A),
    !MBind M, !MRet M, !FMap M, !MJoin M} : Prop := {
  collection_monad_simple A :> SimpleCollection A (M A);
  elem_of_bind {A B} (f : A → M B) (X : M A) (x : B) :
    x ∈ X ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ X;
  elem_of_ret {A} (x y : A) : x ∈ mret y ↔ x = y;
  elem_of_fmap {A B} (f : A → B) (X : M A) (x : B) :
    x ∈ f <$> X ↔ ∃ y, x = f y ∧ y ∈ X;
  elem_of_join {A} (X : M (M A)) (x : A) : x ∈ mjoin X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X
}.

(** The function [fresh X] yields an element that is not contained in [X]. We
will later prove that [fresh] is [Proper] with respect to the induced setoid
equality on collections. *)
Class Fresh A C := fresh: C → A.
Instance: Params (@fresh) 3.
Class FreshSpec A C `{ElemOf A C,
    Empty C, Singleton A C, Union C, Fresh A C} : Prop := {
  fresh_collection_simple :>> SimpleCollection A C;
  fresh_proper_alt X Y : (∀ x, x ∈ X ↔ x ∈ Y) → fresh X = fresh Y;
  is_fresh (X : C) : fresh X ∉ X
}.

(** * Booleans *)
(** The following coercion allows us to use Booleans as propositions. *)
Coercion Is_true : bool >-> Sortclass.
Hint Unfold Is_true.
Hint Resolve orb_prop_intro andb_prop_intro.
Notation "(&&)" := andb (only parsing).
Notation "(||)" := orb (only parsing).
Infix "&&*" := (zip_with (&&)) (at level 40).
Infix "||*" := (zip_with (||)) (at level 50).

Definition bool_le (β1 β2 : bool) : Prop := negb β1 || β2.
Infix "=.>" := bool_le (at level 70).
Infix "=.>*" := (Forall2 bool_le) (at level 70).
Instance: PartialOrder bool_le.
Proof. repeat split; repeat intros [|]; compute; tauto. Qed.

(** * Miscellaneous *)
Class Half A := half: A → A.
Notation "½" := half : C_scope.
Notation "½*" := (fmap (M:=list) half) : C_scope.

Lemma proj1_sig_inj {A} (P : A → Prop) x (Px : P x) y (Py : P y) :
  x↾Px = y↾Py → x = y.
Proof. injection 1; trivial. Qed.
Lemma not_symmetry `{R : relation A, !Symmetric R} x y : ¬R x y → ¬R y x.
Proof. intuition. Qed.
Lemma symmetry_iff `(R : relation A) `{!Symmetric R} x y : R x y ↔ R y x.
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
Instance prod_map_injective {A A' B B'} (f : A → A') (g : B → B') :
  Injective (=) (=) f → Injective (=) (=) g →
  Injective (=) (=) (prod_map f g).
Proof.
  intros ?? [??] [??] ?; simpl in *; f_equal;
    [apply (injective f)|apply (injective g)]; congruence.
Qed.

Definition prod_relation {A B} (R1 : relation A) (R2 : relation B) :
  relation (A * B) := λ x y, R1 (x.1) (y.1) ∧ R2 (x.2) (y.2).
Section prod_relation.
  Context `{R1 : relation A, R2 : relation B}.
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
Lemma or_l P Q : ¬Q → P ∨ Q ↔ P.
Proof. tauto. Qed.
Lemma or_r P Q : ¬P → P ∨ Q ↔ Q.
Proof. tauto. Qed.
Lemma and_wlog_l (P Q : Prop) : (Q → P) → Q → (P ∧ Q).
Proof. tauto. Qed.
Lemma and_wlog_r (P Q : Prop) : P → (P → Q) → (P ∧ Q).
Proof. tauto. Qed.
Instance: ∀ A B (x : B), Commutative (=) (λ _ _ : A, x).
Proof. red. trivial. Qed.
Instance: ∀ A (x : A), Associative (=) (λ _ _ : A, x).
Proof. red. trivial. Qed.
Instance: ∀ A, Associative (=) (λ x _ : A, x).
Proof. red. trivial. Qed.
Instance: ∀ A, Associative (=) (λ _ x : A, x).
Proof. red. trivial. Qed.
Instance: ∀ A, Idempotent (=) (λ x _ : A, x).
Proof. red. trivial. Qed.
Instance: ∀ A, Idempotent (=) (λ _ x : A, x).
Proof. red. trivial. Qed.

Instance left_id_propholds {A} (R : relation A) i f :
  LeftId R i f → ∀ x, PropHolds (R (f i x) x).
Proof. red. trivial. Qed.
Instance right_id_propholds {A} (R : relation A) i f :
  RightId R i f → ∀ x, PropHolds (R (f x i) x).
Proof. red. trivial. Qed.
Instance left_absorb_propholds {A} (R : relation A) i f :
  LeftAbsorb R i f → ∀ x, PropHolds (R (f i x) i).
Proof. red. trivial. Qed.
Instance right_absorb_propholds {A} (R : relation A) i f :
  RightAbsorb R i f → ∀ x, PropHolds (R (f x i) i).
Proof. red. trivial. Qed.
Instance idem_propholds {A} (R : relation A) f :
  Idempotent R f → ∀ x, PropHolds (R (f x x) x).
Proof. red. trivial. Qed.

Lemma injective_iff {A B} {R : relation A} {S : relation B} (f : A → B)
  `{!Injective R S f} `{!Proper (R ==> S) f} x y : S (f x) (f y) ↔ R x y.
Proof. firstorder. Qed.
Instance: Injective (=) (=) (@inl A B).
Proof. injection 1; auto. Qed.
Instance: Injective (=) (=) (@inr A B).
Proof. injection 1; auto. Qed.
Instance: Injective2 (=) (=) (=) (@pair A B).
Proof. injection 1; auto. Qed.
Instance: ∀ `{Injective2 A B C R1 R2 R3 f} y, Injective R1 R3 (λ x, f x y).
Proof. repeat intro; edestruct (injective2 f); eauto. Qed.
Instance: ∀ `{Injective2 A B C R1 R2 R3 f} x, Injective R2 R3 (f x).
Proof. repeat intro; edestruct (injective2 f); eauto. Qed.

Lemma cancel_injective `{Cancel A B R1 f g}
  `{!Equivalence R1} `{!Proper (R2 ==> R1) f} : Injective R1 R2 g.
Proof.
  intros x y E. rewrite <-(cancel f g x), <-(cancel f g y), E. reflexivity.
Qed.
Lemma cancel_surjective `{Cancel A B R1 f g} : Surjective R1 f.
Proof. intros y. exists (g y). auto. Qed.

Lemma impl_transitive (P Q R : Prop) : (P → Q) → (Q → R) → (P → R).
Proof. tauto. Qed.
Instance: Commutative (↔) (@eq A).
Proof. red; intuition. Qed.
Instance: Commutative (↔) (λ x y, @eq A y x).
Proof. red; intuition. Qed.
Instance: Commutative (↔) (↔).
Proof. red; intuition. Qed.
Instance: Commutative (↔) (∧).
Proof. red; intuition. Qed.
Instance: Associative (↔) (∧).
Proof. red; intuition. Qed.
Instance: Idempotent (↔) (∧).
Proof. red; intuition. Qed.
Instance: Commutative (↔) (∨).
Proof. red; intuition. Qed.
Instance: Associative (↔) (∨).
Proof. red; intuition. Qed.
Instance: Idempotent (↔) (∨).
Proof. red; intuition. Qed.
Instance: LeftId (↔) True (∧).
Proof. red; intuition. Qed.
Instance: RightId (↔) True (∧).
Proof. red; intuition. Qed.
Instance: LeftAbsorb (↔) False (∧).
Proof. red; intuition. Qed.
Instance: RightAbsorb (↔) False (∧).
Proof. red; intuition. Qed.
Instance: LeftId (↔) False (∨).
Proof. red; intuition. Qed.
Instance: RightId (↔) False (∨).
Proof. red; intuition. Qed.
Instance: LeftAbsorb (↔) True (∨).
Proof. red; intuition. Qed.
Instance: RightAbsorb (↔) True (∨).
Proof. red; intuition. Qed.
Instance: LeftId (↔) True impl.
Proof. unfold impl. red; intuition. Qed.
Instance: RightAbsorb (↔) True impl.
Proof. unfold impl. red; intuition. Qed.
Instance: LeftDistr (↔) (∧) (∨).
Proof. red; intuition. Qed.
Instance: RightDistr (↔) (∧) (∨).
Proof. red; intuition. Qed.
Instance: LeftDistr (↔) (∨) (∧).
Proof. red; intuition. Qed.
Instance: RightDistr (↔) (∨) (∧).
Proof. red; intuition. Qed.
Lemma not_injective `{Injective A B R R' f} x y : ¬R x y → ¬R' (f x) (f y).
Proof. intuition. Qed.
Instance injective_compose {A B C} R1 R2 R3 (f : A → B) (g : B → C) :
  Injective R1 R2 f → Injective R2 R3 g → Injective R1 R3 (g ∘ f).
Proof. red; intuition. Qed.
Instance surjective_compose {A B C} R (f : A → B) (g : B → C) :
  Surjective (=) f → Surjective R g → Surjective R (g ∘ f).
Proof.
  intros ?? x. unfold compose. destruct (surjective g x) as [y ?].
  destruct (surjective f y) as [z ?]. exists z. congruence.
Qed.

Section sig_map.
  Context `{P : A → Prop} `{Q : B → Prop} (f : A → B) (Hf : ∀ x, P x → Q (f x)).
  Definition sig_map (x : sig P) : sig Q := f (`x) ↾ Hf _ (proj2_sig x).
  Global Instance sig_map_injective:
    (∀ x, ProofIrrel (P x)) → Injective (=) (=) f → Injective (=) (=) sig_map.
  Proof.
    intros ?? [x Hx] [y Hy]. injection 1. intros Hxy.
    apply (injective f) in Hxy; subst. rewrite (proof_irrel _ Hy). auto.
  Qed.
End sig_map.
Arguments sig_map _ _ _ _ _ _ !_ /.
