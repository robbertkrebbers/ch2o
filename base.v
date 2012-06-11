Global Generalizable All Variables.
Global Set Automatic Coercions Import.
Require Export Morphisms RelationClasses List Bool Utf8 Program Setoid NArith.

Arguments existT {_ _} _ _.
Arguments existT2 {_ _ _} _ _ _.

Definition proj1_T2 {A} {P Q : A → Type} (x : sigT2 P Q) : A :=
  match x with existT2 a _ _ => a end.
Definition proj2_T2 {A} {P Q : A → Type} (x : sigT2 P Q) : P (proj1_T2 x) :=
  match x with existT2 _ p _ => p end.
Definition proj3_T2 {A} {P Q : A → Type} (x : sigT2 P Q) : Q (proj1_T2 x) :=
  match x with existT2 _ _ q => q end.

(*  Common notations *)
Delimit Scope C_scope with C.
Global Open Scope C_scope.

Notation "(=)" := eq (only parsing) : C_scope.
Notation "( x =)" := (eq x) (only parsing) : C_scope.
Notation "(= x )" := (λ y, eq y x) (only parsing) : C_scope.
Notation "(≠)" := (λ x y, x ≠ y) (only parsing) : C_scope.
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing) : C_scope.
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing) : C_scope.

Hint Extern 0 (?x = ?x) => reflexivity.

Notation "(→)" := (λ x y, x → y) : C_scope.
Notation "( T →)" := (λ y, T → y) : C_scope.
Notation "(→ T )" := (λ y, y → T) : C_scope.
Notation "t $ r" := (t r) (at level 65, right associativity, only parsing) : C_scope.
Infix "∘" := compose : C_scope.
Notation "(∘)" := compose (only parsing) : C_scope.
Notation "( f ∘)" := (compose f) (only parsing) : C_scope.
Notation "(∘ f )" := (λ g, compose g f) (only parsing) : C_scope.
Notation "x ↾ p" := (exist _ x p) (at level 20) : C_scope.
Notation "` x" := (proj1_sig x) : C_scope.

(* Provable propositions *)
Class PropHolds (P : Prop) := prop_holds: P.

(* Decidable propositions *)
Class Decision (P : Prop) := decide : {P} + {¬P}.
Arguments decide _ {_}.

(* Common relations & operations *)
Class Equiv A := equiv: relation A.
Infix "≡" := equiv (at level 70, no associativity) : C_scope.
Notation "(≡)" := equiv (only parsing) : C_scope.
Notation "( x ≡)" := (equiv x) (only parsing) : C_scope.
Notation "(≡ x )" := (λ y, y ≡ x) (only parsing) : C_scope.
Notation "(≢)" := (λ x y, ¬x ≡ y) (only parsing) : C_scope.
Notation "x ≢ y":= (¬x ≡ y) (at level 70, no associativity) : C_scope.
Notation "( x ≢)" := (λ y, x ≢ y) (only parsing) : C_scope.
Notation "(≢ x )" := (λ y, y ≢ x) (only parsing) : C_scope.

Instance equiv_default_relation `{Equiv A} : DefaultRelation (≡) | 3.
Hint Extern 0 (?x ≡ ?x) => reflexivity.

Class Empty A := empty: A.
Notation "∅" := empty : C_scope.

Class Union A := union: A → A → A.
Infix "∪" := union (at level 50, left associativity) : C_scope.
Notation "(∪)" := union (only parsing) : C_scope.
Notation "( x ∪)" := (union x) (only parsing) : C_scope.
Notation "(∪ x )" := (λ y, union y x) (only parsing) : C_scope.

Class Intersection A := intersection: A → A → A.
Infix "∩" := intersection (at level 40) : C_scope.
Notation "(∩)" := intersection (only parsing) : C_scope.
Notation "( x ∩)" := (intersection x) (only parsing) : C_scope.
Notation "(∩ x )" := (λ y, intersection y x) (only parsing) : C_scope.

Class Difference A := difference: A → A → A.
Infix "∖" := difference (at level 40) : C_scope.
Notation "(∖)" := difference (only parsing) : C_scope.
Notation "( x ∖)" := (difference x) (only parsing) : C_scope.
Notation "(∖ x )" := (λ y, difference y x) (only parsing) : C_scope.

Class SubsetEq A := subseteq: A → A → Prop.
Infix "⊆" := subseteq (at level 70) : C_scope.
Notation "(⊆)" := subseteq (only parsing) : C_scope.
Notation "( X ⊆ )" := (subseteq X) (only parsing) : C_scope.
Notation "( ⊆ X )" := (λ Y, subseteq Y X) (only parsing) : C_scope.
Notation "X ⊈ Y" := (¬X ⊆ Y) (at level 70) : C_scope.
Notation "(⊈)" := (λ X Y, X ⊈ Y) (only parsing) : C_scope.
Notation "( X ⊈ )" := (λ Y, X ⊈ Y) (only parsing) : C_scope.
Notation "( ⊈ X )" := (λ Y, Y ⊈ X) (only parsing) : C_scope.

Hint Extern 0 (?x ⊆ ?x) => reflexivity.

Class Singleton A B := singleton: A → B.
Notation "{{ x }}" := (singleton x) : C_scope.
Notation "{{ x ; y ; .. ; z }}" := (union .. (union (singleton x) (singleton y)) .. (singleton z)) : C_scope.

Class ElemOf A B := elem_of: A → B → Prop.
Infix "∈" := elem_of (at level 70) : C_scope.
Notation "(∈)" := elem_of (only parsing) : C_scope.
Notation "( x ∈)" := (elem_of x) (only parsing) : C_scope.
Notation "(∈ X )" := (λ x, elem_of x X) (only parsing) : C_scope.
Notation "x ∉ X" := (¬x ∈ X) (at level 80) : C_scope.
Notation "(∉)" := (λ x X, x ∉ X) (only parsing) : C_scope.
Notation "( x ∉)" := (λ X, x ∉ X) (only parsing) : C_scope.
Notation "(∉ X )" := (λ x, x ∉ X) (only parsing) : C_scope.

Class UnionWith M := union_with: ∀ {A}, (A → A → A) → M A → M A → M A.
Class IntersectWith M := intersect_with: ∀ {A}, (A → A → A) → M A → M A → M A.

(* Common properties *)
Class Injective {A B} R S (f : A → B) := injective: ∀ x y : A, S (f x) (f y) → R x y.
Class Idempotent {A} R (f : A → A → A) := idempotent: ∀ x, R (f x x) x.
Class Commutative {A B} R (f : B → B → A) := commutative: ∀ x y, R (f x y) (f y x).
Class LeftId {A} R (i : A) (f : A → A → A) := left_id: ∀ x, R (f i x) x.
Class RightId {A} R (i : A) (f : A → A → A) := right_id: ∀ x, R (f x i) x.
Class Associative {A} R (f : A → A → A) := associative: ∀ x y z, R (f x (f y z)) (f (f x y) z).

Arguments injective {_ _ _ _} _ {_} _ _ _.
Arguments idempotent {_ _} _ {_} _.
Arguments commutative {_ _ _} _ {_} _ _.
Arguments left_id {_ _} _ _ {_} _.
Arguments right_id {_ _} _ _ {_} _.
Arguments associative {_ _} _ {_} _ _ _.

(* Monadic operations *)
Section monad_ops.
  Context (M : Type → Type).

  Class MRet := mret: ∀ {A}, A → M A.
  Class MBind := mbind: ∀ {A B}, (A → M B) → M A → M B.
  Class MJoin := mjoin: ∀ {A}, M (M A) → M A.
  Class FMap := fmap: ∀ {A B}, (A → B) → M A → M B.
End monad_ops.

Arguments mret {M MRet A} _.
Arguments mbind {M MBind A B} _ _.
Arguments mjoin {M MJoin A} _.
Arguments fmap {M FMap A B} _ _.

Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : C_scope.
Notation "x ← y ; z" := (y ≫= (λ x : _, z)) (at level 65, next at level 35, right associativity) : C_scope.
Infix "<$>" := fmap (at level 65, right associativity, only parsing) : C_scope.

(* Ordered structures *)
Class BoundedPreOrder A `{Empty A} `{SubsetEq A} := {
  bounded_preorder :>> PreOrder (⊆);
  subseteq_empty x : ∅ ⊆ x
}.

(* Note: no equality to avoid the need for setoids. We define equality in a generic way. *)
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

(* Containers *)
Class Size C := size: C → nat.
Class Map A C := map: (A → A) → (C → C).

Class Collection A C `{ElemOf A C} `{Empty C} `{Union C} 
    `{Intersection C} `{Difference C} `{Singleton A C} `{Map A C} := {
  elem_of_empty (x : A) : x ∉ ∅;
  elem_of_singleton (x y : A) : x ∈ {{ y }} ↔ x = y;
  elem_of_union X Y (x : A) : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y;
  elem_of_intersection X Y (x : A) : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y;
  elem_of_difference X Y (x : A) : x ∈ X ∖ Y ↔ x ∈ X ∧ x ∉ Y;
  elem_of_map f X (x : A) : x ∈ map f X ↔ ∃ y, x = f y ∧ y ∈ X
}.

Class Elements A C := elements: C → list A.
Class FinCollection A C `{Empty C} `{Union C} `{Intersection C} `{Difference C} 
    `{Singleton A C} `{ElemOf A C} `{Map A C} `{Elements A C} := {
  fin_collection :>> Collection A C;
  elements_spec X x : x ∈ X ↔ In x (elements X);
  elements_nodup X : NoDup (elements X)
}. 

Class Fresh A C := fresh: C → A.
Class FreshSpec A C `{!Fresh A C} `{!ElemOf A C} := {
  fresh_proper X Y : (∀ x, x ∈ X ↔ x ∈ Y) → fresh X = fresh Y;
  is_fresh (X : C) : fresh X ∉ X
}.

(* Maps *)
Class Lookup K M := lookup: ∀ {A}, K → M A → option A.
Notation "m !! i" := (lookup i m) (at level 20) : C_scope.
Notation "(!!)" := lookup (only parsing) : C_scope.
Notation "( m !!)" := (λ i, lookup i m) (only parsing) : C_scope.
Notation "(!! i )" := (lookup i) (only parsing) : C_scope.

Class PartialAlter K M := partial_alter: ∀ {A}, (option A → option A) → K → M A → M A.
Class Alter K M := alter: ∀ {A}, (A → A) → K → M A → M A.
Class Dom K M := dom: ∀ C `{Empty C} `{Union C} `{Singleton K C}, M → C.
Class Merge M := merge: ∀ {A}, (option A → option A → option A) → M A → M A → M A.
Class Insert K M := insert: ∀ {A}, K → A → M A → M A.
Notation "<[ k := a ]>" := (insert k a) (at level 5, right associativity) : C_scope.
Class Delete K M := delete: K → M → M.

(* Misc *)
Instance pointwise_reflexive {A} `{R : relation B} :
  Reflexive R → Reflexive (pointwise_relation A R) | 9.
Proof. firstorder. Qed.
Instance pointwise_symmetric {A} `{R : relation B} :
  Symmetric R → Symmetric (pointwise_relation A R) | 9.
Proof. firstorder. Qed.
Instance pointwise_transitive {A} `{R : relation B} :
  Transitive R → Transitive (pointwise_relation A R) | 9.
Proof. firstorder. Qed.

Definition fst_map {A A' B} (f : A → A') (p : A * B) : A' * B := (f (fst p), snd p).
Definition snd_map {A B B'} (f : B → B') (p : A * B) : A * B' := (fst p, f (snd p)).
Definition prod_relation {A B} (R1 : relation A) (R2 : relation B) : relation (A * B) := λ x y,
  R1 (fst x) (fst y) ∧ R2 (snd x) (snd y).

Section prod_relation.
  Context `{R1 : relation A} `{R2 : relation B}.
  Global Instance: Reflexive R1 → Reflexive R2 → Reflexive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance: Symmetric R1 → Symmetric R2 → Symmetric (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance: Transitive R1 → Transitive R2 → Transitive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance: Equivalence R1 → Equivalence R2 → Equivalence (prod_relation R1 R2).
  Proof. split; apply _. Qed.
  Global Instance: Proper (R1 ==> R2 ==> prod_relation R1 R2) pair.
  Proof. firstorder eauto. Qed.
  Global Instance: Proper (prod_relation R1 R2 ==> R1) fst.
  Proof. firstorder eauto. Qed.
  Global Instance: Proper (prod_relation R1 R2 ==> R2) snd.
  Proof. firstorder eauto. Qed.
End prod_relation.

Definition lift_relation {A B} (R : relation A) (f : B → A) : relation B := λ x y, R (f x) (f y).
Definition lift_relation_equivalence {A B} (R : relation A) (f : B → A) :
  Equivalence R → Equivalence (lift_relation R f).
Proof. unfold lift_relation. firstorder. Qed.
Hint Extern 0 (Equivalence (lift_relation _ _)) => eapply @lift_relation_equivalence : typeclass_instances.

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

Instance left_id_propholds {A} (R : relation A) i f : LeftId R i f → ∀ x, PropHolds (R (f i x) x).
Proof. easy. Qed.
Instance right_id_propholds {A} (R : relation A) i f : RightId R i f → ∀ x, PropHolds (R (f x i) x).
Proof. easy. Qed.
Instance idem_propholds {A} (R : relation A) f : Idempotent R f → ∀ x, PropHolds (R (f x x) x).
Proof. easy. Qed.

Ltac simplify_eqs := repeat
  match goal with
  | |- _ => progress subst
  | |- _ = _ => reflexivity
  | H : _ ≠ _ |- _ => now destruct H
  | H : _ = _ → False |- _ => now destruct H
  | H : _ = _ |- _ => discriminate H
  | H : _ = _ |-  ?G => change (id G); injection H; clear H; intros; unfold id at 1
  | H : ?f _ = ?f _ |- _ => apply (injective f) in H
  | H : ?f _ ?x = ?f _ ?x |- _ => apply (injective (λ y, f y x)) in H
  end.

Hint Extern 0 (PropHolds _) => assumption : typeclass_instances.
Instance: Proper (iff ==> iff) PropHolds.
Proof. now repeat intro. Qed.

Ltac solve_propholds :=
  match goal with
  | [ |- PropHolds (?P) ] => apply _
  | [ |- ?P ] => change (PropHolds P); apply _
  end.

Tactic Notation "remember" constr(t) "as" "(" ident(x) "," ident(E) ")" :=
  remember t as x;
  match goal with
  | E' : x = _ |- _ => rename E' into E
  end.
