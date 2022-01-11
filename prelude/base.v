(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects type class interfaces, notations, and general theorems
that are used throughout the whole development. Most importantly it contains
abstract interfaces for ordered structures, collections, and various other data
structures. *)

From stdpp Require Export prelude sets.

(** Throughout this development we use [C_scope] for all general purpose
notations that do not belong to a more specific scope. *)
Global Declare Scope C_scope.
Delimit Scope C_scope with C.
Global Open Scope C_scope.

Class EquivE E A := equivE: E → relation A.
#[global] Instance: Params (@equivE) 4 := {}.
Notation "X ≡{ Γ } Y" := (equivE Γ X Y)
  (at level 70, format "X  ≡{ Γ }  Y") : C_scope.
Notation "(≡{ Γ } )" := (equivE Γ) (only parsing, Γ at level 1) : C_scope.
Notation "X ≡{ Γ1 , Γ2 , .. , Γ3 } Y" :=
  (equivE (pair .. (Γ1, Γ2) .. Γ3) X Y)
  (at level 70, format "'[' X  ≡{ Γ1 , Γ2 , .. , Γ3 }  '/' Y ']'") : C_scope.
Notation "(≡{ Γ1 , Γ2 , .. , Γ3 } )" := (equivE (pair .. (Γ1, Γ2) .. Γ3))
  (only parsing, Γ1 at level 1) : C_scope.

Infix "∪*" := (zip_with (∪)) (at level 50, left associativity) : C_scope.
Notation "(∪*)" := (zip_with (∪)) (only parsing) : C_scope.
Infix "∪**" := (zip_with (zip_with (∪)))
  (at level 50, left associativity) : C_scope.
Infix "∪*∪**" := (zip_with (prod_zip (∪) (∪*)))
  (at level 50, left associativity) : C_scope.

Infix "∖*" := (zip_with (∖)) (at level 40, left associativity) : C_scope.
Notation "(∖*)" := (zip_with (∖)) (only parsing) : C_scope.
Infix "∖**" := (zip_with (zip_with (∖)))
  (at level 40, left associativity) : C_scope.
Infix "∖*∖**" := (zip_with (prod_zip (∖) (∖*)))
  (at level 50, left associativity) : C_scope.

Class SubsetEqE E A := subseteqE: E → relation A.
#[global] Instance: Params (@subseteqE) 4 := {}.
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
Global Hint Extern 0 (_ ⊆{_} _) => reflexivity: core.

(** * Type classes *)
(** ** Provable propositions *)
(** This type class collects provable propositions. It is useful to constraint
type classes by arbitrary propositions. *)
Class PropHolds (P : Prop) := prop_holds: P.

Global Hint Extern 0 (PropHolds _) => assumption : typeclass_instances.
#[global] Instance: Proper (iff ==> iff) PropHolds.
Proof. repeat intro; trivial. Qed.

Ltac solve_propholds :=
  match goal with
  | |- PropHolds (?P) => apply _
  | |- ?P => change (PropHolds P); apply _
  end.

Infix "⊆*" := (Forall2 (⊆)) (at level 70) : C_scope.
Notation "(⊆*)" := (Forall2 (⊆)) (only parsing) : C_scope.
Infix "⊆**" := (Forall2 (⊆*)) (at level 70) : C_scope.
Infix "⊆1*" := (Forall2 (λ p q, p.1 ⊆ q.1)) (at level 70) : C_scope.
Infix "⊆2*" := (Forall2 (λ p q, p.2 ⊆ q.2)) (at level 70) : C_scope.
Infix "⊆1**" := (Forall2 (λ p q, p.1 ⊆* q.1)) (at level 70) : C_scope.
Infix "⊆2**" := (Forall2 (λ p q, p.2 ⊆* q.2)) (at level 70) : C_scope.

Infix "##*" := (Forall2 (##)) (at level 70) : C_scope.
Notation "(##*)" := (Forall2 (##)) (only parsing) : C_scope.
Infix "##**" := (Forall2 (##*)) (at level 70) : C_scope.
Infix "##1*" := (Forall2 (λ p q, p.1 ## q.1)) (at level 70) : C_scope.
Infix "##2*" := (Forall2 (λ p q, p.2 ## q.2)) (at level 70) : C_scope.
Infix "##1**" := (Forall2 (λ p q, p.1 ##* q.1)) (at level 70) : C_scope.
Infix "##2**" := (Forall2 (λ p q, p.2 ##* q.2)) (at level 70) : C_scope.
Global Hint Extern 0 (_ ## _) => symmetry; eassumption: core.
Global Hint Extern 0 (_ ##* _) => symmetry; eassumption: core.

Class DisjointE E A := disjointE : E → A → A → Prop.
#[global] Instance: Params (@disjointE) 4 := {}.
Notation "X ##{ Γ } Y" := (disjointE Γ X Y)
  (at level 70, format "X  ##{ Γ }  Y") : C_scope.
Notation "(##{ Γ } )" := (disjointE Γ) (only parsing, Γ at level 1) : C_scope.
Notation "Xs ##{ Γ }* Ys" := (Forall2 (##{Γ}) Xs Ys)
  (at level 70, format "Xs  ##{ Γ }*  Ys") : C_scope.
Notation "(##{ Γ }* )" := (Forall2 (##{Γ}))
  (only parsing, Γ at level 1) : C_scope.
Notation "X ##{ Γ1 , Γ2 , .. , Γ3 } Y" := (disjoint (pair .. (Γ1, Γ2) .. Γ3) X Y)
  (at level 70, format "X  ##{ Γ1 , Γ2 , .. , Γ3 }  Y") : C_scope.
Notation "Xs ##{ Γ1 , Γ2 , .. , Γ3 }* Ys" :=
  (Forall2 (disjoint (pair .. (Γ1, Γ2) .. Γ3)) Xs Ys)
  (at level 70, format "Xs  ##{ Γ1 ,  Γ2 , .. , Γ3 }*  Ys") : C_scope.
Global Hint Extern 0 (_ ##{_} _) => symmetry; eassumption: core.

Class DisjointList A := disjoint_list : list A → Prop.
#[global] Instance: Params (@disjoint_list) 2 := {}.
Notation "## Xs" := (disjoint_list Xs) (at level 20, format "##  Xs") : C_scope.

Section disjoint_list.
  Context `{Disjoint A, Union A, Empty A}.
  Inductive disjoint_list_default : DisjointList A :=
    | disjoint_nil_2 : ## (@nil A)
    | disjoint_cons_2 (X : A) (Xs : list A) : X ## ⋃ Xs → ## Xs → ## (X :: Xs).
  #[global] Existing Instance disjoint_list_default.

  Lemma disjoint_list_nil  : ## @nil A ↔ True.
  Proof. split; constructor. Qed.
  Lemma disjoint_list_cons X Xs : ## (X :: Xs) ↔ X ## ⋃ Xs ∧ ## Xs.
  Proof. split. inversion_clear 1; auto. intros [??]. constructor; auto. Qed.
End disjoint_list.

(**
This was removed in std++ 1.5.0 
*)
Class LookupE (E K A M : Type) := lookupE: E → K → M → option A.
#[global] Instance: Params (@lookupE) 6 := {}.
Notation "m !!{ Γ } i" := (lookupE Γ i m)
  (at level 20, format "m  !!{ Γ }  i") : C_scope.
Notation "(!!{ Γ } )" := (lookupE Γ) (only parsing, Γ at level 1) : C_scope.
Arguments lookupE _ _ _ _ _ _ !_ !_ / : simpl nomatch.

Class InsertE (E K A M : Type) := insertE: E → K → A → M → M.
#[global] Instance: Params (@insert) 6 := {}.
Notation "<[ k := a ]{ Γ }>" := (insertE Γ k a)
  (at level 5, right associativity, format "<[ k := a ]{ Γ }>") : C_scope.
Arguments insertE _ _ _ _ _ _ !_ _ !_ / : simpl nomatch.

(** We do not use a setoid equality in the following interfaces to avoid the
need for proofs that the relations and operations are proper. Instead, we
define setoid equality generically [λ X Y, X ⊆ Y ∧ Y ⊆ X]. *)
Class EmptySpec A `{Empty A, SubsetEq A} : Prop := subseteq_empty X : ∅ ⊆@{A} X.
#[global] Instance fin_set_empty_spec `{FinSet A C} : EmptySpec C.
Proof. firstorder auto. Qed.

Class JoinSemiLattice A `{SubsetEq A, Union A}: Prop := {
  join_semi_lattice_pre :> PreOrder (⊆@{A});
  union_subseteq_l (X Y: A) : X ⊆ X ∪ Y;
  union_subseteq_r (X Y: A) : Y ⊆ X ∪ Y;
  union_least (X Y Z: A) : X ⊆ Z → Y ⊆ Z → X ∪ Y ⊆ Z
}.
#[global] Instance fin_set_join_semi_lattice `{FinSet A C}: JoinSemiLattice C.
Proof. firstorder auto. Qed.