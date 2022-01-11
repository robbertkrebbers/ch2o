(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file describes a subset of the C type system. This subset includes
pointer, array, struct, and union types, but omits qualifiers as volatile and
const. Also variable length arrays are omitted from the formalization. *)
From stdpp Require Import fin_maps stringmap mapset.
From Coq Require Import String.
Require Import prelude stringmap.
Require Export type_classes integer_coding.

(** * Tags *)
(** We consider an (unordered) environment to maps tags (struct and union
names) to lists of types corresponding to the fields of structs and unions.
We use the same namespace for structs and unions. *)
Definition tag := string.
Definition tagmap := stringmap.
Notation tagset := (mapset tagmap).

#[global] Instance tag_eq_dec: EqDecision tag. 
Proof. solve_decision. Defined.
#[global] Instance tagmap_dec `{EqDecision A}: EqDecision (tagmap A).
Proof. solve_decision. Defined.
#[global] Instance tagmap_empty {A} : Empty (tagmap A) := @empty (stringmap A) _.
#[global] Instance tagmap_lookup {A} : Lookup tag A (tagmap A) :=
  @lookup _ _ (stringmap A) _.
#[global] Instance tagmap_partial_alter {A} : PartialAlter tag A (tagmap A) :=
  @partial_alter _ _ (stringmap A) _.
#[global] Instance tagmap_to_list {A} : FinMapToList tag A (tagmap A) :=
  @map_to_list _ _ (tagmap A) _.
#[global] Instance tagmap_omap: OMap tagmap := @omap stringmap _.
#[global] Instance tagmap_merge : Merge tagmap := @merge stringmap _.
#[global] Instance tagmap_fmap: FMap tagmap := @fmap stringmap _.
#[global] Instance: FinMap tag tagmap := _.
#[global] Instance tagmap_dom {A} : Dom (tagmap A) tagset := mapset_dom.
#[global] Instance: FinMapDom tag tagmap tagset := mapset_dom_spec.

Typeclasses Opaque tag tagmap.

(** * Function names *)
(** Function names have a separate namespace from structs/unions. *)
Definition funname := string.
Definition funmap := stringmap.
Notation funset := (mapset funmap).

#[global] Instance funname_eq_dec: EqDecision funname.
Proof. solve_decision. Defined.
#[global] Instance funmap_dec {A} `{EqDecision A}: EqDecision (funmap A).
Proof. solve_decision. Defined.
#[global] Instance funmap_empty {A} : Empty (funmap A) := @empty (stringmap A) _.
#[global] Instance funmap_lookup {A} : Lookup funname A (funmap A) :=
  @lookup _ _ (stringmap A) _.
#[global] Instance funmap_partial_alter {A} : PartialAlter funname A (funmap A) :=
  @partial_alter _ _ (stringmap A) _.
#[global] Instance funmap_to_list {A} : FinMapToList funname A (funmap A) :=
  @map_to_list _ _ (funmap A) _.
#[global] Instance funmap_omap: OMap funmap := @omap stringmap _.
#[global] Instance funmap_merge : Merge funmap := @merge stringmap _.
#[global] Instance funmap_fmap: FMap funmap := @fmap stringmap _.
#[global] Instance: FinMap funname funmap := _.
#[global] Instance funmap_dom {A} : Dom (funmap A) funset := mapset_dom.
#[global] Instance: FinMapDom funname funmap funset := mapset_dom_spec.

Typeclasses Opaque funname funmap.

(** * Types *)
(** Types are defined mutually inductively. The type [type] represents the
types of full C types (arrays, structs, unions), and [base_type] describes the
types of values that can occur at the leafs of a full value (integers,
pointers). Structs and unions include a name that refers to their fields in the
environment. *)
Inductive compound_kind := Struct_kind | Union_kind.

Inductive type (K : iType) : iType :=
  | TBase :> base_type K → type K
  | TArray : type K → nat → type K
  | TCompound : compound_kind → tag → type K
with ptr_type (K : iType) : iType :=
  | TType : type K → ptr_type K
  | TAny : ptr_type K
  | TFun : list (type K) → type K → ptr_type K
with base_type (K : iType) : iType :=
  | TVoid : base_type K
  | TInt : int_type K → base_type K
  | TPtr : ptr_type K → base_type K.

Declare Scope ctype_scope.
Declare Scope cptr_type_scope.
Declare Scope cbase_type_scope.
Delimit Scope ctype_scope with T.
Delimit Scope cptr_type_scope with PT.
Delimit Scope cbase_type_scope with BT.
Bind Scope ctype_scope with type.
Bind Scope cptr_type_scope with ptr_type.
Bind Scope cbase_type_scope with base_type.
Local Open Scope ctype_scope.

Arguments TBase {_} _%BT.
Arguments TArray {_} _ _.
Arguments TCompound {_} _ _%string.
Arguments TType {_} _%T.
Arguments TAny {_}.
Arguments TFun {_} _%T _%T.
Arguments TVoid {_}.
Arguments TInt {_} _%IT.
Arguments TPtr {_} _%PT.

Notation "'baseT' τ" := (TBase τ) (at level 10) : ctype_scope.
Notation "'baseT' τ" := (TType (TBase τ)) (at level 10) : cptr_type_scope.
Notation "τ .[ n ]" := (TArray τ n)
  (at level 25, left associativity, format "τ .[ n ]") : ctype_scope.
Notation "τ .[ n ]" := (TType (TArray τ n))
  (at level 25, left associativity, format "τ .[ n ]") : cptr_type_scope.
Notation "'compoundT{' c } s" := (TCompound c s)
  (at level 10, format "'compoundT{' c }  s") : ctype_scope.
Notation "'compoundT{' c } s" := (TType (TCompound c s))
  (at level 10, format "'compoundT{' c }  s") : cptr_type_scope.
Notation "'structT' s" := (TCompound Struct_kind s) (at level 10) : ctype_scope.
Notation "'structT' s" := (TType (TCompound Struct_kind s))
  (at level 10) : cptr_type_scope.
Notation "'unionT' s" := (TCompound Union_kind s) (at level 10) : ctype_scope.
Notation "'unionT' s" := (TType (TCompound Union_kind s))
  (at level 10) : cptr_type_scope.
Notation "'voidT'" := TVoid : cbase_type_scope.
Notation "'voidT'" := (TBase TVoid) : ctype_scope.
Notation "'intT' τ" := (TInt τ) (at level 10) : cbase_type_scope.
Notation "'intT' τ" := (TBase (TInt τ)) (at level 10) : ctype_scope.
Notation "'intT' τ" := (TType (TBase (TInt τ))) (at level 10) : cptr_type_scope.
Notation "'charT{' K }" := (TInt (charT{K})) : cbase_type_scope.
Notation "'charT'" := (TInt charT) : cbase_type_scope.
Notation "'charT{' K }" := (TBase (charT{K})) : ctype_scope.
Notation "'charT'" := (TBase charT) : ctype_scope.
Notation "'charT{' K }" := (TType (charT{K})) : cptr_type_scope.
Notation "'charT'" := (TType charT) : cptr_type_scope.
Notation "'ucharT'" := (TInt ucharT) : cbase_type_scope.
Notation "'ucharT'" := (TBase ucharT) : ctype_scope.
Notation "'ucharT'" := (TType (TBase ucharT)) : cptr_type_scope.
Notation "'scharT'" := (TInt scharT) : cbase_type_scope.
Notation "'scharT'" := (TBase scharT) : ctype_scope.
Notation "'scharT'" := (TType (TBase scharT)) : cptr_type_scope.
Notation "'uintT'" := (TInt uintT) : cbase_type_scope.
Notation "'uintT'" := (TBase uintT) : ctype_scope.
Notation "'uintT'" := (TType (TBase uintT)) : cptr_type_scope.
Notation "'sintT'" := (TInt sintT) : cbase_type_scope.
Notation "'sintT'" := (TBase sintT) : ctype_scope.
Notation "'sintT'" := (TType (TBase sintT)) : cptr_type_scope.
Notation "'uptrT'" := (TInt uptrT) : cbase_type_scope.
Notation "'uptrT'" := (TBase uptrT) : ctype_scope.
Notation "'uptrT'" := (TType (TBase uptrT)) : cptr_type_scope.
Notation "'sptrT'" := (TInt sptrT) : cbase_type_scope.
Notation "'sptrT'" := (TBase sptrT) : ctype_scope.
Notation "'sptrT'" := (TType (TBase sptrT)) : cptr_type_scope.
Notation "τp .*" := (TPtr τp) (at level 25, format "τp .*") : cbase_type_scope.
Notation "τp .*" := (TBase (τp.*)) (at level 25, format "τp .*") : ctype_scope.
Notation "τp .*" := (TType (TBase (τp.*)))
  (at level 25, format "τp .*") : cptr_type_scope.
Notation "τs ~> τ" := (TFun τs τ) (at level 40) : ctype_scope.

#[global] Instance compound_kind_eq_dec: EqDecision compound_kind.
Proof. solve_decision. Defined.
Section dec.
Context `{EqDecision K}.
Fixpoint type_eq_dec' (τ1 τ2 : type K) : Decision (τ1 = τ2)
with ptr_type_eq_dec' (τp1 τp2 : ptr_type K) : Decision (τp1 = τp2)
with base_type_eq_dec' (τb1 τb2 : base_type K) : Decision (τb1 = τb2).
Proof.
 refine
  match τ1, τ2 with
  | baseT τb1, baseT τb2 => cast_if (decide (τb1 = τb2))
  | τ1.[n1], τ2.[n2] =>
     cast_if_and (decide (n1 = n2)) (decide (τ1 = τ2))
  | compoundT{c1} s1, compoundT{c2} s2 =>
     cast_if_and (decide (c1 = c2)) (decide (s1 = s2))
  | _, _ => right _
  end; try solve_decision; abstract congruence.
 refine
  match τp1, τp2 with
  | TType τ1, TType τ2 => cast_if (decide (τ1 = τ2))
  | TAny, TAny => left _
  | τs1 ~> τ1, τs2 ~> τ2 =>
     cast_if_and (decide (τ1 = τ2)) (decide (τs1 = τs2))
  | _, _ => right _
  end; try solve_decision; abstract congruence.
 refine
  match τb1, τb2 with
  | voidT, voidT => left _
  | intT τi1, intT τi2 => cast_if (decide (τi1 = τi2))
  | τp1.*, τp2.* => cast_if (decide (τp1 = τp2))
  | _, _ => right _
  end%BT; try solve_decision; abstract congruence.
Defined.
#[global] Instance type_eq_dec: EqDecision (type K) := type_eq_dec'.
#[global] Instance ptr_type_eq_dec: EqDecision (ptr_type K) := ptr_type_eq_dec'.
#[global] Instance base_type_eq_dec: EqDecision (base_type K) := base_type_eq_dec'.
End dec.

#[global] Instance maybe_TInt {K} : Maybe (@TInt K) := λ τb,
  match τb with intT τi => Some τi | _ => None end%BT.
#[global] Instance maybe_TPtr {K} : Maybe (@TPtr K) := λ τb,
  match τb with τp.* => Some τp | _ => None end%BT.
#[global] Instance maybe_TBase {K} : Maybe (@TBase K) := λ τ,
  match τ with baseT τb => Some τb | _ => None end.
#[global] Instance maybe_TArray {K} : Maybe2 (@TArray K) := λ τ,
  match τ with τ.[n] => Some (τ,n) | _ => None end.
#[global] Instance maybe_TCompound {K} : Maybe2 (@TCompound K) := λ τ,
  match τ with compoundT{c} t => Some (c,t) | _ => None end.
#[global] Instance maybe_TType {K} : Maybe (@TType K) := λ τ,
  match τ with TType τ => Some τ | _ => None end.
#[global] Instance maybe_TFun {K} : Maybe2 (@TFun K) := λ τ,
  match τ with τs ~> τ => Some (τs,τ) | _ => None end.

(** * Environments *)
Record env (K : iType) : iType := mk_env {
  env_t : tagmap (list (type K));
  env_f : funmap (list (type K) * type K)
}.
Add Printing Constructor env.
Arguments mk_env {_} _ _.
Arguments env_t {_} _.
Arguments env_f {_} _.

#[global] Instance env_subseteq {K} : SubsetEq (env K) := λ Γ1 Γ2,
  env_t Γ1 ⊆ env_t Γ2 ∧ env_f Γ1 ⊆ env_f Γ2.
#[global] Instance env_empty {K} : Empty (env K) := mk_env ∅ ∅.
#[global] Instance env_lookup_compound {K} :
  Lookup tag (list (type K)) (env K) := λ t Γ, env_t Γ !! t.
#[global] Instance env_lookup_fun {K} :
  Lookup funname (list (type K) * type K) (env K) := λ f Γ, env_f Γ !! f.
#[global] Instance env_insert_compound {K} :
    Insert tag (list (type K)) (env K) := λ t τs Γ,
  mk_env (<[t:=τs]>(env_t Γ)) (env_f Γ).
#[global] Instance env_insert_fun {K} :
    Insert funname (list (type K) * type K) (env K) := λ f τsτ Γ,
  mk_env (env_t Γ) (<[f:=τsτ]>(env_f Γ)).
#[global] Instance env_delete_compound {K} :
  Delete tag (env K) := λ t Γ, mk_env (delete t (env_t Γ)) (env_f Γ).
#[global] Instance env_delete_fun {K} :
  Delete funname (env K) := λ f Γ, mk_env (env_t Γ) (delete f (env_f Γ)).

(** * Well-formed types *)
(** Not all pseudo-types are valid C types; in particular circular unions and
structs (like [struct t { struct t x; }]) are not excluded. The predicate
[type_valid Γ] describes that a type is valid with respect to [Γ]. That means,
recursive occurrences of unions and structs are always guarded by a pointer.
The predicate [env_valid] describes that an environment is valid. *)
Section types.
  Context {K : iType} `{EqDecision K}.
  Implicit Types Γ Σ : env K.
  Implicit Types τ : type K.
  Implicit Types τp : ptr_type K.
  Implicit Types τs : list (type K).
  Implicit Types τps : list (ptr_type K).
  Implicit Types τb : base_type K.
  Implicit Types τi : int_type K.
  Implicit Types t : tag.
  Implicit Types f : funname.

  Inductive type_valid' Γ : type K → Prop :=
    | TBase_valid' τb : base_type_valid' Γ τb → type_valid' Γ (baseT τb)
    | TArray_valid' τ n : type_valid' Γ τ → n ≠ 0 → type_valid' Γ (τ.[n])
    | TCompound_valid' c t : is_Some (Γ !! t) → type_valid' Γ (compoundT{c} t)
  with ptr_type_valid' Γ : ptr_type K → Prop :=
    | TAny_ptr_valid' : ptr_type_valid' Γ TAny
    | TBase_ptr_valid' τb :
       base_type_valid' Γ τb → ptr_type_valid' Γ (baseT τb)
    | TArray_ptr_valid' τ n :
       type_valid' Γ τ → n ≠ 0 → ptr_type_valid' Γ (τ.[n])
    | TCompound_ptr_valid' c t : ptr_type_valid' Γ (compoundT{c} t)
    | TFun_ptr_valid' τs τ :
       Forall (ptr_type_valid' Γ) (TType <$> τs) → ptr_type_valid' Γ (TType τ) →
       ptr_type_valid' Γ (τs ~> τ)
  with base_type_valid' Γ : base_type K → Prop :=
    | TVoid_valid' : base_type_valid' Γ voidT
    | TInt_valid' τi : base_type_valid' Γ (intT τi)
    | TPtr_valid' τp : ptr_type_valid' Γ τp → base_type_valid' Γ (τp.*).
  Global Instance type_valid : Valid (env K) (type K) := type_valid'.
  Global Instance ptr_type_valid :
    Valid (env K) (ptr_type K) := ptr_type_valid'.
  Global Instance base_type_valid :
    Valid (env K) (base_type K) := base_type_valid'.

  Lemma TBase_valid Γ τb : ✓{Γ} τb → ✓{Γ} (baseT τb).
  Proof. by constructor. Qed.
  Lemma TArray_valid Γ τ n : ✓{Γ} τ → n ≠ 0 → ✓{Γ} (τ.[n]).
  Proof. by constructor. Qed.
  Lemma TCompound_valid Γ c t : is_Some (Γ !! t) → ✓{Γ} (compoundT{c} t).
  Proof. by constructor. Qed.

  Lemma TAny_ptr_valid Γ : ✓{Γ} TAny.
  Proof. constructor. Qed.
  Lemma TBase_ptr_valid Γ τb : ✓{Γ} τb → ✓{Γ} (baseT τb)%PT.
  Proof. by constructor. Qed.
  Lemma TArray_ptr_valid Γ τ n : ✓{Γ} τ → n ≠ 0 → ✓{Γ} (τ.[n])%PT.
  Proof. by constructor. Qed.
  Lemma TCompound_ptr_valid Γ c t : ✓{Γ} (compoundT{c} t)%PT.
  Proof. by constructor. Qed.
  Lemma TFun_ptr_valid Γ τs τ :
    ✓{Γ}* (TType <$> τs) → ✓{Γ} (TType τ) → ✓{Γ} (τs ~> τ).
  Proof. by constructor. Qed.

  Lemma TVoid_valid Γ : ✓{Γ} voidT%BT.
  Proof. by constructor. Qed.
  Lemma TInt_valid Γ τi : ✓{Γ} (intT τi)%BT.
  Proof. by constructor. Qed.
  Lemma TPtr_valid Γ τp : ✓{Γ} τp → ✓{Γ} (τp.*)%BT.
  Proof. by constructor. Qed.

  Lemma TBase_valid_inv Γ τb : ✓{Γ} (baseT τb) → ✓{Γ} τb.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_valid_inv Γ τ n : ✓{Γ} (τ.[n]) → ✓{Γ} τ ∧ n ≠ 0.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_valid_inv_type Γ τ n : ✓{Γ} (τ.[n]) → ✓{Γ} τ.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_valid_inv_size Γ τ n : ✓{Γ} (τ.[n]) → n ≠ 0.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_ptr_valid_inv_size Γ τ n : ✓{Γ} (TType (τ.[n])) → n ≠ 0.
  Proof. by inversion_clear 1. Qed.
  Lemma TCompound_valid_inv Γ c t : ✓{Γ} (compoundT{c} t) → is_Some (Γ !! t).
  Proof. by inversion_clear 1. Qed.
  Lemma TBase_ptr_valid_inv Γ τb : ✓{Γ} (baseT τb)%PT → ✓{Γ} τb.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_ptr_valid_inv_type Γ τ n : ✓{Γ} (τ.[n])%PT → ✓{Γ} τ.
  Proof. by inversion_clear 1. Qed.
  Lemma TFun_valid_inv Γ τs τ :
    ✓{Γ} (τs ~> τ) → ✓{Γ}* (TType <$> τs) ∧ ✓{Γ} (TType τ).
  Proof. by inversion 1. Qed.
  Lemma TFun_valid_inv_args Γ τs τ : ✓{Γ} (τs ~> τ) → ✓{Γ}* (TType <$> τs).
  Proof. by inversion 1. Qed.
  Lemma TFun_valid_inv_ret Γ τs τ : ✓{Γ} (τs ~> τ) → ✓{Γ} (TType τ).
  Proof. by inversion 1. Qed.
  Lemma TPtr_valid_inv Γ τp : ✓{Γ} (τp.*)%BT → ✓{Γ} τp.
  Proof. by inversion_clear 1. Qed.

  Fixpoint type_valid_dec Γ τ : Decision (✓{Γ} τ)
  with ptr_type_valid_dec Γ τp : Decision (✓{Γ} τp)
  with ptr_type_valid_dec_aux Γ τ : Decision (✓{Γ} (TType τ))
  with base_type_valid_dec Γ τb : Decision (✓{Γ} τb).
  Proof.
   refine
    match τ with
    | baseT τb => cast_if (decide (✓{Γ} τb))
    | τ.[n] => cast_if_and (decide (n ≠ 0)) (decide (✓{Γ} τ))
    | compoundT{c} t => cast_if (decide (is_Some (Γ !! t)))
    end; clear type_valid_dec ptr_type_valid_dec ptr_type_valid_dec_aux
      base_type_valid_dec; abstract first [by constructor | by inversion 1].
   refine
    match τp with
    | TAny => left _
    | TType τ => cast_if (decide (✓{Γ} (TType τ)))
    | τs ~> τ => cast_if_and
       (decide (Forall (ptr_type_valid Γ ∘ TType) τs)) (decide (✓{Γ} (TType τ)))
    end; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec
      ptr_type_valid_dec_aux; abstract (repeat match goal with
        | H : _ |- _ => rewrite <-Forall_fmap in H
        end; first [done|by constructor | by inversion 1]).
   refine
    match τ with
    | baseT τb => cast_if (decide (✓{Γ} τb))
    | τ.[n] => cast_if_and (decide (n ≠ 0)) (decide (✓{Γ} τ))
    | compoundT{_} _ => left _
    end; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec
      ptr_type_valid_dec_aux; abstract first [by constructor | by inversion 1].
   refine
    match τb with
    | τp.* => cast_if (decide (✓{Γ} τp)) | _ => left _
    end%BT; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec
      ptr_type_valid_dec_aux; abstract first [by repeat constructor | by inversion 1].
  Defined.
  #[global] Existing Instance type_valid_dec.
  #[global] Existing Instance base_type_valid_dec.
  #[global] Existing Instance ptr_type_valid_dec.

  Lemma type_valid_inv Γ (P : Prop) τ :
    ✓{Γ} τ →
    match τ with
    | baseT τ => (✓{Γ} τ → P) → P
    | τ.[n] => (✓{Γ} τ → n ≠ 0 → P) → P
    | compoundT{c} t => (is_Some (Γ !! t) → P) → P
    end.
  Proof. destruct 1; eauto. Qed.
  Lemma type_valid_ptr_type_valid Γ τ : ✓{Γ} τ → ✓{Γ} (TType τ).
  Proof. by destruct 1; constructor. Qed.
  Lemma types_valid_ptr_types_valid Γ τs : ✓{Γ}* τs → ✓{Γ}* (TType <$> τs).
  Proof. induction 1; csimpl; eauto using type_valid_ptr_type_valid. Qed.

  Inductive type_complete (Γ : env K) : type K → Prop :=
    | TBase_complete τb : type_complete Γ (baseT τb)
    | TArray_complete τ n : type_complete Γ (τ.[n])
    | TCompound_complete c t :
       is_Some (Γ !! t) → type_complete Γ (compoundT{c} t).
  Global Instance type_complete_dec Γ τ : Decision (type_complete Γ τ).
  Proof.
   refine
    match τ with
    | compoundT{_} t => cast_if (decide (is_Some (Γ !! t))) | _ => left _
    end; abstract first [by constructor|by inversion 1].
  Defined.
  Lemma type_valid_complete Γ τ : ✓{Γ} τ → type_complete Γ τ.
  Proof. by destruct 1; constructor. Qed.
  Lemma type_complete_valid Γ τ : ✓{Γ} (TType τ) → type_complete Γ τ → ✓{Γ} τ.
  Proof. by do 2 inversion 1; constructor. Qed.
  Lemma types_complete_valid Γ τs :
    ✓{Γ}* (TType <$> τs) → Forall (type_complete Γ) τs → ✓{Γ}* τs.
  Proof. induction 2; decompose_Forall; eauto using type_complete_valid. Qed.

  Global Instance: PartialOrder (⊆@{env K}).
  Proof.
    split; [split|].
    * done.
    * intros ??? [??] [??]; split; etransitivity; eauto.
    * by intros [??] [??] [??] [??]; f_equal; eapply map_subseteq_po.
  Qed.
  Lemma env_wf : wf (⊂@{env K}).
  Proof.
    intros [Γc Γf]; revert Γf. induction (map_wf Γc) as [Γc _ IH]; intros Γf.
    induction (map_wf Γf) as [Γf _ IHf]; constructor; intros [Γc' Γf'] HΓ.
    cut (Γc' ⊂ Γc ∨ Γc' = Γc ∧ Γf' ⊂ Γf); [intros [?|[-> ?]]; eauto|].
    destruct HΓ as [[??] HΓ];
      destruct (map_subseteq_inv_L Γc' Γc); simplify_equality'; auto.
    right; repeat split; auto. by contradict HΓ.
  Qed.
  Lemma lookup_compound_weaken Γ1 Γ2 t τs :
    Γ1 !! t = Some τs → Γ1 ⊆ Γ2 → Γ2 !! t = Some τs.
  Proof. by intros ? [??]; apply (lookup_weaken (env_t Γ1)). Qed.
  Lemma lookup_fun_weaken Γ1 Γ2 f τs τ :
    Γ1 !! f = Some (τs,τ) → Γ1 ⊆ Γ2 → Γ2 !! f = Some (τs,τ).
  Proof. by intros ? [??]; apply (lookup_weaken (env_f Γ1)). Qed.
  Lemma lookup_compound_weaken_is_Some Γ1 Γ2 t :
    is_Some (Γ1 !! t) → Γ1 ⊆ Γ2 → is_Some (Γ2 !! t).
  Proof. intros [τs ?] ?; exists τs; eauto using lookup_compound_weaken. Qed.
  Lemma lookup_insert_compound Γ t τs : <[t:=τs]>Γ !! t = Some τs.
  Proof. apply lookup_insert. Qed.
  Lemma lookup_insert_compound_ne Γ t t' τs :
    t ≠ t' → <[t:=τs]>Γ !! t' = Γ !! t'.
  Proof. apply (lookup_insert_ne (env_t Γ)). Qed.
  Lemma lookup_fun_compound Γ f τs τ : <[f:=(τs,τ)]>Γ !! f = Some (τs,τ).
  Proof. apply lookup_insert. Qed.
  Lemma lookup_fun_compound_ne Γ f f' τs τ :
    f ≠ f' → <[f:=(τs,τ)]>Γ !! f' = Γ !! f'.
  Proof. apply (lookup_insert_ne (env_f Γ)). Qed.
  Lemma insert_fun_id Γ f τsτ : Γ !! f = Some τsτ → <[f:=τsτ]>Γ = Γ.
  Proof.
    destruct Γ; intros; unfold insert, env_insert_fun; f_equal'.
    by apply insert_id.
  Qed.
  Lemma delete_compound_subseteq_compat Γ1 Γ2 t :
    Γ1 ⊆ Γ2 → delete t Γ1 ⊆ delete t Γ2.
  Proof. intros []; split. by apply delete_mono. done. Qed.
  Lemma delete_compound_subseteq Γ t : is_Some (Γ !! t) → delete t Γ ⊆ Γ.
  Proof. split. apply delete_subseteq. done. Qed.
  Lemma delete_compound_subset Γ t : is_Some (Γ !! t) → delete t Γ ⊂ Γ.
  Proof.
    split; [by apply delete_compound_subseteq|].
    intros [??]. by destruct (delete_subset (env_t Γ) t).
  Qed.
  Lemma delete_compound_subset_alt Γ t τs : Γ !! t = Some τs → delete t Γ ⊂ Γ.
  Proof. eauto using delete_compound_subset. Qed.
  Lemma insert_compound_subseteq Γ t τs : Γ !! t = None → Γ ⊆ <[t:=τs]> Γ.
  Proof. split. by apply insert_subseteq. done. Qed.
  Lemma insert_fun_subseteq Γ f τs τ : Γ !! f = None → Γ ⊆ <[f:=(τs,τ)]> Γ.
  Proof. split. done. by apply insert_subseteq. Qed.

  Lemma type_valid_weaken_help Γ1 Γ2 τ :
    ✓{Γ1} τ → env_t Γ1 ⊆ env_t Γ2 → ✓{Γ2} τ
  with ptr_type_valid_weaken_help Γ1 Γ2 τp :
    ✓{Γ1} τp → env_t Γ1 ⊆ env_t Γ2 → ✓{Γ2} τp
  with base_type_valid_weaken_help Γ1 Γ2 τb :
    ✓{Γ1} τb → env_t Γ1 ⊆ env_t Γ2 → ✓{Γ2} τb.
  Proof.
    * unfold valid, base_type_valid, type_valid in *.
      destruct 1; constructor; eauto.
      eapply (lookup_weaken_is_Some (env_t _)); eauto.
    * unfold valid, base_type_valid, type_valid, ptr_type_valid in *.
      destruct 1; econstructor; eauto using Forall_impl.
    * unfold valid, base_type_valid, ptr_type_valid, type_valid in *.
      destruct 1; econstructor; eauto.
  Qed.
  Lemma type_valid_weaken Γ1 Γ2 τ : ✓{Γ1} τ → Γ1 ⊆ Γ2 → ✓{Γ2} τ.
  Proof. intros ? [??]; eapply type_valid_weaken_help; eauto. Qed.
  Lemma ptr_type_valid_weaken Γ1 Γ2 τp : ✓{Γ1} τp → Γ1 ⊆ Γ2 → ✓{Γ2} τp.
  Proof. intros ? [??]; eapply ptr_type_valid_weaken_help; eauto. Qed.
  Lemma base_type_valid_weaken Γ1 Γ2 τb : ✓{Γ1} τb → Γ1 ⊆ Γ2 → ✓{Γ2} τb.
  Proof. intros ? [??]; eapply base_type_valid_weaken_help; eauto. Qed.
  Lemma type_valid_strict_weaken Γ Σ τ  : ✓{Γ} τ → Γ ⊂ Σ → ✓{Σ} τ.
  Proof. intros. eapply type_valid_weaken, strict_include; eauto. Qed.
  Lemma types_valid_weaken Γ Σ τs : ✓{Γ}* τs → Γ ⊆ Σ → ✓{Σ}* τs.
  Proof. eauto using Forall_impl, type_valid_weaken. Qed.
  Lemma ptr_types_valid_weaken Γ Σ τps : ✓{Γ}* τps → Γ ⊆ Σ → ✓{Σ}* τps.
  Proof. eauto using Forall_impl, ptr_type_valid_weaken. Qed.
  Lemma types_valid_strict_weaken Γ Σ τs : ✓{Γ}* τs → Γ ⊂ Σ → ✓{Σ}* τs.
  Proof. eauto using Forall_impl, type_valid_strict_weaken. Qed.
  Lemma type_complete_weaken Γ Σ τ : type_complete Γ τ → Γ ⊆ Σ → type_complete Σ τ.
  Proof.
    intros [] [??]; constructor; eauto.
    eapply (lookup_weaken_is_Some (env_t _)); eauto.
  Qed.
  Lemma types_complete_weaken Γ Σ τs :
    Forall (type_complete Γ) τs → Γ ⊆ Σ → Forall (type_complete Σ) τs.
  Proof. induction 1; eauto using type_complete_weaken. Qed.

  Inductive env_valid : Valid () (env K) :=
    | env_empty_valid : ✓ ∅
    | env_insert_compound_valid Γ t τs :
       ✓ Γ → ✓{Γ}* τs → τs ≠ [] → Γ !! t = None → ✓ (<[t:=τs]>Γ)
    | env_insert_fun_valid Γ f τs τ :
       ✓ Γ → ✓{Γ}* (TType <$> τs) → ✓{Γ} (TType τ) →
       Γ !! f = None → ✓ (<[f:=(τs,τ)]>Γ).
  #[global] Existing Instance env_valid.

  Lemma env_valid_delete Γ t τs :
    ✓ Γ → Γ !! t = Some τs → ∃ Γ', Γ' ⊆ delete t Γ ∧ ✓{Γ'}* τs ∧ τs ≠ [] ∧ ✓ Γ'.
  Proof.
    intros HΓ Ht. induction HΓ
      as [|Γ t' τs' HΓ IH Hτs' Hlen|Γ f τs' τ' ? IH]; [done| |].
    { destruct (decide (t = t')) as [->|].
      { rewrite lookup_insert_compound in Ht. simplify_equality'.
        by exists Γ; repeat split; simpl; rewrite ?delete_insert by done. }
      rewrite lookup_insert_compound_ne in Ht by done.
      destruct IH as (Γ'&?&?&?&?); auto; exists Γ'; split_and ?; auto.
      transitivity (delete t Γ);
        auto using delete_compound_subseteq_compat, insert_compound_subseteq. }
    destruct (IH Ht) as (Γ'&?&?&?&?). exists Γ'; split_and ?; auto.
    transitivity (delete t Γ);
      auto using delete_compound_subseteq_compat, insert_fun_subseteq.
  Qed.
  Lemma env_valid_lookup_subset Γ t τs :
    ✓ Γ → Γ !! t = Some τs → ∃ Γ', Γ' ⊂ Γ ∧ ✓{Γ'}* τs ∧ τs ≠ [] ∧ ✓ Γ'.
  Proof.
    intros. destruct (env_valid_delete Γ t τs) as (Γ'&?&?&?&?); auto.
    exists Γ'; split_and ?; auto.
    eapply strict_transitive_r; eauto using delete_compound_subset.
  Qed.
  Lemma env_valid_lookup Γ t τs : ✓ Γ → Γ !! t = Some τs → ✓{Γ}* τs.
  Proof.
    intros. destruct (env_valid_lookup_subset Γ t τs) as (?&?&?&?);
      eauto using types_valid_strict_weaken.
  Qed.
  Lemma env_valid_lookup_lookup Γ t τs i τ : 
    ✓ Γ → Γ !! t = Some τs → τs !! i = Some τ → ✓{Γ} τ.
  Proof.
    intros ? Ht Hi. eapply Forall_lookup_1, Hi; eauto using env_valid_lookup.
  Qed.
  Lemma env_valid_lookup_singleton Γ t τ : ✓ Γ → Γ !! t = Some [τ] → ✓{Γ} τ.
  Proof. intros. by apply (env_valid_lookup_lookup Γ t [τ] 0 τ). Qed.
  Lemma env_valid_fun_valid Γ f τs τ :
    ✓ Γ → Γ !! f = Some (τs,τ) → ✓{Γ}* (TType <$> τs) ∧ ✓{Γ} (TType τ).
  Proof.
    intros HΓ Hf. induction HΓ as [| |Γ f' τs' τ' ? IH]; [done| |].
    { naive_solver eauto using ptr_type_valid_weaken,
        ptr_types_valid_weaken, insert_compound_subseteq. }
    destruct (decide (f = f')) as [->|];
      rewrite ?lookup_fun_compound, ?lookup_fun_compound_ne in Hf by done;
      naive_solver eauto using ptr_type_valid_weaken,
        ptr_types_valid_weaken, insert_fun_subseteq.
  Qed.
  Lemma env_valid_args_valid Γ f τs τ :
    ✓ Γ → Γ !! f = Some (τs,τ) → ✓{Γ}* (TType <$> τs).
  Proof. eapply env_valid_fun_valid. Qed.
  Lemma env_valid_ret_valid Γ f τs τ :
    ✓ Γ → Γ !! f = Some (τs,τ) → ✓{Γ} (TType τ).
  Proof. eapply env_valid_fun_valid. Qed.
End types.

(** A very inefficient decision procedure for wellformedness of environments.
It checks wellformedness by trying all permutations of the environment. This
decision procedure is not intended to be used for computation. *)
Section env_valid_dec.
  Context {K : iType}.

  Definition env_f_valid (Γ : env K) : Prop :=
    map_Forall (λ _ τsτ,
      ✓{Γ}* (TType <$> τsτ.1) ∧ ✓{Γ} (TType (τsτ.2))) (env_f Γ).
  Inductive env_c_valid : list (tag * list (type K)) → Prop :=
    | env_nil_valid : env_c_valid []
    | env_cons_valid Γc t τs :
       env_c_valid Γc → ✓{mk_env (list_to_map Γc) ∅}* τs →
       τs ≠ [] → t ∉ (Γc.*1) → env_c_valid ((t,τs) :: Γc).
  Lemma env_c_valid_nodup Γc : env_c_valid Γc → NoDup (Γc.*1).
  Proof. by induction 1; csimpl; constructor. Qed.
  Global Instance env_c_valid_dec : ∀ Γc, Decision (env_c_valid Γc).
  Proof.
   refine (
    fix go Γc :=
    match Γc return Decision (env_c_valid Γc) with
    | [] => left _
    | (s,τs) :: Γc => cast_if_and4
       (decide (✓{mk_env (list_to_map Γc) ∅}* τs))
       (decide (τs ≠ [])) (decide (s ∉ Γc.*1)) (go Γc)
    end); clear go; first [by constructor |by inversion 1].
  Defined.
  Lemma env_c_valid_correct Γ :
    ✓ Γ ↔ env_f_valid Γ ∧ ∃ Γc, map_to_list (env_t Γ) ≡ₚ Γc ∧ env_c_valid Γc.
  Proof.
    split.
    * intros HΓ; split.
      { intros ? [??]; split;
          eauto using env_valid_args_valid, env_valid_ret_valid. }
      induction HΓ as [|Γ t τs ? (Γc&HΓ&?)|Γ f τs τ ? (Γc&HΓ&?)]; simpl; eauto.
      { eexists []. rewrite map_to_list_empty; by repeat constructor. }
      exists ((t,τs) :: Γc); split; [by rewrite map_to_list_insert, HΓ by done|].
      constructor; auto.
      { erewrite <-list_to_map_flip by eauto.
        eauto using Forall_impl, type_valid_weaken_help. }
      by erewrite not_elem_of_list_to_map, <-list_to_map_flip by eauto.
    * destruct Γ as [Γc Γf]; simpl; intros (HΓf&Γc'&HΓc&HΓc').
      assert (✓ (mk_env Γc ∅)).
      { erewrite (list_to_map_flip Γc) by eauto; clear Γc HΓc HΓf.
        induction HΓc' as [|Γc t τs ? IH]; simpl; [by constructor|].
        change (✓ (<[t:=τs]> (mk_env (list_to_map Γc) ∅))); constructor; auto.
        by apply not_elem_of_list_to_map. }
      clear Γc' HΓc HΓc'. revert HΓf. unfold env_f_valid; simpl.
      generalize Γf at 1 2; intros Γf'; revert Γf.
      refine (map_Forall_ind _ _ _ _); [done|].
      intros Γf f [τs τ] ? [] ??; simpl in *.
      change (✓ (<[f:=(τs,τ)]> (mk_env Γc Γf)));
        constructor; eauto using Forall_impl, ptr_type_valid_weaken_help.
  Qed.
  Lemma env_c_valid_correct_alt Γ :
    ✓ Γ ↔
      env_f_valid Γ ∧ Exists env_c_valid (permutations (map_to_list (env_t Γ))).
  Proof.
    rewrite env_c_valid_correct, Exists_exists.
    by setoid_rewrite permutations_Permutation.
  Qed.
  Global Instance env_valid_dec (Γ : env K) : Decision (✓ Γ).
  Proof.
   refine (cast_if (decide (env_f_valid Γ ∧
     Exists env_c_valid (permutations (map_to_list (env_t Γ))))));
     by rewrite env_c_valid_correct_alt.
  Defined.
End env_valid_dec.

(** A nice induction principle for wellformed types. *)
Section type_env_ind.
  Context {K : iType} `{EqDecision K}.
  Context (Γ : env K) (HΓ : ✓ Γ).

  Context (P : type K → Prop).
  Context (Pbase : ∀ τb, ✓{Γ} τb → P (baseT τb)).
  Context (Parray : ∀ τ n, ✓{Γ} τ → P τ → n ≠ 0 → P (τ.[n])).
  Context (Pcompound : ∀ c t τs,
    Γ !! t = Some τs → ✓{Γ}* τs → Forall P τs →
    τs ≠ [] → P (compoundT{c} t)).

  Lemma type_env_ind: ∀ τ, ✓{Γ} τ → P τ.
  Proof.
    cut (∀ Γ' τ, Γ' ⊆ Γ → ✓ Γ' → ✓{Γ'} τ → P τ).
    { intros help τ. by apply help. }
    induction Γ' as [Γ' IH] using (well_founded_induction env_wf).
    intros τ HΣΓ HΣ Hτ. induction Hτ as [τb Hτb|τ n Hτ|c t Ht].
    * by apply Pbase, (base_type_valid_weaken Γ').
    * apply Parray; eauto. by apply (type_valid_weaken Γ').
    * inversion Ht as [τs Hτs].
      destruct (env_valid_lookup_subset Γ' t τs) as (Γ''&?&Hτs'&Hlen&?); auto.
      assert (Γ'' ⊂ Γ) by eauto using (strict_transitive_l (R:=(⊆@{env K}))).
      apply Pcompound with τs; eauto using lookup_compound_weaken.
      + apply Forall_impl with (✓{Γ''}); auto.
        intros. eapply type_valid_strict_weaken; eauto.
      + clear Hτs Hlen. induction Hτs'; constructor; auto.
        apply (IH Γ''); eauto using (strict_include (R:=(⊆):relation (env _))).
  Qed.
End type_env_ind.

(** A nice iteration principle for well-formed types. *)
Section type_iter.
  Context {K : iType} `{EqDecision K}.
  Context {A : Type} (R : relation A) `{!Equivalence R}.
  Local Infix "≡" := R.
  Implicit Type τ : type K.
  Implicit Type Γ Σ : env K.

  Section definition.
    Context (fb : base_type K → A)
      (fa : type K → nat → A → A)
      (fc: compound_kind → tag → list (type K) → (type K → A) → A).

    Definition type_iter_inner
        (g : tag → list (type K) * (type K → A)) : type K → A :=
      fix go τ :=
      match τ with
      | baseT τb => fb τb
      | τ.[n] => fa τ n (go τ)
      | compoundT{c} t => let (τs,h) := g t in fc c t τs h
      end.
    Definition type_iter_accF (Γ : env K) (go : ∀ Σ, Σ ⊂ Γ → type K → A)
        (t : tag) : list (type K) * (type K → A) :=
      match Some_dec (Γ !! t) with
      | inleft (τs↾Hτs) => (τs, go (delete t Γ)
          (delete_compound_subset_alt _ _ _ Hτs))
      | inright _ => ([], λ _, fb voidT) (**i dummy *)
      end.
    Definition type_iter_acc : ∀ Γ : env K, Acc (⊂) Γ → type K → A :=
      Fix_F _ (λ Γ go, type_iter_inner (type_iter_accF Γ go)).
    Definition type_iter (Γ : env K) : type K → A :=
      type_iter_acc _ (wf_guard 32 env_wf Γ).
  End definition.

  Lemma type_iter_acc_weaken fb1 fb2 fa1 fa2 fc1 fc2 Γ Γ1 Γ2 acc1 acc2 τ :
    ✓ Γ →
    (∀ τb, ✓{Γ} τb → fb1 τb ≡ fb2 τb) →
    (∀ τ n x y, ✓{Γ} τ → x ≡ y → fa1 τ n x ≡ fa2 τ n y) →
    (∀ rec1 rec2 c t τs,
      Γ !! t = Some τs → ✓{Γ}* τs → Forall (λ τ, rec1 τ ≡ rec2 τ) τs →
      fc1 c t τs rec1 ≡ fc2 c t τs rec2) →
    ✓{Γ} τ → Γ ⊆ Γ1 → Γ ⊆ Γ2 →
    type_iter_acc fb1 fa1 fc1 Γ1 acc1 τ ≡ type_iter_acc fb2 fa2 fc2 Γ2 acc2 τ.
  Proof.
    intros HΓ Hbase Harray. revert Γ1 Γ2 acc1 acc2 τ HΓ.
    induction Γ as [Γ IH] using (well_founded_induction env_wf).
    intros Γ1 Γ2 [acc1] [acc2] τ HΓ Hcompound Hτ HΓ1 HΓ2. simpl.
    induction Hτ as [τ Hτ|τ n Hτ|c t [τs Ht]]; simpl; try reflexivity; auto.
    assert (Γ1 !! t = Some τs) by eauto using lookup_compound_weaken.
    assert (Γ2 !! t = Some τs) by eauto using lookup_compound_weaken.
    unfold type_iter_accF.
    destruct (Some_dec (Γ1 !! t)) as [[τs1 Ht1]|?],
      (Some_dec (Γ2 !! t)) as [[τs2 Ht2]|?]; simplify_equality'.
    generalize (acc1 _ (delete_compound_subset_alt Γ1 t τs1 Ht1)),
      (acc2 _ (delete_compound_subset_alt Γ2 t τs1 Ht2)); intros acc1' acc2'.
    destruct (env_valid_delete Γ t τs1) as (Γ'&?&Hτs&Hlen&?); trivial.
    assert (Γ' ⊆ Γ).
    { transitivity (delete t Γ); eauto using delete_compound_subseteq. }
    apply Hcompound; eauto using types_valid_weaken.
    assert (is_Some (Γ !! t)) by eauto. clear Ht Ht1 Ht2 Hlen acc1 acc2.
    induction Hτs as [|τ τs]; constructor; auto. apply (IH Γ').
    * eauto using (strict_transitive_r (R:=(⊆@{env K}))),
        delete_compound_subset, lookup_compound_weaken_is_Some.
    * eauto using base_type_valid_weaken.
    * eauto using type_valid_weaken.
    * done.
    * eauto using lookup_compound_weaken, types_valid_weaken.
    * done.
    * transitivity (delete t Γ); eauto using delete_compound_subseteq_compat.
    * transitivity (delete t Γ); eauto using delete_compound_subseteq_compat.
  Qed.
  Lemma type_iter_weaken fb1 fb2 fa1 fa2 fc1 fc2 Γ Σ τ :
    ✓ Γ →
    (∀ τb, ✓{Γ} τb → fb1 τb ≡ fb2 τb) →
    (∀ τ n x y, ✓{Γ} τ → x ≡ y → fa1 τ n x ≡ fa2 τ n y) →
    (∀ rec1 rec2 c t τs,
      Γ !! t = Some τs → ✓{Γ}* τs → Forall (λ τ, rec1 τ ≡ rec2 τ) τs →
      fc1 c t τs rec1 ≡ fc2 c t τs rec2) →
    ✓{Γ} τ → Γ ⊆ Σ →
    type_iter fb1 fa1 fc1 Γ τ ≡ type_iter fb2 fa2 fc2 Σ τ.
  Proof. intros. by apply (type_iter_acc_weaken _ _ _ _ _ _ Γ). Qed.

  Lemma type_iter_base fb fa fc Γ τb : type_iter fb fa fc Γ (baseT τb) = fb τb.
  Proof. done. Qed.
  Lemma type_iter_array fb fa fc Γ τ n :
    type_iter fb fa fc Γ (τ.[n]) = fa τ n (type_iter fb fa fc Γ τ).
  Proof. unfold type_iter. by destruct (wf_guard _ env_wf Γ). Qed.
  Lemma type_iter_compound fb fa fc Γ c t τs :
    ✓ Γ → (∀ τ n x y, ✓{Γ} τ → x ≡ y → fa τ n x ≡ fa τ n y) →
    (∀ rec1 rec2 c t τs,
      Γ !! t = Some τs → ✓{Γ}* τs → Forall (λ τ, rec1 τ ≡ rec2 τ) τs →
      fc c t τs rec1 ≡ fc c t τs rec2) →
    Γ !! t = Some τs →
    type_iter fb fa fc Γ (compoundT{c} t) ≡ fc c t τs (type_iter fb fa fc Γ).
  Proof.
    intros ? Harray Hcompound Ht. unfold type_iter at 1.
    destruct (wf_guard _ env_wf Γ) as [accΓ]. simpl.
    unfold type_iter_accF.
    destruct (Some_dec (Γ !! t)) as [[τs' Ht']|?]; [|congruence].
    generalize (accΓ _ (delete_compound_subset_alt Γ t τs' Ht')). intros accΓ'.
    simplify_map_eq.
    destruct (env_valid_delete Γ t τs) as (Γ'&?&Hτs&Hlen&?); trivial.
    assert (Γ' ⊆ Γ).
    { transitivity (delete t Γ); eauto using delete_compound_subseteq. }
    apply Hcompound; eauto using types_valid_weaken.
    clear Ht Hlen. induction Hτs; constructor; auto.
    by apply (type_iter_acc_weaken _ _ _ _ _ _ Γ');
      eauto using lookup_compound_weaken, type_valid_weaken, types_valid_weaken.
  Qed.
  Lemma type_iter_compound_None fb fa fc Γ c t :
    Γ !! t = None →
    type_iter fb fa fc Γ (compoundT{c} t) = fc c t [] (λ _, fb voidT%BT).
  Proof.
    intros Ht. unfold type_iter.
    destruct (wf_guard _ env_wf Γ) as [accΓ]; simpl.
    unfold type_iter_accF. destruct (Some_dec _) as [[??]|?]; congruence.
  Qed.
End type_iter.
