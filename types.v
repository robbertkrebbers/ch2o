(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file describes a subset of the C type system. This subset includes
pointer, array, struct, and union types, but omits qualifiers as volatile and
const. Also variable length arrays are omitted from the formalization. *)
Require Import nmap mapset.
Require Export prelude abstract_integers fin_maps.

(** * Tags *)
(** We use a named approach to represent unions and structs. We consider an
(unordered) environment that is indexed by tags corresponding to the names
of structs and unions, and which assigns a list of types corresponding to the
fields of these structs and unions. We use the same namespace for structs and
unions. *)
(** We define tags as binary naturals and use the [Nmap] implementation to
obtain efficient finite maps and finite sets with these indexes as keys. *)
Definition tag := N.
Definition tagmap := Nmap.
Notation tagset := (mapset tagmap).

Instance tag_eq_dec: ∀ i1 i2: tag, Decision (i1 = i2) := decide_rel (=).
Instance tag_fresh `{FinCollection tag C} : Fresh tag C := _.
Instance tag_fresh_spec `{FinCollection tag C} :
  FreshSpec tag C := _.

Instance tagmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : tagmap A, Decision (m1 = m2) := decide_rel (=).
Instance tagmap_empty {A} : Empty (tagmap A) := @empty (Nmap A) _.
Instance tagmap_lookup {A} : Lookup tag A (tagmap A) :=
  @lookup _ _ (Nmap A) _.
Instance tagmap_partial_alter {A} : PartialAlter tag A (tagmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance tagmap_to_list {A} : FinMapToList tag A (tagmap A) :=
  @map_to_list _ _ (tagmap A) _.
Instance tagmap_merge : Merge tagmap := @merge Nmap _.
Instance tagmap_fmap: FMap tagmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap tag tagmap := _.

Instance tagmap_dom {A} : Dom (tagmap A) tagset := mapset_dom.
Instance: FinMapDom tag tagmap tagset := mapset_dom_spec.

Instance tag_lexico : Lexico tag := @lexico N _.
Instance tag_lexico_po : PartialOrder (@lexico tag _) := _.
Instance tag_trichotomy: TrichotomyT (@lexico tag _) := _.

Typeclasses Opaque tag tagmap.

(** * Types *)
(** Types are defined mutually inductively. The type [type] represents the
types of full C types (arrays, structs, unions), and [base_type] describes the
types of values that can occur at the leafs of a full value (integers,
pointers). Structs and unions include a name that refers to their fields in the
environment. *)
Inductive compound_kind := Struct | Union.

Inductive type (Ti : Set) :=
  | TBase :> base_type Ti → type Ti
  | TVoid : type Ti
  | TArray : type Ti → nat → type Ti
  | TCompound : compound_kind → tag → type Ti
with base_type (Ti : Set) :=
  | TInt : int_type Ti → base_type Ti
  | TPtr : type Ti → base_type Ti.

Delimit Scope ctype_scope with T.
Delimit Scope cbase_type_scope with BT.
Bind Scope ctype_scope with type.
Bind Scope cbase_type_scope with base_type.

Arguments TBase {_} _%BT.
Arguments TVoid {_}.
Arguments TArray {_} _ _.
Arguments TCompound {_} _ _.
Arguments TInt {_} _%IT.
Arguments TPtr {_} _%T.

Notation "'base' τ" := (TBase τ) (at level 10) : ctype_scope.
Notation "'void'" := TVoid : ctype_scope.
Notation "τ .[ n ]" := (TArray τ n)
  (at level 25, left associativity, format "τ .[ n ]") : ctype_scope.
Notation "'compound' @{ c } s" := (TCompound c s)
  (at level 10, format "'compound' @{ c }  s") : ctype_scope.
Notation "'struct' s" := (TCompound Struct s) (at level 10) : ctype_scope.
Notation "'union' s" := (TCompound Union s) (at level 10) : ctype_scope.
Notation "'intt' τ" := (TInt τ) (at level 10) : cbase_type_scope.
Notation "'intt' τ" := (TBase (intt τ)) (at level 10) : ctype_scope.
Notation "'uchar'" := (TInt uchar) : cbase_type_scope.
Notation "'uchar'" := (TBase uchar) : ctype_scope.
Notation "'schar'" := (TInt schar) : cbase_type_scope.
Notation "'schar'" := (TBase schar) : ctype_scope.
Notation "'uint'" := (TInt uint) : cbase_type_scope.
Notation "'uint'" := (TBase uint) : ctype_scope.
Notation "'sint'" := (TInt sint) : cbase_type_scope.
Notation "'sint'" := (TBase sint) : ctype_scope.
Notation "'uptr'" := (TInt uptr) : cbase_type_scope.
Notation "'uptr'" := (TBase uptr) : ctype_scope.
Notation "'sptr'" := (TInt sptr) : cbase_type_scope.
Notation "'sptr'" := (TBase sptr) : ctype_scope.
Notation "τ .*" := (TPtr τ) (at level 25, format "τ .*") : cbase_type_scope.
Notation "τ .*" := (TBase (τ.*)) (at level 25, format "τ .*") : ctype_scope.

Notation env Ti := (tagmap (list (type Ti))).

Instance compound_kind_eq_dec (c1 c2 : compound_kind) : Decision (c1 = c2).
Proof. solve_decision. Defined.
Fixpoint type_eq_dec {Ti : Set} {dec : ∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}
  (τ1 τ2 : type Ti) : Decision (τ1 = τ2)
with base_type_eq_dec {Ti : Set} {dec : ∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}
  (τ1 τ2 : base_type Ti) : Decision (τ1 = τ2).
Proof.
 refine
  match τ1, τ2 with
  | base τ1, base τ2 => cast_if (decide_rel (=) τ1 τ2)
  | void, void => left _
  | τ1.[n1], τ2.[n2] =>
     cast_if_and (decide_rel (=) n1 n2) (decide_rel (=) τ1 τ2)
  | compound@{c1} s1, compound@{c2} s2 =>
     cast_if_and (decide_rel (=) c1 c2) (decide_rel (=) s1 s2)
  | _, _ => right _
  end%T; clear base_type_eq_dec type_eq_dec; abstract congruence.
 refine
  match τ1, τ2 with
  | intt τ1, intt τ2 => cast_if (decide_rel (=) τ1 τ2)
  | τ1.*, τ2.* => cast_if (decide_rel (=) τ1 τ2)
  | _, _ => right _
  end%BT; clear base_type_eq_dec type_eq_dec; abstract congruence.
Defined.
Existing Instance type_eq_dec.
Existing Instance base_type_eq_dec.

Inductive is_TArray {Ti} : type Ti → Prop :=
  TArray_is_TArray τ n : is_TArray (τ.[n]).
Instance is_TArray_dec {Ti} (τ : type Ti) : Decision (is_TArray τ).
Proof.
 refine match τ with τ.[_] => left _ | _ => right _ end%T;
  first [constructor | abstract by inversion 1].
Defined.

Definition array_elem {Ti} (τ : type Ti) : type Ti :=
  match τ with τ.[n] => τ | _ => τ end%T.
Definition array_size {Ti} (τ : type Ti) : nat :=
  match τ with _.[n] => n | _ => 1 end%T.

(** Some useful type classes to get nice overloaded notations for the different
kinds of values that we will consider. *)
Class Typed (M T V : Type) := typed: M → V → T → Prop.
Notation "m ⊢ v : τ" := (typed m v τ) (at level 74, v at level 50) : C_scope.
Notation "m ⊢* vs :* τs" := (Forall2 (typed m) vs τs)
  (at level 74, vs at level 70) : C_scope.
Notation "m ⊢* vs : τ" := (Forall (λ v, m ⊢ v : τ) vs)
  (at level 74, vs at level 70) : C_scope.
Class PathTyped (T R : Type) := path_typed: T → R → T → Prop.
Notation "p @ τ ↣ σ" := (path_typed τ p σ) (at level 70) : C_scope.

Class TypeCheck (M T V : Type) := type_check: M → V → option T.
Arguments type_check {_ _ _ _} _ !_ / : simpl nomatch.
Class TypeCheckSpec (M T V : Type) `{Typed M T V} `{TypeCheck M T V} :=
  type_check_correct m x τ : type_check m x = Some τ ↔ m ⊢ x : τ.

Class TypeOf (T V : Type) := type_of: V → T.
Arguments type_of {_ _ _} !_ / : simpl nomatch.
Class TypeOfSpec (M T V : Type) `{Typed M T V} `{TypeOf T V} :=
  type_of_correct m x τ : m ⊢ x : τ → type_of x = τ.
Class PathTypeCheckSpec (T R : Type) `{PathTyped T R} `{Lookup R T T} :=
  path_type_check_correct p τ σ : τ !! p = Some σ ↔ p @ τ ↣ σ.

Section typed.
  Context `{Typed M T V}.

  Lemma Forall2_Forall_typed m vs τs τ :
    m ⊢* vs :* τs → Forall (=τ) τs → m ⊢* vs : τ.
  Proof. induction 1; inversion 1; subst; eauto. Qed.
End typed.

Section type_check.
  Context `{TypeCheckSpec M T V}.

  Lemma type_check_None m x τ : type_check m x = None → ¬m ⊢ x : τ.
  Proof. rewrite <-type_check_correct. congruence. Qed.
  Lemma type_check_sound m x τ : type_check m x = Some τ → m ⊢ x : τ.
  Proof. by rewrite type_check_correct. Qed.
  Lemma type_check_complete m x τ : m ⊢ x : τ → type_check m x = Some τ.
  Proof. by rewrite type_check_correct. Qed.
  Lemma typed_unique m x τ1 τ2 : m ⊢ x : τ1 → m ⊢ x : τ2 → τ1 = τ2.
  Proof. rewrite <-!type_check_correct. congruence. Qed.

  Context `{∀ τ1 τ2 : T, Decision (τ1 = τ2)}.
  Global Instance typed_dec m x τ : Decision (m ⊢ x : τ).
  Proof.
   refine (
    match Some_dec (type_check m x) with
    | inleft (τ'↾_) => cast_if (decide (τ = τ'))
    | inright _ => right _
    end); abstract (rewrite <-type_check_correct; congruence).
  Defined.
End type_check.

Section type_of.
  Context `{TypeOfSpec M T V}.

  Lemma type_of_typed m x τ : m ⊢ x : τ → m ⊢ x : type_of x.
  Proof. intros. erewrite type_of_correct; eauto. Qed.
  Lemma typed_unique_alt m x τ1 τ2 : m ⊢ x : τ1 → m ⊢ x : τ2 → τ1 = τ2.
  Proof.
    intros Hτ1 Hτ2. apply type_of_correct in Hτ1. apply type_of_correct in Hτ2.
    congruence.
  Qed.
  Lemma fmap_type_of m vs τs : m ⊢* vs :* τs → type_of <$> vs = τs.
  Proof. induction 1; simpl; f_equal; eauto using type_of_correct. Qed.
End type_of.

Section path_type_check.
  Context `{PathTypeCheckSpec T R}.

  Lemma path_type_check_None p τ σ : τ !! p = None → p @ τ ↣ σ → False.
  Proof. rewrite <-path_type_check_correct. congruence. Qed.
  Lemma path_type_check_sound p τ σ : τ !! p = Some σ → p @ τ ↣ σ.
  Proof. by rewrite path_type_check_correct. Qed.
  Lemma path_type_check_complete p τ σ : p @ τ ↣ σ → τ !! p = Some σ.
  Proof. by rewrite path_type_check_correct. Qed.
  Lemma path_typed_unique p τ σ1 σ2 : p @ τ ↣ σ1 → p @ τ ↣ σ2 → σ1 = σ2.
  Proof. rewrite <-!path_type_check_correct. congruence. Qed.

  Context `{∀ τ1 τ2 : T, Decision (τ1 = τ2)}.
  Global Instance path_typed_dec p τ σ : Decision (p @ τ ↣ σ).
  Proof.
   refine (cast_if (decide (τ !! p = Some σ)));
    abstract by rewrite <-path_type_check_correct.
  Defined.
End path_type_check.

Ltac simplify_type_equality := repeat
  match goal with
  | _ => progress simplify_equality
  | H : type_check _ _ = Some _ |- _ => apply type_check_sound in H
  | H : _ !! _ = Some _ |- _ => apply path_type_check_sound in H
  | H : context [ type_of ?x ], H2 : _ ⊢ ?x : _ |- _ =>
    rewrite !(type_of_correct _ _ _ H2) in H
  | H2 : _ ⊢ ?x : _ |- context [ type_of ?x ] =>
    rewrite !(type_of_correct _ _ _ H2)
  | H1 : type_check ?m ?x = None, H2 : ?m ⊢ ?x : _ |- _ =>
    destruct (type_check_None _ _ _ H1 H2)
  | H1 : ?τ !! ?p = None, H2 : ?p @ ?τ ↣ _ |- _ =>
    destruct (path_type_check_None _ _ _ H1 H2)
  | H1 : ?m ⊢ ?x : ?τ1, H2 : ?m ⊢ ?x : ?τ2 |- _ =>
    unless (τ2 = τ1) by done; pose proof (typed_unique m x τ2 τ1 H2 H1)
  | H1 : ?m ⊢ ?x : ?τ1, H2 : ?m ⊢ ?x : ?τ2 |- _ =>
    unless (τ2 = τ1) by done; pose proof (typed_unique_alt m x τ2 τ1 H2 H1)
  | H1 : ?p @ ?τ ↣ ?σ1, H2 : ?p @ ?τ ↣ ?σ2 |- _ =>
    unless (σ2 = σ1) by done; pose proof (path_typed_unique p τ σ2 σ1 H2 H1)
  end.
Ltac simplify_type_equality' :=
  repeat (progress simpl in * || simplify_type_equality).

Class Valid (M V : Type) := valid: M → V → Prop.
Notation "m ⊢ 'valid' v" := (valid m v)
  (at level 74, v at level 9, format "m  ⊢  'valid'  v") : C_scope.
Notation "m ⊢* 'valid' vs" := (Forall (valid m) vs)
  (at level 74, v at level 9, format "m  ⊢*  'valid'  vs") : C_scope.
Notation "⊢ 'valid' v" := (valid () v)
  (at level 10, v at level 9, format "⊢  'valid'  v") : C_scope.

(** * Well-formed types *)
(** Our definition of types still allows invalid types; in particular circular
unions and structs. For example [struct s { struct s x; }]. The predicate
[type_valid Γ] describes that a type is valid with respect to an environment
[Γ]. That means, recursive occurrences of unions and structs are always guarded
by a pointer. The predicate [env_valid] describes that an environment is
valid. *)
Section types.
  Context {Ti : Set}.
  Implicit Types Γ Σ : env Ti.

  Inductive type_valid Γ : type Ti → Prop :=
    | TBase_valid τ : base_type_valid Γ τ → type_valid Γ (base τ)
    | TArray_valid τ n : type_valid Γ τ → n ≠ 0 → type_valid Γ (τ.[n])
    | TCompound_valid c s : is_Some (Γ !! s) → type_valid Γ (compound@{c} s)
  with ptr_type_valid Γ : type Ti → Prop :=
    | TBase_ptr_valid τ : base_type_valid Γ τ → ptr_type_valid Γ (base τ)
    | TVoid_ptr_valid : ptr_type_valid Γ void
    | TArray_ptr_valid τ n : type_valid Γ τ → n ≠ 0 → ptr_type_valid Γ (τ.[n])
    | TCompound_ptr_valid c s : ptr_type_valid Γ (compound@{c} s)
  with base_type_valid Γ : base_type Ti → Prop :=
    | TInt_valid τ : base_type_valid Γ (intt τ)
    | TPtr_valid τ : ptr_type_valid Γ τ → base_type_valid Γ (τ.*).

  Fixpoint type_valid_dec Γ τ : Decision (type_valid Γ τ)
  with ptr_type_valid_dec Γ τ : Decision (ptr_type_valid Γ τ)
  with base_type_valid_dec Γ τ : Decision (base_type_valid Γ τ).
  Proof.
   refine
    match τ with
    | void => right _
    | base τ => cast_if (base_type_valid_dec Γ τ)
    | τ.[n] => cast_if_and (decide (n ≠ 0)) (type_valid_dec Γ τ)
    | compound@{c} s => cast_if (decide (is_Some (Γ !! s)))
    end%T; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec;
      abstract first [by constructor | by inversion 1].
   refine
    match τ with
    | void => left _
    | base τ => cast_if (base_type_valid_dec Γ τ)
    | τ.[n] => cast_if_and (decide (n ≠ 0)) (type_valid_dec Γ τ)
    | compound@{_} _ => left _
    end%T; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec;
      abstract first [by constructor | by inversion 1].
   refine
    match τ with
    | intt τ => left _
    | τ.* => cast_if (ptr_type_valid_dec Γ τ)
    end%BT; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec;
      abstract first [by constructor | by inversion 1].
  Defined.
  Global Existing Instance type_valid_dec.
  Global Existing Instance ptr_type_valid_dec.
  Global Existing Instance base_type_valid_dec.

  Lemma type_valid_ptr_type_valid Γ τ : type_valid Γ τ → ptr_type_valid Γ τ.
  Proof. by destruct 1; constructor. Qed.

  Inductive env_valid : env Ti → Prop :=
    | env_empty_valid : env_valid ∅
    | env_add_valid Γ s τs :
       env_valid Γ → Forall (type_valid Γ) τs → length τs ≠ 0 →
       Γ !! s = None → env_valid (<[s:=τs]>Γ).
  Class EnvValid Γ := env_valid_: env_valid Γ.

  Lemma type_valid_weaken Γ Σ τ : type_valid Γ τ → Γ ⊆ Σ → type_valid Σ τ
  with ptr_type_valid_weaken Γ Σ τ :
    ptr_type_valid Γ τ → Γ ⊆ Σ → ptr_type_valid Σ τ
  with base_type_valid_weaken Γ Σ τ :
    base_type_valid Γ τ → Γ ⊆ Σ → base_type_valid Σ τ.
  Proof.
    destruct 1; constructor; eauto using lookup_weaken_is_Some.
    destruct 1; econstructor; eauto.
    destruct 1; econstructor; eauto.
  Qed.

  Lemma type_valid_weaken_subset Γ Σ τ :
    type_valid Γ τ → Γ ⊂ Σ → type_valid Σ τ.
  Proof. eauto using type_valid_weaken, (strict_include (R:=(⊆))). Qed.
  Lemma types_valid_weaken Γ Σ τs :
    Forall (type_valid Γ) τs → Γ ⊆ Σ → Forall (type_valid Σ) τs.
  Proof. eauto using Forall_impl, type_valid_weaken. Qed.
  Lemma types_valid_weaken_subset Γ Σ τs :
    Forall (type_valid Γ) τs → Γ ⊂ Σ → Forall (type_valid Σ) τs.
  Proof. eauto using Forall_impl, type_valid_weaken_subset. Qed.

  Lemma env_valid_delete Γ s τs :
    env_valid Γ → Γ !! s = Some τs → ∃ Σ,
      Σ ⊆ delete s Γ ∧ Forall (type_valid Σ) τs ∧ length τs ≠ 0 ∧ env_valid Σ.
  Proof.
    intros HΓ Hs. induction HΓ as [|Γ s' τs' HΓ IH Hτs' Hs'].
    { by simpl_map. }
    destruct (decide (s = s')); simplify_map_equality.
    * exists Γ. by rewrite delete_insert.
    * destruct (IH Hs) as (Σ&?&?&?&?). exists Σ. split_ands; auto.
      rewrite delete_insert_ne by done. transitivity (delete s Γ); [done |].
      apply insert_subseteq. by rewrite lookup_delete_ne.
  Qed.
  Lemma env_valid_lookup_subset Γ s τs :
    env_valid Γ → Γ !! s = Some τs → ∃ Σ,
      Σ ⊂ Γ ∧ Forall (type_valid Σ) τs ∧ length τs ≠ 0 ∧ env_valid Σ.
  Proof.
    intros. destruct (env_valid_delete Γ s τs) as (Σ&?&?&?&?); auto.
    exists Σ. split_ands; auto.
    apply strict_transitive_r with (delete s Γ); eauto using delete_subset_alt.
  Qed.
  Lemma env_valid_union Γ Σ :
    Γ ⊥ Σ → env_valid Γ → env_valid Σ → env_valid (Γ ∪ Σ).
  Proof.
    induction 2; decompose_map_disjoint.
    * by rewrite (left_id ∅ (∪)).
    * rewrite <-insert_union_l.
      constructor; eauto using types_valid_weaken, map_union_subseteq_l.
      by rewrite lookup_union_None.
  Qed.

  Context `{HΓ : !EnvValid Γ}.

  Lemma env_valid_lookup_length s τs : Γ !! s = Some τs → length τs ≠ 0.
  Proof.
    intros. by destruct (env_valid_lookup_subset Γ s τs) as (?&?&?&?&?).
  Qed.
  Lemma env_valid_lookup s τs : Γ !! s = Some τs → Forall (type_valid Γ) τs.
  Proof.
    intros. destruct (env_valid_lookup_subset Γ s τs) as (?&?&?&?);
      eauto using types_valid_weaken_subset.
  Qed.
  Lemma env_valid_lookup_lookup s τs i τ :
    Γ !! s = Some τs → τs !! i = Some τ → type_valid Γ τ.
  Proof.
    intros Hs ?. apply env_valid_lookup in Hs. eapply Forall_lookup; eauto.
  Qed.
  Lemma env_valid_lookup_singleton s τ : Γ !! s = Some [τ] → type_valid Γ τ.
  Proof. intros. by apply (env_valid_lookup_lookup s [τ] 0 τ). Qed.
End types.

(** A very inefficient decision procedure for wellformedness of environments.
It checks wellformedness by trying all permutations of the environment. This
decision procedure is not intended to be used for computation. *)
Section env_valid_dec.
  Context {Ti : Set}.

  Inductive list_env_valid : list (tag * list (type Ti)) → Prop :=
    | env_nil_valid : list_env_valid []
    | env_cons_valid Γ s τs :
       list_env_valid Γ → Forall (type_valid (map_of_list Γ)) τs →
       length τs ≠ 0 → map_of_list Γ !! s = None →
       list_env_valid ((s,τs) :: Γ).

  Lemma list_env_valid_nodup Γ : list_env_valid Γ → NoDup (fst <$> Γ).
  Proof.
    induction 1 as [| Γ s τs ? IH]; simpl;
      constructor; auto using not_elem_of_map_of_list_2.
  Qed.

  Instance list_env_valid_dec: ∀ Γ, Decision (list_env_valid Γ).
  Proof.
   refine (
    fix go Γ :=
    match Γ return Decision (list_env_valid Γ) with
    | [] => left _
    | (s,τs) :: Γ => cast_if_and4
       (decide (Forall (type_valid (map_of_list Γ)) τs))
       (decide (length τs ≠ 0))
       (decide (map_of_list Γ !! s = None))
       (go Γ)
    end); clear go; first [by constructor | by inversion 1].
  Defined.

  Lemma list_env_valid_correct Γ :
    env_valid Γ ↔ ∃ Γ', map_to_list Γ ≡ₚ Γ' ∧ list_env_valid Γ'.
  Proof.
    split.
    * induction 1 as [| Γ s τs ? IH].
      + eexists []. rewrite map_to_list_empty. split; constructor.
      + destruct IH as [Γ' [Hperm ?]]. exists ((s,τs) :: Γ').
        rewrite map_to_list_insert, Hperm by done.
        split; [done |]. apply map_of_list_proper in Hperm;
          auto using map_to_list_key_nodup.
        rewrite map_of_to_list in Hperm. subst. constructor; auto.
    * intros [Γ' [Hperm HΓ']]. revert Γ Hperm.
      induction HΓ' as [| Γ' s τs ? IH]; intros Γ Hperm.
      + apply map_to_list_empty_inv_alt in Hperm. subst. constructor.
      + apply map_to_list_insert_inv in Hperm. subst. constructor; auto.
        apply IH. rewrite map_to_of_list; auto using list_env_valid_nodup.
  Qed.
  Lemma list_env_valid_correct_alt Γ :
    env_valid Γ ↔ Exists list_env_valid (permutations (map_to_list Γ)).
  Proof.
    rewrite list_env_valid_correct, Exists_exists.
    by setoid_rewrite permutations_Permutation.
  Qed.

  Global Instance env_valid_dec (Γ : env Ti) : Decision (env_valid Γ).
  Proof.
   refine (cast_if
    (decide (Exists list_env_valid (permutations (map_to_list Γ)))));
    by rewrite list_env_valid_correct_alt.
  Defined.
End env_valid_dec.

(** A nice induction principle for wellformed types. *)
Section type_env_ind.
  Context `{Γ : env Ti} `{!EnvValid Γ}.

  Context (P : type Ti → Prop).
  Context (Pbase : ∀ τ, base_type_valid Γ τ → P (base τ)).
  Context (Parray : ∀ τ n, type_valid Γ τ → P τ → n ≠ 0 → P (τ.[n])).
  Context (Pcompound : ∀ c s τs,
    Γ !! s = Some τs → Forall (type_valid Γ) τs → Forall P τs →
    length τs ≠ 0 → P (compound@{c} s)).

  Lemma type_env_ind: ∀ τ, type_valid Γ τ → P τ.
  Proof.
    cut (∀ Σ τ, Σ ⊆ Γ → env_valid Σ → type_valid Σ τ → P τ).
    { intros help τ. by apply help. }
    induction Σ as [Σ IH] using (well_founded_induction map_wf).
    intros τ HΣΓ HΣ Hτ. induction Hτ as [τ Hτ | τ n Hτ | c s Hs].
    * by apply Pbase, (base_type_valid_weaken Σ).
    * apply Parray; eauto. by apply (type_valid_weaken Σ).
    * inversion Hs as [τs Hτs].
      destruct (env_valid_lookup_subset Σ s τs) as (Σ'&?&Hτs'&Hlen&?); auto.
      assert (Σ' ⊂ Γ) by eauto using (strict_transitive_l (R:=(⊆))).
      apply Pcompound with τs; auto.
      + apply Forall_impl with (type_valid Σ'); auto.
        intros. eapply type_valid_weaken_subset; eauto.
      + clear Hτs Hlen. induction Hτs'; constructor; auto.
        apply (IH Σ'); eauto using (strict_include (R:=(⊆))).
  Qed.
End type_env_ind.

(** And a weaker one for arbitrary types in a well formed environment. *)
Section weak_type_env_ind.
  Context `{Γ : env Ti} `{!EnvValid Γ}.

  Context (P : type Ti → Prop).
  Context (Pbase : ∀ τ, P (base τ)).
  Context (Pvoid : P void).
  Context (Parray : ∀ τ n, P τ → P (τ.[n])).
  Context (Pcompound : ∀ c s τs,
    Γ !! s = Some τs → Forall P τs → P (compound@{c} s)).
  Context (PcompoundNone : ∀ c s, Γ !! s = None → P (compound@{c} s)).

  Lemma weak_type_env_ind τ : P τ.
  Proof.
    induction τ as [τ| |τ n|c s]; auto.
    destruct (Γ !! s) as [τs|] eqn:Hs; auto.
    destruct (env_valid_lookup_subset Γ s τs) as (Σ'&?&Hτs&_&?); auto.
    apply Pcompound with τs; auto.
    clear Hs. induction Hτs as [|τ τs]; constructor; auto.
    apply type_env_ind; eauto using type_valid_weaken, (strict_include (R:=(⊆))).
  Qed.
End weak_type_env_ind.

(** A nice iteration principle for wellformed types. *)
Section type_iter.
  Context {Ti : Set} {A : Type} (R : relation A) `{!Equivalence R}.
  Local Infix "≡" := R.
  Context (fbase : base_type Ti → A).
  Context (fvoid : A).
  Context (farray : type Ti → nat → A → A).
  Context (fcompound: compound_kind → tag → list (type Ti) → (type Ti → A) → A).

  Definition type_iter_inner
      (g : tag → list (type Ti) * (type Ti → A)) : type Ti → A :=
    fix go τ :=
    match τ with
    | base τ => fbase τ
    | void => fvoid
    | τ.[n] => farray τ n (go τ)
    | compound@{c} s => let (τs,h) := g s in fcompound c s τs h
    end%T.
  Definition type_iter_accF Γ (go : ∀ Σ, Σ ⊂ Γ → type Ti → A)
      (s : tag) : list (type Ti) * (type Ti → A) :=
    match Some_dec (Γ !! s) with
    | inleft (τs↾Hτs) => (τs, go (delete s Γ) (delete_subset_alt _ _ _ Hτs))
    | inright _ => ([], λ _, fvoid) (**i dummy *)
    end.
  Definition type_iter_acc : ∀ Γ, Acc (⊂) Γ → type Ti → A :=
    Fix_F _ $ λ Γ go, type_iter_inner (type_iter_accF Γ go).
  Definition type_iter (Γ : env Ti) : type Ti → A :=
    type_iter_acc _ (wf_guard 32 map_wf Γ).

  Lemma type_iter_acc_weaken Γ (Σ1 Σ2 : env Ti) acc1 acc2 τ :
    env_valid Γ →
    (∀ τ n x y, x ≡ y → farray τ n x ≡ farray τ n y) →
    (∀ f g c s τs,
      Γ !! s = Some τs → Forall (λ τ, f τ ≡ g τ) τs →
      fcompound c s τs f ≡ fcompound c s τs g) →
    type_valid Γ τ → Γ ⊆ Σ1 → Γ ⊆ Σ2 →
    type_iter_acc Σ1 acc1 τ ≡ type_iter_acc Σ2 acc2 τ.
  Proof.
    intros HΓ Harray. revert Σ1 Σ2 acc1 acc2 τ HΓ.
    induction Γ as [Γ IH] using (well_founded_induction map_wf).
    intros Σ1 Σ2 [acc1] [acc2] τ HΓ Hcompound Hτ HΣ1 HΣ2. simpl.
    induction Hτ as [τ Hτ | τ n Hτ | c s [τs Hs]]; simpl; try reflexivity; auto.
    unfold type_iter_accF. destruct (Some_dec (Σ1 !! s)) as [[τs1 Hs1]|?],
      (Some_dec (Σ2 !! s)) as [[τs2 Hs2]|?];
      try by (exfalso; simplify_map_equality).
    generalize (acc1 _ (delete_subset_alt Σ1 s τs1 Hs1)),
      (acc2 _ (delete_subset_alt Σ2 s τs2 Hs2)); intros acc1' acc2'.
    simplify_map_equality.
    destruct (env_valid_delete Γ s τs) as (Γ'&?&Hτs&Hlen&?); trivial.
    assert (Γ' ⊆ Γ) by (transitivity (delete s Γ); auto using delete_subseteq).
    apply Hcompound; auto. assert (is_Some (Γ !! s)) by eauto.
    clear Hs Hlen acc1 acc2.
    induction Hτs; constructor; auto. apply (IH Γ'); trivial.
    * eauto using (strict_transitive_r (R:=(⊆))),
        delete_subset, lookup_weaken_is_Some.
    * eauto using lookup_weaken.
    * transitivity (delete s Γ); eauto using delete_subseteq_compat.
    * transitivity (delete s Γ); eauto using delete_subseteq_compat.
  Qed.

  Context `{Γ : env Ti} `{!EnvValid Γ}.

  Lemma type_iter_base τ : type_iter Γ (base τ) = fbase τ.
  Proof. done. Qed.
  Lemma type_iter_void : type_iter Γ void = fvoid.
  Proof. done. Qed.
  Lemma type_iter_array τ n :
    type_iter Γ (τ.[n]) = farray τ n (type_iter Γ τ).
  Proof. unfold type_iter. by destruct (wf_guard _ map_wf Γ). Qed.
  Lemma type_iter_compound c s τs :
    (∀ τ n x y, x ≡ y → farray τ n x ≡ farray τ n y) →
    (∀ f g c s τs,
      Γ !! s = Some τs → Forall (λ τ, f τ ≡ g τ) τs →
      fcompound c s τs f ≡ fcompound c s τs g) →
    Γ !! s = Some τs →
    type_iter Γ (compound@{c} s) ≡ fcompound c s τs (type_iter Γ).
  Proof.
    intros Harray Hcompound Hs. unfold type_iter at 1.
    destruct (wf_guard _ map_wf Γ) as [accΓ]. simpl.
    unfold type_iter_accF.
    destruct (Some_dec (Γ !! s)) as [[τs' Hs']|?]; [|congruence].
    generalize (accΓ _ (delete_subset_alt Γ s τs' Hs')). intros accΓ'.
    simplify_map_equality. apply Hcompound; auto.
    destruct (env_valid_delete Γ s τs) as (Γ'&?&Hτs&Hlen&?); trivial.
    assert (Γ' ⊆ Γ) by (transitivity (delete s Γ); auto using delete_subseteq).
    clear Hs Hlen. induction Hτs; constructor; auto.
    apply (type_iter_acc_weaken Γ'); eauto using lookup_weaken.
  Qed.
  Lemma type_iter_compound_None c s :
    Γ !! s = None →
    type_iter Γ (compound@{c} s) = fcompound c s [] (λ _, fvoid).
  Proof.
    intros Hs. unfold type_iter.
    destruct (wf_guard _ map_wf Γ) as [accΓ]; simpl.
    unfold type_iter_accF. destruct (Some_dec _) as [[??]|?]; congruence.
  Qed.
End type_iter.
