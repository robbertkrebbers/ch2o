(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file describes a subset of the C type system. This subset includes
pointer, array, struct, and union types, but omits qualifiers as volatile and
const. Also variable length arrays are omitted from the formalization. *)
Require Import nmap mapset.
Require Export type_classes abstract_integers fin_maps.

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
Instance tagmap_omap: OMap tagmap := λ A B f, @omap Nmap _ _ f _.
Instance tagmap_merge : Merge tagmap := @merge Nmap _.
Instance tagmap_fmap: FMap tagmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap tag tagmap := _.

Instance tagmap_dom {A} : Dom (tagmap A) tagset := mapset_dom.
Instance: FinMapDom tag tagmap tagset := mapset_dom_spec.

Instance tag_lexico : Lexico tag := @lexico N _.
Instance tag_lexico_order : StrictOrder (@lexico tag _) := _.
Instance tag_trichotomy: TrichotomyT (@lexico tag _) := _.

Typeclasses Opaque tag tagmap.

(** * Types *)
(** Types are defined mutually inductively. The type [type] represents the
types of full C types (arrays, structs, unions), and [base_type] describes the
types of values that can occur at the leafs of a full value (integers,
pointers). Structs and unions include a name that refers to their fields in the
environment. *)
Inductive compound_kind := Struct_kind | Union_kind.

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

Notation "'baseT' τ" := (TBase τ) (at level 10) : ctype_scope.
Notation "'voidT'" := TVoid : ctype_scope.
Notation "τ .[ n ]" := (TArray τ n)
  (at level 25, left associativity, format "τ .[ n ]") : ctype_scope.
Notation "'compoundT{' c } s" := (TCompound c s)
  (at level 10, format "'compoundT{' c }  s") : ctype_scope.
Notation "'structT' s" := (TCompound Struct_kind s) (at level 10) : ctype_scope.
Notation "'unionT' s" := (TCompound Union_kind s) (at level 10) : ctype_scope.
Notation "'intT' τ" := (TInt τ) (at level 10) : cbase_type_scope.
Notation "'intT' τ" := (TBase (TInt τ)) (at level 10) : ctype_scope.
Notation "'ucharT'" := (TInt ucharT) : cbase_type_scope.
Notation "'ucharT'" := (TBase ucharT) : ctype_scope.
Notation "'scharT'" := (TInt scharT) : cbase_type_scope.
Notation "'scharT'" := (TBase scharT) : ctype_scope.
Notation "'uintT'" := (TInt uintT) : cbase_type_scope.
Notation "'uintT'" := (TBase uintT) : ctype_scope.
Notation "'sintT'" := (TInt sintT) : cbase_type_scope.
Notation "'sintT'" := (TBase sintT) : ctype_scope.
Notation "'uptrT'" := (TInt uptrT) : cbase_type_scope.
Notation "'uptrT'" := (TBase uptrT) : ctype_scope.
Notation "'sptrT'" := (TInt sptrT) : cbase_type_scope.
Notation "'sptrT'" := (TBase sptrT) : ctype_scope.
Notation "τ .*" := (TPtr τ) (at level 25, format "τ .*") : cbase_type_scope.
Notation "τ .*" := (TBase (τ.*)) (at level 25, format "τ .*") : ctype_scope.

Notation env Ti := (tagmap (list (type Ti))).

Instance compound_kind_eq_dec (c1 c2 : compound_kind) : Decision (c1 = c2).
Proof. solve_decision. Defined.
Fixpoint type_eq_dec {Ti : Set} {dec : ∀ τi1 τi2 : Ti, Decision (τi1 = τi2)}
  (τ1 τ2 : type Ti) : Decision (τ1 = τ2)
with base_type_eq_dec {Ti : Set} {dec : ∀ τi1 τi2 : Ti, Decision (τi1 = τi2)}
  (τ1 τ2 : base_type Ti) : Decision (τ1 = τ2).
Proof.
 refine
  match τ1, τ2 with
  | baseT τi1, baseT τi2 => cast_if (decide_rel (=) τi1 τi2)
  | voidT, voidT => left _
  | τ1.[n1], τ2.[n2] =>
     cast_if_and (decide_rel (=) n1 n2) (decide_rel (=) τ1 τ2)
  | compoundT{c1} s1, compoundT{c2} s2 =>
     cast_if_and (decide_rel (=) c1 c2) (decide_rel (=) s1 s2)
  | _, _ => right _
  end%T; clear base_type_eq_dec type_eq_dec; abstract congruence.
 refine
  match τ1, τ2 with
  | intT τi1, intT τi2 => cast_if (decide_rel (=) τi1 τi2)
  | τ1.*, τ2.* => cast_if (decide_rel (=) τ1 τ2)
  | _, _ => right _
  end%BT; clear base_type_eq_dec type_eq_dec; abstract congruence.
Defined.
Existing Instance type_eq_dec.
Existing Instance base_type_eq_dec.

Definition maybe_TArray {Ti} (τ : type Ti) : option (type Ti * nat) :=
  match τ with τ.[n] => Some (τ,n) | _ => None end%T.
Definition maybe_TCompound {Ti} (τ : type Ti) : option (compound_kind * tag) :=
  match τ with compoundT{c} s => Some (c,s) | _ => None end%T.

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
  Implicit Types τ : type Ti.
  Implicit Types τb : base_type Ti.
  Implicit Types τi : int_type Ti.

  Inductive type_valid' Γ : type Ti → Prop :=
    | TBase_valid' τb : base_type_valid' Γ τb → type_valid' Γ (baseT τb)
    | TArray_valid' τ n : type_valid' Γ τ → n ≠ 0 → type_valid' Γ (τ.[n])
    | TCompound_valid' c s : is_Some (Γ !! s) → type_valid' Γ (compoundT{c} s)
  with ptr_type_valid Γ : type Ti → Prop :=
    | TBase_ptr_valid' τb : base_type_valid' Γ τb → ptr_type_valid Γ (baseT τb)
    | TVoid_ptr_valid : ptr_type_valid Γ voidT
    | TArray_ptr_valid' τ n : type_valid' Γ τ → n ≠ 0 → ptr_type_valid Γ (τ.[n])
    | TCompound_ptr_valid c s : ptr_type_valid Γ (compoundT{c} s)
  with base_type_valid' Γ : base_type Ti → Prop :=
    | TInt_valid' τi : base_type_valid' Γ (intT τi)
    | TPtr_valid' τ : ptr_type_valid Γ τ → base_type_valid' Γ (τ.*).
  Global Instance type_valid : Valid (env Ti) (type Ti) := type_valid'.
  Global Instance base_type_valid :
    Valid (env Ti) (base_type Ti) := base_type_valid'.

  Lemma TBase_valid Γ τb : ✓{Γ} τb → ✓{Γ} (baseT τb)%T.
  Proof. by constructor. Qed.
  Lemma TArray_valid Γ τ n : ✓{Γ} τ → n ≠ 0 → ✓{Γ} (τ.[n])%T.
  Proof. by constructor. Qed.
  Lemma TCompound_valid Γ c s : is_Some (Γ !! s) → ✓{Γ} (compoundT{c} s)%T.
  Proof. by constructor. Qed.
  Lemma TBase_ptr_valid Γ τb : ✓{Γ} τb → ptr_type_valid Γ (baseT τb)%T.
  Proof. by constructor. Qed.
  Lemma TArray_ptr_valid Γ τ n : ✓{Γ} τ → n ≠ 0 → ptr_type_valid Γ (τ.[n]).
  Proof. by constructor. Qed.
  Lemma TInt_valid Γ τi : ✓{Γ} (intT τi)%BT.
  Proof. by constructor. Qed.
  Lemma TPtr_valid Γ τ : ptr_type_valid Γ τ → ✓{Γ} (τ.*)%BT.
  Proof. by constructor. Qed.

  Lemma TBase_valid_inv Γ τb : ✓{Γ} (baseT τb)%T → ✓{Γ} τb.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_valid_inv Γ τ n : ✓{Γ} (τ.[n])%T → ✓{Γ} τ ∧ n ≠ 0.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_valid_inv_type Γ τ n : ✓{Γ} (τ.[n])%T → ✓{Γ} τ.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_valid_inv_size Γ τ n : ✓{Γ} (τ.[n])%T → n ≠ 0.
  Proof. by inversion_clear 1. Qed.
  Lemma TCompound_valid_inv Γ c s : ✓{Γ} (compoundT{c} s)%T → is_Some (Γ !! s).
  Proof. by inversion_clear 1. Qed.
  Lemma TBase_ptr_valid_inv Γ τb : ptr_type_valid Γ (baseT τb)%T → ✓{Γ} τb.
  Proof. by inversion_clear 1. Qed.
  Lemma TArray_ptr_valid_inv Γ τ n : ✓{Γ} (τ.[n])%T → ✓{Γ} τ.
  Proof. by inversion_clear 1. Qed.
  Lemma TPtr_valid_inv Γ τ : ✓{Γ} (τ.*)%BT → ptr_type_valid Γ τ.
  Proof. by inversion_clear 1. Qed.

  Fixpoint type_valid_dec Γ τ : Decision (✓{Γ} τ)
  with ptr_type_valid_dec Γ τ : Decision (ptr_type_valid Γ τ)
  with base_type_valid_dec Γ τb : Decision (✓{Γ} τb).
  Proof.
   refine
    match τ with
    | voidT => right _
    | baseT τb => cast_if (base_type_valid_dec Γ τb)
    | τ.[n] => cast_if_and (decide (n ≠ 0)) (type_valid_dec Γ τ)
    | compoundT{c} s => cast_if (decide (is_Some (Γ !! s)))
    end%T; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec;
      abstract first [by constructor | by inversion 1].
   refine
    match τ with
    | voidT => left _
    | baseT τb => cast_if (base_type_valid_dec Γ τb)
    | τ.[n] => cast_if_and (decide (n ≠ 0)) (type_valid_dec Γ τ)
    | compoundT{_} _ => left _
    end%T; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec;
      abstract first [by constructor | by inversion 1].
   refine
    match τb with
    | intT _ => left _
    | τ.* => cast_if (ptr_type_valid_dec Γ τ)
    end%BT; clear type_valid_dec ptr_type_valid_dec base_type_valid_dec;
      abstract first [by constructor | by inversion 1].
  Defined.
  Global Existing Instance type_valid_dec.
  Global Existing Instance ptr_type_valid_dec.
  Global Existing Instance base_type_valid_dec.

  Lemma base_type_valid_inv Γ (P : Prop) τb :
    ✓{Γ} τb →
    match τb with
    | intT τ => P → P
    | τ.* => (ptr_type_valid Γ τ → P) → P
    end%BT.
  Proof. destruct 1; eauto. Qed.
  Lemma type_valid_inv Γ (P : Prop) τ :
    ✓{Γ} τ →
    match τ with
    | baseT τ => (✓{Γ} τ → P) → P
    | τ.[n] => (✓{Γ} τ → n ≠ 0 → P) → P
    | compoundT{c} s => (is_Some (Γ !! s) → P) → P
    | _ => P
    end%T.
  Proof. destruct 1; eauto. Qed.

  Lemma type_valid_ptr_type_valid Γ τ : ✓{Γ} τ → ptr_type_valid Γ τ.
  Proof. by destruct 1; constructor. Qed.

  Inductive env_valid : Valid () (env Ti) :=
    | env_empty_valid : ✓ ∅
    | env_add_valid Γ s τs :
       ✓ Γ → ✓{Γ}* τs → 1 < length τs → Γ !! s = None → ✓ (<[s:=τs]>Γ).
  Global Existing Instance env_valid.

  Lemma type_valid_weaken Γ Σ τ : ✓{Γ} τ → Γ ⊆ Σ → ✓{Σ} τ
  with ptr_type_valid_weaken Γ Σ τ :
    ptr_type_valid Γ τ → Γ ⊆ Σ → ptr_type_valid Σ τ
  with base_type_valid_weaken Γ Σ (τ : base_type Ti) :
    ✓{Γ} τ → Γ ⊆ Σ → ✓{Σ} τ.
  Proof.
    * unfold valid, base_type_valid, type_valid in *.
      destruct 1; constructor; eauto using lookup_weaken_is_Some.
    * unfold valid, base_type_valid, type_valid in *.
      destruct 1; econstructor; eauto.
    * unfold valid, base_type_valid, type_valid in *.
      destruct 1; econstructor; eauto.
  Qed.

  Lemma type_valid_weaken_subset Γ Σ τ  : ✓{Γ} τ → Γ ⊂ Σ → ✓{Σ} τ.
  Proof.
    eauto using type_valid_weaken, (strict_include (R:=(⊆):relation (env _))).
  Qed.
  Lemma types_valid_weaken Γ Σ (τs : list (type Ti)) :
    ✓{Γ}* τs → Γ ⊆ Σ → ✓{Σ}* τs.
  Proof. eauto using Forall_impl, type_valid_weaken. Qed.
  Lemma types_valid_weaken_subset Γ Σ (τs : list (type Ti)) :
    ✓{Γ}* τs → Γ ⊂ Σ → ✓{Σ}* τs.
  Proof. eauto using Forall_impl, type_valid_weaken_subset. Qed.

  Lemma env_valid_delete Γ s τs :
    ✓ Γ → Γ !! s = Some τs → ∃ Σ, Σ ⊆ delete s Γ ∧ ✓{Σ}* τs ∧ 1 < length τs ∧ ✓ Σ.
  Proof.
    intros HΓ Hs. induction HΓ as [|Γ s' τs' HΓ IH Hτs' Hs']; [by simpl_map|].
    destruct (decide (s = s')); simplify_map_equality.
    * exists Γ. by rewrite delete_insert.
    * destruct (IH Hs) as (Σ&?&?&?&?). exists Σ. split_ands; auto.
      rewrite delete_insert_ne by done. transitivity (delete s Γ); [done |].
      apply insert_subseteq. by rewrite lookup_delete_ne.
  Qed.
  Lemma env_valid_lookup_subset Γ s τs :
    ✓ Γ → Γ !! s = Some τs → ∃ Σ, Σ ⊂ Γ ∧ ✓{Σ}* τs ∧ 1 < length τs ∧ ✓ Σ.
  Proof.
    intros. destruct (env_valid_delete Γ s τs) as (Σ&?&?&?&?); auto.
    exists Σ. split_ands; auto.
    apply strict_transitive_r with (delete s Γ); eauto using delete_subset_alt.
  Qed.
  Lemma env_valid_union Γ Σ : Γ ⊥ Σ → ✓ Γ → ✓ Σ → ✓ (Γ ∪ Σ).
  Proof.
    induction 2; decompose_map_disjoint; [by rewrite (left_id_L ∅ (∪)) |].
    rewrite <-insert_union_l.
    constructor; eauto using types_valid_weaken, map_union_subseteq_l.
    by rewrite lookup_union_None.
  Qed.

  Lemma env_valid_lookup_length Γ s τs : ✓ Γ → Γ !! s = Some τs → 1 < length τs.
  Proof.
    intros. by destruct (env_valid_lookup_subset Γ s τs) as (?&?&?&?&?).
  Qed.
  Lemma env_valid_lookup Γ s τs : ✓ Γ → Γ !! s = Some τs → ✓{Γ}* τs.
  Proof.
    intros. destruct (env_valid_lookup_subset Γ s τs) as (?&?&?&?);
      eauto using types_valid_weaken_subset.
  Qed.
  Lemma env_valid_lookup_lookup Γ s τs i τ : 
    ✓ Γ →Γ !! s = Some τs → τs !! i = Some τ → ✓{Γ} τ.
  Proof.
    intros ? Hs ?. apply env_valid_lookup in Hs; auto. eapply Forall_lookup; eauto.
  Qed.
  Lemma env_valid_lookup_singleton Γ s τ : ✓ Γ → Γ !! s = Some [τ] → ✓{Γ} τ.
  Proof. intros. by apply (env_valid_lookup_lookup Γ s [τ] 0 τ). Qed.
End types.

(** A very inefficient decision procedure for wellformedness of environments.
It checks wellformedness by trying all permutations of the environment. This
decision procedure is not intended to be used for computation. *)
Section env_valid_dec.
  Context {Ti : Set}.

  Inductive list_env_valid : list (tag * list (type Ti)) → Prop :=
    | env_nil_valid : list_env_valid []
    | env_cons_valid Γ s τs :
       list_env_valid Γ → ✓{map_of_list Γ}* τs →
       1 < length τs → map_of_list Γ !! s = None →
       list_env_valid ((s,τs) :: Γ).

  Lemma list_env_valid_nodup Γ : list_env_valid Γ → NoDup (fst <$> Γ).
  Proof.
    induction 1; simpl; constructor; auto using not_elem_of_map_of_list_2.
  Qed.

  Instance list_env_valid_dec: ∀ Γ, Decision (list_env_valid Γ).
  Proof.
   refine (
    fix go Γ :=
    match Γ return Decision (list_env_valid Γ) with
    | [] => left _
    | (s,τs) :: Γ => cast_if_and4
       (decide (✓{map_of_list Γ}* τs))
       (decide (1 < length τs))
       (decide (map_of_list Γ !! s = None))
       (go Γ)
    end); clear go; first [by constructor | by inversion 1].
  Defined.

  Lemma list_env_valid_correct Γ :
    ✓ Γ ↔ ∃ Γ', map_to_list Γ ≡ₚ Γ' ∧ list_env_valid Γ'.
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
    ✓ Γ ↔ Exists list_env_valid (permutations (map_to_list Γ)).
  Proof.
    rewrite list_env_valid_correct, Exists_exists.
    by setoid_rewrite permutations_Permutation.
  Qed.

  Global Instance env_valid_dec (Γ : env Ti) : Decision (✓ Γ).
  Proof.
   refine (cast_if
    (decide (Exists list_env_valid (permutations (map_to_list Γ)))));
    by rewrite list_env_valid_correct_alt.
  Defined.
End env_valid_dec.

(** A nice induction principle for wellformed types. *)
Section type_env_ind.
  Context {Ti} (Γ : env Ti) (HΓ : ✓ Γ).

  Context (P : type Ti → Prop).
  Context (Pbase : ∀ τb, ✓{Γ} τb → P (baseT τb)).
  Context (Parray : ∀ τ n, ✓{Γ} τ → P τ → n ≠ 0 → P (τ.[n])).
  Context (Pcompound : ∀ c s τs,
    Γ !! s = Some τs → ✓{Γ}* τs → Forall P τs →
    1 < length τs → P (compoundT{c} s)).

  Lemma type_env_ind: ∀ τ : type Ti, ✓{Γ} τ → P τ.
  Proof.
    cut (∀ Σ τ, Σ ⊆ Γ → ✓ Σ → ✓{Σ} τ → P τ).
    { intros help τ. by apply help. }
    induction Σ as [Σ IH] using (well_founded_induction map_wf).
    intros τ HΣΓ HΣ Hτ. induction Hτ as [τb Hτb|τ n Hτ|c s Hs].
    * by apply Pbase, (base_type_valid_weaken Σ).
    * apply Parray; eauto. by apply (type_valid_weaken Σ).
    * inversion Hs as [τs Hτs].
      destruct (env_valid_lookup_subset Σ s τs) as (Σ'&?&Hτs'&Hlen&?); auto.
      assert (Σ' ⊂ Γ) by eauto using (strict_transitive_l (R:=(⊆))).
      apply Pcompound with τs; eauto using lookup_weaken.
      + apply Forall_impl with (✓{Σ'}); auto.
        intros. eapply type_valid_weaken_subset; eauto.
      + clear Hτs Hlen. induction Hτs'; constructor; auto.
        apply (IH Σ'); eauto using (strict_include (R:=(⊆):relation (env _))).
  Qed.
End type_env_ind.

(** And a weaker one for arbitrary types in a well formed environment. *)
Section weak_type_env_ind.
  Context {Ti} (Γ : env Ti) (HΓ : ✓ Γ).

  Context (P : type Ti → Prop).
  Context (Pbase : ∀ τb, P (baseT τb)).
  Context (Pvoid : P voidT).
  Context (Parray : ∀ τ n, P τ → P (τ.[n])).
  Context (Pcompound : ∀ c s τs,
    Γ !! s = Some τs → Forall P τs → P (compoundT{c} s)).
  Context (PcompoundNone : ∀ c s, Γ !! s = None → P (compoundT{c} s)).

  Lemma weak_type_env_ind τ : P τ.
  Proof.
    intros. induction τ as [τb| |τ n|c s]; auto.
    destruct (Γ !! s) as [τs|] eqn:Hs; auto.
    destruct (env_valid_lookup_subset Γ s τs) as (Σ'&?&Hτs&_&?); auto.
    apply Pcompound with τs; auto.
    clear Hs. induction Hτs as [|τ τs]; constructor; auto.
    apply (type_env_ind Γ); eauto using type_valid_weaken,
      (strict_include (R:=(⊆) : relation (env _))).
  Qed.
End weak_type_env_ind.

(** A nice iteration principle for well-formed types. *)
Section type_iter.
  Context {Ti : Set} {A : Type} (R : relation A) `{!Equivalence R}.
  Local Infix "≡" := R.
  Implicit Type τ : type Ti.
  Implicit Type Γ Σ : env Ti.

  Section definition.
    Context (fb : base_type Ti → A)
      (fv : A)
      (fa : type Ti → nat → A → A)
      (fc: compound_kind → tag → list (type Ti) → (type Ti → A) → A).

    Definition type_iter_inner
        (g : tag → list (type Ti) * (type Ti → A)) : type Ti → A :=
      fix go τ :=
      match τ with
      | baseT τb => fb τb
      | voidT => fv
      | τ.[n] => fa τ n (go τ)
      | compoundT{c} s => let (τs,h) := g s in fc c s τs h
      end%T.
    Definition type_iter_accF (Γ : env Ti) (go : ∀ Σ, Σ ⊂ Γ → type Ti → A)
        (s : tag) : list (type Ti) * (type Ti → A) :=
      match Some_dec (Γ !! s) with
      | inleft (τs↾Hτs) => (τs, go (delete s Γ) (delete_subset_alt _ _ _ Hτs))
      | inright _ => ([], λ _, fv) (**i dummy *)
      end.
    Definition type_iter_acc : ∀ Γ : env Ti, Acc (⊂) Γ → type Ti → A :=
      Fix_F _ (λ Γ go, type_iter_inner (type_iter_accF Γ go)).
    Definition type_iter (Γ : env Ti) : type Ti → A :=
      type_iter_acc _ (wf_guard 32 map_wf Γ).
  End definition.

  Lemma type_iter_acc_weaken fb1 fb2 fv fa1 fa2 fc1 fc2 Γ Σ1 Σ2 acc1 acc2 τ :
    ✓ Γ →
    (∀ τb, ✓{Γ} τb → fb1 τb ≡ fb2 τb) →
    (∀ τ n x y, ✓{Γ} τ → x ≡ y → fa1 τ n x ≡ fa2 τ n y) →
    (∀ rec1 rec2 c s τs,
      Γ !! s = Some τs → ✓{Γ}* τs → Forall (λ τ, rec1 τ ≡ rec2 τ) τs →
      fc1 c s τs rec1 ≡ fc2 c s τs rec2) →
    ✓{Γ} τ → Γ ⊆ Σ1 → Γ ⊆ Σ2 →
    type_iter_acc fb1 fv fa1 fc1 Σ1 acc1 τ ≡
      type_iter_acc fb2 fv fa2 fc2 Σ2 acc2 τ.
  Proof.
    intros HΓ Hbase Harray. revert Σ1 Σ2 acc1 acc2 τ HΓ.
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
    apply Hcompound; eauto using types_valid_weaken.
    assert (is_Some (Γ !! s)) by eauto. clear Hs Hlen acc1 acc2.
    induction Hτs as [|τ τs]; constructor; auto. apply (IH Γ').
    * eauto using (strict_transitive_r (R:=(⊆))),
        delete_subset, lookup_weaken_is_Some.
    * eauto using base_type_valid_weaken.
    * eauto using type_valid_weaken.
    * done.
    * eauto using lookup_weaken, types_valid_weaken.
    * done.
    * transitivity (delete s Γ); eauto using delete_subseteq_compat.
    * transitivity (delete s Γ); eauto using delete_subseteq_compat.
  Qed.
  Lemma type_iter_weaken fb1 fb2 fv fa1 fa2 fc1 fc2 Γ Σ τ :
    ✓ Γ →
    (∀ τb, ✓{Γ} τb → fb1 τb ≡ fb2 τb) →
    (∀ τ n x y, ✓{Γ} τ → x ≡ y → fa1 τ n x ≡ fa2 τ n y) →
    (∀ rec1 rec2 c s τs,
      Γ !! s = Some τs → ✓{Γ}* τs → Forall (λ τ, rec1 τ ≡ rec2 τ) τs →
      fc1 c s τs rec1 ≡ fc2 c s τs rec2) →
    ✓{Γ} τ → Γ ⊆ Σ →
    type_iter fb1 fv fa1 fc1 Γ τ ≡ type_iter fb2 fv fa2 fc2 Σ τ.
  Proof. intros. by apply (type_iter_acc_weaken _ _ _ _ _ _ _ Γ). Qed.

  Lemma type_iter_base fb fv fa fc Γ τb :
    type_iter fb fv fa fc Γ (baseT τb) = fb τb.
  Proof. done. Qed.
  Lemma type_iter_void fb fv fa fc Γ : type_iter fb fv fa fc Γ voidT = fv.
  Proof. done. Qed.
  Lemma type_iter_array fb fv fa fc Γ τ n :
    type_iter fb fv fa fc Γ (τ.[n]) = fa τ n (type_iter fb fv fa fc Γ τ).
  Proof. unfold type_iter. by destruct (wf_guard _ map_wf Γ). Qed.
  Lemma type_iter_compound fb fv fa fc Γ c s τs :
    ✓ Γ →
    (∀ τ n x y, ✓{Γ} τ → x ≡ y → fa τ n x ≡ fa τ n y) →
    (∀ rec1 rec2 c s τs,
      Γ !! s = Some τs → ✓{Γ}* τs → Forall (λ τ, rec1 τ ≡ rec2 τ) τs →
      fc c s τs rec1 ≡ fc c s τs rec2) →
    Γ !! s = Some τs →
    type_iter fb fv fa fc Γ (compoundT{c} s) ≡
      fc c s τs (type_iter fb fv fa fc Γ).
  Proof.
    intros ? Harray Hcompound Hs. unfold type_iter at 1.
    destruct (wf_guard _ map_wf Γ) as [accΓ]. simpl.
    unfold type_iter_accF.
    destruct (Some_dec (Γ !! s)) as [[τs' Hs']|?]; [|congruence].
    generalize (accΓ _ (delete_subset_alt Γ s τs' Hs')). intros accΓ'.
    simplify_map_equality.
    destruct (env_valid_delete Γ s τs) as (Γ'&?&Hτs&Hlen&?); trivial.
    assert (Γ' ⊆ Γ) by (transitivity (delete s Γ); auto using delete_subseteq).
    apply Hcompound; eauto using types_valid_weaken.
    clear Hs Hlen. induction Hτs; constructor; auto.
    by apply (type_iter_acc_weaken _ _ _ _ _ _ _ Γ');
      eauto using lookup_weaken, type_valid_weaken, types_valid_weaken.
  Qed.
  Lemma type_iter_compound_None fb fv fa fc Γ c s :
    Γ !! s = None →
    type_iter fb fv fa fc Γ (compoundT{c} s) = fc c s [] (λ _, fv).
  Proof.
    intros Hs. unfold type_iter.
    destruct (wf_guard _ map_wf Γ) as [accΓ]; simpl.
    unfold type_iter_accF. destruct (Some_dec _) as [[??]|?]; congruence.
  Qed.
End type_iter.
