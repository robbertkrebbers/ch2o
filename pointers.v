(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import nmap mapset fragmented.
Require Export references.
Local Open Scope ctype_scope.

(** * Pointer casts *)
Reserved Infix ">*>" (at level 70).
Inductive castable `{IntEnv Ti} `{PtrEnv Ti} : type Ti → type Ti → Prop :=
  | castable_void τ : τ >*> void
  | castable_uchar τ : τ >*> uchar
  | castable_refl τ : τ >*> τ
where "τ >*> σ" := (@castable _ _ _ τ σ) : C_scope.
Notation "(>*>)" := castable (only parsing) : C_scope.

Section castable.
  Context `{EnvSpec Ti}.

  Global Instance castable_dec (τ1 τ2 : type Ti) : Decision (τ1 >*> τ2).
  Proof.
   refine
    (if decide (τ2 = void) then left _ else
    if decide (τ2 = uchar) then left _ else cast_if (decide (τ1 = τ2)));
    first [by subst; constructor | by inversion 1; subst].
  Defined.
  Global Instance: Reflexive (>*>).
  Proof. constructor. Qed.

  Lemma castable_alt τ1 τ2 : τ1 >*> τ2 ↔ τ1 = τ2 ∨ τ2 = uchar ∨ τ2 = void.
  Proof. split. destruct 1; auto. intros [-> |[->| ->]]; constructor. Qed.

  Lemma castable_type_valid τ σ :
    type_valid get_env τ → τ >*> σ → type_valid get_env σ ∨ σ = void.
  Proof. destruct 2; auto; left; repeat constructor. Qed.
  Lemma castable_ptr_type_valid τ σ :
    ptr_type_valid get_env τ → τ >*> σ → ptr_type_valid get_env σ.
  Proof. destruct 2; auto; repeat constructor. Qed.

  Lemma castable_size_of τ σ :
    type_valid get_env τ → τ >*> σ → size_of σ ≤ size_of τ.
  Proof.
    intros Hτ. pose proof (size_of_pos _ Hτ). rewrite castable_alt.
    intros [?|[?|?]]; subst; auto.
    * rewrite size_of_int, int_size_char; lia.
    * rewrite size_of_void; lia.
  Qed.
  Lemma castable_size_of_pos τ σ :
    type_valid get_env τ → τ >*> σ → 0 < size_of σ.
  Proof.
    intros. destruct (castable_type_valid τ σ) as [?|?]; subst;
      auto using size_of_pos. rewrite size_of_void; lia.
  Qed.
  Lemma castable_size_of_ne_0 τ σ :
    type_valid get_env τ → τ >*> σ → size_of σ ≠ 0.
  Proof. intros. eapply Nat.neq_0_lt_0, castable_size_of_pos; eauto. Qed.
End castable.

(** * Indexes into the memory *)
(** We define indexes into the memory as binary naturals and use the [Nmap]
implementation to obtain efficient finite maps and finite sets with these
indexes as keys. *)
Definition index := N.
Definition indexmap := Nmap.
Notation indexset := (mapset indexmap).

Instance index_dec: ∀ i1 i2 : index, Decision (i1 = i2) := decide_rel (=).
Instance index_fresh_`{FinCollection index C} : Fresh index C := _.
Instance index_fresh_spec `{FinCollection index C} : FreshSpec index C := _.
Instance index_inhabited: Inhabited index := populate 0%N.

Instance indexmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : indexmap A, Decision (m1 = m2) := decide_rel (=).
Instance indexmap_empty {A} : Empty (indexmap A) := @empty (Nmap A) _.
Instance indexmap_lookup {A} : Lookup index A (indexmap A) :=
  @lookup _ _ (Nmap A) _.
Instance indexmap_partial_alter {A} : PartialAlter index A (indexmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance indexmap_to_list {A} : FinMapToList index A (indexmap A) :=
  @map_to_list _ _ (Nmap A) _.
Instance indexmap_merge: Merge indexmap := @merge Nmap _.
Instance indexmap_fmap: FMap indexmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap index indexmap := _.

Instance indexmap_dom {A} : Dom (indexmap A) indexset := mapset_dom.
Instance: FinMapDom index indexmap indexset := mapset_dom_spec.

Instance index_lexico : Lexico index := @lexico N _.
Instance index_lexico_po : PartialOrder (@lexico index _) := _.
Instance index_trichotomy: TrichotomyT (@lexico index _) := _.

Typeclasses Opaque index indexmap.

Class TypeOfIndex (Ti : Set) (M : Type) :=
  type_of_index : M → index → option (type Ti).
Class IndexAlive (M : Type) :=
  index_alive : M → index → Prop.

Class MemorySpec (Ti : Set) M `{TypeOfIndex Ti M} `{IndexAlive M}
    `{Valid () M} `{IntEnv Ti} `{PtrEnv Ti}
    `{∀ m x, Decision (index_alive m x)} := {
  mem_env_spec :>> EnvSpec Ti;
  mem_inhabited :> Inhabited M;
  type_of_index_valid m x τ :
    ⊢ valid m → type_of_index m x = Some τ → type_valid get_env τ;
  type_of_index_typed m x τ :
    ⊢ valid m → type_of_index m x = Some τ → int_typed (size_of τ) sptr
}.

(** * Addresses *)
Record addr (Ti : Set) := Addr {
  addr_index : index;
  addr_ref_base : ref;
  addr_byte : nat;
  addr_type_base : type Ti;
  addr_type : type Ti
}.
Add Printing Constructor addr.
Arguments Addr {_} _ _ _ _ _.
Arguments addr_index {_} _.
Arguments addr_ref_base {_} _.
Arguments addr_byte {_} _.
Arguments addr_type_base {_} _.
Arguments addr_type {_} _.

Instance addr_eq_dec {Ti : Set} `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}
  (a1 a2 : addr Ti) : Decision (a1 = a2).
Proof. solve_decision. Defined.

Section addr_operations.
  Context `{IntEnv Ti} `{PtrEnv Ti} `{TypeOfIndex Ti M} `{IndexAlive M}.

  Inductive addr_typed' (m : M) : addr Ti → type Ti → Prop :=
    Addr_typed x r (i : nat) τ σ σc :
      ref_offset r = 0 →
      type_of_index m x = Some τ →
      type_valid get_env τ →
      (* to avoid parametrization by valid memories everywhere *)
      r @ τ ↣ σ →
      σ >*> σc →
      i ≤ size_of σ * ref_size r →
      i `mod` size_of σc = 0 →
      addr_typed' m (Addr x r i σ σc) σc.
  Global Instance addr_typed: Typed M (type Ti) (addr Ti) := addr_typed'.

  Global Instance type_of_addr: TypeOf (type Ti) (addr Ti) := addr_type.
  Global Instance addr_type_check: TypeCheck M (type Ti) (addr Ti) := λ m a,
    let 'Addr x r i σ σc := a in
    guard (ref_offset r = 0);
    τ ← type_of_index m x;
    guard (type_valid get_env τ);
    σ' ← τ !! r;
    guard (σ' = σ);
    guard (σ >*> σc);
    guard (i ≤ size_of σ * ref_size r);
    guard (i `mod` size_of σc = 0);
    Some σc.
  Global Arguments addr_type_check _ !_ /.

  Global Instance addr_frozen: Frozen (addr Ti) := λ a,
    Forall frozen (addr_ref_base a).
  Global Instance addr_freeze: Freeze (addr Ti) := λ a,
    let 'Addr x r i σ σc := a in Addr x (freeze <$> r) i σ σc.

  Definition addr_byte_size (a : addr Ti) : nat :=
    size_of (addr_type_base a) * ref_size (addr_ref_base a).
  Global Arguments addr_byte_size !_ /.
  Definition addr_strict (m : M) (a : addr Ti) : Prop :=
    index_alive m (addr_index a) ∧
    addr_byte a < addr_byte_size a ∧
    type_of a ≠ void.
  Global Arguments addr_strict _ !_ /.
  Definition addr_is_obj (a : addr Ti) : Prop :=
    type_of a = addr_type_base a.
  Global Arguments addr_is_obj !_ /.
  Definition addr_offset (a : addr Ti) : nat :=
    addr_byte a `div` size_of' a.
  Global Arguments addr_offset !_ /.

  Definition addr_ref (a : addr Ti) : ref :=
    ref_set_offset (addr_byte a `div` size_of (addr_type_base a))
      (addr_ref_base a).
  Global Arguments addr_ref !_ /.
  Definition addr_ref_byte (a : addr Ti) : nat :=
    addr_byte a `mod` size_of (addr_type_base a).
  Global Arguments addr_ref_byte !_ /.

  Global Instance addr_disjoint: Disjoint (addr Ti) := λ a1 a2,
    (addr_index a1 ≠ addr_index a2) ∨
    (addr_index a1 = addr_index a2 ∧ addr_ref a1 ⊥ addr_ref a2) ∨
    (addr_index a1 = addr_index a2 ∧
      freeze <$> addr_ref a1 = freeze <$> addr_ref a2 ∧
      ¬addr_is_obj a1 ∧ ¬addr_is_obj a2 ∧
      addr_ref_byte a1 ≠ addr_ref_byte a2).

  Definition addr_new (x : index) (τ : type Ti) : addr Ti := Addr x [] 0 τ τ.

  Definition addr_plus_ok (m : M) (j : Z) (a : addr Ti) : Prop :=
    index_alive m (addr_index a) ∧
    (0 ≤ addr_byte a + j * size_of' a ≤ addr_byte_size a)%Z.
  Global Arguments addr_plus_ok _ _ !_ /.
  Definition addr_plus (j : Z) (a : addr Ti): addr Ti :=
    let 'Addr x r i σ σc := a in Addr x r (Z.to_nat (i + j * size_of σc)) σ σc.
  Global Arguments addr_plus _ !_ /.

  Definition addr_minus_ok (m : M) (a1 a2 : addr Ti) : Prop :=
    index_alive m (addr_index a1) ∧
    freeze <$> addr_ref_base a1 = freeze <$> addr_ref_base a2.
  Global Arguments addr_minus_ok _ !_ !_ /.
  Definition addr_minus (a1 a2 : addr Ti) : Z :=
    (addr_offset a1 - addr_offset a2)%Z.
  Global Arguments addr_minus !_ !_ /.

  Definition addr_cast_ok (σc : type Ti) (a : addr Ti) : Prop :=
    addr_type_base a >*> σc ∧ addr_byte a `mod` size_of σc = 0.
  Global Arguments addr_cast_ok _ !_ /.
  Definition addr_cast (σc : type Ti) (a : addr Ti) : addr Ti :=
    let 'Addr x r i σ _ := a in Addr x r i σ σc.
  Global Arguments addr_cast _ !_ /.

  Definition addr_array (a : addr Ti) : addr Ti :=
    match type_of a with
    | τ.[n] => Addr (addr_index a) (RArray 0 n :: addr_ref a) 0 τ τ
    | _ => a
    end.
  Global Arguments addr_array !_ /.
  Definition addr_struct (i : nat) (a : addr Ti) : addr Ti :=
    match type_of a with
    | struct s =>
       match get_env !! s ≫= (!! i) with
       | Some τ => Addr (addr_index a) (RStruct i s :: addr_ref a) 0 τ τ
       | _ => a
       end
    | _ => a
    end.
  Global Arguments addr_struct _ !_ /.
  Definition addr_union (i : nat) (a : addr Ti) : addr Ti :=
    match type_of a with
    | union s =>
       match get_env !! s ≫= (!! i) with
       | Some τ => Addr (addr_index a) (RUnion i s false :: addr_ref a) 0 τ τ
       | _ => a
       end
    | _ => a
    end.
  Global Arguments addr_union _ !_ /.
End addr_operations.

Section addresses.
  Context `{MemorySpec Ti M}.

  Implicit Types a : addr Ti.
  Implicit Types m : M.
  Implicit Types τ σ : type Ti.
  Implicit Types r : ref.

  Lemma addr_freeze_frozen a : frozen (freeze a).
  Proof. destruct a. apply ref_freeze_frozen. Qed.
  Lemma addr_frozen_freeze a : frozen a → freeze a = a.
  Proof. intros. destruct a; simpl. by rewrite ref_frozen_freeze. Qed.
  Lemma addr_frozen_alt a : frozen a ↔ freeze a = a.
  Proof.
    split; intros E; eauto using addr_frozen_freeze.
    rewrite <-E. eauto using addr_freeze_frozen.
  Qed.

  Lemma addr_freeze_idempotent a : freeze (freeze a) = freeze a.
  Proof. apply addr_frozen_freeze, addr_freeze_frozen. Qed.
  Lemma addr_freeze_idempotent_alt a : freeze a ~{freeze} a.
  Proof. by apply addr_freeze_idempotent. Qed.
  Global Instance: Proper ((~{freeze}) ==> (=)) (@freeze (addr Ti) _).
  Proof. by intros ???. Qed.
  Global Instance: Symmetric (@disjoint (addr Ti) _).
  Proof.
    intros a1 a2. unfold disjoint, addr_disjoint.
    rewrite !(symmetry_iff (⊥) (addr_ref a1)). naive_solver auto.
  Qed.

  Lemma addr_typed_alt m a σ :
    m ⊢ a : σ ↔ ∃ τ,
      ref_offset (addr_ref_base a) = 0 ∧
      type_of_index m (addr_index a) = Some τ ∧
      type_valid get_env τ ∧
      addr_ref_base a @ τ ↣ addr_type_base a ∧
      addr_type_base a >*> σ ∧
      addr_byte a ≤ addr_byte_size a ∧
      addr_byte a `mod` size_of σ = 0 ∧
      type_of a = σ.
  Proof.
    split.
    * destruct 1; simpl; eauto 10.
    * intros (?&?&?&?&?&?&?&?&?). destruct a; simpl in *; subst.
      econstructor; eauto.
  Qed.

  Lemma addr_typed_offset m a σ : m ⊢ a : σ → ref_offset (addr_ref_base a) = 0.
  Proof. by destruct 1. Qed.
  Lemma addr_typed_base_type_valid m a σ :
    m ⊢ a : σ → type_valid get_env (addr_type_base a).
  Proof. destruct 1. eauto using ref_typed_type_valid, type_of_index_valid. Qed.
  Lemma addr_typed_cast m a σ : m ⊢ a : σ → addr_type_base a >*> σ.
  Proof. by destruct 1. Qed.
  Lemma addr_typed_byte_size m a σ : m ⊢ a : σ → addr_byte a ≤ addr_byte_size a.
  Proof. by destruct 1. Qed.
  Lemma addr_offset_alligned m a σ : m ⊢ a : σ → addr_byte a `mod` size_of σ = 0.
  Proof. by destruct 1. Qed.

  Lemma addr_typed_ref_base m a σ :
    m ⊢ a : σ → ∃ τ,
      type_of_index m (addr_index a) = Some τ ∧
      addr_ref_base a @ τ ↣ addr_type_base a.
  Proof. destruct 1; eauto 10. Qed.
  Lemma addr_typed_ref m a σ :
    m ⊢ a : σ → addr_strict m a → ∃ τ,
      type_of_index m (addr_index a) = Some τ ∧
      addr_ref a @ τ ↣ addr_type_base a.
  Proof.
    intros ? (?&?&?). destruct (addr_typed_ref_base m a σ) as (τ&?&?); auto.
    exists τ; split; auto. apply ref_set_offset_typed; auto.
    apply Nat.div_lt_upper_bound;
      eauto using size_of_ne_0, addr_typed_base_type_valid.
  Qed.
  Lemma addr_typed_ref_type_base_inv m a σ τ σ' :
    m ⊢ a : σ → type_of_index m (addr_index a) = Some τ →
    addr_ref a @ τ ↣ σ' → σ' = addr_type_base a.
  Proof.
    intros [] ??; simplify_option_equality.
    eauto using ref_set_offset_typed_unique, eq_sym.
  Qed.

  Lemma addr_typed_type_valid m a τ :
    m ⊢ a : τ → type_valid get_env τ ∨ τ = void.
  Proof.
    destruct 1 as [x r i τ σ σc]. destruct (castable_type_valid σ σc);
      subst; eauto using ref_typed_type_valid, type_of_index_valid.
  Qed.
  Lemma addr_size_of_type_pos m a τ : m ⊢ a : τ → 0 < size_of τ.
  Proof.
    intros. destruct (addr_typed_type_valid m a τ); subst;
      auto using size_of_pos. rewrite size_of_void; lia.
  Qed.

  Lemma addr_typed_ptr_type_valid m a τ : m ⊢ a : τ → ptr_type_valid get_env τ.
  Proof.
    intros. destruct (addr_typed_type_valid m a τ); subst;
      auto using TVoid_ptr_valid, type_valid_ptr_type_valid.
  Qed.

  Global Instance: TypeOfSpec M (type Ti) (addr Ti).
  Proof. by destruct 1. Qed.
  Global Instance: TypeCheckSpec M (type Ti) (addr Ti).
  Proof.
    intros m a τ. split.
    * destruct a; intros; simplify_option_equality;
        econstructor; eauto using path_type_check_sound.
    * destruct 1; simplify_option_equality; try done.
      by erewrite path_type_check_complete by eauto; simplify_option_equality.
  Qed.
  Lemma addr_typed_weaken_mem m1 m2 a τ :
    (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
    m1 ⊢ a : τ → m2 ⊢ a : τ.
  Proof. destruct 2; econstructor; eauto. Qed.


  Lemma addr_byte_size_typed m a σc :
    ⊢ valid m → m ⊢ a : σc → int_typed (addr_byte_size a) sptr.
  Proof.
    intros ? [x r i τ σ σc' ???????]. split.
    { transitivity 0; auto using int_lower_nonpos with zpos. }
    unfold addr_byte_size; simpl. apply Z.le_lt_trans with (size_of τ).
    { by apply Nat2Z.inj_le, size_of_ref. }
    apply int_typed_upper; eauto using type_of_index_typed.
  Qed.
  Lemma addr_byte_typed m a σc :
    ⊢ valid m → m ⊢ a : σc → int_typed (addr_byte a) sptr.
  Proof.
    intros. split.
    { transitivity 0; auto using int_lower_nonpos with zpos. }
    apply Z.le_lt_trans with (addr_byte_size a).
    { apply Nat2Z.inj_le. eauto using addr_typed_byte_size. }
    eauto using int_typed_upper, addr_byte_size_typed.
  Qed.
  Lemma addr_offset_typed m a σc :
    ⊢ valid m → m ⊢ a : σc → int_typed (addr_offset a) sptr.
  Proof.
    unfold addr_offset. intros. split.
    { transitivity 0; auto using int_lower_nonpos with zpos. }
    assert (0 < size_of' a)%Z.
    { erewrite type_of_correct by eauto.
      eapply (Nat2Z.inj_lt 0), addr_size_of_type_pos; eauto. }
    rewrite Z2Nat_inj_div. apply Z.div_lt_upper_bound; auto.
    apply Z.lt_le_trans with (1 * int_upper sptr)%Z.
    * rewrite Z.mul_1_l. eauto using int_typed_upper, addr_byte_typed.
    * apply Z.mul_le_mono_pos_r; auto using int_upper_pos with lia.
  Qed.

  Lemma addr_index_freeze a : addr_index (freeze a) = addr_index a.
  Proof. by destruct a. Qed.
  Global Instance: Proper ((~{freeze}) ==> (=)) (@addr_index Ti).
  Proof.
    intros ?? Ha. by rewrite <-addr_index_freeze, Ha, addr_index_freeze.
  Qed.
  Lemma addr_ref_base_freeze a :
    addr_ref_base (freeze a) = freeze <$> addr_ref_base a.
  Proof. by destruct a. Qed.
  Global Instance:
    Proper ((~{freeze}) ==> (~{fmap freeze})) (@addr_ref_base Ti).
  Proof.
    intros ?? Ha. unfold proj_eq. by rewrite <-!addr_ref_base_freeze, Ha.
  Qed.
  Lemma addr_byte_freeze a : addr_byte (freeze a) = addr_byte a.
  Proof. by destruct a. Qed.
  Global Instance: Proper ((~{freeze}) ==> (=)) (@addr_byte Ti).
  Proof. intros ?? Ha. by rewrite <-addr_byte_freeze, Ha, addr_byte_freeze. Qed.
  Lemma addr_type_base_freeze a : addr_type_base (freeze a) = addr_type_base a.
  Proof. by destruct a. Qed.
  Global Instance: Proper ((~{freeze}) ==> (=)) (@addr_type_base Ti).
  Proof.
    intros ?? Ha. by rewrite <-addr_type_base_freeze, Ha, addr_type_base_freeze.
  Qed.
  Lemma addr_type_of_freeze a : type_of (freeze a) = type_of a.
  Proof. by destruct a. Qed.
  Global Instance: Proper ((~{freeze}) ==> (=)) (@type_of (type _) (addr Ti) _).
  Proof.
    intros ?? Ha. by rewrite <-addr_type_of_freeze, Ha, addr_type_of_freeze.
  Qed.
  Lemma addr_offset_freeze a : addr_offset (freeze a) = addr_offset a.
  Proof. by destruct a. Qed.
  Global Instance: Proper ((~{freeze}) ==> (=)) (@addr_offset Ti _).
  Proof.
    intros ?? Ha. by rewrite <-addr_offset_freeze, Ha, addr_offset_freeze.
  Qed.
  Lemma addr_ref_freeze a : addr_ref (freeze a) = freeze <$> addr_ref a.
  Proof.
    unfold addr_ref. by rewrite !addr_ref_base_freeze, addr_byte_freeze,
      addr_type_base_freeze, ref_set_offset_freeze.
  Qed.
  Global Instance: Proper ((~{freeze}) ==> (~{fmap freeze})) (@addr_ref Ti _).
  Proof. intros ?? Ha. unfold proj_eq. by rewrite <-!addr_ref_freeze, Ha. Qed.
  Lemma addr_is_obj_freeze a : addr_is_obj (freeze a) ↔ addr_is_obj a.
  Proof.
    unfold addr_is_obj. by rewrite addr_type_of_freeze, addr_type_base_freeze.
  Qed.
  Global Instance: Proper ((~{freeze}) ==> iff) (@addr_is_obj Ti).
  Proof.
    intros ?? Ha. by rewrite <-addr_is_obj_freeze, Ha, addr_is_obj_freeze.
  Qed.

  Lemma addr_ref_byte_freeze a : addr_ref_byte (freeze a) = addr_ref_byte a.
  Proof.
    unfold addr_ref_byte. by rewrite addr_byte_freeze, addr_type_base_freeze.
  Qed.
  Global Instance: Proper ((~{freeze}) ==> (=)) (@addr_ref_byte Ti _).
  Proof.
    intros ?? Ha. by rewrite <-addr_ref_byte_freeze, Ha, addr_ref_byte_freeze.
  Qed.

  Lemma addr_typed_freeze m a τ : m ⊢ freeze a : τ ↔ m ⊢ a : τ.
  Proof.
    split.
    * destruct a as [x r i σ σc]; inversion_clear 1. econstructor; eauto.
      + by rewrite <-ref_offset_freeze.
      + by apply ref_typed_freeze.
      + by rewrite <-ref_size_freeze.
    * destruct 1 as [x r i τ σ σc]; econstructor; eauto.
      + by rewrite ref_offset_freeze.
      + by apply ref_typed_freeze.
      + by rewrite ref_size_freeze.
  Qed.
  Global Instance:
    Proper ((~{freeze}) ==> (=) ==> iff) (@typed _ _ (addr Ti) _ m).
  Proof.
    intros ? ?? Ha ?? <-. by rewrite <-addr_typed_freeze, Ha, addr_typed_freeze.
  Qed.
  Lemma addr_type_check_freeze m a : type_check m (freeze a) = type_check m a.
  Proof.
    apply option_eq. intros. by rewrite !type_check_correct, addr_typed_freeze.
  Qed.

  Global Instance:
    Proper ((~{freeze}) ==> (~{freeze}) ==> iff) (@disjoint (addr Ti) _).
  Proof.
    assert (∀ r1 r2, freeze <$> r1 ⊥ r2 ↔ r1 ⊥ r2) as help.
    { intros. by rewrite ref_freeze_idempotent_alt. }
    assert (∀ a1 a2, freeze a1 ⊥ a2 ↔ a1 ⊥ a2) as help2.
    { intros a1 a2. unfold disjoint, addr_disjoint.
      by rewrite !addr_index_freeze, !addr_ref_freeze, !addr_is_obj_freeze,
        !addr_ref_byte_freeze, !ref_freeze_idempotent, help. }
    intros a1 a2 Ha12 a3 a4 Ha34. rewrite <-(help2 a1), Ha12, help2.
    by rewrite (symmetry_iff (⊥) a2), <-(help2 a3), Ha34, help2.
  Qed.

  Global Instance addr_is_strict_dec a : Decision (addr_strict m a).
  Proof. apply _. Defined.
  Global Instance addr_frozen_dec a : Decision (frozen a).
  Proof. apply _. Defined.
  Global Instance addr_disjoint_dec a1 a2 : Decision (a1 ⊥ a2).
  Proof. apply _. Defined.

  Lemma addr_strict_not_void m a σ : m ⊢ a : σ → addr_strict m a → σ ≠ void.
  Proof. by intros ? (?&?&?); simplify_type_equality. Qed.
  Lemma addr_is_obj_ref_byte m a σ :
    m ⊢ a : σ → addr_is_obj a → addr_ref_byte a = 0.
  Proof. by intros [x r i τ σ' σc] ?; simpl in *; subst. Qed.
  Lemma addr_is_obj_type_base m a σ :
    m ⊢ a : σ → addr_is_obj a → addr_type_base a = σ.
  Proof. by intros [x r i τ σ' σc] ?. Qed.
  Lemma addr_not_is_obj_type m a σ :
    m ⊢ a : σ → ¬addr_is_obj a → σ ≠ void → σ = uchar.
  Proof.
    intros [x r i τ σ' σc] ??. destruct (proj1 (castable_alt σ' σc))
      as [?|[?|?]]; simplify_equality'; auto.
  Qed.

  Lemma addr_ref_typed m a σ :
    m ⊢ a : σ → addr_strict m a →
    ∃ τ, type_of_index m (addr_index a) = Some τ ∧
      addr_ref a @ τ ↣ addr_type_base a.
  Proof.
    intros [x r i τ σ' σc Hr] (?&?&?); simpl in *. exists τ. split; auto.
    apply ref_set_offset_typed; auto. apply Nat.div_lt_upper_bound;
      eauto using size_of_ne_0, ref_typed_type_valid, type_of_index_valid.
  Qed.
  Lemma addr_byte_range m a σ :
    m ⊢ a : σ → addr_strict m a → addr_ref_byte a < size_of (addr_type_base a).
  Proof.
    intros. apply Nat.mod_bound_pos; auto with lia.
    eapply size_of_pos, addr_typed_base_type_valid; eauto.
  Qed.

  Lemma addr_plus_ok_typed m a σ j :
    m ⊢ a : σ → addr_plus_ok m j a → m ⊢ addr_plus j a : σ.
  Proof.
    intros [x r i τ σ' σc Hr] (?&?&?); simpl in *. econstructor; eauto.
    { apply Nat2Z.inj_le. by rewrite Z2Nat.id by done. }
    apply Nat2Z.inj. rewrite Z2Nat_inj_mod, Z2Nat.id by done.
    rewrite Z.mod_add, <-Z2Nat_inj_mod; auto with f_equal.
    rewrite (Nat2Z.inj_iff _ 0). eauto using castable_size_of_ne_0,
      ref_typed_type_valid, type_of_index_valid.
  Qed.
  Lemma addr_type_plus a j : type_of (addr_plus j a) = type_of a.
  Proof. by destruct a. Qed.
  Lemma addr_type_base_plus a j :
    addr_type_base (addr_plus j a) = addr_type_base a.
  Proof. by destruct a. Qed.
  Lemma addr_index_plus a j : addr_index (addr_plus j a) = addr_index a.
  Proof. by destruct a. Qed.
  Lemma addr_byte_size_plus a j :
    addr_byte_size (addr_plus j a) = addr_byte_size a.
  Proof. by destruct a. Qed.
  Lemma addr_plus_0 a : addr_plus 0 a = a.
  Proof. destruct a; simpl. by rewrite Z.mul_0_l, Z.add_0_r, Nat2Z.id. Qed.
  Lemma addr_plus_plus a j1 j2 :
    (0 ≤ addr_byte a + j2 * size_of' a)%Z →
    addr_plus j1 (addr_plus j2 a) = addr_plus (j1 + j2) a.
  Proof.
    intros. destruct a as [x r i τ σ]; simpl; do 2 f_equal.
    by rewrite Z2Nat.id, (Z.add_comm j1), Z.mul_add_distr_r, Z.add_assoc.
  Qed.
  Lemma addr_plus_plus_nat a (j1 j2 : nat) :
    addr_plus j1 (addr_plus j2 a) = addr_plus (j1 + j2)%nat a.
  Proof. rewrite Nat2Z.inj_add. apply addr_plus_plus; auto with zpos. Qed.
  Lemma addr_is_obj_plus a j : addr_is_obj (addr_plus j a) ↔ addr_is_obj a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_base_plus a j :
    addr_ref_base (addr_plus j a) = addr_ref_base a.
  Proof. by destruct a. Qed.

  Lemma addr_minus_ok_typed m a1 a2 σ :
    ⊢ valid m → m ⊢ a1 : σ → m ⊢ a2 : σ → int_typed (addr_minus a1 a2) sptr.
  Proof.
    intros Hm Ha1 Ha2. unfold addr_minus.
    destruct (addr_offset_typed m a1 σ Hm Ha1),
      (addr_offset_typed m a2 σ Hm Ha2).
    red. change (int_lower sptr) with (-int_upper sptr)%Z. auto with lia.
  Qed.

  Lemma addr_cast_ok_uchar a : addr_cast_ok uchar a.
  Proof. split. constructor. by rewrite size_of_int, int_size_char. Qed.
  Lemma addr_cast_ok_typed m a σ σc :
    m ⊢ a : σ → addr_cast_ok σc a → m ⊢ addr_cast σc a : σc.
  Proof. intros [??????] [??]; econstructor; eauto. Qed.
  Lemma addr_type_cast a σc : type_of (addr_cast σc a) = σc.
  Proof. by destruct a. Qed.
  Lemma addr_index_cast a σc : addr_index (addr_cast σc a) = addr_index a.
  Proof. by destruct a. Qed.
  Lemma addr_byte_size_cast a σc :
    addr_byte_size (addr_cast σc a) = addr_byte_size a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_cast a σc : addr_ref (addr_cast σc a) = addr_ref a.
  Proof. by destruct a. Qed.
  Lemma addr_ref_byte_cast a σc :
    addr_ref_byte (addr_cast σc a) = addr_ref_byte a.
  Proof. by destruct a. Qed.
  Lemma addr_cast_self m a σ : m ⊢ a : σ → addr_cast σ a = a.
  Proof. by destruct 1. Qed.
  Lemma addr_is_obj_cast a σc :
    addr_is_obj (addr_cast σc a) ↔ σc = addr_type_base a.
  Proof. by destruct a. Qed.

  Lemma addr_ref_plus_char_cast m a σ j :
    m ⊢ a : σ → addr_is_obj a → j < size_of σ →
    addr_ref (addr_plus j (addr_cast uchar a)) = addr_ref a.
  Proof.
    destruct 1 as [x r i σ' σ]; intros ??; simplify_equality'.
    f_equal. rewrite size_of_int, int_size_char; simpl.
    rewrite Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
    symmetry. apply Nat.div_unique with (i `mod` size_of σ + j); [lia|].
    by rewrite Nat.add_assoc, <-Nat.div_mod
      by eauto using ref_typed_type_valid, size_of_ne_0.
  Qed.
  Lemma addr_ref_byte_plus_char_cast m a σ j :
    m ⊢ a : σ → addr_is_obj a → j < size_of σ →
    addr_ref_byte (addr_plus j (addr_cast uchar a)) = j.
  Proof.
    destruct 1 as [x r i σ' σ ??????? Hiσ]; intros ??; simplify_equality'.
    f_equal. rewrite size_of_int, int_size_char; simpl.
    rewrite Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
    rewrite <-Nat.add_mod_idemp_l
      by eauto using ref_typed_type_valid, size_of_ne_0.
    rewrite Hiσ, Nat.add_0_l. by apply Nat.mod_small.
  Qed.
  Lemma addr_byte_lt_size_char_cast m a σ j :
    m ⊢ a : σ → addr_is_obj a → j < size_of σ →
    addr_byte a < addr_byte_size a →
    addr_byte (addr_plus j (addr_cast uchar a)) < addr_byte_size a.
  Proof.
    destruct 1 as [x r i σ' σ ??????? Hiσ]; intros ???; simplify_equality'.
    rewrite size_of_int, int_size_char; simpl.
    rewrite Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
    apply Nat.lt_le_trans with (i + size_of σ); [lia|].
    apply Nat.div_exact in Hiσ; eauto using ref_typed_type_valid, size_of_ne_0.
    rewrite Hiσ, <-Nat.mul_succ_r. apply Nat.mul_le_mono_l, Nat.le_succ_l.
    apply Nat.div_lt_upper_bound;
      eauto using ref_typed_type_valid, size_of_ne_0.
  Qed.

  Lemma addr_array_typed m a n τ :
    m ⊢ a : τ.[n] → addr_strict m a → m ⊢ addr_array a : τ.
  Proof.
    rewrite addr_typed_alt. intros (τ'&?&?&?&?&Hcast&?&?&?) (?&?&?).
    destruct a as [x r i σ' σc]; inversion Hcast; simpl in *; subst.
    assert (type_valid get_env (τ.[n])) as Hτn by eauto using
      ref_typed_type_valid, type_of_index_valid; inversion Hτn; subst.
    econstructor; simpl; eauto.
    * econstructor; [constructor; lia |]. apply ref_set_offset_typed; auto.
      apply Nat.div_lt_upper_bound; auto using size_of_ne_0.
    * done.
    * lia.
    * by rewrite Nat.mod_0_l by eauto using size_of_ne_0.
  Qed.
  Lemma addr_struct_typed m a j s τs τ :
    m ⊢ a : struct s → addr_strict m a →
    get_env !! s = Some τs → τs !! j = Some τ → m ⊢ addr_struct j a : τ.
  Proof.
    rewrite addr_typed_alt. intros (τ'&?&?&?&?&Hcast&?&?&?) (?&?&?) ??.
    destruct a as [x r i σ' σc]; inversion Hcast; simplify_option_equality.
    econstructor; simpl; eauto.
    * econstructor; [econstructor; eauto |]. apply ref_set_offset_typed; auto.
      apply Nat.div_lt_upper_bound; eauto using size_of_ne_0, TCompound_valid.
    * done.
    * lia.
    * by rewrite Nat.mod_0_l by
        eauto using size_of_ne_0, env_valid_lookup_lookup.
  Qed.
  Lemma addr_union_typed m a j s τs τ :
    m ⊢ a : struct s → addr_strict m a →
    get_env !! s = Some τs → τs !! j = Some τ → m ⊢ addr_struct j a : τ.
  Proof.
    rewrite addr_typed_alt. intros (τ'&?&?&?&?&Hcast&?&?&?) (?&?&?) ??.
    destruct a as [x r i σ' σc]; inversion Hcast; simplify_option_equality.
    econstructor; simpl; eauto.
    * econstructor; [econstructor; eauto |]. apply ref_set_offset_typed; auto.
      apply Nat.div_lt_upper_bound; eauto using size_of_ne_0, TCompound_valid.
    * done.
    * lia.
    * by rewrite Nat.mod_0_l by
        eauto using size_of_ne_0, env_valid_lookup_lookup.
  Qed.

  Lemma addr_disjoint_cases m a1 a2 σ1 σ2 :
    m ⊢ a1 : σ1 → m ⊢ a2 : σ2 →
    frozen a1 → frozen a2 → addr_is_obj a1 → addr_is_obj a2 →
    (**i 1.) *) (∀ j1 j2, addr_plus j1 a1 ⊥ addr_plus j2 a2) ∨
    (**i 2.) *) σ1 ⊆ σ2 ∨
    (**i 3.) *) σ2 ⊆ σ1 ∨
    (**i 4.) *) addr_index a1 = addr_index a2 ∧ (∃ s r1' i1 r2' i2 r',
      addr_ref_base a1 = r1' ++ [RUnion i1 s false] ++ r' ∧
      addr_ref_base a2 = r2' ++ [RUnion i2 s false] ++ r' ∧ i1 ≠ i2).
  Proof.
    intros Ha1 Ha2 ????. destruct (decide (addr_index a1 = addr_index a2));
      [|by do 2 left; rewrite !addr_index_plus].
    destruct (addr_typed_ref_base m a1 σ1) as (τ&?&?); auto.
    destruct (addr_typed_ref_base m a2 σ2) as (τ'&?&?); auto.
    assert (τ' = τ) by congruence; subst.
    unfold disjoint, addr_disjoint. destruct (ref_disjoint_cases τ
      (addr_ref_base a1) (addr_ref_base a2)
      (addr_type_base a1) (addr_type_base a2))
      as [?|[?|[?|(s&r1'&i1&r2'&i2&r'&Hr1'&Hr2'&?)]]]; auto.
    * left. intros j1 j2. right; left. rewrite !addr_index_plus.
      split; auto. destruct a1, a2; simpl; eauto.
    * right; left. by rewrite <-(addr_is_obj_type_base m a1 σ1),
        <-(addr_is_obj_type_base m a2 σ2) by done.
    * do 2 right; left. by rewrite <-(addr_is_obj_type_base m a1 σ1),
        <-(addr_is_obj_type_base m a2 σ2) by done.
    * do 3 right. split; auto. unfold addr_ref.
      generalize (addr_offset a2 `div` size_of (addr_type_base a2)).
      generalize (addr_offset a1 `div` size_of (addr_type_base a1)).
      intros j1 j2. destruct r1' as [|rs1 r1'], r2' as [|rs2 r2'].
      + eexists s, [], i1, [], i2, r'. by rewrite Hr1', Hr2'.
      + eexists s, [], i1, (rs2 :: r2'), i2, r'. by rewrite Hr1', Hr2'.
      + eexists s, (rs1 :: r1'), i1, [], i2, r'. by rewrite Hr1', Hr2'.
      + eexists s, (rs1 :: r1'), i1, (rs2 :: r2'), i2, r'.
        by rewrite Hr1', Hr2'.
  Qed.
End addresses.

(** * Pointers *)
Inductive ptr Ti := NULL : type Ti → ptr Ti | Ptr : addr Ti → ptr Ti.
Arguments NULL {_} _.
Arguments Ptr {_} _.

Instance ptr_eq_dec {Ti : Set} `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}
  (p1 p2 : ptr Ti) : Decision (p1 = p2).
Proof. solve_decision. Defined.

Section ptr_operations.
  Context `{IntEnv Ti} `{PtrEnv Ti} `{TypeOfIndex Ti M} `{IndexAlive M}.

  Inductive ptr_typed' (m : M) : ptr Ti → type Ti → Prop :=
    | NULL_typed τ : ptr_type_valid get_env τ →  ptr_typed' m (NULL τ) τ
    | Ptr_typed a σ : m ⊢ a : σ → ptr_typed' m (Ptr a) σ.
  Global Instance ptr_typed: Typed M (type Ti) (ptr Ti) := ptr_typed'.

  Global Instance type_of_ptr: TypeOf (type Ti) (ptr Ti) := λ p,
    match p with NULL τ => τ | Ptr a => type_of a end.
  Global Instance ptr_type_check: TypeCheck M (type Ti) (ptr Ti) := λ m p,
    match p with
    | NULL τ => guard (ptr_type_valid get_env τ); Some τ
    | Ptr a => type_check m a
    end.

  Inductive is_NULL : ptr Ti → Prop := mk_is_NULL τ : is_NULL (NULL τ).
  Inductive ptr_frozen : Frozen (ptr Ti) :=
    | NULL_frozen τ : frozen (@NULL Ti τ)
    | Pointer_frozen a : frozen a → frozen (@Ptr Ti a).
  Global Existing Instance ptr_frozen.

  Global Instance ptr_freeze: Freeze (ptr Ti) := λ p,
    match p with NULL τ => NULL τ | Ptr a => Ptr (freeze a) end.

  Definition ptr_cast_ok (σc : type Ti) (p : ptr Ti) : Prop :=
    match p with NULL _ => True | Ptr a => addr_cast_ok σc a end.
  Global Arguments ptr_cast_ok _ !_ /.
  Definition ptr_cast (σc : type Ti) (p : ptr Ti) : ptr Ti :=
    match p with NULL _ => NULL σc | Ptr a => Ptr (addr_cast σc a) end.
  Global Arguments ptr_cast _ !_ /.

  Definition ptr_plus_ok (m : M) (j : Z) (p : ptr Ti) : Prop :=
    match p with NULL _ => j = 0 | Ptr a => addr_plus_ok m j a end.
  Global Arguments ptr_plus_ok _ _ !_ /.
  Definition ptr_plus (j : Z) (p : ptr Ti) : ptr Ti :=
    match p with NULL τ => NULL τ | Ptr a => Ptr (addr_plus j a) end.
  Global Arguments ptr_cast _ !_ /.

  Definition ptr_minus_ok (m : M) (p1 p2 : ptr Ti) : Prop :=
    match p1, p2 with
    | NULL _, NULL _ => True
    | Ptr a1, Ptr a2 => addr_minus_ok m a1 a2
    | _, _ => False
    end.
  Global Arguments ptr_minus_ok _ !_ !_ /.
  Definition ptr_minus (p1 p2 : ptr Ti) : Z :=
    match p1, p2 with
    | NULL _, NULL _ => 0
    | Ptr a1, Ptr a2 => addr_minus a1 a2
    | _, _ => 0
    end.
  Global Arguments ptr_minus !_ !_ /.
End ptr_operations.

Section ptr.
  Context `{MemorySpec Ti M}.
  Implicit Types p : ptr Ti.
  Implicit Types a : addr Ti.
  Implicit Types m : M.
  Implicit Types τ : type Ti.

  Lemma ptr_freeze_frozen p : frozen (freeze p).
  Proof. destruct p; constructor; simpl; auto using addr_freeze_frozen. Qed.
  Lemma ptr_frozen_freeze p : frozen p → freeze p = p.
  Proof.
    destruct 1; simpl; auto. auto using addr_frozen_freeze with f_equal.
  Qed.
  Lemma ptr_freeze_idempotent p : freeze (freeze p) = freeze p.
  Proof. apply ptr_frozen_freeze, ptr_freeze_frozen. Qed.
  Lemma ptr_freeze_idempotent_alt p : freeze p ~{freeze} p.
  Proof. apply ptr_freeze_idempotent. Qed.
  Lemma ptr_frozen_alt p : frozen p ↔ freeze p = p.
  Proof.
    split; intros E; eauto using ptr_frozen_freeze.
    rewrite <-E. eauto using ptr_freeze_frozen.
  Qed.

  Lemma ptr_typed_type_valid m p τ : m ⊢ p : τ → ptr_type_valid get_env τ.
  Proof.
    destruct 1; eauto using TVoid_ptr_valid, addr_typed_ptr_type_valid.
  Qed.

  Global Instance: TypeCheckSpec M (type Ti) (ptr Ti).
  Proof.
    intros m p τ. split.
    * destruct p; intros; simplify_option_equality;
        constructor; auto using type_check_sound.
    * by destruct 1; simplify_option_equality;
        erewrite ?type_check_complete by eauto.
  Qed.
  Global Instance: TypeOfSpec M (type Ti) (ptr Ti).
  Proof. by destruct 1; simpl; erewrite ?type_of_correct by eauto. Qed.
  Lemma ptr_typed_weaken_mem m1 m2 p τ :
    (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
    m1 ⊢ p : τ → m2 ⊢ p : τ.
  Proof. destruct 2; econstructor; eauto using addr_typed_weaken_mem. Qed.

  Lemma ptr_typed_freeze m p τ : m ⊢ freeze p : τ ↔ m ⊢ p : τ.
  Proof.
    split.
    * destruct p; inversion_clear 1; constructor; auto.
      by apply addr_typed_freeze.
    * destruct 1; constructor; auto. by apply addr_typed_freeze.
  Qed.
  Lemma ptr_type_check_freeze m p : type_check m (freeze p) = type_check m p.
  Proof.
    apply option_eq. intros. by rewrite !type_check_correct, ptr_typed_freeze.
  Qed.
  Lemma ptr_freeze_type_of p : type_of (freeze p) = type_of p.
  Proof. by destruct p; simpl; rewrite ?addr_type_of_freeze. Qed.

  Global Instance ptr_frozen_dec p : Decision (ptr_frozen p).
  Proof.
   refine
    match p with NULL _ => left _ | Ptr a => cast_if (decide (frozen a)) end;
    first [by constructor | abstract by inversion 1].
  Defined.
  Global Instance is_NULL_dec p : Decision (is_NULL p).
  Proof.
   refine match p with NULL _ => left _ | _ => right _ end;
     first [by constructor | abstract by inversion 1].
  Defined.

  Lemma ptr_plus_ok_typed m p σ j :
    m ⊢ p : σ → ptr_plus_ok m j p → m ⊢ ptr_plus j p : σ.
  Proof. destruct 1; simpl; constructor; auto using addr_plus_ok_typed. Qed.
  Lemma ptr_minus_ok_typed m p1 p2 σ :
    ⊢ valid m → m ⊢ p1 : σ → m ⊢ p2 : σ → int_typed (ptr_minus p1 p2) sptr.
  Proof.
    destruct 2, 1; simpl; try by apply int_typed_small.
    eauto using addr_minus_ok_typed.
  Qed.
  Lemma ptr_cast_ok_typed m p σ σc :
    m ⊢ p : σ → ptr_cast_ok σc p →
    ptr_type_valid get_env σc → m ⊢ ptr_cast σc p : σc.
  Proof. destruct 1; simpl; constructor; eauto using addr_cast_ok_typed. Qed.
End ptr.

Notation ptr_bit Ti := (frag (ptr Ti)).

Section ptr_bit_ops.
  Context `{PtrEnv Ti} `{IntEnv Ti} `{TypeOfIndex Ti M}.

  Global Instance ptr_bit_valid: Valid M (ptr_bit Ti) := λ m ps, ∃ τ,
    m ⊢ frag_item ps : τ ∧
    frozen (frag_item ps) ∧
    frag_index ps < bit_size_of (τ.*).

  Definition ptr_to_bits (p : ptr Ti) : list (ptr_bit Ti) :=
    to_frags (bit_size_of (type_of p.*)) (freeze p).
  Definition ptr_of_bits (τ : type Ti)
      (pps : list (ptr_bit Ti)) : option (ptr Ti) :=
    p ← of_frags (bit_size_of (τ.*)) pps;
    guard (type_of p = τ);
    Some p.
End ptr_bit_ops.

Section ptr_bits.
  Context `{MemorySpec Ti M}.
  Implicit Types m : M.
  Implicit Types τ : type Ti.
  Implicit Types p : ptr Ti.
  Implicit Types ps : ptr_bit Ti.

  Global Instance ptr_bit_valid_dec m ps : Decision (m ⊢ valid ps).
  Proof.
   refine
    match Some_dec (type_check m (frag_item ps)) with
    | inleft (τ↾Hτ) => cast_if_and (decide (frozen (frag_item ps)))
       (decide (frag_index ps < bit_size_of (τ.*)))
    | inright Hτ => right _
    end; abstract first
    [ simplify_type_equality; econstructor; eauto
    | by destruct 1 as (?&?&?&?); simplify_type_equality ].
  Defined.
  Lemma ptr_bit_valid_weaken_mem m1 m2 ps :
    (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
    m1 ⊢ valid ps → m2 ⊢ valid ps.
  Proof. intros ? (τ&?&?&?); exists τ; eauto using ptr_typed_weaken_mem. Qed.

  Lemma ptr_to_bits_freeze p : ptr_to_bits (freeze p) = ptr_to_bits p.
  Proof.
    unfold ptr_to_bits. by rewrite ptr_freeze_type_of, ptr_freeze_idempotent.
  Qed.
  Lemma ptr_to_bits_length_alt p :
    length (ptr_to_bits p) = bit_size_of (type_of p.* ).
  Proof. unfold ptr_to_bits. by rewrite (to_frags_length _). Qed.
  Lemma ptr_to_bits_length m p τ :
    m ⊢ p : τ → length (ptr_to_bits p) = bit_size_of (τ.* ).
  Proof. intros. erewrite ptr_to_bits_length_alt, type_of_correct; eauto. Qed.

  Lemma ptr_to_bits_valid m p τ : m ⊢ p : τ → m ⊢* valid (ptr_to_bits p).
  Proof.
    intros. apply (Forall_to_frags _).
    intros i. erewrite type_of_correct by eauto. exists τ; simpl.
    rewrite ptr_typed_freeze. eauto using ptr_freeze_frozen.
  Qed.
  Lemma ptr_of_bits_typed_frozen m p τ pss :
    ptr_of_bits τ pss = Some p → m ⊢* valid pss → m ⊢ p : τ ∧ frozen p.
  Proof.
    unfold ptr_of_bits. intros.
    destruct (of_frags _ _) eqn:?; simplify_option_equality.
    destruct (Forall_of_frags (bit_size_of (type_of p.* ))
      (λ q, m ⊢ valid q) p pss 0) as (?&?&?&?); eauto using type_of_typed.
    by apply Nat.neq_0_lt_0, bit_size_of_base_ne_0.
  Qed.
  Lemma ptr_of_bits_typed m p τ pss :
    ptr_of_bits τ pss = Some p → m ⊢* valid pss → m ⊢ p : τ.
  Proof. intros. eapply ptr_of_bits_typed_frozen; eauto. Qed.
  Lemma ptr_of_bits_frozen m p τ pss :
    ptr_of_bits τ pss = Some p → m ⊢* valid pss → frozen p.
  Proof. intros. eapply ptr_of_bits_typed_frozen; eauto. Qed.

  Lemma ptr_of_bits_type_of p τ pss :
    ptr_of_bits τ pss = Some p → τ = type_of p.
  Proof. unfold ptr_of_bits. intros. by simplify_option_equality. Qed.
  Lemma ptr_to_of_bits_alt p τ pss :
    ptr_of_bits τ pss = Some (freeze p) → ptr_to_bits p = pss.
  Proof.
    intros. unfold ptr_of_bits, ptr_to_bits in *. simplify_option_equality.
    by rewrite <-(ptr_freeze_type_of p), (of_to_frags_1 _ _ pss).
  Qed.
  Lemma ptr_to_of_bits m p τ pss :
    ptr_of_bits τ pss = Some p → m ⊢* valid pss → ptr_to_bits p = pss.
  Proof.
    intros. apply ptr_to_of_bits_alt with τ.
    by rewrite ptr_frozen_freeze by eauto using ptr_of_bits_frozen.
  Qed.
  Lemma ptr_of_to_bits_alt p :
    ptr_of_bits (type_of p) (ptr_to_bits p) = Some (freeze p).
  Proof.
    unfold ptr_of_bits, ptr_to_bits. rewrite (of_to_frags_2 _).
    simpl. rewrite ptr_freeze_type_of. by simplify_option_equality.
  Qed.
  Lemma ptr_of_to_bits m p τ :
    m ⊢ p : τ → ptr_of_bits τ (ptr_to_bits p) = Some (freeze p).
  Proof. intros. erewrite <-ptr_of_to_bits_alt, type_of_correct; eauto. Qed.
End ptr_bits.
