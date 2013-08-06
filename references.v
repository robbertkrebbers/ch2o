(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export abstract_integers types.
Local Open Scope ctype_scope.

(** * Pointers environments *)
Section env.
Local Unset Elimination Schemes.

Class PtrEnv (Ti : Set) := {
  get_env : env Ti;
  size_of : type Ti → nat;
  field_sizes : list (type Ti) → list nat
}.

Class EnvSpec (Ti : Set) `{IntEnv Ti} `{PtrEnv Ti} := {
  int_env_spec :>> IntEnvSpec Ti;
  get_env_valid :> EnvValid get_env;
  size_of_ptr_ne_0 τ : size_of (τ.*) ≠ 0;
  size_of_int τ : size_of (intt τ) = int_size τ;
  size_of_void : size_of void = 1;
  size_of_array τ n : size_of (τ.[n]) = n * size_of τ;
  size_of_struct s τs :
    get_env !! s = Some τs → size_of (struct s) = sum_list (field_sizes τs);
  size_of_fields τs :
    Forall2 (λ τ sz, size_of τ ≤ sz) τs (field_sizes τs);
  size_of_union s τs :
    get_env !! s = Some τs → Forall (λ τ, size_of τ ≤ size_of (union s)) τs
}.
End env.

Section env_spec.
  Context `{EnvSpec Ti}.

  Definition field_offset (τs : list (type Ti)) (i : nat) : nat :=
    sum_list $ take i $ field_sizes τs.
  Definition bit_size_of (τ : type Ti) : nat := size_of τ * char_bits.
  Definition field_bit_sizes (τs : list (type Ti)) : list nat :=
    fmap (λ sz, sz * char_bits) (field_sizes τs).
  Definition field_bit_offset (τs : list (type Ti)) (i : nat) : nat :=
    sum_list $ take i $ field_bit_sizes τs.

  Lemma field_sizes_same_length τs : τs `same_length` field_sizes τs.
  Proof. eauto using Forall2_same_length, size_of_fields. Qed.
  Lemma field_sizes_length τs : length (field_sizes τs) = length τs.
  Proof. symmetry. by apply same_length_length, field_sizes_same_length. Qed.
  Lemma size_of_union_lookup s τs i τ :
    get_env !! s = Some τs → τs !! i = Some τ → size_of τ ≤ size_of (union s).
  Proof.
    intros. assert (Forall (λ τ, size_of τ ≤ size_of (union s)) τs) as Hτs
      by eauto using size_of_union; rewrite Forall_lookup in Hτs. eauto.
  Qed.
  Lemma size_of_struct_lookup s τs i τ :
    get_env !! s = Some τs → τs !! i = Some τ → size_of τ ≤ size_of (struct s).
  Proof.
    intros Hs Hτs. erewrite size_of_struct by eauto. clear Hs. revert i Hτs.
    induction (size_of_fields τs) as [|σ sz σs szs]; intros [|?] ?;
      simplify_equality'; auto with lia.
    transitivity (sum_list szs); eauto with lia.
  Qed.
  Lemma size_of_union_singleton s τ :
    get_env !! s = Some [τ] → size_of τ ≤ size_of (union s).
  Proof. intros. by apply (size_of_union_lookup s [τ] 0). Qed.

  Lemma bit_size_of_int τ : bit_size_of (intt τ) = int_bits τ.
  Proof. unfold bit_size_of. by rewrite size_of_int. Qed.
  Lemma bit_size_of_int_same_kind τ1 τ2 :
    IRank τ1 = IRank τ2 → bit_size_of (intt τ1) = bit_size_of (intt τ2).
  Proof.
    destruct τ1, τ2; intros; simplify_equality'. by rewrite !bit_size_of_int.
  Qed.
  Lemma bit_size_of_void : bit_size_of void = char_bits.
  Proof. unfold bit_size_of. by rewrite size_of_void, Nat.mul_1_l. Qed.
  Lemma bit_size_of_array τ n : bit_size_of (τ.[n]) = n * bit_size_of τ.
  Proof. unfold bit_size_of. by rewrite !size_of_array, Nat.mul_assoc. Qed.
  Lemma bit_size_of_struct s τs :
    get_env !! s = Some τs →
    bit_size_of (struct s) = sum_list (field_bit_sizes τs).
  Proof.
    unfold bit_size_of, field_bit_sizes. intros.
    erewrite size_of_struct by eauto.
    elim (field_sizes τs); simpl; auto with lia.
  Qed.
  Lemma bit_size_of_fields τs :
    Forall2 (λ τ sz, bit_size_of τ ≤ sz) τs (field_bit_sizes τs).
  Proof.
    unfold bit_size_of, field_bit_sizes. induction (size_of_fields τs);
      simpl; constructor; auto using Nat.mul_le_mono_nonneg_r with lia.
  Qed.
  Lemma bit_size_of_union s τs :
    get_env !! s = Some τs →
    Forall (λ τ, bit_size_of τ ≤ bit_size_of (union s)) τs.
  Proof.
    intros Hτs. apply size_of_union in Hτs. unfold bit_size_of.
    induction Hτs; constructor; auto using Nat.mul_le_mono_nonneg_r with lia.
  Qed.

  Lemma field_bit_sizes_same_length τs : τs `same_length` field_bit_sizes τs.
  Proof. eauto using Forall2_same_length, bit_size_of_fields. Qed.
  Lemma field_bit_sizes_length τs : length (field_bit_sizes τs) = length τs.
  Proof. symmetry. by apply same_length_length, field_bit_sizes_same_length. Qed.
  Lemma bit_size_of_union_lookup s τs i τ :
    get_env !! s = Some τs → τs !! i = Some τ →
    bit_size_of τ ≤ bit_size_of (union s).
  Proof.
    intros. unfold bit_size_of. apply Nat.mul_le_mono_nonneg_r;
      eauto using size_of_union_lookup with lia.
  Qed.
  Lemma bit_size_of_union_singleton s τ :
    get_env !! s = Some [τ] → bit_size_of τ ≤ bit_size_of (union s).
  Proof. intros. by apply (bit_size_of_union_lookup s [τ] 0). Qed.
  Lemma field_bit_offset_alt τs i :
    field_bit_offset τs i = field_offset τs i * char_bits.
  Proof.
    unfold field_bit_offset, field_offset, field_bit_sizes.
    revert i. induction (field_sizes τs) as [|?? IH]; intros [|i]; simpl; auto with lia.
    by rewrite IH, Nat.mul_add_distr_r.
  Qed.

  Lemma size_of_base_ne_0 τ : size_of (base τ) ≠ 0.
  Proof.
    destruct τ.
    * rewrite size_of_int. apply int_size_ne_0.
    * apply size_of_ptr_ne_0.
  Qed.
  Lemma bit_size_of_base_ne_0 τ : bit_size_of (base τ) ≠ 0.
  Proof.
    apply Nat.neq_mul_0. auto using char_bits_ne_0, size_of_base_ne_0.
  Qed.
  Global Instance: ∀ τ, PropHolds (size_of (base τ) ≠ 0).
  Proof. apply size_of_base_ne_0. Qed.
  Global Instance: ∀ τ, PropHolds (bit_size_of (base τ) ≠ 0).
  Proof. apply bit_size_of_base_ne_0. Qed.

  Lemma size_of_ne_0 τ : type_valid get_env τ → size_of τ ≠ 0.
  Proof.
    revert τ. refine (type_env_ind _ _ _ _).
    * auto using size_of_base_ne_0.
    * intros. rewrite size_of_array. by apply Nat.neq_mul_0.
    * intros [] s τs Hs Hτs Hsz Hlen.
      + erewrite size_of_struct by eauto. clear Hs.
        induction (size_of_fields τs); simpl; decompose_Forall; auto with lia.
      + apply size_of_union in Hs.
        destruct Hs; decompose_Forall; auto with lia.
  Qed.
  Lemma size_of_pos τ : type_valid get_env τ → 0 < size_of τ.
  Proof. intros. by apply Nat.neq_0_lt_0, size_of_ne_0. Qed.
  Lemma bit_size_of_ne_0 τ : type_valid get_env τ → bit_size_of τ ≠ 0.
  Proof.
    intros. apply Nat.neq_mul_0. auto using char_bits_ne_0, size_of_ne_0.
  Qed.
  Lemma bit_size_of_pos τ : type_valid get_env τ → 0 < bit_size_of τ.
  Proof. intros. by apply Nat.neq_0_lt_0, bit_size_of_ne_0. Qed.
End env_spec.

Notation size_of' v := (size_of (type_of v)).
Notation bit_size_of' v := (bit_size_of (type_of v)).

(** * References *)
Inductive ref_seg :=
  | RArray : nat → nat → ref_seg
  | RStruct : nat → tag → ref_seg
  | RUnion : nat → tag → bool → ref_seg.
Notation ref := (list ref_seg).

Instance ref_seg_eq_dec (r1 r2 : ref_seg) : Decision (r1 = r2).
Proof.
 refine
  match r1, r2 with
  | RArray i1 n1, RArray i2 n2 =>
     cast_if_and (decide (i1 = i2)) (decide (n1 = n2))
  | RStruct i1 s1, RStruct i2 s2 =>
     cast_if_and (decide (i1 = i2)) (decide (s1 = s2))
  | RUnion i1 s1 q1, RUnion i2 s2 q2 =>
     cast_if_and3 (decide (i1 = i2)) (decide (s1 = s2)) (decide (q1 = q2))
  | _, _ => right _
  end; abstract congruence.
Defined.

Inductive ref_seg_typed `{PtrEnv Ti} : PathTyped (type Ti) ref_seg :=
  | RArray_typed τ i n : i < n → RArray i n @ τ.[n] ↣ τ
  | RStruct_typed s i τs τ :
     get_env !! s = Some τs → τs !! i = Some τ → RStruct i s @ struct s ↣ τ
  | RUnion_typed s i q τs τ :
     get_env !! s = Some τs → τs !! i = Some τ → RUnion i s q @ union s ↣ τ.
Existing Instance ref_seg_typed.
Inductive ref_typed `{PtrEnv Ti} : PathTyped (type Ti) ref :=
  | ref_nil_2 τ : [] @ τ ↣ τ
  | ref_typed_cons_2 (r : ref) (rs : ref_seg) τ1 τ2 τ3 :
     rs @ τ2 ↣ τ3 → r @ τ1 ↣ τ2 → rs :: r @ τ1 ↣ τ3.
Existing Instance ref_typed.
Instance subtype `{PtrEnv Ti} : SubsetEq (type Ti) :=
  λ τ1 τ2, ∃ r : ref, r @ τ2 ↣ τ1.

Instance ref_seg_lookup `{PtrEnv Ti} :
    Lookup ref_seg (type Ti) (type Ti) := λ rs τ,
  match rs, τ with
  | RArray i n', τ.[n] => guard (n = n'); guard (i < n); Some τ
  | RStruct i s', struct s => guard (s = s'); get_env !! s ≫= (!! i)
  | RUnion i s' _, union s => guard (s = s'); get_env !! s ≫= (!! i)
  | _, _ => None
  end.
Instance ref_lookup `{PtrEnv Ti} : Lookup ref (type Ti) (type Ti) :=
  fix go r τ :=
  match r with
  | [] => Some τ
  | rs :: r => @lookup _ _ _ go r τ ≫= ref_seg_lookup rs
  end.

Class Frozen A := frozen: A → Prop.
Class Freeze A := freeze: A → A.
Arguments freeze {_ _} !_ / : simpl nomatch.
Class Unfreeze A := unfreeze: A → A.
Arguments unfreeze {_ _} !_ / : simpl nomatch.

Inductive ref_seg_frozen: Frozen ref_seg :=
  | RArray_frozen i n : frozen (RArray i n)
  | RStruct_frozen i s : frozen (RStruct i s)
  | RUnion_frozen i s : frozen (RUnion i s false).
Existing Instance ref_seg_frozen.

Instance ref_seg_freeze: Freeze ref_seg := λ rs,
  match rs with
  | RArray i n => RArray i n
  | RStruct i s => RStruct i s
  | RUnion i s _ => RUnion i s false
  end.
Instance ref_seg_unfreeze: Unfreeze ref_seg := λ rs,
  match rs with
  | RArray i n => RArray i n
  | RStruct i s => RStruct i s
  | RUnion i s _ => RUnion i s true
  end.

Definition ref_seg_set_offset (i : nat) (rs : ref_seg) : ref_seg :=
  match rs with RArray _ n => RArray i n | _ => rs end.
Arguments ref_seg_set_offset _ !_ : simpl nomatch.
Definition ref_set_offset (i : nat) (r : ref) : ref :=
  match r with rs :: r => ref_seg_set_offset i rs :: r | _ => r end.
Arguments ref_set_offset _ !_ : simpl nomatch.
Notation ref_base := (ref_set_offset 0).
Definition ref_offset (r : ref) : nat :=
  match r with RArray i _ :: r => i | _ => 0 end.
Arguments ref_offset !_ : simpl nomatch.
Definition ref_size (r : ref) : nat :=
  match r with RArray _ n :: _ => n | _ => 1 end.
Arguments ref_size !_ : simpl nomatch.

(*
Definition ref_seg_byte_offset `{PtrEnv Ti} (τ : type Ti) (rs : ref_seg) :
    option (type Ti * nat) :=
  match rs, τ with
  | RArray i _, τ.[_] =>
     Some (τ, i * size_of τ)
  | RStruct i, struct s =>
     τs ← get_env !! s;
     τ ← τs !! i;
     Some (τ, struct_offset τs i)
  | RUnion i _, union s =>
     τs ← get_env !! s;
     τ ← τs !! i;
     Some (τ, 0)
  | _, _ => None
  end.
Fixpoint ref_byte_offset `{PtrEnv Ti} (τ : type Ti) (r : ref) :
    option (type Ti * nat) :=
  match r with
  | [] => Some (τ, 0)
  | rs :: r =>
     σi ← ref_byte_offset τ r;
     ρj ← ref_seg_byte_offset (fst σi) rs;
     Some (fst ρj, snd σi + snd ρj)
  end.
*)
Inductive ref_seg_disjoint: Disjoint ref_seg :=
  | RArray_disjoint i1 i2 n : i1 ≠ i2 → RArray i1 n ⊥ RArray i2 n
  | RStruct_disjoint i1 i2 s : i1 ≠ i2 → RStruct i1 s ⊥ RStruct i2 s.
Existing Instance ref_seg_disjoint.
Inductive ref_disjoint: Disjoint ref :=
  | ref_disjoint_here rs1 rs2 r1 r2 :
     rs1 ⊥ rs2 → r1 ~{fmap freeze} r2 → rs1 :: r1 ⊥ rs2 :: r2
  | ref_disjoint_cons_l rs1 r1 r2 : r1 ⊥ r2 → rs1 :: r1 ⊥ r2
  | ref_disjoint_cons_r rs2 r1 r2 : r1 ⊥ r2 → r1 ⊥ rs2 :: r2.
Existing Instance ref_disjoint.

Section refs.
Context `{EnvSpec Ti}.
Implicit Types τ : type Ti.
Implicit Types rs : ref_seg.
Implicit Types r : ref.

Lemma ref_typed_nil τ1 τ2 : [] @ τ1 ↣ τ2 ↔ τ1 = τ2.
Proof.
  split. by inversion 1; simplify_list_equality. intros. subst. constructor.
Qed.
Lemma ref_typed_cons rs r τ1 τ3 :
  rs :: r @ τ1 ↣ τ3 ↔ ∃ τ2, r @ τ1 ↣ τ2 ∧ rs @ τ2 ↣ τ3.
Proof.
  split. inversion 1; subst; eauto. intros (?&?&?). econstructor; eauto.
Qed.
Lemma ref_typed_app r1 r2 τ1 τ3 :
  r1 ++ r2 @ τ1 ↣ τ3 ↔ ∃ τ2, r2 @ τ1 ↣ τ2 ∧ r1 @ τ2 ↣ τ3.
Proof.
  revert τ1 τ3. induction r1; simpl; intros.
  * setoid_rewrite ref_typed_nil. naive_solver.
  * setoid_rewrite ref_typed_cons. naive_solver.
Qed.
Lemma ref_typed_singleton rs τ1 τ2 : [rs] @ τ1 ↣ τ2 ↔ rs @ τ1 ↣ τ2.
Proof.
  rewrite ref_typed_cons. setoid_rewrite ref_typed_nil. naive_solver.
Qed.
Lemma ref_typed_snoc r rs τ1 τ3 :
  r ++ [rs] @ τ1 ↣ τ3 ↔ ∃ τ2, rs @ τ1 ↣ τ2 ∧ r @ τ2 ↣ τ3.
Proof.
  setoid_rewrite ref_typed_app. by setoid_rewrite ref_typed_singleton.
Qed.
Lemma ref_typed_snoc_2 r rs τ1 τ2 τ3 :
  rs @ τ1 ↣ τ2 ∧ r @ τ2 ↣ τ3 → r ++ [rs] @ τ1 ↣ τ3.
Proof. rewrite ref_typed_snoc. eauto. Qed.

Lemma ref_seg_typed_type_valid rs τ σ :
  rs @ τ ↣ σ → type_valid get_env τ → type_valid get_env σ.
Proof.
  destruct 1; inversion 1; subst; eauto using env_valid_lookup_lookup.
Qed.
Lemma ref_typed_type_valid r τ σ :
  r @ τ ↣ σ → type_valid get_env τ → type_valid get_env σ.
Proof. induction 1; eauto using ref_seg_typed_type_valid. Qed.

Lemma ref_lookup_nil τ : τ !! [] = Some τ.
Proof. done. Qed.
Lemma ref_lookup_cons rs r τ : τ !! (rs :: r) = (τ !! r) ≫= (!! rs).
Proof. done. Qed.
Lemma ref_lookup_app r1 r2 τ : τ !! (r1 ++ r2) = (τ !! r2) ≫= (!! r1).
Proof.
  induction r1 as [|rs1 r1 IH]; simpl.
  * by destruct (τ !! r2).
  * rewrite ref_lookup_cons. by rewrite IH, option_bind_assoc.
Qed.
Lemma ref_lookup_snoc r rs τ : τ !! (r ++ [rs]) = (τ !! rs) ≫= (!! r).
Proof. apply ref_lookup_app. Qed.

Lemma ref_seg_typed_valid τ rs σ :
  type_valid get_env τ → rs @ τ ↣ σ → type_valid get_env σ.
Proof.
  intros Hτ.
  destruct 1; inversion_clear Hτ; eauto using env_valid_lookup_lookup.
Qed.
Lemma ref_valid_typed_valid τ r σ :
  type_valid get_env τ → r @ τ ↣ σ → type_valid get_env σ.
Proof. induction 2; eauto using ref_seg_typed_valid. Qed.

Global Instance: PathTypeCheckSpec (type Ti) ref_seg.
Proof.
  intros rs τ σ. split.
  * destruct rs, τ as [| | |[]]; intros;
      simplify_option_equality; econstructor; eauto.
  * by destruct 1; simplify_option_equality.
Qed.
Global Instance: PathTypeCheckSpec (type Ti) ref.
Proof.
  intros r τ σ. split.
  * revert σ. induction r; intros σ.
    + intros. simplify_equality. constructor.
    + rewrite ref_lookup_cons. intros. simplify_option_equality.
      econstructor; eauto. by apply path_type_check_correct.
  * induction 1 as [|????? Hrs]; [done |]. rewrite ref_lookup_cons.
    simplify_option_equality. by apply path_type_check_complete.
Qed.

Lemma ref_seg_typed_inv_void rs σ : ¬rs @ void ↣ σ.
Proof. inversion 1. Qed.
Lemma ref_typed_inv_void r σ : r @ void ↣ σ → σ = void ∧ r = [].
Proof.
  destruct r as [|rs r] using rev_ind.
  * rewrite ref_typed_nil. by intros; subst.
  * rewrite ref_typed_snoc. intros (?&Hrs&_).
    edestruct ref_seg_typed_inv_void; eauto.
Qed.
Lemma ref_seg_typed_inv_base (τ : base_type Ti) rs σ : ¬rs @ base τ ↣ σ.
Proof. inversion 1. Qed.
Lemma ref_typed_inv_base (τ : base_type Ti) r σ :
  r @ base τ ↣ σ → σ = base τ ∧ r = [].
Proof.
  destruct r as [|rs r] using rev_ind.
  * rewrite ref_typed_nil. by intros; subst.
  * rewrite ref_typed_snoc. intros (?&Hrs&_).
    edestruct ref_seg_typed_inv_base; eauto.
Qed.

Global Instance: PreOrder (@subseteq (type Ti) _).
Proof.
  repeat split.
  * eexists []. constructor.
  * intros τ1 τ2 τ3 (r1&?) (r2&?). exists (r1 ++ r2).
    apply ref_typed_app; eauto.
Qed.

Global Instance:
  Proper ((~{freeze}) ==> (~{fmap freeze}) ==> (~{fmap freeze}))
  (@cons ref_seg).
Proof. repeat intro. unfold proj_eq in *; simpl; congruence. Qed.
Global Instance:
  Proper ((~{fmap freeze}) ==> (~{fmap freeze}) ==> (~{fmap freeze}))
  (@app ref_seg).
Proof.
  repeat intro. unfold proj_eq in *; by rewrite !fmap_app; f_equal.
Qed.

Lemma ref_seg_freeze_frozen rs : frozen (freeze rs).
Proof. destruct rs; constructor. Qed.
Lemma ref_freeze_frozen r : Forall frozen (freeze <$> r).
Proof. apply Forall_fmap, Forall_true, ref_seg_freeze_frozen. Qed.

Lemma ref_seg_frozen_freeze rs : frozen rs → freeze rs = rs.
Proof. by destruct 1. Qed.
Lemma ref_frozen_freeze r : Forall frozen r → freeze <$> r = r.
Proof. induction 1; simpl; f_equal; auto using ref_seg_frozen_freeze. Qed.

Lemma ref_seg_freeze_idempotent rs : freeze (freeze rs) = freeze rs.
Proof. apply ref_seg_frozen_freeze, ref_seg_freeze_frozen. Qed.
Lemma ref_seg_freeze_idempotent_alt rs : freeze rs ~{freeze} rs.
Proof. apply ref_seg_freeze_idempotent. Qed.
Lemma ref_freeze_idempotent r : freeze <$> freeze <$> r = freeze <$> r.
Proof. apply ref_frozen_freeze, ref_freeze_frozen. Qed.
Lemma ref_freeze_idempotent_alt r : freeze <$> r ~{fmap freeze} r.
Proof. apply ref_freeze_idempotent. Qed.

Global Instance: Proper ((~{freeze}) ==> (=)) (@freeze ref_seg _).
Proof. by intros ???. Qed.
Global Instance: Proper ((~{fmap freeze}) ==> (=)) (fmap freeze : ref → ref).
Proof. by intros ???. Qed.

Lemma ref_seg_unfreeze_freeze rs : unfreeze (freeze rs) = unfreeze rs.
Proof. by destruct rs. Qed.
Lemma ref_seg_freeze_unfreeze rs : freeze (unfreeze rs) = freeze rs.
Proof. by destruct rs. Qed.
Lemma ref_unfreeze_freeze r : unfreeze <$> freeze <$> r = unfreeze <$> r.
Proof. induction r; simpl; f_equal; auto using ref_seg_unfreeze_freeze. Qed.
Lemma ref_freeze_unfreeze r : freeze <$> unfreeze <$> r = freeze <$> r.
Proof. induction r; simpl; f_equal; auto using ref_seg_freeze_unfreeze. Qed.

Lemma ref_seg_typed_freeze τ rs σ : freeze rs @ τ ↣ σ ↔ rs @ τ ↣ σ.
Proof.
  split.
  * destruct rs; inversion_clear 1; econstructor; eauto.
  * destruct 1; econstructor; eauto.
Qed.
Global Instance:
  Proper ((=) ==> (~{freeze}) ==> (=) ==> iff) (@path_typed _ ref_seg _).
Proof.
  intros ?? <- ?? E ?? <-.
  by rewrite <-ref_seg_typed_freeze, E, ref_seg_typed_freeze.
Qed.
Lemma ref_typed_freeze τ r σ : freeze <$> r @ τ ↣ σ ↔ r @ τ ↣ σ.
Proof.
  revert τ σ. induction r as [|rs r IH]; intros τ σ; simpl.
  * by rewrite ref_typed_nil.
  * rewrite !ref_typed_cons.
    setoid_rewrite ref_seg_typed_freeze. by setoid_rewrite IH.
Qed.
Global Instance:
  Proper ((=) ==> (~{fmap freeze}) ==> (=) ==> iff) (@path_typed _ ref _).
Proof.
  intros ?? <- ?? E ?? <-.
  by rewrite <-ref_typed_freeze, E, ref_typed_freeze.
Qed.

Lemma ref_seg_lookup_freeze τ rs : τ !! freeze rs = τ !! rs.
Proof.
  apply option_eq. intros.
  by rewrite !path_type_check_correct, ref_seg_typed_freeze.
Qed.
Global Instance:
  Proper ((~{freeze}) ==> (=) ==> (=)) (@lookup ref_seg _ _ _).
Proof.
  intros ?? E ?? <-.
  by rewrite <-ref_seg_lookup_freeze, E, ref_seg_lookup_freeze.
Qed.
Lemma ref_lookup_freeze τ r : τ !! (freeze <$> r) = τ !! r.
Proof.
  apply option_eq. intros. by rewrite !path_type_check_correct, ref_typed_freeze.
Qed.
Global Instance:
  Proper ((~{fmap freeze}) ==> (=) ==> (=)) (@lookup ref _ _ _).
Proof.
  intros ?? E ?? <-.
  by rewrite <-ref_lookup_freeze, E, ref_lookup_freeze.
Qed.

Global Instance: Symmetric (@disjoint ref_seg _).
Proof. destruct 1; constructor; auto. Qed.
Global Instance: Symmetric (@disjoint ref _).
Proof. intros ??. induction 1; constructor (by auto). Qed.

Global Instance:
  Proper ((~{freeze}) ==> (~{freeze}) ==> iff) (@disjoint ref_seg _).
Proof.
  assert (∀ rs1 rs2, freeze rs1 ⊥ rs2 ↔ rs1 ⊥ rs2) as help.
  { split.
    * by destruct rs1; inversion_clear 1; constructor.
    * by destruct 1; constructor. }
  intros rs1 rs2 Hr12 rs3 rs4 Hr34. rewrite <-(help rs1), Hr12, help.
  by rewrite (symmetry_iff (⊥) rs2), <-(help rs3), Hr34, help.
Qed.
Global Instance:
  Proper ((~{fmap freeze}) ==> (~{fmap freeze}) ==> iff) (@disjoint ref _).
Proof.
  assert (∀ r1 r2, freeze <$> r1 ⊥ r2 ↔ r1 ⊥ r2) as help.
  { split.
    * intros Hr. remember (freeze <$> r1) as r1' eqn:Hr1'. revert r1 Hr1'.
      induction Hr; intros [|??] ?;
        simplify_equality; try constructor (by eauto).
      rewrite ref_seg_freeze_idempotent_alt, ref_freeze_idempotent_alt in *.
      by constructor.
    * induction 1; try constructor (by auto). constructor.
      + by rewrite ref_seg_freeze_idempotent_alt.
      + by rewrite ref_freeze_idempotent_alt. }
  intros r1 r2 Hr12 r3 r4 Hr34. rewrite <-(help r1), Hr12, help.
  by rewrite (symmetry_iff (⊥) r2), <-(help r3), Hr34, help.
Qed.

Lemma ref_disjoint_app_l r1 r1' r2' : r1' ⊥ r2' → r1 ++ r1' ⊥ r2'.
Proof. induction r1; simpl; auto using ref_disjoint_cons_l. Qed.
Lemma ref_disjoint_app_r r2 r1' r2' : r1' ⊥ r2' → r1' ⊥ r2 ++ r2'.
Proof. induction r2; simpl; auto using ref_disjoint_cons_r. Qed.
Lemma ref_disjoint_app r1 r2 r1' r2' : r1' ⊥ r2' → r1 ++ r1' ⊥ r2 ++ r2'.
Proof. auto using ref_disjoint_app_l, ref_disjoint_app_r. Qed.

Lemma ref_disjoint_here_app r1 r2 r1' r2' :
  r1 ⊥ r2 → r1' ~{fmap freeze} r2' → r1 ++ r1' ⊥ r2 ++ r2'.
Proof.
  intros Hr Hr'. induction Hr; simpl.
  * apply ref_disjoint_here; auto. by f_equiv.
  * by apply ref_disjoint_cons_l.
  * by apply ref_disjoint_cons_r.
Qed.
Lemma ref_disjoint_alt r1 r2 :
  r1 ⊥ r2 ↔ ∃ r1' rs1 r1'' r2' rs2 r2'',
    r1 = r1' ++ [rs1] ++ r1'' ∧ r2 = r2' ++ [rs2] ++ r2'' ∧
    rs1 ⊥ rs2 ∧ r1'' ~{fmap freeze} r2''.
Proof.
  split.
  * induction 1 as [rs1 rs2 r1 r2|
      rs1 r1 r2 ? (r1'&rs1'&r1''&r2'&rs2'&r2''&?&?&?&?)|
      rs2 r1 r2 ? (r1'&rs1'&r1''&r2'&rs2'&r2''&?&?&?&?)]; subst.
    + by eexists [], rs1, r1, [], rs2, r2.
    + by eexists (rs1 :: r1'), rs1', r1'', r2', rs2', r2''.
    + by eexists r1', rs1', r1'', (rs2 :: r2'), rs2', r2''.
  * intros (r1'&rs1'&r1''&r2'&rs2'&r2''&?&?&?&?); subst.
    apply ref_disjoint_app. by constructor.
Qed.

Lemma ref_disjoint_snoc r1 r2 rs1 rs2 :
  r1 ++ [rs1] ⊥ r2 ++ [rs2] ↔ rs1 ⊥ rs2 ∨ (r1 ⊥ r2 ∧ rs1 ~{freeze} rs2).
Proof.
  split.
  * rewrite ref_disjoint_alt.
    intros (r1'&rs1'&r1''&r2'&rs2'&r2''&Hr1&Hr2&?&Hr'').
    destruct r1'' as [|rs1'' r1'' _] using @rev_ind;
      destruct r2'' as [|rs2'' r2'' _] using @rev_ind.
    + simplify_list_equality. by left.
    + unfold proj_eq in Hr''. rewrite fmap_app in Hr''.
      by simplify_list_equality.
    + unfold proj_eq in Hr''. rewrite fmap_app in Hr''.
      by simplify_list_equality.
    + rewrite !(associative_L (++)) in Hr1, Hr2. unfold proj_eq in Hr''.
      rewrite !fmap_app in Hr''; simplify_list_equality.
      right. split; auto. rewrite <-!(associative_L (++)).
      apply ref_disjoint_app. by constructor.
  * intros [?|[? Hr]].
    + rewrite ref_disjoint_alt. naive_solver.
    + rewrite Hr. by apply ref_disjoint_here_app.
Qed.
Lemma ref_disjoint_singleton rs1 rs2 : [rs1] ⊥ [rs2] ↔ rs1 ⊥ rs2.
Proof.
  rewrite ref_disjoint_alt. split.
  * by intros ([]&?&?&[]&?&?&?&?&?&?); simplify_list_equality.
  * intros. eexists [], rs1, []. by eexists [], rs2, [].
Qed.

Global Instance ref_seg_frozen_dec rs : Decision (ref_seg_frozen rs).
Proof.
 refine match rs with RUnion _ _ true => right _ | _ => left _ end;
  abstract first [constructor | inversion 1].
Defined.
Global Instance ref_seg_disjoint_dec rs1 rs2 :
  Decision (ref_seg_disjoint rs1 rs2).
Proof.
 refine
  match rs1, rs2 with
  | RArray i n1, RArray j n2 =>
     if decide (n1 = n2) then cast_if_not (decide (i = j)) else right _
  | RStruct i s1, RStruct j s2 =>
     if decide (s1 = s2) then cast_if_not (decide (i = j)) else right _
  | _, _ => right _
  end; abstract first [by subst; constructor | by inversion 1].
Defined.

Inductive ref_disjoint_rev: ref → ref → Prop :=
  | ref_disjoint_rev_here rs1 rs2 r1' r2' :
     rs1 ⊥ rs2 → ref_disjoint_rev (rs1 :: r1') (rs2 :: r2')
  | ref_disjoint_rev_cons rs1 rs2 r1 r2 :
     rs1 ~{freeze} rs2 →
     ref_disjoint_rev r1 r2 → ref_disjoint_rev (rs1 :: r1) (rs2 :: r2).
Global Instance ref_disjoint_rev_dec: ∀ r1 r2,
  Decision (ref_disjoint_rev r1 r2).
Proof.
 refine (
  fix go r1 r2 :=
  match r1, r2 return Decision (ref_disjoint_rev r1 r2) with
  | rs1 :: r1, rs2 :: r2 =>
     if decide (rs1 ⊥ rs2) then left _
     else cast_if_and (decide (rs1 ~{freeze} rs2)) (go r1 r2)
  | _, _ => right _
  end); clear go;
   first [econstructor (by auto) | abstract (inversion 1; auto)].
Defined.
Lemma ref_disjoint_rev_correct_1 r1 r2 :
  ref_disjoint_rev r1 r2 → reverse r1 ⊥ reverse r2.
Proof.
  induction 1 as [|rs1 rs2 r1 r2 Hrs]; rewrite !reverse_cons.
  * by apply ref_disjoint_app, ref_disjoint_singleton.
  * rewrite Hrs. by apply ref_disjoint_here_app.
Qed.
Lemma ref_disjoint_rev_correct_2 r1 r2 :
  r1 ⊥ r2 → ref_disjoint_rev (reverse r1) (reverse r2).
Proof.
  rewrite ref_disjoint_alt.
  intros (r1'&rs1'&r1''&r2'&rs2'&r2''&Hr1&Hr2&?&Hr''); subst.
  rewrite !reverse_app, !reverse_singleton, <-!(associative_L (++)); simpl.
  apply (f_equal reverse) in Hr''. rewrite <-!fmap_reverse in Hr''.
  revert Hr''. generalize (reverse r2''); clear r2''.
  induction (reverse r1''); intros [|??] ?; simplify_equality';
    constructor (by auto).
Qed.
Lemma ref_disjoint_rev_correct r1 r2 :
  r1 ⊥ r2 ↔ ref_disjoint_rev (reverse r1) (reverse r2).
Proof.
  split.
  * apply ref_disjoint_rev_correct_2.
  * intros. rewrite <-(reverse_involutive r1), <-(reverse_involutive r2).
    by apply ref_disjoint_rev_correct_1.
Qed.
Global Instance ref_disjoint_dec r1 r2 : Decision (r1 ⊥ r2).
Proof.
  refine (cast_if (decide (ref_disjoint_rev (reverse r1) (reverse r2))));
   by rewrite ref_disjoint_rev_correct.
Qed.

Lemma RArray_disjoint_snoc r1 r2 i1 i2 n :
  r1 ++ [RArray i1 n] ⊥ r2 ++ [RArray i2 n] ↔ i1 ≠ i2 ∨ r1 ⊥ r2.
Proof.
  rewrite ref_disjoint_snoc. split.
  * intros [Harr|[??]]; [inversion Harr|]; tauto.
  * destruct (decide (i1 = i2)); intros [?|?];
      simplify_equality; eauto using RArray_disjoint.
Qed.
Lemma RStruct_disjoint_snoc r1 r2 i1 i2 s :
  r1 ++ [RStruct i1 s] ⊥ r2 ++ [RStruct i2 s] ↔ i1 ≠ i2 ∨ r1 ⊥ r2.
Proof.
  rewrite ref_disjoint_snoc. split.
  * intros [Hstru|[??]]; [inversion Hstru|]; tauto.
  * destruct (decide (i1 = i2)); intros [?|?];
      simplify_equality; eauto using RStruct_disjoint.
Qed.
Lemma RUnion_disjoint_snoc r1 r2 i1 q1 i2 q2 s :
  r1 ++ [RUnion i1 s q1] ⊥ r2 ++ [RUnion i2 s q2] ↔ i1 = i2 ∧ r1 ⊥ r2.
Proof.
  rewrite ref_disjoint_snoc. split.
  * by intros [Hu|[??]]; [inversion Hu|];
      unfold proj_eq in *; simplify_equality.
  * intros [<- ?]; eauto using RStruct_disjoint.
Qed.

Lemma ref_typed_array_size r rs σ τ :
  rs @ σ ↣ τ → ref_size (rs :: r) = array_size σ.
Proof. by intros []. Qed.
Lemma ref_typed_size τ r σ : r @ τ ↣ σ → ref_offset r < ref_size r.
Proof. destruct 1 as [|????? []]; auto with lia. Qed.

Lemma ref_offset_freeze r : ref_offset (freeze <$> r) = ref_offset r.
Proof. by destruct r as [|[]]. Qed.
Global Instance: Proper ((~{fmap freeze}) ==> (=)) ref_offset.
Proof.
  unfold proj_eq. intros r1 r2 ?.
  rewrite <-(ref_offset_freeze r1), <-(ref_offset_freeze r2). by f_equal.
Qed.
Lemma ref_size_freeze r : ref_size (freeze <$> r) = ref_size r.
Proof. by destruct r as [|[]]; simpl; rewrite ?ref_lookup_freeze. Qed.
Global Instance: Proper ((~{fmap freeze}) ==> (=)) ref_size.
Proof.
  unfold proj_eq. intros r1 r2 ?.
  rewrite <-(ref_size_freeze r1), <-(ref_size_freeze r2). by f_equal.
Qed.
Lemma ref_set_offset_freeze r i :
  ref_set_offset i (freeze <$> r) = freeze <$> ref_set_offset i r.
Proof. by destruct r as [|[]]. Qed.
Global Instance:
  Proper ((~{fmap freeze}) ==> (~{fmap freeze})) (ref_set_offset i).
Proof.
  unfold proj_eq. intros ????. rewrite <-!ref_set_offset_freeze. by f_equal.
Qed.

Lemma ref_size_set_offset i r : ref_size (ref_set_offset i r) = ref_size r.
Proof. by destruct r as [|[]]. Qed.
Lemma ref_offset_set_offset r i :
  i < ref_size r → ref_offset (ref_set_offset i r) = i.
Proof. destruct r as [|[]]; simpl in *; auto with lia. Qed.
Lemma ref_set_offset_typed τ r σ i :
  i < ref_size r → r @ τ ↣ σ → ref_set_offset i r @ τ ↣ σ.
Proof.
  destruct 2 as [|r rs ??? [] Hr]; simpl; repeat econstructor; eauto.
Qed.
Lemma ref_set_offset_offset r : ref_set_offset (ref_offset r) r = r.
Proof. by destruct r as [|[]]. Qed.
Lemma ref_set_offset_set_offset r i j :
  ref_set_offset i (ref_set_offset j r) = ref_set_offset i r.
Proof. by destruct r as [|[]]. Qed.

Lemma ref_set_offset_typed_unique τ r σ1 σ2 i :
  r @ τ ↣ σ1 → ref_set_offset i r @ τ ↣ σ2 → σ1 = σ2.
Proof.
  destruct 1 as [|r rs  τ τ' σ1 Hrs Hr]; simpl; [by rewrite ref_typed_nil |].
  rewrite ref_typed_cons. intros (τ''&?&Hrs'); simplify_type_equality'.
  by destruct Hrs; simpl in *; inversion Hrs'; simplify_option_equality.
Qed.
Lemma ref_set_offset_disjoint r i :
  ref_set_offset i r ⊥ r ∨ ref_set_offset i r = r.
Proof.
  destruct r as [|[j n| |]]; simpl; auto.
  destruct (decide (i = j)); subst; auto. by left; repeat constructor.
Qed.

Lemma size_of_ref τ r σ : r @ τ ↣ σ → size_of σ * ref_size r ≤ size_of τ.
Proof.
  induction 1 as [|r rs τ1 τ2 τ3 [] Hr IH]; simpl;
    auto with lia; (etransitivity; [|apply IH]); apply ref_typed_size in Hr.
  * rewrite <-(Nat.mul_1_r (size_of τ * n)), size_of_array.
    apply Nat.mul_le_mono; auto with lia.
  * apply Nat.mul_le_mono; eauto using size_of_struct_lookup with lia.
  * apply Nat.mul_le_mono; eauto using size_of_union_lookup with lia.
Qed.
Lemma ref_typed_subtype τ r1 r2 σ1 σ2 :
  r1 @ τ ↣ σ1 → r2 @ τ ↣ σ2 → r1 `suffix_of` r2 → σ2 ⊆ σ1.
Proof.
  intros Hr1 Hr2 [r ->]. rewrite ref_typed_app in Hr2.
  destruct Hr2 as (σ'&?&?); simplify_type_equality. by exists r.
Qed.

Lemma ref_disjoint_cases_help τ r1 r2 σ1 σ2 :
  r1 @ τ ↣ σ1 → r2 @ τ ↣ σ2 →
  (**i 1.) *) (∀ j1 j2, ref_set_offset j1 r1 ⊥ ref_set_offset j2 r2) ∨
  (**i 2.) *) (∃ j r', r1 ~{fmap freeze} r' ++ ref_set_offset j r2) ∨
  (**i 3.) *) (∃ j r', r2 ~{fmap freeze} r' ++ ref_set_offset j r1) ∨
  (**i 4.) *) ∃ s r1' i1 q1 r2' i2 q2 r',
    r1 ~{fmap freeze} r1' ++ [RUnion i1 s q1] ++ r' ∧
    r2 ~{fmap freeze} r2' ++ [RUnion i2 s q2] ++ r' ∧ i1 ≠ i2.
Proof.
  intros Hr1. revert r2 σ2. revert τ r1 σ1 Hr1. assert (∀ τ rs1 r2 σ1 σ2,
    rs1 @ τ ↣ σ1 → r2 @ τ ↣ σ2 →
    (* 1.) *) (∀ j1 j2, ref_set_offset j1 [rs1] ⊥ ref_set_offset j2 r2) ∨
    (* 2.) *) (∃ j r', r2 ~{fmap freeze} r' ++ ref_set_offset j [rs1]) ∨
    (* 3.) *) r2 = [] ∨
    (* 4.) *) ∃ s i1 q1 r2' i2 q2, rs1 = RUnion i1 s q1 ∧
      r2 = r2' ++ [RUnion i2 s q2] ∧ i1 ≠ i2) as aux.
  { intros τ rs1 r2 σ1 σ2 Hrs1 Hr2. destruct r2 as [|rs2 r2 _] using rev_ind.
    { by do 2 right; left. }
    rewrite ref_typed_snoc in Hr2. destruct Hr2 as (σ2'&Hrs2&Hr2).
    destruct Hrs1 as [? i1 n|s i1|s i1 q1];
      inversion Hrs2 as [? i2|? i2|? i2 q2]; subst.
    * right; left. by eexists i2, r2.
    * destruct (decide (i1 = i2)); subst.
      + right; left. by eexists 0, r2.
      + left. intros. simpl. destruct r2; simpl.
        { by repeat constructor. }
        rewrite app_comm_cons. apply ref_disjoint_app_r. by repeat constructor.
    * destruct (decide (i1 = i2)); subst.
      + right; left. eexists 0, r2. simpl. f_equiv.
      + do 3 right. by eexists s, i1, q1, r2, i2, q2. }
  induction 1 as [τ|r1 rs1 τ τ1 σ1 Hrs1 Hr1 IH]; intros r2 σ2 Hr2.
  { do 2 right; left. exists 0 r2. simpl. by rewrite (right_id_L [] (++)). }
  destruct Hr2 as [τ|r2 rs2 τ τ2 σ2 Hrs2 Hr2].
  { right; left. exists 0 (rs1 :: r1). simpl. by rewrite (right_id_L [] (++)). }
  destruct (IH _ _ Hr2) as
    [Hr|[(j&r'&Hr1')|[(j&r'&Hr2')|(s&r1'&i1&q1&r2'&i2&q2&r'&Hr1'&Hr2'&?)]]];
    clear IH.
  * left. intros j1 j2. simpl. apply ref_disjoint_cons_l, ref_disjoint_cons_r.
    by rewrite <-(ref_set_offset_offset r1), <-(ref_set_offset_offset r2).
  * rewrite Hr1', ref_typed_app in Hr1. destruct Hr1 as (τ2'&Hr2'&Hr').
    assert (τ2' = τ2) by
      eauto using ref_set_offset_typed_unique, eq_sym; subst; clear Hr2'.
    destruct (ref_set_offset_disjoint r2 j) as [?|Hr2eq].
    { left. intros j1 j2. simpl. rewrite Hr1', app_comm_cons.
      by apply ref_disjoint_app_l, ref_disjoint_cons_r. }
    rewrite Hr2eq in Hr1'; clear Hr2eq. destruct (aux τ2 rs2 (rs1 :: r') σ2 σ1)
      as [Hr|[(j'&r''&Hr'')|[?|(s&i1&q1&r2'&i2&q2&?&Hr2'&?)]]]; subst.
    { done. }
    { econstructor; eauto. }
    + left. intros j1 j2. simpl. rewrite Hr1'. rewrite app_comm_cons.
      apply (ref_disjoint_here_app _ [_]); auto. symmetry. by apply Hr.
    + right; left. exists j' r''. simpl.
      by rewrite Hr1', app_comm_cons, Hr'', <-(associative_L (++)).
    + discriminate_list_equality.
    + do 3 right. eexists s, r2', i2, q2, [], i1, q1, r2.
      by rewrite Hr1', app_comm_cons, Hr2', (associative_L (++)).
  * rewrite Hr2', ref_typed_app in Hr2. destruct Hr2 as (τ1'&Hr1'&Hr').
    assert (τ1' = τ1) by
      eauto using ref_set_offset_typed_unique, eq_sym; subst; clear Hr1'.
    destruct (ref_set_offset_disjoint r1 j) as [?|Hr1eq].
    { left. intros j1 j2. simpl. rewrite Hr2', app_comm_cons.
      apply (ref_disjoint_app [_]). by symmetry. }
    rewrite Hr1eq in Hr2'; clear Hr1eq. destruct (aux τ1 rs1 (rs2 :: r') σ1 σ2)
      as [Hr|[(j'&r''&Hr'')|[?|(s&i1&q1&r2'&i2&q2&?&Hr1'&?)]]]; subst.
    { done. }
    { econstructor; eauto. }
    + left. intros j1 j2. simpl. rewrite Hr2', app_comm_cons.
      apply (ref_disjoint_here_app [_]). by apply Hr. done.
    + do 2 right; left. exists j' r''. simpl.
      by rewrite Hr2', app_comm_cons, Hr'', <-(associative_L (++)).
    + discriminate_list_equality.
    + do 3 right. eexists s, [], i1, q1, r2', i2, q2, r1.
      by rewrite Hr2', app_comm_cons, Hr1', !(associative_L (++)).
  * do 3 right.
    eexists s, (rs1 :: r1'), i1, q1, (rs2 :: r2'), i2, q2, r'.
    by rewrite Hr1', Hr2'.
Qed.
Lemma ref_disjoint_cases τ r1 r2 σ1 σ2 :
  r1 @ τ ↣ σ1 → r2 @ τ ↣ σ2 → Forall frozen r1 → Forall frozen r2 →
  (**i 1.) *) (∀ j1 j2, ref_set_offset j1 r1 ⊥ ref_set_offset j2 r2) ∨
  (**i 2.) *) σ1 ⊆ σ2 ∨
  (**i 3.) *) σ2 ⊆ σ1 ∨
  (**i 4.) *) ∃ s r1' i1 r2' i2 r',
    r1 = r1' ++ [RUnion i1 s false] ++ r' ∧
    r2 = r2' ++ [RUnion i2 s false] ++ r' ∧ i1 ≠ i2.
Proof.
  intros Hr1 Hr2 ??. destruct (ref_disjoint_cases_help τ r1 r2 σ1 σ2) as
    [?|[(j&r'&Hr1')|[(j&r'&Hr2')|(s&r1'&i1&q1&r2'&i2&q2&r'&Hr1'&Hr2'&?)]]];
    eauto.
  * rewrite Hr1', ref_typed_app in Hr1. destruct Hr1 as (σ2'&?&?).
    assert (σ2' = σ2) by eauto using ref_set_offset_typed_unique, eq_sym; subst.
    right; left. by exists r'.
  * rewrite Hr2', ref_typed_app in Hr2. destruct Hr2 as (σ1'&?&?).
    assert (σ1' = σ1) by eauto using ref_set_offset_typed_unique, eq_sym; subst.
    do 2 right; left. by exists r'.
  * do 3 right. unfold proj_eq in Hr1', Hr2'.
    rewrite ref_frozen_freeze, !fmap_app in Hr1', Hr2' by done. naive_solver.
Qed.
End refs.
