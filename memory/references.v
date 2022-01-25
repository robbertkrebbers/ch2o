(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import list.
Require Export type_environment.
Local Open Scope ctype_scope.

(** * References *)
Inductive ref_seg (K : iType) : iType :=
  | RArray : nat → type K → nat → ref_seg K
  | RStruct : nat → tag → ref_seg K
  | RUnion : nat → tag → bool → ref_seg K.
Notation ref K := (list (ref_seg K)).
Arguments RArray {_} _ _ _.
Arguments RStruct {_} _ _.
Arguments RUnion {_} _ _ _.

#[global] Instance ref_seg_eq_dec `{EqDecision K}: EqDecision (ref_seg K).
Proof.
  intros * r1 r2.
  refine
    match r1, r2 with
    | RArray i1 τ1 n1, RArray i2 τ2 n2 =>
      cast_if_and3 (decide (i1 = i2)) (decide (τ1 = τ2)) (decide (n1 = n2))
    | RStruct i1 s1, RStruct i2 s2 =>
      cast_if_and (decide (i1 = i2)) (decide (s1 = s2))
    | RUnion i1 s1 β1, RUnion i2 s2 β2 =>
      cast_if_and3 (decide (i1 = i2)) (decide (s1 = s2)) (decide (β1 = β2))
    | _, _ => right _
    end; abstract congruence.
Defined.

Inductive ref_seg_typed' `{Env K} (Γ : env K) :
     ref_seg K → type K → type K → Prop :=
  | RArray_typed τ i n :
     i < n → ref_seg_typed' Γ (RArray i τ n) (τ.[n]) τ
  | RStruct_typed t i τs τ :
     Γ !! t = Some τs → τs !! i = Some τ →
     ref_seg_typed' Γ (RStruct i t) (structT t) τ
  | RUnion_typed t i β τs τ :
     Γ !! t = Some τs → τs !! i = Some τ →
     ref_seg_typed' Γ (RUnion i t β) (unionT t) τ.
#[global] Instance ref_seg_typed `{Env K} :
  PathTyped (env K) (type K) (type K) (ref_seg K) := ref_seg_typed'.

Inductive ref_typed' `{Env K} (Γ : env K) :
     ref K → type K → type K → Prop :=
  | ref_nil_typed' τ : ref_typed' Γ [] τ τ
  | ref_cons_typed' r rs τ1 τ2 τ3 :
     Γ ⊢ rs : τ2 ↣ τ3 → ref_typed' Γ r τ1 τ2 → ref_typed' Γ (rs :: r) τ1 τ3.
#[global] Instance ref_typed `{Env K} :
  PathTyped (env K) (type K) (type K) (ref K) := ref_typed'.

#[global] Instance subtype `{Env K} : SubsetEqE (env K) (type K) :=
  λ Γ τ1 τ2, ∃ r : ref K, Γ ⊢ r : τ2 ↣ τ1.
#[global] Instance ref_seg_lookup `{EqDecision K} :
    LookupE (env K) (ref_seg K) (type K) (type K) := λ Γ rs τ,
  match rs, τ with
  | RArray i τ' n', τ.[n] =>
     guard (τ = τ'); guard (n = n'); guard (i < n); Some τ
  | RStruct i t', structT t => guard (t = t'); Γ !! t ≫= (.!! i)
  | RUnion i t' _, unionT t => guard (t = t'); Γ !! t ≫= (.!! i)
  | _, _ => None
  end.
#[global] Instance ref_lookup `{EqDecision K} :
    LookupE (env K) (ref K) (type K) (type K) :=
  fix go Γ r τ {struct r} := let _ : LookupE _ _ _ _ := @go in
  match r with [] => Some τ | rs :: r => τ !!{Γ} r ≫= lookupE Γ rs end.

Class Freeze A := freeze: bool → A → A.
Arguments freeze {_ _} _ !_ /.
Definition frozen `{Freeze A} (x : A) := freeze true x = x.
Arguments freeze {_ _} _ !_ /.

#[global] Instance ref_seg_freeze {K} : Freeze (ref_seg K) := λ β rs,
  match rs with
  | RArray i τ n => RArray i τ n
  | RStruct i t => RStruct i t
  | RUnion i t _ => RUnion i t β
  end.

Definition ref_seg_set_offset {K} (i : nat) (rs : ref_seg K) : ref_seg K :=
  match rs with RArray _ τ n => RArray i τ n | _ => rs end.
Arguments ref_seg_set_offset _ _ !_ /.
Notation ref_seg_base := (ref_seg_set_offset 0).
Definition ref_set_offset {K} (i : nat) (r : ref K) : ref K :=
  match r with rs :: r => ref_seg_set_offset i rs :: r | _ => r end.
Arguments ref_set_offset _ _ !_ /.
Notation ref_base := (ref_set_offset 0).

Definition ref_seg_offset {K} (rs : ref_seg K) : nat :=
  match rs with RArray i _ _ => i | _ => 0 end.
Arguments ref_seg_offset _ !_ /.
Definition ref_offset {K} (r : ref K) : nat :=
  match r with rs :: r => ref_seg_offset rs | _ => 0 end.
Arguments ref_offset _ !_ /.
Definition ref_seg_size {K} (rs : ref_seg K) : nat :=
  match rs with RArray _ _ n => n | _ => 1 end.
Arguments ref_seg_size _ !_ /.
Definition ref_size {K} (r : ref K) : nat :=
  match r with rs :: _ => ref_seg_size rs | _ => 1 end.
Arguments ref_size _ !_ /.

Inductive ref_seg_disjoint {K} : Disjoint (ref_seg K) :=
  | RArray_disjoint i1 i2 τ n : i1 ≠ i2 → @RArray K i1 τ n ## RArray i2 τ n
  | RStruct_disjoint i1 i2 t : i1 ≠ i2 → @RStruct K i1 t ## RStruct i2 t.
#[global] Existing Instance ref_seg_disjoint.
Inductive ref_disjoint {K} : Disjoint (ref K) :=
  | ref_disjoint_here rs1 rs2 (r1 r2 : ref K) :
     freeze true <$> r1 = freeze true <$> r2 →
     rs1 ## rs2 → rs1 :: r1 ## rs2 :: r2
  | ref_disjoint_cons_l rs1 (r1 r2 : ref K) : r1 ## r2 → rs1 :: r1 ## r2
  | ref_disjoint_cons_r rs2 (r1 r2 : ref K): r1 ## r2 → r1 ## rs2 :: r2.
#[global] Existing Instance ref_disjoint.

Definition ref_seg_object_offset `{Env K}
    (Γ : env K) (rs : ref_seg K) : nat :=
  match rs with
  | RArray i τ _ => i * bit_size_of Γ τ
  | RStruct i t => from_option (λ τs, bit_offset_of Γ τs i) 0 (Γ !! t)
  | RUnion i _ _ => 0
  end.
Definition ref_object_offset `{Env K} (Γ : env K) (r : ref K) : nat :=
  sum_list (ref_seg_object_offset Γ <$> r).

Inductive ref_seg_le {K} : SubsetEq (ref_seg K) :=
  | RArray_refine i τ n : @RArray K i τ n ⊆ RArray i τ n
  | RStruct_refine i t : @RStruct K i t ⊆ RStruct i t
  | RUnion_refine i t (β1 β2 : bool) :
     (β2 → β1) → @RUnion K i t β1 ⊆ RUnion i t β2.
#[global] Existing Instance ref_seg_le.

Section ref_typed_ind.
  Context `{Env K} (Γ : env K) (P : ref K → type K → type K → Prop).
  Context (Pnil : ∀ τ, P [] τ τ).
  Context (Pcons : ∀ r rs τ1 τ2 τ3,
    Γ ⊢ rs : τ2 ↣ τ3 → Γ ⊢ r : τ1 ↣ τ2 → P r τ1 τ2 → P (rs :: r) τ1 τ3).
  Lemma ref_typed_ind r τ σ : ref_typed' Γ r τ σ → P r τ σ.
  Proof. induction 1; eauto. Qed. 
End ref_typed_ind.

Section references.
Context `{EqDecision K, EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types τ : type K.
Implicit Types rs : ref_seg K.
Implicit Types r : ref K.

Lemma ref_typed_nil Γ τ1 τ2 : Γ ⊢ @nil (ref_seg K) : τ1 ↣ τ2 ↔ τ1 = τ2.
Proof. split. by intros; simplify_type_equality. intros <-. constructor. Qed.
Lemma ref_typed_nil_2 Γ τ : Γ ⊢ @nil (ref_seg K) : τ ↣ τ.
Proof. constructor. Qed.
Lemma ref_typed_cons Γ rs r τ1 τ3 :
  Γ ⊢ rs :: r : τ1 ↣ τ3 ↔ ∃ τ2, Γ ⊢ r : τ1 ↣ τ2 ∧ Γ ⊢ rs : τ2 ↣ τ3.
Proof.
  unfold path_typed at 1 2, ref_typed; simpl. split.
  * inversion 1; subst; eauto.
  * intros (?&?&?). econstructor; eauto.
Qed.
Lemma ref_typed_app Γ r1 r2 τ1 τ3 :
  Γ ⊢ r1 ++ r2 : τ1 ↣ τ3 ↔ ∃ τ2, Γ ⊢ r2 : τ1 ↣ τ2 ∧ Γ ⊢ r1 : τ2 ↣ τ3.
Proof.
  revert τ1 τ3. induction r1; simpl; intros.
  * setoid_rewrite ref_typed_nil. naive_solver.
  * setoid_rewrite ref_typed_cons. naive_solver.
Qed.
Lemma ref_typed_singleton Γ rs τ1 τ2 : Γ ⊢ [rs] : τ1 ↣ τ2 ↔ Γ ⊢ rs : τ1 ↣ τ2.
Proof. rewrite ref_typed_cons. setoid_rewrite ref_typed_nil. naive_solver. Qed.
Lemma ref_typed_snoc Γ r rs τ1 τ3 :
  Γ ⊢ r ++ [rs] : τ1 ↣ τ3 ↔ ∃ τ2, Γ ⊢ rs : τ1 ↣ τ2 ∧ Γ ⊢ r : τ2 ↣ τ3.
Proof. setoid_rewrite ref_typed_app. by setoid_rewrite ref_typed_singleton. Qed.
Lemma ref_typed_snoc_2 Γ r rs τ1 τ2 τ3 :
  Γ ⊢ rs : τ1 ↣ τ2 ∧ Γ ⊢ r : τ2 ↣ τ3 → Γ ⊢ r ++ [rs] : τ1 ↣ τ3.
Proof. rewrite ref_typed_snoc; eauto. Qed.
Lemma ref_lookup_nil Γ : lookupE Γ (@nil (ref_seg K)) = Some.
Proof. done. Qed.
Lemma ref_lookup_cons Γ rs r :
  lookupE Γ (rs :: r) = λ τ, τ !!{Γ} r ≫= lookupE Γ rs.
Proof. done. Qed.
Lemma ref_lookup_singleton Γ rs : lookupE Γ [rs] = lookupE Γ rs.
Proof. done. Qed.
Lemma ref_lookup_app Γ r1 r2 τ :
  τ !!{Γ} (r1 ++ r2) = (τ !!{Γ} r2) ≫= lookupE Γ r1.
Proof.
  induction r1 as [|rs1 r1 IH]; simpl; [by destruct (τ !!{_} r2)|].
  by rewrite ref_lookup_cons, IH, option_bind_assoc.
Qed.
Lemma ref_lookup_snoc Γ r rs τ :
  τ !!{Γ} (r ++ [rs]) = (τ !!{Γ} rs) ≫= lookupE Γ r.
Proof. apply ref_lookup_app. Qed.

Lemma ref_seg_typed_ptr_type_valid Γ rs τ σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ → ✓{Γ} (TType τ) → ✓{Γ} σ.
Proof.
  intro. destruct 1; inversion 1; subst;
    eauto using env_valid_lookup_lookup.
Qed.
Lemma ref_seg_typed_type_valid Γ rs τ σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ → ✓{Γ} τ → ✓{Γ} σ.
Proof. eauto using type_valid_ptr_type_valid, ref_seg_typed_ptr_type_valid. Qed.
Lemma ref_typed_type_valid Γ r τ σ : ✓ Γ → Γ ⊢ r : τ ↣ σ → ✓{Γ} τ → ✓{Γ} σ.
Proof. intro. induction 1; eauto using ref_seg_typed_type_valid. Qed.
#[global] Instance:
  PathTypeCheckSpecUnique (env K) (type K) (type K) (ref_seg K) (λ _, True).
Proof.
  split.
  * intros Γ rs τ σ _. split; [|by destruct 1; simplify_option_eq].
    destruct rs, τ as [| |[]]; intros;
      simplify_option_eq; econstructor; eauto.
  * by destruct 2; inversion 1.
Qed.
#[global] Instance:
  PathTypeCheckSpecUnique (env K) (type K) (type K) (ref K) (λ _, True).
Proof.
  split.
  * intros Γ r τ σ. split.
    + revert σ. induction r as [|rs r IH]; intros σ.
      { rewrite ref_lookup_nil; intros; simplify_equality'; constructor. }
      rewrite ref_lookup_cons, ref_typed_cons, bind_Some.
      intros (σ'&?&?). exists σ'; split; auto. by apply path_type_check_correct.
    + induction 1; [done|rewrite ref_lookup_cons].
      simplify_option_eq. by apply path_type_check_complete.
  * intros Γ r τ1 τ2 σ _ Hr. revert τ2.
    induction Hr as [|r rs σ1 σ2 σ3 ?? IH] using @ref_typed_ind; intros τ1.
    { by rewrite ref_typed_nil. }
    rewrite ref_typed_cons; intros (τ2&?&?); apply IH.
    by rewrite (path_typed_unique_l Γ rs σ2 τ2 σ3) by done.
Qed.
Lemma ref_seg_typed_weaken Γ1 Γ2 rs τ σ :
  Γ1 ⊢ rs : τ ↣ σ → Γ1 ⊆ Γ2 → Γ2 ⊢ rs : τ ↣ σ.
Proof. destruct 1; econstructor; eauto using lookup_compound_weaken. Qed.
Lemma ref_typed_weaken Γ1 Γ2 r τ σ : Γ1 ⊢ r : τ ↣ σ → Γ1 ⊆ Γ2 → Γ2 ⊢ r : τ ↣ σ.
Proof.
  intros Hr ?. induction Hr using @ref_typed_ind;
    econstructor; eauto using ref_seg_typed_weaken.
Qed.
Lemma ref_lookup_weaken Γ1 Γ2 r τ σ :
  τ !!{Γ1} r = Some σ → Γ1 ⊆ Γ2 → τ !!{Γ2} r = Some σ.
Proof. rewrite !path_type_check_correct by done. by apply ref_typed_weaken. Qed.
Lemma ref_seg_typed_inv_base Γ τb rs σ : ¬Γ ⊢ rs : baseT τb ↣ σ.
Proof. inversion 1. Qed.
Lemma ref_typed_inv_base Γ τb r σ :
  Γ ⊢ r : baseT τb ↣ σ → σ = baseT τb ∧ r = [].
Proof.
  destruct r as [|rs r] using rev_ind; [by rewrite ref_typed_nil|].
  rewrite ref_typed_snoc; intros (?&Hrs&_).
  edestruct ref_seg_typed_inv_base; eauto.
Qed.
Lemma ref_seg_typed_size Γ τ rs σ :
  Γ ⊢ rs : τ ↣ σ → ref_seg_offset rs < ref_seg_size rs.
Proof. destruct 1; auto with lia. Qed.
Lemma ref_typed_size Γ τ r σ : Γ ⊢ r : τ ↣ σ → ref_offset r < ref_size r.
Proof. destruct 1; csimpl; eauto using ref_seg_typed_size. Qed.
Lemma ref_set_offset_length r i : length (ref_set_offset i r) = length r.
Proof. by destruct r. Qed.
Lemma ref_seg_size_set_offset i rs :
  ref_seg_size (ref_seg_set_offset i rs) = ref_seg_size rs.
Proof. by destruct rs. Qed.
Lemma ref_size_set_offset i r : ref_size (ref_set_offset i r) = ref_size r.
Proof. destruct r; simpl; auto using ref_seg_size_set_offset. Qed.
Lemma ref_seg_offset_set_offset rs i :
  i < ref_seg_size rs → ref_seg_offset (ref_seg_set_offset i rs) = i.
Proof. destruct rs; simpl in *; auto with lia. Qed.
Lemma ref_offset_set_offset r i :
  i < ref_size r → ref_offset (ref_set_offset i r) = i.
Proof. destruct r; simpl; auto using ref_seg_offset_set_offset with lia. Qed.
Lemma ref_offset_base_nil r : ref_base r = [] → ref_offset r = 0.
Proof. by destruct r. Qed.
Lemma ref_seg_set_offset_typed Γ τ rs σ i :
  i < ref_seg_size rs → Γ ⊢ rs : τ ↣ σ → Γ ⊢ ref_seg_set_offset i rs : τ ↣ σ.
Proof. destruct 2; econstructor; eauto. Qed.
Lemma ref_set_offset_typed Γ τ r σ i :
  i < ref_size r → Γ ⊢ r : τ ↣ σ → Γ ⊢ ref_set_offset i r : τ ↣ σ.
Proof. destruct 2; econstructor; eauto using ref_seg_set_offset_typed. Qed.
Lemma ref_seg_set_offset_offset rs :
  ref_seg_set_offset (ref_seg_offset rs) rs = rs.
Proof. by destruct rs. Qed.
Lemma ref_set_offset_offset r : ref_set_offset (ref_offset r) r = r.
Proof. destruct r; f_equal'; auto using ref_seg_set_offset_offset. Qed.
Lemma ref_set_offset_set_offset r i j :
  ref_set_offset i (ref_set_offset j r) = ref_set_offset i r.
Proof. by destruct r as [|[]]. Qed.
Lemma ref_set_offset_typed_unique Γ τ r σ1 σ2 i :
  Γ ⊢ r : τ ↣ σ1 → Γ ⊢ ref_set_offset i r : τ ↣ σ2 → σ1 = σ2.
Proof.
  destruct r as [|rs r]; simpl; [rewrite !ref_typed_nil; congruence|].
  rewrite !ref_typed_cons. intros (τ1&?&Hrs1) (τ2&?&Hrs2).
  simplify_type_equality'.
  by destruct Hrs1; inversion Hrs2; simplify_option_eq.
Qed.
Lemma size_of_ref Γ τ r σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ → size_of Γ σ * ref_size r ≤ size_of Γ τ.
Proof.
  intros ?. induction 1 as [|r rs τ1 τ2 τ3 Hrs Hr IH]
    using @ref_typed_ind; simpl; [lia|].
  transitivity (size_of Γ τ2 * ref_size r); [|done].
  apply ref_typed_size in Hr.
  destruct Hrs as [τ' i n|s i τs τ'|s i τs τ']; simpl.
  * rewrite <-(Nat.mul_1_r (size_of Γ τ' * n)), size_of_array.
    apply Nat.mul_le_mono; auto with lia.
  * apply Nat.mul_le_mono; eauto using size_of_struct_lookup with lia.
  * apply Nat.mul_le_mono; eauto using size_of_union_lookup with lia.
Qed.
Lemma size_of_ref' Γ τ r σ : ✓ Γ → Γ ⊢ r : τ ↣ σ → size_of Γ σ ≤ size_of Γ τ.
Proof.
  intros ? Hr. rewrite <-(Nat.mul_1_r (size_of Γ σ)).
  transitivity (size_of Γ σ * ref_size r); auto using size_of_ref.
  apply ref_typed_size in Hr; apply Nat.mul_le_mono_l; lia.
Qed.

#[global] Instance: `{PreOrder (@subseteqE (env K) (type K) _ Γ)}.
Proof.
  intros Γ. repeat split.
  * eexists []. constructor.
  * intros ??? (r1&?) (r2&?). exists (r1 ++ r2). apply ref_typed_app; eauto.
Qed.
Lemma ref_typed_subtype Γ τ r1 r2 σ1 σ2 :
  Γ ⊢ r1 : τ ↣ σ1 → Γ ⊢ r2 : τ ↣ σ2 → r1 `suffix_of` r2 → σ2 ⊆{Γ} σ1.
Proof.
  intros Hr1 Hr2 [r ->]. rewrite ref_typed_app in Hr2.
  destruct Hr2 as (σ'&?&?); simplify_type_equality. by exists r.
Qed.
Lemma subtype_weaken Γ Σ σ τ : σ ⊆{Γ} τ → Γ ⊆ Σ → σ ⊆{Σ} τ.
Proof. intros (r&?); exists r; eauto using ref_typed_weaken. Qed.

Lemma ref_seg_freeze_freeze β1 β2 rs : freeze β1 (freeze β2 rs) = freeze β1 rs.
Proof. by destruct rs. Qed.
Lemma ref_freeze_freeze (β1 β2: bool) (r: ref K):
  freeze β1 <$> (freeze β2 <$> r) = freeze β1 <$> r.
Proof.
  rewrite <-list_fmap_compose.
  apply list_fmap_ext; simpl; auto using ref_seg_freeze_freeze.
Qed.
Lemma ref_seg_freeze_le_l rs : freeze true rs ⊆ rs.
Proof. by destruct rs; constructor. Qed.
Lemma ref_freeze_le_l r : freeze true <$> r ⊆* r.
Proof. induction r; simpl; auto using ref_seg_freeze_le_l. Qed.
Lemma ref_seg_freeze_le_r rs : rs ⊆ freeze false rs.
Proof. by destruct rs; constructor. Qed.
Lemma ref_freeze_le_r r : r ⊆* freeze false <$> r.
Proof. induction r; simpl; auto using ref_seg_freeze_le_r. Qed.
Lemma ref_seg_freeze_le β rs1 rs2 : rs1 ⊆ rs2 → freeze β rs1 = freeze β rs2.
Proof. by destruct 1. Qed.
Lemma ref_freeze_le β r1 r2 : r1 ⊆* r2 → freeze β <$> r1 = freeze β <$> r2.
Proof. induction 1; f_equal'; eauto using ref_seg_freeze_le. Qed.
#[global] Instance: PartialOrder (@subseteq (ref_seg K) _).
Proof.
  repeat split; [by intros []; constructor| |].
  * destruct 1; inversion 1; constructor; auto.
  * destruct 1; inversion 1; f_equal. by apply eq_bool_prop_intro.
Qed.
Lemma ref_seg_typed_le Γ rs1 rs2 τ σ :
  Γ ⊢ rs1 : τ ↣ σ → rs1 ⊆ rs2 → Γ ⊢ rs2 : τ ↣ σ.
Proof. destruct 1; inversion 1; econstructor; eauto. Qed.
Lemma ref_typed_le Γ r1 r2 τ σ : Γ ⊢ r1 : τ ↣ σ → r1 ⊆* r2 → Γ ⊢ r2 : τ ↣ σ.
Proof.
  intros Hr1; revert r2. induction Hr1 using @ref_typed_ind; intros;
    decompose_Forall_hyps; typed_constructor; eauto using ref_seg_typed_le.
Qed.
Lemma ref_seg_typed_ge Γ rs1 rs2 τ σ :
  Γ ⊢ rs2 : τ ↣ σ → rs1 ⊆ rs2 → Γ ⊢ rs1 : τ ↣ σ.
Proof. destruct 1; inversion 1; econstructor; eauto. Qed.
Lemma ref_typed_ge Γ r1 r2 τ σ : Γ ⊢ r2 : τ ↣ σ → r1 ⊆* r2 → Γ ⊢ r1 : τ ↣ σ.
Proof.
  intros Hr2; revert r1. induction Hr2 using @ref_typed_ind; intros;
    decompose_Forall_hyps; typed_constructor; eauto using ref_seg_typed_ge.
Qed.
Lemma ref_seg_typed_freeze Γ β τ rs σ :
  Γ ⊢ freeze β rs : τ ↣ σ ↔ Γ ⊢ rs : τ ↣ σ.
Proof.
  destruct β; split; eauto using ref_seg_typed_ge,
    ref_seg_typed_le, ref_seg_freeze_le_l, ref_seg_freeze_le_r.
Qed.
Lemma ref_typed_freeze Γ β τ r σ : Γ ⊢ freeze β <$> r : τ ↣ σ ↔ Γ ⊢ r : τ ↣ σ.
Proof.
  destruct β; split; eauto using ref_typed_ge,
    ref_typed_le, ref_freeze_le_l, ref_freeze_le_r.
Qed.
Lemma ref_offset_le r1 r2 : r1 ⊆* r2 → ref_offset r1 = ref_offset r2.
Proof. by destruct 1 as [|???? []]. Qed.
Lemma ref_size_le r1 r2 : r1 ⊆* r2 → ref_size r1 = ref_size r2.
Proof. by destruct 1 as [|???? []]. Qed.
Lemma ref_frozen_le r1 r2 :
  r1 ⊆* r2 → freeze true <$> r2 = r2 → freeze true <$> r1 = r1.
Proof.
  induction 1 as [|???? [| |?? []]]; intros; simplify_equality'; f_equal; tauto.
Qed.
Lemma ref_le_unique r1 r2 r3 :
  r1 ⊆* r2 → r1 ⊆* r3 → freeze true <$> r2 = freeze true <$> r3.
Proof.
  intros. transitivity (freeze true <$> r1); auto using ref_freeze_le, eq_sym.
Qed.
Lemma ref_le_unique_alt r1 r2 r3 :
  r1 ⊆* r2 → r1 ⊆* r3 →
  freeze true <$> r2 = r2 → freeze true <$> r3 = r3 → r2 = r3.
Proof. intros ?? <- <-; eauto using ref_le_unique. Qed.
Lemma ref_seg_set_offset_le rs1 rs2 i :
  rs1 ⊆ rs2 → ref_seg_set_offset i rs1 ⊆ ref_seg_set_offset i rs2.
Proof. by destruct 1; constructor. Qed.
Lemma ref_set_offset_le r1 r2 i :
  r1 ⊆* r2 → ref_set_offset i r1 ⊆* ref_set_offset i r2.
Proof. destruct 1; constructor; auto using ref_seg_set_offset_le. Qed.
Lemma ref_seg_offset_freeze β rs :
  ref_seg_offset (freeze β rs) = ref_seg_offset rs.
Proof. by destruct rs. Qed.
Lemma ref_offset_freeze β r : ref_offset (freeze β <$> r) = ref_offset r.
Proof. destruct r; simpl; auto using ref_seg_offset_freeze. Qed.
Lemma ref_seg_set_offset_freeze β rs i :
  ref_seg_set_offset i (freeze β rs) = freeze β (ref_seg_set_offset i rs).
Proof. by destruct rs. Qed.
Lemma ref_set_offset_freeze β r i :
  ref_set_offset i (freeze β <$> r) = freeze β <$> ref_set_offset i r.
Proof. destruct r; f_equal'; auto using ref_seg_set_offset_freeze. Qed.
Lemma ref_seg_size_freeze β rs : ref_seg_size (freeze β rs) = ref_seg_size rs.
Proof. by destruct rs. Qed.
Lemma ref_size_freeze β r : ref_size (freeze β <$> r) = ref_size r.
Proof. destruct r; simpl; auto using ref_seg_size_freeze. Qed.
Lemma ref_seg_object_offset_freeze Γ β rs :
  ref_seg_object_offset Γ (freeze β rs) = ref_seg_object_offset Γ rs.
Proof. by destruct rs. Qed.
Lemma ref_object_offset_freeze Γ β r :
  ref_object_offset Γ (freeze β <$> r) = ref_object_offset Γ r.
Proof.
  unfold ref_object_offset.
  induction r; f_equal'; auto using ref_seg_object_offset_freeze.
Qed.
Lemma ref_object_offset_le Γ r1 r2 :
  r1 ⊆* r2 → ref_object_offset Γ r1 = ref_object_offset Γ r2.
Proof.
  intros. rewrite <-(ref_object_offset_freeze Γ false r1),
    <-(ref_object_offset_freeze Γ false r2); f_equal; auto using ref_freeze_le.
Qed.

Lemma ref_disjoint_app_l r1 r1' r2' : r1' ## r2' → r1 ++ r1' ## r2'.
Proof. induction r1; simpl; auto using ref_disjoint_cons_l. Qed.
Lemma ref_disjoint_app_r r2 r1' r2' : r1' ## r2' → r1' ## r2 ++ r2'.
Proof. induction r2; simpl; auto using ref_disjoint_cons_r. Qed.
Lemma ref_disjoint_app r1 r2 r1' r2' : r1' ## r2' → r1 ++ r1' ## r2 ++ r2'.
Proof. auto using ref_disjoint_app_l, ref_disjoint_app_r. Qed.
Lemma ref_disjoint_here_app_1 r1 r2 r1' r2' :
  r1 ## r2 → freeze true <$> r1' = freeze true <$> r2' → r1 ++ r1' ## r2 ++ r2'.
Proof.
  induction 1; simpl; constructor; rewrite ?fmap_app; auto with f_equal.
Qed.
#[global] Instance: Symmetric (@disjoint (ref_seg K) _).
Proof. destruct 1; constructor; auto. Qed.
#[global] Instance: Symmetric (@disjoint (ref K) _).
Proof. induction 1; constructor; by auto. Qed.
Lemma ref_disjoint_alt r1 r2 :
  r1 ## r2 ↔ ∃ r1' rs1 r1'' r2' rs2 r2'',
    r1 = r1' ++ [rs1] ++ r1'' ∧ r2 = r2' ++ [rs2] ++ r2'' ∧
    rs1 ## rs2 ∧ freeze true <$> r1'' = freeze true <$> r2''.
Proof.
  split.
  * induction 1 as [rs1 rs2 r1 r2|
      rs1 r1 r2 ? (r1'&rs1'&r1''&r2'&rs2'&r2''&->&->&?&?)|
      rs2 r1 r2 ? (r1'&rs1'&r1''&r2'&rs2'&r2''&->&->&?&?)].
    + by eexists [], rs1, r1, [], rs2, r2.
    + by eexists (rs1 :: r1'), rs1', r1'', r2', rs2', r2''.
    + by eexists r1', rs1', r1'', (rs2 :: r2'), rs2', r2''.
  * intros (r1'&rs1'&r1''&r2'&rs2'&r2''&->&->&?&?).
    apply ref_disjoint_app. by constructor.
Qed.
Lemma ref_disjoint_snoc r1 r2 rs1 rs2 :
  r1 ++ [rs1] ## r2 ++ [rs2] ↔
    rs1 ## rs2 ∨ (r1 ## r2 ∧ freeze true rs1 = freeze true rs2).
Proof.
  split.
  * rewrite ref_disjoint_alt;
      intros (r1'&rs1'&r1''&r2'&rs2'&r2''&Hr1&Hr2&?&Hr'').
    destruct r1'' as [|rs1'' r1'' _] using @rev_ind;
      destruct r2'' as [|rs2'' r2'' _] using @rev_ind.
    + simplify_list_eq. by left.
    + rewrite fmap_app in Hr''. by discriminate_list_equality.
    + rewrite fmap_app in Hr''. by discriminate_list_equality.
    + simplify_list_eq.
      right; split. by apply ref_disjoint_app; constructor. done.
  * intros [?|[? Hr]].
    + rewrite ref_disjoint_alt. naive_solver.
    + by apply ref_disjoint_here_app_1; f_equal'.
Qed.
Lemma ref_disjoint_singleton rs1 rs2 : [rs1] ## [rs2] ↔ rs1 ## rs2.
Proof.
  rewrite ref_disjoint_alt. split.
  * by intros ([]&?&?&[]&?&?&?&?&?&?);
      simplify_list_eq; try discriminate_list_equality.
  * intros. by eexists [], rs1, [], [], rs2, [].
Qed.
Lemma ref_disjoint_nil_inv_l r : ¬[] ## r.
Proof.
  rewrite ref_disjoint_alt. intros (?&?&?&?&?&?&?&_);
    simplify_list_eq; discriminate_list_equality.
Qed.
Lemma ref_disjoint_nil_inv_r r : ¬r ## [].
Proof. intros ?. by apply (ref_disjoint_nil_inv_l r). Qed.
#[global] Instance: Irreflexive (@disjoint (ref_seg K) _).
Proof. by inversion 1. Qed.
Lemma ref_disjoint_app_inv_l r1 r2 : ¬r1 ++ r2 ## r2.
Proof.
  rewrite ref_disjoint_alt. intros (r1'&rs1&r1''&r2'&rs2&r2''&Hr&->&Hrs&Hr').
  simplify_list_eq. by destruct (irreflexivity (##) rs1).
Qed.
Lemma ref_disjoint_app_inv_r r1 r2 : ¬r2 ## r1 ++ r2.
Proof. intros ?. by destruct (ref_disjoint_app_inv_l r1 r2). Qed.
#[global] Instance: Irreflexive (@disjoint (ref K) _).
Proof. intros r ?. by destruct (ref_disjoint_app_inv_l [] r). Qed.
Lemma ref_disjoint_here_app_2 r1 r2 r : r1 ++ r ## r2 ++ r → r1 ## r2.
Proof.
  induction r as [|rs r IH] using rev_ind; [by rewrite !(right_id_L [] (++)) |].
  rewrite !(assoc_L (++)), ref_disjoint_snoc. intros [?|[??]]; auto.
  by destruct (irreflexivity (##) rs).
Qed.
Lemma ref_disjoint_here_app r1 r2 r : r1 ## r2 ↔ r1 ++ r ## r2 ++ r.
Proof.
  split; eauto using ref_disjoint_here_app_2.
  intros. by apply ref_disjoint_here_app_1.
Qed.
Lemma ref_seg_disjoint_le rs1 rs2 rs3 rs4 :
  rs1 ## rs2 → rs1 ⊆ rs3 → rs2 ⊆ rs4 → rs3 ## rs4.
Proof. by destruct 1; do 2 inversion 1; constructor. Qed.
Lemma ref_disjoint_le r1 r2 r3 r4 : r1 ## r2 → r1 ⊆* r3 → r2 ⊆* r4 → r3 ## r4.
Proof.
  rewrite ref_disjoint_alt; intros (r1'&rs1&r1''&r2'&rs2&r2''&->&->&?&?) ??.
  decompose_Forall_hyps.
  apply ref_disjoint_app, ref_disjoint_here; eauto using ref_seg_disjoint_le.
  transitivity (freeze true <$> r1''); auto using ref_freeze_le, eq_sym.
  transitivity (freeze true <$> r2''); auto using ref_freeze_le, eq_sym.
Qed.
Lemma ref_seg_disjoint_ge rs1 rs2 rs3 rs4 :
  rs3 ## rs4 → rs1 ⊆ rs3 → rs2 ⊆ rs4 → rs1 ## rs2.
Proof. by destruct 1; do 2 inversion 1; constructor. Qed.
Lemma ref_disjoint_ge r1 r2 r3 r4 : r3 ## r4 → r1 ⊆* r3 → r2 ⊆* r4 → r1 ## r2.
Proof.
  rewrite ref_disjoint_alt; intros (r3'&rs3&r3''&r4'&rs4&r4''&->&->&?&?) ??.
  decompose_Forall_hyps.
  apply ref_disjoint_app, ref_disjoint_here; eauto using ref_seg_disjoint_ge.
  transitivity (freeze true <$> r3''); auto using ref_freeze_le, eq_sym.
  transitivity (freeze true <$> r4''); auto using ref_freeze_le, eq_sym.
Qed.

#[global] Instance ref_seg_disjoint_dec rs1 rs2 : Decision (rs1 ## rs2).
Proof.
 refine
  match rs1,rs2 with
  | RArray i τ1 n1, RArray j τ2 n2 =>
     cast_if (decide (n1 = n2 ∧ τ1 = τ2 ∧ i ≠ j))
  | RStruct i t1, RStruct j t2 => cast_if (decide (t1 = t2 ∧ i ≠ j))
  | _, _ => right _
  end; abstract first [intuition; subst; by constructor|inversion 1; intuition].
Defined.
Inductive ref_disjoint_rev: ref K → ref K → Prop :=
  | ref_disjoint_rev_here rs1 rs2 r1' r2' :
     rs1 ## rs2 → ref_disjoint_rev (rs1 :: r1') (rs2 :: r2')
  | ref_disjoint_rev_cons rs1 rs2 r1 r2 :
     freeze true rs1 = freeze true rs2 →
     ref_disjoint_rev r1 r2 → ref_disjoint_rev (rs1 :: r1) (rs2 :: r2).
#[global] Instance ref_disjoint_rev_dec:∀ r1 r2, Decision (ref_disjoint_rev r1 r2).
Proof.
 refine (
  fix go r1 r2 :=
  match r1, r2 return Decision (ref_disjoint_rev r1 r2) with
  | rs1 :: r1, rs2 :: r2 =>
     if decide (rs1 ## rs2) then left _
     else cast_if_and (decide (freeze true rs1 = freeze true rs2)) (go r1 r2)
  | _, _ => right _
  end); clear go; try (subst; constructor; by auto); try (inversion 1; auto).
Defined.
Lemma ref_disjoint_rev_correct_1 r1 r2 :
  ref_disjoint_rev r1 r2 → reverse r1 ## reverse r2.
Proof.
  induction 1 as [|rs1 r1 r2]; rewrite !reverse_cons.
  * by apply ref_disjoint_app, ref_disjoint_singleton.
  * by apply ref_disjoint_here_app_1; f_equal'.
Qed.
Lemma ref_disjoint_rev_correct_2 r1 r2 :
  r1 ## r2 → ref_disjoint_rev (reverse r1) (reverse r2).
Proof.
  rewrite ref_disjoint_alt. intros (r1'&rs1'&r1''&r2'&rs2'&r2''&->&->&?&Hr'').
  rewrite !reverse_app, !reverse_singleton, <-!(assoc_L (++)); simpl.
  apply (f_equal reverse) in Hr''. rewrite <-!fmap_reverse in Hr''.
  revert Hr''. generalize (reverse r2''); clear r2''.
  induction (reverse r1''); intros [|??] ?; simplify_equality';
    constructor; by auto.
Qed.
Lemma ref_disjoint_rev_correct r1 r2 :
  r1 ## r2 ↔ ref_disjoint_rev (reverse r1) (reverse r2).
Proof.
  split; [apply ref_disjoint_rev_correct_2|].
  intros. rewrite <-(reverse_involutive r1), <-(reverse_involutive r2).
  by apply ref_disjoint_rev_correct_1.
Qed.
#[global] Instance ref_disjoint_dec r1 r2 : Decision (r1 ## r2).
Proof.
  refine (cast_if (decide (ref_disjoint_rev (reverse r1) (reverse r2))));
   by rewrite ref_disjoint_rev_correct.
Defined.

Lemma RArray_disjoint_snoc r1 r2 i1 i2 τ n :
  r1 ++ [RArray i1 τ n] ## r2 ++ [RArray i2 τ n] ↔ i1 ≠ i2 ∨ r1 ## r2.
Proof.
  rewrite ref_disjoint_snoc. split.
  * intros [Harr|[??]]; [inversion Harr|]; tauto.
  * destruct (decide (i1 = i2)); intros [?|?];
      simplify_equality; eauto using RArray_disjoint.
Qed.
Lemma RStruct_disjoint_snoc r1 r2 i1 i2 t :
  r1 ++ [RStruct i1 t] ## r2 ++ [RStruct i2 t] ↔ i1 ≠ i2 ∨ r1 ## r2.
Proof.
  rewrite ref_disjoint_snoc. split.
  * intros [Hstruct|[??]]; [inversion Hstruct|]; tauto.
  * destruct (decide (i1 = i2)); intros [?|?];
      simplify_equality; eauto using RStruct_disjoint.
Qed.
Lemma RUnion_disjoint_snoc r1 r2 i1 β1 i2 β2 t :
  r1 ++ [RUnion i1 t β1] ## r2 ++ [RUnion i2 t β2] ↔ i1 = i2 ∧ r1 ## r2.
Proof.
  rewrite ref_disjoint_snoc. split.
  * by intros [Hu|[??]]; [inversion Hu|]; simplify_equality.
  * destruct β1, β2; intros [<- ?]; auto.
Qed.
Lemma ref_set_offset_disjoint r i :
  ref_set_offset i r ## r ∨ ref_set_offset i r = r.
Proof.
  destruct r as [|[j n| |]]; simpl; auto.
  destruct (decide (i = j)) as [->|]; auto. by left; repeat constructor.
Qed.

Lemma ref_seg_object_offset_weaken Γ1 Γ2 rs τ σ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊢ rs : τ ↣ σ → Γ1 ⊆ Γ2 →
  ref_seg_object_offset Γ1 rs = ref_seg_object_offset Γ2 rs.
Proof.
  destruct 3; intros;
    simplify_option_eq by eauto using lookup_compound_weaken;
    eauto using bit_size_of_weaken, TArray_valid_inv_type,
    bit_offset_of_weaken, env_valid_lookup with f_equal.
Qed.
Lemma ref_object_offset_weaken Γ1 Γ2 r τ σ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊢ r : τ ↣ σ → Γ1 ⊆ Γ2 →
  ref_object_offset Γ1 r = ref_object_offset Γ2 r.
Proof.
  unfold ref_object_offset.
  induction 3 using @ref_typed_ind; intros; f_equal';
    eauto using ref_seg_object_offset_weaken, ref_typed_type_valid.
Qed.
Lemma ref_object_offset_app Γ r1 r2 :
  ref_object_offset Γ (r1 ++ r2)
  = ref_object_offset Γ r1 + ref_object_offset Γ r2.
Proof. unfold ref_object_offset. induction r1; csimpl; lia. Qed.
Lemma ref_object_offset_singleton Γ rs :
  ref_object_offset Γ [rs] = ref_seg_object_offset Γ rs.
Proof. unfold ref_object_offset; simpl; lia. Qed.
Lemma ref_object_offset_set_offset Γ τ r σ i :
  Γ ⊢ r : τ ↣ σ → i < ref_size r →
  ref_object_offset Γ (ref_set_offset i r) + ref_offset r * bit_size_of Γ σ
  = ref_object_offset Γ r + i * bit_size_of Γ σ.
Proof. unfold ref_object_offset. destruct 1 as [|????? []], i; simpl; lia. Qed.
Lemma ref_object_offset_set_offset_0 Γ τ r σ i :
  Γ ⊢ r : τ ↣ σ → i < ref_size r → ref_offset r = 0 →
  ref_object_offset Γ (ref_set_offset i r)
  = ref_object_offset Γ r + i * bit_size_of Γ σ.
Proof.
  intros ?? Hr. erewrite <-ref_object_offset_set_offset, Hr by eauto. lia.
Qed.
Lemma ref_seg_object_offset_size Γ τ rs σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ →
  ref_seg_object_offset Γ rs +
    (ref_seg_size rs - ref_seg_offset rs) * bit_size_of Γ σ ≤ bit_size_of Γ τ.
Proof.
  destruct 2; simplify_option_eq.
  * rewrite bit_size_of_array. rewrite <-Nat.mul_add_distr_r.
    apply Nat.mul_le_mono_r; lia.
  * rewrite Nat.add_0_r; eauto using bit_offset_of_size.
  * rewrite Nat.add_0_r; eauto using bit_size_of_union_lookup.
Qed.
Lemma ref_seg_object_offset_size' Γ τ rs σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ →
  ref_seg_object_offset Γ rs + bit_size_of Γ σ ≤ bit_size_of Γ τ.
Proof.
  intros. feed pose proof (ref_seg_object_offset_size Γ τ rs σ); auto.
  feed pose proof (ref_seg_typed_size Γ τ rs σ); auto.
  cut (1 * bit_size_of Γ σ ≤
    (ref_seg_size rs - ref_seg_offset rs) * bit_size_of Γ σ); [lia|].
  apply Nat.mul_le_mono_r; lia.
Qed.
Lemma ref_object_offset_size Γ τ r σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ →
  ref_object_offset Γ r +
    (ref_size r - ref_offset r) * bit_size_of Γ σ ≤ bit_size_of Γ τ.
Proof.
  unfold ref_object_offset.
  induction 2 as [|r rs τ1 τ2 τ3] using @ref_typed_ind; csimpl; [lia|].
  feed pose proof (ref_seg_object_offset_size Γ τ2 rs τ3); auto.
  feed pose proof (ref_typed_size Γ τ1 r τ2); auto.
  cut (1 * bit_size_of Γ τ2 ≤
    (ref_size r - ref_offset r) * bit_size_of Γ τ2); [lia|].
  apply Nat.mul_le_mono_r; lia.
Qed.
Lemma ref_object_offset_size' Γ τ r σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ →
  ref_object_offset Γ r + bit_size_of Γ σ ≤ bit_size_of Γ τ.
Proof.
  intros. feed pose proof (ref_object_offset_size Γ τ r σ); auto.
  feed pose proof (ref_typed_size Γ τ r σ); auto.
  cut (1 * bit_size_of Γ σ ≤
    (ref_size r - ref_offset r) * bit_size_of Γ σ); [lia|].
  apply Nat.mul_le_mono_r; lia.
Qed.
Lemma ref_seg_disjoint_object_offset Γ τ rs1 rs2 σ1 σ2 :
  ✓ Γ → rs1 ## rs2 → Γ ⊢ rs1 : τ ↣ σ1 → Γ ⊢ rs2 : τ ↣ σ2 →
  ref_seg_object_offset Γ rs1 + bit_size_of Γ σ1 ≤ ref_seg_object_offset Γ rs2 ∨
  ref_seg_object_offset Γ rs2 + bit_size_of Γ σ2 ≤ ref_seg_object_offset Γ rs1.
Proof.
  destruct 2 as [i j n|i j]; do 2 inversion 1; simplify_option_eq.
  * assert (i < j ∨ j < i) as [|] by lia; [left|right];
      rewrite <-Nat.mul_succ_l; apply Nat.mul_le_mono_r; lia.
  * assert (i < j ∨ j < i) as [|] by lia; eauto using bit_offset_of_lt.
Qed.
Lemma ref_disjoint_object_offset Γ τ r1 r2 σ1 σ2 :
  ✓ Γ → r1 ## r2 → Γ ⊢ r1 : τ ↣ σ1 → Γ ⊢ r2 : τ ↣ σ2 →
  ref_object_offset Γ r1 + bit_size_of Γ σ1 ≤ ref_object_offset Γ r2 ∨
  ref_object_offset Γ r2 + bit_size_of Γ σ2 ≤ ref_object_offset Γ r1.
Proof.
  rewrite ref_disjoint_alt; intros ? (r1''&rs1&r1'&r2''&rs2&r2'&->&->&?&Hr').
  repeat setoid_rewrite ref_typed_app; setoid_rewrite ref_typed_singleton.
  intros (σ1'&(τ'&?&?)&?) (σ2'&(τ''&?&?)&?).
  assert (Γ ⊢ r2' : τ ↣ τ'); simplify_type_equality.
  { apply ref_typed_le with (freeze true <$> r2'); auto using ref_freeze_le_l.
    rewrite <-Hr'. eauto using ref_typed_ge, ref_freeze_le_l. }
  rewrite !ref_object_offset_app, !ref_object_offset_singleton,
    <-(ref_object_offset_freeze _ true r1'), Hr', !ref_object_offset_freeze.
  destruct (ref_seg_disjoint_object_offset Γ τ'' rs1 rs2 σ1' σ2'); auto.
  * efeed pose proof (ref_object_offset_size' Γ σ1'); eauto. lia.
  * efeed pose proof (ref_object_offset_size' Γ σ2'); eauto; lia.
Qed.
Lemma ref_typed_align_of Γ τ rs σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ rs : τ ↣ σ → (align_of Γ σ | align_of Γ τ).
Proof. destruct 3; simpl; eauto using align_of_compound, align_of_array. Qed.
Lemma ref_typed_bit_align_of Γ τ rs σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ rs : τ ↣ σ → (bit_align_of Γ σ | bit_align_of Γ τ).
Proof. eauto using Nat.mul_divide_mono_r, ref_typed_align_of. Qed.
Lemma bit_align_of_ref_seg_object_offset Γ τ rs σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ rs : τ ↣ σ →
  (bit_align_of Γ σ | ref_seg_object_offset Γ rs).
Proof.
  destruct 3; simplify_option_eq; eauto using Nat.divide_0_r,
    bit_align_of_offset_of, Nat.divide_mul_r, bit_align_of_divide,
    TArray_valid_inv_type, env_valid_lookup.
Qed.
Lemma bit_align_of_ref_object_offset Γ τ r σ :
  ✓ Γ → ✓{Γ} τ → Γ ⊢ r : τ ↣ σ → (bit_align_of Γ σ | ref_object_offset Γ r).
Proof.
  unfold ref_object_offset.
  induction 3 using @ref_typed_ind; csimpl; auto using Nat.divide_0_r.
  apply Nat.divide_add_r; eauto using bit_align_of_ref_seg_object_offset,
    ref_typed_type_valid, Nat.divide_trans, ref_typed_bit_align_of.
Qed.
End references.
