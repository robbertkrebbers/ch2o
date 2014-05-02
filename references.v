(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export abstract_integers type_environment.
Local Open Scope ctype_scope.

(** * References *)
Inductive ref_seg (Ti : Set) :=
  | RArray : nat → type Ti → nat → ref_seg Ti
  | RStruct : nat → tag → ref_seg Ti
  | RUnion : nat → tag → bool → ref_seg Ti.
Notation ref Ti := (list (ref_seg Ti)).
Arguments RArray {_} _ _ _.
Arguments RStruct {_} _ _.
Arguments RUnion {_} _ _ _.

Instance ref_seg_eq_dec {Ti : Set} `{∀ τi1 τi2 : Ti, Decision (τi1 = τi2)}
  (r1 r2 : ref_seg Ti) : Decision (r1 = r2).
Proof.
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
(*
Instance ref_seg_lexico : Lexico ref_seg := λ rs1 rs2,
  match rs1, rs2 with
  | RArray i1 n1, RArray i2 n2 => lexico (i1,n1) (i2,n2)
  | RArray _ _, (RStruct _ _ | RUnion _ _ _) => True
  | RStruct i1 s1, RStruct i2 s2 => lexico (i1,s1) (i2,s2)
  | RStruct _ _, RUnion _ _ _ => True
  | RUnion i1 s1 β1, RUnion i2 s2 β2 => lexico (i1,s1,β1) (i2,s2,β2)
  | _, _ => False
  end.
Instance ref_seg_lexico_po: StrictOrder (@lexico ref_seg _).
Proof.
  unfold lexico, ref_seg_lexico. repeat split.
  * intros [??|??|???] ?; simplify_order.
  * by intros [] [] [] ??; simplify_order.
Qed.
Instance ref_seg_trichotomy: TrichotomyT (@lexico ref_seg _).
Proof.
 red; refine (λ rs1 rs2,
  match rs1, rs2 with
  | RArray i1 n1, RArray i2 n2 =>
     cast_trichotomy (trichotomyT lexico (i1,n1) (i2,n2))
  | RArray _ _, (RStruct _ _ | RUnion _ _ _) => inleft (left _)
  | RStruct i1 s1, RStruct i2 s2 =>
     cast_trichotomy (trichotomyT lexico (i1,s1) (i2,s2))
  | RStruct _ _, RUnion _ _ _ => inleft (left _)
  | RUnion i1 s1 β1, RUnion i2 s2 β2 =>
     cast_trichotomy (trichotomyT lexico (i1,s1,β1) (i2,s2,β2))
  | _, _ => inright _
  end);
  abstract (repeat (done || constructor || congruence || by inversion 1)).
Defined.
*)

Inductive ref_seg_typed' `{PtrEnv Ti} (Γ : env Ti) :
     ref_seg Ti → type Ti → type Ti → Prop :=
  | RArray_typed τ i n :
     i < n → ref_seg_typed' Γ (RArray i τ n) (τ.[n]) τ
  | RStruct_typed s i τs τ :
     Γ !! s = Some τs → τs !! i = Some τ →
     ref_seg_typed' Γ (RStruct i s) (structT s) τ
  | RUnion_typed s i β τs τ :
     Γ !! s = Some τs → τs !! i = Some τ →
     ref_seg_typed' Γ (RUnion i s β) (unionT s) τ.
Instance ref_seg_typed `{PtrEnv Ti} :
  PathTyped (env Ti) (type Ti) (ref_seg Ti) := ref_seg_typed'.
Instance subtype `{PtrEnv Ti} : SubsetEqE (env Ti) (type Ti) :=
  λ Γ τ1 τ2, ∃ r : ref Ti, Γ ⊢ r : τ2 ↣ τ1.
Instance ref_seg_lookup {Ti : Set} `{∀ τi1 τi2 : Ti, Decision (τi1 = τi2)} :
    LookupE (env Ti) (ref_seg Ti) (type Ti) (type Ti) := λ Γ rs τ,
  match rs, τ with
  | RArray i τ' n', τ.[n] =>
     guard (τ = τ'); guard (n = n'); guard (i < n); Some τ
  | RStruct i s', structT s => guard (s = s'); Γ !! s ≫= (!! i)
  | RUnion i s' _, unionT s => guard (s = s'); Γ !! s ≫= (!! i)
  | _, _ => None
  end.

Definition ref_seg_object_type {Ti} (rs : ref_seg Ti) : type Ti :=
  match rs with
  | RArray _ τ n => τ.[n]
  | RStruct _ s => structT s
  | RUnion _ s _ => unionT s
  end.
Definition ref_object_type {Ti} (τ : type Ti) (r : ref Ti) : type Ti :=
  match reverse r with [] => τ | rs :: _ => ref_seg_object_type rs end.
Definition ref_seg_type {Ti} (Γ : env Ti) (rs : ref_seg Ti) : type Ti :=
  match rs with
  | RArray _ τ n => τ
  | RStruct i s => from_option voidT (Γ !! s ≫= (!! i))
  | RUnion i s _ => from_option voidT (Γ !! s ≫= (!! i))
  end.

Class Freeze A := freeze: bool → A → A.
Arguments freeze {_ _} _ !_ /.
Definition frozen `{Freeze A} (x : A) : Prop := freeze true x = x.

Instance ref_seg_freeze {Ti} : Freeze (ref_seg Ti) := λ β rs,
  match rs with
  | RArray i τ n => RArray i τ n
  | RStruct i s => RStruct i s
  | RUnion i s _ => RUnion i s β
  end.

Definition ref_seg_set_offset {Ti} (i : nat) (rs : ref_seg Ti) : ref_seg Ti :=
  match rs with RArray _ τ n => RArray i τ n | _ => rs end.
Arguments ref_seg_set_offset _ _ !_ /.
Definition ref_set_offset {Ti} (i : nat) (r : ref Ti) : ref Ti :=
  match r with rs :: r => ref_seg_set_offset i rs :: r | _ => r end.
Arguments ref_set_offset _ _ !_ /.
Notation ref_base := (ref_set_offset 0).

Definition ref_seg_offset {Ti} (rs : ref_seg Ti) : nat :=
  match rs with RArray i _ _ => i | _ => 0 end.
Arguments ref_seg_offset _ !_ /.
Definition ref_offset {Ti} (r : ref Ti) : nat :=
  match r with rs :: r => ref_seg_offset rs | _ => 0 end.
Arguments ref_offset _ !_ /.
Definition ref_seg_size {Ti} (rs : ref_seg Ti) : nat :=
  match rs with RArray _ _ n => n | _ => 1 end.
Arguments ref_seg_size _ !_ /.
Definition ref_size {Ti} (r : ref Ti) : nat :=
  match r with rs :: _ => ref_seg_size rs | _ => 1 end.
Arguments ref_size _ !_ /.

Inductive ref_seg_disjoint {Ti} : Disjoint (ref_seg Ti) :=
  | RArray_disjoint i1 i2 τ n : i1 ≠ i2 → @RArray Ti i1 τ n ⊥ RArray i2 τ n
  | RStruct_disjoint i1 i2 s : i1 ≠ i2 → @RStruct Ti i1 s ⊥ RStruct i2 s.
Existing Instance ref_seg_disjoint.
Inductive ref_disjoint {Ti : Set} : Disjoint (ref Ti) :=
  | ref_disjoint_here rs1 rs2 (r1 r2 : ref Ti) :
     freeze true <$> r1 = freeze true <$> r2 →
     rs1 ⊥ rs2 → rs1 :: r1 ⊥ rs2 :: r2
  | ref_disjoint_cons_l rs1 (r1 r2 : ref Ti) : r1 ⊥ r2 → rs1 :: r1 ⊥ r2
  | ref_disjoint_cons_r rs2 (r1 r2 : ref Ti): r1 ⊥ r2 → r1 ⊥ rs2 :: r2.
Existing Instance ref_disjoint.

Definition ref_seg_object_offset `{IntEnv Ti, PtrEnv Ti}
    (Γ : env Ti) (rs : ref_seg Ti) : nat :=
  match rs with
  | RArray i τ _ => i * bit_size_of Γ τ
  | RStruct i s => default 0 (Γ !! s) $ λ τs, field_bit_offset Γ τs i
  | RUnion i _ _ => 0
  end.
Definition ref_object_offset `{IntEnv Ti, PtrEnv Ti} (Γ : env Ti)
  (r : ref Ti) : nat := sum_list (ref_seg_object_offset Γ <$> r).

Definition ref_seg_object_offset_right `{IntEnv Ti, PtrEnv Ti}
    (Γ : env Ti) (rs : ref_seg Ti) : nat :=
  bit_size_of Γ (ref_seg_object_type rs)
  - ref_seg_object_offset Γ rs - bit_size_of Γ (ref_seg_type Γ rs).
Arguments ref_seg_object_offset_right _ _ _ _ !_ /.
Definition ref_object_offset_right `{IntEnv Ti, PtrEnv Ti} (Γ : env Ti)
  (r : ref Ti) : nat := sum_list (ref_seg_object_offset_right Γ <$> r).

Section references.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types τ : type Ti.
Implicit Types rs : ref_seg Ti.
Implicit Types r : ref Ti.

Lemma ref_seg_typed_type_valid Γ rs τ σ :
  ✓ Γ → Γ ⊢ rs : τ ↣ σ → ✓{Γ} τ → ✓{Γ} σ.
Proof.
  intro. destruct 1; intros Hτ; apply (type_valid_inv Γ _ _ Hτ);
    eauto using env_valid_lookup_lookup.
Qed.
Lemma ref_typed_type_valid Γ r τ σ : ✓ Γ → Γ ⊢ r : τ ↣ σ → ✓{Γ} τ → ✓{Γ} σ.
Proof. intro. induction 1; eauto using ref_seg_typed_type_valid. Qed.
Global Instance: PathTypeCheckSpec (env Ti) (type Ti) (ref_seg Ti).
Proof.
  split.
  * intros Γ rs τ σ. split; [|by destruct 1; simplify_option_equality].
    destruct rs, τ as [| | |[]]; intros;
      simplify_option_equality; econstructor; eauto.
  * by destruct 1; inversion 1.
Qed.
Lemma ref_seg_typed_weaken Γ1 Γ2 rs τ σ :
  Γ1 ⊢ rs : τ ↣ σ → Γ1 ⊆ Γ2 → Γ2 ⊢ rs : τ ↣ σ.
Proof. destruct 1; econstructor; eauto using lookup_weaken. Qed.
Lemma ref_typed_weaken Γ1 Γ2 r τ σ : Γ1 ⊢ r : τ ↣ σ → Γ1 ⊆ Γ2 → Γ2 ⊢ r : τ ↣ σ.
Proof.
  intros Hr ?. induction Hr using @list_typed_ind;
    econstructor; eauto using ref_seg_typed_weaken.
Qed.
Lemma ref_lookup_weaken Γ1 Γ2 r τ σ :
  τ !!{Γ1} r = Some σ → Γ1 ⊆ Γ2 → τ !!{Γ2} r = Some σ.
Proof. rewrite !path_type_check_correct. by apply ref_typed_weaken. Qed.
Lemma ref_seg_typed_inv_void Γ rs σ : ¬Γ ⊢ rs : voidT ↣ σ.
Proof. inversion 1. Qed.
Lemma ref_typed_inv_void Γ r σ : Γ ⊢ r : voidT ↣ σ → σ = voidT ∧ r = [].
Proof.
  destruct r as [|rs r] using rev_ind; [by rewrite list_typed_nil|].
  rewrite list_typed_snoc. intros (?&Hrs&_).
  edestruct ref_seg_typed_inv_void; eauto.
Qed.
Lemma ref_seg_typed_inv_base Γ τb rs σ : ¬Γ ⊢ rs : baseT τb ↣ σ.
Proof. inversion 1. Qed.
Lemma ref_typed_inv_base Γ τb r σ :
  Γ ⊢ r : baseT τb ↣ σ → σ = baseT τb ∧ r = [].
Proof.
  destruct r as [|rs r] using rev_ind; [by rewrite list_typed_nil|].
  rewrite list_typed_snoc; intros (?&Hrs&_).
  edestruct ref_seg_typed_inv_base; eauto.
Qed.
Lemma ref_seg_object_type_correct Γ rs τ σ :
  Γ ⊢ rs : τ ↣ σ → ref_seg_object_type rs = τ.
Proof. by destruct 1. Qed.
Lemma ref_object_type_correct Γ r τ σ : Γ ⊢ r : τ ↣ σ → ref_object_type σ r = τ.
Proof.
  destruct r as [|rs r _] using rev_ind; [by rewrite list_typed_nil|].
  unfold ref_object_type. rewrite list_typed_snoc, reverse_snoc.
  intros (?&?&?); eauto using ref_seg_object_type_correct.
Qed.
Lemma ref_seg_typed_unique Γ rs τ1 σ1 τ2 σ2 :
  Γ ⊢ rs : τ1 ↣ σ1 → Γ ⊢ rs : τ2 ↣ σ2 → τ1 = τ2 ∧ σ1 = σ2.
Proof. by destruct 1; inversion_clear 1; simplify_equality. Qed.
Lemma ref_typed_unique Γ r τ1 σ1 τ2 σ2 :
  Γ ⊢ r : τ1 ↣ σ1 → Γ ⊢ r : τ2 ↣ σ2 → r ≠ [] → τ1 = τ2 ∧ σ1 = σ2.
Proof.
  destruct r as [|rs r _] using rev_ind; [done|]. rewrite !list_typed_snoc.
  intros (τ1'&?&?) (τ2'&?&?) _.
  destruct (ref_seg_typed_unique Γ rs τ1 τ1' τ2 τ2') as [-> ->]; auto.
  by simplify_type_equality.
Qed.
Lemma ref_typed_size Γ τ r σ : Γ ⊢ r : τ ↣ σ → ref_offset r < ref_size r.
Proof. destruct 1 as [|????? []]; auto with lia. Qed.
Lemma ref_set_offset_length r i : length (ref_set_offset i r) = length r.
Proof. by destruct r. Qed.
Lemma ref_size_set_offset i r : ref_size (ref_set_offset i r) = ref_size r.
Proof. by destruct r as [|[]]. Qed.
Lemma ref_offset_set_offset r i :
  i < ref_size r → ref_offset (ref_set_offset i r) = i.
Proof. destruct r as [|[]]; simpl in *; auto with lia. Qed.
Lemma ref_offset_base_nil r : ref_base r = [] → ref_offset r = 0.
Proof. by destruct r. Qed.
Lemma ref_set_offset_typed Γ τ r σ i :
  i < ref_size r → Γ ⊢ r : τ ↣ σ → Γ ⊢ ref_set_offset i r : τ ↣ σ.
Proof.
  destruct 2 as [|r rs ??? [] Hr]; simpl; repeat econstructor; eauto.
Qed.
Lemma ref_set_offset_offset r : ref_set_offset (ref_offset r) r = r.
Proof. by destruct r as [|[]]. Qed.
Lemma ref_set_offset_set_offset r i j :
  ref_set_offset i (ref_set_offset j r) = ref_set_offset i r.
Proof. by destruct r as [|[]]. Qed.
Lemma ref_set_offset_typed_unique Γ τ r σ1 σ2 i :
  Γ ⊢ r : τ ↣ σ1 → Γ ⊢ ref_set_offset i r : τ ↣ σ2 → σ1 = σ2.
Proof.
  destruct r as [|rs r]; simpl; [rewrite !list_typed_nil; congruence|].
  rewrite !list_typed_cons. intros (τ1&?&Hrs1) (τ2&?&Hrs2).
  simplify_type_equality'.
  by destruct Hrs1; inversion Hrs2; simplify_option_equality.
Qed.
Lemma size_of_ref Γ τ r σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ → size_of Γ σ * ref_size r ≤ size_of Γ τ.
Proof.
  intros ?. induction 1 as [|r rs τ1 τ2 τ3 Hrs Hr IH]
    using @list_typed_ind; simpl; [lia|].
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

Global Instance: PreOrder (@subseteqE (env Ti) (type Ti) _ Γ).
Proof.
  intros Γ. repeat split.
  * eexists []. constructor.
  * intros ??? (r1&?) (r2&?). exists (r1 ++ r2). apply list_typed_app; eauto.
Qed.
Lemma ref_typed_subtype Γ τ r1 r2 σ1 σ2 :
  Γ ⊢ r1 : τ ↣ σ1 → Γ ⊢ r2 : τ ↣ σ2 → r1 `suffix_of` r2 → σ2 ⊆{Γ} σ1.
Proof.
  intros Hr1 Hr2 [r ->]. rewrite list_typed_app in Hr2.
  destruct Hr2 as (σ'&?&?); simplify_type_equality. by exists r.
Qed.
Lemma subtype_weaken Γ Σ σ τ : σ ⊆{Γ} τ → Γ ⊆ Σ → σ ⊆{Σ} τ.
Proof. intros (r&?); exists r; eauto using ref_typed_weaken. Qed.

Lemma ref_seg_lookup_freeze Γ β rs : lookupE Γ (freeze β rs) = lookupE Γ rs.
Proof. by destruct rs. Qed.
Lemma ref_seg_typed_freeze Γ β τ rs σ :
  Γ ⊢ freeze β rs : τ ↣ σ ↔ Γ ⊢ rs : τ ↣ σ.
Proof. by rewrite <-!path_type_check_correct, ref_seg_lookup_freeze. Qed.
Lemma ref_seg_typed_freeze_1 Γ β τ rs σ :
  Γ ⊢ freeze β rs : τ ↣ σ → Γ ⊢ rs : τ ↣ σ.
Proof. by rewrite ref_seg_typed_freeze. Qed.
Lemma ref_seg_typed_freeze_2 Γ β τ rs σ :
  Γ ⊢ rs : τ ↣ σ → Γ ⊢ freeze β rs : τ ↣ σ.
Proof. by rewrite ref_seg_typed_freeze. Qed.
Lemma ref_lookup_freeze Γ β r : lookupE Γ (freeze β <$> r) = lookupE Γ r.
Proof.
  induction r as [|rs r IH]; [done|].
  by rewrite fmap_cons, !list_path_lookup_cons, ref_seg_lookup_freeze, IH.
Qed.
Lemma ref_typed_freeze Γ β τ r σ : Γ ⊢ freeze β <$> r : τ ↣ σ ↔ Γ ⊢ r : τ ↣ σ.
Proof. by rewrite <-!path_type_check_correct, ref_lookup_freeze. Qed.
Lemma ref_typed_freeze_1 Γ β τ r σ : Γ ⊢ freeze β <$> r : τ ↣ σ → Γ ⊢ r : τ ↣ σ.
Proof. by rewrite ref_typed_freeze. Qed.
Lemma ref_typed_freeze_2 Γ β τ r σ : Γ ⊢ r : τ ↣ σ → Γ ⊢ freeze β <$> r : τ ↣ σ.
Proof. by rewrite ref_typed_freeze. Qed.

Lemma ref_seg_freeze_freeze β1 β2 rs : freeze β1 (freeze β2 rs) = freeze β1 rs.
Proof. by destruct rs. Qed.
Lemma ref_freeze_freeze β1 β2 r :
  freeze β1 <$> freeze β2 <$> r = freeze β1 <$> r.
Proof.
  rewrite <-list_fmap_compose.
  apply list_fmap_ext; simpl; auto using ref_seg_freeze_freeze.
Qed.
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
Proof. destruct r; simpl; f_equal; auto using ref_seg_set_offset_freeze. Qed.
Lemma ref_seg_size_freeze β rs : ref_seg_size (freeze β rs) = ref_seg_size rs.
Proof. by destruct rs. Qed.
Lemma ref_size_freeze β r : ref_size (freeze β <$> r) = ref_size r.
Proof. destruct r; simpl; auto using ref_seg_size_freeze. Qed.

Lemma ref_disjoint_app_l r1 r1' r2' : r1' ⊥ r2' → r1 ++ r1' ⊥ r2'.
Proof. induction r1; simpl; auto using ref_disjoint_cons_l. Qed.
Lemma ref_disjoint_app_r r2 r1' r2' : r1' ⊥ r2' → r1' ⊥ r2 ++ r2'.
Proof. induction r2; simpl; auto using ref_disjoint_cons_r. Qed.
Lemma ref_disjoint_app r1 r2 r1' r2' : r1' ⊥ r2' → r1 ++ r1' ⊥ r2 ++ r2'.
Proof. auto using ref_disjoint_app_l, ref_disjoint_app_r. Qed.
Lemma ref_disjoint_here_app_1 r1 r2 r1' r2' :
  r1 ⊥ r2 → freeze true <$> r1' = freeze true <$> r2' → r1 ++ r1' ⊥ r2 ++ r2'.
Proof.
  induction 1; simpl; constructor; rewrite ?fmap_app; auto with f_equal.
Qed.
Global Instance: Symmetric (@disjoint (ref_seg Ti) _).
Proof. destruct 1; constructor; auto. Qed.
Global Instance: Symmetric (@disjoint (ref Ti) _).
Proof. induction 1; constructor (by auto). Qed.
Lemma ref_seg_disjoint_freeze_l β rs1 rs2 : freeze β rs1 ⊥ rs2 ↔ rs1 ⊥ rs2.
Proof.
  split; [|by destruct 1; constructor].
  by destruct rs1; inversion_clear 1; constructor.
Qed.
Lemma ref_seg_disjoint_freeze_r β rs1 rs2 : rs1 ⊥ freeze β rs2 ↔ rs1 ⊥ rs2.
Proof. by rewrite !(symmetry_iff (⊥) rs1), ref_seg_disjoint_freeze_l. Qed.
Lemma ref_disjoint_freeze_l β r1 r2 : freeze β <$> r1 ⊥ r2 ↔ r1 ⊥ r2.
Proof.
  split.
  * intros Hr. remember (freeze β <$> r1) as r1' eqn:Hr1'. revert r1 Hr1'.
    induction Hr; intros [|??] ?; simplify_equality.
    + rewrite ref_freeze_freeze in *. constructor; auto.
      eapply ref_seg_disjoint_freeze_l; eauto.
    + constructor (by auto).
    + constructor (by auto).
    + constructor (by auto).
  * induction 1; try constructor (by auto). constructor.
    + by rewrite ref_freeze_freeze.
    + by rewrite ref_seg_disjoint_freeze_l.
Qed.
Lemma ref_disjoint_freeze_r β r1 r2 : r1 ⊥ freeze β <$> r2 ↔ r1 ⊥ r2.
Proof. by rewrite !(symmetry_iff (⊥) r1), ref_disjoint_freeze_l. Qed.
Lemma ref_disjoint_alt r1 r2 :
  r1 ⊥ r2 ↔ ∃ r1' rs1 r1'' r2' rs2 r2'',
    r1 = r1' ++ [rs1] ++ r1'' ∧ r2 = r2' ++ [rs2] ++ r2'' ∧
    rs1 ⊥ rs2 ∧ freeze true <$> r1'' = freeze true <$> r2''.
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
  r1 ++ [rs1] ⊥ r2 ++ [rs2] ↔
    rs1 ⊥ rs2 ∨ (r1 ⊥ r2 ∧ freeze true rs1 = freeze true rs2).
Proof.
  split.
  * rewrite ref_disjoint_alt;
      intros (r1'&rs1'&r1''&r2'&rs2'&r2''&Hr1&Hr2&?&Hr'').
    destruct r1'' as [|rs1'' r1'' _] using @rev_ind;
      destruct r2'' as [|rs2'' r2'' _] using @rev_ind.
    + simplify_list_equality. by left.
    + rewrite fmap_app in Hr''. by simplify_list_equality.
    + rewrite fmap_app in Hr''. by simplify_list_equality.
    + rewrite !(associative_L (++)) in Hr1, Hr2.
      rewrite !fmap_app in Hr''; simplify_list_equality.
      right. split; auto. rewrite <-!(associative_L (++)).
      apply ref_disjoint_app. by constructor.
  * intros [?|[? Hr]].
    + rewrite ref_disjoint_alt. naive_solver.
    + by apply ref_disjoint_here_app_1; simpl; f_equal.
Qed.
Lemma ref_disjoint_singleton rs1 rs2 : [rs1] ⊥ [rs2] ↔ rs1 ⊥ rs2.
Proof.
  rewrite ref_disjoint_alt. split.
  * by intros ([]&?&?&[]&?&?&?&?&?&?); simplify_list_equality.
  * intros. by eexists [], rs1, [], [], rs2, [].
Qed.
Lemma ref_disjoint_nil_inv_l r : ¬[] ⊥ r.
Proof.
  rewrite ref_disjoint_alt. intros (?&?&?&?&?&?&?&_); simplify_list_equality.
Qed.
Lemma ref_disjoint_nil_inv_r r : ¬r ⊥ [].
Proof. intros ?. by apply (ref_disjoint_nil_inv_l r). Qed.
Global Instance: Irreflexive (@disjoint (ref_seg Ti) _).
Proof. by inversion 1. Qed.
Lemma ref_disjoint_app_inv_l r1 r2 : ¬r1 ++ r2 ⊥ r2.
Proof.
  rewrite ref_disjoint_alt. intros (r1'&rs1&r1''&r2'&rs2&r2''&Hr&->&Hrs&Hr').
  destruct (irreflexivity (⊥) rs1). rewrite !(associative_L (++)) in Hr.
  apply app_injective_2 in Hr;
    [|by rewrite <-(fmap_length (freeze true) r1''), Hr', fmap_length].
  by destruct Hr; simplify_list_equality.
Qed.
Lemma ref_disjoint_app_inv_r r1 r2 : ¬r2 ⊥ r1 ++ r2.
Proof. intros ?. by destruct (ref_disjoint_app_inv_l r1 r2). Qed.
Global Instance: Irreflexive (@disjoint (ref Ti) _).
Proof. intros r ?. by destruct (ref_disjoint_app_inv_l [] r). Qed.

Lemma ref_disjoint_here_app_2 r1 r2 r : r1 ++ r ⊥ r2 ++ r → r1 ⊥ r2.
Proof.
  induction r as [|rs r IH] using rev_ind; [by rewrite !(right_id_L [] (++)) |].
  rewrite !(associative_L (++)), ref_disjoint_snoc. intros [?|[??]]; auto.
  by destruct (irreflexivity (⊥) rs).
Qed.
Lemma ref_disjoint_here_app r1 r2 r : r1 ⊥ r2 ↔ r1 ++ r ⊥ r2 ++ r.
Proof.
  split.
  + intros. by apply ref_disjoint_here_app_1.
  + eauto using ref_disjoint_here_app_2.
Qed.
Global Instance ref_seg_disjoint_dec rs1 rs2 : Decision (rs1 ⊥ rs2).
Proof.
 refine
  match rs1,rs2 with
  | RArray i τ1 n1, RArray j τ2 n2 =>
     cast_if (decide (n1 = n2 ∧ τ1 = τ2 ∧ i ≠ j))
  | RStruct i s1, RStruct j s2 => cast_if (decide (s1 = s2 ∧ i ≠ j))
  | _, _ => right _
  end; abstract first [intuition; subst; by constructor|inversion 1; intuition].
Defined.

Inductive ref_disjoint_rev: ref Ti → ref Ti → Prop :=
  | ref_disjoint_rev_here rs1 rs2 r1' r2' :
     rs1 ⊥ rs2 → ref_disjoint_rev (rs1 :: r1') (rs2 :: r2')
  | ref_disjoint_rev_cons rs1 rs2 r1 r2 :
     freeze true rs1 = freeze true rs2 →
     ref_disjoint_rev r1 r2 → ref_disjoint_rev (rs1 :: r1) (rs2 :: r2).
Global Instance ref_disjoint_rev_dec:∀ r1 r2, Decision (ref_disjoint_rev r1 r2).
Proof.
 refine (
  fix go r1 r2 :=
  match r1, r2 return Decision (ref_disjoint_rev r1 r2) with
  | rs1 :: r1, rs2 :: r2 =>
     if decide (rs1 ⊥ rs2) then left _
     else cast_if_and (decide (freeze true rs1 = freeze true rs2)) (go r1 r2)
  | _, _ => right _
  end); clear go;
    abstract first [subst; constructor (by auto) | inversion 1; auto].
Defined.
Lemma ref_disjoint_rev_correct_1 r1 r2 :
  ref_disjoint_rev r1 r2 → reverse r1 ⊥ reverse r2.
Proof.
  induction 1 as [|rs1 r1 r2]; rewrite !reverse_cons.
  * by apply ref_disjoint_app, ref_disjoint_singleton.
  * by apply ref_disjoint_here_app_1; simpl; f_equal.
Qed.
Lemma ref_disjoint_rev_correct_2 r1 r2 :
  r1 ⊥ r2 → ref_disjoint_rev (reverse r1) (reverse r2).
Proof.
  rewrite ref_disjoint_alt. intros (r1'&rs1'&r1''&r2'&rs2'&r2''&->&->&?&Hr'').
  rewrite !reverse_app, !reverse_singleton, <-!(associative_L (++)); simpl.
  apply (f_equal reverse) in Hr''. rewrite <-!fmap_reverse in Hr''.
  revert Hr''. generalize (reverse r2''); clear r2''.
  induction (reverse r1''); intros [|??] ?; simplify_equality';
    constructor (by auto).
Qed.
Lemma ref_disjoint_rev_correct r1 r2 :
  r1 ⊥ r2 ↔ ref_disjoint_rev (reverse r1) (reverse r2).
Proof.
  split; [apply ref_disjoint_rev_correct_2|].
  intros. rewrite <-(reverse_involutive r1), <-(reverse_involutive r2).
  by apply ref_disjoint_rev_correct_1.
Qed.
Global Instance ref_disjoint_dec r1 r2 : Decision (r1 ⊥ r2).
Proof.
  refine (cast_if (decide (ref_disjoint_rev (reverse r1) (reverse r2))));
   by rewrite ref_disjoint_rev_correct.
Qed.

Lemma RArray_disjoint_snoc r1 r2 i1 i2 τ n :
  r1 ++ [RArray i1 τ n] ⊥ r2 ++ [RArray i2 τ n] ↔ i1 ≠ i2 ∨ r1 ⊥ r2.
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
  * intros [Hstruct|[??]]; [inversion Hstruct|]; tauto.
  * destruct (decide (i1 = i2)); intros [?|?];
      simplify_equality; eauto using RStruct_disjoint.
Qed.
Lemma RUnion_disjoint_snoc r1 r2 i1 β1 i2 β2 s :
  r1 ++ [RUnion i1 s β1] ⊥ r2 ++ [RUnion i2 s β2] ↔ i1 = i2 ∧ r1 ⊥ r2.
Proof.
  rewrite ref_disjoint_snoc. split.
  * by intros [Hu|[??]]; [inversion Hu|]; simplify_equality.
  * destruct β1, β2; intros [<- ?]; auto.
Qed.
Lemma ref_set_offset_disjoint r i :
  ref_set_offset i r ⊥ r ∨ ref_set_offset i r = r.
Proof.
  destruct r as [|[j n| |]]; simpl; auto.
  destruct (decide (i = j)) as [->|]; auto. by left; repeat constructor.
Qed.

Lemma ref_seg_object_offset_freeze Γ β rs :
  ref_seg_object_offset Γ (freeze β rs) = ref_seg_object_offset Γ rs.
Proof. by destruct rs. Qed.
Lemma ref_object_offset_freeze Γ β r :
  ref_object_offset Γ (freeze β <$> r) = ref_object_offset Γ r.
Proof.
  unfold ref_object_offset.
  induction r; f_equal'; auto using ref_seg_object_offset_freeze.
Qed.
Lemma ref_object_offset_app Γ r1 r2 :
  ref_object_offset Γ (r1 ++ r2)
  = ref_object_offset Γ r1 + ref_object_offset Γ r2.
Proof. unfold ref_object_offset. induction r1; simpl; lia. Qed.
Lemma ref_object_offset_singleton Γ rs :
  ref_object_offset Γ [rs] = ref_seg_object_offset Γ rs.
Proof. unfold ref_object_offset; simpl; lia. Qed.
Lemma ref_object_offset_right_app Γ r1 r2 :
  ref_object_offset_right Γ (r1 ++ r2)
  = ref_object_offset_right Γ r1 + ref_object_offset_right Γ r2.
Proof. unfold ref_object_offset_right. induction r1; simpl; lia. Qed.
Lemma ref_seg_object_offset_right_freeze Γ β rs :
  ref_seg_object_offset_right Γ (freeze β rs) = ref_seg_object_offset_right Γ rs.
Proof. by destruct rs. Qed.
Lemma ref_object_offset_right_freeze Γ β r :
  ref_object_offset_right Γ (freeze β <$> r) = ref_object_offset_right Γ r.
Proof.
  unfold ref_object_offset_right.
  induction r; f_equal'; auto using ref_seg_object_offset_right_freeze.
Qed.
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
  ref_seg_object_offset Γ rs + bit_size_of Γ σ ≤ bit_size_of Γ τ.
Proof.
  destruct 2; simplify_option_equality.
  * rewrite bit_size_of_array, <-Nat.mul_succ_l. apply Nat.mul_le_mono_r; lia.
  * eauto using field_bit_offset_size.
  * eauto using bit_size_of_union_lookup.
Qed.
Lemma ref_object_offset_size Γ τ r σ :
  ✓ Γ → Γ ⊢ r : τ ↣ σ → ref_object_offset Γ r + bit_size_of Γ σ ≤ bit_size_of Γ τ.
Proof.
  unfold ref_object_offset. induction 2 using @list_typed_ind; simpl; [done|].
  efeed pose proof ref_seg_object_offset_size; eauto; lia.
Qed.
Lemma ref_seg_disjoint_object_offset Γ τ rs1 rs2 σ1 σ2 :
  ✓ Γ → rs1 ⊥ rs2 → Γ ⊢ rs1 : τ ↣ σ1 → Γ ⊢ rs2 : τ ↣ σ2 →
  ref_seg_object_offset Γ rs1 + bit_size_of Γ σ1 ≤ ref_seg_object_offset Γ rs2 ∨
  ref_seg_object_offset Γ rs2 + bit_size_of Γ σ2 ≤ ref_seg_object_offset Γ rs1.
Proof.
  destruct 2 as [i j n|i j]; do 2 inversion 1; simplify_option_equality.
  * assert (i < j ∨ j < i) as [|] by lia; [left|right];
      rewrite <-Nat.mul_succ_l; apply Nat.mul_le_mono_r; lia.
  * assert (i < j ∨ j < i) as [|] by lia; eauto using field_bit_offset_lt.
Qed.
Lemma ref_disjoint_object_offset Γ τ r1 r2 σ1 σ2 :
   ✓ Γ → r1 ⊥ r2 → Γ ⊢ r1 : τ ↣ σ1 → Γ ⊢ r2 : τ ↣ σ2 →
  ref_object_offset Γ r1 + bit_size_of Γ σ1 ≤ ref_object_offset Γ r2 ∨
  ref_object_offset Γ r2 + bit_size_of Γ σ2 ≤ ref_object_offset Γ r1.
Proof.
  rewrite ref_disjoint_alt; intros ? (r1''&rs1&r1'&r2''&rs2&r2'&->&->&?&Hr').
  repeat setoid_rewrite list_typed_app; setoid_rewrite list_typed_singleton.
  intros (σ1'&(τ'&Hτ'&?)&?) (σ2'&(?&?&?)&?); rewrite <-(ref_typed_freeze _ true),
    Hr', ref_typed_freeze in Hτ'; simplify_type_equality.
  rewrite !ref_object_offset_app, !ref_object_offset_singleton,
    <-(ref_object_offset_freeze _ true r1'), Hr', !ref_object_offset_freeze.
  destruct (ref_seg_disjoint_object_offset Γ τ' rs1 rs2 σ1' σ2'); auto.
  * efeed pose proof (ref_object_offset_size Γ σ1'); eauto; lia.
  * efeed pose proof (ref_object_offset_size Γ σ2'); eauto; lia.
Qed.

Lemma ref_disjoint_cases Γ τ r1 r2 σ1 σ2 :
  ✓ Γ → Γ ⊢ r1 : τ ↣ σ1 → freeze true <$> r1 = r1 →
  Γ ⊢ r2 : τ ↣ σ2 → freeze true <$> r2 = r2 →
  (**i 1.) *) (∀ j1 j2, ref_set_offset j1 r1 ⊥ ref_set_offset j2 r2) ∨
  (**i 2.) *) σ1 ⊆{Γ} σ2 ∨
  (**i 3.) *) σ2 ⊆{Γ} σ1 ∨
  (**i 4.) *) ∃ s r1' i1 r2' i2 r', r1 = r1' ++ RUnion i1 s true :: r' ∧
    r2 = r2' ++ RUnion i2 s true :: r' ∧ i1 ≠ i2.
Proof.
  intros HΓ Hr1 Hr1F Hr2 Hr2F. cut (
    (**i 1.) *) (∀ j1 j2, ref_set_offset j1 r1 ⊥ ref_set_offset j2 r2) ∨
    (**i 2.) *) (∃ j r', r1 = r' ++ ref_set_offset j r2) ∨
    (**i 3.) *) (∃ j r', r2 = r' ++ ref_set_offset j r1) ∨
    (**i 4.) *) ∃ s r1' i1 r2' i2 r', r1 = r1' ++ [RUnion i1 s true] ++ r' ∧
      r2 = r2' ++ [RUnion i2 s true] ++ r' ∧ i1 ≠ i2).
  { intros [?|[(j&r'&->)|[(j&r'&->)|(s&r1'&i1&r2'&i2&r'&Hr1'&Hr2'&?)]]].
    * by left.
    * rewrite list_typed_app in Hr1; destruct Hr1 as (σ2'&?&?).
      assert (σ2'=σ2) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
      by right; left; exists r'.
    * rewrite list_typed_app in Hr2; destruct Hr2 as (σ1'&?&?).
      assert (σ1'=σ1) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
      by do 2 right; left; exists r'.
    * do 3 right; naive_solver. }
  revert r1 τ σ1 Hr1 r2 σ2 Hr1F Hr2 Hr2F. assert (∀ τ rs1 r2 σ1 σ2,
    Γ ⊢ rs1 : τ ↣ σ1 → freeze true rs1 = rs1 →
    Γ ⊢ r2 : τ ↣ σ2 → freeze true <$> r2 = r2 →
    (* 1.) *) (∀ j1 j2, ref_set_offset j1 [rs1] ⊥ ref_set_offset j2 r2) ∨
    (* 2.) *) (∃ j r', r2 = r' ++ ref_set_offset j [rs1]) ∨
    (* 3.) *) r2 = [] ∨
    (* 4.) *) ∃ s i1 r2' i2, rs1 = RUnion i1 s true ∧
      r2 = r2' ++ [RUnion i2 s true] ∧ i1 ≠ i2) as aux.
  { intros τ rs1 r2 σ1 σ2 Hrs1 Hrs1F Hr2 Hr2F.
    destruct r2 as [|rs2 r2 _] using rev_ind; [by do 2 right; left|].
    rewrite list_typed_snoc in Hr2; destruct Hr2 as (σ2'&Hrs2&Hr2).
    rewrite fmap_app in Hr2F. destruct Hrs1 as [? i1 n|s i1|s i1 ?];
      inversion Hrs2 as [? i2|? i2|? i2 []]; simplify_list_equality'.
    * by right; left; exists i2 r2.
    * destruct (decide (i1 = i2)) as [->|]; [by right; left; exists 0 r2|].
      left. intros _ ?. destruct r2; simpl; [by repeat constructor|].
      rewrite app_comm_cons. apply ref_disjoint_app_r. by repeat constructor.
    * destruct (decide (i1 = i2)) as [->|]; [by right; left; exists 0 r2|].
      do 3 right. by exists s i1 r2 i2. }
  induction 1 as [τ|r1 rs1 τ τ1 σ1 Hrs1 Hr1 IH]
    using @list_typed_ind; intros r2 σ2 Hr1F Hr2 Hr2F; simplify_equality'.
  { do 2 right; left; exists 0 r2. by rewrite (right_id_L [] (++)). }
  destruct Hr2 as [τ|r2 rs2 τ τ2 σ2 Hrs2 Hr2 _]
    using @list_typed_ind; simplify_equality'.
  { right; left; exists 0 (rs1 :: r1). by rewrite (right_id_L [] (++)). }
  destruct (IH r2 τ2) as
    [Hr|[(j&r'&->)|[(j&r'&->)|(s&r1'&i1&r2'&i2&r'&->&->&?)]]];
    auto; clear IH; simplify_equality'.
  * left; intros j1 j2. apply ref_disjoint_cons_l, ref_disjoint_cons_r.
    by rewrite <-(ref_set_offset_offset r1), <-(ref_set_offset_offset r2).
  * rewrite list_typed_app in Hr1; destruct Hr1 as (τ2'&Hr2'&Hr').
    assert (τ2' = τ2) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
    destruct (ref_set_offset_disjoint r2 j) as [?| ->].
    { left; intros j1 j2. rewrite app_comm_cons.
      by apply ref_disjoint_app_l, ref_disjoint_cons_r. }
    destruct (aux τ2 rs2 (rs1 :: r') σ2 σ1)
      as [Hr|[(j'&r''&Hr'')|[?|(s&i1&r2'&i2&?&Hr2''&?)]]];
      simplify_equality'; auto.
    { econstructor; eauto. }
    { destruct (app_injective_1 (freeze true <$> r') r'
        (freeze true <$> ref_set_offset j r2) (ref_set_offset j r2));
        rewrite ?fmap_length, <-?fmap_app; congruence. }
    + left; intros j1 j2. rewrite app_comm_cons.
      apply (ref_disjoint_here_app _ [_]), symmetry, Hr.
    + right; left; exists j' r''.
      by rewrite app_comm_cons, Hr'', <-(associative_L (++)).
    + do 3 right. eexists s, r2', i2, [], i1, r2.
      by rewrite app_comm_cons, Hr2'', <-(associative_L (++)).
  * rewrite list_typed_app in Hr2; destruct Hr2 as (τ1'&Hr1'&Hr').
    assert (τ1' = τ1) as -> by eauto using ref_set_offset_typed_unique, eq_sym.
    destruct (ref_set_offset_disjoint r1 j) as [?| ->]; simpl.
    { left; intros. rewrite app_comm_cons. by apply (ref_disjoint_app [_]). }
    destruct (aux τ1 rs1 (rs2 :: r') σ1 σ2)
      as [Hr|[(j'&r''&Hr'')|[?|(s&i1&r2'&i2&?&Hr1''&?)]]];
      simplify_equality'; auto.
    { econstructor; eauto. }
    { destruct (app_injective_1 (freeze true <$> r') r'
        (freeze true <$> ref_set_offset j r1) (ref_set_offset j r1));
        rewrite ?fmap_length, <-?fmap_app; congruence. }
    + left; intros j1 j2. rewrite app_comm_cons.
      apply (ref_disjoint_here_app [_]), Hr.
    + do 2 right; left; exists j' r''.
      by rewrite app_comm_cons, Hr'', <-(associative_L (++)).
    + do 3 right; eexists s, [], i1, r2', i2, r1.
      by rewrite app_comm_cons, Hr1'', <-(associative_L (++)).
  * by do 3 right; eexists s, (rs1 :: r1'), i1, (rs2 :: r2'), i2, r'.
Qed.
End references.
