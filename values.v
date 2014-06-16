(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export base_values.
Local Open Scope ctype_scope.

Inductive val (Ti : Set) : Set :=
  | VBase : base_val Ti → val Ti
  | VArray : type Ti → list (val Ti) → val Ti
  | VStruct : tag → list (val Ti) → val Ti
  | VUnion : tag → nat → val Ti → val Ti
  | VUnionAll : tag → list (val Ti) → val Ti.

Delimit Scope base_val with V.
Bind Scope val_scope with val.
Open Scope val_scope.
Arguments VVoid {_}.
Arguments VBase {_} _.
Arguments VArray {_} _ _%V.
Arguments VStruct {_} _ _%V.
Arguments VUnion {_} _ _ _%V.
Arguments VUnionAll  {_} _ _%V.

Notation "'voidV'" := (VBase voidV) : val_scope.
Notation "'indetV' τ" := (VBase (indetV τ)) (at level 10) : val_scope.
Notation "'intV{' τi } x" := (VBase (intV{τi} x))
  (at level 10, format "intV{ τi }  x") : val_scope.
Notation "'ptrV' p" := (VBase (ptrV p)) (at level 10) : val_scope.
Notation "'byteV' bs" := (VBase (byteV bs)) (at level 10) : val_scope.

Instance: Injective (=) (=) (@VBase Ti).
Proof. by injection 1. Qed.
Instance: Injective2 (=) (=) (=) (@VArray Ti).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VStruct Ti s).
Proof. by injection 1. Qed.
Instance: Injective2 (=) (=) (=) (@VUnion Ti s).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VUnionAll Ti s).
Proof. by injection 1. Qed.

Definition maybe_VBase {Ti} (v : val Ti) : option (base_val Ti) :=
  match v with VBase vb => Some vb | _ => None end.
Instance val_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)} :
  ∀ v1 v2 : val Ti, Decision (v1 = v2).
Proof.
 refine (
  fix go v1 v2 : Decision (v1 = v2) :=
  match v1, v2 with
  | VBase vb1, VBase vb2 => cast_if (decide_rel (=) vb1 vb2)
  | VArray τ1 vs1, VArray τ2 vs2 =>
     cast_if_and (decide_rel (=) τ1 τ2) (decide_rel (=) vs1 vs2)
  | VStruct s1 vs1, VStruct s2 vs2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) vs1 vs2)
  | VUnion s1 i1 v1, VUnion s2 i2 v2 =>
     cast_if_and3 (decide_rel (=) s1 s2) (decide_rel (=) i1 i2)
       (decide_rel (=) v1 v2)
  | VUnionAll s1 vs1, VUnionAll s2 vs2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) vs1 vs2)
  | _, _ => right _
  end); clear go; abstract congruence.
Defined.

Section val_ind.
  Context {Ti} (P : val Ti → Prop).
  Context (Pbase : ∀ vb, P (VBase vb)).
  Context (Parray : ∀ τ vs, Forall P vs → P (VArray τ vs)).
  Context (Pstruct : ∀ s vs, Forall P vs → P (VStruct s vs)).
  Context (Punion : ∀ s i v, P v → P (VUnion s i v)).
  Context (Punion_all : ∀ s vs, Forall P vs → P (VUnionAll s vs)).
  Definition val_ind_alt: ∀ v, P v :=
    fix go v :=
    match v return P v with
    | VBase _ => Pbase _
    | VArray _ _ => Parray _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) _
    | VStruct _ _ => Pstruct _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) _
    | VUnion _ _ _ => Punion _ _ _ (go _)
    | VUnionAll _ _ => Punion_all _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) _
    end.
End val_ind.

Definition val_map {Ti} (f : base_val Ti → base_val Ti) : val Ti → val Ti :=
  fix go v :=
  match v with
  | VBase vb => VBase (f vb)
  | VArray τ vs => VArray τ (go <$> vs)
  | VStruct s vs => VStruct s (go <$> vs)
  | VUnion s i v => VUnion s i (go v)
  | VUnionAll s vs => VUnionAll s (go <$> vs)
  end.
Notation val_freeze β := (val_map (freeze β)).

Section operations.
  Context `{IntEnv Ti, PtrEnv Ti}.

  Definition val_unflatten (Γ : env Ti) : type Ti → list (bit Ti) → val Ti :=
    type_iter
    (**i TBase =>     *) (λ τb bs, VBase (base_val_unflatten Γ τb bs))
    (**i TArray =>    *) (λ τ n rec bs, VArray τ (array_unflatten Γ rec τ n bs))
    (**i TCompound => *) (λ c s τs rec bs,
      match c with
      | Struct_kind => VStruct s (struct_unflatten Γ (λ τ bs,
         let τsz := bit_size_of Γ τ in rec τ (take τsz bs)) τs bs)
      | Union_kind =>
         VUnionAll s ((λ τ, rec τ (take (bit_size_of Γ τ) bs)) <$> τs)
      end) Γ.

  Inductive vals_representable (Γ : env Ti) (m : mem Ti)
      (vs : list (val Ti)) (τs : list (type Ti)) : Prop :=
    make_vals_representable bs :
      ✓{Γ,m}* bs →
      Forall (λ τ, bit_size_of Γ τ ≤ length bs) τs →
      vs = (λ τ, val_unflatten Γ τ (take (bit_size_of Γ τ) bs)) <$> τs →
      vals_representable Γ m vs τs.
  Inductive val_typed' (Γ : env Ti) (m : mem Ti) : val Ti → type Ti → Prop :=
    | VBase_typed vb τb :
       (Γ,m) ⊢ vb : τb → val_typed' Γ m (VBase vb) (baseT τb)
    | VArray_typed vs τ n :
       n = length vs → Forall (λ v, val_typed' Γ m v τ) vs → n ≠ 0 →
       val_typed' Γ m (VArray τ vs) (τ.[n])
    | VStruct_typed s vs τs :
       Γ !! s = Some τs → Forall2 (val_typed' Γ m) vs τs →
       val_typed' Γ m (VStruct s vs) (structT s)
    | VUnion_typed s i τs v τ :
       Γ !! s = Some τs → τs !! i = Some τ →
       val_typed' Γ m v τ → val_typed' Γ m (VUnion s i v) (unionT s)
    | VUnionAll_typed s vs τs :
       Γ !! s = Some τs → Forall2 (val_typed' Γ m) vs τs →
       vals_representable Γ m vs τs →
       val_typed' Γ m (VUnionAll s vs) (unionT s).
  Global Instance val_typed:
    Typed (env Ti * mem Ti) (type Ti) (val Ti) := curry val_typed'.

  Lemma val_typed_inv_l Γ m (P : type Ti → Prop) v τ :
    (Γ,m) ⊢ v : τ →
    match v with
    | VBase vb => (∀ τb, (Γ,m) ⊢ vb : τb → P (baseT τb)) → P τ
    | VArray τ' vs =>
       (∀ n, n = length vs → (Γ,m) ⊢* vs : τ' → n ≠ 0 → P (τ'.[n])) → P τ
    | VStruct s vs =>
       (∀ τs, Γ !! s = Some τs → (Γ,m) ⊢* vs :* τs → P (structT s)) → P τ
    | VUnion s i v =>
       (∀ τs τ', Γ !! s = Some τs → τs !! i = Some τ' →
         (Γ,m) ⊢ v : τ' → P (unionT s)) → P τ
    | VUnionAll s vs =>
       (∀ τs, Γ !! s = Some τs → (Γ,m) ⊢* vs :* τs →
         vals_representable Γ m vs τs → P (unionT s)) → P τ
    end.
  Proof. destruct 1; simplify_equality; eauto. Qed.
  Lemma val_typed_inv_r Γ m (P : val Ti → Prop) v τ :
    (Γ,m) ⊢ v : τ →
    match τ with
    | baseT τb => (∀ vb, (Γ,m) ⊢ vb : τb → P (VBase vb)) → P v
    | τ'.[n] =>
       (∀ vs,
         n = length vs → (Γ,m) ⊢* vs : τ' → n ≠ 0 → P (VArray τ' vs)) → P v
    | structT s =>
       (∀ vs τs, Γ !! s = Some τs → (Γ,m) ⊢* vs :* τs →
         P (VStruct s vs)) → P v
    | unionT s =>
       (∀ i τs v' τ', Γ !! s = Some τs → τs !! i = Some τ' →
         (Γ,m) ⊢ v' : τ' → P (VUnion s i v')) →
       (∀ vs τs, Γ !! s = Some τs → (Γ,m) ⊢* vs :* τs →
         vals_representable Γ m vs τs → P (VUnionAll s vs)) → P v
    end.
  Proof. destruct 1; simplify_equality; eauto. Qed.
  Section val_typed_ind.
    Context (Γ : env Ti) (m : mem Ti) (P : val Ti → type Ti → Prop).
    Context (Pbase : ∀ vb τb, (Γ,m) ⊢ vb : τb → P (VBase vb) (baseT τb)).
    Context (Parray : ∀ vs τ,
      (Γ,m) ⊢* vs : τ → Forall (λ v, P v τ) vs →
      length vs ≠ 0 → P (VArray τ vs) (τ.[length vs])).
    Context (Pstruct : ∀ s vs τs,
      Γ !! s = Some τs → (Γ,m) ⊢* vs :* τs → Forall2 P vs τs →
      P (VStruct s vs) (structT s)).
    Context (PUnion : ∀ s i τs v τ,
      Γ !! s = Some τs → τs !! i = Some τ → (Γ,m) ⊢ v : τ → P v τ →
      P (VUnion s i v) (unionT s)).
    Context (Punion_none : ∀ s vs τs,
      Γ !! s = Some τs → (Γ,m) ⊢* vs :* τs → Forall2 P vs τs →
      vals_representable Γ m vs τs → P (VUnionAll s vs) (unionT s)).
    Definition val_typed_ind : ∀ v τ, val_typed' Γ m v τ → P v τ.
    Proof.
      fix 3; destruct 1; simplify_equality;
        eauto using Forall_impl, Forall2_impl.
    Qed.
  End val_typed_ind.

  Global Instance type_of_val: TypeOf (type Ti) (val Ti) := λ v,
    match v with
    | VBase vb => baseT (type_of vb)
    | VArray τ vs => τ.[length vs]
    | VStruct s _ => structT s
    | VUnion s _ _ | VUnionAll s _ => unionT s
    end.

  Definition val_new (Γ : env Ti) : type Ti → val Ti := type_iter
    (**i TBase     *) (λ τb,
      VBase (if decide (τb = voidT%BT) then VVoid else VIndet τb))
    (**i TArray    *) (λ τ n x, VArray τ (replicate n x))
    (**i TCompound *) (λ c s τs rec,
      match c with
      | Struct_kind => VStruct s (rec <$> τs)
      | Union_kind => VUnionAll s (rec <$> τs)
      end) Γ.
  Definition val_0 (Γ : env Ti) : type Ti → val Ti := type_iter
    (**i TBase     *) (λ τb, VBase (base_val_0 τb))
    (**i TArray    *) (λ τ n x, VArray τ (replicate n x))
    (**i TCompound *) (λ c s τs rec,
      match c with
      | Struct_kind => VStruct s (rec <$> τs)
      | Union_kind => VUnion s 0 (default (VUnionAll s []) (τs !! 0) rec)
      end) Γ.
  Definition val_flatten (Γ : env Ti) : val Ti → list (bit Ti) :=
    fix go v :=
    match v with
    | VBase vb => base_val_flatten Γ vb
    | VArray _ vs => vs ≫= go
    | VStruct s vs =>
       default [] (Γ !! s) $ λ τs,
         let szs := field_bit_sizes Γ τs in
         mjoin (zip_with (λ w sz, resize sz BIndet (go w)) vs szs)
    | VUnion s i v => resize (bit_size_of Γ (unionT s)) BIndet (go v)
    | VUnionAll s vs =>
       let sz := bit_size_of Γ (unionT s) in
       from_option (replicate sz BIndet) (bits_list_join sz (go <$> vs))
    end.

  Fixpoint to_val (Γ : env Ti) (w : mtree Ti) : val Ti :=
    match w with
    | MBase τb bs => VBase (base_val_unflatten Γ τb (tagged_tag <$> bs))
    | MArray τ ws => VArray τ (to_val Γ <$> ws)
    | MStruct s wxbss => VStruct s (to_val Γ ∘ fst <$> wxbss)
    | MUnion s i w _ => VUnion s i (to_val Γ w)
    | MUnionAll s bs => val_unflatten Γ (unionT s) (tagged_tag <$> bs)
    end.
  Definition array_of_val (Γ : env Ti) (f : list perm → val Ti → mtree Ti) :
      list perm → list (val Ti) → list (mtree Ti) :=
    fix go xs vs :=
    match vs with
    | [] => []
    | v :: vs =>
       let sz := bit_size_of' Γ v in f (take sz xs) v :: go (drop sz xs) vs
    end.
  Definition struct_of_val (Γ : env Ti) (f : list perm → val Ti → mtree Ti) :
      list perm → list (val Ti) → list nat → list (mtree Ti * list (pbit Ti)) :=
    fix go xs vs pads :=
    match vs, pads with
    | v :: vs, pad :: pads =>
       let sz := bit_size_of' Γ v in
       let xs' := drop sz xs in
       (f (take sz xs) v,
        flip PBit BIndet <$> take pad xs') :: go (drop pad xs') vs pads
    | _, _ => []
    end.
  Fixpoint of_val (Γ : env Ti) (xs : list perm) (v : val Ti) : mtree Ti :=
    match v with
    | VBase vb =>
       MBase (type_of vb) (zip_with PBit xs (base_val_flatten Γ vb))
    | VArray τ vs => MArray τ (array_of_val Γ (of_val Γ) xs vs)
    | VStruct s vs =>
       let pads := field_bit_padding Γ (type_of <$> vs) in
       MStruct s (struct_of_val Γ (of_val Γ) xs vs pads)
    | VUnion s i v =>
       let sz := bit_size_of' Γ v in
       MUnion s i (of_val Γ (take sz xs) v) (flip PBit BIndet <$> drop sz xs)
    | VUnionAll s vs =>
       MUnionAll s (zip_with PBit xs (val_flatten Γ (VUnionAll s vs)))
    end.

  Global Instance vtype_check:
      TypeCheck (env Ti * mem Ti) (type Ti) (val Ti) :=
    fix go (Γm : _ * _) v {struct v} := let _ : TypeCheck _ _ _ := @go in
    let (Γ,m) := Γm in
    match v with
    | VBase vb => TBase <$> type_check (Γ,m) vb
    | VArray τ vs =>
       guard (length vs ≠ 0);
       τs ← mapM (type_check (Γ,m)) vs;
       guard (Forall (τ =) τs);
       Some (τ.[length vs])
    | VStruct s vs =>
       τs ← Γ !! s;
       τs' ← mapM (type_check (Γ,m)) vs;
       guard ((τs' : list (type Ti)) = τs);
       Some (structT s)
    | VUnion s i v =>
       τ ← Γ !! s ≫= (!! i);
       τ' ← type_check (Γ,m) v;
       guard ((τ' : type Ti) = τ);
       Some (unionT s)
    | VUnionAll s vs =>
       τs ← Γ !! s;
       τs' ← mapM (type_check (Γ,m)) vs;
       guard (τs = τs');
       let sz := bit_size_of Γ (unionT s) in
       bs ← bits_list_join sz (val_flatten Γ <$> vs);
       guard (vs = (λ τ, val_unflatten Γ τ (take (bit_size_of Γ τ) bs)) <$> τs);
       Some (unionT s)
    end.

  Global Instance val_lookup_seg:
      Lookup (ref_seg Ti) (val Ti) (val Ti) := λ rs v,
    match rs, v with
    | RArray i τ n, VArray τ' vs =>
       guard (n = length vs); guard (τ = τ'); vs !! i
    | RStruct i s, VStruct s' vs => guard (s = s'); vs !! i
    | RUnion i s _, VUnion s' j v => guard (s = s'); guard (i = j); Some v
    | RUnion i s _, VUnionAll s' vs => guard (s = s'); vs !! i
    | _, _ => None
    end.
  Global Instance val_lookup: Lookup (ref Ti) (val Ti) (val Ti) :=
    fix go r v := let _ : Lookup _ _ _ := @go in
    match r with [] => Some v | rs :: r => v !! r ≫= (!! rs) end.

  Inductive val_union_free : val Ti → Prop :=
    | VBase_union_free vb : val_union_free (VBase vb)
    | VArray_union_free τ vs :
       Forall (val_union_free) vs → val_union_free (VArray τ vs)
    | VStruct_union_free s vs :
       Forall val_union_free vs → val_union_free (VStruct s vs)
    | VUnionAll_union_free s vs :
       Forall val_union_free vs → val_union_free (VUnionAll s vs).
  Section val_union_free_ind.
    Context (Γ : env Ti) (P : val Ti → Prop).
    Context (Pbase : ∀ vb, P (VBase vb)).
    Context (Parray : ∀ τ vs,
      Forall val_union_free vs → Forall P vs → P (VArray τ vs)).
    Context (Pstruct : ∀ s vs,
      Forall val_union_free vs → Forall P vs → P (VStruct s vs)).
    Context (Punion_none : ∀ s vs,
      Forall val_union_free vs → Forall P vs → P (VUnionAll s vs)).
    Definition val_union_free_ind_alt: ∀ v, val_union_free v → P v.
    Proof. fix 2; destruct 1; eauto using Forall_impl. Qed.
  End val_union_free_ind.
  Global Instance val_union_free_dec: ∀ v, Decision (val_union_free v).
  Proof.
   refine (
    fix go v :=
    match v return Decision (val_union_free v) with
    | VBase v => left _
    | VArray _ vs => cast_if (decide (Forall val_union_free vs))
    | VStruct _ vs => cast_if (decide (Forall val_union_free vs))
    | VUnion s i v => right _
    | VUnionAll _ vs => cast_if (decide (Forall val_union_free vs))
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.

  Inductive val_refine' (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : mem Ti) :
       val Ti → val Ti → type Ti → Prop :=
    | VBase_refine vb1 vb2 τb :
       vb1 ⊑{Γ,f@m1↦m2} vb2 : τb →
       val_refine' Γ f m1 m2 (VBase vb1) (VBase vb2) (baseT τb)
    | VArray_refine τ n vs1 vs2 :
       n = length vs1 →
       Forall2 (λ v1 v2, val_refine' Γ f m1 m2 v1 v2 τ) vs1 vs2 →
       n ≠ 0 → val_refine' Γ f m1 m2 (VArray τ vs1) (VArray τ vs2) (τ.[n])
    | VStruct_refine s τs vs1 vs2 :
       Γ !! s = Some τs → Forall3 (val_refine' Γ f m1 m2) vs1 vs2 τs →
       val_refine' Γ f m1 m2 (VStruct s vs1) (VStruct s vs2) (structT s)
    | VUnion_refine s τs i v1 v2 τ :
       Γ !! s = Some τs → τs !! i = Some τ → val_refine' Γ f m1 m2 v1 v2 τ →
       val_refine' Γ f m1 m2 (VUnion s i v1) (VUnion s i v2) (unionT s)
    | VUnionAll_refine s τs vs1 vs2 :
       Γ !! s = Some τs → Forall3 (val_refine' Γ f m1 m2) vs1 vs2 τs →
       vals_representable Γ m1 vs1 τs → vals_representable Γ m2 vs2 τs →
       val_refine' Γ f m1 m2 (VUnionAll s vs1) (VUnionAll s vs2) (unionT s)
    | VUnion_VUnionAll_refine s τs i v1 v2 τ vs2 :
       Γ !! s = Some τs → τs !! i = Some τ → vs2 !! i = Some v2 →
       val_refine' Γ f m1 m2 v1 v2 τ → vals_representable Γ m2 vs2 τs →
       val_refine' Γ f m1 m2 (VUnion s i v1) (VUnionAll s vs2) (unionT s).
  Global Instance val_refine:
    RefineT Ti (mem Ti) (val Ti) (type Ti) := val_refine'.

  Lemma val_refine_inv_l Γ f m1 m2 (P : val Ti → Prop) v1 v2 τ :
    v1 ⊑{Γ,f@m1↦m2} v2 : τ →
    match v1, τ with
    | VBase vb1, baseT τb =>
       (∀ vb2, vb1 ⊑{Γ,f@m1↦m2} vb2 : τb → P (VBase vb2)) → P v2
    | VArray τ' vs1, _ =>
       (∀ vs2, vs1 ⊑{Γ,f@m1↦m2}* vs2 : τ' → P (VArray τ' vs2)) → P v2
    | VStruct s vs1, _ =>
       (∀ τs vs2, Γ !! s = Some τs →
         vs1 ⊑{Γ,f@m1↦m2}* vs2 :* τs → P (VStruct s vs2)) → P v2 
    | VUnion s i v1, _ =>
       (∀ τs v2 τ, Γ !! s = Some τs → τs !! i = Some τ →
         v1 ⊑{Γ,f@m1↦m2} v2 : τ → P (VUnion s i v2)) →
       (∀ τs v2 τ vs2, Γ !! s = Some τs → τs !! i = Some τ →
         vs2 !! i = Some v2 → v1 ⊑{Γ,f@m1↦m2} v2 : τ →
         vals_representable Γ m2 vs2 τs → P (VUnionAll s vs2)) → P v2
    | VUnionAll s vs1, _ =>
       (∀ τs vs2, Γ !! s = Some τs → vs1 ⊑{Γ,f@m1↦m2}* vs2 :* τs →
         vals_representable Γ m1 vs1 τs → vals_representable Γ m2 vs2 τs →
         P (VUnionAll s vs2)) → P v2
    | _, _ => P v2
    end.
  Proof. destruct 1; eauto. Qed.
  Section val_refine_ind.
    Context (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : mem Ti).
    Context (P : val Ti → val Ti → type Ti → Prop).
    Context (Pbase : ∀ vb1 vb2 τb,
      vb1 ⊑{Γ,f@m1↦m2} vb2 : τb → P (VBase vb1) (VBase vb2) (baseT τb)).
    Context (Parray : ∀ τ n vs1 vs2,
      length vs1 = n → vs1 ⊑{Γ,f@m1↦m2}* vs2 : τ →
      Forall2 (λ v1 v2, P v1 v2 τ) vs1 vs2 → n ≠ 0 →
      P (VArray τ vs1) (VArray τ vs2) (τ.[n])).
    Context (Pstruct : ∀ s τs vs1 vs2,
      Γ !! s = Some τs → vs1 ⊑{Γ,f@m1↦m2}* vs2 :* τs → Forall3 P vs1 vs2 τs →
      P (VStruct s vs1) (VStruct s vs2) (structT s)).
    Context (Punion : ∀ s τs i v1 v2 τ,
      Γ !! s = Some τs → τs !! i = Some τ →
      v1 ⊑{Γ,f@m1↦m2} v2 : τ → P v1 v2 τ →
      P (VUnion s i v1) (VUnion s i v2) (unionT s)).
    Context (Punion_none : ∀ s τs vs1 vs2,
      Γ !! s = Some τs → vs1 ⊑{Γ,f@m1↦m2}* vs2 :* τs → Forall3 P vs1 vs2 τs →
      vals_representable Γ m1 vs1 τs → vals_representable Γ m2 vs2 τs →
      P (VUnionAll s vs1) (VUnionAll s vs2) (unionT s)).
    Context (Punion_union_none : ∀ s τs i v1 v2 τ vs2,
      Γ !! s = Some τs → τs !! i = Some τ → vs2 !! i = Some v2 →
      v1 ⊑{Γ,f@m1↦m2} v2 : τ → P v1 v2 τ → vals_representable Γ m2 vs2 τs →
      P (VUnion s i v1) (VUnionAll s vs2) (unionT s)).
    Definition val_refine_ind: ∀ v1 v2 τ,
      val_refine' Γ f m1 m2 v1 v2 τ → P v1 v2 τ.
    Proof. fix 4; destruct 1; eauto using Forall2_impl, Forall3_impl. Qed.
  End val_refine_ind.

  Definition val_true (v : val Ti) : Prop :=
    match v with VBase vb => base_val_true vb | _ => False end.
  Definition val_false (v : val Ti) : Prop :=
    match v with VBase vb => base_val_false vb | _ => False end.

  Inductive unop_typed : unop → type Ti → type Ti → Prop :=
    | TBase_unop_typed op τb σb :
       base_unop_typed op τb σb → unop_typed op (baseT τb) (baseT σb).
  Definition unop_type_of (op : unop) (τ : type Ti) : option (type Ti) :=
    match τ with
    | baseT τb => σb ← base_unop_type_of op τb; Some (baseT σb) | _ => None
    end.
  Definition val_unop_ok (op : unop) (v : val Ti) : Prop :=
    match v with VBase vb => base_val_unop_ok op vb | _ => False end.
  Global Arguments val_unop_ok !_ !_ /.
  Definition val_unop (op : unop) (v : val Ti) : val Ti :=
    match v with VBase vb => VBase (base_val_unop op vb) | _ => v end.
  Global Arguments val_unop !_ !_ /.

  Inductive binop_typed : binop → type Ti → type Ti → type Ti → Prop :=
    | TBase_binop_typed op τb1 τb2 σb :
       base_binop_typed op τb1 τb2 σb →
       binop_typed op (baseT τb1) (baseT τb2) (baseT σb).
  Definition binop_type_of (op : binop) (τ1 τ2 : type Ti) : option (type Ti) :=
    match τ1, τ2 with
    | baseT τb1, baseT τb2 =>
       σb ← base_binop_type_of op τb1 τb2; Some (baseT σb)
    | _, _ => None
    end.
  Definition val_binop_ok (Γ : env Ti) (m : mem Ti)
      (op : binop) (v1 v2 : val Ti) : Prop :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => base_val_binop_ok Γ m op vb1 vb2 | _, _ => False
    end.
  Global Arguments val_binop_ok _ _ !_ !_ !_ /.
  Definition val_binop (Γ : env Ti) (op : binop) (v1 v2 : val Ti) : val Ti :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => VBase (base_val_binop Γ op vb1 vb2) | _, _ => v1
    end.
  Global Arguments val_binop _ !_ !_ !_ /.

  Inductive cast_typed (Γ : env Ti) : type Ti → type Ti → Prop :=
    | TBase_cast_typed τb1 τb2 :
       base_cast_typed Γ τb1 τb2 → cast_typed Γ (baseT τb1) (baseT τb2)
    | TBase_TVoid_cast_typed τ : cast_typed Γ τ voidT.
  Definition val_cast_ok (Γ : env Ti) (τ : type Ti) (v : val Ti) : Prop :=
    match v, τ with
    | VBase vb, baseT τb => base_val_cast_ok Γ τb vb
    | _, voidT => True | _ , _ => False
    end.
  Global Arguments val_cast_ok _ !_ !_ /.
  Definition val_cast (τ : type Ti) (v : val Ti) : val Ti :=
    match v, τ with
    | VBase vb, baseT τb => VBase (base_val_cast τb vb)
    | _, voidT => VBase VVoid | _ , _ => v
    end.
  Global Arguments val_cast !_ !_ /.
End operations.

Section val.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types m : mem Ti.
Implicit Types τb : base_type Ti.
Implicit Types τ : type Ti.
Implicit Types τs : list (type Ti).
Implicit Types b : bit Ti.
Implicit Types bs : list (bit Ti).
Implicit Types x : perm.
Implicit Types xs : list perm.
Implicit Types xb : pbit Ti.
Implicit Types xbs : list (pbit Ti).
Implicit Types w : mtree Ti.
Implicit Types ws : list (mtree Ti).
Implicit Types rs : ref_seg Ti.
Implicit Types r : ref Ti.
Implicit Types vb : base_val Ti.
Implicit Types v : val Ti.
Implicit Types vs : list (val Ti).
Notation vals_unflatten Γ τs bs :=
  ((λ τ, val_unflatten Γ τ (take (bit_size_of Γ τ) bs)) <$> τs).

Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Hint Extern 0 (_ ⊑* _) => reflexivity.
Hint Resolve Forall_take Forall_drop Forall_app_2
  Forall_replicate Forall_resize.
Hint Resolve Forall2_take Forall2_drop Forall2_app
  Forall2_replicate Forall2_resize.
Hint Resolve BIndet_valid BIndet_refine
  BIndet_BIndet_refine BIndet_weak_refine.
Hint Immediate env_valid_lookup env_valid_lookup_lookup.
Hint Extern 0 (Separation _) => apply (_ : Separation (pbit Ti)).
Local Arguments union _ _ !_ !_ /.

(** ** Properties of the [val_flatten] function *)
Lemma val_flatten_length Γ m τ v :
  ✓ Γ → (Γ,m) ⊢ v : τ → length (val_flatten Γ v) = bit_size_of Γ τ.
Proof.
  intros HΓ Hvτ. revert v τ Hvτ. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros. by erewrite base_val_flatten_length by eauto.
  * intros vs τ _ IH _. rewrite bit_size_of_array.
    induction IH; csimpl; rewrite ?app_length; auto.
  * intros s vs τs Hs Hvs IH.
    rewrite (bit_size_of_struct _ _ τs), Hs by done; simpl; clear Hs.
    revert vs Hvs IH. induction (bit_size_of_fields _ τs HΓ)
      as [|τ sz ?? Hn]; intros; decompose_Forall_hyps'; [done |].
    rewrite app_length, resize_length; f_equal. eauto.
  * intros. by rewrite resize_length.
  * intros s vs τs Hs Hvs IH Hrep.
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs'; simpl.
    + eauto using bits_list_join_length.
    + by rewrite replicate_length.
Qed.
Lemma val_flatten_valid Γ m v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → ✓{Γ,m}* (val_flatten Γ v).
Proof.
  intros HΓ Hvτ. revert v τ Hvτ. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * eauto using base_val_flatten_valid.
  * intros vs τ Hvs IH _. induction IH; decompose_Forall_hyps'; auto.
  * intros s vs τs Hs Hvs IH. rewrite Hs; simpl; clear Hs. revert vs Hvs IH.
    induction (bit_size_of_fields _ τs HΓ);intros; decompose_Forall_hyps'; auto.
  * eauto.
  * intros s vs τs Hs Hvs IH Hrep.
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs'; simpl; auto.
    eapply bits_list_join_valid; eauto. elim IH; csimpl; auto.
Qed.

Ltac solve_length := repeat first
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite resize_length | rewrite fmap_length | rewrite replicate_length
  | erewrite ctree_flatten_length by eauto|erewrite val_flatten_length by eauto
  | rewrite zip_with_length | erewrite base_val_flatten_length by eauto
  | match goal with
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
      | H : Γ !! ?s = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s))
          by eauto using bit_size_of_union_lookup
      | H : Γ !! ?s = Some [?τ] |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT s))
          by eauto using bit_size_of_union_singleton
      end
    end]; lia.
Hint Extern 0 (length _ = _) => solve_length.
Hint Extern 0 (_ ≤ length _) => solve_length.
Hint Extern 0 (length _ ≤ _) => solve_length.

(** ** Properties of the [val_unflatten] function *)
Lemma val_unflatten_base Γ τb :
  val_unflatten Γ τb = λ bs, VBase (base_val_unflatten Γ τb bs).
Proof. unfold val_unflatten. by rewrite type_iter_base. Qed. 
Lemma val_unflatten_array Γ τ n :
  val_unflatten Γ (τ.[n]) = λ bs,
    VArray τ (array_unflatten Γ (val_unflatten Γ τ) τ n bs).
Proof. unfold val_unflatten. by rewrite type_iter_array. Qed.
Lemma val_unflatten_compound Γ c s τs bs :
  ✓ Γ → Γ !! s = Some τs → val_unflatten Γ (compoundT{c} s) bs =
    match c with
    | Struct_kind => VStruct s (struct_unflatten Γ (λ τ bs,
       let τsz := bit_size_of Γ τ in val_unflatten Γ τ (take τsz bs)) τs bs)
    | Union_kind => VUnionAll s (vals_unflatten Γ τs bs)
    end.
Proof.
  intros HΓ Hs. unfold val_unflatten. erewrite (type_iter_compound
    (pointwise_relation (list (bit Ti)) (@eq (val Ti))) _ _ _ _); try done.
  { intros ???????; f_equal. by apply array_unflatten_weaken. }
  clear s τs Hs bs. intros f g [] s τs Hs Hτs ? bs; f_equal.
  { eapply struct_unflatten_weaken, Forall_impl; eauto. }
  eapply Forall_fmap_ext, Forall_impl; eauto.
Qed.
Lemma val_unflatten_weaken Γ1 Γ2 τ bs :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → val_unflatten Γ1 τ bs = val_unflatten Γ2 τ bs.
Proof.
  intros. apply (type_iter_weaken (pointwise_relation _ (=))); try done.
  { intros ???. by erewrite base_val_unflatten_weaken by eauto. }
  { intros ???????; f_equal. by apply array_unflatten_weaken. }
  clear bs. intros f g [] s τs Hs Hτs Hfg bs; f_equal; auto.
  { eapply struct_unflatten_weaken, Forall_impl; eauto 1.
    auto using bit_size_of_weaken with f_equal. }
  clear Hs. induction Hfg; decompose_Forall_hyps'; f_equal;
    auto using bit_size_of_weaken with f_equal.
Qed.
Lemma vals_unflatten_weaken Γ1 Γ2 τs bs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  vals_unflatten Γ1 τs bs = vals_unflatten Γ2 τs bs.
Proof.
  induction 2; intros; f_equal'; auto.
  by erewrite bit_size_of_weaken, val_unflatten_weaken by eauto.
Qed.
Lemma val_unflatten_typed Γ m τ bs :
  ✓ Γ → ✓{Γ} τ → ✓{Γ,m}* bs → length bs = bit_size_of Γ τ →
  (Γ,m) ⊢ val_unflatten Γ τ bs : τ.
Proof.
  intros HΓ Hτ. revert τ Hτ bs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb Hτ bs Hbs Hbs'. rewrite val_unflatten_base.
    typed_constructor; auto using base_val_unflatten_typed.
  * intros τ n Hτ IH Hn bs; rewrite val_unflatten_array, bit_size_of_array.
    intros Hbs Hbs'. typed_constructor; eauto using array_unflatten_length.
    revert bs Hbs Hbs'. clear Hn. induction n; simpl; auto.
  * intros [] s τs Hs Hτs IH _ bs; erewrite val_unflatten_compound,
       ?bit_size_of_struct by eauto; intros Hbs Hbs'.
    { typed_constructor; eauto. unfold struct_unflatten.
      revert bs Hbs Hbs'. clear Hs Hτs. induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps'; auto. }
    typed_constructor; eauto.
    { clear Hτs. pose proof (bit_size_of_union _ _ _ HΓ Hs); clear Hs.
      induction IH; decompose_Forall_hyps'; auto. }
    exists bs; auto. rewrite Hbs'. auto using bit_size_of_union.
Qed.
Lemma vals_unflatten_typed Γ m τs bs :
  ✓ Γ → ✓{Γ}* τs → ✓{Γ,m}* bs → Forall (λ τ, bit_size_of Γ τ ≤ length bs) τs →
  (Γ,m) ⊢* vals_unflatten Γ τs bs :* τs.
Proof.
  induction 2; intros; decompose_Forall_hyps'; auto using val_unflatten_typed.
Qed.
Lemma vals_representable_typed Γ m vs τs :
  ✓ Γ → ✓{Γ}* τs → vals_representable Γ m vs τs → (Γ,m) ⊢* vs :* τs.
Proof. intros ?? [bs ?? ->]. auto using vals_unflatten_typed. Qed.
Lemma val_unflatten_type_of Γ τ bs :
  ✓ Γ → ✓{Γ} τ → type_of (val_unflatten Γ τ bs) = τ.
Proof.
  intros HΓ Hτ. revert τ Hτ bs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb _ bs. rewrite val_unflatten_base; simpl.
    by rewrite base_val_unflatten_type_of.
  * intros τ [|n] _ IH ? bs; [done|]. rewrite val_unflatten_array; simpl.
    by rewrite array_unflatten_length.
  * intros [] s τs ? _ _ _ bs; by erewrite val_unflatten_compound by eauto.
Qed.
Lemma vals_unflatten_type_of Γ τs bs :
  ✓ Γ → ✓{Γ}* τs → type_of <$> vals_unflatten Γ τs bs = τs.
Proof. induction 2; f_equal'; auto using val_unflatten_type_of. Qed.
Lemma vals_unflatten_representable Γ m bs τs :
  ✓{Γ,m}* bs → Forall (λ τ, bit_size_of Γ τ ≤ length bs) τs →
  vals_representable Γ m (vals_unflatten Γ τs bs) τs.
Proof. by exists bs. Qed.
Lemma val_unflatten_frozen Γ m τ bs :
  ✓ Γ → ✓{Γ,m}* bs →
  val_freeze true (val_unflatten Γ τ bs) = val_unflatten Γ τ bs.
Proof.
  intros HΓ. revert τ bs. refine (weak_type_env_ind _ HΓ _ _ _ _ _).
  * intros. rewrite val_unflatten_base; simpl.
    by rewrite base_val_unflatten_frozen by eauto.
  * intros τ n IH bs Hbs. rewrite val_unflatten_array; f_equal'. revert bs Hbs.
    induction n; intros; f_equal'; auto.
  * intros [] s τs Hs IH bs Hbs;
      erewrite val_unflatten_compound by eauto; f_equal'; clear Hs.
    { unfold struct_unflatten. revert bs Hbs.
      induction (bit_size_of_fields _ τs HΓ); intros;
        decompose_Forall_hyps'; f_equal; auto. }
    revert bs Hbs; induction IH; intros; f_equal'; eauto.
  * intros c s Hs bs Hbs.
    unfold val_unflatten; rewrite type_iter_compound_None by eauto.
    destruct c; f_equal'. unfold struct_unflatten; simpl; auto.
    rewrite !field_bit_sizes_nil by done. repeat constructor.
Qed.
Lemma vals_unflatten_frozen Γ m τs bs :
  ✓ Γ → ✓{Γ,m}* bs →
  val_freeze true <$> vals_unflatten Γ τs bs = vals_unflatten Γ τs bs.
Proof. intros. induction τs; f_equal'; eauto using val_unflatten_frozen. Qed.
Lemma val_unflatten_union_free Γ τ bs :
  ✓ Γ → val_union_free (val_unflatten Γ τ bs).
Proof.
  intros HΓ. revert τ bs. refine (weak_type_env_ind _ HΓ _ _ _ _ _).
  * intros. rewrite val_unflatten_base. by constructor.
  * intros τ n IH bs. rewrite val_unflatten_array. constructor.
    revert bs. induction n; simpl; auto.
  * intros [] s τs Hs IH bs; erewrite !val_unflatten_compound by eauto.
    { constructor. unfold struct_unflatten. revert bs. clear Hs.
      induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps'; auto. }
    constructor. elim IH; csimpl; auto.
  * intros c s Hs bs. unfold val_unflatten;
      rewrite type_iter_compound_None by done; simpl.
    destruct c; repeat constructor.
    unfold struct_unflatten. rewrite field_bit_sizes_nil by done. constructor.
Qed.
Lemma val_unflatten_between Γ τ bs1 bs2 bs3 :
  ✓ Γ → ✓{Γ} τ → bs1 ⊑* bs2 → bs2 ⊑* bs3 → length bs1 = bit_size_of Γ τ →
  val_unflatten Γ τ bs1 = val_unflatten Γ τ bs3 →
  val_unflatten Γ τ bs2 = val_unflatten Γ τ bs3.
Proof.
  intros HΓ Hτ. revert τ Hτ bs1 bs2 bs3. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb ? bs1 bs2 bs3 ??.
    rewrite !val_unflatten_base, !(injective_iff VBase).
    by apply base_val_unflatten_between.
  * intros τ n ? IH _ bs1 bs2 bs3 Hbs1 Hbs2. rewrite !val_unflatten_array,
       bit_size_of_array, !(injective_iff (VArray _)).
    revert bs1 bs2 bs3 Hbs1 Hbs2.
    induction n; intros; simplify_equality'; f_equal'; eauto.
  * intros [] s τs Hs Hτs IH _ bs1 bs2 bs3 Hbs1 Hbs2;
      erewrite !val_unflatten_compound, ?bit_size_of_struct by eauto.
    { rewrite !(injective_iff (VStruct s)). clear Hs Hτs.
      revert bs1 bs2 bs3 Hbs1 Hbs2. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros ???; simpl;
        rewrite ?take_take; intros; decompose_Forall_hyps'; f_equal; eauto. }
    pose proof (bit_size_of_union _ _ _ HΓ Hs). clear Hs Hτs.
    rewrite !(injective_iff (VUnionAll s)). revert bs1 bs2 bs3 Hbs1 Hbs2.
    induction IH; intros; decompose_Forall_hyps'; f_equal; eauto.
Qed.
Lemma vals_unflatten_between Γ τs bs1 bs2 bs3 :
  ✓ Γ → ✓{Γ}* τs → bs1 ⊑* bs2 → bs2 ⊑* bs3 →
  Forall (λ τ, bit_size_of Γ τ ≤ length bs1) τs →
  vals_unflatten Γ τs bs1 = vals_unflatten Γ τs bs3 →
  vals_unflatten Γ τs bs2 = vals_unflatten Γ τs bs3.
Proof.
  induction 2; intros; decompose_Forall_hyps'; f_equal;
    eauto using val_unflatten_between.
Qed.

(** ** General properties of the typing judgment *)
Lemma val_typed_int_frozen Γ m v τi :
  (Γ,m) ⊢ v : intT τi → val_freeze true v = v.
Proof. inversion_clear 1;simpl. by erewrite base_typed_int_frozen by eauto. Qed.
Lemma val_union_free_base Γ m v τb : (Γ,m) ⊢ v : baseT τb → val_union_free v.
Proof. inversion 1; constructor. Qed.
Lemma val_typed_type_valid Γ m v τ : ✓ Γ → (Γ,m) ⊢ v : τ → ✓{Γ} τ.
Proof.
  induction 2 using @val_typed_ind; econstructor; decompose_Forall_hyps;
    try match goal with
    | H : length ?vs ≠ 0, H2 : Forall _ ?vs |- _ => destruct H2; [done|]
    end; eauto; eapply base_val_typed_type_valid; eauto.
Qed.
Lemma val_typed_types_valid Γ m vs τs : ✓ Γ → (Γ,m) ⊢* vs :* τs → ✓{Γ}* τs.
Proof. induction 2; constructor; eauto using val_typed_type_valid. Qed.
Global Instance: TypeOfSpec (env Ti * mem Ti) (type Ti) (val Ti).
Proof.
  intros [Γ mm]. induction 1 using @val_typed_ind; decompose_Forall_hyps';
    eauto using type_of_correct with f_equal.
Qed.
Lemma vals_representable_weaken Γ1 Γ2 m1 m2 vs τs :
  ✓ Γ1 → ✓{Γ1}* τs → vals_representable Γ1 m1 vs τs → Γ1 ⊆ Γ2 →
  (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → vals_representable Γ2 m2 vs τs.
Proof.
  intros ? Hτs [bs ? Hlen Hvs]. exists bs.
  * eauto using Forall_impl, bit_valid_weaken.
  * clear Hvs. induction Hτs; decompose_Forall_hyps'; constructor; auto 2.
    by erewrite <-bit_size_of_weaken by eauto.
  * by erewrite <-vals_unflatten_weaken by eauto.
Qed.
Lemma val_typed_weaken Γ1 Γ2 m1 m2 v τ :
  ✓ Γ1 → (Γ1,m1) ⊢ v : τ → Γ1 ⊆ Γ2 → (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) →
  (Γ2,m2) ⊢ v : τ.
Proof.
  intros ? Hvτ ??. induction Hvτ using @val_typed_ind; econstructor;
    erewrite <-1?vals_unflatten_weaken;
    erewrite <-1?bit_size_of_weaken by eauto using TCompound_valid;
    eauto using base_typed_weaken, lookup_weaken, vals_representable_weaken,
      Forall_impl, bit_valid_weaken, val_typed_types_valid.
Qed.
Lemma val_freeze_freeze β1 β2 v :
  val_map (freeze β1) (val_map (freeze β2) v) = val_map (freeze β1) v.
Proof.
  assert (∀ vs, Forall (λ v, val_map (freeze β1)
      (val_map (freeze β2) v) = val_map (freeze β1) v) vs →
    val_map (freeze β1) <$> val_map (freeze β2) <$> vs =
      val_map (freeze β1) <$> vs).
  { induction 1; f_equal'; auto. }
  induction v using val_ind_alt; f_equal'; auto using base_val_freeze_freeze.
Qed.
Lemma vals_freeze_freeze β1 β2 vs :
  val_map (freeze β1) <$> val_map (freeze β2) <$> vs
  = val_map (freeze β1) <$> vs.
Proof. induction vs; f_equal'; auto using val_freeze_freeze. Qed.
Lemma vals_representable_freeze Γ m vs τs :
  ✓ Γ → vals_representable Γ m vs τs →
  vals_representable Γ m (val_freeze true <$> vs) τs.
Proof. intros ? [bs ?? ->]. exists bs; eauto using vals_unflatten_frozen. Qed.
Lemma typed_freeze Γ m v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → (Γ,m) ⊢ val_freeze true v : τ.
Proof.
  induction 2 using @val_typed_ind; simplify_equality'.
  * typed_constructor. by apply base_typed_freeze.
  * typed_constructor; auto using fmap_length. by apply Forall_fmap.
  * typed_constructor; eauto. by apply Forall2_fmap_l.
  * typed_constructor; eauto.
  * typed_constructor; eauto using vals_representable_freeze.
    by apply Forall2_fmap_l.
Qed.
Lemma val_freeze_type_of β v : type_of (val_map (freeze β) v) = type_of v.
Proof.
  induction v using val_ind_alt; simpl; simpl; auto.
  by rewrite base_val_freeze_type_of.
Qed.
Lemma vals_freeze_type_of β vs :
  type_of <$> val_map (freeze β) <$> vs = type_of <$> vs.
Proof. induction vs; f_equal'; auto using val_freeze_type_of. Qed.
Lemma val_union_free_freeze β v :
  val_union_free (val_map (freeze β) v) ↔ val_union_free v.
Proof.
  split.
  * assert (∀ vs, Forall (λ v,
        val_union_free (val_map (freeze β) v) → val_union_free v) vs →
      Forall val_union_free (val_map (freeze β) <$> vs) →
      Forall val_union_free vs).
    { induction 1; csimpl; intros; decompose_Forall; eauto. } 
    induction v using val_ind_alt; inversion_clear 1; econstructor; eauto.
  * induction 1 using @val_union_free_ind_alt; simpl;
      econstructor; eauto; by apply Forall_fmap.
Qed.

(** ** Interaction between [val_flatten] and [val_unflatten] *)
Lemma val_union_to_bits_valid Γ m sz vs τs bs :
  ✓ Γ → bits_list_join sz (val_flatten Γ <$> vs) = Some bs →
  (Γ,m) ⊢* vs :* τs → ✓{Γ,m}* bs.
Proof.
  intros ? Hbs Hvs. eapply bits_list_join_valid; eauto.
  elim Hvs; intros; constructor; eauto using val_flatten_valid.
Qed.
Lemma bits_weakly_refine_resize_l sz sz' bs1 bs2 :
  bs1 ⊑* take sz bs2 → length bs2 = sz' →
  sz ≤ sz' → resize sz' BIndet bs1 ⊑* bs2.
Proof.
  intros. transitivity (resize sz' BIndet (take sz bs2)).
  { auto using Forall2_resize, BIndet_weak_refine. }
  rewrite resize_ge by auto. apply Forall2_app_l.
  * by rewrite take_length_le by auto.
  * apply Forall2_replicate_l. auto. auto using Forall_true, BIndet_weak_refine.
Qed.
Lemma val_flatten_unflatten Γ m τ bs :
  ✓ Γ → ✓{Γ} τ → ✓{Γ,m}* bs → length bs = bit_size_of Γ τ →
  val_flatten Γ (val_unflatten Γ τ bs) ⊑* bs.
Proof.
  intros HΓ Hτ. revert τ Hτ bs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb ? bs ?. rewrite val_unflatten_base; simpl.
    eauto using base_val_flatten_unflatten.
  * intros τ n Hτ IH _ bs. rewrite val_unflatten_array; simpl.
    rewrite bit_size_of_array. revert bs.
    induction n as [|n IHn]; simpl; intros bs ??.
    { by erewrite nil_length_inv by eauto. }
    apply Forall2_app_l;
      erewrite val_flatten_length by eauto using val_unflatten_typed; auto.
  * intros [] s τs Hs Hτs IH _ bs; erewrite val_unflatten_compound,
      ?bit_size_of_struct by eauto; simpl; intros Hbs Hbs'.
    { rewrite Hs; simpl. clear Hs Hτs. revert bs Hbs Hbs'.
      unfold struct_unflatten. induction (bit_size_of_fields _ τs HΓ)
        as [|τ sz τs szs]; intros bs ??; decompose_Forall_hyps'.
      { by erewrite nil_length_inv by eauto. }
      apply Forall2_app_l; rewrite resize_length;
        eauto using bits_weakly_refine_resize_l. }
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs''; simpl.
    { apply bit_size_of_union in Hs; auto. revert bs' Hbs''.
      induction IH as [|τ τs]; intros bs' Hbs'';
        decompose_Forall_hyps; simplify_option_equality.
      { eauto using Forall2_replicate_l, resize_length, Forall_true. }
      eapply bits_join_min; eauto using bits_weakly_refine_resize_l. }
    auto using Forall2_replicate_l, Forall_true, resize_length.
Qed.
Lemma vals_representable_as_bits_aux Γ m sz vs τs :
  ✓ Γ → ✓{Γ}* τs → Forall (λ τ, bit_size_of Γ τ ≤ sz) τs →
  Forall2 (λ v τ, val_union_free v →
    val_unflatten Γ τ (val_flatten Γ v) = val_freeze true v) vs τs →
  vals_representable Γ m vs τs →
  ∃ bs, bits_list_join sz (val_flatten Γ <$> vs) = Some bs ∧
    ✓{Γ,m}* bs ∧ vs = vals_unflatten Γ τs bs.
Proof.
  intros HΓ Hτs Hsz IH [bs' ? Hlen ->].
  destruct (bits_list_join_exists sz (val_flatten Γ <$> vals_unflatten Γ τs bs')
    (resize sz BIndet bs')) as (bs&Hbs&Hbsbs').
  { by rewrite resize_length. }
  { clear IH. induction Hτs; decompose_Forall_hyps'; constructor; auto.
    eapply bits_weakly_refine_resize_l; eauto; rewrite take_resize_le,
      resize_le by auto; eauto using val_flatten_unflatten. }
  exists bs. split_ands; [done| |].
  { assert ((Γ,m) ⊢* vals_unflatten Γ τs bs' :* τs) as Hτs'
      by auto using vals_unflatten_typed.
    eapply bits_list_join_valid; eauto. clear Hsz IH Hbs Hbsbs'.
    induction Hτs'; decompose_Forall_hyps'; eauto using val_flatten_valid. }
  apply bits_list_join_Some_alt in Hbs.
  induction Hτs as [|τ τs ?? IHτs]; simplify_equality'; auto.
  apply Forall2_cons_inv in IH; destruct IH as [IH IH'].
  apply Forall_cons in Hbs; destruct Hbs as [Hbs Hbs'].
  decompose_Forall_hyps'; f_equal; auto; clear IH' Hbs' IHτs.
  symmetry; apply (val_unflatten_between _ _
    (val_flatten Γ (val_unflatten Γ τ (take (bit_size_of Γ τ) bs')))
    (take (bit_size_of Γ τ) bs) (take (bit_size_of Γ τ) bs')); auto 1.
  * apply (Forall2_take _ _ _ (bit_size_of Γ τ)) in Hbs.
    rewrite take_resize_le, resize_all_alt in Hbs; auto 1.
    by erewrite val_flatten_length by eauto using val_unflatten_typed.
  * apply (Forall2_take _ _ _ (bit_size_of Γ τ)) in Hbsbs'.
    rewrite take_resize_le, resize_le in Hbsbs'; eauto.
  * by erewrite val_flatten_length by eauto using val_unflatten_typed.
  * by erewrite IH, val_unflatten_frozen
      by eauto using val_unflatten_union_free.
Qed.
Lemma val_unflatten_flatten Γ m τ v :
  ✓ Γ → (Γ,m) ⊢ v : τ → val_union_free v →
  val_unflatten Γ τ (val_flatten Γ v) = val_freeze true v.
Proof.
  intros HΓ. revert v τ. refine (val_typed_ind _ _ _ _ _ _ _ _).
  * intros vb τb ? _. rewrite val_unflatten_base; f_equal'.
    eauto using base_val_unflatten_flatten.
  * intros vs τ ? IH _; inversion_clear 1.
    rewrite val_unflatten_array; f_equal'.
    induction IH; decompose_Forall_hyps';
      rewrite ?take_app_alt, ?drop_app_alt by auto; f_equal; auto.
  * intros s vs τs Hs Hvs IH; inversion_clear 1.
    erewrite val_unflatten_compound by eauto; simpl; rewrite Hs; f_equal'.
    unfold struct_unflatten. clear Hs. revert dependent vs.
    induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
      rewrite ?take_app_alt, ?drop_app_alt; f_equal; auto.
    rewrite take_resize_le, resize_all_alt by auto; auto.
  * intros s i τs v τ Hs Hτs Hv IH. inversion_clear 1.
  * intros s vs τs Hs Hvs IH Hrepr _.
    erewrite val_unflatten_compound by eauto; simpl.
    destruct (vals_representable_as_bits_aux Γ m
      (bit_size_of Γ (unionT s)) vs τs) as (bs&->&?&->);
      eauto using bit_size_of_union; simpl.
    by erewrite vals_unflatten_frozen by eauto.
Qed.
Lemma vals_representable_as_bits Γ m sz vs τs :
  ✓ Γ → ✓{Γ}* τs → Forall (λ τ, bit_size_of Γ τ ≤ sz) τs →
  vals_representable Γ m vs τs →
  ∃ bs, bits_list_join sz (val_flatten Γ <$> vs) = Some bs ∧ length bs = sz ∧
    ✓{Γ,m}* bs ∧ vs = vals_unflatten Γ τs bs.
Proof.
  intros ??? Hvs. destruct (vals_representable_as_bits_aux Γ m sz vs τs)
    as (?&?&?&?); eauto 6 using bits_list_join_length.
  apply vals_representable_typed in Hvs; auto.
  elim Hvs; constructor; eauto using val_unflatten_flatten.
Qed.

(** ** Properties of the [val_new] function *)
Lemma val_new_base Γ τb :
  val_new Γ τb = VBase (if decide (τb = voidT%BT) then VVoid else VIndet τb).
Proof. unfold val_new. by rewrite type_iter_base. Qed.
Lemma val_new_array Γ τ n :
  val_new Γ (τ.[n]) = VArray τ (replicate n (val_new Γ τ)).
Proof. unfold val_new. by rewrite type_iter_array. Qed.
Lemma val_new_compound Γ c s τs :
  ✓ Γ → Γ !! s = Some τs → val_new Γ (compoundT{c} s) =
    match c with
    | Struct_kind => VStruct s (val_new Γ <$> τs)
    | Union_kind => VUnionAll s (val_new Γ <$> τs)
    end.
Proof.
  intros HΓ Hs. unfold val_new; erewrite (type_iter_compound (=)); try done.
  { by intros ????? ->. }
  clear s τs Hs. intros ?? [] ? τs ???; f_equal'; by apply Forall_fmap_ext.
Qed.
Lemma val_new_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → val_new Γ1 τ = val_new Γ2 τ.
Proof.
  intros. apply (type_iter_weaken (=)); try done; [by intros ????? ->|].
  intros go1 go2 [] s τs Hs Hτs ?; f_equal'; by apply Forall_fmap_ext.
Qed.
Lemma val_new_unflatten Γ τ :
  ✓ Γ → ✓{Γ} τ →
  val_new Γ τ = val_unflatten Γ τ (replicate (bit_size_of Γ τ) BIndet).
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb ?. rewrite val_new_base, val_unflatten_base.
    case_decide; subst; [done|].
    by rewrite base_val_unflatten_indet by auto using Forall_replicate_eq.
  * intros τ n _ IH _.
    rewrite val_new_array, val_unflatten_array, bit_size_of_array. f_equal.
    induction n as [|n IHn]; f_equal'.
    + rewrite take_replicate, IH. do 2 f_equal; lia.
    + rewrite drop_replicate, IHn. do 2 f_equal; lia.
  * intros [] s τs Hs _ IH _;  erewrite val_new_compound,
      val_unflatten_compound, ?bit_size_of_struct by eauto; f_equal.
    { unfold struct_unflatten. clear Hs.
      induction (bit_size_of_fields _ τs HΓ); decompose_Forall_hyps'; f_equal.
      + rewrite replicate_plus, take_app_alt,
          take_replicate, Min.min_l by auto; auto.
      + rewrite replicate_plus, drop_app_alt by auto; auto. }
    pose proof (bit_size_of_union _ _ _ HΓ Hs); clear Hs.
    induction IH as [|τ τs Hτ IH]; decompose_Forall_hyps'; f_equal; auto.
    rewrite take_replicate, Hτ. do 2 f_equal; lia.
Qed.
Lemma val_new_typed Γ m τ : ✓ Γ → ✓{Γ} τ → (Γ,m) ⊢ val_new Γ τ : τ.
Proof.
  intros. rewrite val_new_unflatten by done.
  apply val_unflatten_typed; auto using replicate_length.
Qed.
Lemma val_new_type_of Γ τ : ✓ Γ → ✓{Γ} τ → type_of (val_new Γ τ) = τ.
Proof.
  intros. rewrite val_new_unflatten by done. by apply val_unflatten_type_of.
Qed.
Lemma val_new_frozen Γ τ :
  ✓ Γ → ✓{Γ} τ → val_freeze true (val_new Γ τ) = val_new Γ τ.
Proof.
  intros. rewrite val_new_unflatten by done.
  apply (val_unflatten_frozen Γ ∅); auto.
Qed.
Lemma val_new_union_free Γ τ : ✓ Γ → ✓{Γ} τ → val_union_free (val_new Γ τ).
Proof.
  intros. rewrite val_new_unflatten by done.
  eauto using val_unflatten_union_free.
Qed.

(** ** Properties of the [val_0] function *)
Lemma val_0_base Γ τb : val_0 Γ τb = VBase (base_val_0 τb).
Proof. unfold val_0. by rewrite type_iter_base. Qed.
Lemma val_0_array Γ τ n :
  val_0 Γ (τ.[n]) = VArray τ (replicate n (val_0 Γ τ)).
Proof. unfold val_0. by rewrite type_iter_array. Qed.
Lemma val_0_compound Γ c s τs :
  ✓ Γ → Γ !! s = Some τs → val_0 Γ (compoundT{c} s) =
    match c with
    | Struct_kind => VStruct s (val_0 Γ <$> τs)
    | Union_kind => VUnion s 0 (default (VUnionAll s []) (τs !! 0) (val_0 Γ))
    end.
Proof.
  intros HΓ Hs. unfold val_0; erewrite (type_iter_compound (=)); try done.
  { by intros ????? ->. }
  clear s τs Hs. intros ?? [] ? τs ?? Hgo; f_equal'; [|by destruct Hgo].
  by apply Forall_fmap_ext.
Qed.
Lemma val_0_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → val_0 Γ1 τ = val_0 Γ2 τ.
Proof.
  intros. apply (type_iter_weaken (=)); try done; [by intros ????? ->|].
  intros ?? [] ? τs ?? Hgo; f_equal'; [|by destruct Hgo].
  by apply Forall_fmap_ext.
Qed.
Lemma val_0_typed Γ m τ : ✓ Γ → ✓{Γ} τ → (Γ,m) ⊢ val_0 Γ τ : τ.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb. rewrite val_0_base.
    typed_constructor; auto using base_val_0_typed.
  * intros τ n ???. rewrite val_0_array. typed_constructor; auto.
  * intros [] s τs Hs _ IH ?; erewrite val_0_compound by eauto.
    { typed_constructor; eauto. elim IH; csimpl; auto. }
    destruct IH as [|τ τs]; simpl in *; [lia|].
    by typed_constructor; eauto.
Qed.

(** ** Properties of the [to_val] function *)
Lemma to_val_typed Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → (Γ,m) ⊢ to_val Γ w : τ.
Proof.
  intros HΓ. induction 1 using @ctree_typed_ind; simpl.
  * typed_constructor.
    eauto using base_val_unflatten_typed, pbits_tag_valid.
  * typed_constructor; auto using fmap_length. by apply Forall_fmap.
  * typed_constructor; eauto. by apply Forall2_fmap_l.
  * typed_constructor; eauto.
  * eauto using val_unflatten_typed, TCompound_valid, pbits_tag_valid.
Qed.
Lemma to_vals_typed Γ m ws τs :
  ✓ Γ → (Γ,m) ⊢* ws :* τs → (Γ,m) ⊢* to_val Γ <$> ws :* τs.
Proof. induction 2; csimpl; auto using to_val_typed. Qed.
Lemma to_val_type_of Γ w :
  ✓ Γ → ✓{Γ} (type_of w) → type_of (to_val Γ w) = type_of w.
Proof.
  intros HΓ. induction w as [|τ ws IH| | |] using @ctree_ind_alt; simpl; auto.
  * by rewrite base_val_unflatten_type_of.
  * intros. by rewrite val_unflatten_type_of.
Qed.
Lemma to_val_frozen Γ m w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → val_freeze true (to_val Γ w) = to_val Γ w.
Proof.
  induction 2 using @ctree_typed_ind; simpl.
  * by erewrite base_val_unflatten_frozen by eauto using pbits_tag_valid.
  * f_equal. rewrite <-list_fmap_compose. by apply Forall_fmap_ext.
  * f_equal. rewrite <-list_fmap_compose.
    eapply Forall_fmap_ext, Forall2_Forall_l; eauto. eapply Forall_true; eauto.
  * by f_equal.
  * eauto using val_unflatten_frozen, TCompound_valid, pbits_tag_valid.
Qed.
Lemma to_val_union_free Γ w :
  ✓ Γ → union_free w → val_union_free (to_val Γ w).
Proof.
  intros HΓ. by induction 1 using @union_free_ind_alt; simpl;
    try econstructor; eauto using val_unflatten_union_free, TCompound_valid,
    val_new_union_free; decompose_Forall.
Qed.
Lemma to_val_union_free_inv Γ w : val_union_free (to_val Γ w) → union_free w.
Proof.
  induction w as [|ws IH|s wxbss IH| | ] using @ctree_ind_alt;
    simpl; inversion_clear 1; econstructor; eauto.
  * induction IH; decompose_Forall_hyps'; auto.
  * induction IH; decompose_Forall_hyps'; auto.
Qed.
Lemma to_val_unflatten Γ τ xbs :
  ✓ Γ → ✓{Γ} τ → to_val Γ (ctree_unflatten Γ τ xbs)
  = val_unflatten Γ τ (tagged_tag <$> xbs).
Proof.
  intros HΓ Hτ. revert τ Hτ xbs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb _ xbs. by rewrite ctree_unflatten_base, val_unflatten_base.
  * intros τ n _ IH _ xbs.
    rewrite ctree_unflatten_array, val_unflatten_array; f_equal'. revert xbs.
    induction n; intros; f_equal'; rewrite <-?fmap_drop, <-?fmap_take; auto.
  * intros [] s τs Hs _ IH _ xbs; erewrite ctree_unflatten_compound,
      val_unflatten_compound by eauto; f_equal'.
    { unfold struct_unflatten. clear Hs. revert xbs.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        rewrite <-?fmap_drop, <-?fmap_take; f_equal'; auto. }
    by erewrite val_unflatten_compound by eauto.
Qed.

(** ** Properties of the [of_val] function *)
Lemma ctree_flatten_of_val Γ m xs v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → length xs = bit_size_of Γ τ →
  ctree_flatten (of_val Γ xs v) = zip_with PBit xs (val_flatten Γ v).
Proof.
  intros HΓ Hv. revert v τ Hv xs. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * done.
  * intros vs τ Hvs IH _ xs; rewrite bit_size_of_array; revert xs.
    induction IH; intros xs Hxs; decompose_Forall_hyps';
      erewrite ?zip_with_nil_r, ?type_of_correct,
      ?zip_with_app_r, ?val_flatten_length by eauto; f_equal; auto.
  * intros s vs τs Hs Hvs IH xs.
    erewrite Hs, bit_size_of_struct, fmap_type_of by eauto; simpl.
    unfold field_bit_padding. clear Hs. revert vs Hvs IH xs.
    induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
      erewrite ?zip_with_nil_r, ?type_of_correct, ?resize_ge,
      <-?(associative_L (++)), ?zip_with_app_r, ?val_flatten_length,
      ?replicate_length, ?zip_with_replicate_r by eauto; repeat f_equal; auto.
  * intros s i τs v τ ??? IH xs ?. erewrite type_of_correct, resize_ge,
      zip_with_app_r, val_flatten_length, zip_with_replicate_r by eauto.
    f_equal; auto.
  * done.
Qed.
Lemma of_val_unshared Γ m xs v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → length xs = bit_size_of Γ τ → Forall sep_unshared xs →
  Forall (not ∘ sep_unmapped) xs → ctree_unshared (of_val Γ xs v).
Proof.
  intros. erewrite ctree_flatten_of_val by eauto. eauto using PBits_unshared.
Qed.
Lemma of_val_mapped Γ m xs v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → length xs = bit_size_of Γ τ →
  Forall (not ∘ sep_unmapped) xs →
  ctree_Forall (not ∘ sep_unmapped) (of_val Γ xs v).
Proof.
  intros. erewrite ctree_flatten_of_val by eauto. eauto using PBits_mapped.
Qed.
Lemma of_val_typed Γ m xs v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → length xs = bit_size_of Γ τ → Forall sep_valid xs →
  Forall (not ∘ sep_unmapped) xs → (Γ,m) ⊢ of_val Γ xs v : τ.
Proof.
  intros HΓ Hv. revert v τ Hv xs. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros vb τb ? xs ???. erewrite type_of_correct by eauto.
    typed_constructor.
    + eauto using base_val_typed_type_valid.
    + eauto using PBits_valid, base_val_flatten_valid.
    + erewrite zip_with_length, base_val_flatten_length by eauto; lia.
  * intros vs τ Hvs IH Hvs' xs. rewrite bit_size_of_array; intros Hlen  Hxs Hxs'.
    typed_constructor; trivial.
    + clear Hvs Hvs' Hxs Hxs' Hlen IH. revert xs.
      induction vs; intros; f_equal'; auto.
    + revert xs Hxs Hxs' Hlen. clear Hvs'. induction IH; intros;
        decompose_Forall_hyps'; erewrite ?type_of_correct by eauto;
        constructor; auto.
  * intros s vs τs Hs Hvs IH xs.
    erewrite bit_size_of_struct, fmap_type_of by eauto; intros Hlen Hxs Hxs'.
    typed_constructor; eauto; clear Hs; unfold field_bit_padding.
    + revert vs xs Hvs IH Hxs Hxs' Hlen.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        erewrite ?type_of_correct by eauto; constructor; simpl; auto.
    + clear IH. revert vs xs Hvs Hxs Hxs' Hlen.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        erewrite ?type_of_correct by eauto; constructor; simpl; auto.
      erewrite <-zip_with_replicate_r by eauto; eauto 7 using PBits_valid.
    + clear Hxs Hxs' Hlen IH. revert xs vs Hvs.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        constructor; simpl; eauto using PBits_indetify.
    + clear Hxs Hxs' IH. revert vs xs Hvs Hlen.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        erewrite ?type_of_correct by eauto; f_equal; auto.
  * intros. erewrite type_of_correct by eauto. typed_constructor; eauto.
    + erewrite <-zip_with_replicate_l, zip_with_flip by eauto.
      auto using PBits_valid.
    + auto using PBits_indetify.
    + rewrite fmap_length; solve_length.
    + intros [Hc _]. eapply (ctree_Forall_not sep_unmapped Γ m
        (of_val Γ (take (bit_size_of Γ τ) xs) v)); eauto using of_val_mapped.
  * intros s vs τs Hs Hvs IH Hrep xs ???.
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs'; simpl.
    { typed_constructor; eauto.
      + eauto using PBits_valid, val_union_to_bits_valid.
      + erewrite zip_with_length, bits_list_join_length by eauto; auto; lia. }
    typed_constructor; eauto using PBits_valid.
Qed.
Lemma of_val_type_of Γ xs v : type_of (of_val Γ xs v) = type_of v.
Proof.
  destruct v as [|? vs _| | |] using val_ind_alt;
    simplify_equality'; rewrite ?fmap_length; f_equal; auto.
  revert xs; induction vs; intros; f_equal'; auto.
Qed.
Lemma to_of_val Γ m xs v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → length xs = bit_size_of Γ τ →
  to_val Γ (of_val Γ xs v) = val_freeze true v.
Proof.
  intros HΓ Hvτ. revert v τ Hvτ xs.
  refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros. by erewrite type_of_correct, fmap_zip_with_r,
      base_val_unflatten_flatten by eauto.
  * intros vs τ Hvs IH _ xs; rewrite bit_size_of_array; intros Hxs; f_equal.
    revert xs Hxs. induction IH; intros; decompose_Forall_hyps';
      erewrite ?type_of_correct by eauto; f_equal; auto.
  * intros s vs τs Hs Hvs IH xs; erewrite fmap_type_of,
      bit_size_of_struct by eauto; intros Hxs; f_equal.
    revert vs xs Hvs IH Hxs. unfold field_bit_padding. clear Hs.
    induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
      erewrite ?type_of_correct by eauto; f_equal; eauto.
  * intros; erewrite type_of_correct by eauto; f_equal; auto.
  * intros s vs τs Hs Hvs IH Hrepr xs ?.
    destruct (vals_representable_as_bits Γ m (bit_size_of Γ (unionT s)) vs τs)
     as (bs&->&?&?&Hbs); simpl; eauto using bit_size_of_union.
    by erewrite fmap_zip_with_r,
      val_unflatten_compound, Hbs, vals_unflatten_frozen by eauto.
Qed.
Lemma of_val_union_free Γ xs v :
  val_union_free v → union_free (of_val Γ xs v).
Proof.
  intros Hv. revert xs. induction Hv as [|? vs _ IH|s vs _ IH|]
    using @val_union_free_ind_alt; intros xs; simpl; econstructor; eauto.
  * revert xs. induction IH; simpl; constructor; auto.
  * generalize (field_bit_padding Γ (type_of <$> vs)). revert xs.
    induction IH; intros ? [|??]; constructor; simpl; auto.
Qed.
Lemma of_val_union_free_inv Γ m xs v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → length xs = bit_size_of Γ τ →
  union_free (of_val Γ xs v) → val_union_free v.
Proof.
  intros. erewrite <-(val_union_free_freeze true),
    <-(to_of_val _ _ xs) by eauto. by apply to_val_union_free.
Qed.
Lemma of_val_disjoint Γ m w1 w2 v τ :
  ✓ Γ → (Γ,m) ⊢ w1 : τ → ctree_unshared w1 →
  ctree_Forall (not ∘ sep_unmapped) w1 → (Γ,m) ⊢ v : τ → w1 ⊥ w2 →
  of_val Γ (tagged_perm <$> ctree_flatten w1) v ⊥ w2.
Proof.
  intros. assert (ctree_unmapped w2) by eauto using @ctree_unshared_unmapped.
  assert ((Γ,m) ⊢ w2 : τ) by eauto using ctree_disjoint_typed.
  assert (union_free w2)
    by eauto using union_free_unmapped, ctree_typed_sep_valid.
  erewrite <-(union_free_reset w2), <-ctree_unflatten_flatten by eauto.
  assert (Forall (not ∘ sep_unmapped) (tagged_perm <$> ctree_flatten w1)).
  { apply pbits_perm_mapped; eauto using
      Forall_impl, ctree_flatten_valid, pbit_valid_sep_valid. }
  symmetry; eapply ctree_flatten_unflatten_disjoint; eauto using
    of_val_typed, pbits_valid_perm_valid, ctree_flatten_valid; symmetry.
  erewrite ctree_flatten_of_val by eauto.
  eauto using PBits_perm_disjoint, @ctree_flatten_disjoint.
Qed.
Lemma of_val_union_help Γ m xs1 xs2 v τ :
  ✓ Γ → (Γ,m) ⊢ v : τ → Forall sep_valid xs1 → Forall (not ∘ sep_unmapped) xs1 →
  length xs1 = bit_size_of Γ τ → of_val Γ (xs1 ∪* xs2) v
  = ctree_merge true (∪) (of_val Γ xs1 v) (flip PBit BIndet <$> xs2).
Proof.
  intros HΓ Hv. revert v τ Hv xs1 xs2.
  refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros; f_equal; auto using PBits_union.
  * intros vs τ Hvs IH _ xs1 xs2 Hxs1 Hxs1'. rewrite bit_size_of_array.
    intros Hlen; f_equal. revert xs1 xs2 Hxs1 Hxs1' Hlen.
    induction IH; intros; decompose_Forall_hyps'; simplify_type_equality; auto.
    erewrite zip_with_take, zip_with_drop, <-fmap_take, <-fmap_drop,
      ctree_flatten_length by eauto using of_val_typed; f_equal; auto.
  * intros s vs τs Hs Hvs IH xs1 xs2 Hxs1 Hxs1'.
    erewrite bit_size_of_struct by eauto; intros Hlen; f_equal.
    unfold field_bit_padding; erewrite fmap_type_of by eauto.
    clear Hs. revert vs xs1 xs2 Hvs IH Hxs1 Hxs1' Hlen.
    induction (bit_size_of_fields _ τs HΓ); intros;
      decompose_Forall_hyps'; simplify_type_equality; auto.
    erewrite !zip_with_drop, !zip_with_take, <-!fmap_drop, <-!fmap_take,
      ctree_flatten_length, fmap_length, take_length, drop_length,
      Min.min_l, PBits_BIndet_union by (eauto using of_val_typed; lia);
      repeat f_equal; eauto 6.
  * intros s i τs v τ ??? IH xs1 xs2 ???; simplify_type_equality'.
    by erewrite zip_with_take, zip_with_drop, <-fmap_take, <-fmap_drop, IH,
      ctree_flatten_length, PBits_BIndet_union by eauto using of_val_typed.
  * intros; f_equal; auto using PBits_union.
Qed.
Lemma of_val_union Γ m w1 w2 v τ :
  ✓ Γ → (Γ,m) ⊢ w1 : τ → ctree_unshared w1 →
  ctree_Forall (not ∘ sep_unmapped) w1 → (Γ,m) ⊢ v : τ → w1 ⊥ w2 →
  of_val Γ (tagged_perm <$> ctree_flatten (w1 ∪ w2)) v
  = of_val Γ (tagged_perm <$> ctree_flatten w1) v ∪ w2.
Proof.
  intros. assert (ctree_unmapped w2).
  { eapply seps_unshared_unmapped; eauto using @ctree_flatten_disjoint. }
  assert (Forall (not ∘ sep_unmapped) (tagged_perm <$> ctree_flatten w1)).
  { apply pbits_perm_mapped; eauto using
      Forall_impl, ctree_flatten_valid, pbit_valid_sep_valid. }
  rewrite ctree_flatten_union, pbits_perm_union by done.
  by erewrite of_val_union_help, PBits_BIndet_tag, ctree_merge_flatten
    by eauto using of_val_disjoint, pbits_valid_perm_valid, ctree_flatten_valid.
Qed.

(** ** Decidable typing *)
Local Arguments type_check _ _ _ _ _ !_ /.
Global Instance:
  TypeCheckSpec (env Ti * mem Ti) (type Ti) (val Ti) (✓ ∘ fst).
Proof.
  intros [Γ m] v τ ?; revert v τ. assert (∀ vs τs,
    Forall (λ v, ∀ τ, type_check (Γ,m) v = Some τ → (Γ,m) ⊢ v : τ) vs →
    mapM (type_check (Γ,m)) vs = Some τs → (Γ,m) ⊢* vs :* τs).
  { intros vs τs. rewrite mapM_Some. intros. decompose_Forall; eauto. }
  assert (∀ vs τ,
    (Γ,m) ⊢* vs : τ → Forall (λ v, type_check (Γ,m) v = Some τ) vs →
    mapM (type_check (Γ,m)) vs = Some (replicate (length vs) τ)).
  { intros. apply mapM_Some, Forall2_replicate_r;decompose_Forall_hyps; eauto. }
  intros v τ; split.
  * revert τ. induction v using @val_ind_alt; intros; simplify_option_equality.
    + typed_constructor; auto. by apply type_check_sound.
    + typed_constructor; eauto using @Forall2_Forall_typed.
    + typed_constructor; decompose_Forall_hyps; eauto.
    + typed_constructor; eauto.
    + typed_constructor; eauto. apply vals_unflatten_representable.
      - eapply bits_list_join_valid, Forall_fmap,
          Forall2_Forall_l, Forall_true; eauto using val_flatten_valid.
      - erewrite bits_list_join_length by eauto. eauto using bit_size_of_union.
  * induction 1 using @val_typed_ind; simplify_option_equality.
    + by erewrite type_check_complete by eauto.
    + done.
    + erewrite mapM_Some_2; eauto. by simplify_option_equality.
    + done.
    + erewrite mapM_Some_2; eauto; simplify_option_equality.
      by match goal with
      | _ : Γ !! ?s = Some _, H : vals_representable ?Γ ?m ?vs ?τs |- _ =>
        destruct (vals_representable_as_bits Γ m
          (bit_size_of Γ (unionT s)) vs τs) as (?&?&?&?&->);
          eauto using val_typed_types_valid, bit_size_of_union
      end; simplify_option_equality.
Qed.

(** ** Refinements *)
Lemma val_refine_typed_l Γ f m1 m2 v1 v2 τ :
  ✓ Γ → v1 ⊑{Γ,f@m1↦m2} v2 : τ → (Γ,m1) ⊢ v1 : τ.
Proof.
  intros ?. revert v1 v2 τ. refine (val_refine_ind _ _ _ _ _ _ _ _ _ _ _).
  * intros; typed_constructor; eauto using base_val_refine_typed_l.
  * intros τ n vs1 vs2 Hn _ IH ?; typed_constructor; auto. elim IH; eauto.
  * intros s τs vs1 vs2 Hs _ IH; typed_constructor; eauto. elim IH; eauto.
  * intros; typed_constructor; eauto.
  * intros s τs vs1 vs2 ? _ IH ? _. typed_constructor; eauto. elim IH; auto.
  * intros; typed_constructor; eauto.
Qed.
Lemma vals_refine_typed_l Γ f m1 m2 vs1 vs2 τs :
  ✓ Γ → vs1 ⊑{Γ,f@m1↦m2}* vs2 :* τs → (Γ,m1) ⊢* vs1 :* τs.
Proof. induction 2; eauto using val_refine_typed_l. Qed.
Lemma val_refine_typed_r Γ f m1 m2 v1 v2 τ :
  ✓ Γ → v1 ⊑{Γ,f@m1↦m2} v2 : τ → (Γ,m2) ⊢ v2 : τ.
Proof.
  intros ?. revert v1 v2 τ. refine (val_refine_ind _ _ _ _ _ _ _ _ _ _ _).
  * intros; typed_constructor; eauto using base_val_refine_typed_r.
  * intros τ n vs1 vs2 <- _ IH ?; typed_constructor;
      eauto using Forall2_length. elim IH; auto.
  * intros s τs vs1 vs2 Hs _ IH; typed_constructor; eauto. elim IH; eauto.
  * intros; typed_constructor; eauto.
  * intros s τs vs1 vs2 ? _ IH _ ?. typed_constructor; eauto. elim IH; auto.
  * intros; typed_constructor; eauto using vals_representable_typed.
Qed.
Lemma val_refine_type_of_l Γ f m1 m2 v1 v2 τ :
  v1 ⊑{Γ,f@m1↦m2} v2 : τ → type_of v1 = τ.
Proof. destruct 1; f_equal'; eauto using base_val_refine_type_of_l. Qed.
Lemma vals_refine_type_of_l Γ f m1 m2 vs1 vs2 τs :
  ✓ Γ → vs1 ⊑{Γ,f@m1↦m2}* vs2 :* τs → type_of <$> vs1 = τs.
Proof. induction 2; f_equal'; eauto using val_refine_type_of_l. Qed.
Lemma val_refine_type_of_r Γ f m1 m2 v1 v2 τ :
  v1 ⊑{Γ,f@m1↦m2} v2 : τ → type_of v2 = τ.
Proof.
  destruct 1; f_equal'; eauto using base_val_refine_type_of_r, Forall2_length_l.
Qed.
Lemma vals_refine_type_of_r Γ f m1 m2 vs1 vs2 τs :
  ✓ Γ → vs1 ⊑{Γ,f@m1↦m2}* vs2 :* τs → type_of <$> vs2 = τs.
Proof. induction 2; f_equal'; eauto using val_refine_type_of_r. Qed.
Lemma val_refine_id Γ m v τ : (Γ,m) ⊢ v : τ → v ⊑{Γ@m} v : τ.
Proof.
  revert v τ. refine (val_typed_ind _ _ _ _ _ _ _ _).
  * intros. refine_constructor; eauto using base_val_refine_id.
  * intros vs τ _ IH ?. refine_constructor; eauto. elim IH; auto.
  * intros s vs τs ? _ IH. refine_constructor; eauto.
    elim IH; constructor; auto.
  * intros. refine_constructor; eauto.
  * intros s vs τs ? _ IH ?. refine_constructor; eauto.
    elim IH; constructor; auto.
Qed.
Lemma val_refine_compose Γ f g m1 m2 m3 v1 v2 v3 τ :
  ✓ Γ → v1 ⊑{Γ,f@m1↦m2} v2 : τ → v2 ⊑{Γ,g@m2↦m3} v3 : τ →
  v1 ⊑{Γ,f ◎ g@m1↦m3} v3 : τ.
Proof.
  intros HΓ. assert (∀ vs1 vs2 vs3 τs,
    Forall3 (λ v1 v2 τ, ∀ v3,
      v2 ⊑{Γ,g@m2↦m3} v3 : τ → v1 ⊑{Γ,f ◎ g@m1↦m3} v3 : τ) vs1 vs2 τs →
    vs2 ⊑{Γ,g@m2↦m3}* vs3 :* τs → vs1 ⊑{Γ,f ◎ g@m1↦m3}* vs3 :* τs).
  { intros vs1 ws2 vs3 τs Hvs. revert vs3.
    induction Hvs; inversion_clear 1; constructor; auto. }
  intros Hv. revert v1 v2 τ Hv v3.
  refine (val_refine_ind _ _ _ _ _ _ _ _ _ _ _).
  * intros vb1 vb2 τb ? v3 Hv3; pattern v3;
      apply (val_refine_inv_l _ _ _ _ _ _ _ _ Hv3); clear v3 Hv3.
    intros vb3 ?. refine_constructor; eauto using base_val_refine_compose.
  * intros τ n vs1 vs2 <- _ IH Hlen v3 Hv3; pattern v3;
      apply (val_refine_inv_l _ _ _ _ _ _ _ _ Hv3); clear v3 Hv3.
    intros vs3 Hvs3. refine_constructor; eauto.
    revert vs3 Hvs3. clear Hlen. induction IH; inversion_clear 1; auto.
  * intros s τs vs1 vs2 Hs _ IH v3 Hv3; pattern v3;
      apply (val_refine_inv_l _ _ _ _ _ _ _ _ Hv3); clear v3 Hv3.
    intros ? vs3 ? Hvs3; simplify_equality. refine_constructor; eauto.
  * intros s τs i v1 v2 τ ?? _ IH v3 Hv3; pattern v3;
      apply (val_refine_inv_l _ _ _ _ _ _ _ _ Hv3); clear v3 Hv3;
      intros; simplify_equality; refine_constructor; eauto.
  * intros s τs vs1 vs2 Hs _ IH ?? v3 Hv3; pattern v3;
      apply (val_refine_inv_l _ _ _ _ _ _ _ _ Hv3); clear v3 Hv3.
    intros ? vs3 ? Hvs3 ??; simplify_equality. refine_constructor; eauto.
  * intros s τs i v1 v2 τ vs2 Hs Hτ Hv2 _ IH Hvs2' v3 Hv3; pattern v3;
      apply (val_refine_inv_l _ _ _ _ _ _ _ _ Hv3); clear v3 Hv3.
    intros ? vs3 ? Hvs3 _ Hvs3'; simplify_equality'.
    assert (∃ v3, vs3 !! i = Some v3 ∧ v2 ⊑{Γ,g@m2↦m3} v3 : τ) as (v3&?&?).
    { clear Hs IH Hvs2' Hvs3'. revert i v2 τ Hτ Hv2.
      induction Hvs3; intros [|?] ????; simplify_equality'; eauto. }
    refine_constructor; eauto.
Qed.
Lemma val_flatten_refine Γ f m1 m2 v1 v2 τ :
  ✓ Γ → v1 ⊑{Γ,f@m1↦m2} v2 : τ →
  val_flatten Γ v1 ⊑{Γ,f@m1↦m2}* val_flatten Γ v2.
Proof.
  intros ?. revert v1 v2 τ.
  refine (val_refine_ind _ _ _ _ _ _ _ _ _ _ _); simpl.
  * eauto using base_val_flatten_refine.
  * intros τ n vs1 vs2 <- _ ? _. by apply Forall2_bind.
  * intros s τs vs1 vs2 -> _ IH; simpl. generalize (field_bit_sizes Γ τs).
    induction IH; intros [|?]; decompose_Forall_hyps'; auto.
  * eauto.
  * intros s τs vs1 vs2 ?? IH ??.
    destruct (vals_representable_as_bits Γ m1 (bit_size_of Γ (unionT s)) vs1
      τs) as (bs1&Hbs1&?&?&?); eauto using bit_size_of_union.
    destruct (vals_representable_as_bits Γ m2 (bit_size_of Γ (unionT s)) vs2
      τs) as (bs2&Hbs2&?&?&?); eauto using bit_size_of_union.
    rewrite Hbs1, Hbs2; simpl. eapply bits_list_join_refine; eauto.
    elim IH; simpl; constructor; auto.
  * intros s τs i v1 v2 τ vs2 ? Hτ Hv2 ???.
    destruct (vals_representable_as_bits Γ m2 (bit_size_of Γ (unionT s)) vs2
      τs) as (bs2&Hbs2&?&?&?); eauto using bit_size_of_union.
    rewrite Hbs2; simplify_equality'.
    rewrite <-(right_id_L mem_inj_id (◎) f). apply bits_refine_compose with
      m2 (resize (bit_size_of Γ (unionT s)) BIndet (val_flatten Γ v2)); auto.
    rewrite list_lookup_fmap, Hτ in Hv2; simplify_equality'.
    eapply bits_subseteq_refine, bits_weakly_refine_resize_l;
      eauto using val_flatten_unflatten, bit_size_of_union_lookup.
Qed.
Lemma val_unflatten_refine Γ f m1 m2 τ bs1 bs2 :
  ✓ Γ → ✓{Γ} τ → bs1 ⊑{Γ,f@m1↦m2}* bs2 → length bs1 = bit_size_of Γ τ →
  val_unflatten Γ τ bs1 ⊑{Γ,f@m1↦m2} val_unflatten Γ τ bs2 : τ.
Proof.
  intros HΓ Hτ. revert τ Hτ bs1 bs2. refine (type_env_ind _ HΓ _ _ _ _).
  * intros ? τb bs1 bs2 ??. rewrite !val_unflatten_base.
    refine_constructor. by apply base_val_unflatten_refine.
  * intros τ n _ IH Hn bs1 bs2; rewrite !val_unflatten_array, bit_size_of_array.
    intros Hbs Hbs'. refine_constructor; auto using array_unflatten_length.
    revert bs1 bs2 Hbs Hbs'. clear Hn. induction n; simpl; auto.
  * intros [] s τs Hs _ IH _ bs1 bs2; erewrite !val_unflatten_compound,
      ?bit_size_of_struct by eauto; intros Hbs Hbs'.
    { refine_constructor; eauto.
      clear Hs. unfold struct_unflatten. revert bs1 bs2 Hbs Hbs'.
      induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps'; constructor; auto. }
    assert (Forall (λ τ, bit_size_of Γ τ ≤ length bs1) τs).
    { rewrite Hbs'; eauto using bit_size_of_union. }
    refine_constructor; eauto.
    + clear Hbs' Hs. induction IH; decompose_Forall_hyps'; constructor; eauto.
    + apply vals_unflatten_representable; eauto using bits_refine_valid_l.
    + apply vals_unflatten_representable; eauto using bits_refine_valid_r.
      by erewrite <-Forall2_length by eauto.
Qed.
Lemma val_new_refine Γ f m1 m2 τ :
  ✓ Γ → ✓{Γ} τ → val_new Γ τ ⊑{Γ,f@m1↦m2} val_new Γ τ : τ.
Proof.
  intros. rewrite val_new_unflatten by done.
  eauto using val_unflatten_refine, replicate_length.
Qed.
Lemma to_val_refine Γ f m1 m2 w1 w2 τ :
  ✓ Γ → w1 ⊑{Γ,f@m1↦m2} w2 : τ → to_val Γ w1 ⊑{Γ,f@m1↦m2} to_val Γ w2 : τ.
Proof.
  (* Induction on the typing judgment because the IH is otherwise not
     strong enough in the [Union_UnionAll] case *)
  intros HΓ Hw. assert ((Γ,m1) ⊢ w1 : τ) as Hw1
    by eauto using ctree_refine_typed_l.
  revert w1 τ Hw1 f m2 w2 Hw. refine (ctree_typed_ind _ _ _ _ _ _ _ _).
  * intros τb xbs ??? f m2 w2 Hw2; pattern w2;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw2); simpl; clear w2 Hw2.
    refine_constructor; eauto using base_val_unflatten_refine, pbits_tag_refine.
  * intros ws1 τ _ IH Hlen f m2 w2 Hw2; pattern w2;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw2); simpl; clear w2 Hw2.
    intros ws2 Hws. refine_constructor; auto. clear Hlen.
    induction Hws; decompose_Forall_hyps'; constructor; auto.
  * intros s wxbss1 τs Hs ? IH _ _ Hlen f m2 w2 Hw2; pattern w2;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw2); simpl; clear w2 Hw2.
    intros ? wxbss2 ? Hws _ _; simplify_equality.
    refine_constructor; eauto. clear Hlen Hs.
    induction Hws; decompose_Forall_hyps'; constructor; auto.
  * intros s i τs w xbs1 τ ? Hτ ? IH ? _ Hlen _ f m2 w2 Hw2; pattern w2;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw2); simpl; clear w2 Hw2.
    { intros; simplify_equality; refine_constructor; eauto. }
    intros ?? xbs2_ ??; rewrite Forall2_app_inv_l;
      intros (xbs2&xbs2'&?&?&?) ?; decompose_Forall_hyps'.
    erewrite val_unflatten_compound by eauto.
    refine_constructor; eauto; [by rewrite list_lookup_fmap, Hτ| |].
    { rewrite <-(left_id_L _ (◎) f); apply val_refine_compose with
        m1 (val_unflatten Γ τ (tagged_tag <$> ctree_flatten w)); auto.
      { erewrite <-to_val_unflatten,
          ctree_unflatten_flatten by eauto using ctree_typed_type_valid.
        apply IH, union_reset_above;
          eauto using ctree_refine_id, pbits_refine_unshared_inv. }
      rewrite fmap_app, take_app_alt by (by erewrite <-ctree_flatten_length,
        fmap_length by eauto; eauto using Forall2_length).
      eauto using val_unflatten_refine, pbits_tag_refine. }
    eapply vals_unflatten_representable;
      eauto using pbits_tag_valid, pbits_refine_valid_r.
    erewrite fmap_length, app_length, <-Forall2_length,
      ctree_flatten_length, <-Forall2_length by eauto.
    rewrite <-Hlen; eauto using bit_size_of_union.
  * intros s τs xbs ??? f m2 w2 Hw2; pattern w2;
      apply (ctree_refine_inv_l _ _ _ _ _ _ _ _ Hw2); simpl; clear w2 Hw2.
    eauto using val_unflatten_refine, pbits_tag_refine, TCompound_valid.
Qed.
Lemma of_val_refine Γ f m1 m2 xs v1 v2 τ :
  ✓ Γ → Forall sep_unshared xs → Forall (not ∘ sep_unmapped) xs →
  length xs = bit_size_of Γ τ →
  v1 ⊑{Γ,f@m1↦m2} v2 : τ → of_val Γ xs v1 ⊑{Γ,f@m1↦m2} of_val Γ xs v2 : τ.
Proof.
  intros HΓ Hxs Hxs' Hxs'' Hvs. revert v1 v2 τ Hvs xs Hxs Hxs' Hxs''.
  assert (∀ x b, sep_unmapped (PBit x b) → sep_unmapped x) by (by destruct 1).
  refine (val_refine_ind _ _ _ _ _ _ _ _ _ _ _).
  * intros vb1 vb2 ??????; simpl.
    assert ((Γ,m1) ⊢ vb1 : τb) by eauto using base_val_refine_typed_l.
    assert ((Γ,m2) ⊢ vb2 : τb) by eauto using base_val_refine_typed_r.
    simplify_type_equality. refine_constructor; eauto using PBits_refine,
      base_val_flatten_refine, seps_unshared_valid, base_val_typed_type_valid.
  * intros τ n vs1 vs2 <- ? IH Hlen xs Hxs Hxs'; rewrite bit_size_of_array;
      intros Hxs''; simpl; refine_constructor; eauto 2.
    { generalize xs; elim vs1; intros; f_equal'; auto. }
    revert xs Hxs Hxs' Hxs''. clear Hlen. induction IH; intros;
      decompose_Forall_hyps'; erewrite ?val_refine_type_of_l,
      ?val_refine_type_of_r by eauto; constructor; auto.
  * intros s τs vs1 vs2 Hs Hvs IH xs Hxs Hxs'; simpl; erewrite
      bit_size_of_struct, vals_refine_type_of_l, vals_refine_type_of_r by eauto.
    intros Hxs''. refine_constructor; eauto; clear Hs.
    + revert vs1 vs2 xs IH Hvs Hxs Hxs' Hxs''. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ); do 2 inversion_clear 1;
        intros; decompose_Forall_hyps'; erewrite ?val_refine_type_of_l,
        ?val_refine_type_of_r by eauto; constructor; eauto 7.
    + clear IH. revert vs1 vs2 xs Hvs Hxs Hxs' Hxs''. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ); inversion_clear 1;
        intros; decompose_Forall_hyps'; erewrite ?val_refine_type_of_l,
        ?val_refine_type_of_r by eauto; constructor;
        eauto 7 using PBits_BIndet_refine, seps_unshared_valid.
    + clear Hxs Hxs' Hxs'' IH. revert xs vs1 vs2 Hvs. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ); inversion_clear 1;
        constructor; simpl; eauto using PBits_indetify.
    + clear Hxs Hxs' IH. revert vs1 vs2 xs Hvs Hxs''. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ); inversion_clear 1; csimpl; intros;
        erewrite ?val_refine_type_of_l by eauto; f_equal; eauto.
  * intros s τs i v1 v2 ???? IH xs ???; simpl.
    assert ((Γ,m1) ⊢ v1 : τ) by eauto using val_refine_typed_l.
    assert ((Γ,m2) ⊢ v2 : τ) by eauto using val_refine_typed_r.
    simplify_type_equality.
    refine_constructor; eauto using PBits_BIndet_refine.
    + eauto using PBits_BIndet_refine, seps_unshared_valid.
    + eauto using PBits_indetify.
    + solve_length.
    + erewrite ctree_flatten_of_val by eauto. assert (bit_size_of Γ τ ≠ 0).
      { eauto using bit_size_of_ne_0, val_typed_type_valid. }
      assert (length (zip_with PBit (take (bit_size_of Γ τ) xs)
        (val_flatten Γ v1)) ≠ 0) by solve_length.
      intros [? _]; destruct xs, (bit_size_of Γ τ), (val_flatten Γ v1);
        decompose_Forall_hyps'; eauto.
  * intros s τs vs1 vs2 Hs Hvs IH ?? xs ???. refine_constructor; eauto.
    + eapply PBits_refine, val_flatten_refine, VUnionAll_refine;
        auto using seps_unshared_valid; eauto.
    + cut ((Γ,m1) ⊢ VUnionAll s vs1 : unionT s); [intros; solve_length|].
      typed_constructor; eauto using vals_refine_typed_l.
  * intros s τs i v1 v2 τ vs2 Hs Hτ Hv2 Hv12 IH ? xs ???; simpl.
    assert ((Γ,m1) ⊢ v1 : τ) by eauto using val_refine_typed_l.
    simplify_type_equality. destruct (vals_representable_as_bits Γ m2
      (bit_size_of Γ (unionT s)) vs2 τs) as (bs2&->&Hlen&?&->); simpl;
      eauto using bit_size_of_union.
    rewrite list_lookup_fmap, Hτ in Hv2; simplify_equality'.
    refine_constructor; eauto.
    + erewrite ctree_flatten_of_val by eauto using val_refine_typed_l.
      rewrite <-(zip_with_replicate_r _ (bit_size_of Γ (unionT s) -
        bit_size_of Γ τ)), <-zip_with_app, take_drop by auto.
      apply PBits_refine; auto using seps_unshared_valid.
      apply Forall2_app_l;
        [|apply Forall2_replicate_l; eauto using Forall_impl, BIndet_refine].
      rewrite <-(right_id_L _ (◎) f); eapply bits_refine_compose,
        bits_subseteq_refine; eauto using val_flatten_refine.
      erewrite val_flatten_length by eauto.
      eapply val_flatten_unflatten; eauto using val_typed_type_valid.
    + auto using PBits_indetify.
    + apply of_val_typed; auto using seps_unshared_valid.
    + auto using PBits_unshared.
    + solve_length.
    + erewrite ctree_flatten_of_val by eauto. assert (bit_size_of Γ τ ≠ 0).
      { eauto using bit_size_of_ne_0, val_typed_type_valid. }
      assert (length (zip_with PBit (take (bit_size_of Γ τ) xs)
        (val_flatten Γ v1)) ≠ 0) by solve_length.
      intros [? _]; destruct xs, (bit_size_of Γ τ), (val_flatten Γ v1);
        decompose_Forall_hyps'; eauto.
Qed.
Lemma of_val_to_val_refine Γ m x w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ → ctree_Forall (not ∘ sep_unmapped) w →
  of_val Γ (tagged_perm <$> ctree_flatten w) (to_val Γ w) ⊑{Γ@m} w : τ.
Proof.
  intros HΓ. assert (∀ xbs, ✓{Γ,m}* xbs → Forall (not ∘ sep_unmapped) xbs →
    Forall (not ∘ sep_unmapped) (tagged_perm <$> xbs)).
  { eauto using pbits_perm_mapped, Forall_impl, pbit_valid_sep_valid. }
  assert (∀ xbs, ✓{Γ,m}* xbs → Forall sep_valid (tagged_perm <$> xbs)).
  { intros. eapply Forall_fmap, Forall_impl; eauto. by intros ? (?&?&?). }
  assert (∀ xbs, ✓{Γ,m}* xbs →
    Forall (not ∘ sep_unmapped) (tagged_perm <$> xbs) →
    flip PBit BIndet <$> tagged_perm <$> xbs ⊑{Γ@m}* xbs).
  { intros xbs ??. rewrite <-(zip_with_replicate_r _ (length xbs)) by auto.
    pattern xbs at 3; rewrite <-(PBits_perm_tag xbs).
    eapply PBits_refine, bits_subseteq_refine;
      eauto using pbits_tag_valid, base_val_flatten_unflatten.
    eapply Forall2_replicate_l; eauto using Forall_true. }
  revert w τ. refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros τb xbs ????. rewrite base_val_unflatten_type_of by done.
    assert ((Γ,m) ⊢ base_val_unflatten Γ τb (tagged_tag <$> xbs) : τb).
    { eauto using base_val_unflatten_typed, pbits_tag_valid. }
    refine_constructor; eauto 1.
    pattern xbs at 3; rewrite <-(PBits_perm_tag xbs).
    eapply PBits_refine, bits_subseteq_refine;
      eauto using pbits_tag_valid, base_val_flatten_unflatten.
  * intros ws τ Hws IH Hlen ?. refine_constructor; eauto 1.
    + clear Hlen IH. induction Hws; decompose_Forall_hyps'; f_equal';
        erewrite ?type_of_correct, ?fmap_app, ?drop_app_alt
        by eauto using to_val_typed; auto.
    + clear Hlen. induction IH; decompose_Forall_hyps';
        erewrite ?type_of_correct, ?fmap_app, ?take_app_alt, ?drop_app_alt
        by eauto using to_val_typed; auto.
  * intros s wxbss τs Hs Hws IH Hxbss Hindet Hlen ?. rewrite list_fmap_compose.
    erewrite fmap_type_of by (eapply to_vals_typed, Forall2_fmap_l; eauto).
    refine_constructor; eauto; clear Hs.
    + clear Hxbss Hindet. revert dependent wxbss. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        erewrite ?type_of_correct, ?fmap_app, <-?(associative_L (++)),
          ?take_app_alt, ?drop_app_alt by eauto using to_val_typed;
        constructor; auto.
    + clear IH Hindet. revert dependent wxbss. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        erewrite ?type_of_correct, ?fmap_app, <-?(associative_L (++)),
          ?drop_app_alt, ?take_app_alt by eauto using to_val_typed;
        constructor; simpl; auto.
    + clear IH Hindet Hxbss. revert dependent wxbss. unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps';
        erewrite ?type_of_correct, ?fmap_app, <-?(associative_L (++)),
          ?drop_app_alt by eauto using to_val_typed; f_equal'; auto.
  * intros s i τs w xbs τ Hs Hτs Hw IH ?? Hlen ??; decompose_Forall_hyps'.
    erewrite type_of_correct by eauto using to_val_typed.
    refine_constructor; eauto.
    + rewrite fmap_app, take_app_alt by auto; auto.
    + rewrite fmap_app, drop_app_alt by auto; auto.
    + solve_length.
    + rewrite !fmap_app, take_app_alt, drop_app_alt by auto. intros [? _].
      apply (ctree_Forall_not sep_unmapped Γ m w τ);
        eauto using ctree_refine_Forall, pbit_refine_unmapped.
  * intros s τs xbs Hs Hxbs Hlen ?.
    erewrite val_unflatten_compound by eauto; simpl.
    destruct (vals_representable_as_bits Γ m (bit_size_of Γ (unionT s))
      (vals_unflatten Γ τs (tagged_tag <$> xbs)) τs) as (bs'&Hbs'&?&?&?);
      eauto using bit_size_of_union.
    { apply vals_unflatten_representable; eauto using pbits_tag_valid.
      rewrite fmap_length, Hlen. eauto using bit_size_of_union. }
    rewrite Hbs'; simpl. refine_constructor; eauto 1.
    pattern xbs at 2; rewrite <-(PBits_perm_tag xbs).
    eapply PBits_refine, bits_subseteq_refine; eauto using pbits_tag_valid.
    eapply (bits_list_join_min (bit_size_of Γ (unionT s)));
      eauto using resize_length.
    assert (✓{Γ}* τs) as Hτs_valid by eauto.
    apply bit_size_of_union in Hs; auto. clear Hbs'.
    induction Hτs_valid; decompose_Forall_hyps'; constructor;
      eauto using bits_weakly_refine_resize_l,
      val_flatten_unflatten, pbits_tag_valid.
Qed.
Lemma of_val_to_val_refine_unflatten_flatten Γ m x w τ :
  ✓ Γ → (Γ,m) ⊢ w : τ →
  ctree_Forall (not ∘ sep_unmapped) w → ctree_Forall sep_unshared w →
  of_val Γ (tagged_perm <$> ctree_flatten w) (to_val Γ w)
  ⊑{Γ@m} ctree_unflatten Γ τ (ctree_flatten w) : τ.
Proof.
  intros. erewrite ctree_unflatten_flatten by eauto.
  apply (ctree_refine_compose _ mem_inj_id mem_inj_id m m) with w;
    eauto using of_val_to_val_refine, union_reset_above, ctree_refine_id.
Qed.

(** ** Properties of lookup *)
Lemma val_lookup_nil : lookup (A:=val Ti) [] = Some.
Proof. done. Qed.
Lemma val_lookup_cons rs r : lookup (rs :: r) = λ v, v !! r ≫= (!! rs).
Proof. done. Qed.
Lemma val_lookup_app v r1 r2 : v !! (r1 ++ r2) = v !! r2 ≫= (!! r1).
Proof.
  induction r1 as [|rs1 r1 IH]; simpl.
  * by destruct (v !! r2).
  * by rewrite !val_lookup_cons, IH, option_bind_assoc.
Qed.
Lemma val_lookup_snoc v r rs : v !! (r ++ [rs]) = v !! rs ≫= (!! r).
Proof. apply val_lookup_app. Qed.
Lemma val_lookup_seg_freeze q rs : lookup (A:=val Ti) (freeze q rs) = lookup rs.
Proof. by destruct rs. Qed.
Lemma val_lookup_freeze q r : lookup (A:=val Ti) (freeze q <$> r) = lookup r.
Proof.
  induction r as [|rs r IH]; csimpl; [done|].
  by rewrite !val_lookup_cons, val_lookup_seg_freeze, IH.
Qed.
Lemma val_lookup_seg_Some Γ m v τ rs v' :
  ✓ Γ → (Γ,m) ⊢ v : τ → v !! rs = Some v' →
  ∃ σ, Γ ⊢ rs : τ ↣ σ ∧ (Γ,m) ⊢ v' : σ.
Proof.
  intros ?. destruct 1 as [|vs τ n _|s vs τs ? Hvs _|s j τs v τ
    |s vs τs ?? _ [bs ?? ->]] using @val_typed_ind;
    destruct rs as [i|i|i]; intros Hlookup; simplify_option_equality.
  * exists τ. split.
    + constructor; eauto using lookup_lt_Some.
    + eapply (Forall_lookup (λ v, (Γ,m) ⊢ v : τ)); eauto.
  * destruct (Forall2_lookup_l _ _ _ i v' Hvs) as (σ&?&?); eauto.
    exists σ; split; [|done]. econstructor; eauto.
  * exists τ; split; [|done]. econstructor; eauto.
  * apply list_lookup_fmap_inv in Hlookup; destruct Hlookup as (τ&->&?).
    decompose_Forall_hyps'. exists τ; split; [econstructor; eauto|].
    eauto using val_unflatten_typed.
Qed.
Lemma val_lookup_Some Γ m v τ r v' :
  ✓ Γ → (Γ,m) ⊢ v : τ → v !! r = Some v' →
  ∃ σ, Γ ⊢ r : τ ↣ σ ∧ (Γ,m) ⊢ v' : σ.
Proof.
  intros ?. revert v τ.
  induction r as [|rs r IH] using rev_ind; intros v τ Hvτ Hr.
  { simplify_equality. exists τ; split; [econstructor |]; eauto. }
  rewrite val_lookup_snoc in Hr.
  destruct (v !! rs) as [v''|] eqn:Hv''; simplify_equality'.
  destruct (val_lookup_seg_Some Γ m v τ rs v'') as (σ''&?&?); auto.
  destruct (IH v'' σ'') as (σ&?&?); auto.
  exists σ; split; [eapply ref_typed_snoc|]; eauto.
Qed.
Lemma val_lookup_seg_typed Γ m v τ rs v' σ :
  ✓ Γ → (Γ,m) ⊢ v : τ → v !! rs = Some v' → Γ ⊢ rs : τ ↣ σ → (Γ,m) ⊢ v' : σ.
Proof.
  intros. by destruct (val_lookup_seg_Some Γ m v τ rs v')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma val_lookup_typed Γ m v τ r v' σ :
  ✓ Γ → (Γ,m) ⊢ v : τ → v !! r = Some v' → Γ ⊢ r : τ ↣ σ → (Γ,m) ⊢ v' : σ.
Proof.
  intros. by destruct (val_lookup_Some Γ m v τ r v')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma to_val_lookup_seg Γ w rs w' :
  ✓Γ → w !!{Γ} rs = Some w' → frozen rs → to_val Γ w !! rs = Some (to_val Γ w').
Proof.
  intros ? Hr. destruct w; destruct rs; pattern w';
    apply (ctree_lookup_seg_inv _ _ _ _ _ Hr); intros; simplify_option_equality.
  * rewrite list_lookup_fmap. by simplify_option_equality.
  * rewrite list_lookup_fmap. by simplify_option_equality.
  * done.
  * erewrite val_unflatten_compound, to_val_unflatten by eauto.
    by simplify_option_equality;
      rewrite list_lookup_fmap, fmap_take; simplify_option_equality.
Qed.
Lemma to_val_lookup Γ w r w' :
  ✓ Γ → w !!{Γ} r = Some w' → freeze true <$> r = r →
  to_val Γ w !! r = Some (to_val Γ w').
Proof.
  intros ?. revert w. induction r using rev_ind; intros w.
  { by rewrite ctree_lookup_nil; intros; simplify_equality. }
  rewrite ctree_lookup_snoc, fmap_app; intros;
    simplify_option_equality; simplify_list_equality.
  erewrite val_lookup_snoc, to_val_lookup_seg by eauto; eauto.
Qed.

(*
Lemma to_val_lookup_seg_inv Γ m w1 τ rs v1 :
  ✓ Γ → (Γ,m) ⊢ w1 : τ → mval_is_full w1 → to_val Γ w1 !! rs = Some v1 →
  ∃ w2, w1 !!{Γ} rs = Some w2 ∧ to_val Γ w2 = v1.
Proof.
  destruct 2 using @mtyped_case; inversion_clear 1; destruct rs; intros;
    repeat match goal with
    | _ => done
    | H: (_ <$> _) !! _ = Some _ |- _ => rewrite list_lookup_fmap in H
    | H: context [length (_ <$> _) ] |- _ => rewrite fmap_length in H
    | H : context [val_unflatten _ (unionT ?s) _], _ : _ !! ?s = Some ?τs |- _ =>
       rewrite (val_unflatten_compound _ _ _ τs) in H by done
    | _ => progress simplify_option_equality
    end; eauto using to_val_unflatten.
Qed.
Lemma to_val_lookup_inv Γ m w1 τ r v1 :
  ✓ Γ → (Γ,m) ⊢ w1 : τ → mval_is_full w1 → to_val Γ w1 !! r = Some v1 →
  ∃ w2, w1 !!{Γ} r = Some w2 ∧ to_val Γ w2 = v1.
Proof.
  intros ?. revert w1 τ.
  induction r as [|rs r IH] using rev_ind; intros w1 τ ??.
  { rewrite val_lookup_nil; intros; simplify_equality. by exists w1. }
  rewrite val_lookup_snoc; intros.
  destruct (to_val Γ w1 !! rs) as [v|] eqn:Hv; simplify_equality'.
  destruct (to_val_lookup_seg_inv Γ m w1 τ rs v) as (w2&?&<-); auto.
  destruct (mval_lookup_seg_Some Γ m w1 τ rs w2) as (τ2&?&?); auto.
  destruct (IH w2 τ2) as (w3&?&?); eauto using mval_lookup_seg_perm_full.
  exists w3. rewrite mval_lookup_snoc. by simplify_option_equality.
Qed.
*)
Lemma val_lookup_seg_refine Γ f m1 m2 v1 v2 τ rs v3 :
  ✓ Γ → v1 ⊑{Γ,f@m1↦m2} v2 : τ → v1 !! rs = Some v3 →
  ∃ v4, v2 !! rs = Some v4 ∧ v3 ⊑{Γ,f@m1↦m2} v4 : type_of v3.
Proof.
  intros ?. revert v1 v2 τ. refine (val_refine_ind _ _ _ _ _ _ _ _ _ _ _).
  * by destruct rs.
  * intros τ n vs1 vs2 <- ? _ ??; destruct rs; simplify_option_equality
      by eauto using Forall2_length; decompose_Forall_hyps'.
    erewrite val_refine_type_of_l by eauto; eauto.
  * intros s τs vs1 vs2 ?? _ ?; destruct rs; simplify_option_equality.
    decompose_Forall_hyps. erewrite val_refine_type_of_l by eauto; eauto.
  * intros s τs i v1 v2 τ ??? _ ?; destruct rs; simplify_option_equality.
    erewrite val_refine_type_of_l by eauto; eauto.
  * intros s τs vs1 vs2 ?? _ _ _ ?; destruct rs; simplify_option_equality.
    decompose_Forall_hyps. erewrite val_refine_type_of_l by eauto; eauto.
  * intros s τs i v1 v2 τ vs2 ???? _ _ ?; destruct rs; simplify_option_equality.
    decompose_Forall_hyps. erewrite val_refine_type_of_l by eauto; eauto.
Qed.
Lemma val_lookup_refine Γ f m1 m2 v1 v2 τ r v3 :
  ✓ Γ → v1 ⊑{Γ,f@m1↦m2} v2 : τ → v1 !! r = Some v3 →
  ∃ v4, v2 !! r = Some v4 ∧ v3 ⊑{Γ,f@m1↦m2} v4 : type_of v3.
Proof.
  intros ?. revert v1 v2 τ. induction r as [|rs r IH] using rev_ind; simpl.
  { intros v1 v2 τ ??; simplify_equality'. exists v2.
    by erewrite val_refine_type_of_l by eauto. }
  intros v1 v2 τ. rewrite !val_lookup_snoc; intros; simplify_option_equality.
  edestruct (val_lookup_seg_refine Γ f m1 m2 v1 v2 τ rs) as [? [??]];
    simplify_option_equality; eauto.
Qed.

(** ** Properties of unary/binary operations and casts *)
Definition val_true_false_dec v :
  { val_true v ∧ ¬val_false v } + { ¬val_true v ∧ val_false v }
  + { ¬val_true v ∧ ¬val_false v }.
Proof.
 refine
  match v with
  | VBase vb =>
     match base_val_true_false_dec vb with
     | inleft (left _) => inleft (left _)
     | inleft (right _) => inleft (right _) | inright _ => inright _
     end
  | _ => inright _
  end; abstract naive_solver.
Defined.
Lemma val_true_false v : val_true v → val_false v → False.
Proof. by destruct (val_true_false_dec v) as [[[??]|[??]]|[??]]. Qed.
Global Instance val_unop_ok_dec op v : Decision (val_unop_ok op v).
Proof. destruct v; try apply _. Defined.
Global Instance val_binop_ok_dec Γ m op v1 v2 :
  Decision (val_binop_ok Γ m op v1 v2).
Proof. destruct v1, v2; apply _. Defined.
Global Instance val_cast_ok_dec Γ σ v : Decision (val_cast_ok Γ σ v).
Proof. destruct v, σ as [[]| |]; apply _. Defined.

Lemma unop_type_of_correct op τ σ :
  unop_typed op τ σ ↔ unop_type_of op τ = Some σ.
Proof.
  split.
  * destruct 1; simplify_option_equality.
    by erewrite (proj1 (base_unop_type_of_correct _ _ _)) by eauto.
  * destruct τ; intros; simplify_option_equality; constructor.
    by apply base_unop_type_of_correct.
Qed.
Lemma binop_type_of_correct op τ1 τ2 σ :
  binop_typed op τ1 τ2 σ ↔ binop_type_of op τ1 τ2 = Some σ.
Proof.
  split.
  * destruct 1; simplify_option_equality.
    by erewrite (proj1 (base_binop_type_of_correct _ _ _ _)) by eauto.
  * destruct τ1, τ2; intros; simplify_option_equality; constructor.
    by apply base_binop_type_of_correct.
Qed.
Global Instance cast_typed_dec Γ τ σ : Decision (cast_typed Γ τ σ).
Proof.
 refine
  match τ, σ with
  | baseT τb, baseT σb => cast_if (decide (base_cast_typed Γ τb σb))
  | _, baseT σb => cast_if (decide (σb = voidT%BT))
  | _, _ => right _
  end; try abstract first [by subst; constructor (done)|by inversion 1; subst;
    try match goal with
    | H : ¬base_cast_typed _ _ _ |- _ => destruct H; constructor
    end].
Defined.
Lemma cast_typed_weaken Γ1 Γ2 τ σ :
  cast_typed Γ1 τ σ → Γ1 ⊆ Γ2 → cast_typed Γ2 τ σ.
Proof. destruct 1; constructor; eauto using base_cast_typed_weaken. Qed.

Lemma val_unop_typed Γ m op v τ σ :
  (Γ,m) ⊢ v : τ → unop_typed op τ σ → val_unop_ok op v →
  (Γ,m) ⊢ val_unop op v : σ.
Proof.
  intros Hvτ Hσ Hop. destruct Hσ; inversion Hvτ; simpl; simplify_equality;
    done || constructor; eauto using base_val_unop_typed.
Qed.
Lemma val_binop_ok_weaken Γ1 Γ2 m1 m2 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,m1) ⊢ v1 : τ1 → (Γ1,m1) ⊢ v2 : τ2 → val_binop_ok Γ1 m1 op v1 v2 →
  Γ1 ⊆ Γ2 → (∀ o, index_alive m1 o → index_alive m2 o) →
  val_binop_ok Γ2 m2 op v1 v2.
Proof.
  destruct 2, 1, op; simpl; try done; eauto 2 using base_val_binop_ok_weaken.
Qed.
Lemma val_binop_weaken Γ1 Γ2 m1 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,m1) ⊢ v1 : τ1 → (Γ1,m1) ⊢ v2 : τ2 → Γ1 ⊆ Γ2 →
  val_binop Γ1 op v1 v2 = val_binop Γ2 op v1 v2.
Proof.
  destruct 2, 1, op; intros; f_equal'; eauto 2 using base_val_binop_weaken.
Qed.
Lemma val_binop_typed Γ m op v1 v2 τ1 τ2 σ :
  ✓ Γ → ✓{Γ} m → (Γ,m) ⊢ v1 : τ1 → (Γ,m) ⊢ v2 : τ2 →
  binop_typed op τ1 τ2 σ → val_binop_ok Γ m op v1 v2 →
  (Γ,m) ⊢ val_binop Γ op v1 v2 : σ.
Proof.
  intros ?? Hv1τ Hv2τ Hσ Hop.
  destruct Hσ; inversion Hv1τ; inversion Hv2τ; simplify_equality';
    done || constructor; eauto using base_val_binop_typed.
Qed.
Lemma val_cast_ok_weaken Γ1 Γ2 m1 v τ σ :
  ✓ Γ1 → (Γ1,m1) ⊢ v : τ → val_cast_ok Γ1 σ v → Γ1 ⊆ Γ2 → val_cast_ok Γ2 σ v.
Proof. destruct 2, σ; simpl; eauto using base_val_cast_ok_weaken. Qed.
Lemma val_cast_typed Γ m v τ σ :
  ✓ Γ → (Γ,m) ⊢ v : τ → cast_typed Γ τ σ → val_cast_ok Γ σ v →
  (Γ,m) ⊢ val_cast σ v : σ.
Proof.
  intros ? Hvτ Hσ Hok. destruct Hσ; inversion Hvτ; simplify_equality';
    repeat constructor; eauto using base_val_cast_typed, TVoid_cast_typed.
Qed.

(** ** Refinements of unary/binary operations and casts *)
Lemma val_unop_ok_refine Γ f m1 m2 op v1 v2 τ :
  v1 ⊑{Γ,f@m1↦m2} v2 : τ → val_unop_ok op v1 → val_unop_ok op v2.
Proof. destruct op, 1; simpl; eauto using base_val_unop_ok_refine. Qed.
Lemma val_unop_refine Γ f m1 m2 op v1 v2 τ σ :
  ✓ Γ → unop_typed op τ σ → val_unop_ok op v1 →
  v1 ⊑{Γ,f@m1↦m2} v2 : τ → val_unop op v1 ⊑{Γ,f@m1↦m2} val_unop op v2 : σ.
Proof.
  destruct 2; inversion 2; intros; simplify_equality';
    refine_constructor; eauto using base_val_unop_refine.
Qed.
Lemma val_binop_ok_refine Γ f m1 m2 op v1 v2 v3 v4 τ1 τ3 σ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → binop_typed op τ1 τ3 σ →
  v1 ⊑{Γ,f@m1↦m2} v2 : τ1 → v3 ⊑{Γ,f@m1↦m2} v4 : τ3 →
  val_binop_ok Γ m1 op v1 v3 → val_binop_ok Γ m2 op v2 v4.
Proof.
  unfold val_binop_ok; destruct 3; do 2 inversion 1;
    simplify_equality'; eauto using base_val_binop_ok_refine.
Qed.
Lemma val_binop_refine Γ f m1 m2 op v1 v2 v3 v4 τ1 τ3 σ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → binop_typed op τ1 τ3 σ →
  val_binop_ok Γ m1 op v1 v3 →
  v1 ⊑{Γ,f@m1↦m2} v2 : τ1 → v3 ⊑{Γ,f@m1↦m2} v4 : τ3 →
  val_binop Γ op v1 v3 ⊑{Γ,f@m1↦m2} val_binop Γ op v2 v4 : σ.
Proof.
  destruct 3; intro; do 2 inversion 1; simplify_equality';
    refine_constructor; eauto using base_val_binop_refine.
Qed.
Lemma val_cast_ok_refine Γ m1 m2 f v1 v2 τ σ :
  ✓ Γ → v1 ⊑{Γ,f@m1↦m2} v2 : τ → val_cast_ok Γ σ v1 → val_cast_ok Γ σ v2.
Proof.
  unfold val_cast_ok; destruct σ, 2; eauto using base_val_cast_ok_refine.
Qed.
Lemma val_cast_refine Γ f m1 m2 v1 v2 τ σ :
  ✓ Γ → cast_typed Γ τ σ → val_cast_ok Γ σ v1 →
  v1 ⊑{Γ,f@m1↦m2} v2 : τ → val_cast σ v1 ⊑{Γ,f@m1↦m2} val_cast σ v2 : σ.
Proof.
  destruct 2; inversion 2; simplify_equality; repeat refine_constructor;
    eauto using base_val_cast_refine, TVoid_cast_typed.
Qed.
End val.
