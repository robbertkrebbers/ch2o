(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_values base_values.

Inductive val (Ti Vi : Set) :=
  | VBase : base_val Ti Vi → val Ti Vi
  | VArray : type Ti → list (val Ti Vi) → val Ti Vi
  | VStruct : tag → list (val Ti Vi) → val Ti Vi
  | VUnion : tag → nat → val Ti Vi → val Ti Vi
  | VUnionNone : tag → list (val Ti Vi) → val Ti Vi.
Arguments VBase {_ _} _.
Arguments VArray {_ _} _ _.
Arguments VStruct {_ _} _ _.
Arguments VUnion {_ _} _ _ _.
Arguments VUnionNone  {_ _} _ _.

Instance: Injective (=) (=) (@VBase Ti Vi).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VArray Ti Vi τ).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VStruct Ti Vi s).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VUnion Ti Vi s i).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (@VUnionNone Ti Vi s).
Proof. by injection 1. Qed.

Instance val_eq_dec {Ti Vi : Set}
  `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)} `{∀ x1 x2 : Vi, Decision (x1 = x2)} :
  ∀ v1 v2 : val Ti Vi, Decision (v1 = v2).
Proof.
 refine (
  fix go v1 v2 : Decision (v1 = v2) :=
  match v1, v2 with
  | VBase v1, VBase v2 => cast_if (decide_rel (=) v1 v2)
  | VArray τ1 vs1, VArray τ2 vs2 =>
     cast_if_and (decide_rel (=) τ1 τ2) (decide_rel (=) vs1 vs2)
  | VStruct s1 vs1, VStruct s2 vs2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) vs1 vs2)
  | VUnion s1 i1 v1, VUnion s2 i2 v2 =>
     cast_if_and3 (decide_rel (=) s1 s2) (decide_rel (=) i1 i2)
       (decide_rel (=) v1 v2)
  | VUnionNone s1 vs1, VUnionNone s2 vs2 =>
     cast_if_and (decide_rel (=) s1 s2) (decide_rel (=) vs1 vs2)
  | _, _ => right _
  end); clear go; abstract congruence.
Defined.

Section val_ind.
  Context {Ti Vi} (P : val Ti Vi → Prop).
  Context (Pbase : ∀ v, P (VBase v)).
  Context (Parray : ∀ τ vs, Forall P vs → P (VArray τ vs)).
  Context (Pstruct : ∀ s vs, Forall P vs → P (VStruct s vs)).
  Context (Punion : ∀ s i v, P v → P (VUnion s i v)).
  Context (Punion_none : ∀ s vs, Forall P vs → P (VUnionNone s vs)).

  Definition val_ind_alt: ∀ v, P v :=
    fix go v :=
    match v return P v with
    | VBase v => Pbase v
    | VArray τ vs => Parray _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) vs
    | VStruct s vs => Pstruct _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) vs
    | VUnion s i v => Punion _ _ _ (go v)
    | VUnionNone s vs => Punion_none _ _ $ list_ind (Forall _)
       (Forall_nil_2 _) (λ v _, Forall_cons_2 _ _ _ (go v)) vs
    end.
End val_ind.

Definition val_map {Ti Vi} (f : base_val Ti Vi → base_val Ti Vi) :
    val Ti Vi → val Ti Vi :=
  fix go v :=
  match v with
  | VBase v => VBase (f v)
  | VArray τ vs => VArray τ (go <$> vs)
  | VStruct s vs => VStruct s (go <$> vs)
  | VUnion s i v => VUnion s i (go v)
  | VUnionNone s vs => VUnionNone s (go <$> vs)
  end.

Inductive val_forall {Ti Vi} (P : base_val Ti Vi → Prop) : val Ti Vi → Prop :=
  | VBase_forall v : P v → val_forall P (VBase v)
  | VArray_forall τ vs : Forall (val_forall P) vs → val_forall P (VArray τ vs)
  | VStruct_forall s vs : Forall (val_forall P) vs → val_forall P (VStruct s vs)
  | VUnion_forall s i v : val_forall P v → val_forall P (VUnion s i v)
  | VUnionNone_forall s vs :
     Forall (val_forall P) vs → val_forall P (VUnionNone s vs).

Section val_forall_ind.
  Context {Ti Vi} (P : base_val Ti Vi → Prop).
  Context (Q : val Ti Vi → Prop).
  Context (Qbase : ∀ v, P v → Q (VBase v)).
  Context (Qarray : ∀ τ vs,
    Forall (val_forall P) vs → Forall Q vs → Q (VArray τ vs)).
  Context (Qstruct : ∀ s vs,
    Forall (val_forall P) vs → Forall Q vs → Q (VStruct s vs)).
  Context (Qunion : ∀ s i v, val_forall P v → Q v → Q (VUnion s i v)).
  Context (Qunion_none : ∀ s vs,
    Forall (val_forall P) vs → Forall Q vs → Q (VUnionNone s vs)).

  Definition val_forall_ind_alt: ∀ v, val_forall P v → Q v :=
    fix go v Hv :=
    match Hv in val_forall _ v return Q v with
    | VBase_forall _ H => Qbase _ H
    | VArray_forall _ _ H => Qarray _ _ H (Forall_impl _ _ _ H go)
    | VStruct_forall _ _ H => Qstruct _ _ H (Forall_impl _ _ _ H go)
    | VUnion_forall _ _ _  H => Qunion _ _ _ H (go _ H)
    | VUnionNone_forall _ _ H => Qunion_none _ _ H (Forall_impl _ _ _ H go)
    end.
End val_forall_ind.

Section operations.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.

  Global Instance type_of_val: TypeOf (type Ti) (val Ti Vi) := λ v,
    match v with
    | VBase v => TBase (type_of v)
    | VArray τ vs => TArray τ (length vs)
    | VStruct s _ => TStruct s
    | VUnion s _ _ => TUnion s
    | VUnionNone s _ => TUnion s
    end.

  Definition val_of_bytes : type Ti → list (byte Ti Vi) → val Ti Vi :=
    type_iter
    (*i TBase =>     *) (λ τ bs,
      VBase $ base_val_of_bytes τ $ resize (size_of (TBase τ)) BUndef bs)
    (*i TVoid =>     *) (λ bs, VBase $ VUndef $ TInt $ TsInt)
    (*i TArray =>    *) (λ τ n rec bs,
      VArray τ $ array_of_bytes rec τ n bs)
    (*i TCompound => *) (λ c s τs rec bs,
      match c with
      | Struct => VStruct s $ struct_of_bytes rec τs bs
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => VUnion s 0 $ rec τ bs
         | _ => VUnionNone s $ flip rec bs <$> τs
         end
      end).
  Definition mval_to_val : mval Ti Vi → val Ti Vi :=
    fix go v :=
    match v with
    | MBase τ bs => VBase (base_val_of_bytes τ bs)
    | MArray τ vs => VArray τ (go <$> vs)
    | MStruct s vs => VStruct s (go <$> vs)
    | MUnion s i v => VUnion s i (go v)
    | MUnionNone s bs => val_of_bytes (TUnion s) bs
    end.
 
  Definition union_to_bytes (f : val Ti Vi → listset (mval Ti Vi))
      (sz : nat) (vs : list (val Ti Vi)) : listset (list (byte Ti Vi)) :=
    filter (λ bs, vs = flip val_of_bytes bs ∘ type_of <$> vs) $
      intersection_with_list bytes_join {[ replicate sz BUndef ]} $
      fmap (resize sz BUndef ∘ mval_to_bytes) ∘ f <$> vs.
  Definition mval_of_val : val Ti Vi → listset (mval Ti Vi) :=
    fix go v :=
    match v with
    | VBase v => MBase (type_of v) <$> base_val_to_bytes v
    | VArray τ vs => MArray τ <$> mapM go vs
    | VStruct s vs => MStruct s <$> mapM go vs
    | VUnion s i v => MUnion s i <$> go v
    | VUnionNone s vs =>
       MUnionNone s <$> union_to_bytes go (size_of (TUnion s)) vs
    end.
    
  Global Instance val_lookup_item:
      Lookup ref_seg (val Ti Vi) (val Ti Vi) := λ rs v,
    match rs, v with
    | RArray i n _, VArray _ vs => guard (n = length vs); vs !! i
    | RStruct i, VStruct _ vs => vs !! i
    | RUnion i _, VUnion s j v => guard (i = j); Some v
    | RUnion i _, VUnionNone s vs => vs !! i
    | _, _ => None
    end.
  Global Instance val_lookup: Lookup ref (val Ti Vi) (val Ti Vi) :=
    fix go r v :=
    match r with
    | [] => Some v
    | rs :: r => @lookup _ _ _ go r v ≫= (!! rs)
    end.
End operations.

Section vtyped.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.

  Inductive vtyped' (m : M) : val Ti Vi → type Ti → Prop :=
    | VBase_typed' v τ :
       m ⊢ v : τ →
       vtyped' m (VBase v) (TBase τ)
    | VArray_typed' vs τ n :
       type_valid get_env τ →
       n = length vs →
       Forall (λ v, vtyped' m v τ) vs →
       vtyped' m (VArray τ vs) (TArray τ n)
    | VStruct_typed' s vs τs :
       get_env !! s = Some τs →
       Forall2 (vtyped' m) vs τs →
       vtyped' m (VStruct s vs) (TStruct s)
    | VUnion_typed' s i τs v τ :
       get_env !! s = Some τs →
       τs !! i = Some τ →
       vtyped' m v τ →
       vtyped' m (VUnion s i v) (TUnion s)
    | VUnionNone_typed' s vs τs bs :
       get_env !! s = Some τs →
       length τs ≠ 1 →
       Forall2 (vtyped' m) vs τs →
       vs = flip val_of_bytes bs <$> τs →
       Forall (byte_valid m) bs →
       vtyped' m (VUnionNone s vs) (TUnion s).
  Global Instance vtyped: Typed M (type Ti) (val Ti Vi) := vtyped'.

  Lemma VBase_typed m v τ : m ⊢ v : τ → m ⊢ VBase v : TBase τ.
  Proof. by constructor. Qed.
  Lemma VArray_typed m vs τ n :
    type_valid get_env τ → n = length vs →
    m ⊢* vs : τ → m ⊢ VArray τ vs : TArray τ n.
  Proof. by constructor. Qed.
  Lemma VStruct_typed m s vs τs :
    get_env !! s = Some τs → m ⊢* vs :* τs → m ⊢ VStruct s vs : TStruct s.
  Proof. econstructor; eauto. Qed.
  Lemma VUnion_typed m s i τs v τ :
    get_env !! s = Some τs → τs !! i = Some τ →
    m ⊢ v : τ → m ⊢ VUnion s i v : TUnion s.
  Proof. econstructor; eauto. Qed.
  Lemma VUnionNone_typed m s vs τs bs :
    get_env !! s = Some τs → length τs ≠ 1 → m ⊢* vs :* τs →
    vs = flip val_of_bytes bs <$> τs → Forall (byte_valid m) bs →
    m ⊢ VUnionNone s vs : TUnion s.
  Proof. econstructor; eauto. Qed.

  Lemma vtyped_inv_l m (P : type Ti → Prop) v τ :
    m ⊢ v : τ →
    match v with
    | VBase v => (∀ τ', m ⊢ v : τ' → P (TBase τ')) → P τ
    | VArray τ' vs =>
       (∀ n, type_valid get_env τ' → n = length vs →
         m ⊢* vs : τ' → P (TArray τ' n)) →
       P τ
    | VStruct s vs =>
       (∀ τs, get_env !! s = Some τs → m ⊢* vs :* τs → P (TStruct s)) →
       P τ
    | VUnion s i v =>
       (∀ τs τ', get_env !! s = Some τs → τs !! i = Some τ' →
         m ⊢ v : τ' → P (TUnion s)) →
       P τ
    | VUnionNone s vs =>
       (∀ τs bs,
         get_env !! s = Some τs → length τs ≠ 1 → m ⊢* vs :* τs →
         vs = flip val_of_bytes bs <$> τs → Forall (byte_valid m) bs →
         P (TUnion s)) →
       P τ
    end.
  Proof. destruct 1; eauto. Qed.

  Section vtyped_ind.
    Context (m : M) (P : val Ti Vi → type Ti → Prop).
    Context (Pbase : ∀ v τ, m ⊢ v : τ → P (VBase v) (TBase τ)).
    Context (Parray : ∀ vs τ n,
      type_valid get_env τ → n = length vs → m ⊢* vs : τ →
      Forall (λ v, P v τ) vs → P (VArray τ vs) (TArray τ n)).
    Context (Pstruct : ∀ s vs τs,
      get_env !! s = Some τs → m ⊢* vs :* τs → Forall2 P vs τs →
      P (VStruct s vs) (TStruct s)).
    Context (PUnion : ∀ s i τs v τ,
      get_env !! s = Some τs → τs !! i = Some τ → m ⊢ v : τ → P v τ →
      P (VUnion s i v) (TUnion s)).
    Context (Punion_none : ∀ s vs τs bs,
      get_env !! s = Some τs → length τs ≠ 1 → m ⊢* vs :* τs →
      Forall2 P vs τs → vs = flip val_of_bytes bs <$> τs →
      Forall (byte_valid m) bs → P (VUnionNone s vs) (TUnion s)).

    Lemma vtyped_ind : ∀ v τ, vtyped' m v τ → P v τ.
    Proof.
     exact (fix go v τ H :=
      match H in vtyped' _ v τ return P v τ with
      | VBase_typed' _ _ H => Pbase _ _ H
      | VArray_typed' _ _ _ Hτ Hn H =>
         Parray _ _ _ Hτ Hn H (Forall_impl _ _ _ H (λ v, go _ _))
      | VStruct_typed' s _ _ Hs H =>
         Pstruct _ _ _ Hs H (Forall2_impl _ _ _ _ H go)
      | VUnion_typed' _ _ _ _ _ Hs Hτs H => PUnion _ _ _ _ _ Hs Hτs H (go _ _ H)
      | VUnionNone_typed' _ _ _ _ Hs Hτs H Hvs Hbs =>
         Punion_none _ _ _ _ Hs Hτs H (Forall2_impl _ _ _ _ H go) Hvs Hbs
      end).
    Qed.
  End vtyped_ind.

  Section vtyped_case.
    Context (m : M) (P : val Ti Vi → type Ti → Prop).
    Context (Pbase : ∀ v τ, m ⊢ v : τ → P (VBase v) (TBase τ)).
    Context (Parray : ∀ vs τ n,
      type_valid get_env τ → n = length vs →
      m ⊢* vs : τ → P (VArray τ vs) (TArray τ n)).
    Context (Pstruct : ∀ s vs τs,
      get_env !! s = Some τs → m ⊢* vs :* τs → P (VStruct s vs) (TStruct s)).
    Context (PUnion : ∀ s i τs v τ,
      get_env !! s = Some τs → τs !! i = Some τ →
      m ⊢ v : τ → P (VUnion s i v) (TUnion s)).
    Context (Punion_none : ∀ s vs τs bs,
      get_env !! s = Some τs → length τs ≠ 1 → m ⊢* vs :* τs →
      vs = flip val_of_bytes bs <$> τs → Forall (byte_valid m) bs →
      P (VUnionNone s vs) (TUnion s)).

    Lemma vtyped_case : ∀ v τ, vtyped' m v τ → P v τ.
    Proof. destruct 1; eauto. Qed.
  End vtyped_case.
End vtyped.

Ltac vtyped_constructor := first
  [ eapply VBase_typed | eapply VArray_typed | eapply VStruct_typed
  | eapply VUnion_typed | eapply VUnionNone_typed ].

Section val_le.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.

  Inductive val_le' (m : M) : relation (val Ti Vi) :=
    | VBase_le' v1 v2 :
       v1 ⊑@{m} v2 → val_le' m (VBase v1) (VBase v2)
    | VArray_le' vs1 vs2 τ :
       Forall2 (val_le' m) vs1 vs2 → val_le' m (VArray τ vs1) (VArray τ vs2)
    | VStruct_le' s vs1 vs2 :
       Forall2 (val_le' m) vs1 vs2 → val_le' m (VStruct s vs1) (VStruct s vs2)
    | VUnion_le' s i v1 v2 :
       val_le' m v1 v2 → val_le' m (VUnion s i v1) (VUnion s i v2)
    | VUnionNone_le_refl' s vs :
       val_le' m (VUnionNone s vs) (VUnionNone s vs)
    | VUnionNone_le' s vs1 vs2 τs bs1 bs2 :
       get_env !! s = Some τs →
       vs1 = flip val_of_bytes bs1 <$> τs →
       Forall (byte_valid m) bs1 →
       vs2 = flip val_of_bytes bs2 <$> τs →
       bs1 ⊑@{m}* bs2 →
       val_le' m (VUnionNone s vs1) (VUnionNone s vs2)
    | VUnion_VUnionNone_le' s i τs v1 v2 vs2 bs2 :
       get_env !! s = Some τs →
       length τs ≠ 1 →
       vs2 !! i = Some v2 →
       val_le' m v1 v2 →
       vs2 = flip val_of_bytes bs2 <$> τs →
       Forall (byte_valid m) bs2 →
       val_le' m (VUnion s i v1) (VUnionNone s vs2).
  Global Instance val_le: SubsetEqEnv M (val Ti Vi) := val_le'.

  Lemma VBase_le m v1 v2 : v1 ⊑@{m} v2 → VBase v1 ⊑@{m} VBase v2.
  Proof. by constructor. Qed.
  Lemma VArray_le m vs1 vs2 τ :
    vs1 ⊑@{m}* vs2 → VArray τ vs1 ⊑@{m} VArray τ vs2.
  Proof. by constructor. Qed.
  Lemma VStruct_le m s vs1 vs2 :
    vs1 ⊑@{m}* vs2 → VStruct s vs1 ⊑@{m} VStruct s vs2.
  Proof. by constructor. Qed.
  Lemma VUnion_le m s i v1 v2 : v1 ⊑@{m} v2 → VUnion s i v1 ⊑@{m} VUnion s i v2.
  Proof. by constructor. Qed.
  Lemma VUnionNone_le_refl m s vs : VUnionNone s vs ⊑@{m} VUnionNone s vs.
  Proof. by constructor. Qed.
  Lemma VUnionNone_le m s vs1 vs2 τs bs1 bs2 :
    get_env !! s = Some τs →
    vs1 = flip val_of_bytes bs1 <$> τs →
    Forall (byte_valid m) bs1 →
    vs2 = flip val_of_bytes bs2 <$> τs →
    bs1 ⊑@{m}* bs2 →
    VUnionNone s vs1 ⊑@{m} VUnionNone s vs2.
  Proof. econstructor; eauto. Qed.
  Lemma VUnion_VUnionNone_le m s i τs v1 v2 vs2 bs2 :
    get_env !! s = Some τs → length τs ≠ 1 →
    vs2 !! i = Some v2 →
    v1 ⊑@{m} v2 →
    vs2 = flip val_of_bytes bs2 <$> τs →
    Forall (byte_valid m) bs2 →
    VUnion s i v1 ⊑@{m} VUnionNone s vs2.
  Proof. econstructor; eauto. Qed.

  Lemma val_le_inv_l m (P : val Ti Vi → Prop) v1 v2 :
    v1 ⊑@{m} v2 →
    match v1 with
    | VBase v1 => (∀ v2, v1 ⊑@{m} v2 → P (VBase v2)) → P v2
    | VArray τ vs1 => (∀ vs2, vs1 ⊑@{m}* vs2 → P (VArray τ vs2)) → P v2
    | VStruct s vs1 => (∀ vs2, vs1 ⊑@{m}* vs2 → P (VStruct s vs2)) → P v2 
    | VUnion s i v1 =>
       (∀ v2, v1 ⊑@{m} v2 → P (VUnion s i v2)) →
       (∀ τs v2 vs2 bs2,
         get_env !! s = Some τs →
         length τs ≠ 1 →
         vs2 !! i = Some v2 →
         v1 ⊑@{m} v2 →
         vs2 = flip val_of_bytes bs2 <$> τs →
         Forall (byte_valid m) bs2 →
         P (VUnionNone s vs2)) →
       P v2
    | VUnionNone s vs1 =>
       P (VUnionNone s vs1) →
       (∀ vs2 τs bs1 bs2,
         get_env !! s = Some τs →
         vs1 = flip val_of_bytes bs1 <$> τs →
         Forall (byte_valid m) bs1 →
         vs2 = flip val_of_bytes bs2 <$> τs →
         bs1 ⊑@{m}* bs2 →
         P (VUnionNone s vs2)) →
       P v2
    end.
  Proof. destruct 1; eauto. Qed.

  Lemma val_le_inv m (P : Prop) v1 v2 :
    v1 ⊑@{m} v2 →
    match v1, v2 with
    | VBase v1, VBase v2 => (v1 ⊑@{m} v2 → P) → P
    | VArray τ1 vs1, VArray τ2 vs2 => (τ1 = τ2 → vs1 ⊑@{m}* vs2 → P) → P
    | VStruct s1 vs1, VStruct s2 vs2 => (s1 = s2 → vs1 ⊑@{m}* vs2 → P) → P 
    | VUnion s1 i1 v1, VUnion s2 i2 v2 =>
       (s1 = s2 → i1 = i2 → v1 ⊑@{m} v2 → P) → P
    | VUnionNone s1 vs1, VUnionNone s2 vs2 =>
       (s1 = s2 → vs1 = vs2 → P) →
       (∀ τs bs1 bs2,
         s1 = s2 →
         get_env !! s1 = Some τs →
         vs1 = flip val_of_bytes bs1 <$> τs →
         Forall (byte_valid m) bs1 →
         vs2 = flip val_of_bytes bs2 <$> τs →
         bs1 ⊑@{m}* bs2 →
         P) →
       P
    | VUnion s1 i v1, VUnionNone s2 vs2 =>
       (∀ τs v2 bs2,
         s1 = s2 →
         get_env !! s1 = Some τs →
         length τs ≠ 1 →
         vs2 !! i = Some v2 →
         v1 ⊑@{m} v2 →
         vs2 = flip val_of_bytes bs2 <$> τs →
         Forall (byte_valid m) bs2 →
         P) →
       P
    | _, _ => P
    end.
  Proof. destruct 1; eauto. Qed.

  Lemma val_of_bytes_base τ bs :
    val_of_bytes (TBase τ) bs =
      VBase $ base_val_of_bytes τ $ resize (size_of (TBase τ)) BUndef bs.
  Proof. unfold val_of_bytes. by rewrite type_iter_base. Qed. 
  Lemma val_of_bytes_array τ n bs :
    val_of_bytes (TArray τ n) bs =
      VArray τ $ array_of_bytes (val_of_bytes τ) τ n bs.
  Proof. unfold val_of_bytes. by rewrite type_iter_array. Qed.
  Lemma val_of_bytes_compound c s τs bs :
    get_env !! s = Some τs →
    val_of_bytes (TCompound c s) bs =
      match c with
      | Struct => VStruct s $ struct_of_bytes val_of_bytes τs bs
      | Union =>
         match list_singleton_dec τs with
         | inleft (τ↾_) => VUnion s 0 $ val_of_bytes τ bs
         | _ => VUnionNone s $ flip val_of_bytes bs <$> τs
         end
      end.
  Proof.
    intros Hs. unfold val_of_bytes. erewrite (type_iter_compound
      (pointwise_relation (list (byte Ti Vi)) (@eq (val Ti Vi)))); eauto.
    { clear s τs Hs bs. intros τ n f g Hfg bs. f_equal.
      auto using array_of_bytes_ext. }
    clear s τs Hs bs. intros f g [] s τs Hs Hτs bs.
    { f_equal. auto using struct_of_bytes_ext. }
    destruct (list_singleton_dec _) as [[??]|?]; subst; f_equal.
    * by decompose_Forall.
    * apply Forall_fmap_ext. eauto using Forall_impl.
  Qed.

  Lemma val_of_bytes_le m τ bs1 bs2 :
    type_valid get_env τ →
    Forall (byte_valid m) bs1 → bs1 ⊑@{m}* bs2 →
    val_of_bytes τ bs1 ⊑@{m} val_of_bytes τ bs2.
  Proof.
    intros Hτ. revert τ Hτ bs1 bs2. refine (type_env_ind _ _ _ _).
    * intros τ ? bs1 bs2 Hbs. rewrite !val_of_bytes_base. constructor.
      apply base_val_of_bytes_le;
        auto using Forall_resize, BUndef_valid, Forall2_resize.
    * intros τ n ? IH bs1 bs2 Hbs1 Hbs.
      rewrite !val_of_bytes_array. apply VArray_le. revert bs1 bs2 Hbs1 Hbs.
      induction n; simpl; auto using Forall2_take, Forall2_drop, Forall_drop.
    * intros [] s τs Hs Hτs IH bs1 bs2 Hbs1 Hbs.
      { erewrite !val_of_bytes_compound by eauto. apply VStruct_le.
        clear Hs Hτs. unfold struct_of_bytes. revert bs1 bs2 Hbs1 Hbs.
        induction (struct_fields_same_length τs);
          intros; decompose_Forall; simpl;
          auto using Forall2_take, Forall2_drop, Forall_drop. }
      erewrite !val_of_bytes_compound by eauto.
      destruct (list_singleton_dec _) as [[??]|?]; subst.
      { rewrite Forall_singleton in IH. apply VUnion_le. auto. }
      simpl. eapply VUnionNone_le; eauto.
  Qed.

  Section val_le_ind.
    Context (m : M) (P : val Ti Vi → val Ti Vi → Prop).
    Context (Pbase : ∀ v1 v2, v1 ⊑@{m} v2 → P (VBase v1) (VBase v2)).
    Context (Parray : ∀ vs1 vs2 τ,
      vs1 ⊑@{m}* vs2 → Forall2 P vs1 vs2 → P (VArray τ vs1) (VArray τ vs2)).
    Context (Pstruct : ∀ s vs1 vs2,
      vs1 ⊑@{m}* vs2 → Forall2 P vs1 vs2 → P (VStruct s vs1) (VStruct s vs2)).
    Context (Punion : ∀ s i v1 v2,
      v1 ⊑@{m} v2 → P v1 v2 → P (VUnion s i v1) (VUnion s i v2)).
    Context (Punion_none_refl : ∀ s vs, P (VUnionNone s vs) (VUnionNone s vs)).
    Context (Punion_none : ∀ s vs1 vs2 τs bs1 bs2,
      get_env !! s = Some τs →
      vs1 = flip val_of_bytes bs1 <$> τs →
      Forall (byte_valid m) bs1 →
      vs2 = flip val_of_bytes bs2 <$> τs →
      bs1 ⊑@{m}* bs2 →
      vs1 ⊑@{m}* vs2 →
      Forall2 P vs1 vs2 →
      P (VUnionNone s vs1) (VUnionNone s vs2)).
    Context (Punion_union_none : ∀ s i τs v1 v2 vs2 bs2,
      get_env !! s = Some τs →
      length τs ≠ 1 →
      vs2 !! i = Some v2 →
      v1 ⊑@{m} v2 →
      P v1 v2 →
      vs2 = flip val_of_bytes bs2 <$> τs →
      Forall (byte_valid m) bs2 →
      P (VUnion s i v1) (VUnionNone s vs2)).

    Lemma val_le_ind: ∀ v1 v2, val_le' m v1 v2 → P v1 v2.
    Proof.
     assert (∀ vs1 vs2,
       vs1 ⊑@{m}* vs2 → Forall (λ v1, ∀ v2, v1 ⊑@{m} v2 → P v1 v2) vs1 →
       Forall2 P vs1 vs2).
     { induction 1; intros; decompose_Forall; auto. }
     assert (∀ τs bs1 bs2,
       Forall (type_valid get_env) τs → Forall (byte_valid m) bs1 →
       bs1 ⊑@{m}* bs2 →
       flip val_of_bytes bs1 <$> τs ⊑@{m}* flip val_of_bytes bs2 <$> τs).
     { induction 1; simpl; constructor; eauto using val_of_bytes_le. }
     induction v1 using val_ind_alt;
       intros ? Hv1v2; apply (val_le_inv_l _ _ _ _ Hv1v2);
       intros; subst; eauto 7 using env_valid_lookup.
    Qed.
  End val_le_ind.
End val_le.

Ltac val_le_constructor := first
  [ eapply VBase_le | eapply VArray_le | eapply VStruct_le
  | eapply VUnion_le | eapply VUnionNone_le_refl
  | eapply VUnionNone_le | eapply VUnion_VUnionNone_le ].

Inductive union_free `{EnvSpec Ti Vi} : val Ti Vi → Prop :=
  | VBase_union_free v : union_free (VBase v)
  | VArray_union_free vs τ : Forall union_free vs → union_free (VArray τ vs)
  | VStruct_union_free s vs : Forall union_free vs → union_free (VStruct s vs)
  | VUnion_union_free s v τ :
     get_env !! s = Some [τ] → union_free v → union_free (VUnion s 0 v)
  | VUnionNone_union_free s vs :
     Forall union_free vs → union_free (VUnionNone s vs).

Section union_free_ind.
  Context `{EnvSpec Ti Vi} (P : val Ti Vi → Prop).
  Context (Pbase : ∀ v, P (VBase v)).
  Context (Parray : ∀ τ vs,
    Forall union_free vs → Forall P vs → P (VArray τ vs)).
  Context (Pstruct : ∀ s vs,
    Forall union_free vs → Forall P vs → P (VStruct s vs)).
  Context (Punion : ∀ s v τ,
    get_env !! s = Some [τ] → union_free v → P v → P (VUnion s 0 v)).
  Context (Punion_none : ∀ s vs,
    Forall union_free vs → Forall P vs → P (VUnionNone s vs)).

  Lemma union_free_ind_alt: ∀ v, union_free v → P v.
  Proof.
   exact (
    fix go v Hv :=
    match Hv in union_free v return P v with
    | VBase_union_free _ => Pbase _
    | VArray_union_free _ _ H => Parray _ _ H (Forall_impl _ _ _ H go)
    | VStruct_union_free _ _ H => Pstruct _ _ H (Forall_impl _ _ _ H go)
    | VUnion_union_free _ _ _ Hs H => Punion _ _ _ Hs H (go _ H)
    | VUnionNone_union_free _ _ H => Punion_none _ _ H (Forall_impl _ _ _ H go)
    end).
  Qed.
End union_free_ind.

Section val.
Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.
Implicit Types v : val Ti Vi.
Implicit Types vs : list (val Ti Vi).
Implicit Types w : mval Ti Vi.
Implicit Types ws : list (mval Ti Vi).
Implicit Types m : M.
Implicit Types τ : type Ti.
Implicit Types τs : list (type Ti).
Implicit Types bs : list (byte Ti Vi).
Implicit Types r : ref.
Implicit Types rs : ref_seg.
Context `{PropHolds (∀ m i τ,
  type_of_index m i = Some τ → τ = TVoid ∨ type_valid get_env τ)}.

Lemma vtyped_type_valid m v τ : m ⊢ v : τ → type_valid get_env τ.
Proof.
  induction 1 using @vtyped_ind;
    econstructor; eauto using base_typed_type_valid.
Qed.
Global Instance: TypeOfSpec M (type Ti) (val Ti Vi).
Proof. destruct 1; simpl; f_equal; eauto. eapply type_of_correct; eauto. Qed.

Lemma val_of_bytes_typed m τ bs :
  type_valid get_env τ → Forall (byte_valid m) bs → m ⊢ val_of_bytes τ bs : τ.
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros τ Hτ bs Hbs. rewrite val_of_bytes_base.
    vtyped_constructor; auto using base_val_of_bytes_typed,
      Forall_resize, BUndef_valid.
  * intros τ n Hτ IH bs Hbs. rewrite val_of_bytes_array. vtyped_constructor;
      eauto using array_of_bytes_length, Forall_array_of_bytes_alt.
  * intros [] s τs Hs Hτs IH bs Hbs.
    { erewrite val_of_bytes_compound by eauto.
      apply VStruct_typed with τs; eauto using Forall2_struct_of_bytes_alt. }
    erewrite val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[τ ?]|Hτs_len]; subst.
    + rewrite Forall_singleton in IH. eapply VUnion_typed, IH; eauto.
    + apply VUnionNone_typed with τs bs;
        auto using resize_length;
        clear Hτs Hs Hτs_len; induction IH; simpl; constructor; auto.
Qed.
Lemma Forall_val_of_bytes_typed m τs bs :
  Forall (type_valid get_env) τs → Forall (byte_valid m) bs →
  m ⊢* (flip val_of_bytes bs <$> τs) :* τs.
Proof. intros Hτs Hbs. induction Hτs; simpl; auto using val_of_bytes_typed. Qed.

Lemma val_of_bytes_type_of m τ bs :
  type_valid get_env τ → Forall (byte_valid m) bs →
  type_of (val_of_bytes τ bs) = τ.
Proof. intros. eapply type_of_correct, val_of_bytes_typed; eauto. Qed.
Lemma val_of_bytes_fmap_type_of m τs bs :
  Forall (type_valid get_env) τs → Forall (byte_valid m) bs →
  type_of <$> flip val_of_bytes bs <$> τs = τs.
Proof.
  induction 1; simpl; intros; f_equal; eauto using val_of_bytes_type_of.
Qed.

Lemma val_of_bytes_trans m τ bs1 bs2 bs3 :
  type_valid get_env τ → bs1 ⊑@{m}* bs2 → bs2 ⊑@{m}* bs3 →
  val_of_bytes τ bs1 = val_of_bytes τ bs3 →
  val_of_bytes τ bs2 = val_of_bytes τ bs3.
Proof.
  intros Hτ. revert τ Hτ bs1 bs2 bs3. refine (type_env_ind _ _ _ _).
  * intros τ ? bs1 bs2 bs3 ??. rewrite !val_of_bytes_base.
    intros. f_equal. simplify_equality.
    eauto using bytes_le_resize, base_val_of_bytes_trans.
  * intros τ n ? IH bs1 bs2 bs3 Hbs1 Hbs2. rewrite !val_of_bytes_array.
    intros Hbs3. f_equal. simplify_equality.
    revert bs1 bs2 bs3 Hbs1 Hbs2 Hbs3.
    induction n; simpl; intros; f_equal; simplify_list_equality;
      eauto using Forall2_drop, Forall2_take.
  * intros [] s τs Hs Hτs IH bs1 bs2 bs3 Hbs1 Hbs2.
    { erewrite !val_of_bytes_compound by eauto.
      intros Hbs3. f_equal. simplify_equality.
      clear Hs Hτs. revert bs1 bs2 bs3 Hbs1 Hbs2 Hbs3.
      unfold struct_of_bytes.
      induction (struct_fields_same_length τs); simpl in *;
        decompose_Forall; intros; f_equal; simplify_list_equality;
        eauto using Forall2_drop, Forall2_take. }
    erewrite !val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_];
      intros Hbs3; f_equal; simplify_equality; decompose_Forall; eauto.
    clear Hs Hτs. revert bs1 bs2 bs3 Hbs1 Hbs2 Hbs3.
    induction IH; simpl; intros; f_equal; simplify_list_equality; eauto.
Qed.

Lemma VUnionNone_typed_alt m s vs τs bs :
  get_env !! s = Some τs → length τs ≠ 1 →
  vs = flip val_of_bytes bs <$> τs →
  Forall (byte_valid m) bs → m ⊢ VUnionNone s vs : TUnion s.
Proof.
  intros Hs Hτs_len Hvs Hbs. subst. vtyped_constructor; eauto.
  elim (env_valid_lookup s τs Hs); simpl;
    constructor; eauto using val_of_bytes_typed.
Qed.

Lemma val_freeze_frozen v : val_forall frozen (val_map freeze v).
Proof.
  induction v using val_ind_alt; simpl; constructor;
    auto using base_val_freeze_frozen; by apply Forall_fmap.
Qed.
Lemma val_frozen_freeze v : val_forall frozen v → val_map freeze v = v.
Proof.
  assert (∀ vs,
    Forall (λ v, val_map freeze v = v) vs → val_map freeze <$> vs = vs).
  { induction 1; simpl; f_equal; auto. }
  induction 1 using @val_forall_ind_alt; simpl; f_equal;
    auto using base_val_frozen_freeze.
Qed.
Lemma val_freeze_idempotent v :
  val_map freeze (val_map freeze v) = val_map freeze v.
Proof. apply val_frozen_freeze, val_freeze_frozen. Qed.
Lemma val_freeze_type_of v : type_of (val_map freeze v) = type_of v.
Proof.
  induction v using val_ind_alt; simpl; simpl; f_equal;
    auto using base_val_freeze_type_of.
  by rewrite fmap_length.
Qed.

Lemma vals_freeze_frozen vs :
  Forall (val_forall frozen) (val_map freeze <$> vs).
Proof. induction vs; constructor; auto using val_freeze_frozen. Qed.
Lemma vals_frozen_freeze vs :
  Forall (val_forall frozen) vs → val_map freeze <$> vs = vs.
Proof. induction 1; simpl; f_equal; eauto using val_frozen_freeze. Qed.
Lemma vals_freeze_idempotent vs :
  val_map freeze <$> val_map freeze <$> vs = val_map freeze <$> vs.
Proof. apply vals_frozen_freeze, vals_freeze_frozen. Qed.
Lemma vals_freeze_type_of vs :
  type_of <$> val_map freeze <$> vs = type_of <$> vs.
Proof. induction vs; simpl; f_equal; auto using val_freeze_type_of. Qed.

Lemma val_of_bytes_frozen τ bs :
  type_valid get_env τ → val_forall frozen (val_of_bytes τ bs).
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros. rewrite val_of_bytes_base. constructor.
    apply base_val_of_bytes_frozen.
  * intros. rewrite val_of_bytes_array. constructor.
    auto using Forall_array_of_bytes.
  * intros [] s τs ? _ IH bs.
    { erewrite val_of_bytes_compound by eauto. constructor.
      auto using Forall_struct_of_bytes. }
    erewrite val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|?]; subst;
      decompose_Forall; constructor; auto.
    apply Forall_fmap. elim IH; constructor; eauto.
Qed.
Lemma vals_of_bytes_frozen τs bs :
  Forall (type_valid get_env) τs →
  Forall (val_forall frozen) (flip val_of_bytes bs <$> τs).
Proof.
  intros. eapply Forall_fmap, Forall_impl; eauto using val_of_bytes_frozen.
Qed.

Lemma typed_freeze m v τ : m ⊢ v : τ → m ⊢ val_map freeze v : τ.
Proof.
  induction 1 using @vtyped_ind; simpl.
  * constructor. by apply base_typed_freeze.
  * constructor; auto.
    + by rewrite fmap_length.
    + by apply Forall_fmap.
  * econstructor; eauto. by apply Forall2_fmap_l.
  * econstructor; eauto.
  * subst. rewrite vals_frozen_freeze by
      eauto using vals_of_bytes_frozen, env_valid_lookup.
    econstructor; eauto.
Qed.

Lemma vtyped_ge m v1 v2 τ : m ⊢ v1 : τ → v1 ⊑@{m} v2 → m ⊢ v2 : τ.
Proof.
  assert (∀ vs1 vs2 τ,
    Forall2 (λ v1 v2, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs1 : τ → m ⊢* vs2 : τ).
  { induction 1; intros; decompose_Forall; auto. }
  assert (∀ vs1 vs2 τs,
    Forall2 (λ v1 v2, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs1 :* τs → m ⊢* vs2 :* τs).
  { intros vs1 vs2 τs Hvs. revert τs.
    induction Hvs; intros; decompose_Forall; auto. }
  intros Hv1τ Hv1v2. revert τ Hv1τ. induction Hv1v2 using @val_le_ind;
    intros ? Hv1τ; apply (vtyped_inv_l _ _ _ _ Hv1τ); intros; clear Hv1τ;
    simplify_map_equality; eauto using VUnionNone_typed_alt;
    vtyped_constructor; eauto using bytes_valid_ge,
      Forall2_length, base_typed_ge.
Qed.
Lemma vtyped_le m v1 v2 τ : m ⊢ v1 : τ → v2 ⊑@{m} v1 → m ⊢ v2 : τ.
Proof.
  assert (∀ vs1 vs2 τ,
    Forall2 (λ v2 v1, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs2 : τ → m ⊢* vs1 : τ).
  { induction 1; intros; decompose_Forall; auto. }
  assert (∀ vs1 vs2 τs,
    Forall2 (λ v2 v1, ∀ τ, m ⊢ v1 : τ → m ⊢ v2 : τ) vs1 vs2 →
    m ⊢* vs2 :* τs → m ⊢* vs1 :* τs).
  { intros vs1 vs2 τs Hvs. revert τs.
    induction Hvs; intros; decompose_Forall; auto. }
  assert (∀ s i τs v1 v2 vs bs,
    get_env !! s = Some τs →
    v1 ⊑@{m} v2 → vs !! i = Some v2 →
    vs = flip val_of_bytes bs <$> τs →
    Forall (byte_valid m) bs →
    (∀ τ, m ⊢ v2 : τ → m ⊢ v1 : τ) →
    m ⊢ VUnion s i v1 : TUnion s).
  { intros. subst. edestruct @list_lookup_fmap_inv as [? [??]]; eauto.
    subst. vtyped_constructor; eauto using val_of_bytes_typed,
      env_valid_lookup_lookup. }
  intros Hv1τ Hv1v2. revert τ Hv1τ. induction Hv1v2 using @val_le_ind;
    intros ? Hv1τ; apply (vtyped_inv_l _ _ _ _ Hv1τ); intros;
    simplify_map_equality; first
     [ by eauto using vunion_none_typed_alt
     | by eauto
     | vtyped_constructor; eauto using base_typed_le, Forall2_length, eq_sym].
Qed.

Lemma val_of_bytes_masked m τ bs1 bs2 cs2 :
  type_valid get_env τ →
  bs1 ⊑@{m}* bs2 → Forall (byte_valid m) cs2 →
  val_of_bytes τ bs2 = val_of_bytes τ cs2 →
  val_of_bytes τ (mask_bytes bs1 cs2) = val_of_bytes τ bs1.
Proof.
  intros Hτ. revert τ Hτ bs1 bs2 cs2. refine (type_env_ind _ _ _ _).
  * intros τ ? bs1 bs2 cs2.
    rewrite !val_of_bytes_base, !base_val_of_bytes_resize_take.
    intros. f_equal. simplify_equality. rewrite mask_bytes_take.
    eauto using base_val_of_bytes_masked, Forall_take, Forall2_take.
  * intros τ n ? IH bs1 bs2 cs2. rewrite !val_of_bytes_array.
    intros. f_equal. simplify_equality.
    eauto using array_of_bytes_masked.
  * intros [] s τs Hs Hτs IH bs1 bs2 cs2.
    { erewrite !val_of_bytes_compound by eauto.
      intros ???. f_equal. simplify_equality.
      eauto using struct_of_bytes_masked. }
    erewrite !val_of_bytes_compound by eauto.
    intros. destruct (list_singleton_dec _) as [[??]|_]; subst.
    + simplify_equality. f_equal. rewrite Forall_singleton in IH. eauto.
    + simplify_equality. f_equal. clear Hs Hτs.
      induction IH; simpl in *; f_equal; simplify_list_equality; eauto.
Qed.

Lemma Forall_val_of_bytes_masked m τs bs1 bs2 cs2 :
  Forall (type_valid get_env) τs →
  bs1 ⊑@{m}* bs2 → Forall (byte_valid m) cs2 →
  flip val_of_bytes bs2 <$> τs = flip val_of_bytes cs2 <$> τs →
  flip val_of_bytes (mask_bytes bs1 cs2) <$> τs =
    flip val_of_bytes bs1 <$> τs.
Proof.
  intros Hτs ??. induction Hτs; simpl; intros; simplify_list_equality;
    f_equal; eauto using val_of_bytes_masked.
Qed.

Global Instance: PartialOrder (@subseteq_env M (val Ti Vi) _ m).
Proof.
  intros m. repeat split.
  * assert (∀ vs, Forall (λ v, v ⊑@{m} v) vs → vs ⊑@{m}* vs).
    { induction 1; constructor; auto. }
    intros v. induction v using val_ind_alt; econstructor; auto.
  * assert (∀ vs1 vs2 vs3,
      Forall2 (λ v1 v2, ∀ v3, v2 ⊑@{m} v3 → v1 ⊑@{m} v3) vs1 vs2 →
      vs2 ⊑@{m}* vs3 → vs1 ⊑@{m}* vs3).
    { intros ???. apply Forall2_transitive. eauto. }
    assert (∀ s i τs vs2 vs3 v1 v2 bs2 bs3,
      get_env !! s = Some τs → length τs ≠ 1 →
      vs2 !! i = Some v2 → v1 ⊑@{m} v2 →
      (∀ v3, v2 ⊑@{m} v3 → v1 ⊑@{m} v3) →
      bs2 ⊑@{m}* bs3 →
      vs2 = flip val_of_bytes bs2 <$> τs →
      Forall (byte_valid m) bs2 →
      vs3 = flip val_of_bytes bs3 <$> τs →
      VUnion s i v1 ⊑@{m} VUnionNone s vs3).
    { intros s i τs ?? v1 v2 bs2 bs3 Hs Hτs Hv2 ??????. subst.
      destruct (list_lookup_fmap_inv _ _ _ _ Hv2) as [τ [Hτ ?]]. subst.
      simpl in *. apply VUnion_VUnionNone_le with τs (val_of_bytes τ bs3) bs3;
        eauto using val_of_bytes_le, env_valid_lookup_lookup, bytes_valid_ge.
      rewrite list_lookup_fmap. by simplify_option_equality. }
    assert (∀ s τs vs1 vs2 vs3 bs1 bs2 bs2' bs3,
      get_env !! s = Some τs → bs1 ⊑@{m}* bs2 →
      vs1 = flip val_of_bytes bs1 <$> τs → Forall (byte_valid m) bs1 →
      vs2 = flip val_of_bytes bs2 <$> τs → bs2' ⊑@{m}* bs3 →
      vs2 = flip val_of_bytes bs2' <$> τs → Forall (byte_valid m) bs2' →
      vs3 = flip val_of_bytes bs3 <$> τs →
      VUnionNone s vs1 ⊑@{m} VUnionNone s vs3).
    { intros s τs ??? bs1 bs2 bs2' bs3 ?????????. subst.
      apply VUnionNone_le with τs (mask_bytes bs1 bs2') bs3; eauto using
        mask_bytes_valid, Forall_val_of_bytes_masked, env_valid_lookup, eq_sym.
      transitivity bs2'; eauto using mask_bytes_le. }
    intros v1 v2 v3 Hv1v2. revert v3. induction Hv1v2 using @val_le_ind;
      intros ? Hv2v3; apply (val_le_inv_l _ _ _ _ Hv2v3); intros;
      simplify_map_equality; first
       [ by eauto
       | val_le_constructor; eauto; etransitivity; eauto ].
  * assert (∀ vs1 vs2,
      Forall2 (λ v1 v2, v2 ⊑@{m} v1 → v1 = v2) vs1 vs2 →
      vs2 ⊑@{m}* vs1 → vs1 = vs2).
    { induction 1; inversion_clear 1; f_equal; auto. }
    assert (∀ vs1 vs2 τs bs1 bs2,
      Forall (type_valid get_env) τs →
      Forall2 (λ v1 v2, v2 ⊑@{m} v1 → v1 = v2) vs1 vs2 →
      bs1 ⊑@{m}* bs2 →
      vs2 = flip val_of_bytes bs1 <$> τs → Forall (byte_valid m) bs1 →
      vs1 = flip val_of_bytes bs2 <$> τs → vs1 = vs2).
    { intros ?? τs ?? Hτs ?????. subst.
      induction Hτs; simpl in *; decompose_Forall;
        f_equal; eauto using val_of_bytes_le. }
    induction 1 using @val_le_ind;
      intros Hv2v1; apply (val_le_inv _ _ _ _ Hv2v1); intros;
      f_equal; eauto using env_valid_lookup;
      try by apply (anti_symmetric (⊑@{m})).
Qed.

Lemma union_free_freeze v : union_free (val_map freeze v) ↔ union_free v.
Proof.
  split.
  * assert (∀ vs,
      Forall (λ v, union_free (val_map freeze v) → union_free v) vs →
      Forall union_free (val_map freeze <$> vs) → Forall union_free vs).
    { induction 1; simpl; intros; decompose_Forall; eauto. } 
    induction v using val_ind_alt; inversion_clear 1; econstructor; eauto.
  * induction 1 using @union_free_ind_alt; simpl;
      econstructor; eauto; by apply Forall_fmap.
Qed.

Lemma val_of_bytes_union_free τ bs :
  type_valid get_env τ → union_free (val_of_bytes τ bs).
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros. rewrite val_of_bytes_base. by constructor.
  * intros. rewrite val_of_bytes_array.
    constructor. by apply Forall_array_of_bytes.
  * intros [] s τs Hs Hτs IH; intros.
    { erewrite !val_of_bytes_compound by eauto.
      constructor. by apply Forall_struct_of_bytes. }
    erewrite !val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[τ ?]|?]; subst.
    + decompose_Forall. econstructor; eauto.
    + econstructor; eauto. apply Forall_fmap.
      unfold compose. elim IH; simpl; auto.
Qed.

Lemma mval_to_val_typed m w τ : m ⊢ w : τ → m ⊢ mval_to_val w : τ.
Proof.
  induction 1 using @mtyped_ind; simpl.
  * vtyped_constructor. eauto using base_val_of_bytes_typed.
  * vtyped_constructor; trivial.
    + by rewrite fmap_length.
    + by apply Forall_fmap.
  * vtyped_constructor; eauto. by apply Forall2_fmap_l.
  * vtyped_constructor; eauto.
  * eapply val_of_bytes_typed; eauto. constructor; eauto.
Qed.

Lemma mval_to_val_union_free_1 w : union_free (mval_to_val w) → munion_free w.
Proof.
  assert (∀ ws,
    Forall (λ w, union_free (mval_to_val w) → munion_free w) ws →
    Forall union_free (mval_to_val <$> ws) → Forall munion_free ws).
  { induction 1; simpl; intros; decompose_Forall; auto. }
  induction w using @mval_ind_alt; simpl.
  * constructor.
  * inversion_clear 1. constructor; auto.
  * inversion_clear 1. constructor; auto.
  * inversion_clear 1. econstructor; eauto.
  * constructor.
Qed.
Lemma mval_to_val_union_free_2 m w τ :
  m ⊢ w : τ → munion_free w → union_free (mval_to_val w).
Proof.
  assert (∀ ws,
    Forall (λ w, munion_free w → union_free (mval_to_val w)) ws →
    Forall munion_free ws →
    Forall union_free (mval_to_val <$> ws)).
  { induction 1; simpl; intros; decompose_Forall; auto. }
  assert (∀ ws τs,
    Forall2 (λ w _, munion_free w → union_free (mval_to_val w)) ws τs →
    Forall munion_free ws →
    Forall union_free (mval_to_val <$> ws)).
  { induction 1; simpl; intros; decompose_Forall; auto. }
  induction 1 using @mtyped_ind; simpl.
  * constructor.
  * inversion_clear 1. constructor; auto.
  * inversion_clear 1. econstructor; eauto.
  * inversion_clear 1. econstructor; eauto.
  * intros. apply val_of_bytes_union_free. constructor; eauto.
Qed.
Lemma mval_to_val_union_free m w τ :
  m ⊢ w : τ → union_free (mval_to_val w) ↔ munion_free w.
Proof.
  split; eauto using mval_to_val_union_free_2, mval_to_val_union_free_1.
Qed.

Lemma mval_of_bytes_to_val τ bs :
  type_valid get_env τ → mval_to_val (mval_of_bytes τ bs) = val_of_bytes τ bs.
Proof.
  intros Hτ. revert τ Hτ bs. refine (type_env_ind _ _ _ _).
  * intros τ ? bs. by rewrite mval_of_bytes_base, val_of_bytes_base.
  * intros. rewrite mval_of_bytes_array, val_of_bytes_array.
    simpl. erewrite array_of_bytes_fmap; eauto.
  * intros [] s τs Hs Hτs IH bs.
    { erewrite mval_of_bytes_compound, val_of_bytes_compound by eauto.
      simpl. erewrite struct_of_bytes_fmap; eauto. }
    erewrite mval_of_bytes_compound, val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|Hτ]; subst; simpl.
    { f_equal. by decompose_Forall. }
    erewrite val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst; [done|].
    pose proof (size_of_union s τs Hs). pose proof (env_valid_lookup s τs Hs).
    f_equal. clear Hs Hs Hτs Hτ.
    induction IH as [|?? Hτ]; decompose_Forall; simpl; f_equal; auto.
    by rewrite <-Hτ, mval_of_bytes_resize.
Qed.

Lemma val_of_bytes_resize τ bs sz :
  type_valid get_env τ → size_of τ ≤ sz →
  val_of_bytes τ (resize sz BUndef bs) = val_of_bytes τ bs.
Proof. intros. by rewrite <-!mval_of_bytes_to_val, mval_of_bytes_resize. Qed.
Lemma val_of_bytes_take τ bs sz :
  type_valid get_env τ → size_of τ ≤ sz →
  val_of_bytes τ (take sz bs) = val_of_bytes τ bs.
Proof. intros. by rewrite <-!mval_of_bytes_to_val, mval_of_bytes_take. Qed.
Lemma val_of_bytes_app τ bs1 bs2 :
  type_valid get_env τ → length bs1 = size_of τ →
  val_of_bytes τ (bs1 ++ bs2) = val_of_bytes τ bs1.
Proof. intros. by rewrite <-!mval_of_bytes_to_val, mval_of_bytes_app. Qed.

Lemma mval_to_val_le m w1 w2 τ :
  m ⊢ w1 : τ → w1 ⊑@{m} w2 → mval_to_val w1 ⊑@{m} mval_to_val w2.
Proof.
  intros Hw1τ. revert w1 τ Hw1τ w2. assert (∀ ws1 ws2,
    Forall (λ w1, ∀ w2,
      w1 ⊑@{m} w2 → mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 →
    ws1 ⊑@{m}* ws2 →
    Forall2 (λ w1 w2, mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 ws2).
  { induction 2; decompose_Forall; auto. }
  assert (∀ ws1 ws2 τs,
    Forall2 (λ w1 _, ∀ w2,
      w1 ⊑@{m} w2 → mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 τs →
    ws1 ⊑@{m}* ws2 →
    Forall2 (λ w1 w2, mval_to_val w1 ⊑@{m} mval_to_val w2) ws1 ws2).
  { intros ws1 ws2 τs Hws1. revert ws2.
    induction Hws1; intros; decompose_Forall; auto. }
  assert (∀ s i τs w1 τ bs,
    get_env !! s = Some τs → τs !! i = Some τ →
    m ⊢ w1 : τ →
    (∀ w2, w1 ⊑@{m} w2 → mval_to_val w1 ⊑@{m} mval_to_val w2) →
    length τs ≠ 1 →
    resize (size_of (TUnion s)) BUndef (mval_to_bytes w1) ⊑@{m}* bs →
    VUnion s i (mval_to_val w1) ⊑@{m}
      VUnionNone s (flip val_of_bytes bs <$> τs)).
  { intros s i τs w1 τ bs Hs Hi Hw1τ IH Hτs_len Hbs.
    rewrite resize_ge in Hbs by
     (erewrite mval_to_bytes_length by eauto; eauto using size_of_union_lookup).
    apply Forall2_app_inv_l in Hbs. destruct Hbs as (bs1&bs2&?&?&?); subst.
    apply VUnion_VUnionNone_le with τs (val_of_bytes τ bs1) (bs1 ++ bs2); auto.
    * rewrite list_lookup_fmap, Hi. simpl.
      f_equal. apply val_of_bytes_app; eauto using env_valid_lookup_lookup.
      erewrite <-Forall2_length; eauto using mval_to_bytes_length.
    * erewrite <-mval_of_bytes_to_val;
        eauto using mval_of_to_bytes_le, env_valid_lookup_lookup.
    * eapply Forall_app. split.
      + eauto using bytes_valid_ge, mval_to_bytes_valid.
      + eauto using bytes_valid_ge, Forall_replicate, BUndef_valid. }
  induction 1 using @mtyped_ind;
    intros w2 Hw1w2; pattern w2; apply (mval_le_inv_l _ _ _ _ Hw1w2);
    intros; simpl.
  * val_le_constructor. eauto using base_val_of_bytes_le.
  * val_le_constructor. auto using Forall2_fmap_2.
  * val_le_constructor. eauto using Forall2_fmap_2.
  * val_le_constructor. auto.
  * erewrite val_of_bytes_compound by eauto.
    by destruct (list_singleton_dec _) as [[??]|_]; subst; eauto.
  * eauto using val_of_bytes_le, TCompound_valid.
Qed.

Lemma union_to_bytes_length f sz vs bs :
  bs ∈ union_to_bytes f sz vs → length bs = sz.
Proof.
  unfold union_to_bytes. intros Hbs.
  apply elem_of_filter in Hbs. destruct Hbs as (_ & Hbs).
  revert bs Hbs. apply (intersection_with_list_ind _ (λ _, True)).
  + intros. decompose_elem_of. by apply replicate_length.
  + by apply Forall_true.
  + intros. by erewrite bytes_join_length_r by eauto.
Qed.
Lemma union_to_bytes_valid_aux m f sz vs τs bs :
  Forall2 (λ v τ, ∀ w, w ∈ f v → m ⊢ w : τ) vs τs →
  bs ∈ union_to_bytes f sz vs → Forall (byte_valid m) bs.
Proof.
  unfold union_to_bytes. intros Hvs Hbs.
  apply elem_of_filter in Hbs. destruct Hbs as (_ & Hbs).
  revert bs Hbs. apply (intersection_with_list_ind _ (Forall (byte_valid m))).
  + intros. decompose_elem_of. apply Forall_replicate, BUndef_valid.
  + unfold compose. simpl.
    induction Hvs; constructor; intros; decompose_elem_of;
       eauto using Forall_resize, BUndef_valid, mval_to_bytes_valid.
  + eauto using bytes_valid_ge, bytes_join_Some_l.
Qed.

Lemma mval_of_val_typed m v τ w : m ⊢ v : τ → w ∈ mval_of_val v → m ⊢ w : τ.
Proof.
  intros Hvτ. revert v τ Hvτ w. refine (vtyped_ind _ _ _ _ _ _ _); simpl.
  * intros. decompose_elem_of. erewrite type_of_correct by eauto.
    mtyped_constructor; eauto using
      base_typed_type_valid, base_val_to_bytes_valid,
      base_val_to_bytes_length_typed.
  * intros. decompose_elem_of. mtyped_constructor.
    + done.
    + subst. by erewrite <-mapM_length by eauto.
    + eapply elem_of_mapM_Forall; eauto.
  * intros. decompose_elem_of. mtyped_constructor; eauto.
    eapply elem_of_mapM_Forall2_l; eauto.
  * intros. decompose_elem_of. mtyped_constructor; eauto.
  * intros s vs τs bs Hs Hτs Hvsτs IH Hvs Hbs w Hw.
    apply elem_of_fmap in Hw. destruct Hw as (cs & ? & Hcs); subst.
    econstructor; eauto using union_to_bytes_valid_aux, union_to_bytes_length.
Qed.

Lemma union_to_bytes_valid m sz vs τs bs :
  bs ∈ union_to_bytes mval_of_val sz vs →
  m ⊢* vs :* τs → Forall (byte_valid m) bs.
Proof.
  intros Hbs Hvs. revert Hbs. apply union_to_bytes_valid_aux with τs.
  induction Hvs; constructor; eauto using mval_of_val_typed.
Qed.

Lemma mval_of_to_val m v τ w :
  m ⊢ v : τ → w ∈ mval_of_val v → val_map freeze v = mval_to_val w.
Proof.
  intros Hvτ. revert v τ Hvτ w.
  refine (vtyped_ind _ _ _ _ _ _ _); simpl.
  * intros. decompose_elem_of. simpl. by rewrite base_val_of_to_bytes.
  * intros vs τ n Hτ Hn _ IH w Hw.
    rewrite elem_of_fmap in Hw. destruct Hw as (ws & ? & Hws); subst.
    simpl. f_equal. rewrite elem_of_mapM in Hws.
    induction Hws; simpl; decompose_Forall; f_equal; auto.
  * intros s vs τs _ _ IH w Hw.
    rewrite elem_of_fmap in Hw. destruct Hw as (ws & ? & Hws); subst.
    simpl. f_equal. rewrite elem_of_mapM in Hws. revert τs IH.
    induction Hws; simpl; intros; decompose_Forall; f_equal; eauto.
  * intros. decompose_elem_of. simpl. f_equal. eauto.
  * intros s vs τs bs Hs Hτs Hvsτs IH Hvs Hbs w Hw.
    rewrite elem_of_fmap in Hw. destruct Hw as (cs & ? & Hcs); subst.
    simpl. erewrite val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst; [done|].
    f_equal. unfold union_to_bytes in Hcs.
    rewrite elem_of_filter in Hcs. destruct Hcs as [Hcs _].
    erewrite Hcs, list_fmap_compose, fmap_type_of by eauto.
    by rewrite vals_frozen_freeze by
      eauto using vals_of_bytes_frozen, env_valid_lookup.
Qed.

Lemma val_of_to_bytes_union_free m v τ bs :
  m ⊢ v : τ → union_free v →
  bs ∈ mval_to_bytes <$> mval_of_val v → val_of_bytes τ bs = val_map freeze v.
Proof.
  intros Hvτ ? Hbs. apply elem_of_fmap in Hbs. destruct Hbs as (w & ? & Hw).
  assert (m ⊢ w : τ) by eauto using mval_of_val_typed.
  eapply mval_of_to_val in Hw; eauto. subst.
  rewrite <-!mval_of_bytes_to_val by eauto using vtyped_type_valid.
  rewrite (mval_of_to_bytes_union_free m); eauto.
  apply mval_to_val_union_free_1. rewrite <-Hw. by apply union_free_freeze.
Qed.

Lemma union_to_of_bytes_exists_help m τs sz bs2 :
  let vs := flip val_of_bytes bs2 <$> τs in
  Forall (type_valid get_env) τs →
  Forall (λ τ, size_of τ ≤ sz) τs →
  Forall (byte_valid m) bs2 →
  Forall (λ τ, ∀ bs2, Forall (byte_valid m) bs2 →
    ∃ bs1, bs1 ∈ mval_to_bytes <$> mval_of_val (val_of_bytes τ bs2) ∧
      bs1 ⊑@{m}* resize (size_of τ) BUndef bs2) τs →
  ∃ bs1, bs1 ∈ union_to_bytes mval_of_val sz vs ∧
    bs1 ⊑@{m}* resize sz BUndef bs2.
Proof.
  intros vs Hτs Hsz Hbs2 IH. cut (∃ bs1,
    flip val_of_bytes bs1 <$> τs = flip val_of_bytes bs2 <$> τs ∧
    bs1 ∈ intersection_with_list bytes_join {[ replicate sz BUndef ]} $
      fmap (resize sz BUndef ∘ mval_to_bytes) ∘ mval_of_val <$> vs ∧
    bs1 ⊑@{m}* resize sz BUndef bs2).
  { intros (bs1 & ? & ? & ?). unfold vs. exists bs1. split; [|done].
    unfold union_to_bytes. apply elem_of_filter. split; [|done].
    rewrite list_fmap_compose, (fmap_type_of m _ τs); [done |].
    elim Hτs; simpl; constructor; auto using val_of_bytes_typed. }
  unfold vs. clear vs. revert bs2 Hbs2.
  induction IH as [|τ τs IHτ _ IHτs]; intros bs2 Hbs2; simpl.
  { eexists (replicate sz BUndef).
    rewrite elem_of_singleton. split_ands; auto.
    eapply Forall2_replicate_l; eauto using resize_length.
    eapply Forall_resize; eauto. eapply Forall_impl; eauto. by constructor. }
  rewrite Forall_cons in Hτs. destruct Hτs as [Hτ Hτs].
  rewrite Forall_cons in Hsz. destruct Hsz as [Hsz Hsz'].
  destruct (IHτ bs2) as (bs3 & Hbs3 & ?); trivial.
  assert (Forall (byte_valid m) bs3).
  { decompose_elem_of. eauto using mval_to_bytes_valid,
      mval_of_val_typed, val_of_bytes_typed, env_valid_lookup. }
  destruct (IHτs Hτs Hsz' bs2) as (bs4 & ? & Hbs4 & ?); trivial.
  assert (Forall (byte_valid m) bs4).
  { apply (union_to_bytes_valid m sz (flip val_of_bytes bs2 <$> τs) τs);
      eauto using Forall_val_of_bytes_typed.
    unfold union_to_bytes. apply elem_of_filter. split; auto.
    rewrite list_fmap_compose, (val_of_bytes_fmap_type_of m); eauto. }
  destruct (bytes_join_exists m (resize sz BUndef bs3) bs4
    (resize sz BUndef bs2)) as (bs5 & ? & ?); eauto using
    Forall2_resize_ge_r, Forall2_resize, BUndef_le, Forall_BUndef_le.
  exists bs5. split_ands.
  * eapply val_of_to_bytes_union_free in Hbs3;
      eauto using val_of_bytes_typed, val_of_bytes_union_free.
    rewrite val_frozen_freeze in Hbs3
      by eauto using val_of_bytes_frozen. f_equal.
    + rewrite (val_of_bytes_trans m τ (resize sz BUndef bs3)
        bs5 (resize sz BUndef bs2));
        rewrite ?val_of_bytes_resize by done; eauto using
        val_of_bytes_resize, @bytes_join_Some_l, Forall_resize, BUndef_valid.
    + clear dependent τ. clear Hbs4 IHτs.
      induction Hτs as [|τ τs]; simpl in *;
        decompose_Forall; simplify_list_equality; f_equal; auto.
      rewrite (val_of_bytes_trans m τ bs4 bs5 (resize sz BUndef bs2));
        rewrite ?val_of_bytes_resize by done; eauto using
        val_of_bytes_resize, @bytes_join_Some_r, Forall_resize, BUndef_valid.
  * apply elem_of_intersection_with. repeat esplit; eauto. esolve_elem_of.
  * auto.
Qed.

Lemma val_to_of_bytes_exists m τ bs2 :
  type_valid get_env τ → Forall (byte_valid m) bs2 →
  ∃ bs1, bs1 ∈ mval_to_bytes <$> mval_of_val (val_of_bytes τ bs2) ∧
    bs1 ⊑@{m}* resize (size_of τ) BUndef bs2.
Proof.
  intros Hvτ. revert τ Hvτ bs2.
  refine (type_env_ind _ _ _ _).
  * intros τ ? bs2 Hbs2. destruct (base_val_to_of_bytes_le m τ
      (resize (size_of (TBase τ)) BUndef bs2)) as (bs1 & ? & ?).
    { eauto using Forall_resize, BUndef_valid. }
    { by rewrite resize_length. }
    exists bs1. split; [|done].
    rewrite val_of_bytes_base. simpl. rewrite <-collection_fmap_compose.
    apply elem_of_fmap. by exists bs1.
  * intros τ n Hτ IH bs2 Hbs2. rewrite val_of_bytes_array. simpl.
    simpl. setoid_rewrite <-collection_fmap_compose.
    unfold compose. simpl. rewrite size_of_array.
    revert bs2 Hbs2. induction n as [|n IHn]; intros bs2 Hbs2; simpl.
    { eexists []. split. by left. by rewrite resize_0. }
    destruct (IH bs2) as (bs3 & Hbs3 & ?); trivial.
    destruct (IHn (drop (size_of τ) bs2)) as (bs4 & Hbs4 & ?);
      auto using Forall_drop.
    exists (bs3 ++ bs4). split; [| by rewrite resize_plus; apply Forall2_app].
    apply elem_of_fmap in Hbs3. destruct Hbs3 as (v & ? & ?).
    apply elem_of_fmap in Hbs4. destruct Hbs4 as (vs & ? & ?).
    apply elem_of_fmap. exists (v :: vs). split.
    { simpl. by f_equal. }
    rewrite elem_of_bind. exists v. split; [|done].
    rewrite elem_of_bind. exists vs. split; [by left|done].
  * intros [] s τs Hs Hτs IH bs2 Hbs2.
    { erewrite val_of_bytes_compound by eauto.
      simpl. setoid_rewrite <-collection_fmap_compose.
      unfold compose. simpl. erewrite size_of_struct by eauto.
      rewrite Hs; simpl; clear Hs Hτs. revert bs2 Hbs2.
      unfold struct_of_bytes. induction (size_of_struct_fields τs)
        as [|τ sz τs szs ?? IHflds]; simpl; intros bs2 Hbs2.
      { intros. eexists []. split. by left. by rewrite resize_0. }
      rewrite Forall_cons in IH. destruct IH as [IHτ IHτs].
      destruct (IHτ bs2) as (bs3 & Hbs3 & ?); trivial.
      destruct (IHflds IHτs (drop sz bs2)) as (bs4 & Hbs4 & ?);
        auto using Forall_drop.
      exists (resize sz BUndef bs3 ++ bs4). split.
      + apply elem_of_fmap in Hbs3. destruct Hbs3 as (v & ? & ?).
        apply elem_of_fmap in Hbs4. destruct Hbs4 as (vs & ? & ?).
        apply elem_of_fmap. exists (v :: vs). split.
        { simpl. f_equal. by f_equal. done. }
        simpl. rewrite elem_of_bind. exists v. split; [|done].
        rewrite elem_of_bind. exists vs. split; [by left|done].
      + rewrite resize_plus. eauto using Forall2_app,
          Forall2_resize_ge_r, BUndef_le, Forall_BUndef_le. }
    erewrite val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst.
    { rewrite Forall_singleton in IH. simpl.
      setoid_rewrite <-collection_fmap_compose. unfold compose. simpl.
      destruct (IH bs2) as (bs3 & Hbs3 & ?); trivial.
      apply elem_of_fmap in Hbs3. destruct Hbs3 as (v & ? & ?).
      exists (resize (size_of (TUnion s)) BUndef bs3).
      split; [| eauto using Forall2_resize_ge_r, BUndef_le,
        Forall_BUndef_le, size_of_union_singleton].
      apply elem_of_fmap. subst. by exists v. }
    destruct (union_to_of_bytes_exists_help m τs (size_of (TUnion s)) bs2)
      as (bs1 & ? & ?); eauto using size_of_union.
    exists bs1. split; [|done]. simpl. setoid_rewrite <-collection_fmap_compose.
    apply elem_of_fmap. by exists bs1.
Qed.

Lemma union_to_of_bytes_exists m τs sz bs2 :
  let vs := flip val_of_bytes bs2 <$> τs in
  Forall (type_valid get_env) τs →
  Forall (λ τ, size_of τ ≤ sz) τs →
  Forall (byte_valid m) bs2 →
  ∃ bs1, bs1 ∈ union_to_bytes mval_of_val sz vs ∧
    bs1 ⊑@{m}* resize sz BUndef bs2.
Proof.
  eauto using union_to_of_bytes_exists_help, Forall_impl,
    val_to_of_bytes_exists.
Qed.

Lemma mval_of_val_exists m v τ : m ⊢ v : τ → ∃ w, w ∈ mval_of_val v.
Proof.
  revert v τ. refine (vtyped_ind _ _ _ _ _ _ _); simpl.
  * intros v τ Hvτ. destruct (base_val_to_bytes_exists v) as [bs ?].
    exists (MBase τ bs). erewrite type_of_correct by eauto. esolve_elem_of.
  * intros vs τ n Hτ ? Hvs IH. subst.
    assert (∃ ws, ws ∈ mapM mval_of_val vs) as [ws ?].
    { clear Hvs. induction IH; esolve_elem_of. }
    exists (MArray τ ws). esolve_elem_of.
  * intros s vs τs Hs Hτs IH.
    assert (∃ ws, ws ∈ mapM mval_of_val vs) as [ws ?].
    { clear Hs Hτs. induction IH; esolve_elem_of. }
    exists (MStruct s ws). esolve_elem_of.
  * intros s i τs v τ Hs Hτs ? [w Hw]. exists (MUnion s i w). esolve_elem_of.
  * intros s vs τs bs Hs Hτs ??? Hbs.
    destruct (union_to_of_bytes_exists m τs (size_of (TUnion s)) bs)
      as (bs' & ? & Hbs'); eauto using size_of_union, env_valid_lookup.
    exists (MUnionNone s bs'). esolve_elem_of.
Qed.

Lemma mval_of_to_val_exists m w τ :
  m ⊢ w : τ → ∃ w', w' ∈ mval_of_val (mval_to_val w) ∧ w' ⊑@{m} w.
Proof.
  revert w τ. refine (mtyped_ind _ _ _ _ _ _ _); simpl.
  * intros τ bs ???.
    destruct (base_val_to_of_bytes_le m τ bs) as (bs' & ? & ?); trivial.
    exists (MBase τ bs'). rewrite base_val_of_bytes_type_of by done.
    split. esolve_elem_of. by constructor.
  * intros ws τ n Hτ ? Hws IH. subst.
    assert (∃ ws', ws' ∈ mapM mval_of_val (mval_to_val <$> ws) ∧
      ws' ⊑@{m}* ws) as (ws' & ? & ?).
    { clear Hws. induction IH; esolve_elem_of. }
    exists (MArray τ ws'). split. esolve_elem_of. by constructor.
  * intros s ws τs Hs Hτs IH.
    assert (∃ ws', ws' ∈ mapM mval_of_val (mval_to_val <$> ws) ∧
      ws' ⊑@{m}* ws) as (ws' & ? & ?).
    { clear Hs Hτs. induction IH; esolve_elem_of. }
    exists (MStruct s ws'). split. esolve_elem_of. by constructor.
  * intros s i τs w τ Hs Hτs ? (w' & ? & ?).
    exists (MUnion s i w'). split. esolve_elem_of. by constructor.
  * intros s τs bs Hs Hτs Hbs Hlen.
    destruct (union_to_of_bytes_exists m τs (size_of (TUnion s)) bs)
     as (bs' & Hbs' & Hbs'bs); eauto using size_of_union, env_valid_lookup.
    rewrite resize_all_alt in Hbs'bs by done.
    exists (MUnionNone s bs'). erewrite val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|_]; subst; [done |].
    split. esolve_elem_of. by constructor.
Qed.

Lemma mval_of_to_bytes_to_of_val m w τ :
  m ⊢ w : τ → ∃ w', w' ∈ mval_of_val (mval_to_val w) ∧
    w' ⊑@{m} mval_of_bytes τ (mval_to_bytes w).
Proof.
  intros. destruct (mval_of_to_val_exists m w τ) as (w'&?&?); trivial.
  exists w'. split; [done |]. rewrite (mval_of_to_bytes m) by done.
  transitivity w; eauto using munion_reset_above.
Qed.

Lemma mval_of_val_ge m v1 v2 τ w2 :
  m ⊢ v1 : τ → v1 ⊑@{m} v2 → w2 ∈ mval_of_val v2 →
  ∃ w1, w1 ∈ mval_of_val v1 ∧ w1 ⊑@{m} w2.
Proof.
  intros Hv1τ Hv1v2. revert v1 v2 Hv1v2 τ Hv1τ w2.
  refine (val_le_ind _ _ _ _ _ _ _ _ _).
  * intros v1 v2 Hv1v2 τ' Hτ'. apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'. intros τ Hv1τ w2 Hw2. simpl in *.
    apply elem_of_fmap in Hw2. destruct Hw2 as (bs2 & ? & Hbs2).
    destruct (base_val_to_bytes_ge m v1 v2 bs2) as (bs1 & ? & ?); auto.
    exists (MBase τ bs1). subst. simpl.
    erewrite !type_of_correct by eauto using base_typed_ge.
    split; [esolve_elem_of|]. by constructor.
  * intros vs1 vs2 τ _ IH τ' Hτ'. apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'. intros n Hτ Hn Hvs1 w2 Hw2. simpl in *.
    apply elem_of_fmap in Hw2. destruct Hw2 as (ws2 & ? & Hws2). subst.
    apply elem_of_mapM in Hws2. assert (∃ ws1,
      Forall2 (λ w1 v1, w1 ∈ mval_of_val v1) ws1 vs1 ∧
      ws1 ⊑@{m}* ws2) as (ws1 & ? & ?).
    { revert ws2 Hws2. induction IH; intros; decompose_Forall; naive_solver. }
    exists (MArray τ ws1); split; [|by constructor].
    apply elem_of_fmap. exists ws1. by rewrite elem_of_mapM.
  * intros s vs1 vs2 _ IH τ' Hτ'.
    apply (vtyped_inv_l _ _ _ _ Hτ'). clear τ' Hτ'.
    intros τs _ Hvs1 w2 Hw2. simpl in *.
    apply elem_of_fmap in Hw2. destruct Hw2 as (ws2 & ? & Hws2).
    subst. apply elem_of_mapM in Hws2. assert (∃ ws1,
      Forall2 (λ w1 v1, w1 ∈ mval_of_val v1) ws1 vs1 ∧
      ws1 ⊑@{m}* ws2) as (ws1 & ? & ?).
    { revert τs Hvs1 ws2 Hws2.
      induction IH; intros; decompose_Forall; naive_solver. }
    exists (MStruct s ws1); split; [|by constructor].
    apply elem_of_fmap. exists ws1. by rewrite elem_of_mapM.
  * intros s i v1 v2 Hv1v2 IH τ' Hτ'. apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'. intros τs τ Hs Hi Hv1τ w' Hw'. simpl in *. 
    apply elem_of_fmap in Hw'. destruct Hw' as (w2 & ? & Hw2). subst.
    destruct (IH _ Hv1τ _ Hw2) as (w1 & ? & ?).
    exists (MUnion s i w1). split; [esolve_elem_of |]. by constructor.
  * eauto.
  * intros s vs1 vs2 τs bs1 bs2 Hs Hvs1 Hbs1 Hvs2 Hbs Hvs _ τ' Hτ'.
    apply (vtyped_inv_l _ _ _ _ Hτ').
    clear τ' Hτ'. intros ??????? w2 Hw2. simplify_option_equality.
    apply elem_of_fmap in Hw2. destruct Hw2 as (bs4 & ? & Hbs4). subst.
    assert (length bs4 = size_of (TUnion s))
      by eauto using union_to_bytes_length.
    assert (Forall (byte_valid m) bs4).
    { eapply union_to_bytes_valid; eauto using
        Forall_val_of_bytes_typed, bytes_valid_ge, env_valid_lookup. }
    unfold union_to_bytes in Hbs4.
    apply elem_of_filter in Hbs4. destruct Hbs4 as (Hbs2 & ?).
    rewrite list_fmap_compose, (val_of_bytes_fmap_type_of m) in Hbs2
      by eauto using env_valid_lookup, bytes_valid_ge.
    rewrite <-(Forall_val_of_bytes_masked m τs bs1 bs2 bs4)
      by eauto using env_valid_lookup.
    destruct (union_to_of_bytes_exists m τs (size_of (TUnion s))
      (mask_bytes bs1 bs4)) as (bs3 & Hbs3 & Hbs3bs4);
      eauto using size_of_union, env_valid_lookup, mask_bytes_valid.
    exists (MUnionNone s bs3). split; [esolve_elem_of |].
    constructor.
    rewrite resize_all_alt in Hbs3bs4 by (by rewrite mask_bytes_length).
    transitivity (mask_bytes bs1 bs4); auto using mask_bytes_le.
  * intros s i τs v1 v2 vs2 bs2 Hs Hτs Hi Hv1 IH Hvs2 Hbs2 τ' Hτ'.
    apply (vtyped_inv_l _ _ _ _ Hτ'). clear τ' Hτ'.
    intros ? τ ? Hiτ Hv1τ w2' Hw2'. simplify_option_equality.
    apply elem_of_fmap in Hw2'. destruct Hw2' as (bs3 & Hv2 & Hbs3).
    assert (length bs3 = size_of (TUnion s))
      by eauto using union_to_bytes_length.
    unfold union_to_bytes in Hbs3.
    assert (Forall (byte_valid m) bs3).
    { eapply union_to_bytes_valid; eauto using
        Forall_val_of_bytes_typed, env_valid_lookup. }
    apply elem_of_filter in Hbs3. destruct Hbs3 as [Hbs3 ?].
    destruct (val_to_of_bytes_exists m τ bs3) as (bs1 & Hbs1 & ?);
      eauto using env_valid_lookup_lookup.
    rewrite list_fmap_compose, (val_of_bytes_fmap_type_of m) in Hbs3
      by eauto using env_valid_lookup.
    apply (f_equal (!! i)) in Hbs3.
    rewrite !list_lookup_fmap, Hiτ in Hbs3.
    rewrite !list_lookup_fmap, Hiτ in Hi.
    rewrite elem_of_fmap in Hbs1. destruct Hbs1 as (w2 & ? & Hw2).
    simplify_option_equality.
    destruct (IH τ Hv1τ w2) as (w1 & ? & ?); [by rewrite Hbs3|].
    exists (MUnion s i w1). split; [esolve_elem_of |].
    econstructor; eauto using mval_of_val_typed.
    transitivity (resize (size_of (TUnion s)) BUndef (mval_to_bytes w2));
      eauto using bytes_le_resize, mval_to_bytes_le.
    rewrite <-(resize_all_alt bs3 (size_of (TUnion s)) BUndef) by done.
    eauto using Forall2_resize_ge_r, BUndef_le, Forall_BUndef_le,
      size_of_union_lookup.
Qed.

Lemma val_lookup_nil v : v !! [] = Some v.
Proof. done. Qed.
Lemma val_lookup_cons v rs r : v !! (rs :: r) = v !! r ≫= (!! rs).
Proof. done. Qed.
Lemma val_lookup_app v r1 r2 : v !! (r1 ++ r2) = v !! r2 ≫= (!! r1).
Proof.
  induction r1 as [|rs1 r1 IH]; simpl.
  * by destruct (v !! r2).
  * by rewrite !val_lookup_cons, IH, option_bind_assoc.
Qed.
Lemma val_lookup_snoc v r rs : v !! (r ++ [rs]) = v !! rs ≫= (!! r).
Proof. apply val_lookup_app. Qed.

Lemma mval_to_val_lookup_seg w rs w' :
  w !! rs = Some w' → mval_to_val w !! rs = Some (mval_to_val w').
Proof.
  destruct w,rs; intros; simplify_option_equality.
  * rewrite list_lookup_fmap. by simplify_option_equality.
  * exfalso. eauto using fmap_length.
  * rewrite list_lookup_fmap. by simplify_option_equality.
  * done.
  * erewrite val_of_bytes_compound by eauto.
    destruct (list_singleton_dec _) as [[??]|?];
      simplify_list_equality; simplify_option_equality.
    + by rewrite mval_of_bytes_to_val, val_of_bytes_take by
        eauto using env_valid_lookup_singleton.
    + rewrite list_lookup_fmap. simplify_option_equality.
      by rewrite mval_of_bytes_to_val, val_of_bytes_take by
        eauto using env_valid_lookup_lookup.
Qed.

Lemma mval_of_val_lookup_seg m w1 τ rs v1 :
  m ⊢ w1 : τ → mval_to_val w1 !! rs = Some v1 →
  ∃ w2, w1 !! rs = Some w2 ∧ mval_to_val w2 = v1.
Proof.
  destruct 1 using @mtyped_case; destruct rs; intros; simplify_option_equality.
  * rewrite list_lookup_fmap in H7. simplify_option_equality. eauto.
  * exfalso; eauto using fmap_length.
  * rewrite list_lookup_fmap in H6. simplify_option_equality. eauto.
  * eauto.
  * erewrite val_of_bytes_compound in H8 by eauto.
    by destruct (list_singleton_dec _) as [[??]|?].
  * erewrite val_of_bytes_compound in H8 by eauto.
    by destruct (list_singleton_dec _) as [[??]|?].
  * erewrite val_of_bytes_compound in H8 by eauto.
    destruct (list_singleton_dec _) as [[??]|?]; simplify_option_equality.
    rewrite list_lookup_fmap in H8. simplify_option_equality.
    rewrite mval_of_bytes_take by eauto using env_valid_lookup_lookup.
    rewrite <-mval_of_bytes_to_val by eauto using env_valid_lookup_lookup. eauto.
Qed.

Lemma val_lookup_seg_Some m v τ rs v' :
  m ⊢ v : τ → v !! rs = Some v' → ∃ σ, τ ∙ rs ↝ σ ∧ m ⊢ v' : σ.
Proof.
  destruct 1 as [τ v|vs τ n ?? Hvs|s vs τs ? Hvs|s j τs v τ|s vs τs bs];
    destruct rs as [i|i|i]; intros Hlookup; simplify_option_equality.
  * exists τ. split.
    + constructor; eauto using lookup_lt_length_1.
    + eapply (Forall_lookup (λ v, m ⊢ v : τ)); eauto.
  * destruct (Forall2_lookup_l _ _ _ i v' Hvs) as [σ [??]]; eauto.
    exists σ. split; [|done]. econstructor; eauto.
  * exists τ. split; try econstructor; eauto.
  * edestruct @list_lookup_fmap_inv as [? [??]]; eauto.
    subst. eexists; split; try econstructor;
      eauto using val_of_bytes_typed, env_valid_lookup_lookup.
Qed.
Lemma val_lookup_Some m v τ r v' :
  m ⊢ v : τ → v !! r = Some v' → ∃ σ, τ ∙ r ↝ σ ∧ m ⊢ v' : σ.
Proof.
  revert v τ. induction r using rev_ind; intros v τ Hvτ Hr.
  * simpl in Hr. simplify_equality. eexists; split; [econstructor |]; eauto.
  * rewrite val_lookup_snoc in Hr. simplify_option_equality.
    edestruct val_lookup_seg_Some as [? [??]]; eauto.
    edestruct IHr as [? [??]]; eauto.
    eexists; split; [eapply ref_typed_snoc |]; eauto.
Qed.
Lemma val_lookup_seg_typed m v τ rs v' σ :
  m ⊢ v : τ → v !! rs = Some v' → τ ∙ rs ↝ σ → m ⊢ v' : σ.
Proof.
  intros Hvτ Hv' Hrσ.
  destruct (val_lookup_seg_Some _ _ _ _ _ Hvτ Hv') as (σ'&Hrσ'&?).
  rewrite ref_seg_lookup_correct in Hrσ, Hrσ'. by simplify_option_equality.
Qed.
Lemma val_lookup_typed m v τ r v' σ :
  m ⊢ v : τ → v !! r = Some v' → τ ∙ r ↝ σ → m ⊢ v' : σ.
Proof.
  intros Hvτ Hv' Hrσ.
  destruct (val_lookup_Some _ _ _ _ _ Hvτ Hv') as (σ'&Hrσ'&?).
  rewrite ref_lookup_correct in Hrσ, Hrσ'. by simplify_option_equality.
Qed.

Lemma val_lookup_seg_le m v1 v2 rs v3 :
  v1 ⊑@{m} v2 → v1 !! rs = Some v3 → ∃ v4, v2 !! rs = Some v4 ∧ v3 ⊑@{m} v4.
Proof.
  assert (∀ s τs i v3 bs1 bs2,
    get_env !! s = Some τs →
    bs1 ⊑@{m}* bs2 → Forall (byte_valid m) bs1 →
    (flip val_of_bytes bs1 <$> τs) !! i = Some v3 →
    ∃ v4, (flip val_of_bytes bs2 <$> τs) !! i = Some v4 ∧ v3 ⊑@{m} v4).
  { intros s τs i ? bs1 bs2 ????.
    edestruct @list_lookup_fmap_inv as [τ [??]]; eauto.
    exists (val_of_bytes τ bs2). rewrite list_lookup_fmap.
    simplify_option_equality.
    eauto using val_of_bytes_le, env_valid_lookup_lookup. }
  destruct 1; destruct rs; intros;
    repeat (case_match || simplify_option_equality);
    eauto 7 using val_of_bytes_le, env_valid_lookup_lookup,
      bytes_le_resize, Forall2_take, Forall2_lookup_l;
    exfalso; eauto using Forall2_length.
Qed.
Lemma val_lookup_seg_ge m v1 v2 rs v4 :
  v1 ⊑@{m} v2 → v2 !! rs = Some v4 →
  v1 !! rs = None ∨ ∃ v3, v1 !! rs = Some v3 ∧ v3 ⊑@{m} v4.
Proof.
  assert (∀ s τs i v4 bs1 bs2,
    get_env !! s = Some τs →
    bs1 ⊑@{m}* bs2 → Forall (byte_valid m) bs1 →
    (flip val_of_bytes bs2 <$> τs) !! i = Some v4 →
    ∃ v3, (flip val_of_bytes bs1 <$> τs) !! i = Some v3 ∧ v3 ⊑@{m} v4).
  { intros s τs i ? bs1 bs2 ????.
    edestruct @list_lookup_fmap_inv as [τ [??]]; eauto.
    exists (val_of_bytes τ bs1). rewrite list_lookup_fmap.
    simplify_option_equality.
    eauto using val_of_bytes_le, env_valid_lookup_lookup. }
  destruct 1; destruct rs; intros;
    repeat (case_match || simplify_option_equality);
    eauto 7 using mval_of_bytes_le, mval_to_bytes_le,
     env_valid_lookup_lookup, bytes_le_resize, Forall2_take, Forall2_lookup_r.
Qed.

Lemma val_lookup_le m v1 v2 r v3 :
  v1 ⊑@{m} v2 → v1 !! r = Some v3 → ∃ v4, v2 !! r = Some v4 ∧ v3 ⊑@{m} v4.
Proof.
  revert v1 v2. induction r as [|rs r IH] using rev_ind; simpl.
  * intros. rewrite val_lookup_nil. simplify_equality. eauto.
  * intros v1 v2. rewrite !val_lookup_snoc. intros. simplify_option_equality.
    edestruct (val_lookup_seg_le m v1 v2 rs) as [? [??]];
      simplify_option_equality; eauto.
Qed.
Lemma val_lookup_ge m v1 v2 r v4 :
  v1 ⊑@{m} v2 → v2 !! r = Some v4 →
  v1 !! r = None ∨ ∃ v3, v1 !! r = Some v3 ∧ v3 ⊑@{m} v4.
Proof.
  revert v1 v2. induction r as [|rs r IH] using rev_ind; simpl.
  * intros. rewrite val_lookup_nil. simplify_equality. eauto.
  * intros v1 v2. rewrite !val_lookup_snoc. intros. simplify_option_equality.
    edestruct (val_lookup_seg_ge m v1 v2 rs) as [|(?&?&?)];
      simplify_option_equality; eauto.
Qed.

Lemma val_lookup_seg_freeze rs : lookup (A:=val Ti Vi) (freeze rs) = lookup rs.
Proof. by destruct rs. Qed.
Lemma val_lookup_freeze v r : v !! (freeze <$> r) = v !! r.
Proof.
  induction r; simpl.
  * by rewrite val_lookup_nil.
  * rewrite !val_lookup_cons, val_lookup_seg_freeze. congruence.
Qed.
End val.
