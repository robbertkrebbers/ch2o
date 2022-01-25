(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export base_values memory_trees.
Local Open Scope ctype_scope.

Inductive val (K : iType) : iType :=
  | VBase : base_val K → val K
  | VArray : type K → list (val K) → val K
  | VStruct : tag → list (val K) → val K
  | VUnion : tag → nat → val K → val K
  | VUnionAll : tag → list (val K) → val K.

Declare Scope base_val.
Delimit Scope base_val with V.
Declare Scope val_scope.
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

#[global] Instance: `{Inj (=) (=) (@VBase K)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj2 (=) (=) (=) (@VArray K)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj (=) (=) (@VStruct K t)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj2 (=) (=) (=) (@VUnion K t)}.
Proof. by injection 1. Qed.
#[global] Instance: `{Inj (=) (=) (@VUnionAll K t)}.
Proof. by injection 1. Qed.

#[global] Instance maybe_VBase {K} : Maybe (@VBase K) := λ v,
  match v with VBase vb => Some vb | _ => None end.
#[global] Instance val_eq_dec `{EqDecision K}: EqDecision (val K).
Proof.
 refine (
  fix go v1 v2 := let _ : EqDecision (val K) := go in
  match v1, v2 with
  | VBase vb1, VBase vb2 => cast_if (decide (vb1 = vb2))
  | VArray τ1 vs1, VArray τ2 vs2 =>
     cast_if_and (decide (τ1 = τ2)) (decide (vs1 = vs2))
  | VStruct t1 vs1, VStruct t2 vs2 =>
     cast_if_and (decide (t1 = t2)) (decide (vs1 = vs2))
  | VUnion t1 i1 v1, VUnion t2 i2 v2 =>
     cast_if_and3 (decide (t1 = t2)) (decide (i1 = i2))
       (decide (v1 = v2))
  | VUnionAll t1 vs1, VUnionAll t2 vs2 =>
     cast_if_and (decide (t1 = t2)) (decide (vs1 = vs2))
  | _, _ => right _
  end); congruence.
Defined.

Section val_ind.
  Context {K} (P : val K → Prop).
  Context (Pbase : ∀ vb, P (VBase vb)).
  Context (Parray : ∀ τ vs, Forall P vs → P (VArray τ vs)).
  Context (Pstruct : ∀ t vs, Forall P vs → P (VStruct t vs)).
  Context (Punion : ∀ t i v, P v → P (VUnion t i v)).
  Context (Punion_all : ∀ t vs, Forall P vs → P (VUnionAll t vs)).
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

#[global] Instance val_freeze `{Env K} : Freeze (val K) :=
  fix go β v {struct v} := let _ : Freeze (val K) := @go in
  match v with
  | VBase vb => VBase (freeze β vb)
  | VArray τ vs => VArray τ (freeze β <$> vs)
  | VStruct t vs => VStruct t (freeze β <$> vs)
  | VUnion t i v => VUnion t i (freeze β v)
  | VUnionAll t vs => VUnionAll t (freeze β <$> vs)
  end.

Section operations.
  Context `{Env K}.

  Definition val_unflatten (Γ : env K) : type K → list (bit K) → val K :=
    type_iter
    (**i TBase =>     *) (λ τb bs, VBase (base_val_unflatten Γ τb bs))
    (**i TArray =>    *) (λ τ n rec bs, VArray τ (array_unflatten Γ rec τ n bs))
    (**i TCompound => *) (λ c t τs rec bs,
      match c with
      | Struct_kind => VStruct t (struct_unflatten Γ (λ τ bs,
         let τsz := bit_size_of Γ τ in rec τ (take τsz bs)) τs bs)
      | Union_kind =>
         VUnionAll t ((λ τ, rec τ (take (bit_size_of Γ τ) bs)) <$> τs)
      end) Γ.

  Inductive vals_representable (Γ : env K) (Δ : memenv K)
      (vs : list (val K)) (τs : list (type K)) : Prop :=
    make_vals_representable bs :
      ✓{Γ,Δ}* bs →
      Forall (λ τ, bit_size_of Γ τ ≤ length bs) τs →
      vs = (λ τ, val_unflatten Γ τ (take (bit_size_of Γ τ) bs)) <$> τs →
      vals_representable Γ Δ vs τs.
  Inductive val_typed' (Γ : env K) (Δ: memenv K) : val K → type K → Prop :=
    | VBase_typed vb τb :
       (Γ,Δ) ⊢ vb : τb → val_typed' Γ Δ (VBase vb) (baseT τb)
    | VArray_typed vs τ n :
       n = length vs → Forall (λ v, val_typed' Γ Δ v τ) vs → n ≠ 0 →
       val_typed' Γ Δ (VArray τ vs) (τ.[n])
    | VStruct_typed t vs τs :
       Γ !! t = Some τs → Forall2 (val_typed' Γ Δ) vs τs →
       val_typed' Γ Δ (VStruct t vs) (structT t)
    | VUnion_typed t i τs v τ :
       Γ !! t = Some τs → τs !! i = Some τ →
       val_typed' Γ Δ v τ → val_typed' Γ Δ (VUnion t i v) (unionT t)
    | VUnionAll_typed t vs τs :
       Γ !! t = Some τs → Forall2 (val_typed' Γ Δ) vs τs →
       vals_representable Γ Δ vs τs →
       val_typed' Γ Δ (VUnionAll t vs) (unionT t).
  Global Instance val_typed:
    Typed (env K * memenv K) (type K) (val K) := uncurry val_typed'.

  Lemma val_typed_inv_l Γ Δ (P : type K → Prop) v τ :
    (Γ,Δ) ⊢ v : τ →
    match v with
    | VBase vb => (∀ τb, (Γ,Δ) ⊢ vb : τb → P (baseT τb)) → P τ
    | VArray τ' vs =>
       (∀ n, n = length vs → (Γ,Δ) ⊢* vs : τ' → n ≠ 0 → P (τ'.[n])) → P τ
    | VStruct t vs =>
       (∀ τs, Γ !! t = Some τs → (Γ,Δ) ⊢* vs :* τs → P (structT t)) → P τ
    | VUnion t i v =>
       (∀ τs τ', Γ !! t = Some τs → τs !! i = Some τ' →
         (Γ,Δ) ⊢ v : τ' → P (unionT t)) → P τ
    | VUnionAll t vs =>
       (∀ τs, Γ !! t = Some τs → (Γ,Δ) ⊢* vs :* τs →
         vals_representable Γ Δ vs τs → P (unionT t)) → P τ
    end.
  Proof. destruct 1; simplify_equality; eauto. Qed.
  Lemma val_typed_inv_r Γ Δ (P : val K → Prop) v τ :
    (Γ,Δ) ⊢ v : τ →
    match τ with
    | baseT τb => (∀ vb, (Γ,Δ) ⊢ vb : τb → P (VBase vb)) → P v
    | τ'.[n] =>
       (∀ vs,
         n = length vs → (Γ,Δ) ⊢* vs : τ' → n ≠ 0 → P (VArray τ' vs)) → P v
    | structT t =>
       (∀ vs τs, Γ !! t = Some τs → (Γ,Δ) ⊢* vs :* τs →
         P (VStruct t vs)) → P v
    | unionT t =>
       (∀ i τs v' τ', Γ !! t = Some τs → τs !! i = Some τ' →
         (Γ,Δ) ⊢ v' : τ' → P (VUnion t i v')) →
       (∀ vs τs, Γ !! t = Some τs → (Γ,Δ) ⊢* vs :* τs →
         vals_representable Γ Δ vs τs → P (VUnionAll t vs)) → P v
    end.
  Proof. destruct 1; simplify_equality; eauto. Qed.
  Section val_typed_ind.
    Context (Γ : env K) (Δ : memenv K) (P : val K → type K → Prop).
    Context (Pbase : ∀ vb τb, (Γ,Δ) ⊢ vb : τb → P (VBase vb) (baseT τb)).
    Context (Parray : ∀ vs τ,
      (Γ,Δ) ⊢* vs : τ → Forall (λ v, P v τ) vs →
      length vs ≠ 0 → P (VArray τ vs) (τ.[length vs])).
    Context (Pstruct : ∀ t vs τs,
      Γ !! t = Some τs → (Γ,Δ) ⊢* vs :* τs → Forall2 P vs τs →
      P (VStruct t vs) (structT t)).
    Context (PUnion : ∀ t i τs v τ,
      Γ !! t = Some τs → τs !! i = Some τ → (Γ,Δ) ⊢ v : τ → P v τ →
      P (VUnion t i v) (unionT t)).
    Context (Punion_none : ∀ t vs τs,
      Γ !! t = Some τs → (Γ,Δ) ⊢* vs :* τs → Forall2 P vs τs →
      vals_representable Γ Δ vs τs → P (VUnionAll t vs) (unionT t)).
    Definition val_typed_ind : ∀ v τ, val_typed' Γ Δ v τ → P v τ.
    Proof.
      fix H'3 3; destruct 1; simplify_equality;
        eauto using Forall_impl, Forall2_impl.
    Qed.
  End val_typed_ind.

  Global Instance type_of_val: TypeOf (type K) (val K) := λ v,
    match v with
    | VBase vb => baseT (type_of vb)
    | VArray τ vs => τ.[length vs]
    | VStruct t _ => structT t
    | VUnion t _ _ | VUnionAll t _ => unionT t
    end.

  Definition val_new (Γ : env K) (τ : type K) : val K :=
    val_unflatten Γ τ (replicate (bit_size_of Γ τ) BIndet).
  Definition val_flatten (Γ : env K) : val K → list (bit K) :=
    fix go v :=
    match v with
    | VBase vb => base_val_flatten Γ vb
    | VArray _ vs => vs ≫= go
    | VStruct t vs =>
        from_option 
          (λ τs,
            let szs := field_bit_sizes Γ τs in
            mjoin (zip_with (λ w sz, resize sz BIndet (go w)) vs szs))
          [] (Γ !! t)
    | VUnion t i v => resize (bit_size_of Γ (unionT t)) BIndet (go v)
    | VUnionAll t vs =>
       let sz := bit_size_of Γ (unionT t) in
       default (replicate sz BIndet) (bits_list_join sz (go <$> vs))
    end.

  Fixpoint to_val (Γ : env K) (w : mtree K) : val K :=
    match w with
    | MBase τb bs => VBase (base_val_unflatten Γ τb (tagged_tag <$> bs))
    | MArray τ ws => VArray τ (to_val Γ <$> ws)
    | MStruct t wγbss => VStruct t (to_val Γ ∘ fst <$> wγbss)
    | MUnion t i w _ => VUnion t i (to_val Γ w)
    | MUnionAll t bs => val_unflatten Γ (unionT t) (tagged_tag <$> bs)
    end.
  Definition array_of_val (Γ : env K) (f : list perm → val K → mtree K) :
      list perm → list (val K) → list (mtree K) :=
    fix go γs vs :=
    match vs with
    | [] => []
    | v :: vs =>
       let sz := bit_size_of Γ (type_of v) in
       f (take sz γs) v :: go (drop sz γs) vs
    end.
  Definition struct_of_val (Γ : env K) (f : list perm → val K → mtree K) :
      list perm → list (val K) → list nat → list (mtree K * list (pbit K)) :=
    fix go γs vs pads :=
    match vs, pads with
    | v :: vs, pad :: pads =>
       let sz := bit_size_of Γ (type_of v) in
       let γs' := drop sz γs in
       (f (take sz γs) v,
        flip PBit BIndet <$> take pad γs') :: go (drop pad γs') vs pads
    | _, _ => []
    end.
  Fixpoint of_val (Γ : env K) (γs : list perm) (v : val K) : mtree K :=
    match v with
    | VBase vb =>
       MBase (type_of vb) (zip_with PBit γs (base_val_flatten Γ vb))
    | VArray τ vs => MArray τ (array_of_val Γ (of_val Γ) γs vs)
    | VStruct t vs =>
       let pads := field_bit_padding Γ (type_of <$> vs) in
       MStruct t (struct_of_val Γ (of_val Γ) γs vs pads)
    | VUnion t i v =>
       let sz := bit_size_of Γ (type_of v) in
       MUnion t i (of_val Γ (take sz γs) v) (flip PBit BIndet <$> drop sz γs)
    | VUnionAll t vs =>
       MUnionAll t (zip_with PBit γs (val_flatten Γ (VUnionAll t vs)))
    end.

  Global Instance vtype_check:
      TypeCheck (env K * memenv K) (type K) (val K) :=
    fix go (ΓΔ : _ * _) v {struct v} := let _ : TypeCheck _ _ _ := @go in
    let (Γ,Δ) := ΓΔ in
    match v with
    | VBase vb => TBase <$> type_check (Γ,Δ) vb
    | VArray τ vs =>
       guard (length vs ≠ 0);
       τs ← mapM (type_check (Γ,Δ)) vs;
       guard (Forall (τ =.) τs);
       Some (τ.[length vs])
    | VStruct t vs =>
       τs ← Γ !! t;
       τs' ← mapM (type_check (Γ,Δ)) vs;
       guard ((τs' : list (type K)) = τs);
       Some (structT t)
    | VUnion t i v =>
       τ ← Γ !! t ≫= (.!! i);
       τ' ← type_check (Γ,Δ) v;
       guard ((τ' : type K) = τ);
       Some (unionT t)
    | VUnionAll t vs =>
       τs ← Γ !! t;
       τs' ← mapM (type_check (Γ,Δ)) vs;
       guard (τs = τs');
       let sz := bit_size_of Γ (unionT t) in
       bs ← bits_list_join sz (val_flatten Γ <$> vs);
       guard (vs = (λ τ, val_unflatten Γ τ (take (bit_size_of Γ τ) bs)) <$> τs);
       Some (unionT t)
    end.

  Global Instance val_lookup_seg:
      LookupE (env K) (ref_seg K) (val K) (val K) := λ Γ rs v,
    match rs, v with
    | RArray i τ n, VArray τ' vs =>
       guard (n = length vs); guard (τ = τ'); vs !! i
    | RStruct i t, VStruct t' vs => guard (t = t'); vs !! i
    | RUnion i t β, VUnion t' j v =>
       guard (t = t');
       if decide (i = j) then Some v else
       guard (β = false);
       τ ← Γ !! t ≫= (.!! i);
       let bs := resize (bit_size_of Γ τ) BIndet (val_flatten Γ v) in
       Some (val_unflatten Γ τ bs)
    | RUnion i t _, VUnionAll t' vs => guard (t = t'); vs !! i
    | _, _ => None
    end.
  Global Instance val_lookup: LookupE (env K) (ref K) (val K) (val K) :=
    fix go Γ r v {struct r} := let _ : LookupE _ _ _ _ := @go in
    match r with [] => Some v | rs :: r => v !!{Γ} r ≫= lookupE Γ rs end.
  Definition val_alter_seg (Γ : env K) (g : val K → val K)
      (rs : ref_seg K) (v : val K) : val K :=
    match rs, v with
    | RArray i _ _, VArray τ vs => VArray τ (alter g i vs)
    | RStruct i _, VStruct t vs => VStruct t (alter g i vs)
    | RUnion i _ _, VUnion t j v' =>
        if decide (i = j) then VUnion t i (g v')
        else from_option 
          (λ τ,
            let bs := resize (bit_size_of Γ τ) BIndet (val_flatten Γ v) in
            VUnion t i (g (val_unflatten Γ τ bs)))
          v (Γ !! t ≫= (.!! i))
    | RUnion i t _, VUnionAll _ vs => from_option (VUnion t i ∘ g) v (vs !! i)
    | _, _ => v
    end.
  Fixpoint val_alter (Γ : env K) (g : val K → val K)
      (r : ref K) : val K → val K :=
    match r with [] => g | rs :: r => val_alter Γ (val_alter_seg Γ g rs) r end.

  Inductive val_union_free : val K → Prop :=
    | VBase_union_free vb : val_union_free (VBase vb)
    | VArray_union_free τ vs :
       Forall (val_union_free) vs → val_union_free (VArray τ vs)
    | VStruct_union_free t vs :
       Forall val_union_free vs → val_union_free (VStruct t vs)
    | VUnionAll_union_free t vs :
       Forall val_union_free vs → val_union_free (VUnionAll t vs).
  Section val_union_free_ind.
    Context (Γ : env K) (P : val K → Prop).
    Context (Pbase : ∀ vb, P (VBase vb)).
    Context (Parray : ∀ τ vs,
      Forall val_union_free vs → Forall P vs → P (VArray τ vs)).
    Context (Pstruct : ∀ t vs,
      Forall val_union_free vs → Forall P vs → P (VStruct t vs)).
    Context (Punion_none : ∀ t vs,
      Forall val_union_free vs → Forall P vs → P (VUnionAll t vs)).
    Definition val_union_free_ind_alt: ∀ v, val_union_free v → P v.
    Proof. fix H'2 2; destruct 1; eauto using Forall_impl. Qed.
  End val_union_free_ind.
  Global Instance val_union_free_dec: ∀ v, Decision (val_union_free v).
  Proof.
   refine (
    fix go v :=
    match v return Decision (val_union_free v) with
    | VBase v => left _
    | VArray _ vs => cast_if (decide (Forall val_union_free vs))
    | VStruct _ vs => cast_if (decide (Forall val_union_free vs))
    | VUnion t i v => right _
    | VUnionAll _ vs => cast_if (decide (Forall val_union_free vs))
    end); clear go; abstract first [by constructor | by inversion 1].
  Defined.
End operations.

Section values.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types α : bool.
Implicit Types Δ : memenv K.
Implicit Types τb : base_type K.
Implicit Types τ : type K.
Implicit Types τs : list (type K).
Implicit Types b : bit K.
Implicit Types bs : list (bit K).
Implicit Types γ : perm.
Implicit Types γs : list perm.
Implicit Types γb : pbit K.
Implicit Types γbs : list (pbit K).
Implicit Types w : mtree K.
Implicit Types ws : list (mtree K).
Implicit Types rs : ref_seg K.
Implicit Types r : ref K.
Implicit Types vb : base_val K.
Implicit Types v : val K.
Implicit Types vs : list (val K).
Notation vals_unflatten Γ τs bs :=
  ((λ τ, val_unflatten Γ τ (take (bit_size_of Γ τ) bs)) <$> τs).

Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Hint Extern 0 (_ ⊑* _) => reflexivity: core.
Hint Resolve Forall_take Forall_drop Forall_app_2
  Forall_replicate Forall_resize: core.
Hint Resolve Forall2_take Forall2_drop Forall2_app
  Forall2_replicate Forall2_resize: core.
Hint Resolve BIndet_valid BIndet_weak_refine: core.
Hint Immediate env_valid_lookup env_valid_lookup_lookup: core.

(** ** Properties of the [val_flatten] function *)
Lemma val_flatten_length Γ Δ τ v :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length (val_flatten Γ v) = bit_size_of Γ τ.
Proof.
  intros HΓ Hvτ. revert v τ Hvτ. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros. by erewrite base_val_flatten_length by eauto.
  * intros vs τ _ IH _. rewrite bit_size_of_array.
    induction IH; csimpl; rewrite ?app_length; auto.
  * intros t vs τs Ht Hvs IH.
    rewrite (bit_size_of_struct _ _ τs), Ht by done; simpl; clear Ht.
    revert vs Hvs IH. induction (bit_size_of_fields _ τs HΓ)
      as [|τ sz ?? Hn]; intros; decompose_Forall_hyps; [done |].
    rewrite app_length, resize_length; f_equal. eauto.
  * intros. by rewrite resize_length.
  * intros t vs τs Ht Hvs IH Hrep.
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs'; simpl.
    + eauto using bits_list_join_length.
    + by rewrite replicate_length.
Qed.
Lemma val_flatten_valid Γ Δ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → ✓{Γ,Δ}* (val_flatten Γ v).
Proof.
  intros HΓ Hvτ. revert v τ Hvτ. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * eauto using base_val_flatten_valid.
  * intros vs τ Hvs IH _. induction IH; decompose_Forall_hyps; auto.
  * intros t vs τs Ht Hvs IH. rewrite Ht. simpl; clear Ht. revert vs Hvs IH.
    induction (bit_size_of_fields _ τs HΓ);intros; decompose_Forall_hyps; auto.
  * eauto.
  * intros t vs τs Ht Hvs IH Hrep.
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs'; simpl; auto.
    eapply bits_list_join_valid; eauto. elim IH; csimpl; auto.
Qed.
Lemma val_flatten_weaken Γ1 Γ2 Δ1 v τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ1) ⊢ v : τ → val_flatten Γ1 v = val_flatten Γ2 v.
Proof.
  intros ??. revert v τ. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * eauto using base_val_flatten_weaken.
  * intros vs τ _ IH _. induction IH; f_equal'; auto.
  * intros t vs τs Ht _ IH.
    erewrite Ht, lookup_compound_weaken by eauto; simpl.
    erewrite field_bit_sizes_weaken by eauto; f_equal; clear Ht.
    generalize (field_bit_sizes Γ2 τs).
    induction IH; intros [|??]; f_equal'; auto with f_equal.
  * intros; f_equal; eauto using bit_size_of_weaken, TCompound_valid.
  * intros t vs τs Ht _ IH _;
      do 2 f_equal; eauto using bit_size_of_weaken, TCompound_valid.
    elim IH; intros; f_equal'; auto.
Qed.

Ltac solve_length := repeat first
  [ rewrite take_length | rewrite drop_length | rewrite app_length
  | rewrite resize_length | rewrite fmap_length | rewrite replicate_length
  | erewrite ctree_flatten_length by eauto|erewrite val_flatten_length by eauto
  | rewrite zip_with_length | erewrite base_val_flatten_length by eauto
  | match goal with
    | |- context [ bit_size_of ?Γ ?τ ] =>
      match goal with
      | H : Γ !! ?t = Some ?τs, H2 : ?τs !! _ = Some τ |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t))
          by eauto using bit_size_of_union_lookup
      | H : Γ !! ?t = Some [?τ] |- _ =>
        unless (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t)) by done;
        assert (bit_size_of Γ τ ≤ bit_size_of Γ (unionT t))
          by eauto using bit_size_of_union_singleton
      end
    end]; lia.
Hint Extern 0 (length _ = _) => solve_length: core.
Hint Extern 0 (_ ≤ length _) => solve_length: core.
Hint Extern 0 (length _ ≤ _) => solve_length: core.

(** ** Properties of the [val_unflatten] function *)
Lemma val_unflatten_base Γ τb :
  val_unflatten Γ τb = λ bs, VBase (base_val_unflatten Γ τb bs).
Proof. unfold val_unflatten. by rewrite type_iter_base. Qed. 
Lemma val_unflatten_array Γ τ n :
  val_unflatten Γ (τ.[n]) = λ bs,
    VArray τ (array_unflatten Γ (val_unflatten Γ τ) τ n bs).
Proof. unfold val_unflatten. by rewrite type_iter_array. Qed.
Lemma val_unflatten_compound Γ c t τs bs :
  ✓ Γ → Γ !! t = Some τs → val_unflatten Γ (compoundT{c} t) bs =
    match c with
    | Struct_kind => VStruct t (struct_unflatten Γ (λ τ bs,
       let τsz := bit_size_of Γ τ in val_unflatten Γ τ (take τsz bs)) τs bs)
    | Union_kind => VUnionAll t (vals_unflatten Γ τs bs)
    end.
Proof.
  intros HΓ Ht. unfold val_unflatten. erewrite (type_iter_compound
    (pointwise_relation (list (bit K)) (@eq (val K))) _ _ _ _); try done.
  { intros ???????; f_equal. by apply array_unflatten_weaken. }
  clear t τs Ht bs. intros f g [] t τs Ht Hτs ? bs; f_equal.
  { eapply struct_unflatten_weaken, Forall_impl; eauto. }
  eapply Forall_fmap_ext, Forall_impl; eauto.
Qed.
Lemma val_unflatten_weaken Γ1 Γ2 τ bs :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → val_unflatten Γ1 τ bs = val_unflatten Γ2 τ bs.
Proof.
  intros. apply (type_iter_weaken (pointwise_relation _ (=))); try done.
  { intros ???. by erewrite base_val_unflatten_weaken by eauto. }
  { intros ???????; f_equal. by apply array_unflatten_weaken. }
  clear bs. intros f g [] t τs Ht Hτs Hfg bs; f_equal; auto.
  { eapply struct_unflatten_weaken, Forall_impl; eauto 1; intros; simpl.
    erewrite bit_size_of_weaken by eauto; auto. }
  clear Ht. induction Hfg; decompose_Forall_hyps; f_equal; auto.
  erewrite bit_size_of_weaken by eauto; auto.
Qed.
Lemma vals_unflatten_weaken Γ1 Γ2 τs bs :
  ✓ Γ1 → ✓{Γ1}* τs → Γ1 ⊆ Γ2 →
  vals_unflatten Γ1 τs bs = vals_unflatten Γ2 τs bs.
Proof.
  induction 2; intros; f_equal'; auto.
  by erewrite bit_size_of_weaken, val_unflatten_weaken by eauto.
Qed.
Lemma val_unflatten_typed Γ Δ τ bs :
  ✓ Γ → ✓{Γ} τ → ✓{Γ,Δ}* bs → length bs = bit_size_of Γ τ →
  (Γ,Δ) ⊢ val_unflatten Γ τ bs : τ.
Proof.
  intros HΓ Hτ. revert τ Hτ bs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb Hτ bs Hbs Hbs'. rewrite val_unflatten_base.
    typed_constructor; auto using base_val_unflatten_typed.
  * intros τ n Hτ IH Hn bs; rewrite val_unflatten_array, bit_size_of_array.
    intros Hbs Hbs'. typed_constructor; eauto using array_unflatten_length.
    revert bs Hbs Hbs'. clear Hn. induction n; simpl; auto.
  * intros [] t τs Ht Hτs IH _ bs; erewrite val_unflatten_compound,
       ?bit_size_of_struct by eauto; intros Hbs Hbs'.
    { typed_constructor; eauto. unfold struct_unflatten.
      revert bs Hbs Hbs'. clear Ht Hτs. induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps; auto. }
    typed_constructor; eauto.
    { clear Hτs. pose proof (bit_size_of_union _ _ _ HΓ Ht); clear Ht.
      induction IH; decompose_Forall_hyps; auto. }
    exists bs; auto. rewrite Hbs'. auto using bit_size_of_union.
Qed.
Lemma vals_unflatten_typed Γ Δ τs bs :
  ✓ Γ → ✓{Γ}* τs → ✓{Γ,Δ}* bs → Forall (λ τ, bit_size_of Γ τ ≤ length bs) τs →
  (Γ,Δ) ⊢* vals_unflatten Γ τs bs :* τs.
Proof.
  induction 2; intros; decompose_Forall_hyps; auto using val_unflatten_typed.
Qed.
Lemma vals_representable_typed Γ Δ vs τs :
  ✓ Γ → ✓{Γ}* τs → vals_representable Γ Δ vs τs → (Γ,Δ) ⊢* vs :* τs.
Proof. intros ?? [bs ?? ->]. auto using vals_unflatten_typed. Qed.
Lemma val_unflatten_type_of Γ τ bs :
  ✓ Γ → ✓{Γ} τ → type_of (val_unflatten Γ τ bs) = τ.
Proof.
  intros HΓ Hτ. revert τ Hτ bs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb _ bs. rewrite val_unflatten_base; simpl.
    by rewrite base_val_unflatten_type_of.
  * intros τ [|n] _ IH ? bs; [done|]. rewrite val_unflatten_array; simpl.
    by rewrite array_unflatten_length.
  * intros [] t τs ? _ _ _ bs; by erewrite val_unflatten_compound by eauto.
Qed.
Lemma vals_unflatten_type_of Γ τs bs :
  ✓ Γ → ✓{Γ}* τs → type_of <$> vals_unflatten Γ τs bs = τs.
Proof. induction 2; f_equal'; auto using val_unflatten_type_of. Qed.
Lemma vals_unflatten_representable Γ Δ bs τs :
  ✓{Γ,Δ}* bs → Forall (λ τ, bit_size_of Γ τ ≤ length bs) τs →
  vals_representable Γ Δ (vals_unflatten Γ τs bs) τs.
Proof. by exists bs. Qed.
Lemma val_unflatten_frozen Γ Δ τ bs :
  ✓ Γ → ✓{Γ} τ → ✓{Γ,Δ}* bs →
  freeze true (val_unflatten Γ τ bs) = val_unflatten Γ τ bs.
Proof.
  intros HΓ Hτ. revert τ Hτ bs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite val_unflatten_base; simpl.
    by rewrite base_val_unflatten_frozen by eauto.
  * intros τ n _ IH _ bs Hbs.
    rewrite val_unflatten_array; f_equal'. revert bs Hbs.
    induction n; intros; f_equal'; auto.
  * intros [] t τs Ht _ IH _ bs Hbs;
      erewrite val_unflatten_compound by eauto; f_equal'; clear Ht.
    { unfold struct_unflatten. revert bs Hbs.
      induction (bit_size_of_fields _ τs HΓ); intros;
        decompose_Forall_hyps; f_equal; auto. }
    revert bs Hbs; induction IH; intros; f_equal'; eauto.
Qed.
Lemma vals_unflatten_frozen Γ Δ τs bs :
  ✓ Γ → ✓{Γ}* τs → ✓{Γ,Δ}* bs →
  freeze true <$> vals_unflatten Γ τs bs = vals_unflatten Γ τs bs.
Proof. induction 2; intros; f_equal'; eauto using val_unflatten_frozen. Qed.
Lemma val_unflatten_union_free Γ τ bs :
  ✓ Γ → ✓{Γ} τ → val_union_free (val_unflatten Γ τ bs).
Proof.
  intros HΓ Hτ. revert τ Hτ bs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite val_unflatten_base. by constructor.
  * intros τ n _ IH _ bs. rewrite val_unflatten_array. constructor.
    revert bs. induction n; simpl; auto.
  * intros [] t τs Ht _ IH _ bs; erewrite !val_unflatten_compound by eauto.
    { constructor. unfold struct_unflatten. revert bs. clear Ht.
      induction (bit_size_of_fields _ τs HΓ);
        intros; decompose_Forall_hyps; auto. }
    constructor. elim IH; csimpl; auto.
Qed.
Lemma vals_representable_union_free Γ Δ vs τs :
  ✓ Γ → ✓{Γ}* τs → vals_representable Γ Δ vs τs → Forall val_union_free vs.
Proof.
  intros ? Hτs [bs _ _ ->].
  induction Hτs; constructor; auto using val_unflatten_union_free.
Qed.
Lemma val_unflatten_between Γ τ bs1 bs2 bs3 :
  ✓ Γ → ✓{Γ} τ → bs1 ⊑* bs2 → bs2 ⊑* bs3 → length bs1 = bit_size_of Γ τ →
  val_unflatten Γ τ bs1 = val_unflatten Γ τ bs3 →
  val_unflatten Γ τ bs2 = val_unflatten Γ τ bs3.
Proof.
  intros HΓ Hτ. revert τ Hτ bs1 bs2 bs3. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb ? bs1 bs2 bs3 ??.
    rewrite !val_unflatten_base, !(inj_iff VBase).
    by apply base_val_unflatten_between.
  * intros τ n ? IH _ bs1 bs2 bs3 Hbs1 Hbs2. rewrite !val_unflatten_array,
       bit_size_of_array, !(inj_iff (VArray _)).
    revert bs1 bs2 bs3 Hbs1 Hbs2.
    induction n; intros; simplify_equality'; f_equal'; eauto.
  * intros [] t τs Ht Hτs IH _ bs1 bs2 bs3 Hbs1 Hbs2;
      erewrite !val_unflatten_compound, ?bit_size_of_struct by eauto.
    { rewrite !(inj_iff (VStruct t)). clear Ht Hτs.
      revert bs1 bs2 bs3 Hbs1 Hbs2. unfold struct_unflatten.
      induction (bit_size_of_fields _ τs HΓ); intros ???; simpl;
        rewrite ?take_take; intros; decompose_Forall_hyps; f_equal; eauto. }
    pose proof (bit_size_of_union _ _ _ HΓ Ht). clear Ht Hτs.
    rewrite !(inj_iff (VUnionAll t)). revert bs1 bs2 bs3 Hbs1 Hbs2.
    induction IH; intros; decompose_Forall_hyps; f_equal; eauto.
Qed.
Lemma vals_unflatten_between Γ τs bs1 bs2 bs3 :
  ✓ Γ → ✓{Γ}* τs → bs1 ⊑* bs2 → bs2 ⊑* bs3 →
  Forall (λ τ, bit_size_of Γ τ ≤ length bs1) τs →
  vals_unflatten Γ τs bs1 = vals_unflatten Γ τs bs3 →
  vals_unflatten Γ τs bs2 = vals_unflatten Γ τs bs3.
Proof.
  induction 2; intros; decompose_Forall_hyps; f_equal;
    eauto using val_unflatten_between.
Qed.
Global Opaque val_unflatten.

(** ** General properties of the typing judgment *)
Lemma val_typed_int_frozen Γ Δ v τi : (Γ,Δ) ⊢ v : intT τi → frozen v.
Proof.
  inversion_clear 1; unfold frozen; simpl.
  by erewrite base_typed_int_frozen by eauto.
Qed.
Lemma val_union_free_base Γ Δ v τb : (Γ,Δ) ⊢ v : baseT τb → val_union_free v.
Proof. inversion 1; constructor. Qed.
Lemma val_typed_type_valid Γ Δ v τ : ✓ Γ → (Γ,Δ) ⊢ v : τ → ✓{Γ} τ.
Proof.
  induction 2 using @val_typed_ind; econstructor; decompose_Forall_hyps;
    try match goal with
    | H : length ?vs ≠ 0, H2 : Forall _ ?vs |- _ => destruct H2; [done|]
    end; eauto; eapply base_val_typed_type_valid; eauto.
Qed.
Lemma val_typed_types_valid Γ Δ vs τs : ✓ Γ → (Γ,Δ) ⊢* vs :* τs → ✓{Γ}* τs.
Proof. induction 2; constructor; eauto using val_typed_type_valid. Qed.
#[global] Instance: TypeOfSpec (env K * memenv K) (type K) (val K).
Proof.
  intros [Γ Δ]. induction 1 using @val_typed_ind; decompose_Forall_hyps;
    f_equal; eauto; eapply type_of_correct; eauto.
Qed.
Lemma vals_representable_weaken Γ1 Γ2 Δ1 Δ2 vs τs :
  ✓ Γ1 → ✓{Γ1}* τs → vals_representable Γ1 Δ1 vs τs → Γ1 ⊆ Γ2 →
  Δ1 ⇒ₘ Δ2 → vals_representable Γ2 Δ2 vs τs.
Proof.
  intros ? Hτs [bs ? Hlen Hvs]. exists bs.
  * eauto using Forall_impl, bit_valid_weaken.
  * clear Hvs. induction Hτs; decompose_Forall_hyps; constructor; auto 2.
    by erewrite <-bit_size_of_weaken by eauto.
  * by erewrite <-vals_unflatten_weaken by eauto.
Qed.
Lemma val_typed_weaken Γ1 Γ2 Δ1 Δ2 v τ :
  ✓ Γ1 → (Γ1,Δ1) ⊢ v : τ → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → (Γ2,Δ2) ⊢ v : τ.
Proof.
  intros ? Hvτ ??. induction Hvτ using @val_typed_ind; econstructor;
    erewrite <-1?vals_unflatten_weaken;
    erewrite <-1?bit_size_of_weaken by eauto using TCompound_valid;
    eauto using base_val_typed_weaken, lookup_compound_weaken,  Forall_impl,
      vals_representable_weaken, bit_valid_weaken, val_typed_types_valid.
Qed.
Lemma VArray_frozen τ vs : frozen (VArray τ vs) ↔ Forall frozen vs.
Proof.
  unfold frozen; split; [|intros Hvs; f_equal'; induction Hvs; f_equal'; auto].
  intros; simplify_equality'. induction vs; simplify_equality'; auto.
Qed.
Lemma val_freeze_freeze β1 β2 v : freeze β1 (freeze β2 v) = freeze β1 v.
Proof.
  assert (∀ vs,
    Forall (λ v, freeze β1 (freeze β2 v) = freeze β1 v) vs →
    freeze β1 <$> (freeze β2 <$> vs) = freeze β1 <$> vs).
  { induction 1; f_equal'; auto. }
  induction v using val_ind_alt; f_equal'; auto using base_val_freeze_freeze.
Qed.
Lemma vals_freeze_freeze β1 β2 vs :
  freeze β1 <$> (freeze β2 <$> vs) = freeze β1 <$> vs.
Proof. induction vs; f_equal'; auto using val_freeze_freeze. Qed.
Lemma vals_representable_freeze Γ m vs τs :
  ✓ Γ → ✓{Γ}* τs → vals_representable Γ m vs τs →
  vals_representable Γ m (freeze true <$> vs) τs.
Proof. intros ?? [bs ?? ->]. exists bs; eauto using vals_unflatten_frozen. Qed.
Lemma val_typed_freeze Γ Δ v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → (Γ,Δ) ⊢ freeze true v : τ.
Proof.
  induction 2 using @val_typed_ind; simplify_equality'.
  * typed_constructor. by apply base_typed_freeze.
  * typed_constructor; auto using fmap_length. by apply Forall_fmap.
  * typed_constructor; eauto. by apply Forall2_fmap_l.
  * typed_constructor; eauto.
  * typed_constructor; eauto using vals_representable_freeze.
    by apply Forall2_fmap_l.
Qed.
Lemma val_union_free_freeze β v :
  val_union_free (freeze β v) ↔ val_union_free v.
Proof.
  split.
  * assert (∀ vs,
      Forall (λ v, val_union_free (freeze β v) → val_union_free v) vs →
      Forall val_union_free (freeze β <$> vs) →
      Forall val_union_free vs).
    { induction 1; csimpl; intros; decompose_Forall; eauto. } 
    induction v using val_ind_alt; inversion_clear 1; econstructor; eauto.
  * induction 1 using @val_union_free_ind_alt; simpl;
      econstructor; eauto; by apply Forall_fmap.
Qed.

(** ** Interaction between [val_flatten] and [val_unflatten] *)
Lemma val_union_to_bits_valid Γ Δ sz vs τs bs :
  ✓ Γ → bits_list_join sz (val_flatten Γ <$> vs) = Some bs →
  (Γ,Δ) ⊢* vs :* τs → ✓{Γ,Δ}* bs.
Proof.
  intros ? Hbs Hvs. eapply bits_list_join_valid; eauto.
  elim Hvs; intros; constructor; eauto using val_flatten_valid.
Qed.
Lemma val_flatten_unflatten Γ Δ τ bs :
  ✓ Γ → ✓{Γ} τ → ✓{Γ,Δ}* bs → length bs = bit_size_of Γ τ →
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
  * intros [] t τs Ht Hτs IH _ bs; erewrite val_unflatten_compound,
      ?bit_size_of_struct by eauto; simpl; intros Hbs Hbs'.
    { rewrite Ht. simpl. clear Ht Hτs. revert bs Hbs Hbs'.
      unfold struct_unflatten. induction (bit_size_of_fields _ τs HΓ)
        as [|τ sz τs szs]; intros bs ??; decompose_Forall_hyps.
      { by erewrite nil_length_inv by eauto. }
      apply Forall2_app_l; rewrite resize_length, <-?(resize_le _ _ BIndet),
        ?resize_resize by done; eauto using Forall2_resize_r, Forall_true. }
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs''; simpl.
    { apply bit_size_of_union in Ht; auto. revert bs' Hbs''.
      induction IH as [|τ τs]; intros bs' Hbs'';
        decompose_Forall_hyps; simplify_option_eq.
      { eauto using Forall2_replicate_l, resize_length, Forall_true. }
      eapply bits_join_min; eauto. rewrite <-?(resize_le _ _ BIndet) by done.
      eauto using Forall2_resize_r_flip, Forall_true. }
    auto using Forall2_replicate_l, Forall_true, resize_length.
Qed.
Lemma vals_representable_as_bits_aux Γ Δ sz vs τs :
  ✓ Γ → ✓{Γ}* τs → Forall (λ τ, bit_size_of Γ τ ≤ sz) τs →
  Forall2 (λ v τ, val_union_free v →
    val_unflatten Γ τ (val_flatten Γ v) = freeze true v) vs τs →
  vals_representable Γ Δ vs τs →
  ∃ bs, bits_list_join sz (val_flatten Γ <$> vs) = Some bs ∧
    ✓{Γ,Δ}* bs ∧ vs = vals_unflatten Γ τs bs.
Proof.
  intros HΓ Hτs Ht IH [bs' ? Hlen ->].
  destruct (bits_list_join_exists sz (val_flatten Γ <$> vals_unflatten Γ τs bs')
    (resize sz BIndet bs')) as (bs&Hbs&Hbsbs').
  { by rewrite resize_length. }
  { clear IH. induction Hτs; decompose_Forall_hyps; constructor; auto.
    rewrite <-?(resize_le _ _ BIndet) by done.
    eauto using Forall2_resize_r, Forall_true, val_flatten_unflatten. }
  exists bs. split_and ?; [done| |].
  { assert ((Γ,Δ) ⊢* vals_unflatten Γ τs bs' :* τs) as Hτs'
      by auto using vals_unflatten_typed.
    eapply bits_list_join_valid; eauto. clear Ht IH Hbs Hbsbs'.
    induction Hτs'; decompose_Forall_hyps; eauto using val_flatten_valid. }
  apply bits_list_join_Some_alt in Hbs.
  induction Hτs as [|τ τs ?? IHτs]; simplify_equality'; auto.
  apply Forall2_cons_1 in IH; destruct IH as [IH IH'].
  apply Forall_cons in Hbs; destruct Hbs as [Hbs Hbs'].
  decompose_Forall_hyps; f_equal; auto; clear IH' Hbs' IHτs.
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
Lemma val_unflatten_flatten Γ Δ τ v :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → val_union_free v →
  val_unflatten Γ τ (val_flatten Γ v) = freeze true v.
Proof.
  intros HΓ. revert v τ. refine (val_typed_ind _ _ _ _ _ _ _ _).
  * intros vb τb ? _. rewrite val_unflatten_base; f_equal'.
    eauto using base_val_unflatten_flatten.
  * intros vs τ ? IH _; inversion_clear 1.
    rewrite val_unflatten_array; f_equal'.
    induction IH; decompose_Forall_hyps;
      rewrite ?take_app_alt, ?drop_app_alt by auto; f_equal; auto.
  * intros t vs τs Ht Hvs IH; inversion_clear 1.
    erewrite val_unflatten_compound by eauto; simpl; rewrite Ht. f_equal'.
    unfold struct_unflatten. clear Ht. revert dependent vs.
    induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
      rewrite ?take_app_alt, ?drop_app_alt; f_equal; auto.
    rewrite take_resize_le, resize_all_alt by auto; auto.
  * intros t i τs v τ Ht Hτs Hv IH. inversion_clear 1.
  * intros t vs τs Ht Hvs IH Hrepr _.
    erewrite val_unflatten_compound by eauto; simpl.
    destruct (vals_representable_as_bits_aux Γ Δ
      (bit_size_of Γ (unionT t)) vs τs) as (bs&->&?&->);
      eauto using bit_size_of_union; simpl.
    by erewrite vals_unflatten_frozen by eauto.
Qed.
Lemma vals_representable_as_bits Γ Δ sz vs τs :
  ✓ Γ → ✓{Γ}* τs → Forall (λ τ, bit_size_of Γ τ ≤ sz) τs →
  vals_representable Γ Δ vs τs →
  ∃ bs, bits_list_join sz (val_flatten Γ <$> vs) = Some bs ∧ length bs = sz ∧
    ✓{Γ,Δ}* bs ∧ vs = vals_unflatten Γ τs bs.
Proof.
  intros ??? Hvs. destruct (vals_representable_as_bits_aux Γ Δ sz vs τs)
    as (?&?&?&?); eauto 6 using bits_list_join_length.
  apply vals_representable_typed in Hvs; auto.
  elim Hvs; constructor; eauto using val_unflatten_flatten.
Qed.

(** ** Properties of the [val_new] function *)
Lemma val_new_base Γ τb :
  val_new Γ τb = VBase (if decide (τb = voidT%BT) then VVoid else VIndet τb).
Proof.
  unfold val_new; rewrite val_unflatten_base. case_decide; subst; [done|].
  by rewrite base_val_unflatten_indet by auto.
Qed.
Lemma val_new_array Γ τ n :
  val_new Γ (τ.[n]) = VArray τ (replicate n (val_new Γ τ)).
Proof.
  unfold val_new; rewrite val_unflatten_array, bit_size_of_array; f_equal.
  by induction n; f_equal'; rewrite ?take_replicate_plus, ?drop_replicate_plus.
Qed.
Lemma val_new_compound Γ c t τs :
  ✓ Γ → Γ !! t = Some τs → val_new Γ (compoundT{c} t) =
    match c with
    | Struct_kind => VStruct t (val_new Γ <$> τs)
    | Union_kind => VUnionAll t (val_new Γ <$> τs)
    end.
Proof.
  intros HΓ Ht. unfold val_new; erewrite val_unflatten_compound by eauto.
  destruct c; f_equal.
  * erewrite ?bit_size_of_struct by eauto; clear Ht.
    unfold struct_unflatten, field_bit_padding.
    by induction (bit_size_of_fields _ τs HΓ); decompose_Forall_hyps;
      rewrite ?take_replicate_plus, ?drop_replicate_plus, ?take_replicate,
      ?drop_replicate, ?Min.min_l, ?fmap_replicate by done; repeat f_equal.
  * eapply Forall_fmap_ext, Forall_impl; [eapply bit_size_of_union; eauto|].
    intros. by rewrite take_replicate, Min.min_l by done.
Qed.
Lemma val_new_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → val_new Γ1 τ = val_new Γ2 τ.
Proof.
  intros. unfold val_new.
  by erewrite val_unflatten_weaken, bit_size_of_weaken by eauto.
Qed.
Lemma val_new_typed Γ Δ τ : ✓ Γ → ✓{Γ} τ → (Γ,Δ) ⊢ val_new Γ τ : τ.
Proof. intros; apply val_unflatten_typed; auto using replicate_length. Qed.
Lemma vals_new_typed Γ Δ τs :
  ✓ Γ → ✓{Γ}* τs → (Γ,Δ) ⊢* val_new Γ <$> τs :* τs.
Proof. induction 2; simpl; eauto using val_new_typed. Qed.
Lemma val_new_type_of Γ τ : ✓ Γ → ✓{Γ} τ → type_of (val_new Γ τ) = τ.
Proof. by apply val_unflatten_type_of. Qed.
Lemma val_new_frozen Γ τ : ✓ Γ → ✓{Γ} τ → frozen (val_new Γ τ).
Proof. intros. apply (val_unflatten_frozen Γ ∅); auto. Qed.

(** ** Properties of the [to_val] function *)
Lemma to_val_typed Γ Δ w τ :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → (Γ,Δ) ⊢ to_val Γ w : τ.
Proof.
  intros HΓ. induction 1 using @ctree_typed_ind; simpl.
  * typed_constructor.
    eauto using base_val_unflatten_typed, pbits_tag_valid.
  * typed_constructor; auto using fmap_length. by apply Forall_fmap.
  * typed_constructor; eauto. by apply Forall2_fmap_l.
  * typed_constructor; eauto.
  * eauto using val_unflatten_typed, TCompound_valid, pbits_tag_valid.
Qed.
Lemma to_vals_typed Γ Δ ws τs :
  ✓ Γ → (Γ,Δ) ⊢* ws :* τs → (Γ,Δ) ⊢* to_val Γ <$> ws :* τs.
Proof. induction 2; csimpl; auto using to_val_typed. Qed.
Lemma to_val_type_of Γ w :
  ✓ Γ → ✓{Γ} (type_of w) → type_of (to_val Γ w) = type_of w.
Proof.
  intros HΓ. induction w as [|τ ws IH| | |] using @ctree_ind_alt; simpl; auto.
  * by rewrite base_val_unflatten_type_of.
  * intros. by rewrite val_unflatten_type_of.
Qed.
Lemma to_val_weaken Γ1 Γ2 Δ w τ :
  ✓ Γ1 → (Γ1,Δ) ⊢ w : τ → Γ1 ⊆ Γ2 → to_val Γ1 w = to_val Γ2 w.
Proof.
  intros ? Hw ?. revert w τ Hw. refine (ctree_typed_ind _ _ _ _ _ _ _ _).
  * intros; f_equal'; auto using base_val_unflatten_weaken.
  * intros; f_equal'; auto using Forall_fmap_ext_1.
  * intros t wγbss τs _ _ IH _ _ _; f_equal'. induction IH; f_equal'; auto.
  * by intros; f_equal'.
  * eauto using val_unflatten_weaken, TCompound_valid.
Qed.
Lemma to_val_frozen Γ Δ w τ : ✓ Γ → (Γ,Δ) ⊢ w : τ → frozen (to_val Γ w).
Proof.
  unfold frozen; induction 2 using @ctree_typed_ind; simpl.
  * by erewrite base_val_unflatten_frozen by eauto using pbits_tag_valid.
  * f_equal. rewrite <-list_fmap_compose. by apply Forall_fmap_ext.
  * f_equal. rewrite <-list_fmap_compose.
    eapply Forall_fmap_ext, Forall2_Forall_l; eauto. eapply Forall_true; eauto.
  * by f_equal.
  * eauto using val_unflatten_frozen, TCompound_valid, pbits_tag_valid.
Qed.
Lemma to_val_union_free_inv Γ w : val_union_free (to_val Γ w) → union_free w.
Proof.
  induction w as [|ws IH|s wγbss IH| | ] using @ctree_ind_alt;
    simpl; inversion_clear 1; econstructor; eauto.
  * induction IH; decompose_Forall_hyps; auto.
  * induction IH; decompose_Forall_hyps; auto.
Qed.
Lemma to_val_unflatten Γ τ γbs :
  ✓ Γ → ✓{Γ} τ → to_val Γ (ctree_unflatten Γ τ γbs)
  = val_unflatten Γ τ (tagged_tag <$> γbs).
Proof.
  intros HΓ Hτ. revert τ Hτ γbs. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb _ γbs. by rewrite ctree_unflatten_base, val_unflatten_base.
  * intros τ n _ IH _ γbs.
    rewrite ctree_unflatten_array, val_unflatten_array; f_equal'. revert γbs.
    induction n; intros; f_equal'; rewrite <-?fmap_drop, <-?fmap_take; auto.
  * intros [] t τs Ht _ IH _ γbs; erewrite ctree_unflatten_compound,
      val_unflatten_compound by eauto; f_equal'.
    { unfold struct_unflatten. clear Ht. revert γbs.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
        rewrite <-?fmap_drop, <-?fmap_take; f_equal'; auto. }
    by erewrite val_unflatten_compound by eauto.
Qed.
Lemma to_val_ctree_map Γ f w :
  (∀ γb, tagged_tag (f γb) = tagged_tag γb) →
  to_val Γ (ctree_map f w) = to_val Γ w.
Proof.
  intros ?. induction w using @ctree_ind_alt; f_equal'; auto.
  * f_equal. rewrite <-list_fmap_compose. by apply list_fmap_ext.
  * rewrite <-list_fmap_compose. by apply Forall_fmap_ext.
  * rewrite <-list_fmap_compose. by apply Forall_fmap_ext.
  * rewrite <-list_fmap_compose. by apply list_fmap_ext.
Qed.
Lemma to_val_unmapped Γ Δ w τ :
  ✓ Γ → (Γ,Δ) ⊢ w : τ → ctree_unmapped w → to_val Γ w = val_new Γ τ.
Proof.
  intros HΓ; revert w τ; refine (ctree_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros τb γbs ????; rewrite val_new_base, pbits_unmapped_tag by done.
    by case_decide; subst; rewrite ?base_val_unflatten_indet by auto.
  * intros ws τ _ IH _ ?; rewrite val_new_array; f_equal.
    induction IH; decompose_Forall_hyps; f_equal'; auto.
  * intros t wγbss τs Hs _ IH _ _ _ ?.
    erewrite val_new_compound by eauto; f_equal; clear Hs.
    induction IH; decompose_Forall_hyps; f_equal'; auto.
  * intros t i τs w γbs τ ?????????; decompose_Forall_hyps; tauto.
  * intros t τs γbs ????; unfold val_new.
    rewrite pbits_unmapped_tag by done; congruence.
Qed.
  
(** ** Properties of the [of_val] function *)
Lemma ctree_flatten_of_val Γ Δ γs v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length γs = bit_size_of Γ τ →
  ctree_flatten (of_val Γ γs v) = zip_with PBit γs (val_flatten Γ v).
Proof.
  intros HΓ Hv. revert v τ Hv γs. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * done.
  * intros vs τ Hvs IH _ γs; rewrite bit_size_of_array; revert γs.
    induction IH; intros γs Hγs; decompose_Forall_hyps;
      erewrite ?zip_with_nil_r, ?type_of_correct,
      ?zip_with_app_r, ?val_flatten_length by eauto; f_equal; auto.
  * intros t vs τs Ht Hvs IH γs.
    erewrite Ht, bit_size_of_struct, fmap_type_of by eauto; simpl.
    unfold field_bit_padding. clear Ht. revert vs Hvs IH γs.
    induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
      erewrite ?zip_with_nil_r, ?type_of_correct, ?resize_ge,
      <-?(assoc_L (++)), ?zip_with_app_r, ?val_flatten_length,
      ?replicate_length, ?zip_with_replicate_r by eauto; repeat f_equal; auto.
  * intros t i τs v τ ??? IH γs ?. erewrite type_of_correct, resize_ge,
      zip_with_app_r, val_flatten_length, zip_with_replicate_r by eauto.
    f_equal; auto.
  * done.
Qed.
Lemma ctree_flatten_of_val' Γ Δ γs v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length γs = bit_size_of Γ τ →
  tagged_tag <$> ctree_flatten (of_val Γ γs v) = val_flatten Γ v.
Proof. intros. by erewrite ctree_flatten_of_val, fmap_zip_with_r by eauto. Qed.
Lemma of_val_unshared Γ Δ γs v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length γs = bit_size_of Γ τ → Forall sep_unshared γs →
  Forall (not ∘ sep_unmapped) γs → ctree_unshared (of_val Γ γs v).
Proof.
  intros. erewrite ctree_flatten_of_val by eauto; eauto using PBits_unshared.
Qed.
Lemma of_val_mapped Γ Δ γs v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length γs = bit_size_of Γ τ →
  Forall (not ∘ sep_unmapped) γs →
  ctree_Forall (not ∘ sep_unmapped) (of_val Γ γs v).
Proof.
  intros. erewrite ctree_flatten_of_val by eauto. eauto using PBits_mapped.
Qed.
Lemma of_val_typed Γ Δ γs v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length γs = bit_size_of Γ τ → Forall sep_valid γs →
  Forall (not ∘ sep_unmapped) γs → (Γ,Δ) ⊢ of_val Γ γs v : τ.
Proof.
  intros HΓ Hv. revert v τ Hv γs. refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros vb τb ? γs ???. erewrite type_of_correct by eauto.
    typed_constructor.
    + eauto using base_val_typed_type_valid.
    + eauto using PBits_valid, base_val_flatten_valid.
    + erewrite zip_with_length, base_val_flatten_length by eauto; lia.
  * intros vs τ Hvs IH Hvs' γs. rewrite bit_size_of_array; intros Hlen  Hγs Hγs'.
    typed_constructor; trivial.
    + clear Hvs Hvs' Hγs Hγs' Hlen IH. revert γs.
      induction vs; intros; f_equal'; auto.
    + revert γs Hγs Hγs' Hlen. clear Hvs'. induction IH; intros;
        decompose_Forall_hyps; erewrite ?type_of_correct by eauto;
        constructor; auto.
  * intros t vs τs Ht Hvs IH γs.
    erewrite bit_size_of_struct, fmap_type_of by eauto; intros Hlen Hγs Hγs'.
    typed_constructor; eauto; clear Ht; unfold field_bit_padding.
    + revert vs γs Hvs IH Hγs Hγs' Hlen.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
        erewrite ?type_of_correct by eauto; constructor; simpl; auto.
    + clear IH. revert vs γs Hvs Hγs Hγs' Hlen.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
        erewrite ?type_of_correct by eauto; constructor; simpl; auto.
      erewrite <-zip_with_replicate_r by eauto; eauto 7 using PBits_valid.
    + clear Hγs Hγs' Hlen IH. revert γs vs Hvs.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
        constructor; simpl; eauto using PBits_indetify.
    + clear Hγs Hγs' IH. revert vs γs Hvs Hlen.
      induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
        erewrite ?type_of_correct by eauto; f_equal; auto.
  * intros. erewrite type_of_correct by eauto. typed_constructor; eauto.
    + erewrite <-zip_with_replicate_l, zip_with_flip by eauto.
      auto using PBits_valid.
    + auto using PBits_indetify.
    + rewrite fmap_length; solve_length.
    + intros [Hc _]. eapply (ctree_Forall_not sep_unmapped Γ Δ
        (of_val Γ (take (bit_size_of Γ τ) γs) v)); eauto using of_val_mapped.
  * intros t vs τs Ht Hvs IH Hrep γs ???.
    destruct (bits_list_join _ _) as [bs'|] eqn:Hbs'; simpl.
    { typed_constructor; eauto.
      + eauto using PBits_valid, val_union_to_bits_valid.
      + erewrite zip_with_length, bits_list_join_length by eauto; auto; lia. }
    typed_constructor; eauto using PBits_valid.
Qed.
Lemma of_val_weaken Γ1 Γ2 Δ1 γs v τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ1) ⊢ v : τ → of_val Γ1 γs v = of_val Γ2 γs v.
Proof.
  intros HΓ ? Hv. revert v τ Hv γs. refine (val_typed_ind _ _ _ _ _ _ _ _).
  * intros; f_equal'; eauto using base_val_flatten_weaken with f_equal.
  * intros vs τ ? IH _ γs; f_equal'; revert γs.
    induction IH; intros; decompose_Forall_hyps; simplify_type_equality;
      erewrite ?(bit_size_of_weaken Γ1 Γ2) by eauto using val_typed_type_valid;
      auto with f_equal.
  * intros t vs τs Ht Hvs IH γs; f_equal'; revert γs.
    erewrite fmap_type_of, field_bit_padding_weaken by eauto; clear Ht.
    generalize (field_bit_padding Γ2 τs).
    induction IH; intros [|??] ?; decompose_Forall_hyps; simplify_type_equality;
      erewrite ?bit_size_of_weaken by eauto using val_typed_type_valid;
      auto with f_equal.
  * intros; simplify_type_equality'.
    erewrite bit_size_of_weaken by eauto using val_typed_type_valid.
    auto with f_equal.
  * intros; unfold of_val; do 2 f_equal; eapply val_flatten_weaken; eauto.
    econstructor; eauto.
Qed.
Lemma of_val_type_of Γ γs v : type_of (of_val Γ γs v) = type_of v.
Proof.
  destruct v as [|? vs _| | |] using val_ind_alt;
    simplify_equality'; rewrite ?fmap_length; f_equal; auto.
  revert γs; induction vs; intros; f_equal'; auto.
Qed.
Lemma to_of_val Γ Δ γs v τ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → length γs = bit_size_of Γ τ →
  to_val Γ (of_val Γ γs v) = freeze true v.
Proof.
  intros HΓ Hvτ. revert v τ Hvτ γs.
  refine (val_typed_ind _ _ _ _ _ _ _ _); simpl.
  * intros. by erewrite type_of_correct, fmap_zip_with_r,
      base_val_unflatten_flatten by eauto.
  * intros vs τ Hvs IH _ γs; rewrite bit_size_of_array; intros Hγs; f_equal.
    revert γs Hγs. induction IH; intros; decompose_Forall_hyps;
      erewrite ?type_of_correct by eauto; f_equal; auto.
  * intros t vs τs Ht Hvs IH γs; erewrite fmap_type_of,
      bit_size_of_struct by eauto; intros Hγs; f_equal.
    revert vs γs Hvs IH Hγs. unfold field_bit_padding. clear Ht.
    induction (bit_size_of_fields _ τs HΓ); intros; decompose_Forall_hyps;
      erewrite ?type_of_correct by eauto; f_equal; eauto.
  * intros; erewrite type_of_correct by eauto; f_equal; auto.
  * intros t vs τs Ht Hvs IH Hrepr γs ?.
    destruct (vals_representable_as_bits Γ Δ (bit_size_of Γ (unionT t)) vs τs)
     as (bs&->&?&?&Hbs); simpl; eauto using bit_size_of_union.
    by erewrite fmap_zip_with_r,
      val_unflatten_compound, Hbs, vals_unflatten_frozen by eauto.
Qed.
Lemma of_val_union_free Γ γs v :
  val_union_free v → union_free (of_val Γ γs v).
Proof.
  intros Hv. revert γs. induction Hv as [|? vs _ IH|s vs _ IH|]
    using @val_union_free_ind_alt; intros γs; simpl; econstructor; eauto.
  * revert γs. induction IH; simpl; constructor; auto.
  * generalize (field_bit_padding Γ (type_of <$> vs)). revert γs.
    induction IH; intros ? [|??]; constructor; simpl; auto.
Qed.
Lemma to_val_new Γ γ τ :
  ✓ Γ → ✓{Γ} τ → to_val Γ (ctree_new Γ (PBit γ BIndet) τ) = val_new Γ τ.
Proof.
  intros. unfold ctree_new. by rewrite to_val_unflatten, fmap_replicate.
Qed.
Lemma of_val_new Γ τ γ :
  ✓ Γ → ✓{Γ} τ →
  of_val Γ (replicate (bit_size_of Γ τ) γ) (val_new Γ τ)
  = ctree_new Γ (PBit γ BIndet) τ.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros. rewrite ctree_new_base, val_new_base.
    by case_decide; simplify_equality'; rewrite zip_with_replicate.
  * intros τ n ? IH _.
    rewrite bit_size_of_array, val_new_array, ctree_new_array; f_equal'.
    induction n; simpl; rewrite ?val_new_type_of, ?take_replicate,
      ?Min.min_l, ?drop_replicate_plus by (auto with lia); f_equal; auto.
  * intros [] t τs Ht Hτs IH _; erewrite val_new_compound,
      ctree_new_compound, ?bit_size_of_struct by eauto; f_equal'.
    { clear Ht. erewrite fmap_type_of by eauto using (vals_new_typed _ ∅).
      unfold field_bit_padding.
      induction (bit_size_of_fields _ τs HΓ) as [|τ sz τs szs ?? IH'];
        decompose_Forall_hyps; auto.
      rewrite val_new_type_of, !drop_replicate, !take_replicate, !Min.min_l,
        fmap_replicate, <-IH' by auto with lia; repeat f_equal; auto with lia. }
    destruct (bits_list_join_exists (bit_size_of Γ (unionT t))
      (val_flatten Γ <$> (val_new Γ <$> τs))
      (replicate (bit_size_of Γ (unionT t)) BIndet)) as (bs'&->&?); auto.
    { apply Forall_fmap, Forall_fmap; apply (Forall_impl ✓{Γ}); auto.
      intros τ ?; simpl. unfold val_new.
      by rewrite (val_flatten_unflatten _ ∅), resize_replicate by eauto. }
    erewrite (bits_subseteq_indets bs') by eauto using Forall_replicate_eq.
    apply zip_with_replicate.
Qed.
Lemma ctree_map_of_val Γ f g γs v :
  (∀ γ b, f (PBit γ b) = PBit (g γ) b) →
  ctree_map f (of_val Γ γs v) = of_val Γ (g <$> γs) v.
Proof.
  intros ?. revert γs. assert (∀ γs bs,
    f <$> zip_with PBit γs bs = zip_with PBit (g <$> γs) bs).
  { induction γs; intros [|??]; f_equal'; auto. }
  assert (∀ γs, f <$> (flip PBit BIndet <$> γs) = flip PBit BIndet <$> (g <$> γs)).
  { intros. rewrite <-!list_fmap_compose. apply list_fmap_ext; simpl; auto. }
  induction v as [|τ vs IH|s vs IH| |] using @val_ind_alt; simpl;
    intros γs; rewrite <-?fmap_drop, <-?fmap_take; f_equal'; revert γs; auto.
  * induction IH; intros; f_equal'; rewrite <-?fmap_take, <-?fmap_drop; auto.
  * generalize (field_bit_padding Γ (type_of <$> vs)).
    induction IH; intros [|??] ?; f_equal';
      rewrite <-?fmap_drop, <-?fmap_take; auto with f_equal.
Qed.

(** ** Decidable typing *)
Local Arguments type_check _ _ _ _ _ !_ /.
#[global] Instance:
  TypeCheckSpec (env K * memenv K) (type K) (val K) (✓ ∘ fst).
Proof.
  intros [Γ Δ] v τ ?; revert v τ. assert (∀ vs τs,
    Forall (λ v, ∀ τ, type_check (Γ,Δ) v = Some τ → (Γ,Δ) ⊢ v : τ) vs →
    mapM (type_check (Γ,Δ)) vs = Some τs → (Γ,Δ) ⊢* vs :* τs).
  { intros vs τs. rewrite mapM_Some. intros. decompose_Forall; eauto. }
  assert (∀ vs τ,
    (Γ,Δ) ⊢* vs : τ → Forall (λ v, type_check (Γ,Δ) v = Some τ) vs →
    mapM (type_check (Γ,Δ)) vs = Some (replicate (length vs) τ)).
  { intros. apply mapM_Some, Forall2_replicate_r;decompose_Forall_hyps; eauto. }
  intros v τ; split.
  * revert τ. induction v using @val_ind_alt; intros; simplify_option_eq.
    + typed_constructor; auto. by apply type_check_sound.
    + typed_constructor; eauto using @Forall2_Forall_typed.
    + typed_constructor; decompose_Forall_hyps; eauto.
    + typed_constructor; eauto.
    + typed_constructor; eauto. apply vals_unflatten_representable.
      - eapply bits_list_join_valid, Forall_fmap,
          Forall2_Forall_l, Forall_true; eauto using val_flatten_valid.
      - erewrite bits_list_join_length by eauto. eauto using bit_size_of_union.
  * induction 1 using @val_typed_ind; simplify_option_eq.
    + by erewrite type_check_complete by eauto.
    + done.
    + erewrite mapM_Some_2; eauto. by simplify_option_eq.
    + done.
    + erewrite mapM_Some_2; eauto; simplify_option_eq.
      by match goal with
      | _ : Γ !! ?s = Some _, H : vals_representable ?Γ ?m ?vs ?τs |- _ =>
        destruct (vals_representable_as_bits Γ Δ
          (bit_size_of Γ (unionT t)) vs τs) as (?&?&?&?&->);
          eauto using val_typed_types_valid, bit_size_of_union
      end; simplify_option_eq.
Qed.

(** ** Properties of lookup *)
Lemma val_lookup_nil Γ : lookupE (A:=val K) Γ [] = Some.
Proof. done. Qed.
Lemma val_lookup_cons Γ rs r :
  lookupE Γ (rs :: r) = λ v, v !!{Γ} r ≫= lookupE Γ rs.
Proof. done. Qed.
Lemma val_lookup_app Γ v r1 r2: v !!{Γ} (r1 ++ r2) = v !!{Γ} r2 ≫= lookupE Γ r1.
Proof.
  induction r1 as [|rs1 r1 IH]; simpl.
  * by destruct (v !!{Γ} r2).
  * by rewrite !val_lookup_cons, IH, option_bind_assoc.
Qed.
Lemma val_lookup_snoc Γ v r rs: v !!{Γ} (r ++ [rs]) = v !!{Γ} rs ≫= lookupE Γ r.
Proof. apply val_lookup_app. Qed.
Lemma val_lookup_seg_Some Γ Δ v τ rs v' :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → v !!{Γ} rs = Some v' →
  ∃ σ, Γ ⊢ rs : τ ↣ σ ∧ (Γ,Δ) ⊢ v' : σ.
Proof.
  intros ?. destruct 1 as [|vs τ n _|s vs τs ? Hvs _|s j τs v τ
    |s vs τs ?? _ [bs ?? ->]] using @val_typed_ind;
    destruct rs as [i|i|i]; intros Hlookup; simplify_option_eq.
  * exists τ. split.
    + constructor; eauto using lookup_lt_Some.
    + eapply (Forall_lookup (λ v, (Γ,Δ) ⊢ v : τ)); eauto.
  * destruct (Forall2_lookup_l _ _ _ i v' Hvs) as (σ&?&?); eauto.
    exists σ; split; [|done]. typed_constructor; eauto.
  * exists τ; split; [|done]. typed_constructor; eauto.
  * eexists; split; eauto using val_unflatten_typed, val_flatten_valid.
    econstructor; eauto.
  * apply list_lookup_fmap_inv in Hlookup; destruct Hlookup as (τ&->&?).
    decompose_Forall_hyps. exists τ; split; [econstructor; eauto|].
    eauto using val_unflatten_typed.
Qed.
Lemma val_lookup_Some Γ Δ v τ r v' :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → v !!{Γ} r = Some v' →
  ∃ σ, Γ ⊢ r : τ ↣ σ ∧ (Γ,Δ) ⊢ v' : σ.
Proof.
  intros ?. revert v τ.
  induction r as [|rs r IH] using rev_ind; intros v τ Hvτ Hr.
  { simplify_type_equality. exists τ; split; [econstructor |]; eauto. }
  rewrite val_lookup_snoc in Hr.
  destruct (v !!{Γ} rs) as [v''|] eqn:Hv''; simplify_equality'.
  destruct (val_lookup_seg_Some Γ Δ v τ rs v'') as (σ''&?&?); auto.
  destruct (IH v'' σ'') as (σ&?&?); auto.
  exists σ; split; [eapply ref_typed_snoc|]; eauto.
Qed.
Lemma val_lookup_seg_typed Γ Δ v τ rs v' σ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → v !!{Γ} rs = Some v' →
  Γ ⊢ rs : τ ↣ σ → (Γ,Δ) ⊢ v' : σ.
Proof.
  intros. by destruct (val_lookup_seg_Some Γ Δ v τ rs v')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma val_lookup_typed Γ Δ v τ r v' σ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → v !!{Γ} r = Some v' → Γ ⊢ r : τ ↣ σ → (Γ,Δ) ⊢ v' : σ.
Proof.
  intros. by destruct (val_lookup_Some Γ Δ v τ r v')
    as (σ'&Hrσ'&?); simplify_type_equality.
Qed.
Lemma val_lookup_seg_weaken Γ1 Γ2 Δ1 rs v τ v' :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ1) ⊢ v : τ →
  v !!{Γ1} rs = Some v' → v !!{Γ2} rs = Some v'.
Proof.
  intros ?? Hv Hrs. destruct Hv, rs; simplify_option_eq; auto.
  erewrite lookup_compound_weaken by eauto; simplify_option_eq.
  by erewrite <-bit_size_of_weaken, <-val_flatten_weaken,
    <-val_unflatten_weaken by eauto.
Qed.
Lemma val_lookup_weaken Γ1 Γ2 Δ1 r v τ v' :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ1) ⊢ v : τ →
  v !!{Γ1} r = Some v' → v !!{Γ2} r = Some v'.
Proof.
  intros ??. revert v'. induction r as [|rs r IH]; intros v3; [done|].
  rewrite !val_lookup_cons, bind_Some; intros ? (v2&?&?).
  destruct (val_lookup_Some Γ1 Δ1 v τ r v2) as (τ2&?&?); auto.
  erewrite IH by eauto; simpl; eauto using val_lookup_seg_weaken.
Qed.
Lemma val_lookup_weaken_is_Some Γ1 Γ2 Δ1 r v τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ1) ⊢ v : τ →
  is_Some (v !!{Γ1} r) → is_Some (v !!{Γ2} r).
Proof. intros ??? [??]; eauto using val_lookup_weaken. Qed.
Lemma to_val_lookup_seg Γ w rs w' :
  ✓ Γ → w !!{Γ} rs = Some w' → frozen rs →
  to_val Γ w !!{Γ} rs = Some (to_val Γ w').
Proof.
  intros ? Hr. destruct w; destruct rs; pattern w';
    apply (ctree_lookup_seg_inv _ _ _ _ _ Hr); intros; simplify_option_eq.
  * rewrite list_lookup_fmap. by simplify_option_eq.
  * rewrite list_lookup_fmap. by simplify_option_eq.
  * done.
  * erewrite val_unflatten_compound, to_val_unflatten by eauto.
    by simplify_option_eq;
      rewrite list_lookup_fmap, fmap_take; simplify_option_eq.
Qed.
Lemma to_val_lookup Γ w r w' :
  ✓ Γ → w !!{Γ} r = Some w' → freeze true <$> r = r →
  to_val Γ w !!{Γ} r = Some (to_val Γ w').
Proof.
  intros ?. revert w. induction r using rev_ind; intros w.
  { by rewrite ctree_lookup_nil; intros; simplify_equality. }
  rewrite ctree_lookup_snoc, fmap_app; intros;
    simplify_option_eq; simplify_list_eq.
  erewrite val_lookup_snoc, to_val_lookup_seg by eauto; eauto.
Qed.

(** ** Properties of alter *)
Implicit Types g : val K → val K.
Lemma val_alter_nil Γ g : val_alter Γ g [] = g.
Proof. done. Qed.
Lemma val_alter_cons Γ g rs r :
  val_alter Γ g (rs :: r) = val_alter Γ (val_alter_seg Γ g rs) r.
Proof. done. Qed.
Lemma val_alter_singleton Γ g rs : val_alter Γ g [rs] = val_alter_seg Γ g rs.
Proof. done. Qed.
Lemma val_alter_app Γ g v r1 r2 :
  val_alter Γ g (r1 ++ r2) v = val_alter Γ (val_alter Γ g r1) r2 v.
Proof.
  revert g. induction r1; simpl; intros; rewrite ?val_alter_cons; auto.
Qed.
Lemma val_alter_snoc Γ g v r rs :
  val_alter Γ g (r ++ [rs]) v = val_alter_seg Γ (val_alter Γ g r) rs v.
Proof. apply val_alter_app. Qed.
Lemma val_alter_seg_freeze Γ β g rs :
  val_alter_seg Γ g (freeze β rs) = val_alter_seg Γ g rs.
Proof. by destruct rs. Qed.
Lemma val_alter_freeze Γ β g r :
  val_alter Γ g (freeze β <$> r) = val_alter Γ g r.
Proof.
  revert g. induction r as [|rs r IH]; intros g; simpl; [done |].
  by rewrite IH, val_alter_seg_freeze.
Qed.
Lemma val_alter_seg_ext Γ g1 g2 v rs :
  (∀ v', g1 v' = g2 v') → val_alter_seg Γ g1 rs v = val_alter_seg Γ g2 rs v.
Proof.
  intros. destruct rs, v; simpl; unfold default; simplify_option_eq;
    repeat case_match; f_equal; auto using list_fmap_ext, list_alter_ext.
Qed.
Lemma val_alter_ext Γ g1 g2 v r :
  (∀ v', g1 v' = g2 v') → val_alter Γ g1 r v = val_alter Γ g2 r v.
Proof.
  intros. revert v. induction r as [|rs r IH] using rev_ind; intros v; [done|].
  rewrite !val_alter_snoc. by apply val_alter_seg_ext.
Qed.
Lemma val_alter_seg_ext_typed Γ Δ g1 g2 v τ rs :
  ✓ Γ → (∀ v' τ', (Γ,Δ) ⊢ v' : τ' → g1 v' = g2 v') → (Γ,Δ) ⊢ v : τ →
  val_alter_seg Γ g1 rs v = val_alter_seg Γ g2 rs v.
Proof.
  intros ? Hg. destruct rs, 1; simpl;
    unfold default; simplify_option_eq; f_equal; auto.
  * apply list_alter_ext; intros; decompose_Forall. eapply Hg; eauto. done.
  * apply list_alter_ext; intros; decompose_Forall. eapply Hg; eauto. done.
  * f_equal; eauto.
  * repeat case_match; f_equal; eauto using val_new_typed.
    eapply Hg; eauto using val_unflatten_typed, val_flatten_valid.
  * repeat case_match; decompose_Forall; f_equal. eapply Hg; eauto.
Qed.
Lemma val_alter_ext_typed Γ Δ g1 g2 v τ r :
  ✓ Γ → (∀ v' τ', (Γ,Δ) ⊢ v' : τ' → g1 v' = g2 v') → (Γ,Δ) ⊢ v : τ →
  val_alter Γ g1 r v = val_alter Γ g2 r v.
Proof.
  intros ?. revert g1 g2 v τ.
  induction r as [|rs r IH]; intros g1 g2 v τ ??; eauto.
  rewrite !val_alter_cons; eauto using val_alter_seg_ext_typed.
Qed.
Lemma val_alter_seg_compose Γ g1 g2 v rs :
  val_alter_seg Γ (g1 ∘ g2) rs v
  = val_alter_seg Γ g1 rs (val_alter_seg Γ g2 rs v).
Proof.
  destruct v, rs; simpl; unfold default;
    repeat (simplify_option_eq || case_match);
    f_equal; auto using list_alter_compose.
Qed.
Lemma val_alter_compose Γ g1 g2 v r :
  val_alter Γ (g1 ∘ g2) r v = val_alter Γ g1 r (val_alter Γ g2 r v).
Proof.
  intros. revert v. induction r as [|rs r IH] using rev_ind; intros w; [done|].
  rewrite !val_alter_snoc, <-val_alter_seg_compose. by apply val_alter_seg_ext.
Qed.
Lemma val_alter_seg_commute Γ g1 g2 v rs1 rs2 :
  rs1 ## rs2 → val_alter_seg Γ g1 rs1 (val_alter_seg Γ g2 rs2 v)
  = val_alter_seg Γ g2 rs2 (val_alter_seg Γ g1 rs1 v).
Proof.
  destruct 1, v; intros; simplify_option_eq;
    f_equal; auto using list_alter_commute.
Qed.
Lemma val_alter_commute Γ g1 g2 v r1 r2 :
  r1 ## r2 → val_alter Γ g1 r1 (val_alter Γ g2 r2 v)
  = val_alter Γ g2 r2 (val_alter Γ g1 r1 v).
Proof.
  rewrite ref_disjoint_alt. intros (r1'&rs1'&r1''&r2'&rs2'&r2''&->&->&?&Hr).
  rewrite !val_alter_app, !val_alter_singleton.
  rewrite <-!(val_alter_freeze _ true _ r1''), !Hr, !val_alter_freeze.
  rewrite <-!val_alter_compose. apply val_alter_ext; intros w'; simpl; auto.
  by apply val_alter_seg_commute.
Qed.
Lemma val_alter_seg_weaken Γ1 Γ2 Δ g rs v τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ) ⊢ v : τ →
  val_alter_seg Γ1 g rs v = val_alter_seg Γ2 g rs v.
Proof.
  destruct rs as [| |j], 3; simplify_option_eq; auto.
  erewrite lookup_compound_weaken by eauto; simpl.
  destruct (_ !! j) eqn:?; f_equal'.
  by erewrite !(bit_size_of_weaken Γ1 Γ2), val_unflatten_weaken,
    val_flatten_weaken by eauto using TCompound_valid.
Qed.
Lemma val_alter_weaken Γ1 Γ2 Δ g r v τ :
  ✓ Γ1 → Γ1 ⊆ Γ2 → (Γ1,Δ) ⊢ v : τ → val_alter Γ1 g r v = val_alter Γ2 g r v.
Proof.
  intros ??. revert g v τ. induction r as [|rs r IH]; intros g v τ ?; [done|].
  erewrite !val_alter_cons, <-IH by eauto.
  eapply val_alter_ext_typed; eauto using val_alter_seg_weaken.
Qed.
Lemma val_alter_seg_typed Γ Δ g v rs τ v' :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → v !!{Γ} rs = Some v' →
  (Γ,Δ) ⊢ g v' : type_of v' → (Γ,Δ) ⊢ val_alter_seg Γ g rs v : τ.
Proof.
  intros HΓ Hv Hrs.
  destruct rs, Hv; change (val_typed' Γ Δ) with (typed (Γ,Δ)) in *; intros;
    simplify_option_eq; decompose_Forall_hyps; simplify_type_equality;
    typed_constructor; eauto using alter_length.
  * apply Forall_alter; naive_solver.
  * apply Forall2_alter_l; naive_solver.
  * rewrite resize_resize by eauto using bit_size_of_union_lookup.
    erewrite <-val_unflatten_type_of by eauto; eauto.
Qed.
Lemma val_alter_typed Γ Δ g v r τ v' :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → v !!{Γ} r = Some v' →
  (Γ,Δ) ⊢ g v' : type_of v' → (Γ,Δ) ⊢ val_alter Γ g r v : τ.
Proof.
  intros HΓ. revert g τ v. induction r as [|rs r IH] using @rev_ind.
  { by intros; simplify_type_equality'. }
  intros g τ v; rewrite val_alter_snoc, val_lookup_snoc; intros.
  destruct (v !!{Γ} rs) as [v''|] eqn:?; simplify_equality'.
  destruct (val_lookup_seg_Some Γ Δ v τ rs v'') as (?&_&?); eauto.
  eapply val_alter_seg_typed; eauto using val_lookup_seg_typed, type_of_typed.
Qed.
Lemma val_alter_const_typed Γ Δ v r τ v' σ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → Γ ⊢ r : τ ↣ σ → is_Some (v !!{Γ} r) →
  (Γ,Δ) ⊢ v' : σ → (Γ,Δ) ⊢ val_alter Γ (λ _, v') r v : τ.
Proof.
  intros ??? [v'' ?] ?; eapply val_alter_typed; eauto.
  by erewrite type_of_correct by eauto using val_lookup_typed. 
Qed.
End values.
