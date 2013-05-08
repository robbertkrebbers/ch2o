(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export pointers bytes.

Inductive base_val (Ti Vi : Set) :=
  | VUndef : base_type Ti → base_val Ti Vi
  | VInt : Vi → base_val Ti Vi
  | VPtr : ptr Ti → base_val Ti Vi
  | VPtrSeg : ptr_seg Ti → base_val Ti Vi.
Arguments VUndef {_ _} _.
Arguments VInt {_ _} _.
Arguments VPtr {_ _} _.
Arguments VPtrSeg {_ _} _.

Instance base_val_eq_dec {Ti Vi : Set}
  `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)} `{∀ x1 x2 : Vi, Decision (x1 = x2)}
  (v1 v2 : base_val Ti Vi) : Decision (v1 = v2).
Proof. solve_decision. Defined.

Inductive base_typed' `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M}
    (m : M) : base_val Ti Vi → base_type Ti → Prop :=
  | VUndef_typed τ : base_type_valid get_env τ → base_typed' m (VUndef τ) τ
  | VInt_typed x τ : τ = type_of_int x → base_typed' m (VInt x) (TInt τ)
  | VPtr_typed p τ : m ⊢ p : τ → base_typed' m (VPtr p) (TPtr τ)
  | VPtrSeg_typed ps :
     ptr_seg_valid m ps → base_typed' m (VPtrSeg ps) (TInt TuChar).
Instance base_typed `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M} :
  Typed M (base_type Ti) (base_val Ti Vi) := base_typed'.

Instance type_of_base_val `{IntEnv Ti Vi} :
    TypeOf (base_type Ti) (base_val Ti Vi) := λ v,
  match v with
  | VUndef τ => τ
  | VInt x => TInt (type_of_int x)
  | VPtr p => TPtr (type_of p)
  | VPtrSeg _ => TInt TuChar
  end.

Inductive base_val_le' `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M}
    (m : M) : relation (base_val Ti Vi) :=
  | VUndef_le τ v : m ⊢ v : τ → base_val_le' m (VUndef τ) v
  | VBase_le_refl v : base_val_le' m v v.
Instance base_val_le `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M} :
  SubsetEqEnv M (base_val Ti Vi) := base_val_le'.

Inductive base_val_frozen {Ti Vi} : Frozen (base_val Ti Vi) :=
  | VUndef_frozen τ : frozen (@VUndef Ti Vi τ)
  | VInt_frozen x : frozen (@VInt Ti Vi x)
  | VPtr_frozen p : frozen p → frozen (@VPtr Ti Vi p)
  | VPtrSeg_frozen ps : frozen (@VPtrSeg Ti Vi ps).
Existing Instance base_val_frozen.
Instance base_val_freeze {Ti Vi} : Freeze (base_val Ti Vi) := λ v,
  match v with
  | VUndef τ => VUndef τ
  | VInt x => VInt x
  | VPtr p => VPtr (freeze p)
  | VPtrSeg ps => VPtrSeg ps
  end.

Definition base_val_to_bytes `{Ienv: IntEnv Ti Vi} `{PtrEnv Ti}
    (v : base_val Ti Vi) : listset (list (byte Ti Vi)) :=
  match v with
  | VUndef τ => {[ @base_undef_bytes _ _ Ienv _ τ ]}
  | VInt x => fmap BChar <$> encode_int x
  | VPtr p => {[ BPtrSeg <$> to_ptr_segs p ]}
  | VPtrSeg ps => {[ [BPtrSeg ps] ]}
  end.

Definition base_val_of_bytes `{IntEnv Ti Vi} `{PtrEnv Ti}
    (τ : base_type Ti) (bs : list (byte Ti Vi)) : base_val Ti Vi :=
  match τ with
  | TInt τi =>
     match bs with
     | [BPtrSeg ps] =>
        if decide_rel (=) τi TuChar then VPtrSeg ps else VUndef τ
     | _ =>
        match mapM maybe_BChar bs ≫= decode_int τi
        with Some vi => VInt vi | None => VUndef τ end
     end
  | TPtr τp =>
     match mapM maybe_BPtrSeg bs ≫= of_ptr_segs τp
     with Some p => VPtr p | None => VUndef τ end
  end.

Definition base_val_0 `{IntEnv Ti Vi} (τ : base_type Ti) : base_val Ti Vi :=
  match τ with
  | TInt τ => VInt (int_of_Z τ 0)
  | TPtr τ => VPtr (NULL τ)
  end.

Section base_value.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.
  Implicit Types v : base_val Ti Vi.
  Implicit Types m : M.
  Implicit Types τ : base_type Ti.
  Implicit Types bs : list (byte Ti Vi).

  Context `{PropHolds (∀ m i (τ : type Ti),
    type_of_index m i = Some τ → τ = TVoid ∨ type_valid get_env τ)}.

  Lemma base_typed_type_valid m v τ : m ⊢ v : τ → base_type_valid get_env τ.
  Proof. destruct 1; try econstructor; eauto using ptr_typed_type_valid. Qed.

  Global Instance: TypeOfSpec M (base_type Ti) (base_val Ti Vi).
  Proof. destruct 1; simpl; f_equal; eauto using type_of_correct. Qed.

  Lemma base_typed_ge m v1 v2 τ : m ⊢ v1 : τ → v1 ⊑@{m} v2 → m ⊢ v2 : τ.
  Proof. intros Hv1τ. destruct 1; [|done]. by inversion Hv1τ; subst. Qed.
  Lemma base_typed_le m v1 v2 τ : m ⊢ v1 : τ → v2 ⊑@{m} v1 → m ⊢ v2 : τ.
  Proof.
    intros Hv1τ. destruct 1; simplify_type_equality; auto.
    constructor. eauto using base_typed_type_valid.
  Qed.

  Global Instance: PartialOrder (@subseteq_env M (base_val Ti Vi) _ m).
  Proof.
    intros m. repeat split.
    * intro. constructor.
    * destruct 1; [|done]. constructor; eauto using base_typed_ge.
    * destruct 1 as [τ v Hvτ|]; [|done].
      inversion_clear 1 as [τ' v' Hvτ'|]; [|done]. by inversion_clear Hvτ'.
  Qed.

  Lemma base_val_freeze_frozen v : frozen (freeze v).
  Proof. destruct v; constructor; auto using ptr_freeze_frozen. Qed.
  Lemma base_val_frozen_freeze v : frozen v → freeze v = v.
  Proof. destruct 1; simpl; f_equal; by apply ptr_frozen_freeze. Qed.
  Lemma base_val_freeze_idempotent v : freeze (freeze v) = freeze v.
  Proof. apply base_val_frozen_freeze, base_val_freeze_frozen. Qed.
  Lemma base_val_freeze_type_of v : type_of (freeze v) = type_of v.
  Proof. by destruct v; simpl; rewrite ?ptr_freeze_type_of. Qed.
  Lemma base_typed_freeze m v τ : m ⊢ freeze v : τ ↔ m ⊢ v : τ.
  Proof.
    split.
    * destruct v; inversion 1; constructor; auto. by apply ptr_typed_freeze.
    * destruct 1; constructor; auto. by apply ptr_typed_freeze.
  Qed.

  Lemma base_val_to_bytes_valid m v τ bs :
    m ⊢ v : τ → bs ∈ base_val_to_bytes v → Forall (byte_valid m) bs.
  Proof.
    destruct 1; simpl; intros; decompose_elem_of.
    * apply base_undef_bytes_valid.
    * apply Forall_fmap, Forall_true. constructor.
    * eapply Forall_fmap, (Forall_impl (ptr_seg_valid m));
        eauto using to_ptr_segs_valid. by constructor.
    * by repeat constructor.
  Qed.
  Lemma base_val_to_bytes_freeze v :
    base_val_to_bytes (freeze v) = base_val_to_bytes v.
  Proof. by destruct v; simpl; rewrite ?to_ptr_segs_freeze. Qed.
  Lemma base_val_to_bytes_exists v : ∃ bs, bs ∈ base_val_to_bytes v.
  Proof.
    destruct v; simpl; try by (eexists; constructor).
    edestruct encode_int_exists as [cs ?].
    eexists (BChar <$> cs). esolve_elem_of.
  Qed.
  Lemma base_val_to_bytes_length v bs :
    bs ∈ base_val_to_bytes v → length bs = size_of (TBase (type_of v)).
  Proof.
    destruct v; simpl; intros Hbs; try decompose_elem_of Hbs.
    * unfold base_undef_bytes. by rewrite replicate_length.
    * rewrite fmap_length, size_of_int. by apply encode_int_length.
    * by rewrite fmap_length, to_ptr_segs_length.
    * by rewrite size_of_int, size_TuChar.
  Qed.
  Lemma base_val_to_bytes_length_typed m v τ bs :
    m ⊢ v : τ → bs ∈ base_val_to_bytes v → length bs = size_of (TBase τ).
  Proof.
    intros. rewrite <-(type_of_correct m v τ) by done.
    auto using base_val_to_bytes_length.
  Qed.
  Lemma base_val_to_bytes_le m v1 v2 bs1 :
    v1 ⊑@{m} v2 → bs1 ∈ base_val_to_bytes v1 →
    ∃ bs2, bs2 ∈ base_val_to_bytes v2 ∧ bs1 ⊑@{m}* bs2.
  Proof.
    destruct 1 as [τ v| ]; simpl.
    * intros; decompose_elem_of.
      destruct (base_val_to_bytes_exists v) as [bs ?].
      eauto 6 using base_undef_bytes_le, base_val_to_bytes_valid,
        base_val_to_bytes_length_typed.
    * by exists bs1.
  Qed.
  Lemma base_val_to_bytes_ge m v1 v2 bs2 :
    v1 ⊑@{m} v2 → bs2 ∈ base_val_to_bytes v2 →
    ∃ bs1, bs1 ∈ base_val_to_bytes v1 ∧ bs1 ⊑@{m}* bs2.
  Proof.
    destruct 1 as [τ v| ]; simpl.
    * intros; decompose_elem_of.
      exists (base_undef_bytes τ). split; [solve_elem_of |].
      eauto using base_undef_bytes_le, base_val_to_bytes_valid,
        base_val_to_bytes_length_typed.
    * by exists bs2.
  Qed.

  Lemma base_val_to_bytes_undef v bs :
    bs ∈ base_val_to_bytes v → BUndef ∈ bs ↔ v = VUndef (type_of v).
  Proof.
    intros Hbs. split.
    * intros Hud. destruct v; simpl in *; decompose_elem_of.
      + done.
      + rewrite elem_of_list_fmap in Hud. by destruct Hud as [? [? _]].
      + rewrite elem_of_list_fmap in Hud. by destruct Hud as [? [? _]].
      + by rewrite elem_of_list_singleton in Hud.
    * intros Hv. revert Hbs. rewrite Hv. simpl. unfold base_undef_bytes.
      generalize (size_of_pos (TBase (type_of v))).
      destruct (size_of (TBase (type_of v))); simpl.
      + lia.
      + rewrite elem_of_singleton. intros. simplify_equality. by left.
  Qed.
  Lemma base_val_to_bytes_undef_typed m v τ bs :
    m ⊢ v : τ → bs ∈ base_val_to_bytes v → BUndef ∈ bs ↔ v = VUndef τ.
  Proof.
    intros. rewrite <-(type_of_correct m v τ) by done.
    eauto using base_val_to_bytes_undef.
  Qed.

  Lemma base_val_of_bytes_typed m τ bs :
    base_type_valid get_env τ → Forall (byte_valid m) bs →
    m ⊢ base_val_of_bytes τ bs : τ.
  Proof.
    assert (∀ bs pss,
      Forall2 (λ b ps, maybe_BPtrSeg b = Some ps) bs pss →
      Forall (byte_valid m) bs → Forall (ptr_seg_valid m) pss).
    { induction 1 as [|[]]; inversion 1; simplify_equality;
        constructor; eauto using BPtrSeg_valid_inv. }
    destruct 1; simpl;
      repeat case_match; simplify_option_equality;
      repeat constructor; decompose_Forall_hyps;
      eauto using decode_int_typed, of_ptr_segs_type_of, eq_sym,
        BPtrSeg_valid_inv, of_ptr_segs_typed.
  Qed.
  Lemma base_val_of_bytes_type_of τ bs :
    base_type_valid get_env τ → type_of (base_val_of_bytes τ bs) = τ.
  Proof.
    destruct 1; simpl;
      repeat case_match; simplify_option_equality;
      eauto using decode_int_typed, of_ptr_segs_type_of, eq_sym, f_equal.
  Qed.

  Lemma base_val_of_to_bytes v bs :
    bs ∈ base_val_to_bytes v → base_val_of_bytes (type_of v) bs = freeze v.
  Proof.
    destruct v as [τ|x|p|ps]; simpl; intros Hbs.
    * decompose_elem_of Hbs. unfold base_undef_bytes.
      pose proof (size_of_pos (TBase τ)).
      destruct (size_of (TBase τ)), τ; simpl; auto with lia.
    * apply elem_of_fmap in Hbs.
      destruct Hbs as [[|c cs] [? Hcs]]; subst; simpl.
      + apply encode_int_length in Hcs. edestruct int_type_size_ne_0; eauto.
      + rewrite mapM_fmap_Some by done. simpl. by rewrite encode_decode_int.
    * decompose_elem_of Hbs; simpl.
      rewrite mapM_fmap_Some by done. simpl. by rewrite (of_to_ptr_segs _).
    * decompose_elem_of Hbs; simpl. by case_decide.
  Qed.
  Lemma base_val_of_to_bytes_typed m v τ bs :
    m ⊢ v : τ → bs ∈ base_val_to_bytes v → base_val_of_bytes τ bs = freeze v.
  Proof.
    intro. rewrite <-(type_of_correct m v τ); auto using base_val_of_to_bytes.
  Qed.
  Lemma base_val_of_bytes_frozen τ bs : frozen (base_val_of_bytes τ bs).
  Proof.
    destruct τ; simpl; repeat case_match; constructor.
    simplify_option_equality. eauto using of_ptr_segs_frozen.
  Qed.

  Lemma base_val_to_of_bytes τ bs (v := base_val_of_bytes τ bs) :
    bs ∈ base_val_to_bytes v ∧ τ = type_of v ∨ v = VUndef τ.
  Proof.
    destruct τ as [τi|τp]; simpl in *.
    * destruct bs as [|[|c|ps] bs]; simpl in *.
      + right. unfold v. by rewrite decode_int_nil.
      + by right.
      + destruct (mapM maybe_BChar bs) as [cs|] eqn:Hcs;
          simpl in *; subst; [| by right].
        destruct (decode_int τi (c :: cs)) as [x|] eqn:Hx;
          simpl in *; subst; [| by right].
        pose proof (decode_int_typed _ _ _ Hx).
        apply decode_encode_int in Hx. subst.
        left. split; [|done]. apply elem_of_fmap_2_alt with (c :: cs); [done|].
        simpl. f_equal. apply (mapM_fmap_Some_inv _ maybe_BChar); [|done].
        by intros ? [] ?; simplify_equality.
      + unfold v. destruct bs; repeat case_decide; solve_elem_of.
    * destruct (mapM maybe_BPtrSeg bs) as [ps|] eqn:Hps;
        simpl in *; subst; [|by right].
      destruct (of_ptr_segs τp ps) as [p|] eqn:Hp;
        simpl in *; subst; [left; split| by right].
      + erewrite to_of_ptr_segs by eauto.
        apply elem_of_singleton, (mapM_fmap_Some_inv _ maybe_BPtrSeg); [|done].
        by intros ? [] ?; simplify_equality.
      + f_equal. eauto using of_ptr_segs_type_of.
  Qed.
  Lemma base_val_to_of_bytes_le m τ bs2 :
    Forall (byte_valid m) bs2 →
    length bs2 = size_of (TBase τ) → ∃ bs1, bs1 ⊑@{m}* bs2 ∧
      bs1 ∈ base_val_to_bytes (base_val_of_bytes τ bs2).
  Proof.
    destruct (base_val_to_of_bytes τ bs2) as [[? _]|Hbs2].
    * by exists bs2.
    * rewrite Hbs2. simpl. exists (base_undef_bytes τ).
      split. auto using base_undef_bytes_le. solve_elem_of.
  Qed.

  Lemma base_val_of_bytes_undef τ bs :
    BUndef ∈ bs → base_val_of_bytes τ bs = VUndef τ.
  Proof.
    intro. destruct (base_val_to_of_bytes τ bs) as [[? Hτ]|?].
    * rewrite Hτ at 2. eapply base_val_to_bytes_undef; eauto.
    * done.
  Qed.
  Lemma base_val_of_bytes_length τ bs :
    length bs ≠ size_of (TBase τ) → base_val_of_bytes τ bs = VUndef τ.
  Proof.
    intro Hlen. destruct (base_val_to_of_bytes τ bs) as [[? Hτ]|?].
    * destruct Hlen. by erewrite Hτ, base_val_to_bytes_length.
    * done.
  Qed.
  Lemma base_val_of_bytes_le m τ bs1 bs2 :
    base_type_valid get_env τ →
    Forall (byte_valid m) bs1 → bs1 ⊑@{m}* bs2 →
    base_val_of_bytes τ bs1 ⊑@{m} base_val_of_bytes τ bs2.
  Proof.
    intros.
    destruct (bytes_le_eq_or_undef m bs1 bs2); subst; trivial.
    rewrite (base_val_of_bytes_undef τ bs1) by done.
    constructor. eapply base_val_of_bytes_typed; eauto using bytes_valid_ge.
  Qed.
  Lemma base_val_of_bytes_inj m v1 v2 τ bs :
    m ⊢ v1 : τ → m ⊢ v2 : τ →
    bs ∈ base_val_to_bytes v1 → bs ∈ base_val_to_bytes v2 →
    freeze v1 = freeze v2.
  Proof.
    intros ?? Hv1 Hv2.
    apply base_val_of_to_bytes in Hv1. apply base_val_of_to_bytes in Hv2.
    erewrite type_of_correct in Hv1 by eauto.
    erewrite type_of_correct in Hv2 by eauto. congruence.
  Qed.
  Lemma base_val_to_bytes_le_inv m v1 v2 bs1 bs2 τ :
    m ⊢ v1 : τ → m ⊢ v2 : τ →
    bs1 ∈ base_val_to_bytes v1 → bs2 ∈ base_val_to_bytes v2 →
    bs1 ⊑@{m}* bs2 → freeze v1 ⊑@{m} freeze v2.
  Proof.
    intros. erewrite <-(base_val_of_to_bytes v1),
      <-(base_val_of_to_bytes v2), !type_of_correct by eauto.
    apply base_val_of_bytes_le; eauto using base_typed_type_valid,
      base_val_to_bytes_valid.
  Qed.
  Lemma base_val_of_bytes_le_undef m τ bs1 bs2 :
    bs1 ⊑@{m}* bs2 →
    base_val_of_bytes τ bs2 = VUndef τ → base_val_of_bytes τ bs1 = VUndef τ.
  Proof.
    intros. destruct (bytes_le_eq_or_undef m bs1 bs2); subst; trivial.
    by apply base_val_of_bytes_undef.
  Qed.

  Lemma base_val_of_bytes_masked m τ bs1 bs2 cs2 :
    base_type_valid get_env τ →
    bs1 ⊑@{m}* bs2 → Forall (byte_valid m) cs2 →
    base_val_of_bytes τ bs2 = base_val_of_bytes τ cs2 →
    base_val_of_bytes τ (mask_bytes bs1 cs2) = base_val_of_bytes τ bs1.
  Proof.
    intros ? Hbs ? Hbscs. destruct (decide (BUndef ∈ bs1)) as [?|Hbs1].
    * rewrite (base_val_of_bytes_undef _ bs1) by done.
      destruct (decide (length cs2 = size_of (TBase τ)));
        [destruct (decide (length bs1 = size_of (TBase τ))) |].
      + rewrite base_val_of_bytes_undef;
          auto using mask_bytes_undef, same_length_length_2 with congruence.
      + apply base_val_of_bytes_le_undef with m cs2; auto using mask_bytes_le.
        rewrite <-Hbscs. apply base_val_of_bytes_length.
        by erewrite <-Forall2_length by eauto.
      + eauto using base_val_of_bytes_le_undef, mask_bytes_le,
          base_val_of_bytes_length.
    * pose proof (bytes_le_no_undef _ _ _ Hbs Hbs1); subst.
      by rewrite mask_bytes_no_undef.
  Qed.

  Lemma base_val_of_bytes_resize_take τ bs :
    base_val_of_bytes τ (resize (size_of (TBase τ)) BUndef bs) =
      base_val_of_bytes τ (take (size_of (TBase τ)) bs).
  Proof.
    destruct (le_lt_dec (size_of (TBase τ)) (length bs)).
    { by rewrite resize_le. }
    rewrite resize_ge, take_ge by lia.
    rewrite (base_val_of_bytes_length _ bs) by lia.
    rewrite base_val_of_bytes_undef; [done |].
    destruct (size_of (TBase τ) - length bs) eqn:?; [lia |].
    simpl. rewrite elem_of_app, elem_of_cons. auto.
  Qed.

  Lemma base_val_of_bytes_trans m τ bs1 bs2 bs3 :
    bs1 ⊑@{m}* bs2 → bs2 ⊑@{m}* bs3 →
    base_val_of_bytes τ bs1 = base_val_of_bytes τ bs3 →
    base_val_of_bytes τ bs2 = base_val_of_bytes τ bs3.
  Proof.
    intros ?? Hbs. destruct (bytes_le_eq_or_undef m bs2 bs3); subst; auto.
    by rewrite <-Hbs, !base_val_of_bytes_undef by eauto using bytes_le_undef.
  Qed.

  Lemma base_val_0_typed m τ : base_type_valid get_env τ → m ⊢ base_val_0 τ : τ.
  Proof. by destruct 1; simpl; repeat constructor; rewrite ?int_of_Z_typed. Qed.
End base_value.
