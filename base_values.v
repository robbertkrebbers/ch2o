(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export pointers bits.
Local Open Scope cbase_type_scope.

Inductive base_val (Ti : Set) :=
  | VIndet : base_type Ti → base_val Ti
  | VInt : int_type Ti → Z → base_val Ti
  | VPtr : ptr Ti → base_val Ti
  | VByte : list (bit Ti) → base_val Ti.
Arguments VIndet {_} _.
Arguments VInt {_} _ _.
Arguments VPtr {_} _.
Arguments VByte {_} _.

Instance base_val_eq_dec {Ti : Set} `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}
  (v1 v2 : base_val Ti) : Decision (v1 = v2).
Proof. solve_decision. Defined.

Section operations.
  Context `{IntEnv Ti} `{PtrEnv Ti} `{TypeOfIndex Ti M} `{IndexAlive M}.

  Inductive base_typed' (m : M) : base_val Ti → base_type Ti → Prop :=
    | VIndet_typed τ : base_type_valid get_env τ → base_typed' m (VIndet τ) τ
    | VInt_typed x τ : int_typed x τ → base_typed' m (VInt τ x) (intt τ)
    | VPtr_typed p τ : m ⊢ p : τ → base_typed' m (VPtr p) (τ.*)
    | VByte_typed bs :
       ¬Forall (BIndet =) bs → ¬Forall (is_Some ∘ maybe_BBit) bs →
       m ⊢* valid bs → length bs = char_bits →
       base_typed' m (VByte bs) uchar.
  Global Instance base_typed:
    Typed M (base_type Ti) (base_val Ti) := base_typed'.

  Global Instance type_of_base_val: TypeOf (base_type Ti) (base_val Ti) := λ v,
    match v with
    | VIndet τ => τ
    | VInt τ _ => intt τ
    | VPtr p => type_of p.*
    | VByte _ => uchar
    end.
  Global Instance base_type_check:
      TypeCheck M (base_type Ti) (base_val Ti) := λ m v,
    match v with
    | VIndet τ => guard (base_type_valid get_env τ); Some τ
    | VInt τ x => guard (int_typed x τ); Some (intt τ)
    | VPtr p => TPtr <$> type_check m p
    | VByte bs =>
       guard (¬Forall (BIndet =) bs); 
       guard (¬Forall (is_Some ∘ maybe_BBit) bs);
       guard (m ⊢* valid bs);
       guard (length bs = char_bits); Some uchar
    end.

  Inductive base_val_le' (m : M) : relation (base_val Ti) :=
    | base_val_le_refl v : base_val_le' m v v
    | VIndet_le τ v : m ⊢ v : τ → base_val_le' m (VIndet τ) v
    | VInt_le x τ : base_val_le' m (VInt τ x) (VInt τ x)
    | VPtr_le p : base_val_le' m (VPtr p) (VPtr p)
    | VByte_le bs1 bs2 :
       ¬Forall (BIndet =) bs1 →
       ¬Forall (is_Some ∘ maybe_BBit) bs2 →
       bs1 ⊑@{m}* bs2 → base_val_le' m (VByte bs1) (VByte bs2)
    | VByte_Vint_le bs1 x2 :
       ¬Forall (BIndet =) bs1 →
       ¬Forall (is_Some ∘ maybe_BBit) bs1 →
       bs1 ⊑@{m}* BBit <$> to_bits uchar x2 →
       int_typed x2 uchar → base_val_le' m (VByte bs1) (VInt uchar x2).
  Global Instance base_val_le: SubsetEqEnv M (base_val Ti) := base_val_le'.

  Definition base_val_to_bits (v : base_val Ti) : list (bit Ti) :=
    match v with
    | VIndet τ => base_indet_bits τ
    | VInt τ x => BBit <$> to_bits τ x
    | VPtr p => BPtr <$> to_ptr_bits p
    | VByte bs => bs
    end.
  Definition base_val_of_bits
      (τ : base_type Ti) (bs : list (bit Ti)) : base_val Ti :=
    let bs := resize (bit_size_of τ) BIndet bs in
    match τ with
    | intt τi =>
       match mapM maybe_BBit bs with
       | Some cs => VInt τi (of_bits τi cs)
       | None =>
          if decide (τi = uchar%IT) then
            if decide (Forall (BIndet =) bs) then VIndet τ else VByte bs
          else VIndet τ
       end
    | τp.* =>
       match mapM maybe_BPtr bs ≫= of_ptr_bits τp with
       | Some p => VPtr p
       | None => VIndet τ
       end
    end.

  Inductive base_val_frozen : Frozen (base_val Ti) :=
    | VIndet_frozen τ : frozen (@VIndet Ti τ)
    | VInt_frozen τ x : frozen (@VInt Ti τ x)
    | VPtr_frozen p : frozen p → frozen (@VPtr Ti p)
    | VByte_frozen c : frozen (@VByte Ti c).
  Global Existing Instance base_val_frozen.
  Global Instance base_val_freeze : Freeze (base_val Ti) := λ v,
    match v with
    | VIndet τ => VIndet τ
    | VInt τ x => VInt τ x
    | VPtr p => VPtr (freeze p)
    | VByte c => VByte c
    end.

  Definition base_val_0 (τ : base_type Ti) : base_val Ti :=
    match τ with intt τ => VInt τ 0 | τ.* => VPtr (NULL τ) end.

  Inductive base_unop_typed : unop → base_type Ti → base_type Ti → Prop :=
    | unop_TInt_typed op τ : base_unop_typed op (intt τ) (intt τ).
  Definition base_unop_ok (op : unop) (v : base_val Ti) : Prop :=
    match v with
    | VInt τ x => int_unop_ok τ op x
    | _ => False
    end.
  Global Arguments base_unop_ok !_ !_ /.
  Definition base_unop (op : unop) (v : base_val Ti) : base_val Ti :=
    match v with
    | VInt τ x => VInt τ (int_unop τ op x)
    | _ => VIndet (type_of v)
    end.
  Global Arguments base_unop !_ !_ /.

  Inductive base_binop_typed :
      binop → base_type Ti → base_type Ti → base_type Ti → Prop :=
    | binop_TInt_TInt_typed op τ: base_binop_typed op (intt τ) (intt τ) (intt τ)
    | CompOp_TPtr_TPtr_typed c τ : base_binop_typed (CompOp c) (τ.*) (τ.*) sptr
    | PlusOp_TPtr_TInt_typed τ σ : base_binop_typed PlusOp (τ.*) (intt σ) (τ.*)
    | PlusOp_VInt_TPtr_typed τ σ : base_binop_typed PlusOp (intt σ) (τ.*) (τ.*)
    | MinusOp_TPtr_TInt_typed τ σ: base_binop_typed MinusOp (τ.*) (intt σ) (τ.*)
    | MinusOp_TInt_TPtr_typed τ σ: base_binop_typed MinusOp (intt σ) (τ.*) (τ.*)
    | MinusOp_TPtr_TPtr_typed τ  : base_binop_typed MinusOp (τ.*) (τ.*) sptr.
  Definition base_binop_ok (m : M) (op : binop) (v1 v2 : base_val Ti) : Prop :=
    match v1, v2, op with
    | VInt τ x1, VInt _ x2, _ => int_binop_ok τ op x1 x2
    | VPtr p1, VPtr p2, CompOp c => ptr_minus_ok m p1 p2
    | VPtr p, VInt _ i, PlusOp => ptr_plus_ok m i p
    | VInt _ i, VPtr p, PlusOp => ptr_plus_ok m i p
    | VPtr p, VInt _ i, MinusOp => ptr_plus_ok m (-i) p
    | VInt _ i, VPtr p, MinusOp => ptr_plus_ok m (-i) p
    | VPtr p1, VPtr p2, MinusOp => ptr_minus_ok m p1 p2
    | _, _, _ => False
    end.
  Global Arguments base_binop_ok _ !_ !_ !_ /.
  Definition base_binop (op : binop) (v1 v2 : base_val Ti) : base_val Ti :=
    match v1, v2, op with
    | VInt τ x1, VInt _ x2, _ => VInt τ (int_binop τ op x1 x2)
    | VPtr p1, VPtr p2, CompOp c =>
       let i := ptr_minus p1 p2 in
       VInt sptr $ Z_of_sumbool (decide_rel (Z_comp c) i 0)
    | VPtr p, VInt _ i, PlusOp => VPtr (ptr_plus i p)
    | VInt _ i, VPtr p, PlusOp => VPtr (ptr_plus i p)
    | VPtr p, VInt _ i, MinusOp => VPtr (ptr_plus (-i) p)
    | VInt _ i, VPtr p, MinusOp => VPtr (ptr_plus (-i) p)
    | VPtr p1, VPtr p2, MinusOp => VInt sptr (ptr_minus p1 p2)
    | _, _, _ => VIndet (type_of v1)
    end.
  Global Arguments base_binop !_ !_ !_ /.

  Inductive base_cast_typed : base_type Ti → base_type Ti → Prop :=
    | TInt_cast_typed τ1 τ2 : base_cast_typed (intt τ1) (intt τ2)
    | TPtr_to_void_cast_typed τ : base_cast_typed (τ.*) (void.*)
    | TPtr_to_uchar_cast_typed τ : base_cast_typed (τ.*) (uchar.*)
    | TPtr_of_void_cast_typed τ :
       ptr_type_valid get_env τ → base_cast_typed (void.*) (τ.*)
    | TPtr_of_uchar_cast_typed τ :
       ptr_type_valid get_env τ → base_cast_typed (uchar.*) (τ.*).
  Definition base_cast_ok (τ : base_type Ti) (v : base_val Ti) : Prop :=
    match v, τ with
    | VInt _ x, intt σ => int_cast_ok σ x
    | VPtr p, σ.* => ptr_cast_ok σ p
    | _ , _ => False
    end.
  Global Arguments base_cast_ok !_ !_ /.
  Definition base_cast (τ : base_type Ti) (v : base_val Ti) : base_val Ti :=
    match v, τ with
    | VInt _ x, intt σ => VInt σ (int_cast σ x)
    | VPtr p, σ.* => VPtr (ptr_cast σ p)
    | _ , _ => VIndet (type_of v)
    end.
  Global Arguments base_cast !_ !_ /.
End operations.

Section properties.
Context `{MemorySpec Ti M}.
Implicit Types v : base_val Ti.
Implicit Types m : M.
Implicit Types τ : base_type Ti.
Implicit Types bs : list (bit Ti).

Lemma base_typed_type_valid m v τ : m ⊢ v : τ → base_type_valid get_env τ.
Proof. destruct 1; try econstructor; eauto using ptr_typed_type_valid. Qed.

Global Instance: TypeOfSpec M (base_type Ti) (base_val Ti).
Proof. destruct 1; simpl; f_equal; eauto using type_of_correct. Qed.
Global Instance: TypeCheckSpec M (base_type Ti) (base_val Ti).
Proof.
  intros m v τ. split.
  * destruct v; intros; simplify_option_equality;
      constructor; eauto using type_check_sound.
  * by destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma base_typed_weaken_mem m1 m2 v τ :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  m1 ⊢ v : τ → m2 ⊢ v : τ.
Proof.
  destruct 2; econstructor;
    eauto using ptr_typed_weaken_mem, bits_valid_weaken_mem.
Qed.
Lemma base_val_le_weaken_mem m1 m2 v1 v2 :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  v1 ⊑@{m1} v2 → v1 ⊑@{m2} v2.
Proof.
  destruct 2; econstructor;
    eauto using base_typed_weaken_mem, bits_le_weaken_mem.
Qed.

Lemma base_typed_ge m v1 v2 τ : m ⊢ v1 : τ → v1 ⊑@{m} v2 → m ⊢ v2 : τ.
Proof.
  intros Hv1τ. destruct 1; auto; inversion Hv1τ; subst; auto.
  * constructor; eauto using bits_valid_ge,
      Forall_BIndet_le_inv, Forall2_length_l.
  * by constructor.
Qed.
Lemma base_typed_le m v1 v2 τ : m ⊢ v1 : τ → v2 ⊑@{m} v1 → m ⊢ v2 : τ.
Proof.
  intros Hv1τ. destruct 1; simplify_type_equality; auto.
  * constructor; eauto using base_typed_type_valid.
  * inversion Hv1τ; subst. constructor; eauto using bits_valid_le,
      mapM_maybe_BBit_is_Some_le, Forall2_length_r.
  * inversion Hv1τ; subst. constructor; eauto.
    { eapply bits_valid_le with (BBit <$> to_bits uchar _); eauto.
      apply Forall_fmap, Forall_true. constructor. }
    erewrite Forall2_length by eauto.
    by rewrite fmap_length, to_bits_length, int_bits_char.
Qed.

Global Instance: PartialOrder (@subseteq_env M (base_val Ti) _ m).
Proof.
  intros m. repeat split.
  * constructor.
  * destruct 1; auto.
    + constructor; eauto using base_typed_ge.
    + inversion 1; subst; constructor; eauto using mapM_maybe_BBit_is_Some_le.
      - etransitivity; eauto.
      - etransitivity; eauto.
    + inversion 1; subst; constructor; eauto.
  * destruct 1 as [|τ' v' Hvτ'| | | |]; inversion 1; subst; auto.
    + by inversion Hvτ'.
    + f_equal. by apply (anti_symmetric (⊑@{m}*)).
Qed.

Lemma base_val_to_bits_valid m v τ :
  m ⊢ v : τ → m ⊢* valid (base_val_to_bits v).
Proof.
  destruct 1; simpl.
  * apply base_indet_bits_valid.
  * apply Forall_fmap, Forall_true. constructor.
  * apply Forall_fmap; eapply (Forall_impl (valid m));
      eauto using to_ptr_bits_valid, BPtr_valid.
  * done.
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
Lemma base_typed_int_frozen m v τi : m ⊢ v : intt τi → frozen v.
Proof. inversion_clear 1; constructor. Qed.

Lemma base_val_to_bits_freeze v :
  base_val_to_bits (freeze v) = base_val_to_bits v.
Proof. by destruct v; simpl; rewrite ?to_ptr_bits_freeze. Qed.
Lemma base_val_to_bits_length m v τ :
  m ⊢ v : τ → length (base_val_to_bits v) = bit_size_of (base τ).
Proof.
  destruct 1; simpl.
  * unfold base_indet_bits. by rewrite replicate_length.
  * by rewrite fmap_length, bit_size_of_int, to_bits_length.
  * by erewrite fmap_length, to_ptr_bits_length by eauto.
  * by rewrite bit_size_of_int, int_bits_char.
Qed.
Lemma base_val_to_bits_le m v1 v2 :
  v1 ⊑@{m} v2 → base_val_to_bits v1 ⊑@{m}* base_val_to_bits v2.
Proof.
  destruct 1; simpl; by eauto using base_indet_bits_le,
    base_val_to_bits_valid, base_val_to_bits_length.
Qed.
Lemma VByte_typed_alt m bs :
  m ⊢ VByte bs : uchar ↔
    m ⊢* valid bs ∧ length bs = char_bits ∧
    base_val_of_bits uchar bs = VByte bs.
Proof.
  unfold base_val_of_bits. split.
  * inversion 1 as [| | |? Hindet Hbit]; subst.
    split; auto. rewrite resize_all_alt by
      (by rewrite bit_size_of_int, int_bits_char).
    repeat (simplify_option_equality || case_match); auto.
    + destruct Hbit. rewrite <-mapM_is_Some; eauto.
    + done.
  * intros (?&?&Hbs). rewrite resize_all_alt in Hbs by
      (by rewrite bit_size_of_int, int_bits_char).
    repeat (simplify_option_equality || case_match). constructor; auto.
    by rewrite <-mapM_is_Some, <-eq_None_not_Some.
Qed.

Lemma mapM_maybe_BPtr_valid m bs pss :
  mapM maybe_BPtr bs = Some pss → m ⊢* valid bs → m ⊢* valid pss.
Proof.
  rewrite mapM_Some. induction 1 as [|[]]; inversion 1;
    simplify_equality; constructor; eauto using BPtr_valid_inv.
Qed.

Lemma base_val_of_bits_typed m τ bs :
  base_type_valid get_env τ → m ⊢* valid bs → m ⊢ base_val_of_bits τ bs : τ.
Proof.
  destruct 1; repeat (case_match || simplify_option_equality);
    decompose_Forall_hyps; constructor; simpl; auto.
  * apply of_bits_typed. rewrite <-bit_size_of_int.
    by erewrite <-Forall2_length, resize_length by eauto using mapM_Some_1.
  * constructor.
  * by rewrite <-mapM_is_Some, <-eq_None_not_Some. 
  * apply Forall_resize. constructor. done.
  * by rewrite resize_length, bit_size_of_int, int_bits_char.
  * constructor.
  * eapply of_ptr_bits_typed; eauto using mapM_maybe_BPtr_valid,
      Forall_resize, BIndet_valid.
  * by constructor.
  * by constructor.
Qed.
Lemma base_val_of_bits_type_of τ bs :
  base_type_valid get_env τ → type_of (base_val_of_bits τ bs) = τ.
Proof.
  destruct 1; repeat (case_match || simplify_option_equality);
    eauto using of_ptr_bits_type_of, eq_sym, f_equal.
Qed.
Lemma base_val_of_bits_resize τ bs sz :
  base_type_valid get_env τ → bit_size_of (base τ) ≤ sz →
  base_val_of_bits τ (resize sz BIndet bs) = base_val_of_bits τ bs.
Proof. destruct 1; intros; simpl; by rewrite !resize_resize. Qed.

Lemma base_val_of_to_bits m v τ :
  m ⊢ v : τ → base_val_of_bits τ (base_val_to_bits v) = freeze v.
Proof.
  destruct 1 as [τ|x|p τ|c Hindet Hbit Hc]; simpl.
  * unfold base_indet_bits, base_val_of_bits. destruct τ as [τ|τ].
    + rewrite resize_all_alt
        by (by rewrite replicate_length, bit_size_of_int).
      repeat case_match; auto.
      - pose proof (bit_size_of_base_ne_0 (intt τ)%BT).
        by destruct (bit_size_of _).
      - exfalso; eauto using Forall_replicate.
    + repeat case_match; auto. by destruct (bit_size_of _).
  * rewrite resize_all_alt by
      (by rewrite bit_size_of_int, fmap_length, to_bits_length).
    rewrite mapM_fmap_Some by done. by rewrite of_to_bits by done.
  * rewrite resize_all_alt by
      (by erewrite fmap_length, to_ptr_bits_length by eauto).
    rewrite mapM_fmap_Some by done; simpl. by rewrite (of_to_ptr_bits m).
  * rewrite <-mapM_is_Some, <-eq_None_not_Some in Hbit.
    rewrite resize_all_alt by (by rewrite bit_size_of_int, int_bits_char).
    by destruct c; repeat case_match.
Qed.
Lemma base_val_of_bits_frozen m τ bs :
  m ⊢* valid bs → frozen (base_val_of_bits τ bs).
Proof.
  destruct τ; repeat (case_match || simplify_option_equality); constructor.
  eapply of_ptr_bits_frozen; eauto using mapM_maybe_BPtr_valid,
      Forall_resize, BIndet_valid.
Qed.

Lemma base_val_to_of_bits m τ bs :
  m ⊢* valid bs → length bs = bit_size_of (base τ) →
  base_val_to_bits (base_val_of_bits τ bs) = bs ∨
  base_val_of_bits τ bs = VIndet τ.
Proof.
  intros ? Hsz. destruct τ as [τ|τ]; simpl.
  * rewrite resize_all_alt by done. repeat case_match; simpl; auto.
    left. erewrite (mapM_fmap_Some_inv maybe_BBit BBit _ bs) by
      (by eauto; intros ? [] ?; simplify_equality).
    by rewrite to_of_bits by
      (by erewrite <-?bit_size_of_int, <-mapM_length by eauto).
  * rewrite resize_all_alt by done.
    repeat (simplify_option_equality || case_match); auto.
    left. erewrite (mapM_fmap_Some_inv maybe_BPtr BPtr _ bs) by
      (by eauto; intros ? [] ?; simplify_equality).
    by erewrite to_of_ptr_bits by eauto using
      mapM_maybe_BPtr_valid, Forall_resize, BIndet_valid.
Qed.

Lemma base_val_of_bits_indet m τ bs :
  τ ≠ uchar → length bs = bit_size_of (base τ) →
  BIndet ∈ bs → base_val_of_bits τ bs = VIndet τ.
Proof.
  intros ? Hsz Hbs. assert (∀ xs, ¬mapM maybe_BBit bs = Some xs) as help1.
  { revert Hbs. clear Hsz.
    induction bs; rewrite ?elem_of_nil, ?elem_of_cons; auto.
    intros [?|?] ??; simplify_option_equality; naive_solver. }
  assert (∀ pss, ¬mapM maybe_BPtr bs = Some pss).
  { revert Hbs. clear Hsz help1.
    induction bs; rewrite ?elem_of_nil, ?elem_of_cons; auto.
    intros [?|?] ??; simplify_option_equality; naive_solver. }
  unfold base_val_of_bits. rewrite resize_all_alt by done.
  repeat (simplify_option_equality || case_match); naive_solver.
Qed.

Lemma base_val_of_bits_replicate τ :
  base_val_of_bits τ (replicate (bit_size_of τ) BIndet) = VIndet τ.
Proof.
  pose proof (bit_size_of_base_ne_0 τ).
  destruct τ; simpl; repeat case_match; auto.
  * destruct (bit_size_of _); simplify_equality.
  * exfalso. eauto using Forall_resize, Forall_replicate.
  * destruct (bit_size_of _); simplify_equality.
Qed.

Lemma base_val_to_of_bits_le m τ bs :
  m ⊢* valid bs → length bs = bit_size_of (base τ) →
  base_val_to_bits (base_val_of_bits τ bs) ⊑@{m}* bs.
Proof.
  intros. destruct (base_val_to_of_bits m τ bs) as [Hbs|Hbs]; auto.
  * by rewrite Hbs.
  * rewrite Hbs; simpl. by apply base_indet_bits_le.
Qed.
Lemma base_val_of_bits_le m τ bs1 bs2 :
  base_type_valid get_env τ → m ⊢* valid bs1 →
  bs1 ⊑@{m}* bs2 → base_val_of_bits τ bs1 ⊑@{m} base_val_of_bits τ bs2.
Proof.
  intros Hτ. revert bs1 bs2. cut (∀ bs1 bs2,
    m ⊢* valid bs1 → length bs1 = bit_size_of τ → length bs2 = bit_size_of τ →
    bs1 ⊑@{m}* bs2 → base_val_of_bits τ bs1 ⊑@{m} base_val_of_bits τ bs2).
  { intros help ????. rewrite <-(base_val_of_bits_resize τ bs1 (bit_size_of τ)),
      <-(base_val_of_bits_resize τ bs2 (bit_size_of τ)) by done.
    apply help; rewrite ?resize_length; auto using
      Forall_resize, BIndet_valid, Forall2_resize. }
  intros bs1 bs2 ? Hbs1 Hbs2 Hbs. destruct (decide (τ = uchar)); subst.
  { unfold base_val_of_bits. rewrite !resize_all_alt by done.
    rewrite bit_size_of_int in Hbs1, Hbs2. destruct (mapM _ bs1) eqn:?.
    { by erewrite mapM_maybe_BBit_Some_le by eauto. }
    repeat case_decide; simplify_equality.
    * destruct (mapM maybe_BBit bs2) as [βs|] eqn:Hβs; auto.
      do 2 constructor. apply of_bits_typed. by erewrite <-mapM_length by eauto.
    * destruct (mapM maybe_BBit bs2) as [βs|] eqn:Hβs.
      { do 2 constructor. apply of_bits_typed.
        by erewrite <-mapM_length by eauto. }
      do 2 constructor; simpl; auto.
      + by rewrite <-mapM_is_Some, <-eq_None_not_Some.
      + eauto using bits_valid_ge.
      + by rewrite int_bits_char in Hbs2.
    * exfalso; eauto using Forall_BIndet_le_inv.
    * destruct (mapM maybe_BBit bs2) as [βs|] eqn:Hβs.
      { constructor; auto.
        + by rewrite <-mapM_is_Some, <-eq_None_not_Some.
        + rewrite to_of_bits by (by erewrite <-mapM_length by eauto).
          by erewrite <-(mapM_fmap_Some_inv maybe_BBit BBit) by
            (by eauto; intros ? [] ?; simplify_equality).
        + apply of_bits_typed. by erewrite <-mapM_length by eauto. }
      constructor; auto. by rewrite <-mapM_is_Some, <-eq_None_not_Some. }
  intros. destruct (bits_le_eq_or_indet m bs1 bs2); subst; auto.
  rewrite (base_val_of_bits_indet m τ bs1); auto.
  constructor. apply base_val_of_bits_typed; eauto using bits_valid_ge.
Qed.

Lemma base_val_to_bits_le_inv m v1 v2 bs1 bs2 τ :
  ⊢ valid m → m ⊢ v1 : τ → m ⊢ v2 : τ →
  base_val_to_bits v1 ⊑@{m}* base_val_to_bits v2 → freeze v1 ⊑@{m} freeze v2.
Proof.
  intros. rewrite <-(base_val_of_to_bits m v1 τ),
    <-(base_val_of_to_bits m v2 τ) by done.
  apply base_val_of_bits_le; eauto
    using base_val_to_bits_valid, base_typed_type_valid.
Qed.
Lemma base_val_to_bits_inj m v1 v2 τ :
  m ⊢ v1 : τ → m ⊢ v2 : τ →
  base_val_to_bits v1 = base_val_to_bits v2 → freeze v1 = freeze v2.
Proof.
  intros. by rewrite <-(base_val_of_to_bits m v1 τ),
    <-(base_val_of_to_bits m v2 τ) by done; f_equal.
Qed.

Lemma base_val_of_bits_char_inj bs1 bs2 :
  length bs1 = bit_size_of uchar → length bs2 = bit_size_of uchar →
  base_val_of_bits uchar bs1 = base_val_of_bits uchar bs2 → bs1 = bs2.
Proof.
  intros Hbs1 Hbs2. unfold base_val_of_bits. rewrite !resize_all_alt by done.
  intros; repeat case_match; simplify_equality.
  * erewrite (mapM_fmap_Some_inv maybe_BBit BBit _ bs1),
      (mapM_fmap_Some_inv maybe_BBit BBit _ bs2) by
      (by eauto; intros ? [] ?; simplify_equality).
    f_equal. by apply (of_bits_inj uchar);
      erewrite <-?bit_size_of_int, <-?mapM_length by eauto.
  * rewrite (proj2 (replicate_as_Forall BIndet (length bs1) bs1)),
      (proj2 (replicate_as_Forall BIndet (length bs2) bs2)) by done. congruence.
  * done.
Qed.

Lemma base_val_of_bits_trans m τ bs1 bs2 bs3 :
  base_type_valid get_env τ →
  bs1 ⊑@{m}* bs2 → bs2 ⊑@{m}* bs3 →
  base_val_of_bits τ bs1 = base_val_of_bits τ bs3 →
  base_val_of_bits τ bs2 = base_val_of_bits τ bs3.
Proof.
  intros ?. revert bs1 bs2 bs3. cut (∀ bs1 bs2 bs3,
    length bs1 = bit_size_of τ → length bs2 = bit_size_of τ →
    length bs3 = bit_size_of τ → bs1 ⊑@{m}* bs2 → bs2 ⊑@{m}* bs3 →
    base_val_of_bits τ bs1 = base_val_of_bits τ bs3 →
    base_val_of_bits τ bs2 = base_val_of_bits τ bs3).
  { intros help bs1 bs2 bs3 ??. rewrite
      <-(base_val_of_bits_resize τ bs1 (bit_size_of τ)),
      <-(base_val_of_bits_resize τ bs2 (bit_size_of τ)),
      <-(base_val_of_bits_resize τ bs3 (bit_size_of τ)) by done.
    apply help; rewrite ?resize_length; auto using
      Forall_resize, BIndet_valid, Forall2_resize. }
  intros bs1 bs2 bs3 ????? Hbs13. destruct (decide (τ = uchar)); subst.
  { apply base_val_of_bits_char_inj in Hbs13; subst; auto.
    by rewrite (anti_symmetric (⊑@{m}*) bs2 bs3). }
  destruct (bits_le_eq_or_indet m bs2 bs3); subst; auto.
  rewrite <-Hbs13, !(base_val_of_bits_indet m); eauto using bits_le_indet.
Qed.

Lemma base_val_of_bits_masked m τ bs1 bs2 bs3 :
  base_type_valid get_env τ →
  bs1 ⊑@{m}* bs2 → m ⊢* valid bs3 →
  length bs2 = length bs3 → bit_size_of τ ≤ length bs2 →
  base_val_of_bits τ bs2 = base_val_of_bits τ bs3 →
  base_val_of_bits τ (mask_bits bs1 bs3) = base_val_of_bits τ bs1.
Proof.
  intros ?. revert bs1 bs2 bs3. cut (∀ bs1 bs2 bs3,
    bs1 ⊑@{m}* bs2 → m ⊢* valid bs3 → length bs1 = bit_size_of τ →
    length bs2 = bit_size_of τ → length bs3 = bit_size_of τ →
    base_val_of_bits τ bs2 = base_val_of_bits τ bs3 →
    base_val_of_bits τ (mask_bits bs1 bs3) = base_val_of_bits τ bs1).
  { intros help bs1 bs2 ?????.
    assert (length bs1 = length bs2) by eauto using Forall2_length.
    rewrite <-(base_val_of_bits_resize τ (mask_bits _ _) (bit_size_of τ)),
      <-(base_val_of_bits_resize τ bs1 (bit_size_of τ)),
      <-(base_val_of_bits_resize τ bs2 (bit_size_of τ)),
      <-(base_val_of_bits_resize τ bs3 (bit_size_of τ)) by done.
    rewrite !resize_le, mask_bits_take by (erewrite ?mask_bits_length; lia).
    apply help; rewrite ?take_length_le by lia;
      auto using Forall2_take, Forall_take, BIndet_valid, BIndet_le. }
  intros bs1 bs2 bs3 Hbs12 ???? Hbs23. destruct (decide (τ = uchar)); subst.
  { apply base_val_of_bits_char_inj in Hbs23; subst; auto.
    by erewrite mask_bits_ge by eauto. }
  destruct (decide (BIndet ∈ bs1)) as [?|Hbs1].
  * rewrite (base_val_of_bits_indet m τ bs1); auto.
    rewrite base_val_of_bits_indet;
      auto using mask_bits_indet, same_length_length_2 with congruence.
    by rewrite mask_bits_length.
  * pose proof (bits_le_no_indet _ _ _ Hbs12 Hbs1); subst.
    by rewrite mask_bits_no_indet by
      auto using same_length_length_2 with congruence.
Qed.

Lemma base_val_0_typed m τ : base_type_valid get_env τ → m ⊢ base_val_0 τ : τ.
Proof.
  destruct 1; simpl; constructor. by apply int_typed_small. by constructor.
Qed.
Lemma base_unop_ok_typed m op v τ σ :
  m ⊢ v : τ → base_unop_typed op τ σ →
  base_unop_ok op v → m ⊢ base_unop op v : σ.
Proof.
  unfold base_unop_ok, base_unop. intros Hvτ Hσ Hop.
  destruct Hσ; inversion Hvτ; simpl; simplify_equality; try done.
  constructor. by apply int_unop_ok_typed.
Qed.
Lemma base_binop_ok_typed m op v1 v2 τ1 τ2 σ :
  ⊢ valid m → m ⊢ v1 : τ1 → m ⊢ v2 : τ2 → base_binop_typed op τ1 τ2 σ →
  base_binop_ok m op v1 v2 → m ⊢ base_binop op v1 v2 : σ.
Proof.
  unfold base_binop_ok, base_binop. intros Hm Hv1τ Hv2τ Hσ Hop.
  destruct Hσ; inversion Hv1τ; inversion Hv2τ;
    simpl; simplify_equality; try done.
  * constructor. by apply int_binop_ok_typed.
  * constructor. by case_decide; apply int_typed_small.
  * constructor. by apply ptr_plus_ok_typed.
  * constructor. by apply ptr_plus_ok_typed.
  * constructor. by apply ptr_plus_ok_typed.
  * constructor. by apply ptr_plus_ok_typed.
  * constructor. eapply ptr_minus_ok_typed; eauto.
Qed.
Lemma base_cast_ok_typed m v τ σ :
  m ⊢ v : τ → base_cast_typed τ σ → base_cast_ok σ v → m ⊢ base_cast σ v : σ.
Proof.
  unfold base_cast_ok, base_cast. intros Hvτ Hσ Hok.
  destruct Hσ; inversion Hvτ; simpl; simplify_equality; try done.
  * constructor. by apply int_cast_ok_typed.
  * constructor. eapply ptr_cast_ok_typed; eauto using TVoid_ptr_valid.
  * constructor. eapply ptr_cast_ok_typed;
      eauto using TBase_ptr_valid, TInt_valid.
  * constructor. eapply ptr_cast_ok_typed; eauto.
  * constructor. eapply ptr_cast_ok_typed; eauto.
Qed.
End properties.
