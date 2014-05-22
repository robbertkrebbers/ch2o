(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_map.
Local Open Scope cbase_type_scope.

Inductive base_val (Ti : Set) : Set :=
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
  Context `{IntEnv Ti, PtrEnv Ti}.

  Record char_byte_valid (Γ : env Ti)
      (m : mem Ti) (bs : list (bit Ti)) : Prop := {
    char_byte_valid_indet : ¬Forall (BIndet =) bs;
    char_byte_valid_bit : ¬(∃ βs, bs = BBit <$> βs);
    char_byte_valid_bits_valid : ✓{Γ,m}* bs;
    char_byte_valid_bits : length bs = char_bits
  }.
  Global Instance char_byte_valid_dec Γ m bs :
    Decision (char_byte_valid Γ m bs).
  Proof.
   refine (cast_if (decide (¬Forall (BIndet =) bs ∧
     ¬(∃ βs, bs = BBit <$> βs) ∧ ✓{Γ,m}* bs ∧ length bs = char_bits)));
     abstract (constructor||intros[]; intuition).
  Defined.
  Inductive base_typed' (Γ : env Ti) (m : mem Ti) :
       base_val Ti → base_type Ti → Prop :=
    | VIndet_typed τb : ✓{Γ} τb → base_typed' Γ m (VIndet τb) τb
    | VInt_typed x τi : int_typed x τi → base_typed' Γ m (VInt τi x) (intT τi)
    | VPtr_typed p τ : (Γ,m) ⊢ p : τ → base_typed' Γ m (VPtr p) (τ.*)
    | VByte_typed bs :
       char_byte_valid Γ m bs → base_typed' Γ m (VByte bs) ucharT.
  Global Instance base_typed:
    Typed (env Ti * mem Ti) (base_type Ti) (base_val Ti) := curry base_typed'.
  Global Instance type_of_base_val: TypeOf (base_type Ti) (base_val Ti) := λ v,
    match v with
    | VIndet τb => τb
    | VInt τi _ => intT τi
    | VPtr p => type_of p.*
    | VByte _ => ucharT
    end.
  Global Instance base_type_check:
    TypeCheck (env Ti * mem Ti) (base_type Ti) (base_val Ti) := λ Γm v,
    match v with
    | VIndet τb => guard (✓{Γm.1} τb); Some τb
    | VInt τi x => guard (int_typed x τi); Some (intT τi)
    | VPtr p => TPtr <$> type_check Γm p
    | VByte bs => guard (char_byte_valid (Γm.1) (Γm.2) bs); Some ucharT
    end.
  Global Instance base_val_freeze : Freeze (base_val Ti) := λ β v,
    match v with
    | VIndet τb => VIndet τb
    | VInt τi x => VInt τi x
    | VPtr p => VPtr (freeze β p)
    | VByte b => VByte b
    end.

  Definition base_val_flatten (Γ : env Ti) (v : base_val Ti) : list (bit Ti) :=
    match v with
    | VIndet τb => replicate (bit_size_of Γ τb) BIndet
    | VInt τi x => BBit <$> int_to_bits τi x
    | VPtr p => BPtr <$> ptr_to_bits Γ p
    | VByte bs => bs
    end.
  Definition base_val_unflatten (Γ : env Ti)
      (τb : base_type Ti) (bs : list (bit Ti)) : base_val Ti :=
    match τb with
    | intT τi =>
       match mapM maybe_BBit bs with
       | Some βs => VInt τi (int_of_bits τi βs)
       | None =>
          if decide (τi = ucharT%IT ∧ ¬Forall (BIndet =) bs)
          then VByte bs else VIndet τb
       end
    | τ.* => default (VIndet τb) (mapM maybe_BPtr bs ≫= ptr_of_bits Γ τ) VPtr
    end.

  Inductive base_val_refine' (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : mem Ti) :
        base_val Ti → base_val Ti → base_type Ti → Prop :=
    | VIndet_refine' τb vb :
       (Γ,m2) ⊢ vb : τb → base_val_refine' Γ f m1 m2 (VIndet τb) vb τb
    | VInt_refine' x τi :
       int_typed x τi →
       base_val_refine' Γ f m1 m2 (VInt τi x) (VInt τi x) (intT τi)
    | VPtr_refine' p1 p2 σ :
       p1 ⊑{Γ,f@m1↦m2} p2 : σ →
       base_val_refine' Γ f m1 m2 (VPtr p1) (VPtr p2) (σ.*)
    | VByte_refine' bs1 bs2 :
       bs1 ⊑{Γ,f@m1↦m2}* bs2 →
       char_byte_valid Γ m1 bs1 → char_byte_valid Γ m2 bs2 →
       base_val_refine' Γ f m1 m2 (VByte bs1) (VByte bs2) ucharT
    | VByte_Vint_refine' bs1 x2 :
       bs1 ⊑{Γ,f@m1↦m2}* BBit <$> int_to_bits ucharT x2 →
       char_byte_valid Γ m1 bs1 → int_typed x2 ucharT →
       base_val_refine' Γ f m1 m2 (VByte bs1) (VInt ucharT x2) ucharT.
  Global Instance base_val_refine:
    RefineT Ti (mem Ti) (base_val Ti) (base_type Ti) := base_val_refine'.

  Definition base_val_0 (τb : base_type Ti) : base_val Ti :=
    match τb with intT τi => VInt τi 0 | τ.* => VPtr (NULL τ) end.
  Inductive base_val_unop_typed : unop → base_type Ti → base_type Ti → Prop :=
    | unop_TInt_typed op τi : base_val_unop_typed op (intT τi) (intT τi).
  Definition base_val_unop_ok (op : unop) (vb : base_val Ti) : Prop :=
    match vb with VInt τ x => int_unop_ok τ op x | _ => False end.
  Global Arguments base_val_unop_ok !_ !_ /.
  Definition base_val_unop (op : unop) (vb : base_val Ti) : base_val Ti :=
    match vb with
    | VInt τi x => VInt τi (int_unop τi op x) | _ => VIndet (type_of vb)
    end.
  Global Arguments base_val_unop !_ !_ /.

  Inductive base_val_binop_typed :
        binop → base_type Ti → base_type Ti → base_type Ti → Prop :=
    | binop_TInt_TInt_typed op τi:
       base_val_binop_typed op (intT τi) (intT τi) (intT τi)
    | CompOp_TPtr_TPtr_typed c τ :
       base_val_binop_typed (CompOp c) (τ.*) (τ.*) sptrT
    | PlusOp_TPtr_TInt_typed τ σ :
       base_val_binop_typed PlusOp (τ.*) (intT σ) (τ.*)
    | PlusOp_VInt_TPtr_typed τ σ :
       base_val_binop_typed PlusOp (intT σ) (τ.*) (τ.*)
    | MinusOp_TPtr_TInt_typed τ σi :
       base_val_binop_typed MinusOp (τ.*) (intT σi) (τ.*)
    | MinusOp_TInt_TPtr_typed τ σi :
       base_val_binop_typed MinusOp (intT σi) (τ.*) (τ.*)
    | MinusOp_TPtr_TPtr_typed τ  :
       base_val_binop_typed MinusOp (τ.*) (τ.*) sptrT.
  Definition base_val_binop_ok (Γ : env Ti) (m : mem Ti)
      (op : binop) (vb1 vb2 : base_val Ti) : Prop :=
    match vb1, vb2, op with
    | VInt τi x1, VInt _ x2, _ => int_binop_ok τi op x1 x2
    | VPtr p1, VPtr p2, CompOp c => ptr_minus_ok m p1 p2
    | VPtr p, VInt _ x, PlusOp => ptr_plus_ok Γ m x p
    | VInt _ x, VPtr p, PlusOp => ptr_plus_ok Γ m x p
    | VPtr p, VInt _ x, MinusOp => ptr_plus_ok Γ m (-x) p
    | VInt _ x, VPtr p, MinusOp => ptr_plus_ok Γ m (-x) p
    | VPtr p1, VPtr p2, MinusOp => ptr_minus_ok m p1 p2
    | _, _, _ => False
    end.
  Global Arguments base_val_binop_ok _ _ !_ !_ !_ /.
  Definition base_val_binop (Γ : env Ti)
      (op : binop) (v1 v2 : base_val Ti) : base_val Ti :=
    match v1, v2, op with
    | VInt τ x1, VInt _ x2, _ => VInt τ (int_binop τ op x1 x2)
    | VPtr p1, VPtr p2, CompOp c =>
       let i := ptr_minus Γ p1 p2 in
       VInt sptrT (Z_of_sumbool (decide_rel (Z_comp c) i 0))
    | VPtr p, VInt _ i, PlusOp => VPtr (ptr_plus Γ i p)
    | VInt _ i, VPtr p, PlusOp => VPtr (ptr_plus Γ i p)
    | VPtr p, VInt _ i, MinusOp => VPtr (ptr_plus Γ (-i) p)
    | VInt _ i, VPtr p, MinusOp => VPtr (ptr_plus Γ (-i) p)
    | VPtr p1, VPtr p2, MinusOp => VInt sptrT (ptr_minus Γ p1 p2)
    | _, _, _ => VIndet (type_of v1)
    end.
  Global Arguments base_val_binop _ !_ !_ !_ /.

  Inductive base_val_cast_typed (Γ : env Ti) :
       base_type Ti → base_type Ti → Prop :=
    | TInt_cast_typed τi1 τi2 : base_val_cast_typed Γ (intT τi1) (intT τi2)
    | TPtr_to_void_cast_typed τ : base_val_cast_typed Γ (τ.*) (voidT.*)
    | TPtr_to_uchar_cast_typed τ : base_val_cast_typed Γ (τ.*) (ucharT.*)
    | TPtr_of_void_cast_typed τ :
       ptr_type_valid Γ τ → base_val_cast_typed Γ (voidT.*) (τ.*)
    | TPtr_of_uchar_cast_typed τ :
       ptr_type_valid Γ τ → base_val_cast_typed Γ (ucharT.*) (τ.*).
  Definition base_val_cast_ok (Γ : env Ti)
      (τb : base_type Ti) (vb : base_val Ti) : Prop :=
    match vb, τb with
    | VInt _ x, intT τi => int_cast_ok τi x
    | VPtr p, τ.* => ptr_cast_ok Γ τ p
    | _ , _ => False
    end.
  Global Arguments base_val_cast_ok _ !_ !_ /.
  Definition base_val_cast (τb : base_type Ti)
      (vb : base_val Ti) : base_val Ti :=
    match vb, τb with
    | VInt _ x, intT τi => VInt τi (int_cast τi x)
    | VPtr p, τ.* => VPtr (ptr_cast τ p)
    | _ , _ => VIndet (type_of vb)
    end.
  Global Arguments base_val_cast !_ !_ /.
End operations.

Arguments base_val_unflatten _ _ _ _ _ _ : simpl never.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types m : mem Ti.
Implicit Types τb : base_type Ti.
Implicit Types vb : base_val Ti.
Implicit Types bs : list (bit Ti).
Implicit Types βs : list bool.

Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Hint Extern 0 (_ ⊑* _) => reflexivity.

(** ** General properties of the typing judgment *)
Lemma base_typed_type_valid Γ m v τb : ✓ Γ → (Γ,m) ⊢ v : τb → ✓{Γ} τb.
Proof. destruct 2; try econstructor; eauto using ptr_typed_type_valid. Qed.
Global Instance: TypeOfSpec (env Ti * mem Ti) (base_type Ti) (base_val Ti).
Proof.
  intros [??]. destruct 1; f_equal'; auto. eapply type_of_correct; eauto.
Qed.
Global Instance:
  TypeCheckSpec (env Ti * mem Ti) (base_type Ti) (base_val Ti) (λ _, True).
Proof.
  intros [Γ mm] vb τb _. split.
  * destruct vb; intros; simplify_option_equality;
      constructor; auto; eapply type_check_sound; eauto.
  * by destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma char_byte_valid_weaken Γ1 Γ2 m1 m2 bs :
  ✓ Γ1 → char_byte_valid Γ1 m1 bs → Γ1 ⊆ Γ2 →
  (∀ o σ, type_of_index m1 o = Some σ → type_of_index m2 o = Some σ) →
  char_byte_valid Γ2 m2 bs.
Proof. destruct 2; constructor; eauto using Forall_impl, bit_valid_weaken. Qed.
Lemma base_typed_weaken Γ1 Γ2 m1 m2 vb τb :
  ✓ Γ1 → (Γ1,m1) ⊢ vb : τb → Γ1 ⊆ Γ2 →
  (∀ o σ, type_of_index m1 o = Some σ → type_of_index m2 o = Some σ) →
  (Γ2,m2) ⊢ vb : τb.
Proof.
  destruct 2; econstructor; eauto using ptr_typed_weaken,
    char_byte_valid_weaken, base_type_valid_weaken.
Qed.
Lemma base_val_frozen_int Γ m v τi : (Γ,m) ⊢ v : intT τi → frozen v.
Proof. inversion 1; constructor. Qed.
Lemma base_val_freeze_freeze β1 β2 vb : freeze β1 (freeze β2 vb) = freeze β1 vb.
Proof. destruct vb; f_equal'; auto using ptr_freeze_freeze. Qed.
Lemma base_val_freeze_type_of β vb : type_of (freeze β vb) = type_of vb.
Proof. by destruct vb; simpl; rewrite ?ptr_freeze_type_of. Qed.
Lemma base_typed_freeze Γ m β vb τb :
  (Γ,m) ⊢ freeze β vb : τb ↔ (Γ,m) ⊢ vb : τb.
Proof.
  split.
  * destruct vb; inversion 1; constructor; auto.
    by apply (ptr_typed_freeze _ _ β).
  * destruct 1; constructor; auto. by apply ptr_typed_freeze.
Qed.
Lemma base_typed_int_frozen Γ m vb τi : (Γ,m) ⊢ vb : intT τi → frozen vb.
Proof. inversion_clear 1; constructor. Qed.

(** ** Properties of the [base_val_flatten] function *)
Lemma base_val_flatten_valid Γ m vb τb :
  (Γ,m) ⊢ vb : τb → ✓{Γ,m}* (base_val_flatten Γ vb).
Proof.
  destruct 1; simpl.
  * apply Forall_replicate, BIndet_valid.
  * apply Forall_fmap, Forall_true. constructor.
  * apply Forall_fmap; eapply (Forall_impl (✓{Γ,m}));
      eauto using ptr_to_bits_valid, BPtr_valid.
  * eauto using char_byte_valid_bits_valid.
Qed.
Lemma base_val_flatten_weaken Γ1 Γ2 m τb vb :
  ✓ Γ1 → (Γ1,m) ⊢ vb : τb → Γ1 ⊆ Γ2 →
  base_val_flatten Γ1 vb = base_val_flatten Γ2 vb.
Proof.
  by destruct 2; intros; simpl; erewrite ?ptr_to_bits_weaken,
    ?bit_size_of_weaken by eauto using TBase_valid.
Qed.
Lemma base_val_flatten_freeze Γ β vb :
  base_val_flatten Γ (freeze β vb) = base_val_flatten Γ vb.
Proof. by destruct vb; simpl; rewrite ?ptr_to_bits_freeze. Qed.
Lemma base_val_flatten_length Γ m vb τb :
  (Γ,m) ⊢ vb : τb → length (base_val_flatten Γ vb) = bit_size_of Γ τb.
Proof.
  destruct 1; simplify_equality'.
  * by rewrite replicate_length.
  * by rewrite fmap_length, bit_size_of_int, int_to_bits_length.
  * by erewrite fmap_length, ptr_to_bits_length_alt, type_of_correct by eauto.
  * by erewrite bit_size_of_int, int_bits_char, char_byte_valid_bits by eauto.
Qed.

(** ** Properties of the [base_val_unflatten] function *)
Inductive base_val_unflatten_view Γ :
     base_type Ti → list (bit Ti) → base_val Ti → Prop :=
  | base_val_of_int τi βs :
     length βs = int_bits τi → base_val_unflatten_view Γ (intT τi)
       (BBit <$> βs) (VInt τi (int_of_bits τi βs))
  | base_val_of_ptr τ p pbs :
     ptr_of_bits Γ τ pbs = Some p →
     base_val_unflatten_view Γ (τ.*) (BPtr <$> pbs) (VPtr p)
  | base_val_of_byte bs :
     length bs = char_bits → ¬Forall (BIndet =) bs →
     ¬(∃ βs, bs = BBit <$> βs) →
     base_val_unflatten_view Γ ucharT bs (VByte bs)
  | base_val_of_byte_indet bs :
     length bs = char_bits → Forall (BIndet =) bs →
     base_val_unflatten_view Γ ucharT bs (VIndet ucharT)
  | base_val_of_int_indet τi bs :
     τi ≠ ucharT%IT →
     length bs = int_bits τi → ¬(∃ βs, bs = BBit <$> βs) →
     base_val_unflatten_view Γ (intT τi) bs (VIndet (intT τi))
  | base_val_of_ptr_indet_1 τ pbs :
     length pbs = bit_size_of Γ (τ.*) → ptr_of_bits Γ τ pbs = None →
     base_val_unflatten_view Γ (τ.*) (BPtr <$> pbs) (VIndet (τ.*))
  | base_val_of_ptr_indet_2 τ bs :
     length bs = bit_size_of Γ (τ.*) → ¬(∃ pbs, bs = BPtr <$> pbs) →
     base_val_unflatten_view Γ (τ.*) bs (VIndet (τ.*)).
Lemma base_val_unflatten_spec Γ τb bs :
  length bs = bit_size_of Γ τb →
  base_val_unflatten_view Γ τb bs (base_val_unflatten Γ τb bs).
Proof.
  intros Hbs. unfold base_val_unflatten. destruct τb as [τi|τ].
  * rewrite bit_size_of_int in Hbs.
    destruct (mapM maybe_BBit bs) as [βs|] eqn:Hβs.
    { rewrite maybe_BBits_spec in Hβs; subst. rewrite fmap_length in Hbs.
      by constructor. }
    assert (¬∃ βs, bs = BBit <$> βs).
    { setoid_rewrite <-maybe_BBits_spec. intros [??]; simplify_equality. }
    destruct (decide _) as [[-> ?]|Hτbs].
    { rewrite int_bits_char in Hbs. by constructor. }
    destruct (decide (τi = ucharT%IT)) as [->|?].
    { rewrite int_bits_char in Hbs.
      constructor; auto. apply dec_stable; naive_solver. }
    by constructor.
  * destruct (mapM maybe_BPtr bs) as [pbs|] eqn:Hpbs; simpl.
    { rewrite maybe_BPtrs_spec in Hpbs; subst. rewrite fmap_length in Hbs.
      by destruct (ptr_of_bits Γ τ pbs) as [p|] eqn:?; constructor. }
    constructor; auto.
    setoid_rewrite <-maybe_BPtrs_spec. intros [??]; simplify_equality.
Qed.
Lemma base_val_unflatten_weaken Γ1 Γ2 τb bs :
  ✓ Γ1 → ✓{Γ1} τb → Γ1 ⊆ Γ2 →
  base_val_unflatten Γ1 τb bs = base_val_unflatten Γ2 τb bs.
Proof.
  intros. unfold base_val_unflatten, default.
  repeat match goal with
    | _ => case_match
    | H : context [ptr_of_bits _ _ _] |- _ =>
      rewrite <-(ptr_of_bits_weaken Γ1 Γ2) in H by eauto using TPtr_valid_inv
    | _ => simplify_option_equality
    end; auto.
Qed.
Lemma base_val_unflatten_int Γ τi βs :
  length βs = int_bits τi →
  base_val_unflatten Γ (intT τi) (BBit <$> βs) = VInt τi (int_of_bits τi βs).
Proof. intros. unfold base_val_unflatten. by rewrite mapM_fmap_Some by done. Qed.
Lemma base_val_unflatten_ptr Γ τ pbs p :
  ptr_of_bits Γ τ pbs = Some p →
  base_val_unflatten Γ (τ.*) (BPtr <$> pbs) = VPtr p.
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ (τ.*) (BPtr <$> pbs));
    simplify_equality'; auto.
  * by erewrite fmap_length, ptr_of_bits_length by eauto.
  * naive_solver (apply Forall_fmap, Forall_true; simpl; eauto).
Qed.
Lemma base_val_unflatten_byte Γ bs :
  ¬Forall (BIndet =) bs → ¬(∃ βs, bs = BBit <$> βs) →
  length bs = char_bits → base_val_unflatten Γ ucharT bs = VByte bs.
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ ucharT bs);
    simplify_equality'; rewrite ?bit_size_of_int, ?int_bits_char; naive_solver.
Qed.
Lemma base_val_unflatten_indet Γ τb bs :
  Forall (BIndet =) bs → length bs = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs = VIndet τb.
Proof.
  intros. assert (∀ τi βs,
    Forall (@BIndet Ti =) (BBit <$> βs) → length βs ≠ int_bits τi).
  { intros τi βs ??. pose proof (int_bits_pos τi).
    destruct βs; decompose_Forall_hyps'; lia. }
  assert (∀ τ pbs p,
    Forall (BIndet =) (BPtr <$> pbs) → ptr_of_bits Γ τ pbs ≠ Some p).
  { intros τ pbs p ??. assert (length pbs ≠ 0).
    { erewrite ptr_of_bits_length by eauto. by apply bit_size_of_base_ne_0. }
    destruct pbs; decompose_Forall_hyps'; lia. }
  feed inversion (base_val_unflatten_spec Γ τb bs); naive_solver.
Qed.
Lemma base_val_unflatten_int_indet Γ τi bs :
  τi ≠ ucharT%IT → length bs = int_bits τi → ¬(∃ βs, bs = BBit <$> βs) →
  base_val_unflatten Γ (intT τi) bs = VIndet (intT τi).
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ (intT τi) bs);
    simplify_equality'; rewrite ?bit_size_of_int; naive_solver.
Qed.
Lemma base_val_unflatten_ptr_indet_1 Γ τ pbs :
  length pbs = bit_size_of Γ (τ.*) → ptr_of_bits Γ τ pbs = None →
  base_val_unflatten Γ (τ.*) (BPtr <$> pbs) = VIndet (τ.*).
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ (τ.*) (BPtr <$> pbs));
    simplify_equality'; rewrite ?fmap_length; naive_solver.
Qed.
Lemma base_val_unflatten_ptr_indet_2 Γ τ bs :
  length bs = bit_size_of Γ (τ.*) → ¬(∃ pbs, bs = BPtr <$> pbs) →
  base_val_unflatten Γ (τ.*) bs = VIndet (τ.*).
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ (τ.*) bs);
    simplify_equality'; naive_solver.
Qed.
Lemma base_val_unflatten_indet_elem_of Γ τb bs :
  τb ≠ ucharT → length bs = bit_size_of Γ τb →
  BIndet ∈ bs → base_val_unflatten Γ τb bs = VIndet τb.
Proof.
  intros ??. feed destruct (base_val_unflatten_spec Γ τb bs);
    rewrite ?elem_of_list_fmap; naive_solver.
Qed.

Lemma base_val_unflatten_typed Γ m τb bs :
  ✓{Γ} τb → ✓{Γ,m}* bs → length bs = bit_size_of Γ τb →
  (Γ,m) ⊢ base_val_unflatten Γ τb bs : τb.
Proof.
  intros. feed destruct (base_val_unflatten_spec Γ τb bs);
    auto; constructor; auto.
  * by apply int_of_bits_typed.
  * eapply ptr_of_bits_typed; eauto using BPtrs_valid_inv.
  * by constructor.
Qed.
Lemma base_val_unflatten_type_of Γ τb bs :
  type_of (base_val_unflatten Γ τb bs) = τb.
Proof.
  unfold base_val_unflatten, default.
  destruct τb; repeat (simplify_option_equality || case_match || intuition).
  f_equal; eauto using ptr_of_bits_type_of.
Qed.
Lemma base_val_unflatten_flatten Γ m vb τb :
  (Γ,m) ⊢ vb : τb →
  base_val_unflatten Γ τb (base_val_flatten Γ vb) = freeze true vb.
Proof.
  destruct 1 as [τb|x|p τ|bs []]; simpl.
  * by rewrite base_val_unflatten_indet
      by auto using Forall_replicate_eq, replicate_length.
  * by rewrite base_val_unflatten_int, int_of_to_bits
      by auto using int_to_bits_length.
  * by erewrite base_val_unflatten_ptr by eauto using ptr_of_to_bits_typed.
  * by rewrite base_val_unflatten_byte by done.
Qed.
Lemma base_val_unflatten_frozen Γ m τb bs :
  ✓{Γ,m}* bs → frozen (base_val_unflatten Γ τb bs).
Proof.
  intros. unfold base_val_unflatten, default, frozen.
  destruct τb; repeat (simplify_option_equality || case_match); f_equal'.
  efeed pose proof (λ bs pbs, proj1 (maybe_BPtrs_spec bs pbs)); eauto.
  subst. eapply ptr_of_bits_frozen; eauto using BPtrs_valid_inv.
Qed.
Lemma base_val_flatten_inj Γ m β vb1 vb2 τb :
  (Γ,m) ⊢ vb1 : τb → (Γ,m) ⊢ vb2 : τb →
  base_val_flatten Γ vb1 = base_val_flatten Γ vb2 → freeze β vb1 = freeze β vb2.
Proof.
  intros ?? Hv. by rewrite <-(base_val_freeze_freeze _ true vb1),
    <-(base_val_freeze_freeze _ true vb2),
    <-(base_val_unflatten_flatten Γ m vb1 τb),
    <-(base_val_unflatten_flatten Γ m vb2 τb), Hv by done.
Qed.
Lemma base_val_flatten_unflatten Γ m τb bs :
  ✓{Γ,m}* bs → length bs = bit_size_of Γ τb →
  base_val_flatten Γ (base_val_unflatten Γ τb bs) ⊑* bs.
Proof.
  intros. cut (base_val_flatten Γ (base_val_unflatten Γ τb bs) = bs
    ∨ base_val_unflatten Γ τb bs = VIndet τb).
  { intros [->| ->]; simpl; eauto using Forall2_replicate_l,
      Forall_true, BIndet_weak_refine, BIndet_valid. }
  feed destruct (base_val_unflatten_spec Γ τb bs); simpl; auto.
  * left. by rewrite int_to_of_bits.
  * left. by erewrite ptr_to_of_bits by eauto using BPtrs_valid_inv.
Qed.
Lemma base_val_flatten_unflatten_char Γ bs :
  length bs = bit_size_of Γ ucharT →
  base_val_flatten Γ (base_val_unflatten Γ ucharT bs) = bs.
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ ucharT bs);
    simplify_equality'; auto using replicate_as_Forall_2.
  by rewrite int_to_of_bits by done.
Qed.
Lemma base_val_unflatten_char_inj Γ bs1 bs2 :
  length bs1 = bit_size_of Γ ucharT → length bs2 = bit_size_of Γ ucharT →
  base_val_unflatten Γ ucharT bs1 = base_val_unflatten Γ ucharT bs2 → bs1 = bs2.
Proof.
  intros ?? Hbs. by rewrite <-(base_val_flatten_unflatten_char Γ bs1),
    <-(base_val_flatten_unflatten_char Γ bs2), Hbs.
Qed.
Lemma base_val_unflatten_between Γ τb bs1 bs2 bs3 :
  ✓{Γ} τb → bs1 ⊑* bs2 → bs2 ⊑* bs3 → length bs1 = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs1 = base_val_unflatten Γ τb bs3 →
  base_val_unflatten Γ τb bs2 = base_val_unflatten Γ τb bs3.
Proof.
  intros ???? Hbs13. destruct (decide (τb = ucharT)) as [->|].
  { apply base_val_unflatten_char_inj in Hbs13; subst;
      eauto using Forall2_length_l.
    by rewrite (anti_symmetric (Forall2 bit_weak_refine) bs2 bs3). }
  destruct (bits_subseteq_eq bs2 bs3) as [->|]; auto.
  rewrite <-Hbs13, !(base_val_unflatten_indet_elem_of Γ);
    eauto using bits_subseteq_indet, Forall2_length_l.
Qed.

(** ** Refinements *)
Lemma base_val_flatten_refine Γ f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb →
  base_val_flatten Γ vb1 ⊑{Γ,f@m1↦m2}* base_val_flatten Γ vb2.
Proof.
  destruct 1; simpl.
  * apply Forall2_replicate_l; eauto using base_val_flatten_length,
      Forall_impl, base_val_flatten_valid, BIndet_refine.
  * by apply BBits_refine.
  * eapply BPtrs_refine, ptr_to_bits_refine; eauto.
  * eauto using BIndet_refine.
  * done.
Qed.
Lemma base_val_refine_typed_l Γ f m1 m2 vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,f@m1↦m2} vb2 : τb → (Γ,m1) ⊢ vb1 : τb.
Proof.
  destruct 2; constructor;eauto using ptr_refine_typed_l, base_typed_type_valid.
Qed.
Lemma base_val_refine_typed_r Γ f m1 m2 vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,f@m1↦m2} vb2 : τb → (Γ,m2) ⊢ vb2 : τb.
Proof. destruct 2; try constructor; eauto using ptr_refine_typed_r. Qed.
Lemma base_val_refine_type_of_l Γ f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb → type_of vb1 = τb.
Proof. destruct 1; f_equal'; eauto using ptr_refine_type_of_l. Qed.
Lemma base_val_refine_type_of_r Γ f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb → type_of vb2 = τb.
Proof.
  destruct 1; f_equal'; eauto using ptr_refine_type_of_r, type_of_correct.
Qed.
Lemma base_val_refine_id Γ m vb τb : (Γ,m) ⊢ vb : τb → vb ⊑{Γ@m} vb : τb.
Proof.
  destruct 1; constructor; eauto using ptr_refine_id,
    bits_refine_id, char_byte_valid_bits_valid; constructor; eauto.
Qed.
Lemma base_val_refine_compose Γ f g m1 m2 m3 vb1 vb2 vb3 τb :
  ✓ Γ → vb1 ⊑{Γ,f@m1↦m2} vb2 : τb → vb2 ⊑{Γ,g@m2↦m3} vb3 : τb →
  vb1 ⊑{Γ,f ◎ g@m1↦m3} vb3 : τb.
Proof.
  destruct 2; inversion 1; simplify_equality; constructor;
    eauto using base_val_refine_typed_r, ptr_refine_compose,
    bits_refine_compose, BBits_refine.
Qed.
Lemma base_val_unflatten_refine Γ f m1 m2 τb bs1 bs2 :
  ✓ Γ → ✓{Γ} τb → bs1 ⊑{Γ,f@m1↦m2}* bs2 → length bs1 = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs1 ⊑{Γ,f@m1↦m2} base_val_unflatten Γ τb bs2 : τb.
Proof.
  intros ?? Hbs Hbs1. assert (length bs2 = bit_size_of Γ τb) as Hbs2.
  { eauto using Forall2_length_l. }
  feed destruct (base_val_unflatten_spec Γ τb bs1)
    as [τi βs1|τ p1 pbs1|bs1|bs1|τi bs1|τ pbs1|τ bs1]; auto.
  * rewrite (BBits_refine_inv_l Γ f m1 m2 βs1 bs2),
      base_val_unflatten_int by done.
    constructor. by apply int_of_bits_typed.
  * destruct (BPtrs_refine_inv_l Γ f m1 m2 pbs1 bs2) as (pbs2&->&?); auto.
    destruct (ptr_of_bits_refine Γ f m1 m2 τ pbs1 pbs2 p1) as (p2&?&?); eauto.
    erewrite base_val_unflatten_ptr by eauto. by constructor.
  * destruct (decide (∃ βs, bs2 = BBit <$> βs)) as [[βs2 ->]|?].
    { rewrite fmap_length, bit_size_of_int in Hbs2.
      rewrite base_val_unflatten_int by done. constructor.
      + by rewrite int_to_of_bits by done.
      + constructor; eauto using bits_refine_valid_l.
      + by apply int_of_bits_typed. }
    assert (length bs2 = char_bits) by eauto using Forall2_length_l.
    rewrite base_val_unflatten_byte by eauto using BIndets_refine_r_inv.
    constructor; auto; constructor; eauto using bits_refine_valid_l,
      bits_refine_valid_r, BIndets_refine_r_inv.
  * destruct (decide (∃ βs, bs2 = BBit <$> βs)) as [[βs2 ->]|?].
    { rewrite fmap_length, bit_size_of_int in Hbs2.
      rewrite base_val_unflatten_int by done. do 2 constructor.
      by apply int_of_bits_typed. }
    destruct (decide (Forall (BIndet =) bs2)).
    { rewrite base_val_unflatten_indet by done. repeat constructor. }
    assert (length bs2 = char_bits) by eauto using Forall2_length_l.
    rewrite base_val_unflatten_byte by done.
    do 3 constructor; eauto using BIndets_refine_l_inv.
  * destruct (decide (∃ βs, bs2 = BBit <$> βs)) as [[βs2 ->]|?].
    { rewrite fmap_length, bit_size_of_int in Hbs2.
      rewrite base_val_unflatten_int by done. do 2 constructor.
      by apply int_of_bits_typed. }
    rewrite bit_size_of_int in Hbs2.
    rewrite base_val_unflatten_int_indet by done. repeat constructor.
  * destruct (BPtrs_refine_inv_l Γ f m1 m2 pbs1 bs2) as (pbs2&->&?); auto.
    destruct (ptr_of_bits Γ τ pbs2) as [p2|] eqn:?.
    { erewrite base_val_unflatten_ptr by eauto. do 2 constructor.
      eapply ptr_of_bits_typed; eauto using ptr_bits_refine_valid_r. }
    rewrite fmap_length in Hbs2.
    rewrite base_val_unflatten_ptr_indet_1 by done. by do 2 constructor.
  * destruct (decide (∃ pbs, bs2 = BPtr <$> pbs)) as [[pbs2 ->]|?].
    { destruct (ptr_of_bits Γ τ pbs2) as [p2|] eqn:?.
      { erewrite base_val_unflatten_ptr by eauto. do 2 constructor.
        eauto using ptr_of_bits_typed,
          ptr_of_bits_Exists_Forall_typed, BPtrs_refine_inv_r. }
      rewrite fmap_length in Hbs2.
      rewrite base_val_unflatten_ptr_indet_1 by done. by do 2 constructor. }
    rewrite base_val_unflatten_ptr_indet_2 by done. by do 2 constructor.
Qed.

(** ** Properties of unary/binary operations and casts *)
Lemma base_val_0_typed Γ m τb : ✓{Γ} τb → (Γ,m) ⊢ base_val_0 τb : τb.
Proof.
  destruct 1; simpl; constructor. by apply int_typed_small. by constructor.
Qed.
Lemma base_val_unop_ok_typed Γ m op vb τb σb :
  (Γ,m) ⊢ vb : τb → base_val_unop_typed op τb σb →
  base_val_unop_ok op vb → (Γ,m) ⊢ base_val_unop op vb : σb.
Proof.
  unfold base_val_unop_ok, base_val_unop. intros Hvτb Hσ Hop.
  destruct Hσ; inversion Hvτb; simplify_equality'; try done.
  constructor. by apply int_unop_ok_typed.
Qed.
Lemma base_binop_ok_typed Γ m op vb1 vb2 τb1 τb2 σb :
  ✓ Γ → (Γ,m) ⊢ vb1 : τb1 → (Γ,m) ⊢ vb2 : τb2 →
  base_val_binop_typed op τb1 τb2 σb →
  base_val_binop_ok Γ m op vb1 vb2 →
  (Γ,m) ⊢ base_val_binop Γ op vb1 vb2 : σb.
Proof.
  unfold base_val_binop_ok, base_val_binop. intros HΓ Hv1τb Hv2τb Hσ Hop.
  revert Hv1τb Hv2τb.
  destruct Hσ; inversion 1; inversion 1; simplify_equality'; try done.
  * constructor. by apply int_binop_ok_typed.
  * constructor. by case_decide; apply int_typed_small.
  * constructor. eapply ptr_plus_ok_typed; eauto.
  * constructor. eapply ptr_plus_ok_typed; eauto.
  * constructor. eapply ptr_plus_ok_typed; eauto.
  * constructor. eapply ptr_plus_ok_typed; eauto.
  * constructor. eapply ptr_minus_ok_typed; eauto.
Qed.
Lemma base_val_cast_ok_typed Γ m vb τb σb :
  (Γ,m) ⊢ vb : τb → base_val_cast_typed Γ τb σb →
  base_val_cast_ok Γ σb vb → (Γ,m) ⊢ base_val_cast σb vb : σb.
Proof.
  unfold base_val_cast_ok, base_val_cast. intros Hvτb Hσb Hok. revert Hvτb.
  destruct Hσb; inversion 1; simplify_equality'; try done.
  * constructor. by apply int_cast_ok_typed.
  * constructor. eapply ptr_cast_ok_typed; eauto using TVoid_ptr_valid.
  * constructor. eapply ptr_cast_ok_typed;
      eauto using TBase_ptr_valid, TInt_valid.
  * constructor. eapply ptr_cast_ok_typed; eauto.
  * constructor. eapply ptr_cast_ok_typed; eauto.
Qed.

Lemma base_val_unop_ok_refine Γ f m1 m2 op vb1 vb2 τb :
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb →
  base_val_unop_ok op vb1 → base_val_unop_ok op vb2.
Proof. by destruct op, 1. Qed.
Lemma base_val_unop_refine Γ f m1 m2 op vb1 vb2 τb σb :
  ✓ Γ → base_val_unop_typed op τb σb → base_val_unop_ok op vb1 →
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb →
  base_val_unop op vb1 ⊑{Γ,f@m1↦m2} base_val_unop op vb2 : σb.
Proof.
  intros ? Hvτb ? Hvb. assert ((Γ,m2) ⊢ base_val_unop op vb2 : σb) as Hvb2.
  { eauto using base_val_unop_ok_typed,
      base_val_refine_typed_r, base_val_unop_ok_refine. }
  destruct Hvτb; inversion Hvb; simplify_equality'; constructor;
    eauto using int_unop_ok_typed.
Qed.
Lemma base_val_binop_ok_refine Γ f m1 m2 op vb1 vb2 vb3 vb4 τb1 τb3 σb :
  ✓ Γ → m1 ⊑{Γ,f} m2 → base_val_binop_typed op τb1 τb3 σb →
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb1 → vb3 ⊑{Γ,f@m1↦m2} vb4 : τb3 →
  base_val_binop_ok Γ m1 op vb1 vb3 → base_val_binop_ok Γ m2 op vb2 vb4.
Proof.
  destruct 3; inversion 1; inversion 1; simplify_equality'; try done;
    eauto using ptr_plus_ok_refine, ptr_minus_ok_refine.
Qed.
Lemma base_val_binop_refine Γ f m1 m2 op vb1 vb2 vb3 vb4 τb1 τb3 σb :
  ✓ Γ → m1 ⊑{Γ,f} m2 → base_val_binop_typed op τb1 τb3 σb →
  base_val_binop_ok Γ m1 op vb1 vb3 →
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb1 → vb3 ⊑{Γ,f@m1↦m2} vb4 : τb3 →
  base_val_binop Γ op vb1 vb3 ⊑{Γ,f@m1↦m2} base_val_binop Γ op vb2 vb4 : σb.
Proof.
  destruct 3; inversion 2; inversion 1; simplify_equality'; try done;
    try constructor; eauto using ptr_plus_refine, int_binop_ok_typed;
    erewrite ptr_minus_refine by eauto; constructor.
  * apply int_typed_small; by case_decide.
  * eapply ptr_minus_ok_typed;
      eauto using ptr_refine_typed_l, ptr_refine_typed_r.
Qed.
Lemma base_val_cast_ok_refine Γ f m1 m2 vb1 vb2 τb σb :
  ✓ Γ → vb1 ⊑{Γ,f@m1↦m2} vb2 : τb →
  base_val_cast_ok Γ σb vb1 → base_val_cast_ok Γ σb vb2.
Proof. destruct σb, 2; simpl; try done; eauto using ptr_cast_ok_refine. Qed.
Lemma base_val_cast_refine Γ f m1 m2 vb1 vb2 τb σb :
  base_val_cast_typed Γ τb σb → base_val_cast_ok Γ σb vb1 →
  vb1 ⊑{Γ,f@m1↦m2} vb2 : τb →
  base_val_cast σb vb1 ⊑{Γ,f@m1↦m2} base_val_cast σb vb2 : σb.
Proof.
  destruct 1; inversion 2; simplify_equality'; try done; constructor;
    eauto using ptr_cast_refine, int_cast_ok_typed, ptr_cast_refine,
    TVoid_ptr_valid, TBase_ptr_valid, TInt_valid.
Qed.
End properties.
