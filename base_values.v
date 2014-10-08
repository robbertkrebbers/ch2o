(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export bits.
Local Open Scope cbase_type_scope.

Inductive base_val (Ti : Set) : Set :=
  | VIndet : base_type Ti → base_val Ti
  | VVoid : base_val Ti
  | VInt : int_type Ti → Z → base_val Ti
  | VPtr : ptr Ti → base_val Ti
  | VByte : list (bit Ti) → base_val Ti.
Arguments VIndet {_} _.
Arguments VVoid {_}.
Arguments VInt {_} _ _.
Arguments VPtr {_} _.
Arguments VByte {_} _.

Delimit Scope base_val_scope with B.
Bind Scope base_val_scope with base_val.
Open Scope base_val_scope.
Notation "'voidV'" := VVoid : base_val_scope.
Notation "'indetV' τ" := (VIndet τ) (at level 10) : base_val_scope.
Notation "'intV{' τi } x" := (VInt τi x)
  (at level 10, format "intV{ τi }  x") : base_val_scope.
Notation "'ptrV' p" := (VPtr p) (at level 10) : base_val_scope.
Notation "'byteV' bs" := (VByte bs) (at level 10) : base_val_scope.

Definition maybe_VInt {Ti} (vb : base_val Ti) : option (int_type Ti * Z) :=
  match vb with VInt τi x => Some (τi,x) | _ => None end.
Definition maybe_VPtr {Ti} (vb : base_val Ti) : option (ptr Ti) :=
  match vb with VPtr p => Some p | _ => None end.
Instance base_val_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (v1 v2 : base_val Ti) : Decision (v1 = v2).
Proof. solve_decision. Defined.

Section operations.
  Context `{Env Ti}.

  Record char_byte_valid (Γ : env Ti)
      (Γm : memenv Ti) (bs : list (bit Ti)) : Prop := {
    char_byte_valid_indet : ¬Forall (BIndet =) bs;
    char_byte_valid_bit : ¬(∃ βs, bs = BBit <$> βs);
    char_byte_valid_bits_valid : ✓{Γ,Γm}* bs;
    char_byte_valid_bits : length bs = char_bits
  }.
  Global Instance char_byte_valid_dec Γ Γm bs :
    Decision (char_byte_valid Γ Γm bs).
  Proof.
   refine (cast_if (decide (¬Forall (BIndet =) bs ∧
     ¬(∃ βs, bs = BBit <$> βs) ∧ ✓{Γ,Γm}* bs ∧ length bs = char_bits)));
     abstract (constructor||intros[]; intuition).
  Defined.
  Inductive base_typed' (Γ : env Ti) (Γm : memenv Ti) :
       base_val Ti → base_type Ti → Prop :=
    | VIndet_typed τb : ✓{Γ} τb → τb ≠ voidT → base_typed' Γ Γm (VIndet τb) τb
    | VVoid_typed : base_typed' Γ Γm VVoid voidT
    | VInt_typed x τi : int_typed x τi → base_typed' Γ Γm (VInt τi x) (intT τi)
    | VPtr_typed p τ : (Γ,Γm) ⊢ p : τ → base_typed' Γ Γm (VPtr p) (τ.*)
    | VByte_typed bs :
       char_byte_valid Γ Γm bs → base_typed' Γ Γm (VByte bs) ucharT.
  Global Instance base_typed: Typed (env Ti * memenv Ti)
    (base_type Ti) (base_val Ti) := curry base_typed'.
  Global Instance type_of_base_val: TypeOf (base_type Ti) (base_val Ti) := λ v,
    match v with
    | VIndet τb => τb
    | VVoid => voidT
    | VInt τi _ => intT τi
    | VPtr p => type_of p.*
    | VByte _ => ucharT
    end.
  Global Instance base_type_check:
    TypeCheck (env Ti * memenv Ti) (base_type Ti) (base_val Ti) := λ ΓΓm v,
    match v with
    | VIndet τb => guard (✓{ΓΓm.1} τb); guard (τb ≠ voidT); Some τb
    | VVoid => Some voidT
    | VInt τi x => guard (int_typed x τi); Some (intT τi)
    | VPtr p => TPtr <$> type_check ΓΓm p
    | VByte bs => guard (char_byte_valid (ΓΓm.1) (ΓΓm.2) bs); Some ucharT
    end.
  Global Instance base_val_freeze : Freeze (base_val Ti) := λ β v,
    match v with VPtr p => VPtr (freeze β p) | _ => v end.

  Definition base_val_flatten (Γ : env Ti) (v : base_val Ti) : list (bit Ti) :=
    match v with
    | VIndet τb => replicate (bit_size_of Γ τb) BIndet
    | VVoid => replicate (bit_size_of Γ voidT) BIndet
    | VInt τi x => BBit <$> int_to_bits τi x
    | VPtr p => BPtr <$> ptr_to_bits Γ p
    | VByte bs => bs
    end.
  Definition base_val_unflatten (Γ : env Ti)
      (τb : base_type Ti) (bs : list (bit Ti)) : base_val Ti :=
    match τb with
    | voidT => VVoid
    | intT τi =>
       match mapM maybe_BBit bs with
       | Some βs => VInt τi (int_of_bits τi βs)
       | None =>
          if decide (τi = ucharT%IT ∧ ¬Forall (BIndet =) bs)
          then VByte bs else VIndet τb
       end
    | τ.* => default (VIndet τb) (mapM maybe_BPtr bs ≫= ptr_of_bits Γ τ) VPtr
    end.

  Inductive base_val_refine' (Γ : env Ti)
        (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
        base_val Ti → base_val Ti → base_type Ti → Prop :=
    | VIndet_VIndet_refine' τb :
       ✓{Γ} τb → τb ≠ voidT →
       base_val_refine' Γ α f Γm1 Γm2 (VIndet τb) (VIndet τb) τb
    | VIndet_refine' τb vb :
       α → (Γ,Γm2) ⊢ vb : τb → τb ≠ voidT →
       base_val_refine' Γ α f Γm1 Γm2 (VIndet τb) vb τb
    | VVoid_refine' : base_val_refine' Γ α f Γm1 Γm2 VVoid VVoid voidT
    | VInt_refine' x τi :
       int_typed x τi →
       base_val_refine' Γ α f Γm1 Γm2 (VInt τi x) (VInt τi x) (intT τi)
    | VPtr_refine' p1 p2 σ :
       p1 ⊑{Γ,α,f@Γm1↦Γm2} p2 : σ →
       base_val_refine' Γ α f Γm1 Γm2 (VPtr p1) (VPtr p2) (σ.*)
    | VPtr_VIndet_refine p1 vb2 σ :
       α → (Γ,Γm1) ⊢ p1 : σ → ¬ptr_alive Γm1 p1 → (Γ,Γm2) ⊢ vb2 : σ.* →
       base_val_refine' Γ α f Γm1 Γm2 (VPtr p1) vb2 (σ.*)
    | VByte_refine' bs1 bs2 :
       bs1 ⊑{Γ,α,f@Γm1↦Γm2}* bs2 →
       char_byte_valid Γ Γm1 bs1 → char_byte_valid Γ Γm2 bs2 →
       base_val_refine' Γ α f Γm1 Γm2 (VByte bs1) (VByte bs2) ucharT
    | VByte_Vint_refine' bs1 x2 :
       α → bs1 ⊑{Γ,α,f@Γm1↦Γm2}* BBit <$> int_to_bits ucharT x2 →
       char_byte_valid Γ Γm1 bs1 → int_typed x2 ucharT →
       base_val_refine' Γ α f Γm1 Γm2 (VByte bs1) (VInt ucharT x2) ucharT
    | VByte_VIndet_refine' bs1 bs2 vb2 :
       α → bs1 ⊑{Γ,α,f@Γm1↦Γm2}* bs2 → char_byte_valid Γ Γm1 bs1 →
       Forall (BIndet =) bs2 → (Γ,Γm2) ⊢ vb2 : ucharT →
       base_val_refine' Γ α f Γm1 Γm2 (VByte bs1) vb2 ucharT.
  Global Instance base_val_refine:
    RefineT Ti (env Ti) (base_type Ti) (base_val Ti) := base_val_refine'.
End operations.

Arguments base_val_unflatten _ _ _ _ _ : simpl never.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types α : bool.
Implicit Types τb : base_type Ti.
Implicit Types vb : base_val Ti.
Implicit Types bs : list (bit Ti).
Implicit Types βs : list bool.

Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Hint Extern 0 (_ ⊑* _) => reflexivity.

(** ** General properties of the typing judgment *)
Lemma base_val_typed_type_valid Γ Γm v τb : ✓ Γ → (Γ,Γm) ⊢ v : τb → ✓{Γ} τb.
Proof. destruct 2; try econstructor; eauto using ptr_typed_type_valid. Qed.
Global Instance: TypeOfSpec (env Ti * memenv Ti) (base_type Ti) (base_val Ti).
Proof.
  intros [??]. destruct 1; f_equal'; auto. eapply type_of_correct; eauto.
Qed.
Global Instance:
  TypeCheckSpec (env Ti * memenv Ti) (base_type Ti) (base_val Ti) (λ _, True).
Proof.
  intros [Γ Γmm] vb τb _. split.
  * destruct vb; intros; simplify_option_equality;
      constructor; auto; eapply type_check_sound; eauto.
  * by destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma char_byte_valid_weaken Γ1 Γ2 Γm1 Γm2 bs :
  ✓ Γ1 → char_byte_valid Γ1 Γm1 bs → Γ1 ⊆ Γ2 → Γm1 ⇒ₘ Γm2 →
  char_byte_valid Γ2 Γm2 bs.
Proof. destruct 2; constructor; eauto using Forall_impl, bit_valid_weaken. Qed.
Lemma base_val_typed_weaken Γ1 Γ2 Γm1 Γm2 vb τb :
  ✓ Γ1 → (Γ1,Γm1) ⊢ vb : τb → Γ1 ⊆ Γ2 → Γm1 ⇒ₘ Γm2 → (Γ2,Γm2) ⊢ vb : τb.
Proof.
  destruct 2; econstructor; eauto using ptr_typed_weaken,
    char_byte_valid_weaken, base_type_valid_weaken.
Qed.
Lemma base_val_frozen_int Γ Γm v τi : (Γ,Γm) ⊢ v : intT τi → frozen v.
Proof. inversion 1; constructor. Qed.
Lemma base_val_freeze_freeze β1 β2 vb : freeze β1 (freeze β2 vb) = freeze β1 vb.
Proof. destruct vb; f_equal'; auto using ptr_freeze_freeze. Qed.
Lemma base_val_freeze_type_of β vb : type_of (freeze β vb) = type_of vb.
Proof. by destruct vb; simpl; rewrite ?ptr_freeze_type_of. Qed.
Lemma base_typed_freeze Γ Γm β vb τb :
  (Γ,Γm) ⊢ freeze β vb : τb ↔ (Γ,Γm) ⊢ vb : τb.
Proof.
  split.
  * destruct vb; inversion 1; constructor; auto.
    by apply (ptr_typed_freeze _ _ β).
  * destruct 1; constructor; auto. by apply ptr_typed_freeze.
Qed.
Lemma base_typed_int_frozen Γ Γm vb τi : (Γ,Γm) ⊢ vb : intT τi → frozen vb.
Proof. inversion_clear 1; constructor. Qed.

(** ** Properties of the [base_val_flatten] function *)
Lemma base_val_flatten_valid Γ Γm vb τb :
  (Γ,Γm) ⊢ vb : τb → ✓{Γ,Γm}* (base_val_flatten Γ vb).
Proof.
  destruct 1; simpl.
  * apply Forall_replicate, BIndet_valid.
  * apply Forall_replicate, BIndet_valid.
  * apply Forall_fmap, Forall_true. constructor.
  * apply Forall_fmap; eapply (Forall_impl (✓{Γ,Γm}));
      eauto using ptr_to_bits_valid, BPtr_valid.
  * eauto using char_byte_valid_bits_valid.
Qed.
Lemma base_val_flatten_weaken Γ1 Γ2 Γm τb vb :
  ✓ Γ1 → (Γ1,Γm) ⊢ vb : τb → Γ1 ⊆ Γ2 →
  base_val_flatten Γ1 vb = base_val_flatten Γ2 vb.
Proof.
  by destruct 2; intros; simpl; erewrite ?ptr_to_bits_weaken,
    ?bit_size_of_weaken by eauto using TBase_valid, TVoid_valid.
Qed.
Lemma base_val_flatten_freeze Γ β vb :
  base_val_flatten Γ (freeze β vb) = base_val_flatten Γ vb.
Proof. by destruct vb; simpl; rewrite ?ptr_to_bits_freeze. Qed.
Lemma base_val_flatten_length Γ Γm vb τb :
  (Γ,Γm) ⊢ vb : τb → length (base_val_flatten Γ vb) = bit_size_of Γ τb.
Proof.
  destruct 1; simplify_equality'.
  * by rewrite replicate_length.
  * by rewrite replicate_length.
  * by rewrite fmap_length, bit_size_of_int, int_to_bits_length.
  * by erewrite fmap_length, ptr_to_bits_length_alt, type_of_correct by eauto.
  * by erewrite bit_size_of_int, int_bits_char, char_byte_valid_bits by eauto.
Qed.

(** ** Properties of the [base_val_unflatten] function *)
Inductive base_val_unflatten_view Γ :
     base_type Ti → list (bit Ti) → base_val Ti → Prop :=
  | base_val_of_void bs : base_val_unflatten_view Γ voidT bs VVoid
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
  intros Hbs. unfold base_val_unflatten. destruct τb as [|τi|τ].
  * constructor.
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
  * destruct (mapM maybe_BPtr bs) as [pbs|] eqn:Hpbs; csimpl.
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
Proof. intro. unfold base_val_unflatten. by rewrite mapM_fmap_Some by done. Qed.
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
  τb ≠ voidT → Forall (BIndet =) bs → length bs = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs = VIndet τb.
Proof.
  intros. assert (∀ τi βs,
    Forall (@BIndet Ti =) (BBit <$> βs) → length βs ≠ int_bits τi).
  { intros τi βs ??. pose proof (int_bits_pos τi).
    destruct βs; decompose_Forall_hyps; lia. }
  assert (∀ τ pbs p,
    Forall (BIndet =) (BPtr <$> pbs) → ptr_of_bits Γ τ pbs ≠ Some p).
  { intros τ pbs p ??. assert (length pbs ≠ 0).
    { erewrite ptr_of_bits_length by eauto. by apply bit_size_of_base_ne_0. }
    destruct pbs; decompose_Forall_hyps; lia. }
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
  τb ≠ ucharT → τb ≠ voidT → length bs = bit_size_of Γ τb →
  BIndet ∈ bs → base_val_unflatten Γ τb bs = VIndet τb.
Proof.
  intros ???. feed destruct (base_val_unflatten_spec Γ τb bs);
    rewrite ?elem_of_list_fmap; naive_solver.
Qed.

Lemma base_val_unflatten_typed Γ Γm τb bs :
  ✓{Γ} τb → ✓{Γ,Γm}* bs → length bs = bit_size_of Γ τb →
  (Γ,Γm) ⊢ base_val_unflatten Γ τb bs : τb.
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
Lemma base_val_unflatten_flatten Γ Γm vb τb :
  (Γ,Γm) ⊢ vb : τb →
  base_val_unflatten Γ τb (base_val_flatten Γ vb) = freeze true vb.
Proof.
  destruct 1 as [τb| |x|p τ|bs []]; simpl.
  * by rewrite base_val_unflatten_indet
      by auto using Forall_replicate_eq, replicate_length.
  * done.
  * by rewrite base_val_unflatten_int, int_of_to_bits
      by auto using int_to_bits_length.
  * by erewrite base_val_unflatten_ptr by eauto using ptr_of_to_bits_typed.
  * by rewrite base_val_unflatten_byte by done.
Qed.
Lemma base_val_unflatten_frozen Γ Γm τb bs :
  ✓{Γ,Γm}* bs → frozen (base_val_unflatten Γ τb bs).
Proof.
  intros. unfold base_val_unflatten, default, frozen.
  destruct τb; repeat (simplify_option_equality || case_match); f_equal'.
  efeed pose proof (λ bs pbs, proj1 (maybe_BPtrs_spec bs pbs)); eauto.
  subst. eapply ptr_of_bits_frozen; eauto using BPtrs_valid_inv.
Qed.
Lemma base_val_flatten_inj Γ Γm β vb1 vb2 τb :
  (Γ,Γm) ⊢ vb1 : τb → (Γ,Γm) ⊢ vb2 : τb →
  base_val_flatten Γ vb1 = base_val_flatten Γ vb2 → freeze β vb1 = freeze β vb2.
Proof.
  intros ?? Hv. by rewrite <-(base_val_freeze_freeze _ true vb1),
    <-(base_val_freeze_freeze _ true vb2),
    <-(base_val_unflatten_flatten Γ Γm vb1 τb),
    <-(base_val_unflatten_flatten Γ Γm vb2 τb), Hv by done.
Qed.
Lemma base_val_flatten_unflatten Γ Γm τb bs :
  ✓{Γ,Γm}* bs → length bs = bit_size_of Γ τb →
  base_val_flatten Γ (base_val_unflatten Γ τb bs) ⊑* bs.
Proof.
  intros. cut (base_val_flatten Γ (base_val_unflatten Γ τb bs) = bs
    ∨ base_val_unflatten Γ τb bs = VIndet τb ∨ τb = voidT).
  { intros [->|[->| ->]]; simpl; eauto using Forall2_replicate_l,
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
  destruct (decide (τb = voidT)) as [->|]; [done|].
  destruct (bits_subseteq_eq bs2 bs3) as [->|]; auto.
  rewrite <-Hbs13, !(base_val_unflatten_indet_elem_of Γ);
    eauto using bits_subseteq_indet, Forall2_length_l.
Qed.

(** ** Refinements *)
Lemma base_val_flatten_refine Γ α f Γm1 Γm2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Γm1↦Γm2} vb2 : τb →
  base_val_flatten Γ vb1 ⊑{Γ,α,f@Γm1↦Γm2}* base_val_flatten Γ vb2.
Proof.
  destruct 1; try (destruct α; [|done]); simpl.
  * apply Forall2_replicate; constructor.
  * apply Forall2_replicate_l; eauto using base_val_flatten_length,
      Forall_impl, base_val_flatten_valid, BIndet_refine.
  * apply Forall2_replicate; repeat constructor.
  * by apply BBits_refine.
  * eapply BPtrs_refine, ptr_to_bits_refine; eauto.
  * eapply BPtrs_any_refine; eauto using ptr_to_bits_valid,
      base_val_flatten_valid, ptr_to_bits_dead.
    by erewrite ptr_to_bits_length, base_val_flatten_length by eauto.
  * done.
  * done.
  * eapply BIndets_refine_r_inv; eauto using base_val_flatten_valid.
    by erewrite base_val_flatten_length, char_byte_valid_bits,
      bit_size_of_int, int_bits_char by eauto.
Qed.
Lemma base_val_refine_typed_l Γ α f Γm1 Γm2 vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,α,f@Γm1↦Γm2} vb2 : τb → (Γ,Γm1) ⊢ vb1 : τb.
Proof.
  destruct 2; constructor;
    eauto using ptr_refine_typed_l, base_val_typed_type_valid.
Qed.
Lemma base_val_refine_typed_r Γ α f Γm1 Γm2 vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,α,f@Γm1↦Γm2} vb2 : τb → (Γ,Γm2) ⊢ vb2 : τb.
Proof.
  destruct 2; try constructor; eauto using ptr_refine_typed_r, TInt_valid.
Qed.
Lemma base_val_refine_type_of_l Γ α f Γm1 Γm2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Γm1↦Γm2} vb2 : τb → type_of vb1 = τb.
Proof.
  destruct 1; simplify_type_equality';
    f_equal'; eauto using ptr_refine_type_of_l.
Qed.
Lemma base_val_refine_type_of_r Γ α f Γm1 Γm2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Γm1↦Γm2} vb2 : τb → type_of vb2 = τb.
Proof.
  destruct 1; f_equal'; eauto using ptr_refine_type_of_r, type_of_correct.
Qed.
Lemma base_val_refine_id Γ α Γm vb τb :
  (Γ,Γm) ⊢ vb : τb → vb ⊑{Γ,α@Γm} vb : τb.
Proof.
  destruct 1; constructor; eauto using ptr_refine_id,
    bits_refine_id, char_byte_valid_bits_valid; constructor; eauto.
Qed.
Lemma base_val_refine_compose Γ α1 α2 f g Γm1 Γm2 Γm3 vb1 vb2 vb3 τb τb' :
  ✓ Γ → vb1 ⊑{Γ,α1,f@Γm1↦Γm2} vb2 : τb → vb2 ⊑{Γ,α2,g@Γm2↦Γm3} vb3 : τb' →
  vb1 ⊑{Γ,α1||α2,f ◎ g@Γm1↦Γm3} vb3 : τb.
Proof.
  intros ? Hvb1 Hvb2. assert (τb = τb') as <- by (eapply (typed_unique _ vb2);
    eauto using base_val_refine_typed_r, base_val_refine_typed_l).
  destruct Hvb1.
  * inversion_clear Hvb2; refine_constructor; auto.
  * refine_constructor; eauto using base_val_refine_typed_r.
  * inversion_clear Hvb2; refine_constructor.
  * by inversion_clear Hvb2; refine_constructor.
  * inversion_clear Hvb2; refine_constructor;
      eauto using ptr_refine_compose, ptr_alive_refine, ptr_refine_typed_l.
  * refine_constructor; eauto using base_val_refine_typed_r.
  * inversion_clear Hvb2; refine_constructor; eauto using bits_refine_compose.
  * inversion_clear Hvb2; refine_constructor;
      eauto using BBits_refine, bits_refine_compose.
  * refine_constructor; eauto using base_val_refine_typed_r.
    by destruct α1; simpl; eauto using (bits_refine_compose _ true true),
      BIndets_refine, BIndets_valid.
Qed.
Lemma base_val_refine_weaken Γ Γ' α α' f f' Γm1 Γm2 Γm1' Γm2' vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,α,f@Γm1↦Γm2} vb2 : τb → Γ ⊆ Γ' → (α → α') →
  Γm1' ⊑{Γ',α',f'} Γm2' → Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend f f' Γm1 Γm2 → vb1 ⊑{Γ',α',f'@Γm1'↦Γm2'} vb2 : τb.
Proof.
  destruct 2; refine_constructor; eauto using base_val_typed_weaken,
    ptr_refine_weaken, ptr_typed_weaken, char_byte_valid_weaken,
    ptr_dead_weaken, Forall2_impl, bit_refine_weaken, base_type_valid_weaken.
Qed.
Lemma base_val_unflatten_refine Γ α f Γm1 Γm2 τb bs1 bs2 :
  ✓ Γ → ✓{Γ} τb → bs1 ⊑{Γ,α,f@Γm1↦Γm2}* bs2 → length bs1 = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs1 ⊑{Γ,α,f@Γm1↦Γm2} base_val_unflatten Γ τb bs2 : τb.
Proof.
  intros ?? Hbs Hbs1. assert (length bs2 = bit_size_of Γ τb) as Hbs2.
  { eauto using Forall2_length_l. }
  (* why cannot Coq swap goals... *)
  assert (α = false ∨ α = true) as [->| ->] by (destruct α; auto).
  { feed destruct (base_val_unflatten_spec Γ τb bs1)
      as [|τi βs1|τ p1 pbs1|bs1|bs1|τi bs1|τ pbs1|τ bs1]; auto.
    * constructor.
    * rewrite (BBits_refine_inv_l Γ false f Γm1 Γm2 βs1 bs2),
        base_val_unflatten_int by done.
      constructor. by apply int_of_bits_typed.
    * destruct (BPtrs_refine_inv_l' Γ f Γm1 Γm2 pbs1 bs2) as (pbs2&->&?); auto.
      destruct (ptr_of_bits_refine Γ false f Γm1 Γm2 τ pbs1 pbs2 p1)
        as (p2&?&?); eauto.
      erewrite base_val_unflatten_ptr by eauto; by constructor.
    * assert (¬(∃ βs, bs2 = BBit <$> βs))
        by naive_solver eauto using BBits_refine_inv_r.
      rewrite bit_size_of_int, int_bits_char in Hbs1, Hbs2.
      erewrite base_val_unflatten_byte by eauto using BIndets_refine_r_inv'.
      repeat constructor; eauto using bits_refine_valid_l,
        bits_refine_valid_r, BIndets_refine_r_inv', BIndets_refine_l_inv'.
    * erewrite base_val_unflatten_indet by eauto using BIndets_refine_l_inv'.
      by constructor.
    * assert (¬(∃ βs, bs2 = BBit <$> βs))
        by naive_solver eauto using BBits_refine_inv_r.
      rewrite bit_size_of_int in Hbs1, Hbs2.
      erewrite base_val_unflatten_int_indet by eauto; constructor; eauto.
    * destruct (BPtrs_refine_inv_l' Γ f Γm1 Γm2 pbs1 bs2) as (pbs2&->&?); auto.
      erewrite base_val_unflatten_ptr_indet_1 by
        eauto using ptr_of_bits_refine_None, Forall2_length_l.
      by constructor.
    * assert (¬(∃ pbs, bs2 = BPtr <$> pbs)).
      { intros [pbs2 ->]. destruct (BPtrs_refine_inv_r' Γ f Γm1 Γm2 bs1 pbs2)
          as (?&->&?); eauto. }
      erewrite base_val_unflatten_ptr_indet_2 by eauto. by constructor. }
  feed destruct (base_val_unflatten_spec Γ τb bs1)
    as [|τi βs1|τ p1 pbs1|bs1|bs1|τi bs1|τ pbs1|τ bs1]; auto.
  * constructor.
  * rewrite (BBits_refine_inv_l Γ true f Γm1 Γm2 βs1 bs2),
      base_val_unflatten_int by done.
    constructor. by apply int_of_bits_typed.
  * destruct (decide (ptr_alive Γm1 p1)).
    { destruct (BPtrs_refine_inv_l Γ true f Γm1 Γm2 pbs1 bs2) as (pbs2&->&?); auto.
      { erewrite <-ptr_to_of_bits by eauto using BPtrs_valid_inv,
          bits_refine_valid_l; eauto using ptr_to_bits_alive. }
      destruct (ptr_of_bits_refine Γ true f Γm1 Γm2 τ pbs1 pbs2 p1)
        as (p2&?&?); eauto.
      erewrite base_val_unflatten_ptr by eauto. by constructor. }
    constructor; eauto using ptr_of_bits_typed, BPtrs_valid_inv,
      bits_refine_valid_l, bits_refine_valid_r, base_val_unflatten_typed.
  * destruct (decide (∃ βs, bs2 = BBit <$> βs)) as [[βs2 ->]|?].
    { rewrite fmap_length, bit_size_of_int in Hbs2.
      rewrite base_val_unflatten_int by done. constructor; auto.
      + by rewrite int_to_of_bits by done.
      + constructor; eauto using bits_refine_valid_l.
      + by apply int_of_bits_typed. }
    assert (length bs2 = char_bits) by eauto using Forall2_length_l.
    destruct (decide (Forall (BIndet =) bs2)).
    { econstructor; eauto using base_val_unflatten_typed, bits_refine_valid_r.
      constructor; eauto using bits_refine_valid_l. }
    rewrite base_val_unflatten_byte by done.
    repeat constructor; eauto using bits_refine_valid_l, bits_refine_valid_r.
  * destruct (decide (∃ βs, bs2 = BBit <$> βs)) as [[βs2 ->]|?].
    { rewrite fmap_length, bit_size_of_int in Hbs2.
      rewrite base_val_unflatten_int by done.
      constructor; auto; constructor; auto using int_of_bits_typed. }
    destruct (decide (Forall (BIndet =) bs2)).
    { rewrite base_val_unflatten_indet by done. by repeat constructor. }
    assert (length bs2 = char_bits) by eauto using Forall2_length_l.
    rewrite base_val_unflatten_byte by done.
    repeat constructor; eauto using BIndets_refine_l_inv.
  * destruct (decide (∃ βs, bs2 = BBit <$> βs)) as [[βs2 ->]|?].
    { rewrite fmap_length, bit_size_of_int in Hbs2.
      rewrite base_val_unflatten_int by done.
      repeat constructor; auto; by apply int_of_bits_typed. }
    rewrite bit_size_of_int in Hbs2.
    rewrite base_val_unflatten_int_indet by done. by repeat constructor.
  * constructor; eauto using base_val_unflatten_typed, bits_refine_valid_r.
  * destruct (decide (∃ pbs, bs2 = BPtr <$> pbs)) as [[pbs2 ->]|?].
    { destruct (ptr_of_bits Γ τ pbs2) as [p2|] eqn:?.
      { erewrite base_val_unflatten_ptr by eauto.
        constructor; auto; constructor; eauto using ptr_of_bits_typed,
          ptr_of_bits_Exists_Forall_typed, BPtrs_refine_inv_r. }
      rewrite fmap_length in Hbs2.
      rewrite base_val_unflatten_ptr_indet_1 by done.
      by constructor; auto; constructor. }
    rewrite base_val_unflatten_ptr_indet_2 by done.
    by constructor; auto; constructor.
Qed.
End properties.
