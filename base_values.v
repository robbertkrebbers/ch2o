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

Instance maybe_VInt {Ti} : Maybe2 (@VInt Ti) := λ vb,
  match vb with VInt τi x => Some (τi,x) | _ => None end.
Instance maybe_VPtr {Ti} : Maybe (@VPtr Ti) := λ vb,
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
       match mapM (maybe BBit) bs with
       | Some βs => VInt τi (int_of_bits τi βs)
       | None =>
          if decide (τi = ucharT%IT ∧ ¬Forall (BIndet =) bs)
          then VByte bs else VIndet τb
       end
    | τ.* => default (VIndet τb) (mapM (maybe BPtr) bs ≫= ptr_of_bits Γ τ) VPtr
    end.
End operations.

Arguments base_val_unflatten _ _ _ _ _ : simpl never.

Section base_values.
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
  * by erewrite bit_size_of_int, int_width_char, char_byte_valid_bits by eauto.
Qed.

(** ** Properties of the [base_val_unflatten] function *)
Inductive base_val_unflatten_view Γ :
     base_type Ti → list (bit Ti) → base_val Ti → Prop :=
  | base_val_of_void bs : base_val_unflatten_view Γ voidT bs VVoid
  | base_val_of_int τi βs :
     length βs = int_width τi → base_val_unflatten_view Γ (intT τi)
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
     length bs = int_width τi → ¬(∃ βs, bs = BBit <$> βs) →
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
    destruct (mapM (maybe BBit) bs) as [βs|] eqn:Hβs.
    { rewrite maybe_BBits_spec in Hβs; subst. rewrite fmap_length in Hbs.
      by constructor. }
    assert (¬∃ βs, bs = BBit <$> βs).
    { setoid_rewrite <-maybe_BBits_spec. intros [??]; simpl in *; congruence. }
    destruct (decide _) as [[-> ?]|Hτbs].
    { rewrite int_width_char in Hbs. by constructor. }
    destruct (decide (τi = ucharT%IT)) as [->|?].
    { rewrite int_width_char in Hbs.
      constructor; auto. apply dec_stable; naive_solver. }
    by constructor.
  * destruct (mapM (maybe BPtr) bs) as [pbs|] eqn:Hpbs; csimpl.
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
  length βs = int_width τi →
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
    simplify_equality'; rewrite ?bit_size_of_int, ?int_width_char; naive_solver.
Qed.
Lemma base_val_unflatten_indet Γ τb bs :
  τb ≠ voidT → Forall (BIndet =) bs → length bs = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs = VIndet τb.
Proof.
  intros. assert (∀ τi βs,
    Forall (@BIndet Ti =) (BBit <$> βs) → length βs ≠ int_width τi).
  { intros τi βs ??. pose proof (int_width_pos τi).
    destruct βs; decompose_Forall_hyps; lia. }
  assert (∀ τ pbs p,
    Forall (BIndet =) (BPtr <$> pbs) → ptr_of_bits Γ τ pbs ≠ Some p).
  { intros τ pbs p ??. assert (length pbs ≠ 0).
    { erewrite ptr_of_bits_length by eauto. by apply bit_size_of_base_ne_0. }
    destruct pbs; decompose_Forall_hyps; lia. }
  feed inversion (base_val_unflatten_spec Γ τb bs); naive_solver.
Qed.
Lemma base_val_unflatten_int_indet Γ τi bs :
  τi ≠ ucharT%IT → length bs = int_width τi → ¬(∃ βs, bs = BBit <$> βs) →
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
End base_values.
