(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export bits.

Local Open Scope cbase_type_scope.

Inductive base_val (K : iType) : iType :=
  | VIndet : base_type K → base_val K
  | VVoid : base_val K
  | VInt : int_type K → Z → base_val K
  | VPtr : ptr K → base_val K
  | VByte : list (bit K) → base_val K.
Arguments VIndet {_} _.
Arguments VVoid {_}.
Arguments VInt {_} _ _.
Arguments VPtr {_} _.
Arguments VByte {_} _.

Declare Scope base_val_scope.
Delimit Scope base_val_scope with B.
Bind Scope base_val_scope with base_val.
Open Scope base_val_scope.
Notation "'voidV'" := VVoid : base_val_scope.
Notation "'indetV' τb" := (VIndet τb) (at level 10) : base_val_scope.
Notation "'intV{' τi } x" := (VInt τi x)
  (at level 10, format "intV{ τi }  x") : base_val_scope.
Notation "'ptrV' p" := (VPtr p) (at level 10) : base_val_scope.
Notation "'byteV' bs" := (VByte bs) (at level 10) : base_val_scope.

#[global] Instance maybe_VInt {K} : Maybe2 (@VInt K) := λ vb,
  match vb with VInt τi x => Some (τi,x) | _ => None end.
#[global] Instance maybe_VPtr {K} : Maybe (@VPtr K) := λ vb,
  match vb with VPtr p => Some p | _ => None end.
#[global] Instance base_val_eq_dec {K} `{EqDecision K}: EqDecision (base_val K).
Proof. solve_decision. Defined.

Section operations.
  Context `{Env K}.

  Record char_byte_valid (Γ : env K)
      (Δ : memenv K) (bs : list (bit K)) : Prop := {
    char_byte_valid_indet : ¬Forall (BIndet =.) bs;
    char_byte_valid_bit : ¬(∃ βs, bs = BBit <$> βs);
    char_byte_valid_bits_valid : ✓{Γ,Δ}* bs;
    char_byte_valid_bits : length bs = char_bits
  }.
  Global Instance char_byte_valid_dec Γ Δ bs :
    Decision (char_byte_valid Γ Δ bs).
  Proof.
   refine (cast_if (decide (¬Forall (BIndet =.) bs ∧
     ¬(∃ βs, bs = BBit <$> βs) ∧ ✓{Γ,Δ}* bs ∧ length bs = char_bits)));
     abstract (constructor||intros[]; intuition).
  Defined.
  Inductive base_typed' (Γ : env K) (Δ : memenv K) :
       base_val K → base_type K → Prop :=
    | VIndet_typed τb : ✓{Γ} τb → τb ≠ voidT → base_typed' Γ Δ (VIndet τb) τb
    | VVoid_typed : base_typed' Γ Δ VVoid voidT
    | VInt_typed x τi : int_typed x τi → base_typed' Γ Δ (VInt τi x) (intT τi)
    | VPtr_typed p τp : (Γ,Δ) ⊢ p : τp → base_typed' Γ Δ (VPtr p) (τp.*)
    | VByte_typed bs :
       char_byte_valid Γ Δ bs → base_typed' Γ Δ (VByte bs) ucharT.
  Global Instance base_typed: Typed (env K * memenv K)
    (base_type K) (base_val K) := uncurry base_typed'.
  Global Instance type_of_base_val: TypeOf (base_type K) (base_val K) := λ v,
    match v with
    | VIndet τb => τb
    | VVoid => voidT
    | VInt τi _ => intT τi
    | VPtr p => type_of p.*
    | VByte _ => ucharT
    end.
  Global Instance base_type_check:
    TypeCheck (env K * memenv K) (base_type K) (base_val K) := λ ΓΔ v,
    match v with
    | VIndet τb => guard (✓{ΓΔ.1} τb); guard (τb ≠ voidT); Some τb
    | VVoid => Some voidT
    | VInt τi x => guard (int_typed x τi); Some (intT τi)
    | VPtr p => TPtr <$> type_check ΓΔ p
    | VByte bs => guard (char_byte_valid (ΓΔ.1) (ΓΔ.2) bs); Some ucharT
    end.
  Global Instance base_val_freeze : Freeze (base_val K) := λ β v,
    match v with VPtr p => VPtr (freeze β p) | _ => v end.

  Definition base_val_flatten (Γ : env K) (v : base_val K) : list (bit K) :=
    match v with
    | VIndet τb => replicate (bit_size_of Γ τb) BIndet
    | VVoid => replicate (bit_size_of Γ voidT) BIndet
    | VInt τi x => BBit <$> int_to_bits τi x
    | VPtr p => BPtr <$> ptr_to_bits Γ p
    | VByte bs => bs
    end.
  Definition base_val_unflatten (Γ : env K)
      (τb : base_type K) (bs : list (bit K)) : base_val K :=
    match τb with
    | voidT => VVoid
    | intT τi =>
       match mapM (maybe BBit) bs with
       | Some βs => VInt τi (int_of_bits τi βs)
       | None =>
          if decide (τi = ucharT%IT ∧ ¬Forall (BIndet =.) bs)
          then VByte bs else VIndet τb
       end
    | τp.* =>
       from_option VPtr (VIndet τb) (mapM (maybe BPtr) bs ≫= ptr_of_bits Γ τp)
    end.
End operations.

Arguments base_val_unflatten _ _ _ _ _ : simpl never.

Section base_values.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α : bool.
Implicit Types τb : base_type K.
Implicit Types τp : ptr_type K.
Implicit Types vb : base_val K.
Implicit Types bs : list (bit K).
Implicit Types βs : list bool.

Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Local Hint Extern 0 (_ ⊑* _) => reflexivity: core.

(** ** General properties of the typing judgment *)
Lemma base_val_typed_type_valid Γ Δ v τb : ✓ Γ → (Γ,Δ) ⊢ v : τb → ✓{Γ} τb.
Proof.
  destruct 2;
    eauto using TVoid_valid, TInt_valid, TPtr_valid, ptr_typed_type_valid.
Qed.
#[global] Instance: TypeOfSpec (env K * memenv K) (base_type K) (base_val K).
Proof.
  intros [??]. destruct 1; f_equal'; auto. eapply type_of_correct; eauto.
Qed.
#[global] Instance:
  TypeCheckSpec (env K * memenv K) (base_type K) (base_val K) (λ _, True).
Proof.
  intros [Γ Δm] vb τb _. split.
  * destruct vb; intros; simplify_option_eq;
      constructor; auto; eapply type_check_sound; eauto.
  * by destruct 1; simplify_option_eq;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma char_byte_valid_weaken Γ1 Γ2 Δ1 Δ2 bs :
  ✓ Γ1 → char_byte_valid Γ1 Δ1 bs → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 →
  char_byte_valid Γ2 Δ2 bs.
Proof. destruct 2; constructor; eauto using Forall_impl, bit_valid_weaken. Qed.
Lemma base_val_typed_weaken Γ1 Γ2 Δ1 Δ2 vb τb :
  ✓ Γ1 → (Γ1,Δ1) ⊢ vb : τb → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → (Γ2,Δ2) ⊢ vb : τb.
Proof.
  destruct 2; econstructor; eauto using ptr_typed_weaken,
    char_byte_valid_weaken, base_type_valid_weaken.
Qed.
Lemma base_val_freeze_freeze β1 β2 vb : freeze β1 (freeze β2 vb) = freeze β1 vb.
Proof. destruct vb; f_equal'; auto using ptr_freeze_freeze. Qed.
Lemma base_typed_freeze Γ Δ β vb τb :
  (Γ,Δ) ⊢ freeze β vb : τb ↔ (Γ,Δ) ⊢ vb : τb.
Proof.
  split.
  * destruct vb; inversion 1; constructor; auto.
    by apply (ptr_typed_freeze _ _ β).
  * destruct 1; constructor; auto. by apply ptr_typed_freeze.
Qed.
Lemma base_typed_int_frozen Γ Δ vb τi : (Γ,Δ) ⊢ vb : intT τi → frozen vb.
Proof. inversion_clear 1; constructor. Qed.

(** ** Properties of the [base_val_flatten] function *)
Lemma base_val_flatten_valid Γ Δ vb τb :
  (Γ,Δ) ⊢ vb : τb → ✓{Γ,Δ}* (base_val_flatten Γ vb).
Proof.
  destruct 1; simpl.
  * apply Forall_replicate, BIndet_valid.
  * apply Forall_replicate, BIndet_valid.
  * apply Forall_fmap, Forall_true. constructor.
  * apply Forall_fmap; eapply (Forall_impl (✓{Γ,Δ}));
      eauto using ptr_to_bits_valid, BPtr_valid.
  * eauto using char_byte_valid_bits_valid.
Qed.
Lemma base_val_flatten_weaken Γ1 Γ2 Δ τb vb :
  ✓ Γ1 → (Γ1,Δ) ⊢ vb : τb → Γ1 ⊆ Γ2 →
  base_val_flatten Γ1 vb = base_val_flatten Γ2 vb.
Proof.
  by destruct 2; intros; simpl; erewrite ?ptr_to_bits_weaken,
    ?bit_size_of_weaken by eauto using TBase_valid, TVoid_valid.
Qed.
Lemma base_val_flatten_freeze Γ β vb :
  base_val_flatten Γ (freeze β vb) = base_val_flatten Γ vb.
Proof. by destruct vb; simpl; rewrite ?ptr_to_bits_freeze. Qed.
Lemma base_val_flatten_length Γ Δ vb τb :
  (Γ,Δ) ⊢ vb : τb → length (base_val_flatten Γ vb) = bit_size_of Γ τb.
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
     base_type K → list (bit K) → base_val K → Prop :=
  | base_val_of_void bs : base_val_unflatten_view Γ voidT bs VVoid
  | base_val_of_int τi βs :
     length βs = int_width τi → base_val_unflatten_view Γ (intT τi)
       (BBit <$> βs) (VInt τi (int_of_bits τi βs))
  | base_val_of_ptr τp p pbs :
     ptr_of_bits Γ τp pbs = Some p →
     base_val_unflatten_view Γ (τp.*) (BPtr <$> pbs) (VPtr p)
  | base_val_of_byte bs :
     length bs = char_bits → ¬Forall (BIndet =.) bs →
     ¬(∃ βs, bs = BBit <$> βs) →
     base_val_unflatten_view Γ ucharT bs (VByte bs)
  | base_val_of_byte_indet bs :
     length bs = char_bits → Forall (BIndet =.) bs →
     base_val_unflatten_view Γ ucharT bs (VIndet ucharT)
  | base_val_of_int_indet τi bs :
     τi ≠ ucharT%IT →
     length bs = int_width τi → ¬(∃ βs, bs = BBit <$> βs) →
     base_val_unflatten_view Γ (intT τi) bs (VIndet (intT τi))
  | base_val_of_ptr_indet_1 τp pbs :
     length pbs = bit_size_of Γ (τp.*) → ptr_of_bits Γ τp pbs = None →
     base_val_unflatten_view Γ (τp.*) (BPtr <$> pbs) (VIndet (τp.*))
  | base_val_of_ptr_indet_2 τp bs :
     length bs = bit_size_of Γ (τp.*) → ¬(∃ pbs, bs = BPtr <$> pbs) →
     base_val_unflatten_view Γ (τp.*) bs (VIndet (τp.*)).
Lemma base_val_unflatten_spec Γ τb bs :
  length bs = bit_size_of Γ τb →
  base_val_unflatten_view Γ τb bs (base_val_unflatten Γ τb bs).
Proof.
  intros Hbs. unfold base_val_unflatten. destruct τb as [|τi|τp].
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
      by destruct (ptr_of_bits Γ τp pbs) as [p|] eqn:?; constructor. }
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
    | _ => simplify_option_eq
    end; auto.
Qed.
Lemma base_val_unflatten_int Γ τi βs :
  length βs = int_width τi →
  base_val_unflatten Γ (intT τi) (BBit <$> βs) = VInt τi (int_of_bits τi βs).
Proof. intro. unfold base_val_unflatten. by rewrite mapM_fmap_Some by done. Qed.
Lemma base_val_unflatten_ptr Γ τp pbs p :
  ptr_of_bits Γ τp pbs = Some p →
  base_val_unflatten Γ (τp.*) (BPtr <$> pbs) = VPtr p.
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ (τp.*) (BPtr <$> pbs));
    simplify_equality'; auto.
  * by erewrite fmap_length, ptr_of_bits_length by eauto.
  * naive_solver (apply Forall_fmap, Forall_true; simpl; eauto).
Qed.
Lemma base_val_unflatten_byte Γ bs :
  ¬Forall (BIndet =.) bs → ¬(∃ βs, bs = BBit <$> βs) →
  length bs = char_bits → base_val_unflatten Γ ucharT bs = VByte bs.
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ ucharT bs);
    simplify_equality'; rewrite ?bit_size_of_int, ?int_width_char; naive_solver.
Qed.
Lemma base_val_unflatten_indet Γ τb bs :
  τb ≠ voidT → Forall (BIndet =.) bs → length bs = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs = VIndet τb.
Proof.
  intros. assert (∀ τi βs,
    Forall (@BIndet K =.) (BBit <$> βs) → length βs ≠ int_width τi).
  { intros τi βs ??. pose proof (int_width_pos τi).
    destruct βs; decompose_Forall_hyps; lia. }
  assert (∀ τp pbs p,
    Forall (BIndet =.) (BPtr <$> pbs) → ptr_of_bits Γ τp pbs ≠ Some p).
  { intros τp pbs p ??. assert (length pbs ≠ 0).
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
Lemma base_val_unflatten_ptr_indet_1 Γ τp pbs :
  length pbs = bit_size_of Γ (τp.*) → ptr_of_bits Γ τp pbs = None →
  base_val_unflatten Γ (τp.*) (BPtr <$> pbs) = VIndet (τp.*).
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ (τp.*) (BPtr <$> pbs));
    simplify_equality'; rewrite ?fmap_length; naive_solver.
Qed.
Lemma base_val_unflatten_ptr_indet_2 Γ τp bs :
  length bs = bit_size_of Γ (τp.*) → ¬(∃ pbs, bs = BPtr <$> pbs) →
  base_val_unflatten Γ (τp.*) bs = VIndet (τp.*).
Proof.
  intros. feed inversion (base_val_unflatten_spec Γ (τp.*) bs);
    simplify_equality'; naive_solver.
Qed.
Lemma base_val_unflatten_indet_elem_of Γ τb bs :
  τb ≠ ucharT → τb ≠ voidT → length bs = bit_size_of Γ τb →
  BIndet ∈ bs → base_val_unflatten Γ τb bs = VIndet τb.
Proof.
  intros ???. feed destruct (base_val_unflatten_spec Γ τb bs);
    rewrite ?elem_of_list_fmap; naive_solver.
Qed.

Lemma base_val_unflatten_typed Γ Δ τb bs :
  ✓{Γ} τb → ✓{Γ,Δ}* bs → length bs = bit_size_of Γ τb →
  (Γ,Δ) ⊢ base_val_unflatten Γ τb bs : τb.
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
  destruct τb; repeat (simplify_option_eq || case_match || intuition).
  f_equal; eauto using ptr_of_bits_type_of.
Qed.
Lemma base_val_unflatten_flatten Γ Δ vb τb :
  (Γ,Δ) ⊢ vb : τb →
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
Lemma base_val_unflatten_frozen Γ Δ τb bs :
  ✓{Γ,Δ}* bs → frozen (base_val_unflatten Γ τb bs).
Proof.
  intros. unfold base_val_unflatten, default, frozen.
  destruct τb; repeat (simplify_option_eq || case_match); f_equal'.
  efeed pose proof (λ bs pbs, proj1 (maybe_BPtrs_spec bs pbs)); eauto.
  subst. eapply ptr_of_bits_frozen; eauto using BPtrs_valid_inv.
Qed.
Lemma base_val_flatten_inj Γ Δ β vb1 vb2 τb :
  (Γ,Δ) ⊢ vb1 : τb → (Γ,Δ) ⊢ vb2 : τb →
  base_val_flatten Γ vb1 = base_val_flatten Γ vb2 → freeze β vb1 = freeze β vb2.
Proof.
  intros ?? Hv. by rewrite <-(base_val_freeze_freeze _ true vb1),
    <-(base_val_freeze_freeze _ true vb2),
    <-(base_val_unflatten_flatten Γ Δ vb1 τb),
    <-(base_val_unflatten_flatten Γ Δ vb2 τb), Hv by done.
Qed.
Lemma base_val_flatten_unflatten Γ Δ τb bs :
  ✓{Γ,Δ}* bs → length bs = bit_size_of Γ τb →
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
    by rewrite (anti_symm (Forall2 bit_weak_refine) bs2 bs3). }
  destruct (decide (τb = voidT)) as [->|]; [done|].
  destruct (bits_subseteq_eq bs2 bs3) as [->|]; auto.
  rewrite <-Hbs13, !(base_val_unflatten_indet_elem_of Γ);
    eauto using bits_subseteq_indet, Forall2_length_l.
Qed.
End base_values.
