(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export base_values bits_refine.
Local Open Scope cbase_type_scope.

Inductive base_val_refine' `{Env K} (Γ : env K)
      (α : bool) (f : meminj K) (Δ1 Δ2 : memenv K) :
      base_val K → base_val K → base_type K → Prop :=
  | VIndet_VIndet_refine' τb :
     ✓{Γ} τb → τb ≠ voidT →
     base_val_refine' Γ α f Δ1 Δ2 (VIndet τb) (VIndet τb) τb
  | VIndet_refine' τb vb :
     α → (Γ,Δ2) ⊢ vb : τb → τb ≠ voidT →
     base_val_refine' Γ α f Δ1 Δ2 (VIndet τb) vb τb
  | VVoid_refine' : base_val_refine' Γ α f Δ1 Δ2 VVoid VVoid voidT
  | VInt_refine' x τi :
     int_typed x τi →
     base_val_refine' Γ α f Δ1 Δ2 (VInt τi x) (VInt τi x) (intT τi)
  | VPtr_refine' p1 p2 σ :
     p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : σ →
     base_val_refine' Γ α f Δ1 Δ2 (VPtr p1) (VPtr p2) (σ.*)
  | VPtr_VIndet_refine p1 vb2 σ :
     α → (Γ,Δ1) ⊢ p1 : σ → ¬ptr_alive Δ1 p1 → (Γ,Δ2) ⊢ vb2 : σ.* →
     base_val_refine' Γ α f Δ1 Δ2 (VPtr p1) vb2 (σ.*)
  | VByte_refine' bs1 bs2 :
     bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 →
     char_byte_valid Γ Δ1 bs1 → char_byte_valid Γ Δ2 bs2 →
     base_val_refine' Γ α f Δ1 Δ2 (VByte bs1) (VByte bs2) ucharT
  | VByte_Vint_refine' bs1 x2 :
     α → bs1 ⊑{Γ,α,f@Δ1↦Δ2}* BBit <$> int_to_bits ucharT x2 →
     char_byte_valid Γ Δ1 bs1 → int_typed x2 ucharT →
     base_val_refine' Γ α f Δ1 Δ2 (VByte bs1) (VInt ucharT x2) ucharT
  | VByte_VIndet_refine' bs1 bs2 vb2 :
     α → bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 → char_byte_valid Γ Δ1 bs1 →
     Forall (BIndet =.) bs2 → (Γ,Δ2) ⊢ vb2 : ucharT →
     base_val_refine' Γ α f Δ1 Δ2 (VByte bs1) vb2 ucharT.
#[global] Instance base_val_refine `{Env K} :
  RefineT K (env K) (base_type K) (base_val K) := base_val_refine'.

Section base_values.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α : bool.
Implicit Types τb : base_type K.
Implicit Types vb : base_val K.
Implicit Types bs : list (bit K).
Implicit Types βs : list bool.

Lemma base_val_flatten_refine Γ α f Δ1 Δ2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Δ1↦Δ2} vb2 : τb →
  base_val_flatten Γ vb1 ⊑{Γ,α,f@Δ1↦Δ2}* base_val_flatten Γ vb2.
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
      bit_size_of_int, int_width_char by eauto.
Qed.
Lemma base_val_refine_typed_l Γ α f Δ1 Δ2 vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,α,f@Δ1↦Δ2} vb2 : τb → (Γ,Δ1) ⊢ vb1 : τb.
Proof.
  destruct 2; constructor;
    eauto using ptr_refine_typed_l, base_val_typed_type_valid.
Qed.
Lemma base_val_refine_typed_r Γ α f Δ1 Δ2 vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,α,f@Δ1↦Δ2} vb2 : τb → (Γ,Δ2) ⊢ vb2 : τb.
Proof.
  destruct 2; try constructor; eauto using ptr_refine_typed_r, TInt_valid.
Qed.
Lemma base_val_refine_type_of_l Γ α f Δ1 Δ2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Δ1↦Δ2} vb2 : τb → type_of vb1 = τb.
Proof.
  destruct 1; simplify_type_equality';
    f_equal'; eauto using ptr_refine_type_of_l.
Qed.
Lemma base_val_refine_type_of_r Γ α f Δ1 Δ2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Δ1↦Δ2} vb2 : τb → type_of vb2 = τb.
Proof.
  destruct 1; f_equal'; eauto using ptr_refine_type_of_r, type_of_correct.
Qed.
Lemma base_val_refine_id Γ α Δ vb τb :
  (Γ,Δ) ⊢ vb : τb → vb ⊑{Γ,α@Δ} vb : τb.
Proof.
  destruct 1; constructor; eauto using ptr_refine_id,
    bits_refine_id, char_byte_valid_bits_valid; constructor; eauto.
Qed.
Lemma base_val_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 vb1 vb2 vb3 τb τb' :
  ✓ Γ → vb1 ⊑{Γ,α1,f1@Δ1↦Δ2} vb2 : τb → vb2 ⊑{Γ,α2,f2@Δ2↦Δ3} vb3 : τb' →
  vb1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} vb3 : τb.
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
Lemma base_val_refine_inverse Γ f Δ1 Δ2 vb1 vb2 τb :
  vb1 ⊑{Γ,false,f@Δ1↦Δ2} vb2 : τb →
  vb2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} vb1 : τb.
Proof.
  destruct 1; try done; constructor;
    eauto using ptr_refine_inverse, bits_refine_inverse.
Qed.
Lemma base_val_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' vb1 vb2 τb :
  ✓ Γ → vb1 ⊑{Γ,α,f@Δ1↦Δ2} vb2 : τb → Γ ⊆ Γ' → (α → α') →
  Δ1' ⊑{Γ',α',f'} Δ2' → Δ1 ⇒ₘ Δ1' → Δ2 ⇒ₘ Δ2' →
  meminj_extend f f' Δ1 Δ2 → vb1 ⊑{Γ',α',f'@Δ1'↦Δ2'} vb2 : τb.
Proof.
  destruct 2; refine_constructor; eauto using base_val_typed_weaken,
    ptr_refine_weaken, ptr_typed_weaken, char_byte_valid_weaken,
    ptr_dead_weaken, Forall2_impl, bit_refine_weaken, base_type_valid_weaken.
Qed.
Lemma base_val_unflatten_refine Γ α f Δ1 Δ2 τb bs1 bs2 :
  ✓ Γ → ✓{Γ} τb → bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 → length bs1 = bit_size_of Γ τb →
  base_val_unflatten Γ τb bs1 ⊑{Γ,α,f@Δ1↦Δ2} base_val_unflatten Γ τb bs2 : τb.
Proof.
  intros ?? Hbs Hbs1. assert (length bs2 = bit_size_of Γ τb) as Hbs2.
  { eauto using Forall2_length_l. }
  (* why cannot Coq swap goals... *)
  assert (α = false ∨ α = true) as [->| ->] by (destruct α; auto).
  { feed destruct (base_val_unflatten_spec Γ τb bs1)
      as [|τi βs1|τ p1 pbs1|bs1|bs1|τi bs1|τ pbs1|τ bs1]; auto.
    * constructor.
    * rewrite (BBits_refine_inv_l Γ false f Δ1 Δ2 βs1 bs2),
        base_val_unflatten_int by done.
      constructor. by apply int_of_bits_typed.
    * destruct (BPtrs_refine_inv_l' Γ f Δ1 Δ2 pbs1 bs2) as (pbs2&->&?); auto.
      destruct (ptr_of_bits_refine Γ false f Δ1 Δ2 τ pbs1 pbs2 p1)
        as (p2&?&?); eauto.
      erewrite base_val_unflatten_ptr by eauto; by constructor.
    * assert (¬(∃ βs, bs2 = BBit <$> βs))
        by naive_solver eauto using BBits_refine_inv_r.
      rewrite bit_size_of_int, int_width_char in Hbs1, Hbs2.
      erewrite base_val_unflatten_byte by eauto using BIndets_refine_r_inv'.
      repeat constructor; eauto using bits_refine_valid_l,
        bits_refine_valid_r, BIndets_refine_r_inv', BIndets_refine_l_inv'.
    * erewrite base_val_unflatten_indet by eauto using BIndets_refine_l_inv'.
      by constructor.
    * assert (¬(∃ βs, bs2 = BBit <$> βs))
        by naive_solver eauto using BBits_refine_inv_r.
      rewrite bit_size_of_int in Hbs1, Hbs2.
      erewrite base_val_unflatten_int_indet by eauto; constructor; eauto.
    * destruct (BPtrs_refine_inv_l' Γ f Δ1 Δ2 pbs1 bs2) as (pbs2&->&?); auto.
      erewrite base_val_unflatten_ptr_indet_1 by
        eauto using ptr_of_bits_refine_None, Forall2_length_l.
      by constructor.
    * assert (¬(∃ pbs, bs2 = BPtr <$> pbs)).
      { intros [pbs2 ->]. destruct (BPtrs_refine_inv_r' Γ f Δ1 Δ2 bs1 pbs2)
          as (?&->&?); eauto. }
      erewrite base_val_unflatten_ptr_indet_2 by eauto. by constructor. }
  feed destruct (base_val_unflatten_spec Γ τb bs1)
    as [|τi βs1|τ p1 pbs1|bs1|bs1|τi bs1|τ pbs1|τ bs1]; auto.
  * constructor.
  * rewrite (BBits_refine_inv_l Γ true f Δ1 Δ2 βs1 bs2),
      base_val_unflatten_int by done.
    constructor. by apply int_of_bits_typed.
  * destruct (decide (ptr_alive Δ1 p1)).
    { destruct (BPtrs_refine_inv_l Γ true f Δ1 Δ2 pbs1 bs2) as (pbs2&->&?); auto.
      { erewrite <-ptr_to_of_bits by eauto using BPtrs_valid_inv,
          bits_refine_valid_l; eauto using ptr_to_bits_alive. }
      destruct (ptr_of_bits_refine Γ true f Δ1 Δ2 τ pbs1 pbs2 p1)
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
    destruct (decide (Forall (BIndet =.) bs2)).
    { econstructor; eauto using base_val_unflatten_typed, bits_refine_valid_r.
      constructor; eauto using bits_refine_valid_l. }
    rewrite base_val_unflatten_byte by done.
    repeat constructor; eauto using bits_refine_valid_l, bits_refine_valid_r.
  * destruct (decide (∃ βs, bs2 = BBit <$> βs)) as [[βs2 ->]|?].
    { rewrite fmap_length, bit_size_of_int in Hbs2.
      rewrite base_val_unflatten_int by done.
      constructor; auto; constructor; auto using int_of_bits_typed. }
    destruct (decide (Forall (BIndet =.) bs2)).
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
Lemma base_val_freeze_refine_l Γ Δ vb τb :
  (Γ,Δ) ⊢ vb : τb → freeze true vb ⊑{Γ,true@Δ} vb : τb.
Proof.
  destruct 1; refine_constructor; eauto using ptr_freeze_refine_l,
    bits_refine_id, char_byte_valid_bits_valid.
Qed.
End base_values.
