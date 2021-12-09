(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export bits pointer_bits_refine.

Inductive bit_refine' `{Env K} (Γ : env K) (α : bool) (f : meminj K)
     (Δ1 Δ2 : memenv K) : relation (bit K) :=
  | BIndet_BIndet_refine' : bit_refine' Γ α f Δ1 Δ2 BIndet BIndet
  | BIndet_refine' b2 :
     α → ✓{Γ,Δ2} b2 → bit_refine' Γ α f Δ1 Δ2 BIndet b2
  | BBit_refine' β : bit_refine' Γ α f Δ1 Δ2 (BBit β) (BBit β)
  | BPtr_refine' pb1 pb2 :
     pb1 ⊑{Γ,α,f@Δ1↦Δ2} pb2 → bit_refine' Γ α f Δ1 Δ2 (BPtr pb1) (BPtr pb2)
  | BPtr_any_refine' pb1 b2 :
     α → ✓{Γ,Δ1} pb1 → ¬ptr_alive Δ1 (fragmented.frag_item pb1) →
     ✓{Γ,Δ2} b2 → bit_refine' Γ α f Δ1 Δ2 (BPtr pb1) b2.
#[global] Instance bit_refine `{Env K} : Refine K (env K) (bit K) := bit_refine'.

Section bits.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α β : bool.
Implicit Types βs : list bool.
Implicit Types pb : ptr_bit K.
Implicit Types b : bit K.
Implicit Types bs : list (bit K).

Lemma bit_refine_valid_l Γ α f Δ1 Δ2 b1 b2 :
  ✓ Γ → b1 ⊑{Γ,α,f@Δ1↦Δ2} b2 → ✓{Γ,Δ1} b1.
Proof. destruct 2; constructor; eauto using ptr_bit_refine_valid_l. Qed.
Lemma bits_refine_valid_l Γ α f Δ1 Δ2 bs1 bs2 :
  ✓ Γ → bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 → ✓{Γ,Δ1}* bs1.
Proof. induction 2; eauto using bit_refine_valid_l. Qed.
Lemma bit_refine_valid_r Γ α f Δ1 Δ2 b1 b2 :
  ✓ Γ → b1 ⊑{Γ,α,f@Δ1↦Δ2} b2 → ✓{Γ,Δ2} b2.
Proof. destruct 2; try constructor; eauto using ptr_bit_refine_valid_r. Qed.
Lemma bits_refine_valid_r Γ α f Δ1 Δ2 bs1 bs2 :
  ✓ Γ → bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 → ✓{Γ,Δ2}* bs2.
Proof. induction 2; eauto using bit_refine_valid_r. Qed.
Lemma bit_refine_id Γ α Δ b : ✓{Γ,Δ} b → b ⊑{Γ,α@Δ} b.
Proof.
  destruct 1; constructor; eauto using ptr_bit_refine_id, BIndet_valid.
Qed.
Lemma bits_refine_id Γ α Δ bs : ✓{Γ,Δ}* bs → bs ⊑{Γ,α@Δ}* bs.
Proof. induction 1; eauto using bit_refine_id. Qed.
Lemma bit_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 b1 b2 b3 :
  ✓ Γ → b1 ⊑{Γ,α1,f1@Δ1↦Δ2} b2 → b2 ⊑{Γ,α2,f2@Δ2↦Δ3} b3 →
  b1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} b3.
Proof.
  destruct 2 as [| | |pb1 pb2 Hpb|].
  * inversion 1; simplify_equality; constructor; auto.
  * constructor; eauto using orb_prop_intro, bit_refine_valid_r.
  * inversion 1; simplify_equality; constructor.
  * inversion 1; simplify_equality; constructor;
      eauto using ptr_bit_refine_compose, ptr_bit_refine_valid_l.
    destruct Hpb as (?&?&?&?); eauto using ptr_alive_refine.
  * constructor; eauto using bit_refine_valid_r.
Qed.
Lemma bits_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 bs1 bs2 bs3 :
  ✓ Γ → bs1 ⊑{Γ,α1,f1@Δ1↦Δ2}* bs2 → bs2 ⊑{Γ,α2,f2@Δ2↦Δ3}* bs3 →
  bs1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3}* bs3.
Proof.
  intros ? Hbs. revert bs3. induction Hbs; inversion_clear 1;
    constructor; eauto using bit_refine_compose.
Qed.
Lemma bit_refine_inverse Γ f Δ1 Δ2 b1 b2 :
  b1 ⊑{Γ,false,f@Δ1↦Δ2} b2 → b2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} b1.
Proof.
  destruct 1; try done; constructor; eauto using ptr_bit_refine_inverse.
Qed.
Lemma bits_refine_inverse Γ f Δ1 Δ2 bs1 bs2 :
  bs1 ⊑{Γ,false,f@Δ1↦Δ2}* bs2 → bs2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1}* bs1.
Proof. induction 1; eauto using bit_refine_inverse. Qed.
Lemma bit_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' b1 b2 :
  ✓ Γ → b1 ⊑{Γ,α,f@Δ1↦Δ2} b2 → Γ ⊆ Γ' → (α → α') ->
  Δ1' ⊑{Γ',α',f'} Δ2' → Δ1 ⇒ₘ Δ1' →
  Δ2 ⇒ₘ Δ2' → meminj_extend f f' Δ1 Δ2 → b1 ⊑{Γ',α',f'@Δ1'↦Δ2'} b2.
Proof.
  destruct 2 as [| | | |??? Hpb]; constructor; eauto using bit_valid_weaken,
    ptr_bit_refine_weaken, ptr_bit_valid_weaken, ptr_dead_weaken.
  destruct Hpb as (?&?&?&?); eauto using ptr_dead_weaken.
Qed.
Lemma BIndet_refine Γ Δ1 Δ2 f b :
  ✓{Γ,Δ2} b → BIndet ⊑{Γ,true,f@Δ1↦Δ2} b.
Proof. by constructor. Qed.
Lemma BIndets_refine Γ Δ1 Δ2 f bs1 bs2 :
  Forall (BIndet =.) bs1 → ✓{Γ,Δ2}* bs2 →
  length bs1 = length bs2 → bs1 ⊑{Γ,true,f@Δ1↦Δ2}* bs2.
Proof.
  rewrite <-Forall2_same_length.
  induction 3; decompose_Forall_hyps; repeat constructor; auto.
Qed.
Lemma BIndet_BIndet_refine Γ α f Δ1 Δ2 : BIndet ⊑{Γ,α,f@Δ1↦Δ2} BIndet.
Proof. repeat constructor. Qed.
Lemma BBit_refine Γ α f Δ1 Δ2 β : BBit β ⊑{Γ,α,f@Δ1↦Δ2} BBit β.
Proof. by constructor. Qed.
Lemma BPtr_refine Γ α f Δ1 Δ2 pb1 pb2 :
  pb1 ⊑{Γ,α,f@Δ1↦Δ2} pb2 → BPtr pb1 ⊑{Γ,α,f@Δ1↦Δ2} BPtr pb2.
Proof. by constructor. Qed.
Lemma BBits_refine Γ α f Δ1 Δ2 βs :
  BBit <$> βs ⊑{Γ,α,f@Δ1↦Δ2}* BBit <$> βs.
Proof. induction βs; constructor; auto using BBit_refine. Qed.
Lemma BPtrs_refine Γ α f Δ1 Δ2 pbs1 pbs2 :
  pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs2 → BPtr <$> pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* BPtr <$> pbs2.
Proof. induction 1; constructor; auto using BPtr_refine. Qed.
Lemma BIndets_refine_l_inv Γ α f Δ1 Δ2 bs1 bs2 :
  Forall (BIndet =.) bs1 → bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 → ✓{Γ,Δ2}* bs2.
Proof.
  induction 2 as [|???? []]; decompose_Forall_hyps; repeat constructor; eauto.
Qed.
Lemma BIndets_refine_l_inv' Γ f Δ1 Δ2 bs1 bs2 :
  Forall (BIndet =.) bs1 → bs1 ⊑{Γ,false,f@Δ1↦Δ2}* bs2 → Forall (BIndet =.) bs2.
Proof.
  by induction 2 as [|????[]]; decompose_Forall_hyps; repeat constructor; eauto.
Qed.
Lemma BIndet_refine_r_inv Γ α f Δ1 Δ2 b1 b3 :
  b1 ⊑{Γ,α,f@Δ1↦Δ2} BIndet → ✓{Γ,Δ2} b3 → b1 ⊑{Γ,true,f@Δ1↦Δ2} b3.
Proof. by inversion 1; constructor; auto. Qed.
Lemma BIndets_refine_r_inv Γ α f Δ1 Δ2 bs1 bs2 bs3 :
  bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 → Forall (BIndet =.) bs2 →
  ✓{Γ,Δ2}* bs3 → length bs1 = length bs3 → bs1 ⊑{Γ,true,f@Δ1↦Δ2}* bs3.
Proof.
  rewrite <-Forall2_same_length. intros Hbs Hbs2. revert bs3.
  induction Hbs; intros; decompose_Forall_hyps; eauto using BIndet_refine_r_inv.
Qed.
Lemma BIndets_refine_r_inv' Γ f Δ1 Δ2 bs1 bs2 bs3 :
  Forall (BIndet =.) bs2 → bs1 ⊑{Γ,false,f@Δ1↦Δ2}* bs2 → Forall (BIndet =.) bs1.
Proof.
  by induction 2 as [|????[]]; decompose_Forall_hyps; repeat constructor; eauto.
Qed.
Lemma BBits_refine_inv_l Γ α f Δ1 Δ2 βs bs :
  BBit <$> βs ⊑{Γ,α,f@Δ1↦Δ2}* bs → bs = BBit <$> βs.
Proof.
  rewrite Forall2_fmap_l.
  by induction 1 as [|???? Hb]; [|inversion Hb]; simplify_equality'.
Qed.
Lemma BBits_refine_inv_r Γ f Δ1 Δ2 βs bs :
  bs ⊑{Γ,false,f@Δ1↦Δ2}* BBit <$> βs → bs = BBit <$> βs.
Proof.
  rewrite Forall2_fmap_r.
  by induction 1 as [|???? Hb]; [|inversion Hb]; simplify_equality'.
Qed.
Lemma BPtrs_any_refine Γ f Δ1 Δ2 pbs1 bs2 :
  ✓{Γ,Δ1}* pbs1 →
  Forall (λ pb, ¬ptr_alive Δ1 (fragmented.frag_item pb)) pbs1 → ✓{Γ,Δ2}* bs2 →
  length pbs1 = length bs2 → BPtr <$> pbs1 ⊑{Γ,true,f@Δ1↦Δ2}* bs2.
Proof.
  rewrite <-Forall2_same_length.
  induction 4; decompose_Forall_hyps; repeat constructor; auto.
Qed.
Lemma BPtrs_refine_inv_l Γ α f Δ1 Δ2 pbs1 bs2 :
  BPtr <$> pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2 →
  Forall (λ pb, ptr_alive Δ1 (fragmented.frag_item pb)) pbs1 →
  ∃ pbs2, bs2 = BPtr <$> pbs2 ∧ pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs2.
Proof.
  rewrite Forall2_fmap_l.
  induction 1 as [|pb1 b2 pbs1 bs2 Hb ? IH]; intros; decompose_Forall_hyps.
  { by eexists []. }
  destruct IH as (pbs2&->&?); auto. inversion Hb; simplify_equality'; try done.
  eexists (_ :: _); csimpl; eauto.
Qed.
Lemma BPtrs_refine_inv_l' Γ f Δ1 Δ2 pbs1 bs2 :
  BPtr <$> pbs1 ⊑{Γ,false,f@Δ1↦Δ2}* bs2 →
  ∃ pbs2, bs2 = BPtr <$> pbs2 ∧ pbs1 ⊑{Γ,false,f@Δ1↦Δ2}* pbs2.
Proof.
  rewrite Forall2_fmap_l.
  induction 1 as [|pb1 b2 pbs1 bs2 Hb ? IH]; intros; [by eexists []|].
  inversion Hb; simplify_equality'; try done.
  destruct IH as (pbs2&->&?); auto. eexists (_ :: _); csimpl; eauto.
Qed.
Lemma BPtrs_refine_inv_r Γ α f Δ1 Δ2 bs1 pbs2 :
  ¬(∃ pbs, bs1 = BPtr <$> pbs) → bs1 ⊑{Γ,α,f@Δ1↦Δ2}* BPtr <$> pbs2 →
  Exists (✓{Γ,Δ2}) pbs2.
Proof.
  intros Hbps. rewrite Forall2_fmap_r. induction 1 as [|???? Hb ? IH].
  { destruct Hbps. by eexists []. }
  inversion Hb; subst; eauto using BPtr_valid_inv.
  right; apply IH; intros [?->]. destruct Hbps; eexists (_ :: _); csimpl; eauto.
Qed.
Lemma BPtrs_refine_inv_r' Γ f Δ1 Δ2 bs1 pbs2 :
  bs1 ⊑{Γ,false,f@Δ1↦Δ2}* BPtr <$> pbs2 →
  ∃ pbs1, bs1 = BPtr <$> pbs1 ∧ pbs1 ⊑{Γ,false,f@Δ1↦Δ2}* pbs2.
Proof.
  rewrite Forall2_fmap_r.
  induction 1 as [|pb1 b2 pbs1 bs2 Hb ? IH]; intros; [by eexists []|].
  inversion Hb; simplify_equality'; try done.
  destruct IH as (pbs2&->&?); auto. eexists (_ :: _); csimpl; eauto.
Qed.
Lemma bit_subseteq_refine Γ Δ b1 b2 :
  ✓{Γ,Δ} b2 → bit_weak_refine b1 b2 → b1 ⊑{Γ,true@Δ} b2.
Proof. destruct 2; eauto using BIndet_refine, bit_refine_id. Qed.
Lemma bits_subseteq_refine Γ Δ bs1 bs2 :
  ✓{Γ,Δ}* bs2 → Forall2 bit_weak_refine bs1 bs2 → bs1 ⊑{Γ,true@Δ}* bs2.
Proof. induction 2; decompose_Forall_hyps; eauto using bit_subseteq_refine. Qed.
Lemma bit_join_refine Γ α f Δ1 Δ2 b1 b2 b3 b1' b2' b3' :
  bit_join b1 b2 = Some b3 → bit_join b1' b2' = Some b3' →
  b1 ⊑{Γ,α,f@Δ1↦Δ2} b1' → b2 ⊑{Γ,α,f@Δ1↦Δ2} b2' → b3 ⊑{Γ,α,f@Δ1↦Δ2} b3'.
Proof.
  destruct 3, 1; repeat
    match goal with
    | H : bit_join ?b _ = _ |- _ => is_var b; destruct b
    | H : bit_join _ ?b = _ |- _ => is_var b; destruct b
    | _ => case_option_guard || simplify_equality' || (constructor; assumption)
    end.
Qed.
Lemma bits_join_refine Γ α f Δ1 Δ2 bs1 bs2 bs3 bs1' bs2' bs3' :
  bits_join bs1 bs2 = Some bs3 → bits_join bs1' bs2' = Some bs3' →
  bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs1' → bs2 ⊑{Γ,α,f@Δ1↦Δ2}* bs2' →
  bs3 ⊑{Γ,α,f@Δ1↦Δ2}* bs3'.
Proof.
  intros Hbs Hbs' Hbs1. revert bs2 bs2' bs3 bs3' Hbs Hbs'.
  induction Hbs1; destruct 3; simplify_option_eq;
    constructor; eauto using bit_join_refine.
Qed.
Lemma bits_list_join_refine Γ α f Δ1 Δ2 sz bss1 bss2 bs1 bs2 :
  bits_list_join sz bss1 = Some bs1 → bits_list_join sz bss2 = Some bs2 →
  Forall2 (Forall2 (refine Γ α f Δ1 Δ2)) bss1 bss2 →
  bs1 ⊑{Γ,α,f@Δ1↦Δ2}* bs2.
Proof.
  intros Hbs1 Hbs2 Hbss. revert bs1 bs2 Hbs1 Hbs2.
  induction Hbss; intros; simplify_option_eq; eauto using
    bits_join_refine, Forall2_replicate, Forall2_resize, BIndet_BIndet_refine.
Qed.
End bits.
