(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import fragmented.
Require Export pointer_bits pointers_refine.

#[global] Instance ptr_bit_refine `{Env K} :
    Refine K (env K) (ptr_bit K) := λ Γ α f Δ1 Δ2 pb1 pb2, ∃ τp,
  frag_item pb1 ⊑{Γ,α,f@Δ1↦Δ2} frag_item pb2 : τp ∧
  frag_index pb1 = frag_index pb2 ∧
  frozen (frag_item pb2) ∧
  frag_index pb1 < bit_size_of Γ (τp.*).

Section pointer_bits.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α : bool.
Implicit Types τp : ptr_type K.
Implicit Types p : ptr K.
Implicit Types pb : ptr_bit K.
Implicit Types pbs : list (ptr_bit K).

Lemma ptr_bit_refine_id Γ α Δ pb : ✓{Γ,Δ} pb → pb ⊑{Γ,α@Δ} pb.
Proof. intros (σ&?&?&?); exists σ; eauto using ptr_refine_id. Qed.
Lemma ptr_bit_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 pb1 pb2 pb3 :
  ✓ Γ → pb1 ⊑{Γ,α1,f1@Δ1↦Δ2} pb2 → pb2 ⊑{Γ,α2,f2@Δ2↦Δ3} pb3 →
  pb1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} pb3.
Proof.
  intros ? (τp1&?&?&?&?) (τp2&?&?&?&?); exists τp1.
  assert (τp1 = τp2) by (by erewrite <-(ptr_refine_type_of_r _ _ _ _ _ _ _ τp1),
    <-(ptr_refine_type_of_l _ _ _ _ _ _ _ τp2) by eauto); subst.
  eauto using ptr_refine_compose with congruence.
Qed.
Lemma ptr_bit_refine_inverse Γ f Δ1 Δ2 pb1 pb2 :
  pb1 ⊑{Γ,false,f@Δ1↦Δ2} pb2 → pb2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} pb1.
Proof.
  intros (τp&?&?&?&?); exists τp; split_and ?; eauto using ptr_refine_inverse,
    ptr_refine_frozen with congruence.
Qed.
Lemma ptr_bit_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' pb1 pb2 :
  ✓ Γ → pb1 ⊑{Γ,α,f@Δ1↦Δ2} pb2 → Γ ⊆ Γ' → (α → α') → Δ1' ⊑{Γ',α',f'} Δ2' →
  Δ1 ⇒ₘ Δ1' → meminj_extend f f' Δ1 Δ2 → pb1 ⊑{Γ',α',f'@Δ1'↦Δ2'} pb2.
Proof.
  intros ? (τp&?&?&?&?) ??. exists τp.
  erewrite <-bit_size_of_weaken by eauto using TBase_valid, TPtr_valid,
    ptr_refine_typed_l, ptr_typed_type_valid; eauto using ptr_refine_weaken.
Qed.
Lemma ptr_bit_refine_valid_l Γ α f Δ1 Δ2 pb1 pb2 :
  ✓ Γ → pb1 ⊑{Γ,α,f@Δ1↦Δ2} pb2 → ✓{Γ,Δ1} pb1.
Proof.
  intros ? (τp&?&?&?&?).
  exists τp; eauto using ptr_refine_typed_l, ptr_refine_frozen.
Qed.
Lemma ptr_bit_refine_valid_r Γ α Δ1 Δ2 f pb1 pb2 :
  ✓ Γ → pb1 ⊑{Γ,α,f@Δ1↦Δ2} pb2 → ✓{Γ,Δ2} pb2.
Proof.
  intros ? (τp&?&?&?&?); exists τp;
    eauto using ptr_refine_typed_r with congruence.
Qed.
Lemma ptr_bits_refine_valid_l Γ α f Δ1 Δ2 pbs1 pbs2 :
  ✓ Γ → pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs2 → ✓{Γ,Δ1}* pbs1.
Proof. induction 2; eauto using ptr_bit_refine_valid_l. Qed.
Lemma ptr_bits_refine_valid_r Γ α f Δ1 Δ2 pbs1 pbs2 :
  ✓ Γ → pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs2 → ✓{Γ,Δ2}* pbs2.
Proof. induction 2; eauto using ptr_bit_refine_valid_r. Qed.
Lemma ptr_bit_refine_unique_l Γ f Δ1 Δ2 pb1 pb2 pb3 :
  pb1 ⊑{Γ,false,f@Δ1↦Δ2} pb3 → pb2 ⊑{Γ,false,f@Δ1↦Δ2} pb3 → pb1 = pb2.
Proof.
  destruct pb1, pb2; intros (τp1&?&?&?&?) (τp2&?&?&?&?);
    f_equal'; eauto using ptr_refine_unique_l with congruence.
Qed.
Lemma ptr_bits_refine_unique_l Γ f Δ1 Δ2 pbs1 pbs2 pbs3 :
  pbs1 ⊑{Γ,false,f@Δ1↦Δ2}* pbs3 → pbs2 ⊑{Γ,false,f@Δ1↦Δ2}* pbs3 →
  pbs1 = pbs2.
Proof.
  intros Hpbs. revert pbs2. induction Hpbs; inversion_clear 1;
    f_equal; eauto using ptr_bit_refine_unique_l.
Qed.
Lemma ptr_bit_refine_unique_r Γ α f Δ1 Δ2 pb1 pb2 pb3 :
  pb1 ⊑{Γ,α,f@Δ1↦Δ2} pb2 → pb1 ⊑{Γ,α,f@Δ1↦Δ2} pb3 → pb2 = pb3.
Proof.
  destruct pb2, pb3; intros (τp1&?&?&?&?) (τp2&?&?&?&?);
    f_equal'; eauto using ptr_refine_unique_r with congruence.
Qed.
Lemma ptr_bits_refine_unique_r Γ α f Δ1 Δ2 pbs1 pbs2 pbs3 :
  pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs2 → pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs3 → pbs2 = pbs3.
Proof.
  intros Hpbs. revert pbs3. induction Hpbs; inversion_clear 1;
    f_equal; eauto using ptr_bit_refine_unique_r.
Qed.
Lemma ptr_to_bits_refine Γ α f Δ1 Δ2 p1 p2 σ :
  p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : σ →
  ptr_to_bits Γ p1 ⊑{Γ,α,f@Δ1↦Δ2}* ptr_to_bits Γ p2.
Proof.
  intros. unfold ptr_to_bits, to_fragments.
  erewrite ptr_refine_type_of_l, ptr_refine_type_of_r by eauto.
  apply Forall2_fmap, Forall_Forall2_diag, Forall_seq; intros j [??].
  exists σ; simpl; split_and ?; unfold frozen; auto using ptr_freeze_freeze.
  by apply ptr_freeze_refine.
Qed.
Lemma ptr_of_bits_refine Γ α f Δ1 Δ2 σ pbs1 pbs2 p1 :
  ptr_of_bits Γ σ pbs1 = Some p1 → pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs2 →
  ∃ p2, ptr_of_bits Γ σ pbs2 = Some p2 ∧ p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : σ.
Proof.
  revert pbs1 pbs2 p1. assert (∀ p1 p2 pbs1 pbs2,
    p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : σ → frozen p2 → pbs1 ⊑{Γ,α,f@Δ1↦Δ2}* pbs2 →
    fragmented (bit_size_of Γ (σ.*)) p1 1 pbs1 →
    fragmented (bit_size_of Γ (σ.*)) p2 1 pbs2).
  { intros p1 p2 pbs1 pbs2 ??? ->.
    apply (ptr_bits_refine_unique_r Γ α f Δ1 Δ2
      (Fragment p1 <$> seq 1 (bit_size_of Γ (σ.*) - 1))); [done|].
    apply Forall2_fmap, Forall_Forall2_diag, Forall_seq; intros j [??].
    exists σ; simpl; split_and ?; auto with lia. }
  intros pbs1 pbs2 p1; unfold ptr_of_bits. destruct 2 as
    [|[p1' []] [p2' []] ?? (?&?&?&?&?)]; simplify_option_eq;
    repeat match goal with
    | H : context [type_of ?p] |- _ =>
      erewrite ?ptr_refine_type_of_l, ?ptr_refine_type_of_r in H by eauto
    end; try done.
  * erewrite ptr_refine_type_of_l by eauto; eauto.
  * exfalso; naive_solver.
Qed.
Lemma ptr_of_bits_refine_None Γ f Δ1 Δ2 σ pbs1 pbs2 :
  ptr_of_bits Γ σ pbs1 = None → pbs1 ⊑{Γ,false,f@Δ1↦Δ2}* pbs2 →
  ptr_of_bits Γ σ pbs2 = None.
Proof.
  revert pbs1 pbs2. assert (∀ p1 p2 pbs1 pbs2,
    p1 ⊑{Γ,false,f@Δ1↦Δ2} p2 : σ → frozen p2 →
    pbs1 ⊑{Γ,false,f@Δ1↦Δ2}* pbs2 →
    fragmented (bit_size_of Γ (σ.* )) p2 1 pbs2 →
    fragmented (bit_size_of Γ (σ.* )) p1 1 pbs1).
  { intros p1 p2 pbs1 pbs2 ??? ->. red.
    apply (ptr_bits_refine_unique_l Γ f Δ1 Δ2 _ _
      (Fragment p2 <$> seq 1 (bit_size_of Γ (σ.*) - 1))); [done|].
    apply Forall2_fmap, Forall_Forall2_diag, Forall_seq; intros j [??].
    exists σ; simpl; split_and ?; auto with lia. }
  intros pbs1 pbs2; unfold ptr_of_bits. destruct 2 as
    [|[p1' []] [p2' []] ?? (?&?&?&?&?)]; simplify_option_eq;
    repeat match goal with
    | H : context [type_of ?p] |- _ =>
      erewrite ?ptr_refine_type_of_l, ?ptr_refine_type_of_r in H by eauto
    end; naive_solver.
Qed.
End pointer_bits.
