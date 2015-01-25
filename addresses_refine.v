(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export addresses refinements.
Require Import pointer_casts.
Local Open Scope ctype_scope.

Inductive ref_refine `{Env Ti} (sz : nat) :
     bool → ref Ti → ref Ti → nat → ref Ti → nat → Prop :=
  | ref_refine_perm r i :
     ref_refine sz false [] r i r i
  | ref_refine_nil r1 i1 r2 i2 :
     ref_base r1 ⊆* r2 → i2 = i1 + sz * ref_offset r1 →
     ref_refine sz true r1 [] i1 r2 i2
  | ref_refine_ne_nil r1' r1 r2 i :
     r1 ++ r1' ⊆* r2 → r1 ≠ [] →
     ref_refine sz true r1' r1 i r2 i.
Inductive addr_refine' `{Env Ti} (Γ : env Ti) (α : bool) (f : meminj Ti)
      (Γm1 Γm2 : memenv Ti) : addr Ti → addr Ti → ptr_type Ti → Prop :=
  | Addr_refine' o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp :
     Γm1 ⊑{Γ,α,f} Γm2 →
     f !! o1 = Some (o2,r') →
     Γm1 ⊢ o1 : τ1 →
     ✓{Γ} τ2 →
     int_typed (size_of Γ τ2) sptrT →
     Γ ⊢ r' : τ2 ↣ τ1 → Γ ⊢ r1 : τ1 ↣ σ →
     ref_offset r1 = 0 →
     i1 ≤ size_of Γ σ * ref_size r1 →
     i1 `mod` ptr_size_of Γ σp = 0 →
     σ >*> σp →
     ref_refine (size_of Γ σ) α r' r1 i1 r2 i2 →
     addr_refine' Γ α f Γm1 Γm2
       (Addr o1 r1 i1 τ1 σ σp) (Addr o2 r2 i2 τ2 σ σp) σp.
Instance addr_refine `{Env Ti} :
  RefineT Ti (env Ti) (ptr_type Ti) (addr Ti) := addr_refine'.

Section addresses.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ σ : type Ti.
Implicit Types τp σp : ptr_type Ti.
Implicit Types r : ref Ti.
Implicit Types a : addr Ti.
Implicit Types α : bool.

Lemma addr_refine_memenv_refine Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → Γm1 ⊑{Γ,α,f} Γm2.
Proof. by destruct 1. Qed.
Lemma addr_refine_typed_l Γ α f Γm1 Γm2 a1 a2 σp :
  ✓ Γ → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → (Γ,Γm1) ⊢ a1 : σp.
Proof.
  intros ?. assert (∀ r τ1 τ2, ✓{Γ} τ1 → Γ ⊢ r : τ1 ↣ τ2 →
    int_typed (size_of Γ τ1) sptrT → int_typed (size_of Γ τ2) sptrT).
  { intros r τ1 τ2 ?? [_ ?]; split.
    { transitivity 0; auto using int_lower_nonpos with zpos. }
    apply Z.le_lt_trans with (size_of Γ τ1); [apply Nat2Z.inj_le|done].
    eauto using size_of_ref'. }
  destruct 1; constructor; eauto using ref_typed_type_valid.
Qed.
Lemma addr_refine_typed_r Γ α f Γm1 Γm2 a1 a2 σp :
  ✓ Γ → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → (Γ,Γm2) ⊢ a2 : σp.
Proof.
  destruct 2 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp HΓm ?????????? Hr].
  assert (ref_offset r' < ref_size r') by eauto using ref_typed_size.
  constructor; auto.
  * by destruct (memenv_refine_typed_l HΓm o1 o2 r' τ1) 
      as (?&?&?); simplify_type_equality'.
  * destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_type_equality'; auto.
    + eapply ref_typed_le; [|eauto]. apply ref_set_offset_typed; auto with lia.
    + eapply ref_typed_le; rewrite ?ref_typed_app; eauto.
  * destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_equality'; auto.
    + by erewrite <-ref_offset_le, ref_offset_set_offset by eauto with lia.
    + erewrite <-ref_offset_le by eauto. by destruct r1.
  * destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_equality'; auto.
    + erewrite <-ref_size_le, ref_size_set_offset by eauto.
      transitivity (size_of Γ σ * S (ref_offset r1)); [lia|].
      apply Nat.mul_le_mono_l; lia.
    + erewrite <-ref_size_le by eauto. by destruct r1.
  * destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_equality'; auto.
    destruct (castable_divide Γ σ σp) as [z ->]; auto.
    destruct σp as [σ'|]; auto.
    by rewrite <-Nat.mul_assoc,
      (Nat.mul_comm (ptr_size_of _ _)), Nat.mul_assoc, Nat.mod_add
      by eauto using size_of_ne_0, castable_type_valid, ref_typed_type_valid.
Qed.
Lemma addr_refine_type_of_l Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → type_of a1 = σp.
Proof. by destruct 1. Qed.
Lemma addr_refine_type_of_r Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → type_of a2 = σp.
Proof. by destruct 1. Qed.
Lemma addr_refine_frozen Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → frozen a2 → frozen a1.
Proof.
  unfold frozen. destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ??????????? Hr];
    destruct Hr as [|r1 i1 r2 i2|]; intros; list_simplifier;
    f_equal; eauto using ref_frozen_le, ref_freeze_freeze.
Qed.
Lemma ref_refine_id sz α r i : ref_refine sz α [] r i r i.
Proof.
  destruct α; [|constructor].
  destruct (decide (r = [])) as [->|];
    constructor; csimpl; rewrite ?(right_id_L [] (++)); auto with lia.
Qed.
Lemma addr_refine_id Γ α Γm a σp : (Γ,Γm) ⊢ a : σp → a ⊑{Γ,α@Γm} a : σp.
Proof.
  destruct 1 as [o r i τ σ σp].
  eexists []; csimpl; auto using memenv_refine_id, ref_refine_id.
  by apply ref_typed_nil.
Qed.
Lemma addr_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 a1 a2 a3 σp σp' :
  ✓ Γ → a1 ⊑{Γ,α1,f1@Γm1↦Γm2} a2 : σp → a2 ⊑{Γ,α2,f2@Γm2↦Γm3} a3 : σp' →
  a1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} a3 : σp.
Proof.
  destruct 2 as [o1 o2 r1 r1' r2 i1 i2 τ1 τ2 σ σp ??????????? Hr3];
    inversion 1 as [? o3 ? r2' r3 ? i3 ? τ3 ????????????? Hr5]; subst.
  exists (r1' ++ r2'); eauto using memenv_refine_compose.
  { by rewrite lookup_meminj_compose; simplify_option_equality. }
  { rewrite ref_typed_app; eauto. }
  destruct Hr3 as [r1 i|r1 i1 r2 i2|r1' r1 r2 i]; inversion Hr5;
    simplify_type_equality'; rewrite ?(right_id_L [] (++)); try by constructor.
  * destruct r1; decompose_Forall_hyps. constructor; auto with lia.
  * destruct r1; decompose_Forall_hyps.
    constructor; simpl; auto. constructor; [etransitivity; eauto|].
    apply Forall2_app; [etransitivity; eauto|eauto].
  * destruct r1; decompose_Forall_hyps.
  * constructor; auto. transitivity (r2 ++ r2'); auto.
    by rewrite (associative_L (++)); apply Forall2_app.
Qed.
Lemma addr_refine_inverse Γ f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,false,f@Γm1↦Γm2} a2 : σp →
  a2 ⊑{Γ,false,meminj_inverse f@Γm2↦Γm1} a1 : σp.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ??????????? Hr].
  inversion Hr; destruct (memenv_refine_perm_l Γ f Γm1 Γm2 o1 τ1)
    as (?&?&?); auto; simplify_type_equality'.
  refine_constructor; eauto using lookup_meminj_inverse_2,
    memenv_refine_inverse, ref_typed_nil_2.
Qed.
Lemma addr_refine_weaken Γ Γ' α α' f f' Γm1 Γm2 Γm1' Γm2' a1 a2 σp :
  ✓ Γ → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp →
  Γ ⊆ Γ' → (α → α') → Γm1' ⊑{Γ',α',f'} Γm2' →
  Γm1 ⇒ₘ Γm1' → meminj_extend f f' Γm1 Γm2 → a1 ⊑{Γ',α',f'@Γm1'↦Γm2'} a2 : σp.
Proof.
  destruct 2 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ??????????? Hr];
    intros ??? [??] [??];
    refine_constructor; eauto using type_valid_weaken, ref_typed_weaken.
  * eauto using option_eq_1_alt.
  * by erewrite <-size_of_weaken by eauto.
  * by erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
  * destruct σp as [σ'|]; simpl; auto. by erewrite <-size_of_weaken
      by eauto using ref_typed_type_valid, castable_type_valid.
  * erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
    destruct Hr, α'; csimpl in *; try tauto || constructor (done).
    apply ref_refine_id.
Qed.
(* only holds for renamings because of end-of-array pointers *)
Lemma addr_refine_unique_l Γ f Γm1 Γm2 a1 a2 a3 σp2 σp3 :
  a1 ⊑{Γ,false,f@Γm1↦Γm2} a3 : σp2 → a2 ⊑{Γ,false,f@Γm1↦Γm2} a3 : σp3 → a1 = a2.
Proof.
  destruct 1 as [o1 o2 r r2 r3 i i3 τ τ2 σ σp ??? _ _ _ _ _ _ _ _ Hr];
    inversion 1 as [o1' o2' r' r2' ? i' ? τ' ??? _ ?? _ _ _ _ _ _ _ _ Hr'];
    inversion Hr; inversion Hr'; simplify_equality.
  destruct (meminj_injective_alt f o1 o1' o2 [] []) as [?|[_ ?]];
    eauto using memenv_refine_injective; simplify_type_equality; auto.
  by destruct (ref_disjoint_nil_inv_l (@nil (ref_seg Ti))).
Qed.
Lemma addr_refine_unique_r Γ α f Γm1 Γm2 a1 a2 a3 σp2 σp3 :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp2 → a1 ⊑{Γ,α,f@Γm1↦Γm2} a3 : σp3 →
  frozen a2 → frozen a3 → a2 = a3.
Proof.
  unfold frozen; destruct 1 as [?????????????????????? Hr1];
    inversion 1 as [?????????????????????? Hr2]; destruct Hr1; inversion Hr2;
    intros; simplify_type_equality'; f_equal; eauto using ref_le_unique_alt.
Qed.
Lemma addr_freeze_refine_l Γ Γm a σp :
  (Γ,Γm) ⊢ a : σp → freeze true a ⊑{Γ,true@Γm} a : σp.
Proof.
  destruct 1. eexists []; csimpl; auto using memenv_refine_id.
  * by apply ref_typed_nil.
  * eauto using ref_typed_ge, ref_freeze_le_l.
  * by rewrite ref_offset_freeze.
  * by rewrite ref_size_freeze.
  * destruct (decide (r = [])) as [->|]; [constructor; simpl; auto with lia|].
    constructor. rewrite (right_id_L [] (++)); auto using ref_freeze_le_l.
    by destruct r.
Qed.
Lemma addr_freeze_refine Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp →
  freeze true a1 ⊑{Γ,α,f@Γm1↦Γm2} freeze true a2 : σp.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp HΓm ?????????? Hr];
    csimpl; refine_constructor; eauto.
  { by apply ref_typed_freeze. }
  { by rewrite ref_offset_freeze. }
  { by rewrite ref_size_freeze. }
  destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; constructor; auto.
  * erewrite <-(memenv_refine_frozen _ _ _ _ _ HΓm _ _ r1) by eauto.
    by erewrite ref_set_offset_freeze, ref_freeze_le by eauto.
  * erewrite <-(memenv_refine_frozen _ _ _ _ _ HΓm _ _ r1'),<-fmap_app by eauto.
    by erewrite ref_freeze_le by eauto.
  * by destruct r1.
Qed.
Lemma addr_ref_refine Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → addr_strict Γ a1 →
  ∃ r, f !! addr_index a1 = Some (addr_index a2, r) ∧
    Γ ⊢ r : addr_type_object a2 ↣ addr_type_object a1 ∧
    addr_ref Γ a1 ++ r ⊆* addr_ref Γ a2.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ' ???????????? Hr];
    intros; simplify_equality'; exists r'; split_ands; auto.
  destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_type_equality'; auto.
  * by rewrite (right_id_L [] (++)).
  * rewrite Nat.mul_comm, Nat.div_add, Nat.div_small, Nat.add_0_l by lia.
    rewrite <-(ref_set_offset_offset r1) at 1.
    rewrite <-(ref_set_offset_set_offset r1 _ 0); auto using ref_set_offset_le.
  * destruct r1; decompose_Forall_hyps.
    constructor; auto using Forall2_app, ref_seg_set_offset_le.
Qed.
Lemma addr_ref_byte_refine Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → addr_strict Γ a1 →
  addr_ref_byte Γ a1 = addr_ref_byte Γ a2.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ' ???????????? Hr];
    intros; destruct Hr; simplify_equality'; auto.
  by rewrite Nat.mul_comm, Nat.mod_add by lia.
Qed.
Lemma addr_is_obj_refine Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → addr_is_obj a1 ↔ addr_is_obj a2.
Proof. by destruct 1. Qed.
Lemma addr_disjoint_refine Γ α α' f Γm1 Γm2 a1 a2 a3 a4 σp1 σp3 :
  ✓ Γ → meminj_injective f → addr_strict Γ a1 → addr_strict Γ a3 →
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp1 → a3 ⊑{Γ,α',f@Γm1↦Γm2} a4 : σp3 →
  a1 ⊥{Γ} a3 → a2 ⊥{Γ} a4.
Proof.
  intros ??????.
  destruct (addr_ref_refine Γ α f Γm1 Γm2 a1 a2 σp1) as (r1&Hf1&_&Hr1); auto.
  destruct (addr_ref_refine Γ α' f Γm1 Γm2 a3 a4 σp3) as (r2&Hf2&_&Hr2); auto.
  intros [?|[[Hidx ?]|(Hidx&Ha&?&?&?)]].
  * edestruct (meminj_injective_ne f (addr_index a1) (addr_index a2))
      as [|[??]]; eauto; [by left|].
    right; left; eauto using ref_disjoint_le, ref_disjoint_app.
  * rewrite Hidx in Hf1; simplify_option_equality.
    right; left; eauto using ref_disjoint_le, ref_disjoint_here_app_1.
  * rewrite Hidx in Hf1; simplify_option_equality. do 2 right; split; [done|].
    erewrite <-!(addr_ref_byte_refine _ _ _ _ _ a1 a2),
      <-!(addr_ref_byte_refine _ _ _ _ _ a3 a4),
      <-!(addr_is_obj_refine _ _ _ _ _ a1 a2),
      <-!(addr_is_obj_refine _ _ _ _ _ a3 a4) by eauto; split_ands; auto.
    transitivity (freeze true <$> addr_ref Γ a1 ++ r1);
      auto using ref_freeze_le, eq_sym.
    rewrite fmap_app, Ha, <-fmap_app; auto using ref_freeze_le.
Qed.
Lemma addr_disjoint_refine_inv Γ α α' f Γm1 Γm2 a1 a2 a3 a4 σp1 σp3 :
  ✓ Γ → addr_strict Γ a1 → addr_strict Γ a3 →
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp1 → a3 ⊑{Γ,α',f@Γm1↦Γm2} a4 : σp3 →
  a2 ⊥{Γ} a4 → a1 ⊥{Γ} a3.
Proof.
  intros ?????.
  destruct (addr_ref_refine Γ α f Γm1 Γm2 a1 a2 σp1) as (r1&Hf1&_&Hr1); auto.
  destruct (addr_ref_refine Γ α' f Γm1 Γm2 a3 a4 σp3) as (r2&Hf2&_&Hr2); auto.
  destruct (decide (addr_index a1 = addr_index a3)) as [Hidx|]; [|by left].
  intros [?|[[Hidx' ?]|(Hidx'&Ha&?&?&?)]]; [congruence| |].
  * right; left; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
    eauto using ref_disjoint_here_app_2, ref_disjoint_ge.
  * right; right; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
    erewrite !(addr_ref_byte_refine _ _ _ _ _ a1 a2),
      !(addr_ref_byte_refine _ _ _ _ _ a3 a4),
      !(addr_is_obj_refine _ _ _ _ _ a1 a2),
      !(addr_is_obj_refine _ _ _ _ _ a3 a4) by eauto; split_ands; auto.
    apply (injective (++ freeze true <$> r1)); rewrite <-!fmap_app.
    erewrite ref_freeze_le by eauto. rewrite Ha.
    eauto using ref_freeze_le, eq_sym.
Qed.
Lemma addr_byte_refine_help Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp →
  ∃ i, i + size_of Γ (addr_type_base a1) * ref_size (addr_ref_base a1)
    ≤ size_of Γ (addr_type_base a2) * ref_size (addr_ref_base a2)
  ∧ addr_byte a2 = i + addr_byte a1.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ??????????? Hr].
  destruct Hr as [|r1 i1 r2 i2 Hr|r1' r1 r2 i]; simplify_type_equality'.
  * by exists 0.
  * exists (size_of Γ σ * ref_offset r1); split; [|lia].
    erewrite <-(ref_size_le _ r2), ref_size_set_offset by eauto.
    rewrite <-Nat.mul_add_distr_l, Nat.add_comm; apply Nat.mul_le_mono_l.
    eapply Nat.le_succ_l, ref_typed_size; eauto.
  * exists 0; split; auto. erewrite <-(ref_size_le _ r2) by eauto.
    by destruct r1.
Qed.
Lemma addr_strict_refine Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp → addr_strict Γ a1 → addr_strict Γ a2.
Proof.
  intros. destruct (addr_byte_refine_help Γ α f Γm1 Γm2 a1 a2 σp)
    as (i&?&?); auto; unfold addr_strict in *; lia.
Qed.
Lemma addr_alive_refine Γ α f Γm1 Γm2 a1 a2 σp :
  index_alive Γm1 (addr_index a1) → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp →
  index_alive Γm2 (addr_index a2).
Proof. destruct 2 as [??????????? []]; eauto. Qed.
Lemma addr_object_offset_refine Γ α f Γm1 Γm2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σp →
  ∃ r, f !! addr_index a1 = Some (addr_index a2, r) ∧
    Γ ⊢ r : addr_type_object a2 ↣ addr_type_object a1 ∧
    addr_object_offset Γ a2 = addr_object_offset Γ a1 + ref_object_offset Γ r.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ' ???????????? Hr];
    intros; simplify_equality'; exists r'; split_ands; auto.
  destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_type_equality'; auto.
  * erewrite <-ref_object_offset_le by eauto.
    cut (ref_object_offset Γ (ref_base r1) + ref_offset r1 * bit_size_of Γ σ'
      = ref_object_offset Γ r1); [unfold bit_size_of; lia|].
    assert (ref_offset r1 < ref_size r1) by eauto using ref_typed_size.
    erewrite ref_object_offset_set_offset by eauto with lia; lia.
  * erewrite <-ref_object_offset_le, ref_object_offset_app by eauto; lia.
Qed.
Lemma addr_top_refine Γ α f Γm1 Γm2 o1 o2 τ :
  ✓ Γ → Γm1 ⊑{Γ,α,f} Γm2 → Γm1 ⊢ o1 : τ → f !! o1 = Some (o2,[]) →
  ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  addr_top o1 τ ⊑{Γ,α,f@Γm1↦Γm2} addr_top o2 τ : Some τ.
Proof.
  eexists []; eauto using Nat.mod_0_l, size_of_ne_0, ref_refine_id;
    by constructor || simpl; lia.
Qed.
Lemma addr_top_array_refine Γ α f Γm1 Γm2 o1 o2 τ (n : Z) :
  ✓ Γ → Γm1 ⊑{Γ,α,f} Γm2 → Γm1 ⊢ o1 : τ.[Z.to_nat n] → f !! o1 = Some (o2,[]) →
  ✓{Γ} τ → Z.to_nat n ≠ 0 → int_typed (n * size_of Γ τ) sptrT →
  addr_top_array o1 τ n ⊑{Γ,α,f@Γm1↦Γm2} addr_top_array o2 τ n : Some τ.
Proof.
  intros. assert (0 ≤ n)%Z by (by destruct n). econstructor; simpl; eauto. 
  * apply TArray_valid; auto with lia.
  * by rewrite size_of_array, Nat2Z.inj_mul, Z2Nat.id by done.
  * by repeat typed_constructor. 
  * repeat typed_constructor; lia.
  * lia.
  * eauto using Nat.mod_0_l, size_of_ne_0.
  * constructor.
  * apply ref_refine_id.
Qed.
End addresses.
