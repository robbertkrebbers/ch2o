(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export addresses refinements.
Require Import pointer_casts.
Local Open Scope ctype_scope.

Inductive ref_refine `{Env K} (sz : nat) :
     bool → ref K → ref K → nat → ref K → nat → Prop :=
  | ref_refine_perm r i :
     ref_refine sz false [] r i r i
  | ref_refine_nil r1 i1 r2 i2 :
     ref_base r1 ⊆* r2 → i2 = i1 + sz * ref_offset r1 →
     ref_refine sz true r1 [] i1 r2 i2
  | ref_refine_ne_nil r1' r1 r2 i :
     r1 ++ r1' ⊆* r2 → r1 ≠ [] →
     ref_refine sz true r1' r1 i r2 i.
Inductive addr_refine' `{Env K} (Γ : env K) (α : bool) (f : meminj K)
      (Δ1 Δ2 : memenv K) : addr K → addr K → ptr_type K → Prop :=
  | Addr_refine' o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp :
     Δ1 ⊑{Γ,α,f} Δ2 →
     f !! o1 = Some (o2,r') →
     Δ1 ⊢ o1 : τ1 →
     ✓{Γ} τ2 →
     Γ ⊢ r' : τ2 ↣ τ1 → Γ ⊢ r1 : τ1 ↣ σ →
     ref_offset r1 = 0 →
     i1 ≤ size_of Γ σ * ref_size r1 →
     (ptr_size_of Γ σp | i1) →
     σ >*> σp →
     ref_refine (size_of Γ σ) α r' r1 i1 r2 i2 →
     addr_refine' Γ α f Δ1 Δ2
       (Addr o1 r1 i1 τ1 σ σp) (Addr o2 r2 i2 τ2 σ σp) σp.
#[global] Instance addr_refine `{Env K} :
  RefineT K (env K) (ptr_type K) (addr K) := addr_refine'.

Section addresses.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τ σ : type K.
Implicit Types τp σp : ptr_type K.
Implicit Types r : ref K.
Implicit Types a : addr K.
Implicit Types α : bool.

Arguments addr_strict _ _ _ !_ /.
Arguments addr_ref _ _ _ !_ /.
Arguments addr_ref_byte _ _ _ !_ /.
Arguments addr_object_offset _ _ _ !_ /.
Arguments addr_elt _ _ _ _ !_ /.

Lemma addr_refine_memenv_refine Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → Δ1 ⊑{Γ,α,f} Δ2.
Proof. by destruct 1. Qed.
Lemma addr_refine_typed_l Γ α f Δ1 Δ2 a1 a2 σp :
  ✓ Γ → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → (Γ,Δ1) ⊢ a1 : σp.
Proof. destruct 2; constructor; eauto using ref_typed_type_valid. Qed.
Lemma addr_refine_typed_r Γ α f Δ1 Δ2 a1 a2 σp :
  ✓ Γ → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → (Γ,Δ2) ⊢ a2 : σp.
Proof.
  destruct 2 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp HΔ ????????? Hr].
  assert (ref_offset r' < ref_size r') by eauto using ref_typed_size.
  constructor; auto.
  * by destruct (memenv_refine_typed_l HΔ o1 o2 r' τ1) 
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
  * destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_type_equality'; auto.
    destruct σp; simplify_equality';
      eauto using Nat.divide_1_l, Nat.divide_add_r, Nat.divide_trans,
      (size_of_castable _ _ (TType _)), Nat.divide_mul_l.
Qed.
Lemma addr_refine_type_of_l Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → type_of a1 = σp.
Proof. by destruct 1. Qed.
Lemma addr_refine_type_of_r Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → type_of a2 = σp.
Proof. by destruct 1. Qed.
Lemma addr_refine_frozen Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → frozen a2 → frozen a1.
Proof.
  unfold frozen. destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ?????????? Hr];
    destruct Hr as [|r1 i1 r2 i2|]; intros; list_simplifier;
    f_equal; eauto using ref_frozen_le, ref_freeze_freeze.
Qed.
Lemma ref_refine_id sz α r i : ref_refine sz α [] r i r i.
Proof.
  destruct α; [|constructor].
  destruct (decide (r = [])) as [->|];
    constructor; csimpl; rewrite ?(right_id_L [] (++)); auto with lia.
Qed.
Lemma addr_refine_id Γ α Δ a σp : (Γ,Δ) ⊢ a : σp → a ⊑{Γ,α@Δ} a : σp.
Proof.
  destruct 1 as [o r i τ σ σp].
  eexists []; csimpl; auto using memenv_refine_id, ref_refine_id.
  by apply ref_typed_nil.
Qed.
Lemma addr_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 a1 a2 a3 σp σp' :
  ✓ Γ → a1 ⊑{Γ,α1,f1@Δ1↦Δ2} a2 : σp → a2 ⊑{Γ,α2,f2@Δ2↦Δ3} a3 : σp' →
  a1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} a3 : σp.
Proof.
  destruct 2 as [o1 o2 r1 r1' r2 i1 i2 τ1 τ2 σ σp ?????????? Hr3];
    inversion 1 as [? o3 ? r2' r3 ? i3 ? τ3 ???????????? Hr5]; subst.
  exists (r1' ++ r2'); eauto using memenv_refine_compose.
  { by rewrite lookup_meminj_compose; simplify_option_eq. }
  { rewrite ref_typed_app; eauto. }
  destruct Hr3 as [r1 i|r1 i1 r2 i2|r1' r1 r2 i]; inversion Hr5;
    simplify_type_equality'; rewrite ?(right_id_L [] (++)); try by constructor.
  * destruct r1; decompose_Forall_hyps. constructor; auto with lia.
  * destruct r1; decompose_Forall_hyps.
    constructor; simpl; auto. constructor; [etransitivity; eauto|].
    apply Forall2_app; [etransitivity; eauto|eauto].
  * destruct r1; decompose_Forall_hyps.
  * constructor; auto. transitivity (r2 ++ r2'); auto.
    by rewrite (assoc_L (++)); apply Forall2_app.
Qed.
Lemma addr_refine_inverse Γ f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,false,f@Δ1↦Δ2} a2 : σp →
  a2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} a1 : σp.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ?????????? Hr].
  inversion Hr; destruct (memenv_refine_perm_l Γ f Δ1 Δ2 o1 τ1)
    as (?&?&?); auto; simplify_type_equality'.
  refine_constructor; eauto using lookup_meminj_inverse_2,
    memenv_refine_inverse, ref_typed_nil_2.
Qed.
Lemma addr_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' a1 a2 σp :
  ✓ Γ → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp →
  Γ ⊆ Γ' → (α → α') → Δ1' ⊑{Γ',α',f'} Δ2' →
  Δ1 ⇒ₘ Δ1' → meminj_extend f f' Δ1 Δ2 → a1 ⊑{Γ',α',f'@Δ1'↦Δ2'} a2 : σp.
Proof.
  destruct 2 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ?????????? Hr];
    intros ??? [??] [??];
    refine_constructor; eauto using type_valid_weaken, ref_typed_weaken.
  * eauto using option_eq_1_alt.
  * by erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
  * destruct σp; simpl; auto. by erewrite <-size_of_weaken
      by eauto using ref_typed_type_valid, castable_type_valid.
  * erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
    destruct Hr, α'; csimpl in *; try tauto || by constructor.
    apply ref_refine_id.
Qed.
(* only holds for renamings because of end-of-array pointers *)
Lemma addr_refine_unique_l Γ f Δ1 Δ2 a1 a2 a3 σp2 σp3 :
  a1 ⊑{Γ,false,f@Δ1↦Δ2} a3 : σp2 → a2 ⊑{Γ,false,f@Δ1↦Δ2} a3 : σp3 → a1 = a2.
Proof.
  destruct 1 as [o1 o2 r r2 r3 i i3 τ τ2 σ σp ??? _ _ _ _ _ _ _ Hr];
    inversion 1 as [o1' o2' r' r2' ? i' ? τ' ??? _ ?? _ _ _ _ _ _ _ Hr'];
    inversion Hr; inversion Hr'; simplify_equality.
  destruct (meminj_injective_alt f o1 o1' o2 [] []) as [?|[_ ?]];
    eauto using memenv_refine_injective; simplify_type_equality; auto.
  by destruct (ref_disjoint_nil_inv_l (@nil (ref_seg K))).
Qed.
Lemma addr_refine_unique_r Γ α f Δ1 Δ2 a1 a2 a3 σp2 σp3 :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp2 → a1 ⊑{Γ,α,f@Δ1↦Δ2} a3 : σp3 →
  frozen a2 → frozen a3 → a2 = a3.
Proof.
  unfold frozen; destruct 1 as [????????????????????? Hr1];
    inversion 1 as [????????????????????? Hr2]; destruct Hr1; inversion Hr2;
    intros; simplify_type_equality'; f_equal; eauto using ref_le_unique_alt.
Qed.
Lemma addr_freeze_refine_l Γ Δ a σp :
  (Γ,Δ) ⊢ a : σp → freeze true a ⊑{Γ,true@Δ} a : σp.
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
Lemma addr_freeze_refine Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp →
  freeze true a1 ⊑{Γ,α,f@Δ1↦Δ2} freeze true a2 : σp.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp HΔ ????????? Hr];
    csimpl; refine_constructor; eauto.
  { by apply ref_typed_freeze. }
  { by rewrite ref_offset_freeze. }
  { by rewrite ref_size_freeze. }
  destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; constructor; auto.
  * erewrite <-(memenv_refine_frozen _ _ _ _ _ HΔ _ _ r1) by eauto.
    by erewrite ref_set_offset_freeze, ref_freeze_le by eauto.
  * erewrite <-(memenv_refine_frozen _ _ _ _ _ HΔ _ _ r1'),<-fmap_app by eauto.
    by erewrite ref_freeze_le by eauto.
  * by destruct r1.
Qed.
Lemma addr_ref_refine Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → addr_strict Γ a1 →
  ∃ r, f !! addr_index a1 = Some (addr_index a2, r) ∧
    Γ ⊢ r : addr_type_object a2 ↣ addr_type_object a1 ∧
    addr_ref Γ a1 ++ r ⊆* addr_ref Γ a2.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ' ??????????? Hr];
    intros; simplify_equality'; exists r'; split_and ?; auto.
  destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_type_equality'; auto.
  * by rewrite (right_id_L [] (++)).
  * rewrite Nat.mul_comm, Nat.div_add, Nat.div_small, Nat.add_0_l by lia.
    rewrite <-(ref_set_offset_offset r1) at 1.
    rewrite <-(ref_set_offset_set_offset r1 _ 0); auto using ref_set_offset_le.
  * destruct r1; decompose_Forall_hyps.
    constructor; auto using Forall2_app, ref_seg_set_offset_le.
Qed.
Lemma addr_ref_byte_refine Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → addr_strict Γ a1 →
  addr_ref_byte Γ a1 = addr_ref_byte Γ a2.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ' ??????????? Hr];
    intros; destruct Hr; simplify_equality'; auto.
  by rewrite Nat.mul_comm, Nat.mod_add by lia.
Qed.
Lemma addr_is_obj_refine Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → addr_is_obj a1 ↔ addr_is_obj a2.
Proof. by destruct 1. Qed.
Lemma addr_disjoint_refine Γ α α' f Δ1 Δ2 a1 a2 a3 a4 σp1 σp3 :
  ✓ Γ → meminj_injective f → addr_strict Γ a1 → addr_strict Γ a3 →
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp1 → a3 ⊑{Γ,α',f@Δ1↦Δ2} a4 : σp3 →
  a1 ##{Γ} a3 → a2 ##{Γ} a4.
Proof.
  intros ??????.
  destruct (addr_ref_refine Γ α f Δ1 Δ2 a1 a2 σp1) as (r1&Hf1&_&Hr1); auto.
  destruct (addr_ref_refine Γ α' f Δ1 Δ2 a3 a4 σp3) as (r2&Hf2&_&Hr2); auto.
  intros [?|[[Hidx ?]|(Hidx&Ha&?&?&?)]].
  * edestruct (meminj_injective_ne f (addr_index a1) (addr_index a2))
      as [|[??]]; eauto; [by left|].
    right; left; eauto using ref_disjoint_le, ref_disjoint_app.
  * rewrite Hidx in Hf1; simplify_option_eq.
    right; left; eauto using ref_disjoint_le, ref_disjoint_here_app_1.
  * rewrite Hidx in Hf1; simplify_option_eq. do 2 right; split; [done|].
    erewrite <-!(addr_ref_byte_refine _ _ _ _ _ a1 a2),
      <-!(addr_ref_byte_refine _ _ _ _ _ a3 a4),
      <-!(addr_is_obj_refine _ _ _ _ _ a1 a2),
      <-!(addr_is_obj_refine _ _ _ _ _ a3 a4) by eauto; split_and ?; auto.
    transitivity (freeze true <$> addr_ref Γ a1 ++ r1);
      auto using ref_freeze_le, eq_sym.
    rewrite fmap_app, Ha, <-fmap_app; auto using ref_freeze_le.
Qed.
Lemma addr_disjoint_refine_inv Γ α α' f Δ1 Δ2 a1 a2 a3 a4 σp1 σp3 :
  ✓ Γ → addr_strict Γ a1 → addr_strict Γ a3 →
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp1 → a3 ⊑{Γ,α',f@Δ1↦Δ2} a4 : σp3 →
  a2 ##{Γ} a4 → a1 ##{Γ} a3.
Proof.
  intros ?????.
  destruct (addr_ref_refine Γ α f Δ1 Δ2 a1 a2 σp1) as (r1&Hf1&_&Hr1); auto.
  destruct (addr_ref_refine Γ α' f Δ1 Δ2 a3 a4 σp3) as (r2&Hf2&_&Hr2); auto.
  destruct (decide (addr_index a1 = addr_index a3)) as [Hidx|]; [|by left].
  intros [?|[[Hidx' ?]|(Hidx'&Ha&?&?&?)]]; [congruence| |].
  * right; left; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
    eauto using ref_disjoint_here_app_2, ref_disjoint_ge.
  * right; right; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
    erewrite !(addr_ref_byte_refine _ _ _ _ _ a1 a2),
      !(addr_ref_byte_refine _ _ _ _ _ a3 a4),
      !(addr_is_obj_refine _ _ _ _ _ a1 a2),
      !(addr_is_obj_refine _ _ _ _ _ a3 a4) by eauto; split_and ?; auto.
    apply (inj (.++ freeze true <$> r1)); rewrite <-!fmap_app.
    erewrite ref_freeze_le by eauto. rewrite Ha.
    eauto using ref_freeze_le, eq_sym.
Qed.
Lemma addr_byte_refine_help Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp →
  ∃ i, i + size_of Γ (addr_type_base a1) * ref_size (addr_ref_base a1)
    ≤ size_of Γ (addr_type_base a2) * ref_size (addr_ref_base a2)
  ∧ addr_byte a2 = i + addr_byte a1.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ σp ?????????? Hr].
  destruct Hr as [|r1 i1 r2 i2 Hr|r1' r1 r2 i]; simplify_type_equality'.
  * by exists 0.
  * exists (size_of Γ σ * ref_offset r1); split; [|lia].
    erewrite <-(ref_size_le _ r2), ref_size_set_offset by eauto.
    rewrite <-Nat.mul_add_distr_l, Nat.add_comm; apply Nat.mul_le_mono_l.
    eapply Nat.le_succ_l, ref_typed_size; eauto.
  * exists 0; split; auto. erewrite <-(ref_size_le _ r2) by eauto.
    by destruct r1.
Qed.
Lemma addr_strict_refine Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp → addr_strict Γ a1 → addr_strict Γ a2.
Proof.
  intros. destruct (addr_byte_refine_help Γ α f Δ1 Δ2 a1 a2 σp)
    as (i&?&?); auto; unfold addr_strict in *; lia.
Qed.
Lemma addr_alive_refine Γ α f Δ1 Δ2 a1 a2 σp :
  index_alive Δ1 (addr_index a1) → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp →
  index_alive Δ2 (addr_index a2).
Proof. destruct 2 as [??????????? []]; eauto. Qed.
Lemma addr_object_offset_refine Γ α f Δ1 Δ2 a1 a2 σp :
  a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : σp →
  ∃ r, f !! addr_index a1 = Some (addr_index a2, r) ∧
    Γ ⊢ r : addr_type_object a2 ↣ addr_type_object a1 ∧
    addr_object_offset Γ a2 = addr_object_offset Γ a1 + ref_object_offset Γ r.
Proof.
  destruct 1 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ' ??????????? Hr];
    intros; simplify_equality'; exists r'; split_and ?; auto.
  destruct Hr as [|r1 i1 r2 i2|r1' r1 r2 i]; simplify_type_equality'; auto.
  * erewrite <-ref_object_offset_le by eauto.
    cut (ref_object_offset Γ (ref_base r1) + ref_offset r1 * bit_size_of Γ σ'
      = ref_object_offset Γ r1); [unfold bit_size_of; lia|].
    assert (ref_offset r1 < ref_size r1) by eauto using ref_typed_size.
    erewrite ref_object_offset_set_offset by eauto with lia; lia.
  * erewrite <-ref_object_offset_le, ref_object_offset_app by eauto; lia.
Qed.
Lemma addr_elt_refine Γ α f Δ1 Δ2 a1 a2 rs σ σ' :
  ✓ Γ → a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : TType σ → addr_strict Γ a1 → Γ ⊢ rs : σ ↣ σ' →
  addr_elt Γ rs a1 ⊑{Γ,α,f@Δ1↦Δ2} addr_elt Γ rs a2 : TType σ'.
Proof.
  inversion 2 as [o1 o2 r1 r' r2 i1 i2 τ1 τ2 σ'' ?????????? Hcast Hr];
    intros ? Hrs; simplify_equality'.
  inversion Hcast; simplify_equality'; try solve [inversion Hrs].
  assert (ref_seg_offset rs < ref_seg_size rs)
    by eauto using ref_seg_typed_size.
  unfold addr_elt; simpl; 
  erewrite path_type_check_complete by eauto; econstructor; simpl; eauto.
  * apply ref_typed_cons; exists σ; split.
    + apply ref_set_offset_typed; auto.
      apply Nat.div_lt_upper_bound;
        eauto using size_of_ne_0, ref_typed_type_valid.
    + apply ref_seg_set_offset_typed; auto with lia.
  * by rewrite ref_seg_offset_set_offset by lia.
  * rewrite ref_seg_size_set_offset. apply Nat.mul_le_mono_l; lia.
  * by apply Nat.divide_mul_l.
  * constructor.
  * destruct Hr as [|r1 i1 r2 i2 Hr|r1' r1 r2 i];
      simplify_type_equality'; constructor; simpl; auto.
    { constructor; auto. rewrite (Nat.mul_comm (size_of _ _)),
        Nat.div_add, Nat.div_small, Nat.add_0_l by lia.
      rewrite <-(ref_set_offset_offset r1) at 1.
      rewrite <-(ref_set_offset_set_offset r1 _ 0).
      eauto using ref_set_offset_le. }
    constructor; auto. destruct r1; decompose_Forall_hyps;
     auto using Forall2_app, ref_seg_set_offset_le.
Qed.
Lemma addr_top_refine Γ α f Δ1 Δ2 o1 o2 τ :
  ✓ Γ → Δ1 ⊑{Γ,α,f} Δ2 → Δ1 ⊢ o1 : τ → f !! o1 = Some (o2,[]) → ✓{Γ} τ → 
  addr_top o1 τ ⊑{Γ,α,f@Δ1↦Δ2} addr_top o2 τ : TType τ.
Proof.
  eexists []; csimpl; rewrite ?ref_typed_nil; auto using Nat.divide_0_r,
    size_of_ne_0, ref_refine_id, castable_TType with lia.
Qed.
Lemma addr_top_array_refine Γ α f Δ1 Δ2 o1 o2 τ (n : Z) :
  ✓ Γ → Δ1 ⊑{Γ,α,f} Δ2 → Δ1 ⊢ o1 : τ.[Z.to_nat n] → f !! o1 = Some (o2,[]) →
  ✓{Γ} τ → Z.to_nat n ≠ 0 →
  addr_top_array o1 τ n ⊑{Γ,α,f@Δ1↦Δ2} addr_top_array o2 τ n : TType τ.
Proof.
  intros. rewrite !(addr_top_array_alt Γ) by done.
  assert (0 ≤ n)%Z by (by destruct n).
  eapply addr_elt_refine; eauto using addr_top_strict,
    addr_top_refine, TArray_valid; constructor; lia.
Qed.
End addresses.
