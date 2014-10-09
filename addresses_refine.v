(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export addresses refinements.
Require Import pointer_casts.
Local Open Scope ctype_scope.

Inductive ref_refine `{Env Ti} (r' : ref Ti) (sz : nat) :
     ref Ti → nat → ref Ti → nat → Prop :=
  | ref_refine_nil i :
     ref_refine r' sz [] i (ref_base r') (i + sz * ref_offset r')
  | ref_refine_ne_nil rs r i :
     ref_refine r' sz (rs :: r) i (rs :: r ++ r') i.
Inductive addr_refine' `{Env Ti} (Γ : env Ti) (α : bool) (f : meminj Ti)
      (Γm1 Γm2 : memenv Ti) : addr Ti → addr Ti → type Ti → Prop :=
  | Addr_refine' o o' r r' r'' i i'' τ τ' σ σc :
     Γm1 ⊑{Γ,α,f} Γm2 →
     f !! o = Some (o',r') →
     Γm1 ⊢ o : τ →
     ✓{Γ} τ' →
     int_typed (size_of Γ τ') sptrT →
     Γ ⊢ r' : τ' ↣ τ → Γ ⊢ r : τ ↣ σ →
     ref_offset r = 0 →
     i ≤ size_of Γ σ * ref_size r →
     i `mod` size_of Γ σc = 0 →
     σ >*> σc →
     ref_refine (freeze true <$> r') (size_of Γ σ) r i r'' i'' →
     addr_refine' Γ α f Γm1 Γm2
       (Addr o r i τ σ σc) (Addr o' r'' i'' τ' σ σc) σc.
Instance addr_refine `{Env Ti} :
  RefineT Ti (env Ti) (type Ti) (addr Ti) := addr_refine'.

Section addresses.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ σ : type Ti.
Implicit Types r : ref Ti.
Implicit Types a : addr Ti.

Lemma ref_refine_nil_alt r' sz r'' i i' :
  i' = i + sz * ref_offset r' → r'' = ref_base r' →
  ref_refine r' sz [] i r'' i'.
Proof. intros -> ->. by constructor. Qed.
Lemma ref_refine_ne_nil_alt r' sz rs r r'' i :
  r'' = rs :: r ++ r' → ref_refine r' sz (rs :: r) i r'' i.
Proof. intros ->. by constructor. Qed.
Lemma addr_refine_typed_l Γ α f Γm1 Γm2 a1 a2 σ :
  ✓ Γ → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → (Γ,Γm1) ⊢ a1 : σ.
Proof.
  intros ?. assert (∀ r τ1 τ2, ✓{Γ} τ1 → Γ ⊢ r : τ1 ↣ τ2 →
    int_typed (size_of Γ τ1) sptrT → int_typed (size_of Γ τ2) sptrT).
  { intros r τ1 τ2 ?? [_ ?]; split.
    { transitivity 0; auto using int_lower_nonpos with zpos. }
    apply Z.le_lt_trans with (size_of Γ τ1); [apply Nat2Z.inj_le|done].
    eauto using size_of_ref'. }
  destruct 1; constructor; eauto using ref_typed_type_valid.
Qed.
Lemma addr_refine_typed_r Γ α f Γm1 Γm2 a1 a2 σ :
  ✓ Γ → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → (Γ,Γm2) ⊢ a2 : σ.
Proof.
  destruct 2 as [o o' r r' r'' i i'' τ τ' σ σc (_&HΓm&_) ?????????? Hr''].
  assert (ref_offset (freeze true <$> r') < ref_size (freeze true <$> r')).
  { intros. eapply ref_typed_size, ref_typed_freeze; eauto. }
  constructor; auto.
  * by destruct (HΓm o o' r' τ) as (?&?&?); simplify_type_equality'.
  * destruct Hr''; simplify_type_equality'.
    + apply ref_set_offset_typed, ref_typed_freeze; auto with lia.
    + rewrite app_comm_cons, ref_typed_app.
      exists τ. by rewrite ref_typed_freeze.
  * destruct Hr''; simplify_equality'; auto.
    by rewrite ref_offset_set_offset by lia.
  * destruct Hr''; simplify_equality'; auto. rewrite ref_size_set_offset.
    transitivity (size_of Γ σ * S (ref_offset (freeze true <$> r'))); [lia|].
    apply Nat.mul_le_mono_l; lia.
  * destruct Hr''; simplify_equality'; auto.
    destruct (castable_divide Γ σ σc) as [z ->]; auto.
    by rewrite <-Nat.mul_assoc, (Nat.mul_comm (size_of _ _)), Nat.mul_assoc,
      Nat.mod_add by eauto using size_of_ne_0,
      castable_type_valid, ref_typed_type_valid.
Qed.
Lemma addr_refine_type_of_l Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → type_of a1 = σ.
Proof. by destruct 1. Qed.
Lemma addr_refine_type_of_r Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → type_of a2 = σ.
Proof. by destruct 1. Qed.
Lemma addr_refine_frozen Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → frozen a1 ↔ frozen a2.
Proof.
  unfold frozen.
  destruct 1 as [o o' r' r r'' i i'' τ τ' σ σc ??????????? []]; csimpl.
  * by rewrite ref_set_offset_freeze, ref_freeze_freeze.
  * rewrite fmap_app, ref_freeze_freeze.
    by split; intro; simplify_list_equality; repeat f_equal.
Qed.
Lemma addr_refine_id Γ α Γm a σ : (Γ,Γm) ⊢ a : σ → a ⊑{Γ,α@Γm} a : σ.
Proof.
  destruct 1 as [o r i τ σ σc].
  eexists []; csimpl; auto using memenv_refine_id; [by apply ref_typed_nil|].
  destruct r as [|rs r]; [apply ref_refine_nil_alt; csimpl; auto with lia|].
  apply ref_refine_ne_nil_alt. by rewrite (right_id_L [] (++)).
Qed.
Lemma addr_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 a1 a2 a3 σ σ' :
  ✓ Γ → a1 ⊑{Γ,α1,f1@Γm1↦Γm2} a2 : σ → a2 ⊑{Γ,α2,f2@Γm2↦Γm3} a3 : σ' →
  a1 ⊑{Γ,α1||α2,f2 ◎ f1@Γm1↦Γm3} a3 : σ.
Proof.
  destruct 2 as [o o2 r r2 r3 i i3 τ τ2 σ σc ??????????? Hr3];
    inversion 1 as [? o4 ? r4 r5 ? i5 ? τ3 ????????????? Hr5]; subst.
  exists (r2 ++ r4); eauto using memenv_refine_compose.
  { by rewrite lookup_meminj_compose; simplify_option_equality. }
  { rewrite ref_typed_app; eauto. }
  destruct Hr3 as [?|rs r i]; inversion Hr5; subst.
  * destruct r2; simplify_equality'. apply ref_refine_nil_alt; auto with lia.
  * destruct r2; simplify_equality'.
    by apply ref_refine_nil_alt; rewrite ?fmap_cons, ?fmap_app.
  * apply ref_refine_ne_nil_alt. by rewrite fmap_app, (associative_L (++)).
Qed.
Lemma addr_refine_weaken Γ Γ' α α' f f' Γm1 Γm2 Γm1' Γm2' a1 a2 σ :
  ✓ Γ → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → Γ ⊆ Γ' → Γm1' ⊑{Γ',α',f'} Γm2' →
  Γm1 ⇒ₘ Γm1' → meminj_extend f f' Γm1 Γm2 → a1 ⊑{Γ',α',f'@Γm1'↦Γm2'} a2 : σ.
Proof.
  destruct 2 as [o o2 r r2 r3 i i3 τ τ2 σ σc]; intros ?? [??] [??];
    econstructor; eauto using type_valid_weaken, ref_typed_weaken.
  * eauto using option_eq_1_alt.
  * by erewrite <-size_of_weaken by eauto.
  * by erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
  * by erewrite <-size_of_weaken
      by eauto using ref_typed_type_valid, castable_type_valid.
  * by erewrite <-size_of_weaken by eauto using ref_typed_type_valid.
Qed.
(* only holds for renamings because of end-of-array pointers *)
Lemma addr_refine_unique_l Γ f Γm1 Γm2 a1 a2 a3 σ2 σ3 :
  a1 ⊑{Γ,false,f@Γm1↦Γm2} a3 : σ2 → a2 ⊑{Γ,false,f@Γm1↦Γm2} a3 : σ3 → a1 = a2.
Proof.
  destruct 1 as [o1 o2 r r2 r3 i i3 τ τ2 σ σc
    (Hinj&_&_&_&?) ?? _ _ _ _ _ _ _ _ Hr];
    inversion 1 as [o1' ? r' r2' ? i' ? τ' ??? _ ?? _ _ _ _ _ _ _ _ Hr'];
    simplify_equality'.
  assert (r2 = [] ∧ r2' = []) as [-> ->] by eauto 6.
  destruct (Hinj o1 o1' o2 [] []); auto; simplify_type_equality;
    [|by destruct (ref_disjoint_nil_inv_l (@nil (ref_seg Ti)))].
  inversion Hr; inversion Hr'; simplify_list_equality; f_equal; lia.
Qed.
Lemma addr_refine_unique_r Γ α α' f Γm1 Γm2 a1 a2 a3 σ2 σ3 :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ2 → a1 ⊑{Γ,α',f@Γm1↦Γm2} a3 : σ3 → a2 = a3.
Proof.
  destruct 1 as [?????????????????????? []];
    inversion 1 as [?????????????????????? Hr2]; inversion Hr2;
    simplify_type_equality'; naive_solver.
Qed.
Lemma addr_freeze_refine Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ →
  freeze true a1 ⊑{Γ,α,f@Γm1↦Γm2} freeze true a2 : σ.
Proof.
  intros Ha. destruct Ha as [o o' r r' r'' i i'' τ τ' σ σc ??????????? Hr''];
    csimpl; econstructor; eauto;
    rewrite ?ref_typed_freeze, ?ref_offset_freeze, ?ref_size_freeze; auto.
  destruct Hr'' as [|r'' i'']; csimpl.
  * eapply ref_refine_nil_alt; eauto.
    by rewrite <-ref_set_offset_freeze, ref_freeze_freeze.
  * eapply ref_refine_ne_nil_alt; eauto.
    by rewrite fmap_app, ref_freeze_freeze.
Qed.
Lemma addr_ref_refine Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → addr_strict Γ a1 →
  ∃ r, f !! addr_index a1 = Some (addr_index a2, r)
    ∧ addr_ref Γ a2 = addr_ref Γ a1 ++ freeze true <$> r.
Proof.
  intros [?? r r' r'' i i'' τ τ' σ' ???????????? Hr''] ?; simplify_equality'.
  exists r'; split; auto. destruct Hr''; simplify_equality'; auto.
  rewrite Nat.mul_comm, Nat.div_add, Nat.div_small, Nat.add_0_l by lia.
  by rewrite ref_set_offset_set_offset, ref_set_offset_offset.
Qed.
Lemma addr_ref_byte_refine Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → addr_strict Γ a1 →
  addr_ref_byte Γ a1 = addr_ref_byte Γ a2.
Proof.
  intros [?? r r' r'' i i'' τ τ' σ' ???????????? Hr''] ?;
    simplify_equality'; destruct Hr''; simplify_equality'; auto.
  by rewrite Nat.mul_comm, Nat.mod_add by lia.
Qed.
Lemma addr_is_obj_refine Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → addr_is_obj a1 ↔ addr_is_obj a2.
Proof. by destruct 1. Qed.
Lemma addr_disjoint_refine Γ α α' f Γm1 Γm2 a1 a2 a3 a4 σ1 σ3 :
  ✓ Γ → meminj_injective f → addr_strict Γ a1 → addr_strict Γ a3 →
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ1 → a3 ⊑{Γ,α',f@Γm1↦Γm2} a4 : σ3 →
  a1 ⊥{Γ} a3 → a2 ⊥{Γ} a4.
Proof.
  intros ??????.
  destruct (addr_ref_refine Γ α f Γm1 Γm2 a1 a2 σ1) as (r1&Hf1&Hr1); auto.
  destruct (addr_ref_refine Γ α' f Γm1 Γm2 a3 a4 σ3) as (r2&Hf2&Hr2); auto.
  intros [?|[[Hidx ?]|(Hidx&Ha&?&?&?)]].
  * edestruct (meminj_injective_ne f (addr_index a1) (addr_index a2))
      as [|[??]]; eauto; [by left|].
    right; left; split; [done|]. rewrite Hr1, Hr2.
    by apply ref_disjoint_app, ref_disjoint_freeze_l, ref_disjoint_freeze_r.
  * rewrite Hidx in Hf1; simplify_option_equality. right; left; split; auto.
    rewrite Hr1, Hr2. by apply ref_disjoint_here_app_1.
  * rewrite Hidx in Hf1; simplify_option_equality. do 2 right; split; [done|].
    by erewrite Hr1, Hr2, !fmap_app, Ha,
      <-!(addr_ref_byte_refine _ _ _ _ _ a1 a2),
      <-!(addr_ref_byte_refine _ _ _ _ _ a3 a4),
      <-!(addr_is_obj_refine _ _ _ _ _ a1 a2),
      <-!(addr_is_obj_refine _ _ _ _ _ a3 a4) by eauto.
Qed.
Lemma addr_disjoint_refine_inv Γ α α' f Γm1 Γm2 a1 a2 a3 a4 σ1 σ3 :
  ✓ Γ → addr_strict Γ a1 → addr_strict Γ a3 →
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ1 → a3 ⊑{Γ,α',f@Γm1↦Γm2} a4 : σ3 →
  a2 ⊥{Γ} a4 → a1 ⊥{Γ} a3.
Proof.
  intros ?????.
  destruct (addr_ref_refine Γ α f Γm1 Γm2 a1 a2 σ1) as (r1&Hf1&Hr1); auto.
  destruct (addr_ref_refine Γ α' f Γm1 Γm2 a3 a4 σ3) as (r2&Hf2&Hr2); auto.
  destruct (decide (addr_index a1 = addr_index a3)) as [Hidx|]; [|by left].
  intros [?|[[Hidx' ?]|(Hidx'&Ha&?&?&?)]]; [congruence| |].
  * right; left; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
    apply ref_disjoint_here_app_2 with (freeze true <$> r1); congruence.
  * right; right; split; [done|]. rewrite Hidx in Hf1; simplify_equality.
    erewrite !(addr_ref_byte_refine _ _ _ _ _ a1 a2),
      !(addr_ref_byte_refine _ _ _ _ _ a3 a4),
      !(addr_is_obj_refine _ _ _ _ _ a1 a2),
      !(addr_is_obj_refine _ _ _ _ _ a3 a4) by eauto; split_ands; auto.
    apply (injective (++ freeze true <$> freeze true <$> r1)).
    rewrite <-!fmap_app. congruence.
Qed.
Lemma addr_byte_refine_help Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ →
  ∃ i, i + size_of Γ (addr_type_base a1) * ref_size (addr_ref_base a1)
    ≤ size_of Γ (addr_type_base a2) * ref_size (addr_ref_base a2)
  ∧ addr_byte a2 = i + addr_byte a1.
Proof.
  destruct 1 as [o o' r r' r'' i i'' τ τ' σ' σc ??????????? Hr''].
  destruct Hr'' as [|r'' i'']; simplify_type_equality'; [|by exists 0].
  rewrite ref_size_set_offset.
  exists (size_of Γ σ' * ref_offset (freeze true <$> r')). split; [|lia].
  rewrite <-Nat.mul_add_distr_l, Nat.add_comm. eapply Nat.mul_le_mono_l,
    Nat.le_succ_l, ref_typed_size, ref_typed_freeze; eauto.
Qed.
Lemma addr_strict_refine Γ α f Γm1 Γm2 a1 a2 σ :
  a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → addr_strict Γ a1 → addr_strict Γ a2.
Proof.
  intros. destruct (addr_byte_refine_help Γ α f Γm1 Γm2 a1 a2 σ)
    as (i&?&?); auto; unfold addr_strict in *; lia.
Qed.
Lemma addr_alive_refine Γ α f Γm1 Γm2 a1 a2 σ :
  index_alive Γm1 (addr_index a1) → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ →
  index_alive Γm2 (addr_index a2).
Proof. destruct 2 as [??????????? (?&?&?&?&?)]; eauto. Qed.
Lemma addr_top_refine Γ α f Γm1 Γm2 o1 o2 τ :
  ✓ Γ → Γm1 ⊑{Γ,α,f} Γm2 → Γm1 ⊢ o1 : τ → f !! o1 = Some (o2,[]) →
  ✓{Γ} τ → int_typed (size_of Γ τ) sptrT →
  addr_top o1 τ ⊑{Γ,α,f@Γm1↦Γm2} addr_top o2 τ : τ.
Proof.
  econstructor; eauto using Nat.mod_0_l, size_of_ne_0.
  * by constructor.
  * by constructor.
  * simpl; lia.
  * apply ref_refine_nil_alt; simpl; auto with lia.
Qed.
Lemma addr_top_array_refine Γ α f Γm1 Γm2 o1 o2 τ (n : Z) :
  ✓ Γ → Γm1 ⊑{Γ,α,f} Γm2 → Γm1 ⊢ o1 : τ.[Z.to_nat n] → f !! o1 = Some (o2,[]) →
  ✓{Γ} τ → Z.to_nat n ≠ 0 → int_typed (n * size_of Γ τ) sptrT →
  addr_top_array o1 τ n ⊑{Γ,α,f@Γm1↦Γm2} addr_top_array o2 τ n : τ.
Proof.
  intros. assert (0 ≤ n)%Z by (by destruct n). econstructor; simpl; eauto. 
  * apply TArray_valid; auto with lia.
  * by rewrite size_of_array, Nat2Z.inj_mul, Z2Nat.id by done.
  * by repeat typed_constructor. 
  * repeat typed_constructor; lia.
  * lia.
  * eauto using Nat.mod_0_l, size_of_ne_0.
  * constructor.
Qed.
End addresses.
