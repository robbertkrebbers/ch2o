(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export refinement_classes.

Record memenv_refine' `{Env Ti} (Γ : env Ti)
    (α : bool) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) := {
  memenv_refine_injective' : meminj_injective f;
  memenv_refine_frozen o1 o2 r :
    f !! o1 = Some (o2,r) → freeze true <$> r = r;
  memenv_refine_typed_l o1 o2 r τ1 :
    f !! o1 = Some (o2,r) → Γm1 ⊢ o1 : τ1 →
    ∃ τ2, Γm2 ⊢ o2 : τ2 ∧ Γ ⊢ r : τ2 ↣ τ1;
  memenv_refine_typed_r o1 o2 r τ2 :
    f !! o1 = Some (o2,r) → Γm2 ⊢ o2 : τ2 →
    ∃ τ1, Γm1 ⊢ o1 : τ1 ∧ Γ ⊢ r : τ2 ↣ τ1;
  memenv_refine_alive_l o1 o2 r :
    f !! o1 = Some (o2,r) → index_alive Γm1 o1 → index_alive Γm2 o2;
  memenv_refine_alive_r o1 o2 r :
    ¬α → f !! o1 = Some (o2,r) → index_alive Γm2 o2 → index_alive Γm1 o1;
  memenv_refine_perm_l' o1 τ1 :
    ¬α → Γm1 ⊢ o1 : τ1 → ∃ o2, f !! o1 = Some (o2,[]);
  memenv_refine_perm_r' o2 τ2 :
    ¬α → Γm2 ⊢ o2 : τ2 → ∃ o1, f !! o1 = Some (o2,[])
}.
Arguments memenv_refine_typed_l {_ _ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments memenv_refine_typed_r {_ _ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments memenv_refine_alive_l {_ _ _ _ _ _ _} _ _ _ _ _ _.
Arguments memenv_refine_alive_r {_ _ _ _ _ _ _} _ _ _ _ _ _ _.

Instance memenv_refine `{Env Ti} :
  RefineM Ti (env Ti) (memenv Ti) := memenv_refine'.

Record meminj_extend {Ti} (f f' : meminj Ti) (Γm1 Γm2 : memenv Ti) := {
  meminj_extend_left o τ : Γm1 ⊢ o : τ → f' !! o = f !! o;
  meminj_extend_right o o' r τ :
    Γm2 ⊢ o' : τ → f' !! o = Some (o',r) → f !! o = Some (o',r)
}.

Definition meminj_inverse {Ti} (f : meminj Ti) : meminj Ti :=
  match f with
  | meminj_id => meminj_id
  | meminj_map f => meminj_map $ map_of_list $ (λ o1o2r,
      let '(o1,(o2,_)) := o1o2r in (o2,(o1,[]))) <$> map_to_list f
  end.

Section memenv_refine.
Context `{EnvSpec Ti}.
Implicit Types α : bool.
Implicit Types f : meminj Ti.
Local Arguments lookup _ _ _ _ _ !_ /.

Lemma memenv_refine_injective Γ α f Γm1 Γm2 :
  Γm1 ⊑{Γ,α,f} Γm2 → meminj_injective f.
Proof. by intros [??]. Qed.
Lemma memenv_refine_perm_l Γ f Γm1 Γm2 o1 τ :
  Γm1 ⊑{Γ,false,f} Γm2 → Γm1 ⊢ o1 : τ →
  ∃ o2, f !! o1 = Some (o2,[]) ∧ Γm2 ⊢ o2 : τ.
Proof.
  intros [_ _ Hl _ _ _ Hl' _] ?. destruct (Hl' o1 τ) as [o2 ?]; auto.
  destruct (Hl o1 o2 [] τ) as (?&?&?); simplify_type_equality; eauto.
Qed.
Lemma memenv_refine_perm_r Γ f Γm1 Γm2 o2 τ :
  Γm1 ⊑{Γ,false,f} Γm2 → Γm2 ⊢ o2 : τ →
  ∃ o1, f !! o1 = Some (o2,[]) ∧ Γm1 ⊢ o1 : τ.
Proof.
  intros [_ _ _ Hr _ _ _ Hr'] ?. destruct (Hr' o2 τ) as [o1 ?]; auto.
  destruct (Hr o1 o2 [] τ) as (τ2&?&?); simplify_type_equality; eauto.
Qed.
Lemma lookup_meminj_inverse_1_help Γ f Γm1 Γm2 o1 o2 r1 :
  Γm1 ⊑{Γ,false,f} Γm2 → meminj_inverse f !! o2 = Some (o1,r1) →
  ∃ r2, f !! o1 = Some (o2,r2) ∧ r1 = [].
Proof.
  destruct f as [|f]; simpl; intros HΓm Ho2; [naive_solver|].
  apply elem_of_map_of_list_2 in Ho2; revert Ho2.
  rewrite elem_of_list_fmap; intros ((o1'&o2'&r2')&?&Ho1'); simplify_equality'.
  apply elem_of_map_to_list in Ho1'; eauto.
Qed.
Lemma lookup_meminj_inverse_1 Γ f Γm1 Γm2 o1 o2 r τ :
  Γm1 ⊑{Γ,false,f} Γm2 → meminj_inverse f !! o2 = Some (o1,r) →
  Γm2 ⊢ o2 : τ → Γm1 ⊢ o1 : τ ∧ f !! o1 = Some (o2,[]) ∧ r = [].
Proof.
  intros HΓm ??.
  destruct (lookup_meminj_inverse_1_help Γ f Γm1 Γm2 o1 o2 r) as (r'&?&?); auto.
  destruct (memenv_refine_perm_r Γ f Γm1 Γm2 o2 τ) as (o1'&?&?); auto.
  destruct (memenv_refine_injective Γ false f
    Γm1 Γm2 HΓm o1 o1' o2 r' []); simplify_equality'; auto.
  by destruct (ref_disjoint_nil_inv_l r').
Qed.
Lemma lookup_meminj_inverse_2 Γ f Γm1 Γm2 o1 o2 r2 τ :
  Γm1 ⊑{Γ,false,f} Γm2 → Γm1 ⊢ o1 : τ →
  f !! o1 = Some (o2,r2) → meminj_inverse f !! o2 = Some (o1,[]).
Proof.
  destruct f as [|f]; simpl; [naive_solver|]; intros HΓm ??.
  apply elem_of_map_of_list_1_help.
  { rewrite elem_of_list_fmap.
    eexists (o1,(o2,r2)); split; auto. by apply elem_of_map_to_list. }
  intros [??]; rewrite elem_of_list_fmap;
    intros ((o1'&o2'&r2')&?&Ho1'); simplify_equality; f_equal.
  apply elem_of_map_to_list in Ho1'.
  destruct (memenv_refine_injective Γ false (meminj_map f)
    Γm1 Γm2 HΓm o1 o1' o2' r2 r2'); simplify_equality'; auto.
  destruct (memenv_refine_perm_l Γ (meminj_map f) Γm1 Γm2 o1 τ)
    as (?&?&?); simplify_equality'; auto.
  by destruct (ref_disjoint_nil_inv_l r2').
Qed.
Lemma memenv_refine_inverse Γ f Γm1 Γm2 :
  Γm1 ⊑{Γ,false,f} Γm2 → Γm2 ⊑{Γ,false,meminj_inverse f} Γm1.
Proof.
  intros HΓm. constructor.
  * intros o2 o2' o1 r1 r1' ??.
    destruct (lookup_meminj_inverse_1_help Γ f Γm1 Γm2 o1 o2 r1); auto.
    destruct (lookup_meminj_inverse_1_help Γ f Γm1 Γm2 o1 o2' r1');naive_solver.
  * intros o2 o1 r ?.
    destruct (lookup_meminj_inverse_1_help Γ f Γm1 Γm2 o1 o2 r); naive_solver.
  * intros o2 o1 r τ ??.
    destruct (lookup_meminj_inverse_1 Γ f Γm1 Γm2 o1 o2 r τ) as (?&?&->); auto.
    eauto using ref_typed_nil_2.
  * intros o1 o2 r τ ??.
    destruct (lookup_meminj_inverse_1_help Γ f Γm1 Γm2 o2 o1 r) as (r'&?&->),
      (memenv_refine_perm_l Γ f Γm1 Γm2 o2 τ) as (o2'&?&?); auto.
    simplify_equality; eauto using ref_typed_nil_2.
  * intros o2 o1 r ?. destruct (lookup_meminj_inverse_1_help Γ f Γm1 Γm2
      o1 o2 r) as (?&?&?); eauto using memenv_refine_alive_r.
  * intros o1 o2 r ??. destruct (lookup_meminj_inverse_1_help Γ f Γm1 Γm2
      o2 o1 r) as (?&?&?); eauto using memenv_refine_alive_l.
  * intros o2 τ2 ??. destruct (memenv_refine_perm_r Γ f Γm1 Γm2 o2 τ2)
      as (o1&?&?); eauto using lookup_meminj_inverse_2.
  * intros o1 τ1 ??. destruct (memenv_refine_perm_l Γ f Γm1 Γm2 o1 τ1)
      as (o2&?&?); eauto using lookup_meminj_inverse_2.
Qed.
Lemma memenv_refine_inverse_compose Γ f Γm1 Γm2 o1 τ1 :
  Γm1 ⊑{Γ,false,f} Γm2 →
  Γm1 ⊢ o1 : τ1 → (meminj_inverse f ◎ f) !! o1 = Some (o1,[]).
Proof.
  intros HΓm ?; rewrite lookup_meminj_compose_Some.
  destruct (memenv_refine_perm_l Γ f Γm1 Γm2 o1 τ1) as (o2&?&?); auto.
  eexists o2, [], []; eauto using lookup_meminj_inverse_2.
Qed.
Lemma memenv_refine_compose_inverse Γ f Γm1 Γm2 o2 τ2 :
  Γm1 ⊑{Γ,false,f} Γm2 →
  Γm2 ⊢ o2 : τ2 → (f ◎ meminj_inverse f) !! o2 = Some (o2,[]).
Proof.
  intros HΓm ?; rewrite lookup_meminj_compose_Some.
  destruct (memenv_refine_perm_r Γ f Γm1 Γm2 o2 τ2) as (o1&?&?); auto.
  eexists o1, [], []; eauto using lookup_meminj_inverse_2.
Qed.
Lemma memenv_refine_id Γ Γm α : Γm ⊑{Γ,α} Γm.
Proof.
  repeat split; intros until 0; rewrite ?lookup_meminj_id;
    naive_solver eauto using meminj_id_injective, ref_typed_nil_2.
Qed.
Lemma memenv_refine_compose Γ α1 α2 f1 f2 Γm1 Γm2 Γm3 :
  ✓ Γ → Γm1 ⊑{Γ,α1,f1} Γm2 → Γm2 ⊑{Γ,α2,f2} Γm3 →
  Γm1 ⊑{Γ,α1||α2,f2 ◎ f1} Γm3.
Proof.
  intros ? HΓm12 HΓm23; repeat split.
  * eauto using meminj_compose_injective, memenv_refine_injective.
  * intros o1 o3 r; rewrite lookup_meminj_compose_Some.
    intros (o2&r2&r3&?&?&->); rewrite fmap_app;
      f_equal; eauto using memenv_refine_frozen.
  * intros o1 o3 r τ1; rewrite lookup_meminj_compose_Some.
    intros (o2&r2&r3&?&?&->) ?; setoid_rewrite ref_typed_app.
    destruct (memenv_refine_typed_l HΓm12 o1 o2 r2 τ1) as (τ2&?&?); auto.
    destruct (memenv_refine_typed_l HΓm23 o2 o3 r3 τ2) as (τ3&?&?); eauto.
  * intros o1 o3 r τ3; rewrite lookup_meminj_compose_Some.
    intros (o2&r2&r3&?&?&->) ?; setoid_rewrite ref_typed_app.
    destruct (memenv_refine_typed_r HΓm23 o2 o3 r3 τ3) as (τ2&?&?); auto.
    destruct (memenv_refine_typed_r HΓm12 o1 o2 r2 τ2) as (τ1&?&?); eauto.
  * intros o1 o3 r; rewrite lookup_meminj_compose_Some.
    intros (o2&r2&r3&?&?&->) ?. do 2 (eapply memenv_refine_alive_l; eauto).
  * intros o1 o3 r ?; rewrite lookup_meminj_compose_Some.
    intros (o2&r2&r3&?&?&->) ?. do 2 (eapply memenv_refine_alive_r; eauto).
  * intros o1 τ1 ??; setoid_rewrite lookup_meminj_compose_Some.
    destruct α1, α2; simplify_equality'; try done.
    destruct (memenv_refine_perm_l Γ f1 Γm1 Γm2 o1 τ1) as (o2&?&?); auto.
    destruct (memenv_refine_perm_l Γ f2 Γm2 Γm3 o2 τ1) as (o3&?&?); auto.
    eexists o3, o2, [], []; eauto.
  * intros o3 τ3 ??; setoid_rewrite lookup_meminj_compose_Some.
    destruct α1, α2; simplify_equality'; try done.
    destruct (memenv_refine_perm_r Γ f2 Γm2 Γm3 o3 τ3) as (o2&?&?); auto.
    destruct (memenv_refine_perm_r Γ f1 Γm1 Γm2 o2 τ3) as (o1&?&?); auto.
    eexists o1, o2, [], []; eauto.
Qed.
Lemma memenv_refine_weaken Γ Γ' α α' f Γm1 Γm2 :
  ✓ Γ → Γm1 ⊑{Γ,α,f} Γm2 → Γ ⊆ Γ' → (α → α') → Γm1 ⊑{Γ',α',f} Γm2.
Proof. destruct 2; split; naive_solver eauto using ref_typed_weaken. Qed.
Lemma meminj_extend_reflexive f Γm1 Γm2 : meminj_extend f f Γm1 Γm2.
Proof. by split. Qed.
Lemma meminj_extend_transitive f f' f'' Γm1 Γm2 Γm1' Γm2' :
  meminj_extend f f' Γm1 Γm2 → meminj_extend f' f'' Γm1' Γm2' →
  Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' → meminj_extend f f'' Γm1 Γm2.
Proof. intros [??] [??] [? _] [? _]; split; eauto using eq_trans. Qed.
Lemma meminj_extend_compose f1 f2 Γm1 Γm2 :
  meminj_extend meminj_id f1 Γm1 Γm1 →
  meminj_extend meminj_id f2 Γm2 Γm2 → Γm1 ⇒ₘ Γm2 →
  meminj_extend meminj_id (f1 ◎ f2) Γm1 Γm1.
Proof.
  intros [Hf Hf'] [Hg Hg'] ?; split.
  * intros o τ ?; apply lookup_meminj_compose_Some.
    eexists o, [], []; eauto 8 using memenv_forward_typed.
  * intros o o'' r τ ?; rewrite lookup_meminj_compose_Some.
    intros (o'&r'&r''&Ho&Ho'&->). eapply Hf' in Ho'; eauto.
    rewrite lookup_meminj_id in Ho'; simplify_equality.
    rewrite (right_id_L [] (++)); eauto using memenv_forward_typed.
Qed.
Lemma meminj_extend_inverse Γ f1 f2 Γm1 Γm2 Γm1' Γm2' :
  Γm1 ⊑{Γ,false,f1} Γm2 → Γm2' ⊑{Γ,false,f2} Γm1' →
  Γm1 ⇒ₘ Γm1' → Γm2 ⇒ₘ Γm2' →
  meminj_extend (meminj_inverse f1) f2 Γm2 Γm1 →
  meminj_extend f1 (meminj_inverse f2) Γm1 Γm2.
Proof.
  intros HΓ1 HΓ2 ?? [Hf Hf']; split.
  * intros o1 τ ?. destruct (memenv_refine_perm_l Γ f1
      Γm1 Γm2 o1 τ) as (o2&Ho1&?); auto; rewrite Ho1.
    eapply lookup_meminj_inverse_2; eauto using memenv_forward_typed.
    erewrite Hf by eauto; eauto using lookup_meminj_inverse_2.
  * intros o1 o2 r τ ??.
    destruct (memenv_refine_perm_r Γ f1 Γm1 Γm2 o2 τ) as (o1'&?&?); auto.
    destruct (lookup_meminj_inverse_1_help Γ f2 Γm2' Γm1' o2 o1 r)
      as (r'&Ho1&->); auto; erewrite Hf in Ho1 by eauto.
    destruct (lookup_meminj_inverse_1 Γ f1 Γm1 Γm2 o1 o2 r' τ)
      as (?&?&?); auto.
Qed.
End memenv_refine.
