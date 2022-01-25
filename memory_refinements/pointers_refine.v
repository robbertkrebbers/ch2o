(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export pointers addresses_refine.
Local Open Scope ctype_scope.

Inductive ptr_refine' `{Env K} (Γ : env K) (α : bool) (f : meminj K)
     (Δ1 Δ2 : memenv K) : ptr K → ptr K → ptr_type K → Prop :=
  | NULL_refine τp :
     ✓{Γ} τp → ptr_refine' Γ α f Δ1 Δ2 (NULL τp) (NULL τp) τp
  | Ptr_refine a1 a2 τp :
     a1 ⊑{Γ,α,f@Δ1↦Δ2} a2 : τp →
     ptr_refine' Γ α f Δ1 Δ2 (Ptr a1) (Ptr a2) τp
  | FunPtr_refine g τs τ :
     Γ !! g = Some (τs,τ) →
     ptr_refine' Γ α f Δ1 Δ2 (FunPtr g τs τ) (FunPtr g τs τ) (τs ~> τ).
#[global] Instance ptr_refine `{Env K} :
  RefineT K (env K) (ptr_type K) (ptr K) := ptr_refine'.

Section pointers.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α : bool.
Implicit Types τp : ptr_type K.
Implicit Types a : addr K.
Implicit Types p : ptr K.

Lemma ptr_refine_typed_l Γ α f Δ1 Δ2 p1 p2 τp :
  ✓ Γ → p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp → (Γ,Δ1) ⊢ p1 : τp.
Proof. destruct 2; constructor; eauto using addr_refine_typed_l. Qed.
Lemma ptr_refine_typed_r Γ α f Δ1 Δ2 p1 p2 τp :
  ✓ Γ → p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp → (Γ,Δ2) ⊢ p2 : τp.
Proof. destruct 2; constructor; eauto using addr_refine_typed_r. Qed.
Lemma ptr_refine_type_of_l Γ α f Δ1 Δ2 p1 p2 τp :
  p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp → type_of p1 = τp.
Proof. destruct 1; simpl; eauto using addr_refine_type_of_l. Qed.
Lemma ptr_refine_type_of_r Γ α f Δ1 Δ2 p1 p2 τp :
  p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp → type_of p2 = τp.
Proof. destruct 1; simpl; eauto using addr_refine_type_of_r. Qed.
Lemma ptr_refine_frozen Γ α f Δ1 Δ2 p1 p2 τp :
  p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp → frozen p2 → frozen p1.
Proof.
  unfold frozen. destruct 1; simpl; auto.
  rewrite !(inj_iff Ptr). eapply addr_refine_frozen; eauto.
Qed.
Lemma ptr_refine_id Γ α Δ p τp : (Γ,Δ) ⊢ p : τp → p ⊑{Γ,α@Δ} p : τp.
Proof. destruct 1; constructor; eauto using addr_refine_id. Qed.
Lemma ptr_refine_compose Γ α1 α2 f1 f2 Δ1 Δ2 Δ3 p1 p2 p3 τp τp' :
  ✓ Γ → p1 ⊑{Γ,α1,f1@Δ1↦Δ2} p2 : τp → p2 ⊑{Γ,α2,f2@Δ2↦Δ3} p3 : τp' →
  p1 ⊑{Γ,α1||α2,f2 ◎ f1@Δ1↦Δ3} p3 : τp.
Proof.
  destruct 2; inversion_clear 1; constructor; eauto using addr_refine_compose.
Qed.
Lemma ptr_refine_inverse Γ f Δ1 Δ2 p1 p2 τp :
  p1 ⊑{Γ,false,f@Δ1↦Δ2} p2 : τp →
  p2 ⊑{Γ,false,meminj_inverse f@Δ2↦Δ1} p1 : τp.
Proof. destruct 1; constructor; eauto using addr_refine_inverse. Qed.
Lemma ptr_refine_weaken Γ Γ' α α' f f' Δ1 Δ2 Δ1' Δ2' p1 p2 τp :
  ✓ Γ → p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp → Γ ⊆ Γ' → (α → α') →
  Δ1' ⊑{Γ',α',f'} Δ2' → Δ1 ⇒ₘ Δ1' →
  meminj_extend f f' Δ1 Δ2 → p1 ⊑{Γ',α',f'@Δ1'↦Δ2'} p2 : τp.
Proof.
  destruct 2; constructor;
    eauto using ptr_type_valid_weaken, addr_refine_weaken, lookup_fun_weaken.
Qed.
Lemma ptr_refine_unique_l Γ f Δ1 Δ2 p1 p2 p3 τp2 τp3 :
  p1 ⊑{Γ,false,f@Δ1↦Δ2} p3 : τp2 → p2 ⊑{Γ,false,f@Δ1↦Δ2} p3 : τp3 → p1 = p2.
Proof.
  destruct 1; inversion_clear 1; f_equal; eauto using addr_refine_unique_l.
Qed.
Lemma ptr_refine_unique_r Γ α f Δ1 Δ2 p1 p2 p3 τp2 τp3 :
  p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp2 → p1 ⊑{Γ,α,f@Δ1↦Δ2} p3 : τp3 →
  frozen p2 → frozen p3 → p2 = p3.
Proof.
  unfold frozen. destruct 1; inversion_clear 1; intros; simplify_equality';
    f_equal; eauto using addr_refine_unique_r.
Qed.
Lemma ptr_freeze_refine_l Γ Δ p τp :
  (Γ,Δ) ⊢ p : τp → freeze true p ⊑{Γ,true@Δ} p : τp.
Proof. destruct 1; refine_constructor; eauto using addr_freeze_refine_l. Qed.
Lemma ptr_freeze_refine Γ α f Δ1 Δ2 p1 p2 τp :
  p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp →
  freeze true p1 ⊑{Γ,α,f@Δ1↦Δ2} freeze true p2 : τp.
Proof. destruct 1; simpl; constructor; eauto using addr_freeze_refine. Qed.
Lemma ptr_alive_refine Γ α f Δ1 Δ2 p1 p2 τp :
  ptr_alive Δ1 p1 → p1 ⊑{Γ,α,f@Δ1↦Δ2} p2 : τp → ptr_alive Δ2 p2.
Proof. destruct 2; simpl in *; eauto using addr_alive_refine. Qed.
End pointers.
