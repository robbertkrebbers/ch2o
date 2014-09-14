(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export addresses.
Local Open Scope ctype_scope.

Inductive ptr (Ti : Set) :=
  | NULL : type Ti → ptr Ti | Ptr : addr Ti → ptr Ti.
Arguments NULL {_} _.
Arguments Ptr {_} _.

Instance ptr_eq_dec `{Ti : Set, ∀ k1 k2 : Ti, Decision (k1 = k2)}
  (p1 p2 : ptr Ti) : Decision (p1 = p2).
Proof. solve_decision. Defined.

Definition maybe_NULL {Ti} (p : ptr Ti) : option (type Ti) :=
  match p with NULL τ => Some τ | _ => None end.
Definition maybe_Ptr {Ti} (p : ptr Ti) : option (addr Ti) :=
  match p with Ptr a => Some a | _ => None end.

Section pointer_operations.
  Context `{Env Ti}.

  Inductive ptr_typed' (Γ : env Ti) (Γm : memenv Ti) : ptr Ti → type Ti → Prop :=
    | NULL_typed τ : ptr_type_valid Γ τ → ptr_typed' Γ Γm (NULL τ) τ
    | Ptr_typed a σ : (Γ,Γm) ⊢ a : σ → ptr_typed' Γ Γm (Ptr a) σ.
  Global Instance ptr_typed:
    Typed (env Ti * memenv Ti) (type Ti) (ptr Ti) := curry ptr_typed'.
  Global Instance ptr_freeze : Freeze (ptr Ti) := λ β p,
    match p with NULL τ => NULL τ | Ptr a => Ptr (freeze β a) end.

  Global Instance type_of_ptr: TypeOf (type Ti) (ptr Ti) := λ p,
    match p with NULL τ => τ | Ptr a => type_of a end.
  Global Instance ptr_type_check:
      TypeCheck (env Ti * memenv Ti) (type Ti) (ptr Ti) := λ ΓΓm p,
    let (Γ,Γm) := ΓΓm in
    match p with
    | NULL τ => guard (ptr_type_valid Γ τ); Some τ
    | Ptr a => type_check (Γ,Γm) a
    end.
  Inductive is_NULL : ptr Ti → Prop := mk_is_NULL τ : is_NULL (NULL τ).
  Definition ptr_alive (Γm : memenv Ti) (p : ptr Ti) : Prop :=
    match p with NULL _ => True | Ptr a => index_alive Γm (addr_index a) end.

  Inductive ptr_refine' (Γ : env Ti) (f : meminj Ti) (Γm1 Γm2 : memenv Ti) :
       ptr Ti → ptr Ti → type Ti → Prop :=
    | NULL_refine τ :
       ptr_type_valid Γ τ → ptr_refine' Γ f Γm1 Γm2 (NULL τ) (NULL τ) τ
    | Ptr_refine a1 a2 τ :
       a1 ⊑{Γ,f@Γm1↦Γm2} a2 : τ → ptr_refine' Γ f Γm1 Γm2 (Ptr a1) (Ptr a2) τ.
  Global Instance ptr_refine:
    RefineT Ti (env Ti) (type Ti) (ptr Ti) := ptr_refine'.
End pointer_operations.

Section pointers.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τ : type Ti.
Implicit Types a : addr Ti.
Implicit Types p : ptr Ti.

Global Instance: Injective (=) (=) (@Ptr Ti).
Proof. by injection 1. Qed.
Lemma ptr_typed_type_valid Γ Γm p τ :
  ✓ Γ → (Γ,Γm) ⊢ p : τ → ptr_type_valid Γ τ.
Proof.
  destruct 2; eauto using addr_typed_type_valid, type_valid_ptr_type_valid.
Qed.
Global Instance: TypeOfSpec (env Ti * memenv Ti) (type Ti) (ptr Ti).
Proof.
  intros [??]. by destruct 1; simpl; erewrite ?type_of_correct by eauto.
Qed.
Global Instance:
  TypeCheckSpec (env Ti * memenv Ti) (type Ti) (ptr Ti) (λ _, True).
Proof.
  intros [Γ Γmm] p τ _. split.
  * destruct p; intros; simplify_option_equality;
      constructor; auto; by apply type_check_sound.
  * by destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma ptr_typed_weaken Γ1 Γ2 Γm1 Γm2 p τ :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τ → Γ1 ⊆ Γ2 → Γm1 ⊆{⇒} Γm2 → (Γ2,Γm2) ⊢ p : τ.
Proof.
  destruct 2; constructor;
    eauto using ptr_type_valid_weaken, addr_typed_weaken.
Qed.
Lemma ptr_freeze_freeze β1 β2 p : freeze β1 (freeze β2 p) = freeze β1 p.
Proof. destruct p; f_equal'; auto using addr_freeze_freeze. Qed.
Lemma ptr_typed_freeze Γ Γm β p τ : (Γ,Γm) ⊢ freeze β p : τ ↔ (Γ,Γm) ⊢ p : τ.
Proof.
  split.
  * destruct p; inversion_clear 1; constructor; auto.
    by apply addr_typed_freeze with β.
  * destruct 1; constructor; auto. by apply addr_typed_freeze.
Qed.
Lemma ptr_type_check_freeze Γ Γm β p :
  type_check (Γ,Γm) (freeze β p) = type_check (Γ,Γm) p.
Proof.
  apply option_eq. intros. by rewrite !type_check_correct, ptr_typed_freeze.
Qed.
Lemma ptr_freeze_type_of β p : type_of (freeze β p) = type_of p.
Proof. by destruct p; simpl; rewrite ?addr_type_of_freeze. Qed.
Global Instance is_NULL_dec p : Decision (is_NULL p).
Proof.
 refine match p with NULL _ => left _ | _ => right _ end;
   first [by constructor | abstract by inversion 1].
Defined.
Lemma ptr_alive_weaken Γm1 Γm2 p :
  ptr_alive Γm1 p → (∀ o, index_alive Γm1 o → index_alive Γm2 o) → ptr_alive Γm2 p.
Proof. destruct p; simpl; auto. Qed.
Lemma ptr_dead_weaken Γ Γm1 Γm2 p σ :
  (Γ,Γm1) ⊢ p : σ → ptr_alive Γm2 p → Γm1 ⊆{⇒} Γm2 → ptr_alive Γm1 p.
Proof. destruct 1; simpl; eauto using addr_dead_weaken. Qed.
Global Instance ptr_alive_dec Γm p : Decision (ptr_alive Γm p).
Proof. destruct p; apply _. Defined.

(** ** Refinements *)
Lemma ptr_refine_typed_l Γ f Γm1 Γm2 p1 p2 σ :
  ✓ Γ → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → (Γ,Γm1) ⊢ p1 : σ.
Proof. destruct 2; constructor; eauto using addr_refine_typed_l. Qed.
Lemma ptr_refine_typed_r Γ f Γm1 Γm2 p1 p2 σ :
  ✓ Γ → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → (Γ,Γm2) ⊢ p2 : σ.
Proof. destruct 2; constructor; eauto using addr_refine_typed_r. Qed.
Lemma ptr_refine_type_of_l Γ f Γm1 Γm2 p1 p2 σ :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → type_of p1 = σ.
Proof. destruct 1; simpl; eauto using addr_refine_type_of_l. Qed.
Lemma ptr_refine_type_of_r Γ f Γm1 Γm2 p1 p2 σ :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → type_of p2 = σ.
Proof. destruct 1; simpl; eauto using addr_refine_type_of_r. Qed.
Lemma ptr_refine_frozen Γ f Γm1 Γm2 p1 p2 σ :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → frozen p1 ↔ frozen p2.
Proof.
  unfold frozen. destruct 1; simpl; auto.
  rewrite !(injective_iff Ptr). eapply (addr_refine_frozen Γ f); eauto.
Qed.
Lemma ptr_refine_id Γ Γm p σ : (Γ,Γm) ⊢ p : σ → p ⊑{Γ@Γm} p : σ.
Proof. destruct 1; constructor; eauto using addr_refine_id. Qed.
Lemma ptr_refine_compose Γ f g Γm1 Γm2 Γm3 p1 p2 p3 σ σ' :
  ✓ Γ → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → p2 ⊑{Γ,g@Γm2↦Γm3} p3 : σ' →
  p1 ⊑{Γ,f ◎ g@Γm1↦Γm3} p3 : σ.
Proof.
  destruct 2; inversion_clear 1; constructor; eauto using addr_refine_compose.
Qed.
Lemma ptr_refine_weaken Γ Γ' f f' Γm1 Γm2 Γm1' Γm2' p1 p2 σ :
  ✓ Γ → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → Γ ⊆ Γ' → Γm1' ⊑{Γ',f'} Γm2' → Γm1 ⊆{⇒} Γm1' →
  meminj_extend f f' Γm1 Γm2 → p1 ⊑{Γ',f'@Γm1'↦Γm2'} p2 : σ.
Proof.
  destruct 2; constructor;
    eauto using ptr_type_valid_weaken, addr_refine_weaken.
Qed.
Lemma ptr_refine_eq Γ Γm p1 p2 σ : p1 ⊑{Γ@Γm} p2 : σ → p1 = p2.
Proof. destruct 1; f_equal; eauto using addr_refine_eq. Qed.
Lemma ptr_refine_unique Γ f Γm1 Γm2 p1 p2 p3 σ2 σ3 :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ2 → p1 ⊑{Γ,f@Γm1↦Γm2} p3 : σ3 → p2 = p3.
Proof.
  destruct 1; inversion_clear 1; f_equal; eauto using addr_refine_unique.
Qed.
Lemma ptr_freeze_refine Γ f Γm1 Γm2 p1 p2 σ :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → freeze true p1 ⊑{Γ,f@Γm1↦Γm2} freeze true p2 : σ.
Proof. destruct 1; simpl; constructor; eauto using addr_freeze_refine. Qed.
Lemma ptr_alive_refine Γ f Γm1 Γm2 p1 p2 σ :
  ptr_alive Γm1 p1 → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → ptr_alive Γm2 p2.
Proof. destruct 2; simpl in *; eauto using addr_alive_refine. Qed.
End pointers.
