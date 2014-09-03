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
  Definition ptr_compare_ok (Γm : memenv Ti) (c : compop) (p1 p2 : ptr Ti) : Prop :=
    match p1, p2 with
    | Ptr a1, Ptr a2 => addr_minus_ok Γm a1 a2
    | NULL _, Ptr a2 =>
       match c with EqOp => index_alive Γm (addr_index a2) | _ => False end
    | Ptr a1, NULL _ =>
       match c with EqOp => index_alive Γm (addr_index a1) | _ => False end
    | NULL _, NULL _ => True
    end.
  Definition ptr_compare (Γ : env Ti) (c : compop) (p1 p2 : ptr Ti) : bool :=
    match p1, p2 with
    | Ptr a1, Ptr a2 => Z_comp c (addr_minus Γ a1 a2) 0
    | NULL _, Ptr a2 => false (* only allowed for EqOp *)
    | Ptr a1, NULL _ => false (* only allowed for EqOp *)
    | NULL _, NULL _ => match c with EqOp | LeOp => true | LtOp => false end
    end.
  Definition ptr_plus_ok (Γ : env Ti) (Γm : memenv Ti) (j : Z) (p : ptr Ti) :=
    match p with NULL _ => j = 0 | Ptr a => addr_plus_ok Γ Γm j a end.
  Global Arguments ptr_plus_ok _ _ _ !_ /.
  Definition ptr_plus (Γ : env Ti) (j : Z) (p : ptr Ti) : ptr Ti :=
    match p with NULL τ => NULL τ | Ptr a => Ptr (addr_plus Γ j a) end.
  Global Arguments ptr_plus _ _ !_ /.
  Definition ptr_minus_ok (Γm : memenv Ti) (p1 p2 : ptr Ti) : Prop :=
    match p1, p2 with
    | NULL _, NULL _ => True
    | Ptr a1, Ptr a2 => addr_minus_ok Γm a1 a2
    | _, _ => False
    end.
  Global Arguments ptr_minus_ok _ !_ !_ /.
  Definition ptr_minus (Γ : env Ti) (p1 p2 : ptr Ti) : Z :=
    match p1, p2 with
    | NULL _, NULL _ => 0
    | Ptr a1, Ptr a2 => addr_minus Γ a1 a2
    | _, _ => 0
    end.
  Global Arguments ptr_minus _ !_ !_ /.
  Definition ptr_cast_ok (Γ : env Ti) (Γm : memenv Ti)
      (σc : type Ti) (p : ptr Ti) : Prop :=
    match p with NULL _ => True | Ptr a => addr_cast_ok Γ Γm σc a end.
  Global Arguments ptr_cast_ok _ _ _ !_ /.
  Definition ptr_cast (σc : type Ti) (p : ptr Ti) : ptr Ti :=
    match p with NULL _ => NULL σc | Ptr a => Ptr (addr_cast σc a) end.
  Global Arguments ptr_cast _ !_ /.

  Inductive ptr_refine' (Γ : env Ti) (f : mem_inj Ti) (Γm1 Γm2 : memenv Ti) :
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
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τ → Γ1 ⊆ Γ2 → (∀ o σ, Γm1 ⊢ o : σ → Γm2 ⊢ o : σ) →
  (Γ2,Γm2) ⊢ p : τ.
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
  (Γ,Γm1) ⊢ p : σ → ptr_alive Γm2 p →
  (∀ o τ, Γm1 ⊢ o : τ → index_alive Γm2 o → index_alive Γm1 o) → ptr_alive Γm1 p.
Proof. destruct 1; simpl; eauto using addr_dead_weaken. Qed.
Global Instance ptr_alive_dec Γm p : Decision (ptr_alive Γm p).
Proof. destruct p; apply _. Defined.
Global Instance ptr_compare_ok_dec Γm c p1 p2 :
  Decision (ptr_compare_ok Γm c p1 p2).
Proof. destruct p1, p2, c; apply _. Defined.
Global Instance ptr_plus_ok_dec Γ Γm j p : Decision (ptr_plus_ok Γ Γm j p).
Proof. destruct p; apply _. Defined.
Global Instance ptr_minus_ok_dec Γm p1 p2 : Decision (ptr_minus_ok Γm p1 p2).
Proof. destruct p1, p2; apply _. Defined.
Global Instance ptr_cast_ok_dec Γ Γm σc p : Decision (ptr_cast_ok Γ Γm σc p).
Proof. destruct p; apply _. Defined.
Lemma ptr_plus_typed Γ Γm p σ j :
  ✓ Γ → (Γ,Γm) ⊢ p : σ → ptr_plus_ok Γ Γm j p → (Γ,Γm) ⊢ ptr_plus Γ j p : σ.
Proof. destruct 2; simpl; constructor; eauto using addr_plus_typed. Qed.
Lemma ptr_minus_typed Γ Γm p1 p2 σ :
  ✓ Γ → (Γ,Γm) ⊢ p1 : σ → (Γ,Γm) ⊢ p2 : σ →
  int_typed (ptr_minus Γ p1 p2) sptrT.
Proof.
  destruct 2, 1; simpl;
    eauto using addr_minus_typed, int_typed_small with lia.
Qed.
Lemma ptr_cast_typed Γ Γm p σ σc :
  (Γ,Γm) ⊢ p : σ → ptr_cast_ok Γ Γm σc p →
  ptr_type_valid Γ σc → (Γ,Γm) ⊢ ptr_cast σc p : σc.
Proof. destruct 1; simpl; constructor; eauto using addr_cast_typed. Qed.

Lemma ptr_compare_ok_weaken Γm1 Γm2 c p1 p2 :
  ptr_compare_ok Γm1 c p1 p2 → (∀ o, index_alive Γm1 o → index_alive Γm2 o) →
  ptr_compare_ok Γm2 c p1 p2.
Proof. destruct p1, p2, c; simpl; eauto using addr_minus_ok_weaken. Qed.
Lemma ptr_compare_weaken Γ1 Γ2 Γm1 c p1 p2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p1 : τ1 → (Γ1,Γm1) ⊢ p2 : τ2 →
  Γ1 ⊆ Γ2 → ptr_compare Γ1 c p1 p2 = ptr_compare Γ2 c p1 p2.
Proof.
  destruct 2,1,c; simpl; intros; done || by erewrite addr_minus_weaken by eauto.
Qed.
Lemma ptr_plus_ok_weaken Γ1 Γ2 Γm1 Γm2 p τ j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τ → ptr_plus_ok Γ1 Γm1 j p →
  Γ1 ⊆ Γ2 → (∀ o, index_alive Γm1 o → index_alive Γm2 o) →
  ptr_plus_ok Γ2 Γm2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_ok_weaken. Qed.
Lemma ptr_plus_weaken Γ1 Γ2 Γm1 p τ j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τ → Γ1 ⊆ Γ2 → ptr_plus Γ1 j p = ptr_plus Γ2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_weaken, f_equal. Qed.
Lemma ptr_minus_ok_weaken Γm1 Γm2 p1 p2:
  ptr_minus_ok Γm1 p1 p2 → (∀ o, index_alive Γm1 o → index_alive Γm2 o) →
  ptr_minus_ok Γm2 p1 p2.
Proof. destruct p1, p2; simpl; eauto using addr_minus_ok_weaken. Qed.
Lemma ptr_minus_weaken Γ1 Γ2 Γm1 p1 p2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p1 : τ1 → (Γ1,Γm1) ⊢ p2 : τ2 →
  Γ1 ⊆ Γ2 → ptr_minus Γ1 p1 p2 = ptr_minus Γ2 p1 p2.
Proof. destruct 2, 1; simpl; eauto using addr_minus_weaken. Qed.
Lemma ptr_cast_ok_weaken Γ1 Γ2 Γm1 Γm2 p τ σc :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τ → ptr_cast_ok Γ1 Γm1 σc p → Γ1 ⊆ Γ2 →
  (∀ o, index_alive Γm1 o → index_alive Γm2 o) → ptr_cast_ok Γ2 Γm2 σc p.
Proof. destruct 2; simpl; eauto using addr_cast_ok_weaken. Qed.
Lemma ptr_compare_ok_alive_l Γm c p1 p2 :
  ptr_compare_ok Γm c p1 p2 → ptr_alive Γm p1.
Proof. destruct p1, p2, c; try done; by intros [??]. Qed.
Lemma ptr_compare_ok_alive_r Γm c p1 p2 :
  ptr_compare_ok Γm c p1 p2 → ptr_alive Γm p2.
Proof. destruct p1, p2, c; done || intros (?&?&?); simpl in *; congruence. Qed.
Lemma ptr_plus_ok_alive Γ Γm p j : ptr_plus_ok Γ Γm j p → ptr_alive Γm p.
Proof. destruct p. done. by intros [??]. Qed.
Lemma ptr_minus_ok_alive_l Γm p1 p2 : ptr_minus_ok Γm p1 p2 → ptr_alive Γm p1.
Proof. destruct p1, p2; try done. by intros [??]. Qed.
Lemma ptr_minus_ok_alive_r Γm p1 p2 : ptr_minus_ok Γm p1 p2 → ptr_alive Γm p2.
Proof. destruct p1, p2; try done. intros (?&?&?); simpl in *; congruence. Qed.
Lemma ptr_cast_ok_alive Γ Γm p σ : ptr_cast_ok Γ Γm σ p → ptr_alive Γm p.
Proof. destruct p. done. by intros [??]. Qed.

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
  ✓ Γ → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → Γ ⊆ Γ' → Γm1' ⊑{Γ',f'} Γm2' → 
  (∀ o o2 r τ, Γm1 ⊢ o : τ → f !! o = Some (o2,r) → f' !! o = Some (o2,r)) →
  (∀ o τ, Γm1 ⊢ o : τ → Γm1' ⊢ o : τ) → p1 ⊑{Γ',f'@Γm1'↦Γm2'} p2 : σ.
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
Lemma ptr_compare_ok_refine Γ Γm1 Γm2 f c p1 p2 p3 p4 σ :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → p3 ⊑{Γ,f@Γm1↦Γm2} p4 : σ →
  ptr_compare_ok Γm1 c p1 p3 → ptr_compare_ok Γm2 c p2 p4.
Proof.
  destruct 1, 1, c; simpl; eauto using addr_minus_ok_refine, addr_alive_refine.
Qed.
Lemma ptr_compare_refine Γ f Γm1 Γm2 c p1 p2 p3 p4 σ :
  ✓ Γ → ptr_compare_ok Γm1 c p1 p3 →
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → p3 ⊑{Γ,f@Γm1↦Γm2} p4 : σ →
  ptr_compare Γ c p1 p3 = ptr_compare Γ c p2 p4.
Proof.
  destruct 3, 1, c; simpl; done || by erewrite addr_minus_refine by eauto.
Qed.
Lemma ptr_plus_ok_refine Γ Γm1 Γm2 f p1 p2 σ j :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → ptr_plus_ok Γ Γm1 j p1 → ptr_plus_ok Γ Γm2 j p2.
Proof. destruct 1; simpl; eauto using addr_plus_ok_refine. Qed.
Lemma ptr_plus_refine Γ f Γm1 Γm2 p1 p2 σ j :
  ✓ Γ → ptr_plus_ok Γ Γm1 j p1 →
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → ptr_plus Γ j p1 ⊑{Γ,f@Γm1↦Γm2} ptr_plus Γ j p2 : σ.
Proof. destruct 3; simpl; constructor; eauto using addr_plus_refine. Qed.
Lemma ptr_minus_ok_refine Γ Γm1 Γm2 f p1 p2 p3 p4 σ :
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → p3 ⊑{Γ,f@Γm1↦Γm2} p4 : σ →
  ptr_minus_ok Γm1 p1 p3 → ptr_minus_ok Γm2 p2 p4.
Proof. destruct 1, 1; simpl; eauto using addr_minus_ok_refine. Qed.
Lemma ptr_minus_refine Γ f Γm1 Γm2 p1 p2 p3 p4 σ :
  ✓ Γ → ptr_minus_ok Γm1 p1 p3 →
  p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ → p3 ⊑{Γ,f@Γm1↦Γm2} p4 : σ →
  ptr_minus Γ p1 p3 = ptr_minus Γ p2 p4.
Proof. destruct 3, 1; simpl; eauto using addr_minus_refine. Qed.
Lemma ptr_cast_ok_refine Γ f Γm1 Γm2 p1 p2 σ σc :
  ✓ Γ → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ →
  ptr_cast_ok Γ Γm1 σc p1 → ptr_cast_ok Γ Γm2 σc p2.
Proof. destruct 2; simpl; eauto using addr_cast_ok_refine. Qed.
Lemma ptr_cast_refine Γ f Γm1 Γm2 p1 p2 σ σc :
  ptr_cast_ok Γ Γm1 σc p1 → ptr_type_valid Γ σc → p1 ⊑{Γ,f@Γm1↦Γm2} p2 : σ →
  ptr_cast σc p1 ⊑{Γ,f@Γm1↦Γm2} ptr_cast σc p2 : σc.
Proof. destruct 3; constructor; eauto using addr_cast_refine. Qed.
End pointers.
