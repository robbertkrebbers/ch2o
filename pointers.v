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

Section pointer_operations.
  Context `{TypeOfIndex Ti M, Refine Ti M, IndexAlive M, IntEnv Ti, PtrEnv Ti,
    ∀ m x, Decision (index_alive m x)}.

  Inductive ptr_typed' (Γ : env Ti) (m : M) : ptr Ti → type Ti → Prop :=
    | NULL_typed τ : ptr_type_valid Γ τ → ptr_typed' Γ m (NULL τ) τ
    | Ptr_typed a σ : (Γ,m) ⊢ a : σ → ptr_typed' Γ m (Ptr a) σ.
  Global Instance ptr_typed:
    Typed (env Ti * M) (type Ti) (ptr Ti) := curry ptr_typed'.
  Global Instance ptr_freeze : Freeze (ptr Ti) := λ β p,
    match p with NULL τ => NULL τ | Ptr a => Ptr (freeze β a) end.

  Global Instance type_of_ptr: TypeOf (type Ti) (ptr Ti) := λ p,
    match p with NULL τ => τ | Ptr a => type_of a end.
  Global Instance ptr_type_check:
      TypeCheck (env Ti * M) (type Ti) (ptr Ti) := λ Γm p,
    let (Γ,m) := Γm in
    match p with
    | NULL τ => guard (ptr_type_valid Γ τ); Some τ
    | Ptr a => type_check (Γ,m) a
    end.
  Inductive is_NULL : ptr Ti → Prop := mk_is_NULL τ : is_NULL (NULL τ).

  Definition ptr_plus_ok (Γ : env Ti) (m : M) (j : Z) (p : ptr Ti) :=
    match p with NULL _ => j = 0 | Ptr a => addr_plus_ok Γ m j a end.
  Global Arguments ptr_plus_ok _ _ _ !_ /.
  Definition ptr_plus (Γ : env Ti) (j : Z) (p : ptr Ti) : ptr Ti :=
    match p with NULL τ => NULL τ | Ptr a => Ptr (addr_plus Γ j a) end.
  Global Arguments ptr_plus _ _ !_ /.
  Definition ptr_minus_ok (m : M) (p1 p2 : ptr Ti) : Prop :=
    match p1, p2 with
    | NULL _, NULL _ => True
    | Ptr a1, Ptr a2 => addr_minus_ok m a1 a2
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
  Definition ptr_cast_ok (Γ : env Ti) (σc : type Ti) (p : ptr Ti) : Prop :=
    match p with NULL _ => True | Ptr a => addr_cast_ok Γ σc a end.
  Global Arguments ptr_cast_ok _ _ !_ /.
  Definition ptr_cast (σc : type Ti) (p : ptr Ti) : ptr Ti :=
    match p with NULL _ => NULL σc | Ptr a => Ptr (addr_cast σc a) end.
  Global Arguments ptr_cast _ !_ /.

  Inductive ptr_refine' (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : M) :
       ptr Ti → ptr Ti → type Ti → Prop :=
    | NULL_refine τ :
       ptr_type_valid Γ τ → ptr_refine' Γ f m1 m2 (NULL τ) (NULL τ) τ
    | Ptr_refine a1 a2 τ :
       a1 ⊑{Γ,f@m1↦m2} a2 : τ → ptr_refine' Γ f m1 m2 (Ptr a1) (Ptr a2) τ.
  Global Instance ptr_refine: RefineT Ti M (ptr Ti) (type Ti) := ptr_refine'.
End pointer_operations.

Section pointers.
Context `{MemSpec Ti M}.
Implicit Types Γ : env Ti.
Implicit Types m : M.
Implicit Types τ : type Ti.
Implicit Types a : addr Ti.
Implicit Types p : ptr Ti.

Global Instance: Injective (=) (=) (@Ptr Ti).
Proof. by injection 1. Qed.
Lemma ptr_typed_type_valid Γ m p τ :
  ✓ Γ → (Γ,m) ⊢ p : τ → ptr_type_valid Γ τ.
Proof. destruct 2; eauto using TVoid_ptr_valid,addr_typed_ptr_type_valid. Qed.
Global Instance: TypeOfSpec (env Ti * M) (type Ti) (ptr Ti).
Proof.
  intros [??]. by destruct 1; simpl; erewrite ?type_of_correct by eauto.
Qed.
Global Instance: TypeCheckSpec (env Ti * M) (type Ti) (ptr Ti) (λ _, True).
Proof.
  intros [Γ mm] p τ _. split.
  * destruct p; intros; simplify_option_equality;
      constructor; auto using type_check_sound.
  * by destruct 1; simplify_option_equality;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma ptr_typed_weaken Γ1 Γ2 m1 m2 p τ :
  ✓ Γ1 → (Γ1,m1) ⊢ p : τ → Γ1 ⊆ Γ2 →
  (∀ o σ, type_of_index m1 o = Some σ → type_of_index m2 o = Some σ) →
  (Γ2,m2) ⊢ p : τ.
Proof.
  destruct 2; constructor;
    eauto using ptr_type_valid_weaken, addr_typed_weaken.
Qed.
Lemma ptr_freeze_freeze β1 β2 p : freeze β1 (freeze β2 p) = freeze β1 p.
Proof. destruct p; f_equal'; auto using addr_freeze_freeze. Qed.
Lemma ptr_typed_freeze Γ m β p τ : (Γ,m) ⊢ freeze β p : τ ↔ (Γ,m) ⊢ p : τ.
Proof.
  split.
  * destruct p; inversion_clear 1; constructor; auto.
    by apply addr_typed_freeze with β.
  * destruct 1; constructor; auto. by apply addr_typed_freeze.
Qed.
Lemma ptr_type_check_freeze Γm β p :
  type_check Γm (freeze β p) = type_check Γm p.
Proof.
  destruct Γm.
  apply option_eq. intros. by rewrite !type_check_correct, ptr_typed_freeze.
Qed.
Lemma ptr_freeze_type_of β p : type_of (freeze β p) = type_of p.
Proof. by destruct p; simpl; rewrite ?addr_type_of_freeze. Qed.
Global Instance is_NULL_dec p : Decision (is_NULL p).
Proof.
 refine match p with NULL _ => left _ | _ => right _ end;
   first [by constructor | abstract by inversion 1].
Defined.

Global Instance ptr_plus_ok_dec Γ m j p : Decision (ptr_plus_ok Γ m j p).
Proof. destruct p; apply _. Defined.
Global Instance ptr_minus_ok_dec m p1 p2 : Decision (ptr_minus_ok m p1 p2).
Proof. destruct p1, p2; apply _. Defined.
Global Instance ptr_cast_ok_dec Γ σc p : Decision (ptr_cast_ok Γ σc p).
Proof. destruct p; apply _. Defined.
Lemma ptr_plus_ok_typed Γ m p σ j :
  ✓ Γ → (Γ,m) ⊢ p : σ → ptr_plus_ok Γ m j p → (Γ,m) ⊢ ptr_plus Γ j p : σ.
Proof. destruct 2; simpl; constructor; eauto using addr_plus_ok_typed. Qed.
Lemma ptr_minus_ok_typed Γ m p1 p2 σ :
  ✓ Γ → (Γ,m) ⊢ p1 : σ → (Γ,m) ⊢ p2 : σ →
  int_typed (ptr_minus Γ p1 p2) sptrT.
Proof.
  destruct 2, 1; simpl;
    eauto using addr_minus_ok_typed, int_typed_small with lia.
Qed.
Lemma ptr_cast_ok_typed Γ m p σ σc :
  (Γ,m) ⊢ p : σ → ptr_cast_ok Γ σc p →
  ptr_type_valid Γ σc → (Γ,m) ⊢ ptr_cast σc p : σc.
Proof. destruct 1; simpl; constructor; eauto using addr_cast_ok_typed. Qed.
Lemma ptr_plus_ok_weaken Γ1 Γ2 m1 m2 p τ j :
  ✓ Γ1 → (Γ1,m1) ⊢ p : τ → ptr_plus_ok Γ1 m1 j p →
  Γ1 ⊆ Γ2 → (∀ o, index_alive m1 o → index_alive m2 o) →
  ptr_plus_ok Γ2 m2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_ok_weaken. Qed.
Lemma ptr_plus_weaken Γ1 Γ2 m1 p τ j :
  ✓ Γ1 → (Γ1,m1) ⊢ p : τ → Γ1 ⊆ Γ2 → ptr_plus Γ1 j p = ptr_plus Γ2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_weaken, f_equal. Qed.
Lemma ptr_minus_ok_weaken m1 m2 p1 p2:
  ptr_minus_ok m1 p1 p2 → (∀ o, index_alive m1 o → index_alive m2 o) →
  ptr_minus_ok m2 p1 p2.
Proof. destruct p1, p2; simpl; eauto using addr_minus_ok_weaken. Qed.
Lemma ptr_minus_weaken Γ1 Γ2 m1 p1 p2 τ1 τ2 :
  ✓ Γ1 → (Γ1,m1) ⊢ p1 : τ1 → (Γ1,m1) ⊢ p2 : τ2 →
  Γ1 ⊆ Γ2 → ptr_minus Γ1 p1 p2 = ptr_minus Γ2 p1 p2.
Proof. destruct 2, 1; simpl; eauto using addr_minus_weaken. Qed.
Lemma ptr_cast_ok_weaken Γ1 Γ2 m1 p τ σc :
  ✓Γ1 → (Γ1,m1) ⊢ p : τ → ptr_cast_ok Γ1 σc p → Γ1 ⊆ Γ2 → ptr_cast_ok Γ2 σc p.
Proof. destruct 2; simpl; eauto using addr_cast_ok_weaken. Qed.

(** ** Refinements *)
Lemma ptr_refine_typed_l Γ f m1 m2 p1 p2 σ :
  ✓ Γ → p1 ⊑{Γ,f@m1↦m2} p2 : σ → (Γ,m1) ⊢ p1 : σ.
Proof. destruct 2; constructor; eauto using addr_refine_typed_l. Qed.
Lemma ptr_refine_typed_r Γ f m1 m2 p1 p2 σ :
  ✓ Γ → p1 ⊑{Γ,f@m1↦m2} p2 : σ → (Γ,m2) ⊢ p2 : σ.
Proof. destruct 2; constructor; eauto using addr_refine_typed_r. Qed.
Lemma ptr_refine_type_of_l Γ f m1 m2 p1 p2 σ :
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → type_of p1 = σ.
Proof. destruct 1; simpl; eauto using addr_refine_type_of_l. Qed.
Lemma ptr_refine_type_of_r Γ f m1 m2 p1 p2 σ :
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → type_of p2 = σ.
Proof. destruct 1; simpl; eauto using addr_refine_type_of_r. Qed.
Lemma ptr_refine_frozen Γ f m1 m2 p1 p2 σ :
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → frozen p1 ↔ frozen p2.
Proof.
  unfold frozen. destruct 1; simpl; auto.
  rewrite !(injective_iff Ptr). eapply (addr_refine_frozen Γ f); eauto.
Qed.
Lemma ptr_refine_id Γ m p σ : (Γ,m) ⊢ p : σ → p ⊑{Γ@m} p : σ.
Proof. destruct 1; constructor; eauto using addr_refine_id. Qed.
Lemma ptr_refine_compose Γ f g m1 m2 m3 p1 p2 p3 σ :
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → p2 ⊑{Γ,g@m2↦m3} p3 : σ →
  p1 ⊑{Γ,f ◎ g@m1↦m3} p3 : σ.
Proof.
  destruct 1; inversion_clear 1; constructor; eauto using addr_refine_compose.
Qed.
Lemma ptr_refine_weaken Γ Γ' f f' m1 m2 m1' m2' p1 p2 σ :
  ✓ Γ → p1 ⊑{Γ,f@m1↦m2} p2 : σ → Γ ⊆ Γ' → f ⊆ f' →
  (∀ o τ, type_of_index m1 o = Some τ → type_of_index m1' o = Some τ) →
  (∀ o τ, type_of_index m2 o = Some τ → type_of_index m2' o = Some τ) →
  p1 ⊑{Γ',f'@m1'↦m2'} p2 : σ.
Proof.
  destruct 2; constructor;
    eauto using ptr_type_valid_weaken, addr_refine_weaken.
Qed.
Lemma ptr_refine_eq Γ m p1 p2 σ : p1 ⊑{Γ@m} p2 : σ → p1 = p2.
Proof. destruct 1; f_equal; eauto using addr_refine_eq. Qed.
Lemma ptr_refine_unique Γ f m1 m2 p1 p2 p3 σ2 σ3 :
  p1 ⊑{Γ,f@m1↦m2} p2 : σ2 → p1 ⊑{Γ,f@m1↦m2} p3 : σ3 → p2 = p3.
Proof.
  destruct 1; inversion_clear 1; f_equal; eauto using addr_refine_unique.
Qed.
Lemma ptr_freeze_refine Γ f m1 m2 p1 p2 σ :
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → freeze true p1 ⊑{Γ,f@m1↦m2} freeze true p2 : σ.
Proof. destruct 1; simpl; constructor; eauto using addr_freeze_refine. Qed.
Lemma ptr_plus_ok_refine Γ m1 m2 f p1 p2 σ j :
  ✓ Γ → m1 ⊑{Γ,f} m2 →
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → ptr_plus_ok Γ m1 j p1 → ptr_plus_ok Γ m2 j p2.
Proof. destruct 3; simpl; eauto using addr_plus_ok_refine. Qed.
Lemma ptr_plus_refine Γ f m1 m2 p1 p2 σ j :
  ✓ Γ → m1 ⊑{Γ,f} m2 → ptr_plus_ok Γ m1 j p1 →
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → ptr_plus Γ j p1 ⊑{Γ,f@m1↦m2} ptr_plus Γ j p2 : σ.
Proof. destruct 4; simpl; constructor; eauto using addr_plus_refine. Qed.
Lemma ptr_minus_ok_refine Γ m1 m2 f p1 p2 p3 p4 σ :
  ✓ Γ → m1 ⊑{Γ,f} m2 → p1 ⊑{Γ,f@m1↦m2} p2 : σ → p3 ⊑{Γ,f@m1↦m2} p4 : σ→
  ptr_minus_ok m1 p1 p3 → ptr_minus_ok m2 p2 p4.
Proof. destruct 3, 1; simpl; eauto using addr_minus_ok_refine. Qed.
Lemma ptr_minus_refine Γ f m1 m2 p1 p2 p3 p4 σ :
  ✓ Γ → ptr_minus_ok m1 p1 p3 →
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → p3 ⊑{Γ,f@m1↦m2} p4 : σ →
  ptr_minus Γ p1 p3 = ptr_minus Γ p2 p4.
Proof. destruct 3, 1; simpl; eauto using addr_minus_refine. Qed.
Lemma ptr_cast_ok_refine Γ f m1 m2 p1 p2 σ σc :
  p1 ⊑{Γ,f@m1↦m2} p2 : σ → ptr_cast_ok Γ σc p1 → ptr_cast_ok Γ σc p2.
Proof. destruct 1; simpl; eauto using addr_cast_ok_refine. Qed.
Lemma ptr_cast_refine Γ f m1 m2 p1 p2 σ σc :
  ptr_cast_ok Γ σc p1 → ptr_type_valid Γ σc → p1 ⊑{Γ,f@m1↦m2} p2 : σ →
  ptr_cast σc p1 ⊑{Γ,f@m1↦m2} ptr_cast σc p2 : σc.
Proof. destruct 3; constructor; eauto using addr_cast_refine. Qed.
End pointers.
