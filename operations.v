(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_map values.
Require Import pointer_casts.
Local Open Scope ctype_scope.

Section operations_definitions.
  Context `{Env Ti}.

  (** ** Operations on addresses *)
  Definition addr_eq_ok (Γ : env Ti) (m : mem Ti) (a1 a2 : addr Ti) : Prop :=
    index_alive' m (addr_index a1) ∧ index_alive' m (addr_index a2) ∧
    (addr_index a1 ≠ addr_index a2 → addr_strict Γ a1 ∧ addr_strict Γ a2).
  Definition addr_eq (Γ : env Ti) (a1 a2 : addr Ti) : bool :=
    if decide (addr_index a1 = addr_index a2)
    then bool_decide (addr_object_offset Γ a1 = addr_object_offset Γ a2)
    else false.
  Definition addr_plus_ok (Γ : env Ti) (m : mem Ti)
      (j : Z) (a : addr Ti) : Prop :=
    index_alive' m (addr_index a) ∧
    (0 ≤ addr_byte a + j * ptr_size_of Γ (type_of a)
       ≤ size_of Γ (addr_type_base a) * ref_size (addr_ref_base a))%Z.
  Global Arguments addr_plus_ok _ _ _ !_ /.
  Definition addr_plus (Γ : env Ti) (j : Z) (a : addr Ti): addr Ti :=
    let 'Addr x r i τ σ σp := a
    in Addr x r (Z.to_nat (i + j * ptr_size_of Γ σp)) τ σ σp.
  Global Arguments addr_plus _ _ !_ /.
  Definition addr_minus_ok (m : mem Ti) (a1 a2 : addr Ti) : Prop :=
    index_alive' m (addr_index a1) ∧
    addr_index a1 = addr_index a2 ∧
    freeze true <$> addr_ref_base a1 = freeze true <$> addr_ref_base a2.
  Global Arguments addr_minus_ok _ !_ !_ /.
  Definition addr_minus (Γ : env Ti) (a1 a2 : addr Ti) : Z :=
    ((addr_byte a1 - addr_byte a2) `div` ptr_size_of Γ (type_of a1))%Z.
  Global Arguments addr_minus _ !_ !_ /.
  Definition addr_cast_ok (Γ : env Ti) (m : mem Ti)
      (σp : ptr_type Ti) (a : addr Ti) : Prop :=
    index_alive' m (addr_index a) ∧
    addr_type_base a >*> σp ∧
    (ptr_size_of Γ σp | addr_byte a).
  Global Arguments addr_cast_ok _ _ _ !_ /.
  Definition addr_cast (σp : ptr_type Ti) (a : addr Ti) : addr Ti :=
    let 'Addr o r i τ σ _ := a in Addr o r i τ σ σp.
  Global Arguments addr_cast _ !_ /.

  (** ** Operations on pointers *)
  Definition ptr_alive' (m : mem Ti) (p : ptr Ti) : Prop :=
    match p with Ptr a => index_alive' m (addr_index a) | NULL _ => True end.
  Definition ptr_compare_ok (Γ : env Ti)  (m : mem Ti)
      (c : compop) (p1 p2 : ptr Ti) : Prop :=
    match p1, p2, c with
    | Ptr a1, Ptr a2, EqOp => addr_eq_ok Γ m a1 a2
    | Ptr a1, Ptr a2, _ => addr_minus_ok m a1 a2
    | NULL _, Ptr a2, EqOp => index_alive' m (addr_index a2)
    | Ptr a1, NULL _, EqOp => index_alive' m (addr_index a1)
    | NULL _, NULL _, _ => True
    | _, _, _ => False
    end.
  Definition ptr_compare (Γ : env Ti) (c : compop) (p1 p2 : ptr Ti) : bool :=
    match p1, p2, c with
    | Ptr a1, Ptr a2, EqOp => addr_eq Γ a1 a2
    | Ptr a1, Ptr a2, _ => Z_comp c (addr_minus Γ a1 a2) 0
    | NULL _, Ptr a2, _ => false
    | Ptr a1, NULL _, _ => false
    | NULL _, NULL _, (EqOp | LeOp) => true
    | NULL _, NULL _, LtOp => false
    end.
  Definition ptr_plus_ok (Γ : env Ti) (m : mem Ti) (j : Z) (p : ptr Ti) :=
    match p with NULL _ => j = 0 | Ptr a => addr_plus_ok Γ m j a end.
  Global Arguments ptr_plus_ok _ _ _ !_ /.
  Definition ptr_plus (Γ : env Ti) (j : Z) (p : ptr Ti) : ptr Ti :=
    match p with NULL τ => NULL τ | Ptr a => Ptr (addr_plus Γ j a) end.
  Global Arguments ptr_plus _ _ !_ /.
  Definition ptr_minus_ok (m : mem Ti) (p1 p2 : ptr Ti) : Prop :=
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
  Definition ptr_cast_ok (Γ : env Ti) (m : mem Ti)
      (σp : ptr_type Ti) (p : ptr Ti) : Prop :=
    match p with NULL _ => True | Ptr a => addr_cast_ok Γ m σp a end.
  Global Arguments ptr_cast_ok _ _ _ !_ /.
  Definition ptr_cast (σp : ptr_type Ti) (p : ptr Ti) : ptr Ti :=
    match p with NULL _ => NULL σp | Ptr a => Ptr (addr_cast σp a) end.
  Global Arguments ptr_cast _ !_ /.  

  (** ** Operations on base values *)
  Definition base_val_true (m : mem Ti) (vb : base_val Ti) : Prop :=
    match vb with
    | VInt _ x => x ≠ 0
    | VPtr (Ptr a) => index_alive' m (addr_index a)
    | _ => False
    end.
  Definition base_val_false (vb : base_val Ti) : Prop :=
    match vb with VInt _ x => x = 0 | VPtr (NULL _) => True | _ => False end.
  Definition base_val_0 (τb : base_type Ti) : base_val Ti :=
    match τb with
    | voidT => VVoid | intT τi => VInt τi 0 | τ.* => VPtr (NULL τ)
    end%BT.
  Inductive base_unop_typed : unop → base_type Ti → base_type Ti → Prop :=
    | TInt_unop_typed op τi :
       base_unop_typed op (intT τi) (intT (int_unop_type_of op τi))
    | TPtr_NotOp_typed τ : base_unop_typed NotOp (τ.*) sintT.
  Definition base_unop_type_of (op : unop)
      (τb : base_type Ti) : option (base_type Ti) :=
    match τb, op with
    | intT τi, op => Some (intT (int_unop_type_of op τi))
    | τ.*, NotOp => Some sintT
    | _, _ => None
    end%BT.
  Definition base_val_unop_ok (m : mem Ti)
      (op : unop) (vb : base_val Ti) : Prop :=
    match vb, op with
    | VInt τi x, op => int_unop_ok op x τi
    | VPtr p, NotOp => ptr_alive' m p
    | _, _ => False
    end.
  Global Arguments base_val_unop_ok _ !_ !_ /.
  Definition base_val_unop (op : unop) (vb : base_val Ti) : base_val Ti :=
    match vb, op with
    | VInt τi x, op => VInt (int_unop_type_of op τi) (int_unop op x τi)
    | VPtr p, _ => VInt sintT (match p with NULL _ => 1 | Ptr _ => 0 end)
    | _, _ => vb (* dummy *)
    end.
  Global Arguments base_val_unop !_ !_ /.

  Inductive base_binop_typed :
        binop → base_type Ti → base_type Ti → base_type Ti → Prop :=
    | TInt_binop_typed op τi1 τi2 :
       base_binop_typed op (intT τi1) (intT τi2)
         (intT (int_binop_type_of op τi1 τi2))
    | CompOp_TPtr_TPtr_typed c τp :
       base_binop_typed (CompOp c) (τp.*) (τp.*) sintT
    | PlusOp_TPtr_TInt_typed τ σ :
       base_binop_typed (ArithOp PlusOp) (Some τ.*) (intT σ) (Some τ.*)
    | PlusOp_VInt_TPtr_typed τ σ :
       base_binop_typed (ArithOp PlusOp) (intT σ) (Some τ.*) (Some τ.*)
    | MinusOp_TPtr_TInt_typed τ σi :
       base_binop_typed (ArithOp MinusOp) (Some τ.*) (intT σi) (Some τ.*)
    | MinusOp_TInt_TPtr_typed τ σi :
       base_binop_typed (ArithOp MinusOp) (intT σi) (Some τ.*) (Some τ.*)
    | MinusOp_TPtr_TPtr_typed τ  :
       base_binop_typed (ArithOp MinusOp) (Some τ.*) (Some τ.*) sptrT.
  Definition base_binop_type_of
      (op : binop) (τb1 τb2 : base_type Ti) : option (base_type Ti) :=
    match τb1, τb2, op with
    | intT τi1, intT τi2, op => Some (intT (int_binop_type_of op τi1 τi2))
    | τp1.*, τp2.*, CompOp _ => guard (τp1 = τp2); Some sintT
    | Some τ.*, intT σ, ArithOp (PlusOp | MinusOp) => Some (Some τ.*)
    | intT σ, Some τ.*, ArithOp (PlusOp | MinusOp) => Some (Some τ.*)
    | Some τ1.*, Some τ2.*, ArithOp MinusOp => guard (τ1 = τ2); Some sptrT
    | _, _, _ => None
    end%BT.
  Definition base_val_binop_ok (Γ : env Ti) (m : mem Ti)
      (op : binop) (vb1 vb2 : base_val Ti) : Prop :=
    match vb1, vb2, op with
    | VInt τi1 x1, VInt τi2 x2, op => int_binop_ok op x1 τi1 x2 τi2
    | VPtr p1, VPtr p2, CompOp c => ptr_compare_ok Γ m c p1 p2
    | VPtr p, VInt _ x, ArithOp PlusOp => ptr_plus_ok Γ m x p
    | VInt _ x, VPtr p, ArithOp PlusOp => ptr_plus_ok Γ m x p
    | VPtr p, VInt _ x, ArithOp MinusOp => ptr_plus_ok Γ m (-x) p
    | VInt _ x, VPtr p, ArithOp MinusOp => ptr_plus_ok Γ m (-x) p
    | VPtr p1, VPtr p2, ArithOp MinusOp => ptr_minus_ok m p1 p2
    | _, _, _ => False
    end.
  Global Arguments base_val_binop_ok _ _ !_ !_ !_ /.
  Definition base_val_binop (Γ : env Ti)
      (op : binop) (v1 v2 : base_val Ti) : base_val Ti :=
    match v1, v2, op with
    | VInt τi1 x1, VInt τi2 x2, op =>
       VInt (int_binop_type_of op τi1 τi2) (int_binop op x1 τi1 x2 τi2)
    | VPtr p1, VPtr p2, CompOp c =>
       VInt sintT (if ptr_compare Γ c p1 p2 then 1 else 0)
    | VPtr p, VInt _ i, ArithOp PlusOp => VPtr (ptr_plus Γ i p)
    | VInt _ i, VPtr p, ArithOp PlusOp => VPtr (ptr_plus Γ i p)
    | VPtr p, VInt _ i, ArithOp MinusOp => VPtr (ptr_plus Γ (-i) p)
    | VInt _ i, VPtr p, ArithOp MinusOp => VPtr (ptr_plus Γ (-i) p)
    | VPtr p1, VPtr p2, ArithOp MinusOp => VInt sptrT (ptr_minus Γ p1 p2)
    | _, _, _ => v1 (* dummy *)
    end.
  Global Arguments base_val_binop _ !_ !_ !_ /.

  Inductive base_cast_typed (Γ : env Ti) :
       base_type Ti → base_type Ti → Prop :=
    | TVoid_cast_typed τb : base_cast_typed Γ τb voidT
    | TInt_cast_typed τi1 τi2 : base_cast_typed Γ (intT τi1) (intT τi2)
    | TPtr_to_TPtr_cast_typed τ : base_cast_typed Γ (Some τ.*) (Some τ.*)
    | TPtr_to_void_cast_typed τp : base_cast_typed Γ (τp.*) (None.*)
    | TPtr_to_uchar_cast_typed τp : base_cast_typed Γ (τp.*) (Some ucharT.*)
    | TPtr_of_void_cast_typed τp : ✓{Γ} τp → base_cast_typed Γ (None.*) (τp.*)
    | TPtr_of_uchar_cast_typed τp :
       ✓{Γ} τp → base_cast_typed Γ (Some ucharT.*) (τp.*).
  Definition base_val_cast_ok (Γ : env Ti) (m : mem Ti)
      (τb : base_type Ti) (vb : base_val Ti) : Prop :=
    match vb, τb with
    | (VVoid | VInt _ _ | VByte _), voidT => True
    | VIndet τi, voidT => τi = ucharT
    | VPtr p, voidT => ptr_alive' m p
    | VInt _ x, intT τi => int_cast_ok τi x
    | VPtr p, τ.* => ptr_cast_ok Γ m τ p
    | VByte _, intT τi => τi = ucharT%IT
    | VIndet τi, intT τi' => τi = ucharT ∧ τi' = ucharT%IT
    | _, _ => False
    end%BT.
  Global Arguments base_val_cast_ok _ _ !_ !_ /.
  Definition base_val_cast (τb : base_type Ti)
      (vb : base_val Ti) : base_val Ti :=
    match vb, τb with
    | _, voidT => VVoid
    | VInt _ x, intT τi => VInt τi (int_cast τi x)
    | VPtr p, τ.* => VPtr (ptr_cast τ p)
    | _ , _ => vb
    end%BT.
  Global Arguments base_val_cast !_ !_ /.

  (** ** Operations on values *)
  Definition val_0 (Γ : env Ti) : type Ti → val Ti := type_iter
    (**i TBase     *) (λ τb, VBase (base_val_0 τb))
    (**i TArray    *) (λ τ n x, VArray τ (replicate n x))
    (**i TCompound *) (λ c s τs rec,
      match c with
      | Struct_kind => VStruct s (rec <$> τs)
      | Union_kind => VUnion s 0 (default (VUnionAll s []) (τs !! 0) rec)
      end) Γ.

  Definition val_true (m : mem Ti) (v : val Ti) : Prop :=
    match v with VBase vb => base_val_true m vb | _ => False end.
  Definition val_false (v : val Ti) : Prop :=
    match v with VBase vb => base_val_false vb | _ => False end.

  Inductive unop_typed : unop → type Ti → type Ti → Prop :=
    | TBase_unop_typed op τb σb :
       base_unop_typed op τb σb → unop_typed op (baseT τb) (baseT σb).
  Definition unop_type_of (op : unop) (τ : type Ti) : option (type Ti) :=
    match τ with
    | baseT τb => σb ← base_unop_type_of op τb; Some (baseT σb) | _ => None
    end.
  Definition val_unop_ok (m : mem Ti) (op : unop) (v : val Ti) : Prop :=
    match v with VBase vb => base_val_unop_ok m op vb | _ => False end.
  Global Arguments val_unop_ok _ !_ !_ /.
  Definition val_unop (op : unop) (v : val Ti) : val Ti :=
    match v with VBase vb => VBase (base_val_unop op vb) | _ => v end.
  Global Arguments val_unop !_ !_ /.

  Inductive binop_typed : binop → type Ti → type Ti → type Ti → Prop :=
    | TBase_binop_typed op τb1 τb2 σb :
       base_binop_typed op τb1 τb2 σb →
       binop_typed op (baseT τb1) (baseT τb2) (baseT σb).
  Definition binop_type_of (op : binop) (τ1 τ2 : type Ti) : option (type Ti) :=
    match τ1, τ2 with
    | baseT τb1, baseT τb2 =>
       σb ← base_binop_type_of op τb1 τb2; Some (baseT σb)
    | _, _ => None
    end.
  Definition val_binop_ok (Γ : env Ti) (m : mem Ti)
      (op : binop) (v1 v2 : val Ti) : Prop :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => base_val_binop_ok Γ m op vb1 vb2 | _, _ => False
    end.
  Global Arguments val_binop_ok _ _ !_ !_ !_ /.
  Definition val_binop (Γ : env Ti) (op : binop) (v1 v2 : val Ti) : val Ti :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => VBase (base_val_binop Γ op vb1 vb2) | _, _ => v1
    end.
  Global Arguments val_binop _ !_ !_ !_ /.

  Inductive cast_typed (Γ : env Ti) : type Ti → type Ti → Prop :=
    | cast_typed_self τ : cast_typed Γ τ τ
    | TBase_cast_typed τb1 τb2 :
       base_cast_typed Γ τb1 τb2 → cast_typed Γ (baseT τb1) (baseT τb2)
    | TBase_TVoid_cast_typed τ : cast_typed Γ τ voidT.
  Definition val_cast_ok (Γ : env Ti) (m : mem Ti)
      (τp : ptr_type Ti) (v : val Ti) : Prop :=
    match v, τp with
    | VBase vb, Some (baseT τb) => base_val_cast_ok Γ m τb vb | _, _ => True
    end.
  Global Arguments val_cast_ok _ _ !_ !_ /.
  Definition val_cast (τp : ptr_type Ti) (v : val Ti) : val Ti :=
    match v, τp with
    | VBase vb, Some (baseT τb) => VBase (base_val_cast τb vb)
    | _, Some voidT => VBase VVoid | _ , _ => v
    end.
  Global Arguments val_cast !_ !_ /.
End operations_definitions.

Section operations.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τb σb : base_type Ti.
Implicit Types τp σp : ptr_type Ti.
Implicit Types τ σ : type Ti.
Implicit Types a : addr Ti.
Implicit Types vb : base_val Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.
Hint Immediate index_alive_1'.
Hint Resolve index_alive_2'.

(** ** Properties of operations on addresses *)
Lemma addr_eq_ok_weaken Γ1 Γ2 Γm1 m1 m2 a1 a2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a1 : τp1 → (Γ1,Γm1) ⊢ a2 : τp2 →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  addr_eq_ok Γ1 m1 a1 a2 → Γ1 ⊆ Γ2 → addr_eq_ok Γ2 m2 a1 a2.
Proof. unfold addr_eq_ok. intuition eauto using addr_strict_weaken. Qed.
Lemma addr_eq_ok_erase Γ m a1 a2 :
  addr_eq_ok Γ (cmap_erase m) a1 a2 = addr_eq_ok Γ m a1 a2.
Proof. unfold addr_eq_ok. by rewrite !index_alive_erase'. Qed.
Lemma addr_eq_weaken Γ1 Γ2 Γm1 a1 a2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a1 : τp1 → (Γ1,Γm1) ⊢ a2 : τp2 →
  Γ1 ⊆ Γ2 → addr_eq Γ1 a1 a2 = addr_eq Γ2 a1 a2.
Proof.
  unfold addr_eq; intros.
  by erewrite !(addr_object_offset_weaken Γ1 Γ2) by eauto.
Qed.
Lemma addr_plus_typed Γ Γm m a σp j :
  ✓ Γ → (Γ,Γm) ⊢ a : σp → addr_plus_ok Γ m j a →
  (Γ,Γm) ⊢ addr_plus Γ j a : σp.
Proof.
  destruct 2 as [o r i τ σ σp]; intros (?&?&?);
    constructor; simpl in *; split_ands; auto.
  { apply Nat2Z.inj_le. by rewrite Nat2Z.inj_mul, Z2Nat.id by done. }
  rewrite <-(Nat2Z.id (ptr_size_of Γ σp)) at 1.
  rewrite Z2Nat_divide by auto with zpos.
  apply Z.divide_add_r; [by apply Nat2Z_divide|by apply Z.divide_mul_r].
Qed.
Lemma addr_plus_ok_weaken Γ1 Γ2 Γm1 m1 m2 a σp j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a : σp → addr_plus_ok Γ1 m1 j a →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  addr_plus_ok Γ2 m2 j a.
Proof.
  unfold addr_plus_ok; intros ?? (?&?&?) ??; simplify_type_equality'.
  erewrite <-addr_size_of_weaken, <-(size_of_weaken _ Γ2)
    by eauto using addr_typed_type_base_valid; eauto.
Qed.
Lemma addr_plus_ok_erase Γ m a j:
  addr_plus_ok Γ (cmap_erase m) j a = addr_plus_ok Γ m j a.
Proof. unfold addr_plus_ok. by rewrite !index_alive_erase'. Qed.
Lemma addr_plus_weaken Γ1 Γ2 Γm1 a σp j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a : σp → Γ1 ⊆ Γ2 → addr_plus Γ1 j a = addr_plus Γ2 j a.
Proof.
  intros ? Ha ?. assert (ptr_size_of Γ1 σp = ptr_size_of Γ2 σp)
    by eauto using addr_size_of_weaken.
  destruct Ha; simplify_type_equality'; congruence.
Qed.
Lemma addr_type_of_plus Γ a j : type_of (addr_plus Γ j a) = type_of a.
Proof. by destruct a. Qed.
Lemma addr_type_base_plus Γ a j :
  addr_type_base (addr_plus Γ j a) = addr_type_base a.
Proof. by destruct a. Qed.
Lemma addr_index_plus Γ a j : addr_index (addr_plus Γ j a) = addr_index a.
Proof. by destruct a. Qed.
Lemma addr_plus_0 Γ a : addr_plus Γ 0 a = a.
Proof. destruct a; simpl. by rewrite Z.mul_0_l, Z.add_0_r, Nat2Z.id. Qed.
Lemma addr_plus_plus Γ a j1 j2 :
  (0 ≤ addr_byte a + j2 * ptr_size_of Γ (type_of a))%Z →
  addr_plus Γ j1 (addr_plus Γ j2 a) = addr_plus Γ (j1 + j2) a.
Proof.
  intros. destruct a as [o r i σ σp]; do 2 f_equal'.
  by rewrite Z2Nat.id, (Z.add_comm j1), Z.mul_add_distr_r, Z.add_assoc.
Qed.
Lemma addr_plus_plus_nat Γ a (j1 j2 : nat) :
  addr_plus Γ j1 (addr_plus Γ j2 a) = addr_plus Γ(j1 + j2)%nat a.
Proof. rewrite Nat2Z.inj_add. apply addr_plus_plus; auto with zpos. Qed.
Lemma addr_is_obj_plus Γ a j : addr_is_obj (addr_plus Γ j a) ↔ addr_is_obj a.
Proof. by destruct a. Qed.
Lemma addr_ref_base_plus Γ a j :
  addr_ref_base (addr_plus Γ j a) = addr_ref_base a.
Proof. by destruct a. Qed.
Lemma addr_minus_typed Γ Γm a1 a2 σp :
  ✓ Γ → (Γ,Γm) ⊢ a1 : σp → (Γ,Γm) ⊢ a2 : σp →
  int_typed (addr_minus Γ a1 a2) sptrT.
Proof.
  intros HΓ Ha1 Ha2; unfold addr_minus; simplify_type_equality'.
  assert (ptr_size_of Γ σp ≠ 0) by eauto using addr_size_of_ne_0.
  assert (int_upper sptrT ≤ ptr_size_of Γ σp * int_upper sptrT)%Z.
  { transitivity (1 * int_upper sptrT)%Z; [lia|].
    apply Z.mul_le_mono_nonneg_r; auto using int_upper_pos with zpos. }
  destruct (addr_byte_representable Γ Γm a1 σp) as [_ ?]; auto.
  destruct (addr_byte_representable Γ Γm a2 σp) as [_ ?]; auto.
  split; [|apply Z.div_lt_upper_bound; lia].
  apply Z.div_le_lower_bound. lia. rewrite int_lower_upper_signed by done; lia.
Qed.
Lemma addr_minus_ok_weaken m1 m2 a1 a2:
  addr_minus_ok m1 a1 a2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  addr_minus_ok m2 a1 a2.
Proof. intros [??]; split; eauto. Qed.
Lemma addr_minus_ok_erase m a1 a2 :
  addr_minus_ok (cmap_erase m) a1 a2 = addr_minus_ok m a1 a2.
Proof. unfold addr_minus_ok. by rewrite !index_alive_erase'. Qed.
Lemma addr_minus_weaken Γ1 Γ2 Γm1 a1 a2 σp1 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a1 : σp1 →
  Γ1 ⊆ Γ2 → addr_minus Γ1 a1 a2 = addr_minus Γ2 a1 a2.
Proof.
  intros. unfold addr_minus; simplify_type_equality.
  by erewrite (addr_size_of_weaken Γ1 Γ2) by eauto.
Qed.
Lemma addr_cast_typed Γ Γm m a σp τp :
  (Γ,Γm) ⊢ a : σp → addr_cast_ok Γ m τp a → (Γ,Γm) ⊢ addr_cast τp a : τp.
Proof. intros [] (?&?&?); constructor; eauto. Qed.
Lemma addr_cast_ok_weaken Γ1 Γ2 Γm1 m1 m2 a σp τp :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a : σp →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  addr_cast_ok Γ1 m1 τp a → Γ1 ⊆ Γ2 → addr_cast_ok Γ2 m2 τp a.
Proof.
  intros ??? (?&?&?) ?; repeat split; auto. destruct τp as [τ|]; simpl; auto.  
  by erewrite <-size_of_weaken
    by eauto using castable_type_valid, addr_typed_type_base_valid.
Qed.
Lemma addr_cast_ok_erase Γ m a τp :
  addr_cast_ok Γ (cmap_erase m) τp a = addr_cast_ok Γ m τp a.
Proof. unfold addr_cast_ok. by rewrite !index_alive_erase'. Qed.
Lemma addr_type_cast a σp : type_of (addr_cast σp a) = σp.
Proof. by destruct a. Qed.
Lemma addr_index_cast a σp : addr_index (addr_cast σp a) = addr_index a.
Proof. by destruct a. Qed.
Lemma addr_ref_cast Γ a σp : addr_ref Γ (addr_cast σp a) = addr_ref Γ a.
Proof. by destruct a. Qed.
Lemma addr_ref_byte_cast Γ a σp :
  addr_ref_byte Γ (addr_cast σp a) = addr_ref_byte Γ a.
Proof. by destruct a. Qed.
Lemma addr_cast_self Γ Γm a σp : (Γ,Γm) ⊢ a : σp → addr_cast σp a = a.
Proof. by destruct 1. Qed.
Lemma addr_is_obj_cast a σp :
  addr_is_obj (addr_cast σp a) ↔ σp = Some (addr_type_base a).
Proof. by destruct a. Qed.
Lemma addr_ref_plus_char_cast Γ Γm a σp j :
  ✓ Γ → (Γ,Γm) ⊢ a : σp → addr_is_obj a → j < ptr_size_of Γ σp →
  addr_ref Γ (addr_plus Γ j (addr_cast (Some ucharT) a)) = addr_ref Γ a.
Proof.
  destruct 2 as [o r i τ σ σp ?????]; intros ??; simplify_equality'; f_equal.
  rewrite size_of_char, Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  symmetry. apply Nat.div_unique with (i `mod` size_of Γ σ + j).
  { by rewrite (λ x y H, proj2 (Nat.mod_divide x y H))
      by eauto using size_of_ne_0, ref_typed_type_valid. }
  by rewrite Nat.add_assoc, <-Nat.div_mod
    by eauto using ref_typed_type_valid, size_of_ne_0.
Qed.
Lemma addr_ref_byte_plus_char_cast Γ Γm a σp j :
  ✓ Γ → (Γ,Γm) ⊢ a : σp → addr_is_obj a → j < ptr_size_of Γ σp →
  addr_ref_byte Γ (addr_plus Γ j (addr_cast (Some ucharT) a)) = j.
Proof.
  destruct 2 as [o r i τ σ σp]; intros; simplify_equality'.
  rewrite size_of_char, Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  rewrite <-Nat.add_mod_idemp_l, (λ y H, proj2 (Nat.mod_divide i y H)),
    Nat.add_0_l by eauto using ref_typed_type_valid, size_of_ne_0.
  by apply Nat.mod_small.
Qed.
Lemma addr_byte_lt_size_char_cast Γ Γm a σp j :
  ✓ Γ → (Γ,Γm) ⊢ a : σp → addr_is_obj a → j < ptr_size_of Γ σp →
  addr_byte a < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a) →
  addr_byte (addr_plus Γ j (addr_cast (Some ucharT) a))
    < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a).
Proof.
  destruct 2 as [o r i τ σ σp ?????? Hi]; intros; simplify_equality'.
  rewrite size_of_char, Z.mul_1_r,Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  apply Nat.lt_le_trans with (i + size_of Γ σ); [lia|].
  destruct Hi as [? ->].
  rewrite <-Nat.mul_succ_l, Nat.mul_comm, <-Nat.mul_le_mono_pos_l,
    Nat.le_succ_l, (Nat.mul_lt_mono_pos_r (size_of Γ σ))
    by eauto using ref_typed_type_valid, size_of_pos; lia.
Qed.

(** ** Properties of operations on pointers *)
Global Instance ptr_alive_dec' m p : Decision (ptr_alive' m p).
Proof.
 refine
  match p with
  | Ptr a => decide (index_alive' m (addr_index a)) | NULL _ => left _
  end; done.
Defined.
Lemma ptr_alive_weaken' m1 m2 p :
  ptr_alive' m1 p → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_alive' m2 p.
Proof. destruct p; simpl; auto. Qed.
Lemma ptr_alive_1' m p : ptr_alive' m p → ptr_alive ('{m}) p.
Proof. destruct p; simpl; eauto. Qed.
Hint Resolve ptr_alive_1'.
Lemma ptr_alive_erase' m p : ptr_alive' (cmap_erase m) p = ptr_alive' m p.
Proof. unfold ptr_alive'. by destruct p; rewrite ?index_alive_erase'. Qed.
Global Instance ptr_compare_ok_dec Γ m c p1 p2 :
  Decision (ptr_compare_ok Γ m c p1 p2).
Proof. destruct p1, p2, c; apply _. Defined.
Global Instance ptr_plus_ok_dec Γ m j p : Decision (ptr_plus_ok Γ m j p).
Proof. destruct p; apply _. Defined.
Global Instance ptr_minus_ok_dec m p1 p2 : Decision (ptr_minus_ok m p1 p2).
Proof. destruct p1, p2; apply _. Defined.
Global Instance ptr_cast_ok_dec Γ m σp p : Decision (ptr_cast_ok Γ m σp p).
Proof. destruct p; apply _. Defined.
Lemma ptr_plus_typed Γ Γm m p σp j :
  ✓ Γ → (Γ,Γm) ⊢ p : σp → ptr_plus_ok Γ m j p →
  (Γ,Γm) ⊢ ptr_plus Γ j p : σp.
Proof. destruct 2; simpl; constructor; eauto using addr_plus_typed. Qed.
Lemma ptr_minus_typed Γ Γm p1 p2 σp :
  ✓ Γ → (Γ,Γm) ⊢ p1 : σp → (Γ,Γm) ⊢ p2 : σp →
  int_typed (ptr_minus Γ p1 p2) sptrT.
Proof.
  destruct 2, 1; simpl;
    eauto using addr_minus_typed, int_typed_small with lia.
Qed.
Lemma ptr_cast_typed Γ Γm m p τp σp :
  (Γ,Γm) ⊢ p : τp → ptr_cast_ok Γ m σp p →
  ✓{Γ} σp → (Γ,Γm) ⊢ ptr_cast σp p : σp.
Proof. destruct 1; simpl; constructor; eauto using addr_cast_typed. Qed.

Lemma ptr_compare_ok_weaken Γ1 Γ2 Γm1 m1 m2 c p1 p2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p1 : τp1 → (Γ1,Γm1) ⊢ p2 : τp2 →
  ptr_compare_ok Γ1 m1 c p1 p2 →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_compare_ok Γ2 m2 c p1 p2.
Proof.
  destruct 2, 1, c; simpl; eauto using addr_minus_ok_weaken, addr_eq_ok_weaken.
Qed.
Lemma ptr_compare_ok_erase Γ m c p1 p2:
  ptr_compare_ok Γ (cmap_erase m) c p1 p2 = ptr_compare_ok Γ m c p1 p2.
Proof.
  unfold ptr_compare_ok. by destruct p1, p2;
    rewrite ?index_alive_erase', ?addr_minus_ok_erase, ?addr_eq_ok_erase.
Qed.
Lemma ptr_compare_weaken Γ1 Γ2 Γm1 c p1 p2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p1 : τp1 → (Γ1,Γm1) ⊢ p2 : τp2 →
  Γ1 ⊆ Γ2 → ptr_compare Γ1 c p1 p2 = ptr_compare Γ2 c p1 p2.
Proof.
  destruct 2,1,c; simpl; intros; eauto 2 using addr_eq_weaken;
    by erewrite addr_minus_weaken by eauto.
Qed.
Lemma ptr_plus_ok_weaken Γ1 Γ2 Γm1 m1 m2 p τp j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τp → ptr_plus_ok Γ1 m1 j p →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_plus_ok Γ2 m2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_ok_weaken. Qed.
Lemma ptr_plus_ok_erase Γ m j p :
  ptr_plus_ok Γ (cmap_erase m) j p = ptr_plus_ok Γ m j p.
Proof. destruct p; simpl; auto using addr_plus_ok_erase. Qed.
Lemma ptr_plus_weaken Γ1 Γ2 Γm1 p τp j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τp → Γ1 ⊆ Γ2 → ptr_plus Γ1 j p = ptr_plus Γ2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_weaken, f_equal. Qed.
Lemma ptr_minus_ok_weaken m1 m2 p1 p2:
  ptr_minus_ok m1 p1 p2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_minus_ok m2 p1 p2.
Proof. destruct p1, p2; simpl; eauto using addr_minus_ok_weaken. Qed.
Lemma ptr_minus_ok_erase m p1 p2 :
  ptr_minus_ok (cmap_erase m) p1 p2 = ptr_minus_ok m p1 p2.
Proof. destruct p1, p2; simpl; auto using addr_minus_ok_erase. Qed.
Lemma ptr_minus_weaken Γ1 Γ2 Γm1 p1 p2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p1 : τp1 → (Γ1,Γm1) ⊢ p2 : τp2 →
  Γ1 ⊆ Γ2 → ptr_minus Γ1 p1 p2 = ptr_minus Γ2 p1 p2.
Proof. destruct 2, 1; simpl; eauto using addr_minus_weaken. Qed.
Lemma ptr_cast_ok_weaken Γ1 Γ2 Γm1 m1 m2 p τp σp :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τp → ptr_cast_ok Γ1 m1 σp p → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_cast_ok Γ2 m2 σp p.
Proof. destruct 2; simpl; eauto using addr_cast_ok_weaken. Qed.
Lemma ptr_cast_ok_erase Γ m p τp :
  ptr_cast_ok Γ (cmap_erase m) τp p = ptr_cast_ok Γ m τp p.
Proof. destruct p; simpl; auto using addr_cast_ok_erase. Qed.
Lemma ptr_compare_ok_alive_l Γ m c p1 p2 :
  ptr_compare_ok Γ m c p1 p2 → ptr_alive ('{m}) p1.
Proof.
  destruct p1, p2, c; simpl; unfold addr_minus_ok, addr_eq_ok; naive_solver.
Qed.
Lemma ptr_compare_ok_alive_r Γ m c p1 p2 :
  ptr_compare_ok Γ m c p1 p2 → ptr_alive ('{m}) p2.
Proof.
  destruct p1 as [|[]], p2 as [|[]], c; csimpl; unfold addr_eq_ok; naive_solver.
Qed.
Lemma ptr_plus_ok_alive Γ m p j : ptr_plus_ok Γ m j p → ptr_alive ('{m}) p.
Proof. destruct p. done. intros [??]; simpl; eauto. Qed.
Lemma ptr_minus_ok_alive_l m p1 p2 : ptr_minus_ok m p1 p2 → ptr_alive ('{m}) p1.
Proof. destruct p1, p2; simpl; try done. intros [??]; eauto. Qed.
Lemma ptr_minus_ok_alive_r m p1 p2 : ptr_minus_ok m p1 p2 → ptr_alive ('{m}) p2.
Proof. destruct p1, p2; simpl; try done. intros (?&<-&?); eauto. Qed.
Lemma ptr_cast_ok_alive Γ m p σp : ptr_cast_ok Γ m σp p → ptr_alive ('{m}) p.
Proof. destruct p; simpl. done. intros [??]; eauto. Qed.

(** ** Properties of operations on base values *)
Definition base_val_true_false_dec m vb :
  { base_val_true m vb ∧ ¬base_val_false vb }
  + { ¬base_val_true m vb ∧ base_val_false vb }
  + { ¬base_val_true m vb ∧ ¬base_val_false vb }.
Proof.
 refine
  match vb with
  | VInt _ x => inleft (cast_if_not (decide (x = 0)))
  | VPtr (Ptr a) =>
    if decide (index_alive' m (addr_index a))
    then inleft (left _) else inright _
  | VPtr (NULL _) => inleft (right _)
  | _ => inright _
  end; abstract naive_solver.
Defined.
Lemma base_val_true_weaken Γ m1 m2 vb :
  base_val_true m1 vb → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  base_val_true m2 vb.
Proof. destruct vb as [| | |[]|]; simpl; auto. Qed.
Lemma base_val_true_erase m vb :
  base_val_true (cmap_erase m) vb = base_val_true m vb.
Proof. by destruct vb as [| | |[]|]; simpl; rewrite ?index_alive_erase'. Qed.

Global Instance base_val_unop_ok_dec m op vb :
  Decision (base_val_unop_ok m op vb).
Proof. destruct vb, op; try apply _. Defined.
Global Instance base_val_binop_ok_dec Γ m op vb1 vb2 :
  Decision (base_val_binop_ok Γ m op vb1 vb2).
Proof.
  destruct vb1, vb2, op as [|op| |]; try apply _; destruct op; apply _.
Defined.
Global Instance base_val_cast_ok_dec Γ m σb vb :
  Decision (base_val_cast_ok Γ m σb vb).
Proof. destruct vb, σb; apply _. Defined.

Lemma base_unop_typed_type_valid Γ op τb σb :
  base_unop_typed op τb σb → ✓{Γ} τb → ✓{Γ} σb.
Proof. destruct 1; constructor. Qed.
Lemma base_binop_typed_type_valid Γ op τb1 τb2 σb :
  base_binop_typed op τb1 τb2 σb → ✓{Γ} τb1 → ✓{Γ} τb2 → ✓{Γ} σb.
Proof. destruct 1; eauto using TInt_valid. Qed.
Lemma base_cast_typed_type_valid Γ τb σb :
  base_cast_typed Γ τb σb → ✓{Γ} τb → ✓{Γ} σb.
Proof.
  destruct 1; eauto using TInt_valid, TVoid_valid, TPtr_valid,
    None_ptr_valid, Some_TBase_ptr_valid.
Qed.
Lemma base_unop_type_of_sound op τb σb :
  base_unop_type_of op τb = Some σb → base_unop_typed op τb σb.
Proof. destruct τb, op; intros; simplify_option_equality; constructor. Qed.
Lemma base_unop_type_of_complete op τb σb :
  base_unop_typed op τb σb → base_unop_type_of op τb = Some σb.
Proof. by destruct 1; simplify_option_equality. Qed.
Lemma base_binop_type_of_sound op τb1 τb2 σb :
  base_binop_type_of op τb1 τb2 = Some σb → base_binop_typed op τb1 τb2 σb.
Proof.
  destruct τb1, τb2, op; intros;
    repeat (case_match || simplify_option_equality); constructor.
Qed.
Lemma base_binop_type_of_complete op τb1 τb2 σb :
  base_binop_typed op τb1 τb2 σb → base_binop_type_of op τb1 τb2 = Some σb.
Proof. by destruct 1; simplify_option_equality; repeat case_match. Qed.
Global Instance base_cast_typed_dec Γ τb σb: Decision (base_cast_typed Γ τb σb).
Proof.
 refine
  match τb, σb with
  | _, voidT => left _
  | intT τi1, intT τi2 => left _
  | τp1.*, None.* => left _
  | None.*, Some τ2.* => cast_if (decide (✓{Γ} (Some τ2)))
  | Some τ1.*, (Some τ2) as τp2.* =>
     cast_if (decide (τ1 = τ2 ∨ τ2 = ucharT ∨ τ1 = ucharT ∧ ✓{Γ} (Some τ2)))
  | _, _ => right _
  end%BT; try abstract first [by intuition; subst; constructor
    |by inversion 1; naive_solver eauto using Some_TBase_ptr_valid, TInt_valid].
Defined.
Lemma base_cast_typed_weaken Γ1 Γ2 τb σb :
  base_cast_typed Γ1 τb σb → Γ1 ⊆ Γ2 → base_cast_typed Γ2 τb σb.
Proof. destruct 1; constructor; eauto using ptr_type_valid_weaken. Qed.

Lemma base_val_0_typed Γ Γm τb : ✓{Γ} τb → (Γ,Γm) ⊢ base_val_0 τb : τb.
Proof.
  destruct 1; simpl; constructor. by apply int_typed_small. by constructor.
Qed.
Lemma base_val_unop_ok_weaken m1 m2 op vb :
  base_val_unop_ok m1 op vb →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  base_val_unop_ok m2 op vb.
Proof. destruct vb, op; simpl; eauto using ptr_alive_weaken'. Qed.
Lemma base_val_unop_ok_erase m op vb :
  base_val_unop_ok (cmap_erase m) op vb = base_val_unop_ok m op vb.
Proof. destruct op, vb; simpl; auto using ptr_alive_erase'. Qed.
Lemma base_val_unop_typed Γ Γm m op vb τb σb :
  (Γ,Γm) ⊢ vb : τb → base_unop_typed op τb σb →
  base_val_unop_ok m op vb → (Γ,Γm) ⊢ base_val_unop op vb : σb.
Proof.
  unfold base_val_unop_ok, base_val_unop. intros Hvτb Hσ Hop.
  destruct Hσ; inversion Hvτb; simplify_equality'; try done.
  * typed_constructor. by apply int_unop_typed.
  * typed_constructor. by apply int_typed_small; case_match.
Qed.
Lemma base_val_binop_ok_weaken Γ1 Γ2 Γm1 m1 m2 op vb1 vb2 τb1 τb2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ vb1 : τb1 → (Γ1,Γm1) ⊢ vb2 : τb2 →
  base_val_binop_ok Γ1 m1 op vb1 vb2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  base_val_binop_ok Γ2 m2 op vb1 vb2.
Proof.
  destruct 2, 1, op as [|[]| |]; simpl; auto; eauto 2 using
    ptr_plus_ok_weaken, ptr_minus_ok_weaken, ptr_compare_ok_weaken.
Qed.
Lemma base_val_binop_ok_erase Γ m op vb1 vb2 :
  base_val_binop_ok Γ (cmap_erase m) op vb1 vb2
  = base_val_binop_ok Γ m op vb1 vb2.
Proof.
 destruct op as [|[]| |], vb1, vb2; simpl;
   auto using ptr_plus_ok_erase, ptr_compare_ok_erase, ptr_minus_ok_erase.
Qed.
Lemma base_val_binop_weaken Γ1 Γ2 Γm1 op vb1 vb2 τb1 τb2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ vb1 : τb1 → (Γ1,Γm1) ⊢ vb2 : τb2 → Γ1 ⊆ Γ2 →
  base_val_binop Γ1 op vb1 vb2 = base_val_binop Γ2 op vb1 vb2.
Proof.
  destruct 2, 1, op as [|[]| |]; intros; f_equal';
    eauto 2 using ptr_plus_weaken, ptr_minus_weaken.
  by erewrite ptr_compare_weaken by eauto.
Qed.
Lemma base_val_binop_typed Γ Γm m op vb1 vb2 τb1 τb2 σb :
  ✓ Γ → (Γ,Γm) ⊢ vb1 : τb1 → (Γ,Γm) ⊢ vb2 : τb2 →
  base_binop_typed op τb1 τb2 σb → base_val_binop_ok Γ m op vb1 vb2 →
  (Γ,Γm) ⊢ base_val_binop Γ op vb1 vb2 : σb.
Proof.
  intros HΓ Hv1τb Hv2τb Hσ Hop. revert Hv1τb Hv2τb.
  unfold base_val_binop_ok, base_val_binop in *;
    destruct Hσ; inversion 1; inversion 1; simplify_equality'; try done.
  * typed_constructor. by apply int_binop_typed.
  * typed_constructor. by case_match; apply int_typed_small.
  * typed_constructor. eapply ptr_plus_typed; eauto.
  * typed_constructor. eapply ptr_plus_typed; eauto.
  * typed_constructor. eapply ptr_plus_typed; eauto.
  * typed_constructor. eapply ptr_plus_typed; eauto.
  * typed_constructor. eapply ptr_minus_typed; eauto.
Qed.
Lemma base_cast_typed_self Γ τb : base_cast_typed Γ τb τb.
Proof. destruct τb as [| |[]]; constructor. Qed.
Lemma base_val_cast_ok_weaken Γ1 Γ2 Γm1 m1 m2 vb τb σb :
  ✓ Γ1 → (Γ1,Γm1) ⊢ vb : τb → base_val_cast_ok Γ1 m1 σb vb →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  base_val_cast_ok Γ2 m2 σb vb.
Proof.
  destruct 2, σb; simpl; eauto using ptr_cast_ok_weaken, ptr_alive_weaken'.
Qed.
Lemma base_val_cast_ok_erase Γ m vb τb :
  base_val_cast_ok Γ (cmap_erase m) τb vb = base_val_cast_ok Γ m τb vb.
Proof.
  destruct vb, τb; simpl; auto using ptr_cast_ok_erase, ptr_alive_erase'.
Qed.
Lemma base_val_cast_typed Γ Γm m vb τb σb :
  ✓ Γ → (Γ,Γm) ⊢ vb : τb → base_cast_typed Γ τb σb →
  base_val_cast_ok Γ m σb vb → (Γ,Γm) ⊢ base_val_cast σb vb : σb.
Proof.
  unfold base_val_cast_ok, base_val_cast. intros ? Hvτb Hσb Hok. revert Hvτb.
  destruct Hσb; inversion 1; simplify_equality'; try (done || by constructor).
  * intuition; simplify_equality. by typed_constructor.
  * typed_constructor. by apply int_cast_typed.
  * typed_constructor.
    eauto using ptr_cast_typed, TPtr_valid_inv, base_val_typed_type_valid.
  * typed_constructor.
    eauto using ptr_cast_typed, TBase_ptr_valid, TVoid_valid, None_ptr_valid.
  * typed_constructor. eauto using ptr_cast_typed, TBase_ptr_valid, TInt_valid.
  * typed_constructor. eauto using ptr_cast_typed.
  * typed_constructor. eauto using ptr_cast_typed.
Qed.
Lemma base_val_cast_ok_void Γ m vb :
  (Γ,'{m}) ⊢ vb : ucharT%BT → base_val_cast_ok Γ m voidT%BT vb.
Proof. by inversion 1. Qed.
Lemma base_val_cast_void vb : base_val_cast voidT vb = VVoid.
Proof. by destruct vb. Qed.

(** ** Properties of operations on values *)
Lemma val_0_base Γ τb : val_0 Γ τb = VBase (base_val_0 τb).
Proof. unfold val_0. by rewrite type_iter_base. Qed.
Lemma val_0_array Γ τ n :
  val_0 Γ (τ.[n]) = VArray τ (replicate n (val_0 Γ τ)).
Proof. unfold val_0. by rewrite type_iter_array. Qed.
Lemma val_0_compound Γ c s τs :
  ✓ Γ → Γ !! s = Some τs → val_0 Γ (compoundT{c} s) =
    match c with
    | Struct_kind => VStruct s (val_0 Γ <$> τs)
    | Union_kind => VUnion s 0 (default (VUnionAll s []) (τs !! 0) (val_0 Γ))
    end.
Proof.
  intros HΓ Hs. unfold val_0; erewrite (type_iter_compound (=)); try done.
  { by intros ????? ->. }
  clear s τs Hs. intros ?? [] ? τs ?? Hgo; f_equal'; [|by destruct Hgo].
  by apply Forall_fmap_ext.
Qed.
Lemma val_0_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → val_0 Γ1 τ = val_0 Γ2 τ.
Proof.
  intros. apply (type_iter_weaken (=)); try done; [by intros ????? ->|].
  intros ?? [] ? τs ?? Hgo; f_equal'; [|by destruct Hgo].
  by apply Forall_fmap_ext.
Qed.
Lemma val_0_typed Γ Γm τ : ✓ Γ → ✓{Γ} τ → (Γ,Γm) ⊢ val_0 Γ τ : τ.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb. rewrite val_0_base.
    typed_constructor; auto using base_val_0_typed.
  * intros τ n ???. rewrite val_0_array.
    typed_constructor; auto using replicate_length, Forall_replicate.
  * intros [] s τs Hs _ IH ?; erewrite val_0_compound by eauto.
    { typed_constructor; eauto. elim IH; csimpl; auto. }
    by destruct IH; simplify_equality'; typed_constructor; eauto.
Qed.

Definition val_true_false_dec m v :
  { val_true m v ∧ ¬val_false v } + { ¬val_true m v ∧ val_false v }
  + { ¬val_true m v ∧ ¬val_false v }.
Proof.
 refine
  match v with
  | VBase vb =>
     match base_val_true_false_dec m vb with
     | inleft (left _) => inleft (left _)
     | inleft (right _) => inleft (right _) | inright _ => inright _
     end
  | _ => inright _
  end; abstract naive_solver.
Defined.
Lemma val_true_false m v : val_true m v → val_false v → False.
Proof. by destruct (val_true_false_dec m v) as [[[??]|[??]]|[??]]. Qed.
Lemma val_true_weaken Γ m1 m2 v :
  val_true m1 v → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  val_true m2 v.
Proof. destruct v; simpl; eauto using base_val_true_weaken. Qed.
Lemma val_true_erase m v : val_true (cmap_erase m) v = val_true m v.
Proof. by destruct v; simpl; auto using base_val_true_erase. Qed.

Global Instance val_unop_ok_dec m op v : Decision (val_unop_ok m op v).
Proof. destruct v; try apply _. Defined.
Global Instance val_binop_ok_dec Γ m op v1 v2 :
  Decision (val_binop_ok Γ m op v1 v2).
Proof. destruct v1, v2; apply _. Defined.
Global Instance val_cast_ok_dec Γ m σp v : Decision (val_cast_ok Γ m σp v).
Proof. destruct v, σp as [[[]| |]|]; apply _. Defined.

Lemma unop_typed_type_valid Γ op τ σ : unop_typed op τ σ → ✓{Γ} τ → ✓{Γ} σ.
Proof.
  destruct 1; eauto using TBase_valid,
    TBase_valid_inv, base_unop_typed_type_valid.
Qed.
Lemma binop_typed_type_valid Γ op τ1 τ2 σ :
  binop_typed op τ1 τ2 σ → ✓{Γ} τ1 → ✓{Γ} τ2 → ✓{Γ} σ.
Proof.
  destruct 1; eauto using TBase_valid,
    TBase_valid_inv, base_binop_typed_type_valid.
Qed.
Lemma cast_typed_type_valid Γ τ σ : cast_typed Γ τ σ → ✓{Γ} τ → ✓{Γ} σ.
Proof.
  destruct 1; eauto using TBase_valid, TVoid_valid, TBase_valid,
    TBase_valid_inv, base_cast_typed_type_valid.
Qed.
Lemma unop_type_of_sound op τ σ :
  unop_type_of op τ = Some σ → unop_typed op τ σ.
Proof.
  destruct τ; intros; simplify_option_equality; constructor.
  auto using base_unop_type_of_sound.
Qed.
Lemma unop_type_of_complete op τ σ :
  unop_typed op τ σ → unop_type_of op τ = Some σ.
Proof.
  destruct 1; simplify_option_equality.
  by erewrite base_unop_type_of_complete by eauto.
Qed.
Lemma binop_type_of_sound op τ1 τ2 σ :
  binop_type_of op τ1 τ2 = Some σ → binop_typed op τ1 τ2 σ.
Proof.
  destruct τ1, τ2; intros; simplify_option_equality; constructor.
  by apply base_binop_type_of_sound.
Qed.
Lemma binop_type_of_complete op τ1 τ2 σ :
  binop_typed op τ1 τ2 σ → binop_type_of op τ1 τ2 = Some σ.
Proof.
  destruct 1; simplify_option_equality.
  by erewrite base_binop_type_of_complete by eauto.
Qed.
Global Instance cast_typed_dec Γ τ σ : Decision (cast_typed Γ τ σ).
Proof.
 refine 
  match decide (τ = σ) with
  | left _ => left _
  | right Hτσ =>
    match τ, σ return τ ≠ σ → Decision (cast_typed Γ τ σ) with
    | baseT τb, baseT σb => λ _, cast_if (decide (base_cast_typed Γ τb σb))
    | _, baseT σb => λ _, cast_if (decide (σb = voidT%BT))
    | _, _ => λ _, right _
    end Hτσ
  end; abstract first
   [ by subst; constructor
   | by inversion 1; subst;
      repeat match goal with
      | H : ¬base_cast_typed _ _ _ |- _ => destruct H; constructor
      end].
Defined.
Lemma cast_typed_weaken Γ1 Γ2 τ σ :
  cast_typed Γ1 τ σ → Γ1 ⊆ Γ2 → cast_typed Γ2 τ σ.
Proof. destruct 1; constructor; eauto using base_cast_typed_weaken. Qed.
Lemma val_unop_ok_weaken m1 m2 op v :
  val_unop_ok m1 op v → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  val_unop_ok m2 op v.
Proof. unfold val_unop_ok; destruct v; eauto using base_val_unop_ok_weaken. Qed.
Lemma val_unop_ok_erase m op v :
  val_unop_ok (cmap_erase m) op v = val_unop_ok m op v.
Proof.
  unfold val_unop_ok; destruct v; simpl; auto using base_val_unop_ok_erase.
Qed.
Lemma val_unop_typed Γ Γm m op v τ σ :
  (Γ,Γm) ⊢ v : τ → unop_typed op τ σ → val_unop_ok m op v →
  (Γ,Γm) ⊢ val_unop op v : σ.
Proof.
  intros Hvτ Hσ Hop. destruct Hσ; inversion Hvτ; simpl; simplify_equality;
    done || constructor; eauto using base_val_unop_typed.
Qed.
Lemma val_binop_ok_weaken Γ1 Γ2 Γm1 m1 m2 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ v1 : τ1 → (Γ1,Γm1) ⊢ v2 : τ2 →
  val_binop_ok Γ1 m1 op v1 v2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  val_binop_ok Γ2 m2 op v1 v2.
Proof.
  destruct 2, 1, op; simpl; try done; eauto 2 using base_val_binop_ok_weaken.
Qed.
Lemma val_binop_ok_erase Γ m op v1 v2 :
  val_binop_ok Γ (cmap_erase m) op v1 v2 = val_binop_ok Γ m op v1 v2.
Proof.
  unfold val_binop_ok; destruct v1,v2; simpl;auto using base_val_binop_ok_erase.
Qed.
Lemma val_binop_weaken Γ1 Γ2 Γm1 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ v1 : τ1 → (Γ1,Γm1) ⊢ v2 : τ2 → Γ1 ⊆ Γ2 →
  val_binop Γ1 op v1 v2 = val_binop Γ2 op v1 v2.
Proof.
  destruct 2, 1, op; intros; f_equal'; eauto 2 using base_val_binop_weaken.
Qed.
Lemma val_binop_typed Γ Γm m op v1 v2 τ1 τ2 σ :
  ✓ Γ → (Γ,Γm) ⊢ v1 : τ1 → (Γ,Γm) ⊢ v2 : τ2 →
  binop_typed op τ1 τ2 σ → val_binop_ok Γ m op v1 v2 →
  (Γ,Γm) ⊢ val_binop Γ op v1 v2 : σ.
Proof.
  intros ? Hv1τ Hv2τ Hσ Hop.
  destruct Hσ; inversion Hv1τ; inversion Hv2τ; simplify_equality';
    done || constructor; eauto using base_val_binop_typed.
Qed.
Lemma val_cast_ok_weaken Γ1 Γ2 Γm1 m1 m2 v τ σ :
  ✓ Γ1 → (Γ1,Γm1) ⊢ v : τ → val_cast_ok Γ1 m1 (Some σ) v →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  val_cast_ok Γ2 m2 (Some σ) v.
Proof. destruct 2, σ; simpl; eauto using base_val_cast_ok_weaken. Qed.
Lemma val_cast_ok_erase Γ m v τp :
  val_cast_ok Γ (cmap_erase m) τp v = val_cast_ok Γ m τp v.
Proof. destruct v, τp as [[]|]; simpl; auto using base_val_cast_ok_erase. Qed.
Lemma val_cast_typed Γ Γm m v τ σ :
  ✓ Γ → (Γ,Γm) ⊢ v : τ → cast_typed Γ τ σ → val_cast_ok Γ m (Some σ) v →
  (Γ,Γm) ⊢ val_cast (Some σ) v : σ.
Proof.
  intros ? Hvτ Hσ Hok. destruct Hσ; inversion Hvτ; simplify_equality';
    repeat typed_constructor;
    eauto using base_val_cast_typed, TVoid_cast_typed, base_cast_typed_self.
Qed.
End operations.
