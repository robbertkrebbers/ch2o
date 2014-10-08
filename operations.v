(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_map values.
Require Import pointer_casts.
Local Open Scope ctype_scope.

Section operations.
  Context `{Env Ti}.

  (** ** Operations on addresses *)
  Definition addr_plus_ok (Γ : env Ti) (m : mem Ti)
      (j : Z) (a : addr Ti) : Prop :=
    index_alive' m (addr_index a) ∧
    (0 ≤ addr_byte a + j * size_of' Γ a
       ≤ size_of Γ (addr_type_base a) * ref_size (addr_ref_base a))%Z.
  Global Arguments addr_plus_ok _ _ _ !_ /.
  Definition addr_plus (Γ : env Ti) (j : Z) (a : addr Ti): addr Ti :=
    let 'Addr x r i τ σ σc := a
    in Addr x r (Z.to_nat (i + j * size_of Γ σc)) τ σ σc.
  Global Arguments addr_plus _ _ !_ /.

  Definition addr_minus_ok (m : mem Ti) (a1 a2 : addr Ti) : Prop :=
    index_alive' m (addr_index a1) ∧
    addr_index a1 = addr_index a2 ∧
    freeze true <$> addr_ref_base a1 = freeze true <$> addr_ref_base a2.
  Global Arguments addr_minus_ok _ !_ !_ /.
  Definition addr_minus (Γ : env Ti) (a1 a2 : addr Ti) : Z :=
    ((addr_byte a1 - addr_byte a2) `div` size_of' Γ a1)%Z.
  Global Arguments addr_minus _ !_ !_ /.

  Definition addr_cast_ok (Γ : env Ti) (m : mem Ti)
      (σc : type Ti) (a : addr Ti) : Prop :=
    index_alive' m (addr_index a) ∧
    addr_type_base a >*> σc ∧
    addr_byte a `mod` size_of Γ σc = 0.
  Global Arguments addr_cast_ok _ _ _ !_ /.
  Definition addr_cast (σc : type Ti) (a : addr Ti) : addr Ti :=
    let 'Addr o r i τ σ _ := a in Addr o r i τ σ σc.
  Global Arguments addr_cast _ !_ /.

  Definition addr_elt (Γ : env Ti) (rs : ref_seg Ti) (a : addr Ti) : addr Ti :=
    from_option a $
     σ ← type_of a !!{Γ} rs;
     Some (Addr (addr_index a) (rs :: addr_ref Γ a) 0 (addr_type_object a) σ σ).
  Global Arguments addr_elt _ _ !_ /.

  (** ** Operations on pointers *)
  Definition ptr_alive' (m : mem Ti) (p : ptr Ti) : Prop :=
    match p with Ptr a => index_alive' m (addr_index a) | NULL _ => True end.
  Definition ptr_compare_ok (m : mem Ti) (c : compop) (p1 p2 : ptr Ti) : Prop :=
    match p1, p2 with
    | Ptr a1, Ptr a2 => addr_minus_ok m a1 a2
    | NULL _, Ptr a2 =>
       match c with EqOp => index_alive' m (addr_index a2) | _ => False end
    | Ptr a1, NULL _ =>
       match c with EqOp => index_alive' m (addr_index a1) | _ => False end
    | NULL _, NULL _ => True
    end.
  Definition ptr_compare (Γ : env Ti) (c : compop) (p1 p2 : ptr Ti) : bool :=
    match p1, p2 with
    | Ptr a1, Ptr a2 => Z_comp c (addr_minus Γ a1 a2) 0
    | NULL _, Ptr a2 => false (* only allowed for EqOp *)
    | Ptr a1, NULL _ => false (* only allowed for EqOp *)
    | NULL _, NULL _ => match c with EqOp | LeOp => true | LtOp => false end
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
      (σc : type Ti) (p : ptr Ti) : Prop :=
    match p with NULL _ => True | Ptr a => addr_cast_ok Γ m σc a end.
  Global Arguments ptr_cast_ok _ _ _ !_ /.
  Definition ptr_cast (σc : type Ti) (p : ptr Ti) : ptr Ti :=
    match p with NULL _ => NULL σc | Ptr a => Ptr (addr_cast σc a) end.
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
    | TInt_NegOp_typed τi :
       base_unop_typed NegOp (intT τi) (intT (int_promote τi))
    | TInt_ComplOp_typed τi :
       base_unop_typed ComplOp (intT τi) (intT (int_promote τi))
    | TInt_NotOp_typed τi :
       base_unop_typed NotOp (intT τi) sintT
    | TPtr_NotOp_typed τ : base_unop_typed NotOp (τ.*) sintT.
  Definition base_unop_type_of (op : unop)
      (τb : base_type Ti) : option (base_type Ti) :=
    match τb, op with
    | intT τi, NotOp => Some sintT
    | intT τi, _ => Some (intT (int_promote τi))
    | τ.*, NotOp => Some sintT
    | _, _ => None
    end%BT.
  Definition base_val_unop_ok (m : mem Ti)
      (op : unop) (vb : base_val Ti) : Prop :=
    match vb, op with
    | VInt τi x, NegOp => int_arithop_ok MinusOp 0 τi x τi
    | VInt τi x, _ => True
    | VPtr p, NotOp => ptr_alive' m p
    | _, _ => False
    end.
  Global Arguments base_val_unop_ok _ !_ !_ /.
  Definition base_val_unop (op : unop) (vb : base_val Ti) : base_val Ti :=
    match vb, op with
    | VInt τi x, NegOp => VInt (int_promote τi) (int_arithop MinusOp 0 τi x τi)
    | VInt τi x, ComplOp =>
       let τi' := int_promote τi in
       VInt τi' (int_of_bits τi' (negb <$> int_to_bits τi' x))
    | VInt τi x, NotOp => VInt sintT (if decide (x = 0) then 1 else 0)
    | VPtr p, _ => VInt sintT (match p with NULL _ => 1 | Ptr _ => 0 end)
    | _, _ => vb
    end.
  Global Arguments base_val_unop !_ !_ /.

  Inductive base_binop_typed :
        binop → base_type Ti → base_type Ti → base_type Ti → Prop :=
    | CompOp_TInt_TInt_typed op τi1 τi2 :
       base_binop_typed (CompOp op) (intT τi1) (intT τi2) sintT
    | ArithOp_TInt_TInt_typed op τi1 τi2 :
       base_binop_typed (ArithOp op) (intT τi1) (intT τi2)
         (intT (int_promote τi1 ∪ int_promote τi2))
    | ShiftOp_TInt_TInt_typed op τi1 τi2 :
       base_binop_typed (ShiftOp op) (intT τi1) (intT τi2)
         (intT (int_promote τi1))
    | BitOp_TInt_TInt_typed op τi1 τi2 :
       base_binop_typed (BitOp op) (intT τi1) (intT τi2)
         (intT (int_promote τi1 ∪ int_promote τi2))
    | CompOp_TPtr_TPtr_typed c τ :
       base_binop_typed (CompOp c) (τ.*) (τ.*) sintT
    | PlusOp_TPtr_TInt_typed τ σ :
       base_binop_typed (ArithOp PlusOp) (τ.*) (intT σ) (τ.*)
    | PlusOp_VInt_TPtr_typed τ σ :
       base_binop_typed (ArithOp PlusOp) (intT σ) (τ.*) (τ.*)
    | MinusOp_TPtr_TInt_typed τ σi :
       base_binop_typed (ArithOp MinusOp) (τ.*) (intT σi) (τ.*)
    | MinusOp_TInt_TPtr_typed τ σi :
       base_binop_typed (ArithOp MinusOp) (intT σi) (τ.*) (τ.*)
    | MinusOp_TPtr_TPtr_typed τ  :
       base_binop_typed (ArithOp MinusOp) (τ.*) (τ.*) sptrT.
  Definition base_binop_type_of
      (op : binop) (τb1 τb2 : base_type Ti) : option (base_type Ti) :=
    match τb1, τb2, op with
    | intT τi1, intT τi2, CompOp _ => Some sintT
    | intT τi1, intT τi2, (ArithOp _ | BitOp _) =>
       Some (intT (int_promote τi1 ∪ int_promote τi2))
    | intT τi1, intT τi2, ShiftOp _ => Some (intT (int_promote τi1))
    | τ1.*, τ2.*, CompOp _ => guard (τ1 = τ2); Some sintT
    | τ.*, intT σ, (ArithOp PlusOp | ArithOp MinusOp) => Some (τ.*)
    | intT σ, τ.*, (ArithOp PlusOp | ArithOp MinusOp) => Some (τ.*)
    | τ1.*, τ2.*, ArithOp MinusOp => guard (τ1 = τ2); Some sptrT
    | _, _, _ => None
    end%BT.
  Definition base_val_binop_ok (Γ : env Ti) (m : mem Ti)
      (op : binop) (vb1 vb2 : base_val Ti) : Prop :=
    match vb1, vb2, op with
    | VInt τi1 x1, VInt τi2 x2, (CompOp _ | BitOp _) => True
    | VInt τi1 x1, VInt τi2 x2, ArithOp op => int_arithop_ok op x1 τi1 x2 τi2
    | VInt τi1 x1, VInt τi2 x2, ShiftOp op => int_shiftop_ok op x1 τi1 x2 τi2
    | VPtr p1, VPtr p2, CompOp c => ptr_compare_ok m c p1 p2
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
    | VInt τi1 x1, VInt τi2 x2, CompOp op =>
       let τi' := int_promote τi1 ∪ int_promote τi2 in
       let x1' := int_cast τi' x1 in let x2' := int_cast τi' x2 in
       VInt sintT (if Z_comp op x1' x2' then 1 else 0)
    | VInt τi1 x1, VInt τi2 x2, ArithOp op =>
       VInt (int_promote τi1 ∪ int_promote τi2) (int_arithop op x1 τi1 x2 τi2)
    | VInt τi1 x1, VInt τi2 x2, ShiftOp op =>
       VInt (int_promote τi1) (int_shiftop op x1 τi1 x2 τi2)
    | VInt τi1 x1, VInt τi2 x2, BitOp op =>
       let τi' := int_promote τi1 ∪ int_promote τi2 in
       VInt τi' (int_of_bits τi'
         (zip_with (bool_bitop op) (int_to_bits τi' x1) (int_to_bits τi' x2)))
    | VPtr p1, VPtr p2, CompOp c =>
       VInt sintT (if ptr_compare Γ c p1 p2 then 1 else 0)
    | VPtr p, VInt _ i, ArithOp PlusOp => VPtr (ptr_plus Γ i p)
    | VInt _ i, VPtr p, ArithOp PlusOp => VPtr (ptr_plus Γ i p)
    | VPtr p, VInt _ i, ArithOp MinusOp => VPtr (ptr_plus Γ (-i) p)
    | VInt _ i, VPtr p, ArithOp MinusOp => VPtr (ptr_plus Γ (-i) p)
    | VPtr p1, VPtr p2, ArithOp MinusOp => VInt sptrT (ptr_minus Γ p1 p2)
    | _, _, _ => VIndet (type_of v1)
    end.
  Global Arguments base_val_binop _ !_ !_ !_ /.

  Inductive base_cast_typed (Γ : env Ti) :
       base_type Ti → base_type Ti → Prop :=
    | TVoid_cast_typed τb : base_cast_typed Γ τb voidT
    | TInt_cast_typed τi1 τi2 : base_cast_typed Γ (intT τi1) (intT τi2)
    | TPtr_to_TPtr_cast_typed τ : base_cast_typed Γ (τ.*) (τ.*)
    | TPtr_to_void_cast_typed τ : base_cast_typed Γ (τ.*) (voidT.*)
    | TPtr_to_uchar_cast_typed τ : base_cast_typed Γ (τ.*) (ucharT.*)
    | TPtr_of_void_cast_typed τ :
       ptr_type_valid Γ τ → base_cast_typed Γ (voidT.*) (τ.*)
    | TPtr_of_uchar_cast_typed τ :
       ptr_type_valid Γ τ → base_cast_typed Γ (ucharT.*) (τ.*).
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
      (τ : type Ti) (v : val Ti) : Prop :=
    match v, τ with
    | VBase vb, baseT τb => base_val_cast_ok Γ m τb vb | _, _ => True
    end.
  Global Arguments val_cast_ok _ _ !_ !_ /.
  Definition val_cast (τ : type Ti) (v : val Ti) : val Ti :=
    match v, τ with
    | VBase vb, baseT τb => VBase (base_val_cast τb vb)
    | _, voidT => VBase VVoid | _ , _ => v
    end.
  Global Arguments val_cast !_ !_ /.
End operations.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γm : memenv Ti.
Implicit Types τb σb : base_type Ti.
Implicit Types τ σ : type Ti.
Implicit Types a : addr Ti.
Implicit Types vb : base_val Ti.
Implicit Types v : val Ti.
Implicit Types m : mem Ti.
Hint Immediate index_alive_1'.
Hint Resolve index_alive_2'.

(** ** Properties of operations on addresses *)
Lemma addr_plus_typed Γ m a σ j :
  ✓ Γ → (Γ,'{m}) ⊢ a : σ → addr_plus_ok Γ m j a →
  (Γ,'{m}) ⊢ addr_plus Γ j a : σ.
Proof.
  intros ? [o r i τ σ' σc ??????] (?&?&?);
    constructor; simpl in *; split_ands; auto.
  { apply Nat2Z.inj_le. by rewrite Nat2Z.inj_mul, Z2Nat.id by done. }
  apply Nat2Z.inj. rewrite Z2Nat_inj_mod, Z2Nat.id by done.
  rewrite Z.mod_add, <-Z2Nat_inj_mod; auto with f_equal.
  rewrite (Nat2Z.inj_iff _ 0); eauto using size_of_ne_0,
    ref_typed_type_valid, castable_type_valid.
Qed.
Lemma addr_plus_ok_weaken Γ1 Γ2 m1 m2 a σ j :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ a : σ → addr_plus_ok Γ1 m1 j a →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  addr_plus_ok Γ2 m2 j a.
Proof.
  unfold addr_plus_ok. intros ?? (?&?&?) ??. erewrite <-addr_size_of_weaken,
    <-(size_of_weaken _ Γ2) by eauto using addr_typed_type_base_valid; eauto.
Qed.
Lemma addr_plus_weaken Γ1 Γ2 Γm1 a σ j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a : σ → Γ1 ⊆ Γ2 → addr_plus Γ1 j a = addr_plus Γ2 j a.
Proof.
  intros ? [o r i τ σ' σc'] ?; simpl. by erewrite size_of_weaken
    by eauto using ref_typed_type_valid, castable_type_valid.
Qed.
Lemma addr_type_plus Γ a j : type_of (addr_plus Γ j a) = type_of a.
Proof. by destruct a. Qed.
Lemma addr_type_base_plus Γ a j :
  addr_type_base (addr_plus Γ j a) = addr_type_base a.
Proof. by destruct a. Qed.
Lemma addr_index_plus Γ a j : addr_index (addr_plus Γ j a) = addr_index a.
Proof. by destruct a. Qed.
Lemma addr_plus_0 Γ a : addr_plus Γ 0 a = a.
Proof. destruct a; simpl. by rewrite Z.mul_0_l, Z.add_0_r, Nat2Z.id. Qed.
Lemma addr_plus_plus Γ a j1 j2 :
  (0 ≤ addr_byte a + j2 * size_of' Γ a)%Z →
  addr_plus Γ j1 (addr_plus Γ j2 a) = addr_plus Γ (j1 + j2) a.
Proof.
  intros. destruct a as [o r i σ σc]; do 2 f_equal'.
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
Lemma addr_byte_representable Γ Γm a σ :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → int_typed (addr_byte a) sptrT.
Proof.
  destruct 2 as [o r i τ σ σc ?? [_ ?]]; simpl; split.
  { transitivity 0; auto using int_lower_nonpos with zpos. }
  assert (size_of Γ σ * ref_size r ≤ size_of Γ τ) by eauto using size_of_ref.
  lia.
Qed.
Lemma addr_minus_typed Γ Γm a1 a2 σ :
  ✓ Γ → (Γ,Γm) ⊢ a1 : σ → (Γ,Γm) ⊢ a2 : σ →
  int_typed (addr_minus Γ a1 a2) sptrT.
Proof.
  intros HΓ Ha1 Ha2; unfold addr_minus; simplify_type_equality'.
  assert (0 < size_of Γ σ)%Z.
  { apply (Nat2Z.inj_lt 0); eauto using size_of_pos, addr_typed_type_valid. }
  assert (int_upper sptrT ≤ size_of Γ σ * int_upper sptrT)%Z.
  { transitivity (1 * int_upper sptrT)%Z; [lia|].
    apply Z.mul_le_mono_nonneg_r; auto using int_upper_pos with zpos. }
  destruct (addr_byte_representable Γ Γm a1 σ) as [_ ?]; auto.
  destruct (addr_byte_representable Γ Γm a2 σ) as [_ ?]; auto.
  split; [|apply Z.div_lt_upper_bound; lia].
  apply Z.div_le_lower_bound; auto. rewrite int_lower_upper_signed by done; lia.
Qed.
Lemma addr_minus_ok_weaken m1 m2 a1 a2:
  addr_minus_ok m1 a1 a2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  addr_minus_ok m2 a1 a2.
Proof. intros [??]; split; eauto. Qed.
Lemma addr_minus_weaken Γ1 Γ2 mm1 a1 a2 σ1 :
  ✓ Γ1 → (Γ1,mm1) ⊢ a1 : σ1 →
  Γ1 ⊆ Γ2 → addr_minus Γ1 a1 a2 = addr_minus Γ2 a1 a2.
Proof.
  intros. unfold addr_minus; simplify_type_equality.
  by erewrite (size_of_weaken Γ1 Γ2) by eauto using addr_typed_type_valid.
Qed.
Lemma addr_cast_typed Γ m a σ σc :
  (Γ,'{m}) ⊢ a : σ → addr_cast_ok Γ m σc a → (Γ,'{m}) ⊢ addr_cast σc a : σc.
Proof. intros [] (?&?&?); constructor; naive_solver. Qed.
Lemma addr_cast_ok_weaken Γ1 Γ2 m1 m2 a σ σc :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ a : σ →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  addr_cast_ok Γ1 m1 σc a → Γ1 ⊆ Γ2 → addr_cast_ok Γ2 m2 σc a.
Proof.
  intros ??? (?&?&?); repeat split; auto. by erewrite <-size_of_weaken
    by eauto using castable_type_valid, addr_typed_type_base_valid.
Qed.
Lemma addr_type_cast a σc : type_of (addr_cast σc a) = σc.
Proof. by destruct a. Qed.
Lemma addr_index_cast a σc : addr_index (addr_cast σc a) = addr_index a.
Proof. by destruct a. Qed.
Lemma addr_ref_cast Γ a σc : addr_ref Γ (addr_cast σc a) = addr_ref Γ a.
Proof. by destruct a. Qed.
Lemma addr_ref_byte_cast Γ a σc :
  addr_ref_byte Γ (addr_cast σc a) = addr_ref_byte Γ a.
Proof. by destruct a. Qed.
Lemma addr_cast_self Γ Γm a σ : (Γ,Γm) ⊢ a : σ → addr_cast σ a = a.
Proof. by destruct 1. Qed.
Lemma addr_is_obj_cast a σc :
  addr_is_obj (addr_cast σc a) ↔ σc = addr_type_base a.
Proof. by destruct a. Qed.
Lemma addr_ref_plus_char_cast Γ Γm a σ j :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_is_obj a → j < size_of Γ σ →
  addr_ref Γ (addr_plus Γ j (addr_cast ucharT a)) = addr_ref Γ a.
Proof.
  destruct 2 as [o r i τ σ σc ?????]; intros ??; simplify_equality'; f_equal.
  rewrite size_of_uchar, Z.mul_1_r,Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  symmetry. apply Nat.div_unique with (i `mod` size_of Γ σ + j); [lia|].
  by rewrite Nat.add_assoc, <-Nat.div_mod
    by eauto using ref_typed_type_valid, size_of_ne_0.
Qed.
Lemma addr_ref_byte_plus_char_cast Γ Γm a σ j :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_is_obj a → j < size_of Γ σ →
  addr_ref_byte Γ (addr_plus Γ j (addr_cast ucharT a)) = j.
Proof.
  destruct 2 as [o r i τ σ σc ?????? Hiσ]; intros; simplify_equality'.
  f_equal. rewrite size_of_uchar.
  rewrite Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  rewrite <-Nat.add_mod_idemp_l
    by eauto using ref_typed_type_valid, size_of_ne_0.
  rewrite Hiσ, Nat.add_0_l. by apply Nat.mod_small.
Qed.
Lemma addr_byte_lt_size_char_cast Γ Γm a σ j :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_is_obj a → j < size_of Γ σ →
  addr_byte a < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a) →
  addr_byte (addr_plus Γ j (addr_cast ucharT a))
    < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a).
Proof.
  destruct 2 as [o r i τ σ σc ?????? Hiσ]; intros; simplify_equality'.
  rewrite size_of_uchar, Z.mul_1_r,Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  apply Nat.lt_le_trans with (i + size_of Γ σ); [lia|].
  apply Nat.div_exact in Hiσ; eauto using ref_typed_type_valid, size_of_ne_0.
  rewrite Hiσ, <-Nat.mul_succ_r. apply Nat.mul_le_mono_l, Nat.le_succ_l.
  apply Nat.div_lt_upper_bound;
    eauto using ref_typed_type_valid, size_of_ne_0.
Qed.
Lemma addr_elt_typed Γ Γm a rs σ σ' :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → addr_strict Γ a → Γ ⊢ rs : σ ↣ σ' →
  ref_seg_offset rs = 0 → (Γ,Γm) ⊢ addr_elt Γ rs a : σ'.
Proof.
  rewrite addr_typed_alt. intros ? (?&?&?&?&?&?&?&Hcast&?) ? Hrs ?.
  destruct a as [o r i τ σ'' σc]; simplify_equality'.
  apply castable_alt in Hcast; destruct Hcast as [?|[?|?]];
    simplify_equality'; try solve [inversion Hrs].
  erewrite path_type_check_complete by eauto; simpl; constructor; auto.
  * apply ref_typed_cons; exists σ; split; auto.
    apply ref_set_offset_typed; auto.
    apply Nat.div_lt_upper_bound; eauto using size_of_ne_0,ref_typed_type_valid.
  * lia.
  * by rewrite Nat.mod_0_l by eauto using size_of_ne_0, ref_typed_type_valid,
      ref_seg_typed_type_valid, castable_type_valid.
Qed.
Lemma addr_elt_strict Γ Γm a rs σ σ' :
  ✓ Γ → (Γ,Γm) ⊢ a : σ → Γ ⊢ rs : σ ↣ σ' → addr_strict Γ (addr_elt Γ rs a).
Proof.
  rewrite addr_typed_alt. intros ? (?&?&?&?&?&?&?&Hcast&?) Hrs.
  destruct a as [o r i τ σ'' σc]; simplify_equality'.
  erewrite path_type_check_complete by eauto; simpl.
  apply Nat.mul_pos_pos.
  * eauto using size_of_pos, ref_typed_type_valid,
      ref_seg_typed_type_valid, castable_type_valid.
  * destruct Hrs; simpl; lia.
Qed.
Lemma addr_elt_weaken Γ1 Γ2 Γm1 a rs σ σ' :
  ✓ Γ1 → (Γ1,Γm1) ⊢ a : σ → Γ1 ⊢ rs : σ ↣ σ' → Γ1 ⊆ Γ2 →
  addr_elt Γ1 rs a = addr_elt Γ2 rs a.
Proof.
  intros. unfold addr_elt; simplify_type_equality.
  by erewrite addr_ref_weaken, !path_type_check_complete
    by eauto using ref_seg_typed_weaken.
Qed.

Lemma addr_plus_ok_refine Γ α f m1 m2 a1 a2 σ j :
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σ →
  addr_plus_ok Γ m1 j a1 → addr_plus_ok Γ m2 j a2.
Proof.
  unfold addr_plus_ok. intros Ha (?&?&?).
  destruct (addr_byte_refine_help Γ α f
    ('{m1}) ('{m2}) a1 a2 σ) as (i&?&?); auto.
  destruct Ha as [??????????? (?&?&?&?&?)];
    simplify_equality'; split; eauto; lia.
Qed.
Lemma addr_plus_refine Γ α f m1 m2 a1 a2 σ j :
  ✓ Γ → addr_plus_ok Γ m1 j a1 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σ →
  addr_plus Γ j a1 ⊑{Γ,α,f@'{m1}↦'{m2}} addr_plus Γ j a2 : σ.
Proof.
  intros ? Ha' Ha. destruct Ha' as (_&?&?), Ha as
    [o o' r r' r'' i i'' τ τ' σ σc ??????????? Hr'']; simplify_equality'.
  econstructor; eauto.
  { apply Nat2Z.inj_le. by rewrite Nat2Z.inj_mul, Z2Nat.id by done. }
  { apply Nat2Z.inj. rewrite Z2Nat_inj_mod, Z2Nat.id by done.
    rewrite Z.mod_add, <-Z2Nat_inj_mod; auto with f_equal.
    rewrite (Nat2Z.inj_iff _ 0).
    eauto using size_of_ne_0, ref_typed_type_valid, castable_type_valid. }
  destruct Hr'' as [i|r i]; simplify_equality'; [|by constructor].
  apply ref_refine_nil_alt; auto. rewrite ref_offset_freeze.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul. 
  transitivity (Z.to_nat ((i + j * size_of Γ σc) +
    size_of Γ σ * ref_offset r')); [f_equal; lia |].
  by rewrite Z2Nat.inj_add, Z2Nat.inj_mul, !Nat2Z.id
    by auto using Z.mul_nonneg_nonneg with lia.
Qed.
Lemma addr_minus_ok_refine Γ α f m1 m2 a1 a2 a3 a4 σ :
  a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σ → a3 ⊑{Γ,α,f@'{m1}↦'{m2}} a4 : σ →
  addr_minus_ok m1 a1 a3 → addr_minus_ok m2 a2 a4.
Proof.
  destruct 1 as [??????????? (?&?&?&?&?) ?????????? []],
    1 as [??????????? (?&?&?&?&?) ?????????? []];
    intros (?&?&Hr); simplify_equality'; eauto.
  rewrite !fmap_app, !ref_freeze_freeze by eauto; eauto with congruence.
Qed.
Lemma addr_minus_refine Γ α f m1 m2 a1 a2 a3 a4 σ :
  addr_minus_ok m1 a1 a3 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σ →
  a3 ⊑{Γ,α,f@'{m1}↦'{m2}} a4 : σ → addr_minus Γ a1 a3 = addr_minus Γ a2 a4.
Proof.
  intros (?&?&?).
  destruct 1 as [o1 o2 r1 r2 r3 i1 i3 τ1 τ2 σ1 σc ??????????? Hr3],
    1 as [o4 o5 r4 r5 r6 i4 i6 τ4 τ5 σ3 σc4 ??????????? Hr6].
  destruct Hr3, Hr6; simplify_type_equality'; f_equal; lia.
Qed.
Lemma addr_cast_ok_refine Γ α f m1 m2 a1 a2 σ σc :
  ✓ Γ → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σ →
  addr_cast_ok Γ m1 σc a1 → addr_cast_ok Γ m2 σc a2.
Proof.
  destruct 2 as [o o' r r' r'' i i'' τ τ' σ σc' (?&?&?&?&?) ?????????? []];
    intros (?&?&?); simplify_equality'; split_ands; eauto.
  destruct (castable_divide Γ σ σc) as [z ->]; auto. rewrite ref_offset_freeze.
  destruct (decide (size_of Γ σc = 0)) as [->|?]; [done|].
  by rewrite !(Nat.mul_comm (_ * size_of _ _)), Nat.mul_assoc, Nat.mod_add.
Qed.
Lemma addr_cast_refine Γ α f m1 m2 a1 a2 σ σc :
  addr_cast_ok Γ m1 σc a1 → a1 ⊑{Γ,α,f@'{m1}↦'{m2}} a2 : σ →
  addr_cast σc a1 ⊑{Γ,α,f@'{m1}↦'{m2}} addr_cast σc a2 : σc.
Proof. intros (?&?&?). destruct 1; simplify_equality'; econstructor; eauto. Qed.
Lemma addr_elt_refine Γ α f Γm1 Γm2 a1 a2 rs σ σ' :
  ✓ Γ → a1 ⊑{Γ,α,f@Γm1↦Γm2} a2 : σ → addr_strict Γ a1 → Γ ⊢ rs : σ ↣ σ' →
  ref_seg_offset rs = 0 →
  addr_elt Γ rs a1 ⊑{Γ,α,f@Γm1↦Γm2} addr_elt Γ rs a2 : σ'.
Proof.
  intros ? [o o' r r' r'' i i'' τ τ' σ'' ??????????? Hcst Hr''] ? Hrs ?; simpl.
  apply castable_alt in Hcst; destruct Hcst as [<-|[?|?]];
    simplify_equality'; try solve [inversion Hrs].
  erewrite path_type_check_complete by eauto; simpl. econstructor; eauto.
  * apply ref_typed_cons; exists σ''; split; auto.
    apply ref_set_offset_typed; auto.
    apply Nat.div_lt_upper_bound; eauto using size_of_ne_0,ref_typed_type_valid.
  * lia.
  * by rewrite Nat.mod_0_l by eauto using size_of_ne_0, ref_typed_type_valid,
      ref_seg_typed_type_valid, castable_type_valid.
  * destruct Hr'' as [i''|]; simplify_equality'; [|by constructor].
    apply ref_refine_ne_nil_alt.
    by rewrite ref_set_offset_set_offset, (Nat.mul_comm (size_of _ _)),
      Nat.div_add, Nat.div_small, Nat.add_0_l, ref_set_offset_offset by lia.
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
Global Instance ptr_compare_ok_dec m c p1 p2 :
  Decision (ptr_compare_ok m c p1 p2).
Proof. destruct p1, p2, c; apply _. Defined.
Global Instance ptr_plus_ok_dec Γ m j p : Decision (ptr_plus_ok Γ m j p).
Proof. destruct p; apply _. Defined.
Global Instance ptr_minus_ok_dec m p1 p2 : Decision (ptr_minus_ok m p1 p2).
Proof. destruct p1, p2; apply _. Defined.
Global Instance ptr_cast_ok_dec Γ m σc p : Decision (ptr_cast_ok Γ m σc p).
Proof. destruct p; apply _. Defined.
Lemma ptr_plus_typed Γ m p σ j :
  ✓ Γ → (Γ,'{m}) ⊢ p : σ → ptr_plus_ok Γ m j p → (Γ,'{m}) ⊢ ptr_plus Γ j p : σ.
Proof. destruct 2; simpl; constructor; eauto using addr_plus_typed. Qed.
Lemma ptr_minus_typed Γ Γm p1 p2 σ :
  ✓ Γ → (Γ,Γm) ⊢ p1 : σ → (Γ,Γm) ⊢ p2 : σ →
  int_typed (ptr_minus Γ p1 p2) sptrT.
Proof.
  destruct 2, 1; simpl;
    eauto using addr_minus_typed, int_typed_small with lia.
Qed.
Lemma ptr_cast_typed Γ m p σ σc :
  (Γ,'{m}) ⊢ p : σ → ptr_cast_ok Γ m σc p →
  ptr_type_valid Γ σc → (Γ,'{m}) ⊢ ptr_cast σc p : σc.
Proof. destruct 1; simpl; constructor; eauto using addr_cast_typed. Qed.

Lemma ptr_compare_ok_weaken m1 m2 c p1 p2 :
  ptr_compare_ok m1 c p1 p2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_compare_ok m2 c p1 p2.
Proof. destruct p1, p2, c; simpl; eauto using addr_minus_ok_weaken. Qed.
Lemma ptr_compare_weaken Γ1 Γ2 Γm1 c p1 p2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p1 : τ1 → (Γ1,Γm1) ⊢ p2 : τ2 →
  Γ1 ⊆ Γ2 → ptr_compare Γ1 c p1 p2 = ptr_compare Γ2 c p1 p2.
Proof.
  destruct 2,1,c; simpl; intros; done || by erewrite addr_minus_weaken by eauto.
Qed.
Lemma ptr_plus_ok_weaken Γ1 Γ2 m1 m2 p τ j :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ p : τ → ptr_plus_ok Γ1 m1 j p →
  Γ1 ⊆ Γ2 → (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_plus_ok Γ2 m2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_ok_weaken. Qed.
Lemma ptr_plus_weaken Γ1 Γ2 Γm1 p τ j :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p : τ → Γ1 ⊆ Γ2 → ptr_plus Γ1 j p = ptr_plus Γ2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_weaken, f_equal. Qed.
Lemma ptr_minus_ok_weaken m1 m2 p1 p2:
  ptr_minus_ok m1 p1 p2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_minus_ok m2 p1 p2.
Proof. destruct p1, p2; simpl; eauto using addr_minus_ok_weaken. Qed.
Lemma ptr_minus_weaken Γ1 Γ2 Γm1 p1 p2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ p1 : τ1 → (Γ1,Γm1) ⊢ p2 : τ2 →
  Γ1 ⊆ Γ2 → ptr_minus Γ1 p1 p2 = ptr_minus Γ2 p1 p2.
Proof. destruct 2, 1; simpl; eauto using addr_minus_weaken. Qed.
Lemma ptr_cast_ok_weaken Γ1 Γ2 m1 m2 p τ σc :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ p : τ → ptr_cast_ok Γ1 m1 σc p → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  ptr_cast_ok Γ2 m2 σc p.
Proof. destruct 2; simpl; eauto using addr_cast_ok_weaken. Qed.
Lemma ptr_compare_ok_alive_l m c p1 p2 :
  ptr_compare_ok m c p1 p2 → ptr_alive ('{m}) p1.
Proof. destruct p1, p2, c; simpl; unfold addr_minus_ok; naive_solver. Qed.
Lemma ptr_compare_ok_alive_r m c p1 p2 :
  ptr_compare_ok m c p1 p2 → ptr_alive ('{m}) p2.
Proof. by destruct p1, p2, c; simpl; try intros (?&<-&?); eauto. Qed.
Lemma ptr_plus_ok_alive Γ m p j : ptr_plus_ok Γ m j p → ptr_alive ('{m}) p.
Proof. destruct p. done. intros [??]; simpl; eauto. Qed.
Lemma ptr_minus_ok_alive_l m p1 p2 : ptr_minus_ok m p1 p2 → ptr_alive ('{m}) p1.
Proof. destruct p1, p2; simpl; try done. intros [??]; eauto. Qed.
Lemma ptr_minus_ok_alive_r m p1 p2 : ptr_minus_ok m p1 p2 → ptr_alive ('{m}) p2.
Proof. destruct p1, p2; simpl; try done. intros (?&<-&?); eauto. Qed.
Lemma ptr_cast_ok_alive Γ m p σ : ptr_cast_ok Γ m σ p → ptr_alive ('{m}) p.
Proof. destruct p; simpl. done. intros [??]; eauto. Qed.

Lemma ptr_alive_refine' Γ α f m1 m2 p1 p2 σ :
  ptr_alive' m1 p1 → p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ → ptr_alive' m2 p2.
Proof. destruct 2; simpl in *; eauto using addr_alive_refine. Qed.
Lemma ptr_compare_ok_refine Γ α f m1 m2 c p1 p2 p3 p4 σ :
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σ →
  ptr_compare_ok m1 c p1 p3 → ptr_compare_ok m2 c p2 p4.
Proof.
  destruct 1, 1, c; simpl; eauto using addr_minus_ok_refine, addr_alive_refine.
Qed.
Lemma ptr_compare_refine Γ α f m1 m2 c p1 p2 p3 p4 σ :
  ✓ Γ → ptr_compare_ok m1 c p1 p3 →
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σ →
  ptr_compare Γ c p1 p3 = ptr_compare Γ c p2 p4.
Proof.
  destruct 3, 1, c; simpl; done || by erewrite addr_minus_refine by eauto.
Qed.
Lemma ptr_plus_ok_refine Γ α f m1 m2 p1 p2 σ j :
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ →
  ptr_plus_ok Γ m1 j p1 → ptr_plus_ok Γ m2 j p2.
Proof. destruct 1; simpl; eauto using addr_plus_ok_refine. Qed.
Lemma ptr_plus_refine Γ α f m1 m2 p1 p2 σ j :
  ✓ Γ → ptr_plus_ok Γ m1 j p1 → p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ →
  ptr_plus Γ j p1 ⊑{Γ,α,f@'{m1}↦'{m2}} ptr_plus Γ j p2 : σ.
Proof. destruct 3; simpl; constructor; eauto using addr_plus_refine. Qed.
Lemma ptr_minus_ok_refine Γ α f m1 m2 p1 p2 p3 p4 σ :
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σ →
  ptr_minus_ok m1 p1 p3 → ptr_minus_ok m2 p2 p4.
Proof. destruct 1, 1; simpl; eauto using addr_minus_ok_refine. Qed.
Lemma ptr_minus_refine Γ α f m1 m2 p1 p2 p3 p4 σ :
  ✓ Γ → ptr_minus_ok m1 p1 p3 →
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ → p3 ⊑{Γ,α,f@'{m1}↦'{m2}} p4 : σ →
  ptr_minus Γ p1 p3 = ptr_minus Γ p2 p4.
Proof. destruct 3, 1; simpl; eauto using addr_minus_refine. Qed.
Lemma ptr_cast_ok_refine Γ α f m1 m2 p1 p2 σ σc :
  ✓ Γ → p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ →
  ptr_cast_ok Γ m1 σc p1 → ptr_cast_ok Γ m2 σc p2.
Proof. destruct 2; simpl; eauto using addr_cast_ok_refine. Qed.
Lemma ptr_cast_refine Γ α f m1 m2 p1 p2 σ σc :
  ptr_cast_ok Γ m1 σc p1 → ptr_type_valid Γ σc →
  p1 ⊑{Γ,α,f@'{m1}↦'{m2}} p2 : σ →
  ptr_cast σc p1 ⊑{Γ,α,f@'{m1}↦'{m2}} ptr_cast σc p2 : σc.
Proof. destruct 3; constructor; eauto using addr_cast_refine. Qed.

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
Proof. destruct 1; constructor; eauto using TPtr_valid_inv. Qed.
Lemma base_cast_typed_type_valid Γ τb σb :
  base_cast_typed Γ τb σb → ✓{Γ} τb → ✓{Γ} σb.
Proof. destruct 1; repeat constructor; eauto using TPtr_valid_inv. Qed.
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
Proof. by destruct 1; simplify_option_equality. Qed.
Global Instance base_cast_typed_dec Γ τb σb: Decision (base_cast_typed Γ τb σb).
Proof.
 refine
  match τb, σb with
  | _, voidT => left _
  | intT τi1, intT τi2 => left _
  | τ1.*, τ2.* => cast_if (decide (τ1 = τ2 ∨ τ2 = voidT%T ∨ τ2 = ucharT%T ∨
      τ1 = voidT%T ∧ ptr_type_valid Γ τ2 ∨ τ1 = ucharT%T ∧ ptr_type_valid Γ τ2))
  | _, _ => right _
  end%BT; abstract first
    [by intuition; subst; constructor|by inversion 1; naive_solver].
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
Lemma base_val_unop_typed Γ m op vb τb σb :
  (Γ,'{m}) ⊢ vb : τb → base_unop_typed op τb σb →
  base_val_unop_ok m op vb → (Γ,'{m}) ⊢ base_val_unop op vb : σb.
Proof.
  unfold base_val_unop_ok, base_val_unop. intros Hvτb Hσ Hop.
  destruct Hσ as [τi|?|?|?]; inversion Hvτb; simplify_equality'; try done.
  * typed_constructor. rewrite <-(idempotent (∪) (int_promote τi)).
    apply int_arithop_typed; auto. by apply int_typed_small.
  * typed_constructor. apply int_of_bits_typed.
    by rewrite fmap_length, int_to_bits_length.
  * typed_constructor. by apply int_typed_small; case_decide.
  * typed_constructor. by apply int_typed_small; case_match.
Qed.
Lemma base_val_binop_ok_weaken Γ1 Γ2 m1 m2 op vb1 vb2 τb1 τb2 :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ vb1 : τb1 → (Γ1,'{m1}) ⊢ vb2 : τb2 →
  base_val_binop_ok Γ1 m1 op vb1 vb2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  base_val_binop_ok Γ2 m2 op vb1 vb2.
Proof.
  destruct 2, 1, op as [|[]| |]; simpl; auto; eauto 2 using
    ptr_plus_ok_weaken, ptr_minus_ok_weaken, ptr_compare_ok_weaken.
Qed.
Lemma base_val_binop_weaken Γ1 Γ2 Γm1 op vb1 vb2 τb1 τb2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ vb1 : τb1 → (Γ1,Γm1) ⊢ vb2 : τb2 → Γ1 ⊆ Γ2 →
  base_val_binop Γ1 op vb1 vb2 = base_val_binop Γ2 op vb1 vb2.
Proof.
  destruct 2, 1, op as [|[]| |]; intros; f_equal';
    eauto 2 using ptr_plus_weaken, ptr_minus_weaken.
  by erewrite ptr_compare_weaken by eauto.
Qed.
Lemma base_val_binop_typed Γ m op vb1 vb2 τb1 τb2 σb :
  ✓ Γ → (Γ,'{m}) ⊢ vb1 : τb1 → (Γ,'{m}) ⊢ vb2 : τb2 →
  base_binop_typed op τb1 τb2 σb → base_val_binop_ok Γ m op vb1 vb2 →
  (Γ,'{m}) ⊢ base_val_binop Γ op vb1 vb2 : σb.
Proof.
  unfold base_val_binop_ok, base_val_binop. intros HΓ Hv1τb Hv2τb Hσ Hop.
  revert Hv1τb Hv2τb.
  destruct Hσ; inversion 1; inversion 1; simplify_equality'; try done.
  * constructor. by case_match; apply int_typed_small.
  * constructor. by apply int_arithop_typed.
  * constructor. by apply int_shiftop_typed.
  * constructor. apply int_of_bits_typed.
    rewrite zip_with_length, !int_to_bits_length; lia.
  * constructor. by case_match; apply int_typed_small.
  * constructor. eapply ptr_plus_typed; eauto.
  * constructor. eapply ptr_plus_typed; eauto.
  * constructor. eapply ptr_plus_typed; eauto.
  * constructor. eapply ptr_plus_typed; eauto.
  * constructor. eapply ptr_minus_typed; eauto.
Qed.
Lemma base_cast_typed_self Γ τb : base_cast_typed Γ τb τb.
Proof. destruct τb; constructor. Qed.
Lemma base_val_cast_ok_weaken Γ1 Γ2 m1 m2 vb τb σb :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ vb : τb → base_val_cast_ok Γ1 m1 σb vb →
  Γ1 ⊆ Γ2 → (∀ o : index, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  base_val_cast_ok Γ2 m2 σb vb.
Proof.
  destruct 2, σb; simpl; eauto using ptr_cast_ok_weaken, ptr_alive_weaken'.
Qed.
Lemma base_val_cast_typed Γ m vb τb σb :
  ✓ Γ → (Γ,'{m}) ⊢ vb : τb → base_cast_typed Γ τb σb →
  base_val_cast_ok Γ m σb vb → (Γ,'{m}) ⊢ base_val_cast σb vb : σb.
Proof.
  unfold base_val_cast_ok, base_val_cast. intros ? Hvτb Hσb Hok. revert Hvτb.
  destruct Hσb; inversion 1; simplify_equality'; try (done || by constructor).
  * intuition; simplify_equality. by constructor.
  * constructor. by apply int_cast_typed.
  * constructor. eapply ptr_cast_typed,
      TPtr_valid_inv, base_val_typed_type_valid; eauto.
  * constructor.
    eapply ptr_cast_typed; eauto using TBase_ptr_valid, TVoid_valid.
  * constructor. eapply ptr_cast_typed;
      eauto using TBase_ptr_valid, TInt_valid.
  * constructor. eapply ptr_cast_typed; eauto.
  * constructor. eapply ptr_cast_typed; eauto.
Qed.
Lemma base_val_cast_ok_void Γ m vb :
  (Γ,'{m}) ⊢ vb : ucharT%BT → base_val_cast_ok Γ m voidT%BT vb.
Proof. by inversion 1. Qed.
Lemma base_val_cast_void vb : base_val_cast voidT vb = VVoid.
Proof. by destruct vb. Qed.

Lemma base_val_true_refine Γ α f m1 m2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_true m1 vb1 → base_val_true m2 vb2.
Proof.
  destruct 1 as [| | | |??? []|???? []| | |];
    naive_solver eauto 10 using addr_alive_refine.
Qed.
Lemma base_val_false_refine Γ α f Γm1 Γm2 vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@Γm1↦Γm2} vb2 : τb → base_val_false vb1 → base_val_false vb2.
Proof. by destruct 1 as [| | | |??? []|???? []| | |]. Qed.
Lemma base_val_unop_ok_refine Γ α f m1 m2 op vb1 vb2 τb :
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_unop_ok m1 op vb1 → base_val_unop_ok m2 op vb2.
Proof. destruct op, 1; naive_solver eauto using ptr_alive_refine'. Qed.
Lemma base_val_unop_refine Γ α f m1 m2 op vb1 vb2 τb σb :
  ✓ Γ → base_unop_typed op τb σb → base_val_unop_ok m1 op vb1 →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_unop op vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} base_val_unop op vb2 : σb.
Proof.
  intros ? Hvτb ? Hvb. assert ((Γ,'{m2}) ⊢ base_val_unop op vb2 : σb) as Hvb2.
  { eauto using base_val_unop_typed,
      base_val_refine_typed_r, base_val_unop_ok_refine. }
  destruct Hvτb; inversion Hvb as [| | | |p1 p2 ? Hp| | | |];
    simplify_equality'; try done.
  * refine_constructor. rewrite <-(idempotent (∪) (int_promote τi)).
    apply int_arithop_typed; auto. by apply int_typed_small.
  * refine_constructor. apply int_of_bits_typed.
    by rewrite fmap_length, int_to_bits_length.
  * refine_constructor. by apply int_typed_small; case_decide.
  * destruct Hp; refine_constructor; by apply int_typed_small.
  * naive_solver.
Qed.
Lemma base_val_binop_ok_refine Γ α f m1 m2 op vb1 vb2 vb3 vb4 τb1 τb3 σb :
  ✓ Γ → base_binop_typed op τb1 τb3 σb →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb1 → vb3 ⊑{Γ,α,f@'{m1}↦'{m2}} vb4 : τb3 →
  base_val_binop_ok Γ m1 op vb1 vb3 → base_val_binop_ok Γ m2 op vb2 vb4.
Proof.
  intros ? Hσ. destruct 1, 1; try done; inversion Hσ;
   try naive_solver eauto using ptr_minus_ok_alive_l, ptr_minus_ok_alive_r,
    ptr_plus_ok_alive, ptr_plus_ok_refine, ptr_minus_ok_refine,
    ptr_compare_ok_refine, ptr_compare_ok_alive_l, ptr_compare_ok_alive_r.
Qed.
Lemma base_val_binop_refine Γ α f m1 m2 op vb1 vb2 vb3 vb4 τb1 τb3 σb :
  ✓ Γ → base_binop_typed op τb1 τb3 σb → base_val_binop_ok Γ m1 op vb1 vb3 →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb1 → vb3 ⊑{Γ,α,f@'{m1}↦'{m2}} vb4 : τb3 →
  base_val_binop Γ op vb1 vb3
    ⊑{Γ,α,f@'{m1}↦'{m2}} base_val_binop Γ op vb2 vb4 : σb.
Proof.
  intros ? Hσ ?; destruct 1, 1; try done; inversion Hσ; simplify_equality';
    try first
    [ by refine_constructor; eauto using int_arithop_typed,
        int_arithop_typed, int_shiftop_typed, ptr_plus_refine
    | exfalso; by eauto using ptr_minus_ok_alive_l, ptr_minus_ok_alive_r,
        ptr_plus_ok_alive, ptr_compare_ok_alive_l, ptr_compare_ok_alive_r ].
  * refine_constructor. by case_match; apply int_typed_small.
  * refine_constructor. apply int_of_bits_typed.
    rewrite zip_with_length, !int_to_bits_length; lia.
  * erewrite ptr_compare_refine by eauto.
    refine_constructor. by case_match; apply int_typed_small.
  * erewrite ptr_minus_refine by eauto. refine_constructor.
    eapply ptr_minus_typed; eauto using ptr_refine_typed_l, ptr_refine_typed_r.
Qed.
Lemma base_val_cast_ok_refine Γ α f m1 m2 vb1 vb2 τb σb :
  ✓ Γ → vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_cast_ok Γ m1 σb vb1 → base_val_cast_ok Γ m2 σb vb2.
Proof.
  assert (∀ vb, (Γ,'{m2}) ⊢ vb : ucharT%BT → base_val_cast_ok Γ m2 ucharT vb).
  { inversion 1; simpl; eauto using int_unsigned_pre_cast_ok,int_cast_ok_more. }
  destruct σb, 2; simpl; try naive_solver eauto using
    ptr_cast_ok_refine, ptr_cast_ok_alive, base_val_cast_ok_void,
    int_unsigned_pre_cast_ok, int_cast_ok_more, ptr_alive_refine'.
Qed.
Lemma base_val_cast_refine Γ α f m1 m2 vb1 vb2 τb σb :
  ✓ Γ → base_cast_typed Γ τb σb → base_val_cast_ok Γ m1 σb vb1 →
  vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} vb2 : τb →
  base_val_cast σb vb1 ⊑{Γ,α,f@'{m1}↦'{m2}} base_val_cast σb vb2 : σb.
Proof.
  assert (∀ vb,
    (Γ,'{m2}) ⊢ vb : ucharT%BT → base_val_cast ucharT vb = vb) as help.
  { inversion 1; f_equal'. by rewrite int_cast_spec, int_typed_pre_cast
      by eauto using int_unsigned_pre_cast_ok,int_cast_ok_more. }
  destruct 2; inversion 2;
    simplify_equality'; intuition; simplify_equality'; try first
    [ by exfalso; eauto using ptr_cast_ok_alive
    | rewrite ?base_val_cast_void, ?help, ?int_cast_spec, ?int_typed_pre_cast
        by eauto using int_unsigned_pre_cast_ok,int_cast_ok_more;
      by refine_constructor; eauto using ptr_cast_refine, int_cast_typed,
        ptr_cast_refine, TVoid_valid, TBase_ptr_valid, TInt_valid,
        TPtr_valid_inv, base_val_typed_type_valid, base_val_refine_typed_l ].
Qed.

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

Global Instance val_unop_ok_dec m op v : Decision (val_unop_ok m op v).
Proof. destruct v; try apply _. Defined.
Global Instance val_binop_ok_dec Γ m op v1 v2 :
  Decision (val_binop_ok Γ m op v1 v2).
Proof. destruct v1, v2; apply _. Defined.
Global Instance val_cast_ok_dec Γ m σ v : Decision (val_cast_ok Γ m σ v).
Proof. destruct v, σ as [[]| |]; apply _. Defined.

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
Lemma val_unop_typed Γ m op v τ σ :
  (Γ,'{m}) ⊢ v : τ → unop_typed op τ σ → val_unop_ok m op v →
  (Γ,'{m}) ⊢ val_unop op v : σ.
Proof.
  intros Hvτ Hσ Hop. destruct Hσ; inversion Hvτ; simpl; simplify_equality;
    done || constructor; eauto using base_val_unop_typed.
Qed.
Lemma val_binop_ok_weaken Γ1 Γ2 m1 m2 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ v1 : τ1 → (Γ1,'{m1}) ⊢ v2 : τ2 →
  val_binop_ok Γ1 m1 op v1 v2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) →
  val_binop_ok Γ2 m2 op v1 v2.
Proof.
  destruct 2, 1, op; simpl; try done; eauto 2 using base_val_binop_ok_weaken.
Qed.
Lemma val_binop_weaken Γ1 Γ2 Γm1 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Γm1) ⊢ v1 : τ1 → (Γ1,Γm1) ⊢ v2 : τ2 → Γ1 ⊆ Γ2 →
  val_binop Γ1 op v1 v2 = val_binop Γ2 op v1 v2.
Proof.
  destruct 2, 1, op; intros; f_equal'; eauto 2 using base_val_binop_weaken.
Qed.
Lemma val_binop_typed Γ m op v1 v2 τ1 τ2 σ :
  ✓ Γ → (Γ,'{m}) ⊢ v1 : τ1 → (Γ,'{m}) ⊢ v2 : τ2 →
  binop_typed op τ1 τ2 σ → val_binop_ok Γ m op v1 v2 →
  (Γ,'{m}) ⊢ val_binop Γ op v1 v2 : σ.
Proof.
  intros ? Hv1τ Hv2τ Hσ Hop.
  destruct Hσ; inversion Hv1τ; inversion Hv2τ; simplify_equality';
    done || constructor; eauto using base_val_binop_typed.
Qed.
Lemma val_cast_ok_weaken Γ1 Γ2 m1 m2 v τ σ :
  ✓ Γ1 → (Γ1,'{m1}) ⊢ v : τ → val_cast_ok Γ1 m1 σ v → Γ1 ⊆ Γ2 →
  (∀ o, index_alive ('{m1}) o → index_alive ('{m2}) o) → val_cast_ok Γ2 m2 σ v.
Proof. destruct 2, σ; simpl; eauto using base_val_cast_ok_weaken. Qed.
Lemma val_cast_typed Γ m v τ σ :
  ✓ Γ → (Γ,'{m}) ⊢ v : τ → cast_typed Γ τ σ → val_cast_ok Γ m σ v →
  (Γ,'{m}) ⊢ val_cast σ v : σ.
Proof.
  intros ? Hvτ Hσ Hok. destruct Hσ; inversion Hvτ; simplify_equality';
    repeat typed_constructor;
    eauto using base_val_cast_typed, TVoid_cast_typed, base_cast_typed_self.
Qed.

Lemma val_true_refine Γ α f m1 m2 v1 v2 τ :
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ → val_true m1 v1 → val_true m2 v2.
Proof. destruct 1; simpl; eauto using base_val_true_refine. Qed.
Lemma val_false_refine Γ α f Γm1 Γm2 v1 v2 τ :
  v1 ⊑{Γ,α,f@Γm1↦Γm2} v2 : τ → val_false v1 → val_false v2.
Proof. destruct 1; simpl; eauto using base_val_false_refine. Qed.
Lemma val_true_false_refine Γ α f m1 m2 v1 v2 τ :
  val_true m1 v1 → val_false v2 → v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ → False.
Proof.
  intros. by destruct (val_true_false_dec m2 v2)
    as [[[??]|[??]]|[??]]; eauto using val_true_refine.
Qed.
Lemma val_false_true_refine Γ α f m1 m2 v1 v2 τ :
  val_false v1 → val_true m2 v2 → v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ → False.
Proof.
  intros. by destruct (val_true_false_dec m2 v2)
    as [[[??]|[??]]|[??]]; eauto using val_false_refine.
Qed.
Lemma val_true_refine_inv Γ α f m1 m2 v1 v2 τ :
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ → val_true m2 v2 →
  val_true m1 v1 ∨ ¬val_true m1 v1 ∧ ¬val_false v1.
Proof.
  intros. destruct (val_true_false_dec m1 v1)
    as [[[??]|[??]]|[??]]; eauto using val_false_true_refine.
Qed.
Lemma val_false_refine_inv Γ α f m1 m2 v1 v2 τ :
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ → val_false v2 →
  val_false v1 ∨ ¬val_true m1 v1 ∧ ¬val_false v1.
Proof.
  intros. destruct (val_true_false_dec m1 v1)
    as [[[??]|[??]]|[??]]; eauto using val_true_false_refine.
Qed.
Lemma val_unop_ok_refine Γ α f m1 m2 op v1 v2 τ :
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_unop_ok m1 op v1 → val_unop_ok m2 op v2.
Proof. destruct op, 1; simpl; eauto using base_val_unop_ok_refine. Qed.
Lemma val_unop_refine Γ α f m1 m2 op v1 v2 τ σ :
  ✓ Γ → unop_typed op τ σ → val_unop_ok m1 op v1 →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_unop op v1 ⊑{Γ,α,f@'{m1}↦'{m2}} val_unop op v2 : σ.
Proof.
  destruct 2; inversion 2; intros; simplify_equality';
    refine_constructor; eauto using base_val_unop_refine.
Qed.
Lemma val_binop_ok_refine Γ α f m1 m2 op v1 v2 v3 v4 τ1 τ3 σ :
  ✓ Γ → binop_typed op τ1 τ3 σ →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ1 → v3 ⊑{Γ,α,f@'{m1}↦'{m2}} v4 : τ3 →
  val_binop_ok Γ m1 op v1 v3 → val_binop_ok Γ m2 op v2 v4.
Proof.
  unfold val_binop_ok; destruct 2; do 2 inversion 1;
    simplify_equality'; eauto using base_val_binop_ok_refine.
Qed.
Lemma val_binop_refine Γ α f m1 m2 op v1 v2 v3 v4 τ1 τ3 σ :
  ✓ Γ → binop_typed op τ1 τ3 σ → val_binop_ok Γ m1 op v1 v3 →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ1 → v3 ⊑{Γ,α,f@'{m1}↦'{m2}} v4 : τ3 →
  val_binop Γ op v1 v3 ⊑{Γ,α,f@'{m1}↦'{m2}} val_binop Γ op v2 v4 : σ.
Proof.
  destruct 2; intro; do 2 inversion 1; simplify_equality';
    refine_constructor; eauto using base_val_binop_refine.
Qed.
Lemma val_cast_ok_refine Γ α f m1 m2 v1 v2 τ σ :
  ✓ Γ → v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_cast_ok Γ m1 σ v1 → val_cast_ok Γ m2 σ v2.
Proof.
  unfold val_cast_ok; destruct σ, 2; eauto using base_val_cast_ok_refine.
Qed.
Lemma val_cast_refine Γ α f m1 m2 v1 v2 τ σ :
  ✓ Γ → cast_typed Γ τ σ → val_cast_ok Γ m1 σ v1 →
  v1 ⊑{Γ,α,f@'{m1}↦'{m2}} v2 : τ →
  val_cast σ v1 ⊑{Γ,α,f@'{m1}↦'{m2}} val_cast σ v2 : σ.
Proof.
  destruct 2; inversion 2; simplify_equality; repeat refine_constructor;
    eauto using base_val_cast_refine, TVoid_cast_typed, base_cast_typed_self.
Qed.
End properties.
