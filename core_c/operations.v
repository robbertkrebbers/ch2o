(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_map values.
Require Import pointer_casts.

Local Open Scope ctype_scope.
Local Coercion Z.of_nat: nat >-> Z.

Section operations_definitions.
  Context `{Env K}.

  (** ** Operations on addresses *)
  Definition addr_compare_ok (Γ : env K) (m : mem K)
      (c : compop) (a1 a2 : addr K) : Prop :=
    index_alive' m (addr_index a1) ∧ index_alive' m (addr_index a2) ∧
    (addr_index a1 ≠ addr_index a2 →
      c = EqOp ∧ addr_strict Γ a1 ∧ addr_strict Γ a2).
  Definition addr_compare (Γ : env K) (c : compop) (a1 a2 : addr K) : bool :=
    bool_decide (addr_index a1 = addr_index a2 ∧
      Z_comp c (addr_object_offset Γ a1) (addr_object_offset Γ a2)).
  Definition addr_plus_ok (Γ : env K) (m : mem K)
      (j : Z) (a : addr K) : Prop :=
    index_alive' m (addr_index a) ∧
    (0 ≤ addr_byte a + j * ptr_size_of Γ (type_of a)
       ≤ size_of Γ (addr_type_base a) * ref_size (addr_ref_base a))%Z.
  Global Arguments addr_plus_ok _ _ _ !_ /.
  Definition addr_plus (Γ : env K) (j : Z) (a : addr K): addr K :=
    let 'Addr x r i τ σ σp := a
    in Addr x r (Z.to_nat (i + j * ptr_size_of Γ σp)) τ σ σp.
  Global Arguments addr_plus _ _ !_ /.
  Definition addr_minus (Γ : env K) (a1 a2 : addr K) : Z :=
    ((addr_byte a1 - addr_byte a2) `div` ptr_size_of Γ (type_of a1))%Z.
  Global Arguments addr_minus _ !_ !_ /.
  Definition addr_minus_ok (Γ : env K) (m : mem K) (a1 a2 : addr K) : Prop :=
    index_alive' m (addr_index a1) ∧
    addr_index a1 = addr_index a2 ∧
    freeze true <$> addr_ref_base a1 = freeze true <$> addr_ref_base a2 ∧
    int_typed (addr_minus Γ a1 a2) sptrT.
  Global Arguments addr_minus_ok _ _ !_ !_ /.
  Definition addr_cast_ok (Γ : env K) (m : mem K)
      (σp : ptr_type K) (a : addr K) : Prop :=
    index_alive' m (addr_index a) ∧
    addr_type_base a >*> σp ∧
    (ptr_size_of Γ σp | addr_byte a).
  Global Arguments addr_cast_ok _ _ _ !_ /.
  Definition addr_cast (σp : ptr_type K) (a : addr K) : addr K :=
    let 'Addr o r i τ σ _ := a in Addr o r i τ σ σp.
  Global Arguments addr_cast _ !_ /.

  (** ** Operations on pointers *)
  Definition ptr_alive' (m : mem K) (p : ptr K) : Prop :=
    match p with Ptr a => index_alive' m (addr_index a) | _ => True end.
  Definition ptr_compare_ok (Γ : env K)  (m : mem K)
      (c : compop) (p1 p2 : ptr K) : Prop :=
    match p1, p2, c with
    | Ptr a1, Ptr a2, _ => addr_compare_ok Γ m c a1 a2
    | FunPtr f1 _ _, FunPtr f2 _ _, EqOp => True
    | NULL _, NULL _, _ => True
    | NULL _, Ptr a2, EqOp => index_alive' m (addr_index a2)
    | NULL _, FunPtr _ _ _, EqOp => True
    | Ptr a1, NULL _, EqOp => index_alive' m (addr_index a1)
    | FunPtr _ _ _, NULL _, EqOp => True
    | _, _, _ => False
    end.
  Definition ptr_compare (Γ : env K) (c : compop) (p1 p2 : ptr K) : bool :=
    match p1, p2, c with
    | Ptr a1, Ptr a2, _ => addr_compare Γ c a1 a2
    | FunPtr f1 _ _, FunPtr f2 _ _, EqOp => bool_decide (f1 = f2)
    | NULL _, NULL _, (EqOp | LeOp) => true
    | NULL _, NULL _, LtOp => false
    | NULL _, (Ptr _ | FunPtr _ _ _), _ => false
    | (Ptr _ | FunPtr _ _ _), NULL _, _ => false
    | _, _, _ => false
    end.
  Definition ptr_plus_ok (Γ : env K) (m : mem K) (j : Z) (p : ptr K) :=
    match p with
    | NULL _ => j = 0 | Ptr a => addr_plus_ok Γ m j a | _ => False
    end.
  Global Arguments ptr_plus_ok _ _ _ !_ /.
  Definition ptr_plus (Γ : env K) (j : Z) (p : ptr K) : ptr K :=
    match p with Ptr a => Ptr (addr_plus Γ j a) | _ => p end.
  Global Arguments ptr_plus _ _ !_ /.
  Definition ptr_minus_ok (Γ : env K) (m : mem K) (p1 p2 : ptr K) : Prop :=
    match p1, p2 with
    | NULL _, NULL _ => True
    | Ptr a1, Ptr a2 => addr_minus_ok Γ m a1 a2
    | _, _ => False
    end.
  Global Arguments ptr_minus_ok _ _ !_ !_ /.
  Definition ptr_minus (Γ : env K) (p1 p2 : ptr K) : Z :=
    match p1, p2 with
    | NULL _, NULL _ => 0
    | Ptr a1, Ptr a2 => addr_minus Γ a1 a2
    | _, _ => 0
    end.
  Global Arguments ptr_minus _ !_ !_ /.
  Inductive ptr_cast_typed : ptr_type K → ptr_type K → Prop :=
    | TAny_to_TAny_cast_typed : ptr_cast_typed TAny TAny
    | TType_to_TType_cast_typed τ : ptr_cast_typed (TType τ) (TType τ)
    | TType_to_TAny_cast_typed τ : ptr_cast_typed (TType τ) TAny
    | TType_to_TChar_cast_typed τ : ptr_cast_typed (TType τ) ucharT
    | TAny_to_TType_cast_typed τ : ptr_cast_typed TAny (TType τ)
    | TChar_to_TType_cast_typed τ : ptr_cast_typed ucharT (TType τ)
    | TFun_to_TFun_cast_typed τs τ : ptr_cast_typed (τs ~> τ) (τs ~> τ).
  Definition ptr_cast_ok (Γ : env K) (m : mem K)
      (σp : ptr_type K) (p : ptr K) : Prop :=
    match p with Ptr a => addr_cast_ok Γ m σp a | _ => True end.
  Global Arguments ptr_cast_ok _ _ _ !_ /.
  Definition ptr_cast (σp : ptr_type K) (p : ptr K) : ptr K :=
    match p with
    | NULL _ => NULL σp | Ptr a => Ptr (addr_cast σp a) | _ => p
    end.
  Global Arguments ptr_cast _ !_ /.  

  (** ** Operations on base values *)
  Definition base_val_branchable (m : mem K) (vb : base_val K) : Prop :=
    match vb with
    | VInt _ _ => True
    | VPtr p => ptr_alive' m p
    | _ => False
    end.
  Definition base_val_is_0 (vb : base_val K) : Prop :=
    match vb with
    | VInt _ x => x = 0
    | VPtr (NULL _) => True
    | _ => False
    end.
  Definition base_val_0 (τb : base_type K) : base_val K :=
    match τb with
    | voidT => VVoid | intT τi => VInt τi 0 | τ.* => VPtr (NULL τ)
    end%BT.
  Inductive base_unop_typed : unop → base_type K → base_type K → Prop :=
    | TInt_unop_typed op τi :
       base_unop_typed op (intT τi) (intT (int_unop_type_of op τi))
    | TPtr_NotOp_typed τ : base_unop_typed NotOp (τ.*) sintT.
  Definition base_unop_type_of (op : unop)
      (τb : base_type K) : option (base_type K) :=
    match τb, op with
    | intT τi, op => Some (intT (int_unop_type_of op τi))
    | τ.*, NotOp => Some sintT
    | _, _ => None
    end%BT.
  Definition base_val_unop_ok (m : mem K)
      (op : unop) (vb : base_val K) : Prop :=
    match vb, op with
    | VInt τi x, op => int_unop_ok op x τi
    | VPtr p, NotOp => ptr_alive' m p
    | _, _ => False
    end.
  Global Arguments base_val_unop_ok _ !_ !_ /.
  Definition base_val_unop (op : unop) (vb : base_val K) : base_val K :=
    match vb, op with
    | VInt τi x, op => VInt (int_unop_type_of op τi) (int_unop op x τi)
    | VPtr p, NotOp => VInt sintT (match p with Ptr _ => 0 | _ => 1 end)
    | _, _ => vb (* dummy *)
    end.
  Global Arguments base_val_unop !_ !_ /.

  Inductive base_binop_typed :
        binop → base_type K → base_type K → base_type K → Prop :=
    | TInt_binop_typed op τi1 τi2 :
       base_binop_typed op (intT τi1) (intT τi2)
         (intT (int_binop_type_of op τi1 τi2))
    | CompOp_TPtr_TPtr_typed c τp :
       base_binop_typed (CompOp c) (τp.*) (τp.*) sintT
    | PlusOp_TPtr_TInt_typed τ σ :
       base_binop_typed (ArithOp PlusOp) (TType τ.*) (intT σ) (TType τ.*)
    | PlusOp_VInt_TPtr_typed τ σ :
       base_binop_typed (ArithOp PlusOp) (intT σ) (TType τ.*) (TType τ.*)
    | MinusOp_TPtr_TInt_typed τ σi :
       base_binop_typed (ArithOp MinusOp) (TType τ.*) (intT σi) (TType τ.*)
    | MinusOp_TInt_TPtr_typed τ σi :
       base_binop_typed (ArithOp MinusOp) (intT σi) (TType τ.*) (TType τ.*)
    | MinusOp_TPtr_TPtr_typed τ  :
       base_binop_typed (ArithOp MinusOp) (TType τ.*) (TType τ.*) sptrT.
  Definition base_binop_type_of
      (op : binop) (τb1 τb2 : base_type K) : option (base_type K) :=
    match τb1, τb2, op with
    | intT τi1, intT τi2, op => Some (intT (int_binop_type_of op τi1 τi2))
    | τp1.*, τp2.*, CompOp _ => guard (τp1 = τp2); Some sintT
    | TType τ.*, intT σ, ArithOp (PlusOp | MinusOp) => Some (TType τ.*)
    | intT σ, TType τ.*, ArithOp (PlusOp | MinusOp) => Some (TType τ.*)
    | TType τ1.*, TType τ2.*, ArithOp MinusOp => guard (τ1 = τ2); Some sptrT
    | _, _, _ => None
    end%BT.
  Definition base_val_binop_ok (Γ : env K) (m : mem K)
      (op : binop) (vb1 vb2 : base_val K) : Prop :=
    match vb1, vb2, op with
    | VInt τi1 x1, VInt τi2 x2, op => int_binop_ok op x1 τi1 x2 τi2
    | VPtr p1, VPtr p2, CompOp c => ptr_compare_ok Γ m c p1 p2
    | VPtr p, VInt _ x, ArithOp PlusOp => ptr_plus_ok Γ m x p
    | VInt _ x, VPtr p, ArithOp PlusOp => ptr_plus_ok Γ m x p
    | VPtr p, VInt _ x, ArithOp MinusOp => ptr_plus_ok Γ m (-x) p
    | VInt _ x, VPtr p, ArithOp MinusOp => ptr_plus_ok Γ m (-x) p
    | VPtr p1, VPtr p2, ArithOp MinusOp => ptr_minus_ok Γ m p1 p2
    | _, _, _ => False
    end.
  Global Arguments base_val_binop_ok _ _ !_ !_ !_ /.
  Definition base_val_binop (Γ : env K)
      (op : binop) (v1 v2 : base_val K) : base_val K :=
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

  Inductive base_cast_typed : base_type K → base_type K → Prop :=
    | TVoid_cast_typed τb : base_cast_typed τb voidT
    | TInt_cast_typed τi1 τi2 : base_cast_typed (intT τi1) (intT τi2)
    | TPtr_to_TPtr_cast_typed τp1 τp2 :
       ptr_cast_typed τp1 τp2 → base_cast_typed (τp1.*) (τp2.*).
  Definition base_val_cast_ok (Γ : env K) (m : mem K)
      (τb : base_type K) (vb : base_val K) : Prop :=
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
  Definition base_val_cast (τb : base_type K)
      (vb : base_val K) : base_val K :=
    match vb, τb with
    | _, voidT => VVoid
    | VInt _ x, intT τi => VInt τi (int_cast τi x)
    | VPtr p, τ.* => VPtr (ptr_cast τ p)
    | _ , _ => vb
    end%BT.
  Global Arguments base_val_cast !_ !_ /.

  (** ** Operations on values *)
  Definition val_0 (Γ : env K) : type K → val K := type_iter
    (**i TBase     *) (λ τb, VBase (base_val_0 τb))
    (**i TArray    *) (λ τ n x, VArray τ (replicate n x))
    (**i TCompound *) (λ c t τs rec,
      match c with
      | Struct_kind => VStruct t (rec <$> τs)
      | Union_kind => VUnion t 0 (from_option rec (VUnionAll t []) (τs !! 0))
      end) Γ.

  Inductive unop_typed : unop → type K → type K → Prop :=
    | TBase_unop_typed op τb σb :
       base_unop_typed op τb σb → unop_typed op (baseT τb) (baseT σb).
  Definition unop_type_of (op : unop) (τ : type K) : option (type K) :=
    match τ with
    | baseT τb => σb ← base_unop_type_of op τb; Some (baseT σb) | _ => None
    end.
  Definition val_unop_ok (m : mem K) (op : unop) (v : val K) : Prop :=
    match v with VBase vb => base_val_unop_ok m op vb | _ => False end.
  Global Arguments val_unop_ok _ !_ !_ /.
  Definition val_unop (op : unop) (v : val K) : val K :=
    match v with VBase vb => VBase (base_val_unop op vb) | _ => v end.
  Global Arguments val_unop !_ !_ /.

  Inductive binop_typed : binop → type K → type K → type K → Prop :=
    | TBase_binop_typed op τb1 τb2 σb :
       base_binop_typed op τb1 τb2 σb →
       binop_typed op (baseT τb1) (baseT τb2) (baseT σb).
  Definition binop_type_of (op : binop) (τ1 τ2 : type K) : option (type K) :=
    match τ1, τ2 with
    | baseT τb1, baseT τb2 =>
       σb ← base_binop_type_of op τb1 τb2; Some (baseT σb)
    | _, _ => None
    end.
  Definition val_binop_ok (Γ : env K) (m : mem K)
      (op : binop) (v1 v2 : val K) : Prop :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => base_val_binop_ok Γ m op vb1 vb2 | _, _ => False
    end.
  Global Arguments val_binop_ok _ _ !_ !_ !_ /.
  Definition val_binop (Γ : env K) (op : binop) (v1 v2 : val K) : val K :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => VBase (base_val_binop Γ op vb1 vb2) | _, _ => v1
    end.
  Global Arguments val_binop _ !_ !_ !_ /.

  Inductive cast_typed : type K → type K → Prop :=
    | cast_typed_self τ : cast_typed τ τ
    | TBase_cast_typed τb1 τb2 :
       base_cast_typed τb1 τb2 → cast_typed (baseT τb1) (baseT τb2)
    | TBase_TVoid_cast_typed τ : cast_typed τ voidT.
  Definition val_cast_ok (Γ : env K) (m : mem K)
      (τp : ptr_type K) (v : val K) : Prop :=
    match v, τp with
    | VBase vb, TType (baseT τb) => base_val_cast_ok Γ m τb vb | _, _ => True
    end.
  Global Arguments val_cast_ok _ _ !_ !_ /.
  Definition val_cast (τp : ptr_type K) (v : val K) : val K :=
    match v, τp with
    | VBase vb, TType (baseT τb) => VBase (base_val_cast τb vb)
    | _, TType voidT => VBase VVoid | _ , _ => v
    end.
  Global Arguments val_cast !_ !_ /.
End operations_definitions.

Section operations.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τb σb : base_type K.
Implicit Types τp σp : ptr_type K.
Implicit Types τ σ : type K.
Implicit Types a : addr K.
Implicit Types vb : base_val K.
Implicit Types v : val K.
Implicit Types m : mem K.
Hint Immediate index_alive_1': core.
Hint Resolve index_alive_2': core.

Arguments addr_is_obj _ !_ /.
Arguments addr_ref _ _ _ !_ /.
Arguments addr_ref_byte _ _ _ !_ /.

(** ** Properties of operations on addresses *)
Lemma addr_compare_ok_weaken Γ1 Γ2 Δ1 m1 m2 c a1 a2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a1 : τp1 → (Γ1,Δ1) ⊢ a2 : τp2 →
  Γ1 ⊆ Γ2 → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  addr_compare_ok Γ1 m1 c a1 a2 → Γ1 ⊆ Γ2 → addr_compare_ok Γ2 m2 c a1 a2.
Proof. unfold addr_compare_ok; intuition eauto using addr_strict_weaken. Qed.
Lemma addr_compare_ok_erase Γ m c a1 a2 :
  addr_compare_ok Γ (cmap_erase m) c a1 a2 = addr_compare_ok Γ m c a1 a2.
Proof. unfold addr_compare_ok; by rewrite !index_alive_erase'. Qed.
Lemma addr_compare_weaken Γ1 Γ2 Δ1 a1 a2 c τp1 τp2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a1 : τp1 → (Γ1,Δ1) ⊢ a2 : τp2 →
  Γ1 ⊆ Γ2 → addr_compare Γ1 c a1 a2 = addr_compare Γ2 c a1 a2.
Proof.
  unfold addr_compare; intros;
    by erewrite ?(addr_object_offset_weaken Γ1 Γ2) by eauto.
Qed.
Lemma addr_plus_typed Γ Δ m a σp j :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_plus_ok Γ m j a →
  (Γ,Δ) ⊢ addr_plus Γ j a : σp.
Proof.
  destruct 2 as [o r i τ σ σp]; intros (?&?&?);
    constructor; simpl in *; split_and ?; auto.
  { apply Nat2Z.inj_le. by rewrite Nat2Z.inj_mul, Z2Nat.id by done. }
  rewrite <-(Nat2Z.id (ptr_size_of Γ σp)) at 1.
  rewrite Z2Nat_divide by auto with zpos.
  apply Z.divide_add_r; [by apply Nat2Z_divide|by apply Z.divide_mul_r].
Qed.
Lemma addr_plus_ok_weaken Γ1 Γ2 Δ1 m1 m2 a σp j :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a : σp → addr_plus_ok Γ1 m1 j a →
  Γ1 ⊆ Γ2 → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  addr_plus_ok Γ2 m2 j a.
Proof.
  unfold addr_plus_ok; intros ?? (?&?&?) ??; simplify_type_equality'.
  erewrite <-addr_size_of_weaken, <-(size_of_weaken _ Γ2)
    by eauto using addr_typed_type_base_valid; eauto.
Qed.
Lemma addr_plus_ok_erase Γ m a j:
  addr_plus_ok Γ (cmap_erase m) j a = addr_plus_ok Γ m j a.
Proof. unfold addr_plus_ok. by rewrite !index_alive_erase'. Qed.
Lemma addr_plus_weaken Γ1 Γ2 Δ1 a σp j :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a : σp → Γ1 ⊆ Γ2 → addr_plus Γ1 j a = addr_plus Γ2 j a.
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
Lemma addr_minus_typed Γ m a1 a2 :
  addr_minus_ok Γ m a1 a2 → int_typed (addr_minus Γ a1 a2) sptrT.
Proof. by intros (?&?&?&?). Qed. 
Lemma addr_minus_weaken Γ1 Γ2 Δ1 a1 a2 σp1 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a1 : σp1 →
  Γ1 ⊆ Γ2 → addr_minus Γ1 a1 a2 = addr_minus Γ2 a1 a2.
Proof.
  intros. unfold addr_minus; simplify_type_equality.
  by erewrite (addr_size_of_weaken Γ1 Γ2) by eauto.
Qed.
Lemma addr_minus_ok_weaken Γ1 Γ2 Δ1 m1 m2 a1 a2 σp1 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a1 : σp1 → addr_minus_ok Γ1 m1 a1 a2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  addr_minus_ok Γ2 m2 a1 a2.
Proof.
  intros ?? [??]; split; erewrite <-?(addr_minus_weaken Γ1 Γ2) by eauto; eauto.
Qed.
Lemma addr_minus_ok_erase Γ  m a1 a2 :
  addr_minus_ok Γ (cmap_erase m) a1 a2 = addr_minus_ok Γ m a1 a2.
Proof. unfold addr_minus_ok. by rewrite !index_alive_erase'. Qed.

Lemma addr_cast_typed Γ Δ m a σp τp :
  (Γ,Δ) ⊢ a : σp → addr_cast_ok Γ m τp a → (Γ,Δ) ⊢ addr_cast τp a : τp.
Proof. intros [] (?&?&?); constructor; eauto. Qed.
Lemma addr_cast_ok_weaken Γ1 Γ2 Δ1 m1 m2 a σp τp :
  ✓ Γ1 → (Γ1,Δ1) ⊢ a : σp →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  addr_cast_ok Γ1 m1 τp a → Γ1 ⊆ Γ2 → addr_cast_ok Γ2 m2 τp a.
Proof.
  intros ??? (?&?&?) ?; repeat split; auto. destruct τp as [τ| |]; simpl; auto.
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
Lemma addr_cast_self Γ Δ a σp : (Γ,Δ) ⊢ a : σp → addr_cast σp a = a.
Proof. by destruct 1. Qed.
Lemma addr_is_obj_cast a σp :
  addr_is_obj (addr_cast σp a) ↔ σp = TType (addr_type_base a).
Proof. by destruct a. Qed.
Lemma addr_ref_plus_char_cast Γ Δ a σp j :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_is_obj a → j < ptr_size_of Γ σp →
  addr_ref Γ (addr_plus Γ j (addr_cast (TType ucharT) a)) = addr_ref Γ a.
Proof.
  destruct 2 as [o r i τ σ σp ?????]; intros ??; simplify_equality'; f_equal.
  rewrite size_of_char, Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  symmetry. apply Nat.div_unique with (i `mod` size_of Γ σ + j).
  { by rewrite (λ x y H, proj2 (Nat.mod_divide x y H))
      by eauto using size_of_ne_0, ref_typed_type_valid. }
  by rewrite Nat.add_assoc, <-Nat.div_mod
    by eauto using ref_typed_type_valid, size_of_ne_0.
Qed.
Lemma addr_ref_byte_plus_char_cast Γ Δ a σp j :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_is_obj a → j < ptr_size_of Γ σp →
  addr_ref_byte Γ (addr_plus Γ j (addr_cast (TType ucharT) a)) = j.
Proof.
  destruct 2 as [o r i τ σ σp]; intros; simplify_equality'.
  rewrite size_of_char, Z.mul_1_r, Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  rewrite <-Nat.add_mod_idemp_l, (λ y H, proj2 (Nat.mod_divide i y H)),
    Nat.add_0_l by eauto using ref_typed_type_valid, size_of_ne_0.
  by apply Nat.mod_small.
Qed.
Lemma addr_byte_lt_size_char_cast Γ Δ a σp j :
  ✓ Γ → (Γ,Δ) ⊢ a : σp → addr_is_obj a → j < ptr_size_of Γ σp →
  addr_byte a < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a) →
  addr_byte (addr_plus Γ j (addr_cast (TType ucharT) a))
    < size_of Γ (addr_type_base a) * ref_size (addr_ref_base a).
Proof.
  destruct 2 as [o r i τ σ σp ????? Hi]; intros; simplify_equality'.
  rewrite size_of_char, Z.mul_1_r,Z2Nat.inj_add, !Nat2Z.id by auto with zpos.
  apply Nat.lt_le_trans with (i + size_of Γ σ); [lia|].
  destruct Hi as [? ->].
  rewrite <-Nat.mul_succ_l, Nat.mul_comm, <-Nat.mul_le_mono_pos_l,
    Nat.le_succ_l, (Nat.mul_lt_mono_pos_r (size_of Γ σ))
    by eauto using ref_typed_type_valid, size_of_pos; lia.
Qed.

(** ** Properties of operations on pointers *)
#[global] Instance ptr_alive_dec' m p : Decision (ptr_alive' m p).
Proof.
 refine
  match p with
  | Ptr a => decide (index_alive' m (addr_index a)) | _ => left _
  end; done.
Defined.
Lemma ptr_alive_weaken' m1 m2 p :
  ptr_alive' m1 p → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  ptr_alive' m2 p.
Proof. destruct p; simpl; auto. Qed.
Lemma ptr_alive_1' m p : ptr_alive' m p → ptr_alive '{m} p.
Proof. destruct p; simpl; eauto. Qed.
Hint Resolve ptr_alive_1': core.
Lemma ptr_alive_erase' m p : ptr_alive' (cmap_erase m) p = ptr_alive' m p.
Proof. unfold ptr_alive'. by destruct p; rewrite ?index_alive_erase'. Qed.
#[global] Instance ptr_compare_ok_dec Γ m c p1 p2 :
  Decision (ptr_compare_ok Γ m c p1 p2).
Proof. destruct p1, p2, c; apply _. Defined.
#[global] Instance ptr_plus_ok_dec Γ m j p : Decision (ptr_plus_ok Γ m j p).
Proof. destruct p; simpl; apply _. Defined.
#[global] Instance ptr_minus_ok_dec Γ m p1 p2 : Decision (ptr_minus_ok Γ m p1 p2).
Proof. destruct p1, p2; apply _. Defined.
#[global] Instance ptr_cast_ok_dec Γ m σp p : Decision (ptr_cast_ok Γ m σp p).
Proof. destruct p; apply _. Defined.

#[global] Instance ptr_cast_typed_dec τp σp : Decision (ptr_cast_typed τp σp).
Proof.
 refine
  match τp, σp with
  | (TType _|TAny), TAny | TAny, TType _ => left _
  | TType τ1, TType τ2 => cast_if (decide (τ1 = τ2 ∨ τ2 = ucharT ∨ τ1 = ucharT))
  | τs1 ~> τ1, τs2 ~> τ2 => cast_if_and (decide (τs1 = τs2)) (decide (τ1 = τ2))
  | _, _ => right _
  end%BT;
  abstract first [by intuition; subst; constructor |by inversion 1; intuition].
Defined.

Lemma ptr_plus_typed Γ Δ m p σp j :
  ✓ Γ → (Γ,Δ) ⊢ p : σp → ptr_plus_ok Γ m j p →
  (Γ,Δ) ⊢ ptr_plus Γ j p : σp.
Proof. destruct 2; simpl; constructor; eauto using addr_plus_typed. Qed.
Lemma ptr_minus_typed Γ m p1 p2 :
  ptr_minus_ok Γ m p1 p2 → int_typed (ptr_minus Γ p1 p2) sptrT.
Proof.
  destruct p1,p2; simpl; eauto using addr_minus_typed, int_typed_small with lia.
Qed.
Lemma ptr_cast_typed' Γ Δ m p τp σp :
  (Γ,Δ) ⊢ p : τp → ptr_cast_typed τp σp → ✓{Γ} σp →
  ptr_cast_ok Γ m σp p → (Γ,Δ) ⊢ ptr_cast σp p : σp.
Proof.
  destruct 1; inversion 1; intros; simplify_equality';
    constructor; eauto using addr_cast_typed.
Qed.
Lemma ptr_cast_typed_self τp : ptr_cast_typed τp τp.
Proof. destruct τp; constructor. Qed.

Lemma ptr_compare_ok_weaken Γ1 Γ2 Δ1 m1 m2 c p1 p2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p1 : τp1 → (Γ1,Δ1) ⊢ p2 : τp2 →
  ptr_compare_ok Γ1 m1 c p1 p2 →
  Γ1 ⊆ Γ2 → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  ptr_compare_ok Γ2 m2 c p1 p2.
Proof.
  destruct 2, 1; simpl; repeat case_match; eauto using addr_compare_ok_weaken.
Qed.
Lemma ptr_compare_ok_erase Γ m c p1 p2:
  ptr_compare_ok Γ (cmap_erase m) c p1 p2 = ptr_compare_ok Γ m c p1 p2.
Proof.
  unfold ptr_compare_ok.
  by destruct p1, p2; rewrite ?index_alive_erase', ?addr_compare_ok_erase.
Qed.
Lemma ptr_compare_weaken Γ1 Γ2 Δ1 c p1 p2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p1 : τp1 → (Γ1,Δ1) ⊢ p2 : τp2 →
  Γ1 ⊆ Γ2 → ptr_compare Γ1 c p1 p2 = ptr_compare Γ2 c p1 p2.
Proof. destruct 2, 1; simpl; intros; eauto 2 using addr_compare_weaken. Qed.
Lemma ptr_plus_ok_weaken Γ1 Γ2 Δ1 m1 m2 p τp j :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p : τp → ptr_plus_ok Γ1 m1 j p →
  Γ1 ⊆ Γ2 → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  ptr_plus_ok Γ2 m2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_ok_weaken. Qed.
Lemma ptr_plus_ok_erase Γ m j p :
  ptr_plus_ok Γ (cmap_erase m) j p = ptr_plus_ok Γ m j p.
Proof. destruct p; simpl; auto using addr_plus_ok_erase. Qed.
Lemma ptr_plus_weaken Γ1 Γ2 Δ1 p τp j :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p : τp → Γ1 ⊆ Γ2 → ptr_plus Γ1 j p = ptr_plus Γ2 j p.
Proof. destruct 2; simpl; eauto using addr_plus_weaken, f_equal. Qed.
Lemma ptr_minus_ok_weaken Γ1 Γ2 Δ1 m1 m2 p1 p2 τp1 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p1 : τp1 → ptr_minus_ok Γ1 m1 p1 p2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  ptr_minus_ok Γ2 m2 p1 p2.
Proof. destruct 2, p2; simpl; eauto using addr_minus_ok_weaken. Qed.
Lemma ptr_minus_ok_erase Γ m p1 p2 :
  ptr_minus_ok Γ (cmap_erase m) p1 p2 = ptr_minus_ok Γ m p1 p2.
Proof. destruct p1, p2; simpl; auto using addr_minus_ok_erase. Qed.
Lemma ptr_minus_weaken Γ1 Γ2 Δ1 p1 p2 τp1 τp2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p1 : τp1 → (Γ1,Δ1) ⊢ p2 : τp2 →
  Γ1 ⊆ Γ2 → ptr_minus Γ1 p1 p2 = ptr_minus Γ2 p1 p2.
Proof. destruct 2, 1; simpl; eauto using addr_minus_weaken. Qed.
Lemma ptr_cast_ok_weaken Γ1 Γ2 Δ1 m1 m2 p τp σp :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p : τp → ptr_cast_ok Γ1 m1 σp p → Γ1 ⊆ Γ2 →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  ptr_cast_ok Γ2 m2 σp p.
Proof. destruct 2; simpl; eauto using addr_cast_ok_weaken. Qed.
Lemma ptr_cast_ok_erase Γ m p τp :
  ptr_cast_ok Γ (cmap_erase m) τp p = ptr_cast_ok Γ m τp p.
Proof. destruct p; simpl; auto using addr_cast_ok_erase. Qed.
Lemma ptr_compare_ok_alive_l Γ m c p1 p2 :
  ptr_compare_ok Γ m c p1 p2 → ptr_alive '{m} p1.
Proof.
  destruct p1,p2,c; simpl; unfold addr_minus_ok, addr_compare_ok; naive_solver.
Qed.
Lemma ptr_compare_ok_alive_r Γ m c p1 p2 :
  ptr_compare_ok Γ m c p1 p2 → ptr_alive '{m} p2.
Proof.
  destruct p1 as [|[]|], p2 as [|[]|], c;
    csimpl; unfold addr_compare_ok; naive_solver.
Qed.
Lemma ptr_plus_ok_alive Γ m p j : ptr_plus_ok Γ m j p → ptr_alive '{m} p.
Proof. destruct p. done. intros [??]; simpl; eauto. done. Qed.
Lemma ptr_minus_ok_alive_l Γ m p1 p2 :
  ptr_minus_ok Γ m p1 p2 → ptr_alive '{m} p1.
Proof. destruct p1, p2; simpl; try done. intros [??]; eauto. Qed.
Lemma ptr_minus_ok_alive_r Γ m p1 p2 :
  ptr_minus_ok Γ m p1 p2 → ptr_alive '{m} p2.
Proof. destruct p1, p2; simpl; try done. intros (?&<-&?); eauto. Qed.
Lemma ptr_cast_ok_alive Γ m p σp : ptr_cast_ok Γ m σp p → ptr_alive '{m} p.
Proof. destruct p; simpl. done. intros [??]; eauto. done. Qed.

(** ** Properties of operations on base values *)
#[global] Instance base_val_branchable_dec m vb :
  Decision (base_val_branchable m vb).
Proof. destruct vb; apply _. Defined.
#[global] Instance base_val_is_0_dec vb : Decision (base_val_is_0 vb).
Proof.
 refine
  match vb with
  | VInt _ x => decide (x = 0) | VPtr (NULL _) => left _ | _ => right _
  end; abstract naive_solver.
Defined.
Lemma base_val_branchable_weaken m1 m2 vb :
  base_val_branchable m1 vb →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  base_val_branchable m2 vb.
Proof. destruct vb; simpl; eauto using ptr_alive_weaken'. Qed.
Lemma base_val_branchable_erase m vb :
  base_val_branchable (cmap_erase m) vb = base_val_branchable m vb.
Proof. by destruct vb; simpl; rewrite ?ptr_alive_erase'. Qed.
Lemma base_val_is_0_branchable m vb :
  base_val_is_0 vb → base_val_branchable m vb.
Proof. by destruct vb as [| | |[]|]. Qed.

#[global] Instance base_val_unop_ok_dec m op vb :
  Decision (base_val_unop_ok m op vb).
Proof. destruct vb, op; try apply _. Defined.
#[global] Instance base_val_binop_ok_dec Γ m op vb1 vb2 :
  Decision (base_val_binop_ok Γ m op vb1 vb2).
Proof.
  destruct vb1, vb2, op as [|op| |]; try apply _; destruct op; apply _.
Defined.
#[global] Instance base_val_cast_ok_dec Γ m σb vb :
  Decision (base_val_cast_ok Γ m σb vb).
Proof. destruct vb, σb; simpl; apply _. Defined.

Lemma base_unop_typed_type_valid Γ op τb σb :
  base_unop_typed op τb σb → ✓{Γ} τb → ✓{Γ} σb.
Proof. destruct 1; constructor. Qed.
Lemma base_binop_typed_type_valid Γ op τb1 τb2 σb :
  base_binop_typed op τb1 τb2 σb → ✓{Γ} τb1 → ✓{Γ} τb2 → ✓{Γ} σb.
Proof. destruct 1; eauto using TInt_valid. Qed.
Lemma base_unop_type_of_sound op τb σb :
  base_unop_type_of op τb = Some σb → base_unop_typed op τb σb.
Proof. destruct τb, op; intros; simplify_option_eq; constructor. Qed.
Lemma base_unop_type_of_complete op τb σb :
  base_unop_typed op τb σb → base_unop_type_of op τb = Some σb.
Proof. by destruct 1; simplify_option_eq. Qed.
Lemma base_binop_type_of_sound op τb1 τb2 σb :
  base_binop_type_of op τb1 τb2 = Some σb → base_binop_typed op τb1 τb2 σb.
Proof.
  destruct τb1, τb2, op; intros;
    repeat (case_match || simplify_option_eq); constructor.
Qed.
Lemma base_binop_type_of_complete op τb1 τb2 σb :
  base_binop_typed op τb1 τb2 σb → base_binop_type_of op τb1 τb2 = Some σb.
Proof. by destruct 1; simplify_option_eq; repeat case_match. Qed.
#[global] Instance base_cast_typed_dec τb σb: Decision (base_cast_typed τb σb).
Proof.
 refine
  match τb, σb with
  | _, voidT | intT _, intT _ => left _
  | τp1.*, τp2.* => cast_if (decide (ptr_cast_typed τp1 τp2))
  | _, _ => right _
  end%BT; abstract first [by constructor|by inversion 1].
Defined.

Lemma base_val_0_typed Γ Δ τb : ✓{Γ} τb → (Γ,Δ) ⊢ base_val_0 τb : τb.
Proof.
  destruct 1; simpl; constructor. by apply int_typed_small. by constructor.
Qed.
Lemma base_val_unop_ok_weaken m1 m2 op vb :
  base_val_unop_ok m1 op vb →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  base_val_unop_ok m2 op vb.
Proof. destruct vb, op; simpl; eauto using ptr_alive_weaken'. Qed.
Lemma base_val_unop_ok_erase m op vb :
  base_val_unop_ok (cmap_erase m) op vb = base_val_unop_ok m op vb.
Proof. destruct op, vb; simpl; auto using ptr_alive_erase'. Qed.
Lemma base_val_unop_typed Γ Δ m op vb τb σb :
  (Γ,Δ) ⊢ vb : τb → base_unop_typed op τb σb →
  base_val_unop_ok m op vb → (Γ,Δ) ⊢ base_val_unop op vb : σb.
Proof.
  unfold base_val_unop_ok, base_val_unop. intros Hvτb Hσ Hop.
  destruct Hσ; inversion Hvτb; simplify_equality'; try done.
  * typed_constructor. by apply int_unop_typed.
  * typed_constructor. by apply int_typed_small; case_match.
Qed.
Lemma base_val_binop_ok_weaken Γ1 Γ2 Δ1 m1 m2 op vb1 vb2 τb1 τb2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ vb1 : τb1 → (Γ1,Δ1) ⊢ vb2 : τb2 →
  base_val_binop_ok Γ1 m1 op vb1 vb2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
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
Lemma base_val_binop_weaken Γ1 Γ2 Δ1 op vb1 vb2 τb1 τb2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ vb1 : τb1 → (Γ1,Δ1) ⊢ vb2 : τb2 → Γ1 ⊆ Γ2 →
  base_val_binop Γ1 op vb1 vb2 = base_val_binop Γ2 op vb1 vb2.
Proof.
  destruct 2, 1, op as [|[]| |]; intros; f_equal';
    eauto 2 using ptr_plus_weaken, ptr_minus_weaken.
  by erewrite ptr_compare_weaken by eauto.
Qed.
Lemma base_val_binop_typed Γ Δ m op vb1 vb2 τb1 τb2 σb :
  ✓ Γ → (Γ,Δ) ⊢ vb1 : τb1 → (Γ,Δ) ⊢ vb2 : τb2 →
  base_binop_typed op τb1 τb2 σb → base_val_binop_ok Γ m op vb1 vb2 →
  (Γ,Δ) ⊢ base_val_binop Γ op vb1 vb2 : σb.
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
Lemma base_cast_typed_self τb : base_cast_typed τb τb.
Proof. destruct τb; constructor; auto using ptr_cast_typed_self. Qed.
Lemma base_val_cast_ok_weaken Γ1 Γ2 Δ1 m1 m2 vb τb σb :
  ✓ Γ1 → (Γ1,Δ1) ⊢ vb : τb → base_val_cast_ok Γ1 m1 σb vb →
  Γ1 ⊆ Γ2 → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  base_val_cast_ok Γ2 m2 σb vb.
Proof.
  destruct 2, σb; simpl; eauto using ptr_cast_ok_weaken, ptr_alive_weaken'.
Qed.
Lemma base_val_cast_ok_erase Γ m vb τb :
  base_val_cast_ok Γ (cmap_erase m) τb vb = base_val_cast_ok Γ m τb vb.
Proof.
  destruct vb, τb; simpl; auto using ptr_cast_ok_erase, ptr_alive_erase'.
Qed.
Lemma base_val_cast_typed Γ Δ m vb τb σb :
  ✓ Γ → (Γ,Δ) ⊢ vb : τb → base_cast_typed τb σb → ✓{Γ} σb →
  base_val_cast_ok Γ m σb vb → (Γ,Δ) ⊢ base_val_cast σb vb : σb.
Proof.
  unfold base_val_cast_ok, base_val_cast. intros ? Hvτb Hcast Hσb Hok.
  revert Hvτb.
  destruct Hcast; inversion 1; simplify_equality'; try (done || by constructor).
  * intuition; simplify_equality. by typed_constructor.
  * typed_constructor. by apply int_cast_typed.
  * typed_constructor; eauto using ptr_cast_typed', TPtr_valid_inv.
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
Lemma val_0_compound Γ c t τs :
  ✓ Γ → Γ !! t = Some τs → val_0 Γ (compoundT{c} t) =
    match c with
    | Struct_kind => VStruct t (val_0 Γ <$> τs)
    | Union_kind => VUnion t 0 (from_option (val_0 Γ) (VUnionAll t []) (τs !! 0))
    end.
Proof.
  intros HΓ Ht. unfold val_0; erewrite (type_iter_compound (=)); try done.
  { by intros ????? ->. }
  clear t τs Ht. intros ?? [] ? τs ?? Hgo; f_equal'; [|by destruct Hgo].
  by apply Forall_fmap_ext.
Qed.
Lemma val_0_weaken Γ1 Γ2 τ :
  ✓ Γ1 → ✓{Γ1} τ → Γ1 ⊆ Γ2 → val_0 Γ1 τ = val_0 Γ2 τ.
Proof.
  intros. apply (type_iter_weaken (=)); try done; [by intros ????? ->|].
  intros ?? [] ? τs ?? Hgo; f_equal'; [|by destruct Hgo].
  by apply Forall_fmap_ext.
Qed.
Lemma val_0_typed Γ Δ τ : ✓ Γ → ✓{Γ} τ → (Γ,Δ) ⊢ val_0 Γ τ : τ.
Proof.
  intros HΓ. revert τ. refine (type_env_ind _ HΓ _ _ _ _).
  * intros τb. rewrite val_0_base.
    typed_constructor; auto using base_val_0_typed.
  * intros τ n ???. rewrite val_0_array.
    typed_constructor; auto using replicate_length, Forall_replicate.
  * intros [] t τs Ht _ IH ?; erewrite val_0_compound by eauto.
    { typed_constructor; eauto. elim IH; csimpl; auto. }
    by destruct IH; simplify_equality'; typed_constructor; eauto.
Qed.

#[global] Instance val_unop_ok_dec m op v : Decision (val_unop_ok m op v).
Proof. destruct v; try apply _. Defined.
#[global] Instance val_binop_ok_dec Γ m op v1 v2 :
  Decision (val_binop_ok Γ m op v1 v2).
Proof. destruct v1, v2; apply _. Defined.
#[global] Instance val_cast_ok_dec Γ m σp v : Decision (val_cast_ok Γ m σp v).
Proof. destruct v, σp as [[[]| |]| |]; apply _. Defined.

Lemma unop_typed_type_valid Γ op τ σ : unop_typed op τ σ → ✓{Γ} τ → ✓{Γ} σ.
Proof.
  destruct 1; eauto using TBase_valid,
    TBase_valid_inv, base_unop_typed_type_valid.
Qed.
Lemma binop_typed_type_valid Γ op τ1 τ2 σ :
  binop_typed op τ1 τ2 σ → ✓{Γ} (TType τ1) → ✓{Γ} (TType τ2) → ✓{Γ} σ.
Proof.
  destruct 1; do 2 inversion 1;
    eauto using TBase_valid, base_binop_typed_type_valid.
Qed.
Lemma cast_typed_type_valid Γ τ σ :
  cast_typed τ σ → ✓{Γ} τ → ✓{Γ} (TType σ) → ✓{Γ} σ.
Proof. destruct 1; eauto using TBase_ptr_valid_inv, TBase_valid. Qed.
Lemma unop_type_of_sound op τ σ :
  unop_type_of op τ = Some σ → unop_typed op τ σ.
Proof.
  destruct τ; intros; simplify_option_eq; constructor.
  auto using base_unop_type_of_sound.
Qed.
Lemma unop_type_of_complete op τ σ :
  unop_typed op τ σ → unop_type_of op τ = Some σ.
Proof.
  destruct 1; simplify_option_eq.
  by erewrite base_unop_type_of_complete by eauto.
Qed.
Lemma binop_type_of_sound op τ1 τ2 σ :
  binop_type_of op τ1 τ2 = Some σ → binop_typed op τ1 τ2 σ.
Proof.
  destruct τ1, τ2; intros; simplify_option_eq; constructor.
  by apply base_binop_type_of_sound.
Qed.
Lemma binop_type_of_complete op τ1 τ2 σ :
  binop_typed op τ1 τ2 σ → binop_type_of op τ1 τ2 = Some σ.
Proof.
  destruct 1; simplify_option_eq.
  by erewrite base_binop_type_of_complete by eauto.
Qed.
#[global] Instance cast_typed_dec τ σ : Decision (cast_typed τ σ).
Proof.
 refine 
  match decide (τ = σ) with
  | left _ => left _
  | right Hτσ =>
    match τ, σ return τ ≠ σ → Decision (cast_typed τ σ) with
    | baseT τb, baseT σb => λ _, cast_if (decide (base_cast_typed τb σb))
    | _, baseT σb => λ _, cast_if (decide (σb = voidT%BT))
    | _, _ => λ _, right _
    end Hτσ
  end; abstract first
   [ by subst; constructor
   | by inversion 1; subst; eauto using base_cast_typed_self, TVoid_cast_typed].
Defined.
Lemma val_unop_ok_weaken m1 m2 op v :
  val_unop_ok m1 op v → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  val_unop_ok m2 op v.
Proof. unfold val_unop_ok; destruct v; eauto using base_val_unop_ok_weaken. Qed.
Lemma val_unop_ok_erase m op v :
  val_unop_ok (cmap_erase m) op v = val_unop_ok m op v.
Proof.
  unfold val_unop_ok; destruct v; simpl; auto using base_val_unop_ok_erase.
Qed.
Lemma val_unop_typed Γ Δ m op v τ σ :
  (Γ,Δ) ⊢ v : τ → unop_typed op τ σ → val_unop_ok m op v →
  (Γ,Δ) ⊢ val_unop op v : σ.
Proof.
  intros Hvτ Hσ Hop. destruct Hσ; inversion Hvτ; simpl; simplify_equality;
    done || constructor; eauto using base_val_unop_typed.
Qed.
Lemma val_binop_ok_weaken Γ1 Γ2 Δ1 m1 m2 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ v1 : τ1 → (Γ1,Δ1) ⊢ v2 : τ2 →
  val_binop_ok Γ1 m1 op v1 v2 → Γ1 ⊆ Γ2 →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  val_binop_ok Γ2 m2 op v1 v2.
Proof.
  destruct 2, 1, op; simpl; try done; eauto 2 using base_val_binop_ok_weaken.
Qed.
Lemma val_binop_ok_erase Γ m op v1 v2 :
  val_binop_ok Γ (cmap_erase m) op v1 v2 = val_binop_ok Γ m op v1 v2.
Proof.
  unfold val_binop_ok; destruct v1,v2; simpl;auto using base_val_binop_ok_erase.
Qed.
Lemma val_binop_weaken Γ1 Γ2 Δ1 op v1 v2 τ1 τ2 :
  ✓ Γ1 → (Γ1,Δ1) ⊢ v1 : τ1 → (Γ1,Δ1) ⊢ v2 : τ2 → Γ1 ⊆ Γ2 →
  val_binop Γ1 op v1 v2 = val_binop Γ2 op v1 v2.
Proof.
  destruct 2, 1, op; intros; f_equal'; eauto 2 using base_val_binop_weaken.
Qed.
Lemma val_binop_typed Γ Δ m op v1 v2 τ1 τ2 σ :
  ✓ Γ → (Γ,Δ) ⊢ v1 : τ1 → (Γ,Δ) ⊢ v2 : τ2 →
  binop_typed op τ1 τ2 σ → val_binop_ok Γ m op v1 v2 →
  (Γ,Δ) ⊢ val_binop Γ op v1 v2 : σ.
Proof.
  intros ? Hv1τ Hv2τ Hσ Hop.
  destruct Hσ; inversion Hv1τ; inversion Hv2τ; simplify_equality';
    done || constructor; eauto using base_val_binop_typed.
Qed.
Lemma val_cast_ok_weaken Γ1 Γ2 Δ1 m1 m2 v τ σ :
  ✓ Γ1 → (Γ1,Δ1) ⊢ v : τ → val_cast_ok Γ1 m1 (TType σ) v →
  Γ1 ⊆ Γ2 → (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  val_cast_ok Γ2 m2 (TType σ) v.
Proof. destruct 2, σ; simpl; eauto using base_val_cast_ok_weaken. Qed.
Lemma val_cast_ok_erase Γ m v τp :
  val_cast_ok Γ (cmap_erase m) τp v = val_cast_ok Γ m τp v.
Proof. destruct v, τp as [[]| |]; simpl; auto using base_val_cast_ok_erase. Qed.
Lemma val_cast_typed Γ Δ m v τ σ :
  ✓ Γ → (Γ,Δ) ⊢ v : τ → cast_typed τ σ → ✓{Γ} σ →
  val_cast_ok Γ m (TType σ) v → (Γ,Δ) ⊢ val_cast (TType σ) v : σ.
Proof.
  intros ? Hvτ Hcast Hσ Hok.
  destruct Hcast; inversion Hσ; inversion Hvτ; simplify_equality';
    repeat typed_constructor;
    eauto using base_val_cast_typed, TVoid_cast_typed, base_cast_typed_self.
Qed.
End operations.
