(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import nmap mapset segmented.
Require Export references.
Local Open Scope ctype_scope.

(** * Indexes into the memory *)
(** We define indexes into the memory as binary naturals and use the [Nmap]
implementation to obtain efficient finite maps and finite sets with these
indexes as keys. *)
Definition index := N.
Definition indexmap := Nmap.
Notation indexset := (mapset indexmap).

Instance index_dec: ∀ i1 i2 : index, Decision (i1 = i2) := decide_rel (=).
Instance index_fresh_`{FinCollection index C} : Fresh index C := _.
Instance index_fresh_spec `{FinCollection index C} : FreshSpec index C := _.
Instance index_inhabited: Inhabited index := populate 0%N.

Instance indexmap_dec {A} `{∀ a1 a2 : A, Decision (a1 = a2)} :
  ∀ m1 m2 : indexmap A, Decision (m1 = m2) := decide_rel (=).
Instance indexmap_empty {A} : Empty (indexmap A) := @empty (Nmap A) _.
Instance indexmap_lookup {A} : Lookup index A (indexmap A) :=
  @lookup _ _ (Nmap A) _.
Instance indexmap_partial_alter {A} : PartialAlter index A (indexmap A) :=
  @partial_alter _ _ (Nmap A) _.
Instance indexmap_to_list {A} : FinMapToList index A (indexmap A) :=
  @map_to_list _ _ (Nmap A) _.
Instance indexmap_merge: Merge indexmap := @merge Nmap _.
Instance indexmap_fmap: FMap indexmap := λ A B f, @fmap Nmap _ _ f _.
Instance: FinMap index indexmap := _.

Instance indexmap_dom {A} : Dom (indexmap A) indexset := mapset_dom.
Instance: FinMapDom index indexmap indexset := mapset_dom_spec.

Typeclasses Opaque index indexmap.

Class TypeOfIndex (Ti : Set) (M : Type) :=
  type_of_index : M → index → option (type Ti).

(** * Locked locations *)
(** In order to model sequence points, we have to keep track of sets of
locations that cannot be written to or read from. We call such locations locked,
and define a type class [Locks] to collect locks in various data structures. *)
Class Locks A := locks: A → indexset.
Arguments locks {_ _} !_ / : simpl nomatch.

Instance list_locks `{Locks A} : Locks (list A) :=
  fix go (l : list A) : indexset :=
  let _ : Locks _ := @go in
  match l with
  | [] => ∅
  | a :: l => locks a ∪ locks l
  end.

Lemma locks_nil `{Locks A} : locks [] = ∅.
Proof. done. Qed.
Lemma locks_app `{Locks A} (l1 l2 : list A) :
  locks (l1 ++ l2) = locks l1 ∪ locks l2.
Proof. apply elem_of_equiv_L. induction l1; esolve_elem_of. Qed.
Lemma locks_snoc `{Locks A} (l1 : list A) a :
  locks (l1 ++ [a]) = locks l1 ∪ locks a.
Proof. rewrite locks_app. simpl. by rewrite (right_id_L ∅ (∪)). Qed.

(** * Left values *)
Record lval := LVal { LIndex : index; LRef : bref }.
Add Printing Constructor lval.

Instance ref_eq_dec (r1 r2 : lval) : Decision (r1 = o2).
Proof. solve_decision. Defined.

Inductive lval_typed' `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M}
     (m : M) : lval → type Ti → Prop :=
  LVal_typed x r τ σ :
    type_of_index m x = Some τ → τ ∙ r ↝ σ → lval_typed' m (LVal x r) σ.
Instance lval_typed `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M} :
  Typed M (type Ti) lval := lval_typed'.

Instance lval_type_check `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M} :
    TypeCheck M (type Ti) lval := λ m lv,
  type_of_index m (LIndex lv) ≫= (!! LRef lv).
Arguments lval_type_check {_ _ _ _ _ _ _} !_ /.

Instance lval_frozen: Frozen lval := λ lv, frozen (LRef lv).
Instance lval_freeze: Freeze lval := λ lv,
  match lv with LVal x r => LVal x (freeze r) end.

Definition lval_base (lv : lval) : lval :=
  match lv with LVal x r => LVal x (bref_base r) end.
Definition lval_offset (lv : lval) : nat := bref_offset (LRef lv).
Arguments lval_offset !_ /.
Definition lval_size (lv : lval) : nat := bref_size (LRef lv).
Arguments lval_size !_ /.
Definition lval_plus (lv : lval) (j : Z) : option lval :=
  match lv with LVal x r => LVal x <$> bref_plus r j end.
Definition lval_minus (lv1 lv2 : lval) : option Z :=
  guard (LIndex lv1 = LIndex lv2); bref_minus (LRef lv1) (LRef lv2).
Arguments lval_minus !_ !_ /.

Inductive lval_disjoint: Disjoint lval :=
  | LVal_bref_disjoint x r1 r2 : r1 ⊥ r2 → LVal x r1 ⊥ LVal x r2
  | LVal_index_disjoint x1 x2 r1 r2 : x1 ≠ x2 → LVal x1 r1 ⊥ LVal x2 r2.
Existing Instance lval_disjoint.

Section lvals.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.
  Implicit Types lv : lval.
  Implicit Types m : M.
  Implicit Types τ : type Ti.

  Lemma lval_freeze_frozen lv : frozen (freeze lv).
  Proof. destruct lv. do 2 red. simpl. apply bref_freeze_frozen. Qed.
  Lemma lval_frozen_freeze lv : frozen lv → freeze lv = lv.
  Proof. destruct lv; simpl; intros; f_equal. by apply bref_frozen_freeze. Qed.
  Lemma lval_frozen_alt lv : frozen lv ↔ freeze lv = lv.
  Proof.
    split; intros E; eauto using lval_frozen_freeze.
    rewrite <-E. eauto using lval_freeze_frozen.
  Qed.
  Lemma lval_freeze_idempotent lv : freeze (freeze lv) = freeze lv.
  Proof. apply lval_frozen_freeze, lval_freeze_frozen. Qed.
  Global Instance: Commutative (↔) (@disjoint lval _).
  Proof. split; destruct 1; constructor (by rewrite (commutative _)). Qed.

  Section lval_typed.
    Context `{Hm: PropHolds (∀ m x τ,
      type_of_index m x = Some τ → τ = void ∨ type_valid get_env τ)}.

    Lemma lval_typed_type_valid m lv τ :
      m ⊢ lv : τ → τ = void ∨ type_valid get_env τ.
    Proof.
      destruct 1; eauto. edestruct Hm; eauto.
      * subst. edestruct bref_typed_void; eauto.
        subst. eauto using TBase_valid, TInt_valid.
      * eauto using bref_typed_type_valid.
    Qed.
    Lemma lval_typed_ptr_type_valid m lv τ :
      m ⊢ lv : τ → ptr_type_valid get_env τ.
    Proof.
      intros. destruct (lval_typed_type_valid m lv τ); subst;
        auto using TVoid_ptr_valid, type_valid_ptr_type_valid.
    Qed.
  End lval_typed.

  Global Instance: TypeCheckSpec M (type Ti) lval.
  Proof.
    intros m lv τ. split.
    * destruct lv; intros; repeat (simplify_option_equality || case_decide);
        econstructor; eauto using bref_lookup_sound.
    * destruct 1; repeat (simplify_option_equality || case_decide);
        auto using bref_lookup_complete.
  Qed.

  Lemma lval_typed_freeze m lv τ : m ⊢ freeze lv : τ ↔ m ⊢ lv : τ.
  Proof.
    split.
    * destruct lv; inversion_clear 1; econstructor; eauto.
      by apply bref_typed_freeze.
    * destruct 1; econstructor; eauto. by apply bref_typed_freeze.
  Qed.
  Lemma lval_type_check_freeze m lv :
    type_check m (freeze lv) = type_check m lv.
  Proof.
    apply option_eq. intros. by rewrite !type_check_correct, lval_typed_freeze.
  Qed.

  Lemma lval_disjoint_freeze_l lv1 lv2 : freeze lv1 ⊥ lv2 ↔ lv1 ⊥ lv2.
  Proof.
    split.
    * destruct lv1, lv2. inversion 1; subst.
      + by apply LVal_bref_disjoint, bref_disjoint_freeze_l.
      + by apply LVal_index_disjoint; rewrite <-1?bref_freeze_idempotent.
    * destruct 1.
      + by apply LVal_bref_disjoint, bref_disjoint_freeze_l.
      + by apply LVal_index_disjoint; rewrite ?bref_freeze_idempotent.
  Qed.
  Lemma lval_disjoint_freeze_r lv1 lv2 : lv1 ⊥ freeze lv2 ↔ lv1 ⊥ lv2.
  Proof. by rewrite !(commutative _ lv1), lval_disjoint_freeze_l. Qed.
  Lemma lval_disjoint_freeze lv1 lv2 : freeze lv1 ⊥ freeze lv2 ↔ lv1 ⊥ lv2.
  Proof. by rewrite lval_disjoint_freeze_l, lval_disjoint_freeze_r. Qed.

  Global Instance lval_frozen_dec lv : Decision (frozen lv).
  Proof. apply _. Defined.
  Global Instance lval_disjoint_dec lv1 lv2 : Decision (lv1 ⊥ lv2).
  Proof.
   refine (
    match lv1, lv2 with
    | LVal x1 r1, LVal x2 r2 =>
       cast_if_not_or (decide (x1 = x2)) (decide (r1 ⊥ r2))
    end); first [subst; by constructor | inversion 1; auto ].
  Defined.

  Lemma lval_base_idempotent lv : lval_base (lval_base lv) = lval_base lv.
  Proof. by destruct lv; simpl; rewrite bref_base_idempotent. Qed.
  Lemma lval_offset_base lv : lval_offset (lval_base lv) = 0.
  Proof. by destruct 0; simpl; rewrite bref_offset_base. Qed.
  Lemma lval_size_base lv : lval_size (lval_base lv) = lval_size lv.
  Proof. by destruct 0; simpl; rewrite bref_size_base. Qed.
  Lemma lval_size_same_base lv lv' :
    lval_base lv = lval_base lv' → lval_size lv = lval_size lv'.
  Proof.
    intros Ho. by rewrite <-(lval_size_base lv), <-(lval_size_base lv'), Ho.
  Qed.

  Lemma lval_eq lv1 lv2 :
    lval_base lv1 = lval_base lv2 → lval_offset lv1 = lval_offset lv2 →
    lv1 = lv2.
  Proof.
    destruct lv1, lv2; simpl; intros; simplify_equality; f_equal.
    by apply bref_eq.
  Qed.
  Lemma lval_typed_alt m lv τ : m ⊢ lv : τ ↔ m ⊢ lval_base lv : τ.
  Proof.
    pose proof bref_typed_alt. split.
    * destruct 1; simpl; repeat econstructor; naive_solver.
    * destruct lv; inversion 1; repeat econstructor; naive_solver.
  Qed.
  Lemma lval_base_typed m lv τ : m ⊢ lv : τ → m ⊢ lval_base lv : τ.
  Proof. rewrite lval_typed_alt. tauto. Qed.
  Lemma lval_offset_size lv : lval_offset lv < lval_size lv.
  Proof. apply bref_offset_size. Qed.
  Lemma lval_offset_size_alt lv : (lval_offset lv < lval_size lv)%Z.
  Proof. apply Nat2Z.inj_lt, lval_offset_size. Qed.

  Lemma lval_base_freeze lv : lval_base (freeze lv) = freeze (lval_base lv).
  Proof. destruct lv; simpl; f_equal; apply bref_base_freeze. Qed.
  Lemma lval_offset_freeze lv : lval_offset (freeze lv) = lval_offset lv.
  Proof. destruct lv; simpl. apply bref_offset_freeze. Qed.
  Lemma lval_size_freeze lv : lval_size (freeze lv) = lval_size lv.
  Proof. destruct lv; simpl. apply bref_size_freeze. Qed.
  Lemma lval_plus_freeze lv i :
    lval_plus (freeze lv) i = freeze <$> lval_plus lv i.
  Proof.
    destruct lv as [j r]; simpl. rewrite bref_plus_freeze.
    by destruct (bref_plus r i).
  Qed.
  Lemma lval_minus_freeze_l lv1 lv2 :
    lval_minus (freeze lv1) lv2 = lval_minus lv1 lv2.
  Proof. destruct lv1, lv2; simpl. by rewrite bref_minus_freeze_l. Qed.
  Lemma lval_minus_freeze_r lv1 lv2 :
    lval_minus lv1 (freeze lv2) = lval_minus lv1 lv2.
  Proof. destruct lv1, lv2; simpl. by rewrite bref_minus_freeze_r. Qed.
  Lemma lval_minus_freeze lv1 lv2 :
    lval_minus (freeze lv1) (freeze lv2) = lval_minus lv1 lv2.
  Proof. by rewrite lval_minus_freeze_l, lval_minus_freeze_r. Qed.

  Lemma lval_base_plus lv i lv' :
    lval_plus lv i = Some lv' → lval_base lv' = lval_base lv.
  Proof.
    intros. destruct lv; simplify_option_equality.
    eauto using bref_base_plus, f_equal.
  Qed.
  Lemma lval_size_plus lv i lv' :
    lval_plus lv i = Some lv' → lval_size lv' = lval_size lv.
  Proof.
    intros. destruct lv; simplify_option_equality.
    eauto using bref_size_plus.
  Qed.
  Lemma lval_offset_plus lv i lv' :
    lval_plus lv i = Some lv' →
    Z.of_nat (lval_offset lv') = (lval_offset lv + i)%Z.
  Proof.
    intros. destruct lv; simplify_option_equality. auto using bref_offset_plus.
  Qed.
  Lemma lval_offset_plus_range lv i lv' :
    lval_plus lv i = Some lv' → (0 ≤ lval_offset lv + i < lval_size lv)%Z.
  Proof.
    intros. rewrite <-(lval_offset_plus _ _ lv'), <-(lval_size_plus lv i lv');
      auto using lval_offset_size_alt with lia.
  Qed.
  Lemma lval_plus_is_Some lv i :
    is_Some (lval_plus lv i) ↔ (0 ≤ lval_offset lv + i < lval_size lv)%Z.
  Proof.
    rewrite is_Some_alt. split.
    * intros [??]. eauto using lval_offset_plus_range.
    * intros [??]. destruct lv as [y r]. simpl.
      feed inversion (proj2 (bref_plus_is_Some r i)); simpl; eauto.
  Qed.

  Lemma lval_plus_Some_2 lv i lv' :
    (0 ≤ lval_offset lv + i < lval_size lv)%Z → lval_base lv' = lval_base lv →
    Z.of_nat (lval_offset lv') = (lval_offset lv + i)%Z →
    lval_plus lv i = Some lv'.
  Proof.
    destruct lv, lv'; simpl. intros; simplify_equality.
    erewrite bref_plus_Some_2; try reflexivity; eauto.
  Qed.
  Lemma lval_plus_Some lv i lv' :
    lval_plus lv i = Some lv' ↔
      (0 ≤ lval_offset lv + i < lval_size lv)%Z ∧ lval_base lv' = lval_base lv ∧
      Z.of_nat (lval_offset lv') = (lval_offset lv + i)%Z.
  Proof.
    split.
    * eauto 6 using lval_base_plus, lval_offset_plus, lval_offset_plus_range.
    * intros [[??] [? Hi]]. eauto using lval_plus_Some_2.
  Qed.

  Lemma lval_plus_typed m lv τ i lv' :
    m ⊢ lv : τ → lval_plus lv i = Some lv' → m ⊢ lv' : τ.
  Proof.
    destruct 1; intros; simplify_option_equality;
      econstructor; eauto using bref_plus_typed.
  Qed.

  Lemma lval_plus_base_offset lv :
    lval_plus (lval_base lv) (lval_offset lv) = Some lv.
  Proof.
    apply lval_plus_Some_2.
    * rewrite lval_offset_base, lval_size_base.
      pose proof (lval_offset_size lv). lia.
    * by rewrite !lval_base_idempotent.
    * rewrite lval_offset_base. lia.
  Qed.

  Lemma lval_minus_Some lv1 lv2 j :
    lval_minus lv1 lv2 = Some j ↔
      lval_base (freeze lv1) = lval_base (freeze lv2) ∧
      j = (lval_offset lv1 - lval_offset lv2)%Z.
  Proof.
    destruct lv1, lv2.
    intuition (simplify_option_equality; eauto using f_equal,
      bref_minus_Some_base, bref_minus_Some_offset, bref_minus_Some_2).
  Qed.
  Lemma lval_minus_Some_2 lv1 lv2 j :
    lval_base (freeze lv1) = lval_base (freeze lv2) →
    j = (lval_offset lv1 - lval_offset lv2)%Z → lval_minus lv1 lv2 = Some j.
  Proof. by rewrite lval_minus_Some. Qed.
  Lemma lval_minus_Some_base lv1 lv2 j :
    lval_minus lv1 lv2 = Some j →
    lval_base (freeze lv1) = lval_base (freeze lv2).
  Proof. rewrite lval_minus_Some. tauto. Qed.
  Lemma lval_minus_Some_offset lv1 lv2 j :
    lval_minus lv1 lv2 = Some j → j = (lval_offset lv1 - lval_offset lv2)%Z.
  Proof. rewrite lval_minus_Some. tauto. Qed.
  Lemma lval_minus_plus lv1 lv2 i :
    lval_minus lv2 lv1 = Some i → lval_plus (freeze lv1) i = Some (freeze lv2).
  Proof.
    rewrite lval_minus_Some. intros [Ho ?]. subst. apply lval_plus_Some_2.
    * erewrite <-lval_size_same_base by eassumption.
      rewrite !lval_offset_freeze, !lval_size_freeze.
      pose proof (lval_offset_size_alt lv2). lia.
    * done.
    * rewrite !lval_offset_freeze. lia.
  Qed.
End lvals.

(** * Pointers *)
Inductive ptr Ti :=
  | NULL : type Ti → ptr Ti
  | Ptr : type Ti → index → ∀ r i, bref_base r = r → i ≤ bref_size r → ptr Ti.
Arguments NULL {_} _.
Arguments Ptr {_} _ _ _ _ _ _.

Lemma Ptr_eq {Ti : Set} `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}
    (τ1 : type Ti) x1 r1 i1 Hlv1 Hi1 τ2 x2 r2 i2 Hlv2 Hi2 :
  τ1 = τ2 → x1 = x2 → r1 = r2 → i1 = i2 →
  Ptr τ1 x1 r1 i1 Hlv1 Hi1 = Ptr τ2 x2 r2 i2 Hlv2 Hi2.
Proof. intros. simplify_equality. f_equal; apply (proof_irrel _). Qed.
Hint Extern 1 (Ptr _ _ _ _ _ _ = Ptr _ _ _ _ _ _) => apply Ptr_eq : f_equal.

Instance ptr_eq_dec {Ti : Set} `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}
  (p1 p2 : ptr Ti) : Decision (p1 = p2).
Proof.
 refine
  match p1, p2 with
  | NULL τ1, NULL τ2 => cast_if (decide (τ1 = τ2))
  | Ptr τ1 x1 r1 i1 _ _, Ptr τ2 x2 r2 i2 _ _ =>
     cast_if_and4 (decide (τ1 = τ2)) (decide (x1 = x2))
                  (decide (r1 = r2)) (decide (i1 = i2))
  | _, _ => right _
  end; abstract (auto with f_equal; try injection 1; congruence).
Defined.

Inductive ptr_cast `{PtrEnv Ti} : type Ti → type Ti → Prop :=
  | ptr_cast_refl τ : ptr_cast τ τ
  | ptr_cast_to_void τ : ptr_cast τ void.

Instance ptr_cast_dec `{IntEnv Ti Vi} `{PtrEnv Ti}
  (τ1 τ2 : type Ti) : Decision (ptr_cast τ1 τ2).
Proof.
 refine (cast_if_or (decide (τ2 = void)) (decide (τ1 = τ2)));
  abstract first [subst; by constructor | inversion 1; congruence ].
Defined.

Inductive ptr_typed' `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M}
     (m : M) : ptr Ti → type Ti → Prop :=
  | NULL_typed (τ : type Ti) :
     ptr_type_valid get_env τ →  ptr_typed' m (NULL τ) τ
  | Ptr_typed (τ τ' σ : type Ti) x r i Hlv Hi :
     type_of_index m x = Some τ →
     τ ∙ r ↝ τ' → ptr_cast τ' σ → ptr_typed' m (Ptr σ x r i Hlv Hi) σ.
Instance ptr_typed `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M} :
  Typed M (type Ti) (ptr Ti) := ptr_typed'.

Instance type_of_ptr {Ti} : TypeOf (type Ti) (ptr Ti) := λ p,
  match p with NULL τ => τ | Ptr τ _ _ _ _ _ => τ end.
Instance ptr_type_check `{IntEnv Ti Vi} `{PtrEnv Ti} `{TypeOfIndex Ti M} :
    TypeCheck M (type Ti) (ptr Ti) := λ m p,
  match p with
  | NULL τ => guard (ptr_type_valid get_env τ); Some τ
  | Ptr σ x r i _ _ =>
     τ' ← type_of_index m x ≫= (!! r);
     guard (ptr_cast τ' σ); Some σ
  end.

Lemma of_lval_prf r : bref_offset r ≤ bref_size (bref_base r).
Proof. rewrite bref_size_base. pose proof (bref_offset_size r). lia. Qed.
Definition of_lval {Ti} (τ : type Ti) (lv : lval) : ptr Ti :=
  match lv with
  | LVal x r => Ptr τ x (bref_base r) (bref_offset r)
                        (bref_base_idempotent _) (of_lval_prf _)
  end.

Definition to_lval {Ti} (p : ptr Ti) : option lval :=
  match p with
  | NULL _ => None
  | Ptr _ x r i _ _ => LVal x <$> bref_plus r i
  end.

Definition ptr_base {Ti} (p : ptr Ti) : ptr Ti :=
  match p with
  | NULL τ => NULL τ
  | Ptr τ x r i Hlv Hi => Ptr τ x r 0 Hlv (le_0_n _)
  end.
Definition ptr_offset {Ti} (p : ptr Ti) : nat :=
  match p with NULL _ => 0 | Ptr _ _ _ i _ _ => i end.
Definition ptr_size {Ti} (p : ptr Ti) : nat :=
  match p with NULL _ => 0 | Ptr _ _ r _ _ _ => bref_size r end.

Inductive is_NULL {Ti} : ptr Ti → Prop := mk_is_NULL τ : is_NULL (NULL τ).
Inductive ptr_frozen {Ti} : Frozen (ptr Ti) :=
  | NULL_frozen τ : frozen (@NULL Ti τ)
  | Pointer_frozen τ x r i Hlv Hi : frozen r → frozen (@Ptr Ti x τ r i Hlv Hi).
Existing Instance ptr_frozen.

Lemma ptr_freeze_prf_1 r : bref_base r = r → bref_base (freeze r) = freeze r.
Proof. intros Hr. by rewrite bref_base_freeze, Hr. Qed.
Lemma ptr_freeze_prf_2 i r : i ≤ bref_size r → i ≤ bref_size (freeze r).
Proof. by rewrite bref_size_freeze. Qed.
Instance ptr_freeze {Ti} : Freeze (ptr Ti) := λ p,
  match p with
  | NULL τ => NULL τ
  | Ptr τ x lv i Hlv Hi =>
     Ptr τ x (freeze lv) i (ptr_freeze_prf_1 _ Hlv) (ptr_freeze_prf_2 _ _ Hi)
  end.

Lemma ptr_plus_prf (i n : nat) (j : Z) :
  (0 ≤ i + j ≤ n)%Z → Z.to_nat (i + j) ≤ n.
Proof. intros. rewrite <-(Nat2Z.id n). apply Z2Nat.inj_le; lia. Qed.
Definition ptr_plus {Ti} (p : ptr Ti) (j : Z) : option (ptr Ti) :=
  match p with
  | NULL τ => guard (j = 0); Some (NULL τ)
  | Ptr τ x r i Hr _ =>
     guard (0 ≤ i + j ≤ bref_size r)%Z as H;
     Some (Ptr τ x r (Z.to_nat (i + j)) Hr (ptr_plus_prf _ _ _ H))
  end.
Definition ptr_minus {Ti} (p1 p2 : ptr Ti) : option Z :=
  match p1, p2 with
  | NULL _, NULL _ => Some 0
  | Ptr _ x1 r1 i1 _ _, Ptr _ x2 r2 i2 _ _ =>
     guard (x1 = x2);
     guard (freeze r1 = freeze r2);
     Some (i1 - i2)
  | _, _ => None
  end%Z.

Section ptr.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.
  Implicit Types p : ptr Ti.
  Implicit Types lv : lval.
  Implicit Types m : M.
  Implicit Types τ : type Ti.

  Context `{Hm : PropHolds (∀ m i τ,
    type_of_index m i = Some τ → type_valid get_env τ)}.

  Lemma ptr_freeze_frozen p : frozen (freeze p).
  Proof. destruct p; constructor; simpl; auto using bref_freeze_frozen. Qed.
  Lemma ptr_frozen_freeze p : frozen p → freeze p = p.
  Proof.
    destruct 1; simpl; auto. auto using bref_frozen_freeze with f_equal.
  Qed.
  Lemma ptr_freeze_idempotent p : freeze (freeze p) = freeze p.
  Proof. apply ptr_frozen_freeze, ptr_freeze_frozen. Qed.
  Lemma ptr_frozen_alt p : frozen p ↔ freeze p = p.
  Proof.
    split; intros E; eauto using ptr_frozen_freeze.
    rewrite <-E. eauto using ptr_freeze_frozen.
  Qed.

  Lemma ptr_cast_type_valid τ σ :
    ptr_type_valid get_env τ → ptr_cast τ σ → ptr_type_valid get_env σ.
  Proof. destruct 2; eauto. constructor. Qed.

  Lemma ptr_typed_type_valid m p τ : m ⊢ p : τ → ptr_type_valid get_env τ.
  Proof.
    destruct 1; eauto using TVoid_ptr_valid.
    eapply ptr_cast_type_valid; eauto.
    eapply type_valid_ptr_type_valid, bref_typed_type_valid; eauto.
  Qed.

  Global Instance: TypeCheckSpec M (type Ti) (ptr Ti).
  Proof.
    intros m p τ. split.
    * destruct p; intros; repeat (simplify_option_equality || case_match);
        econstructor (by eauto using bref_lookup_sound).
    * by destruct 1; repeat (simplify_option_equality || case_match);
        erewrite ?bref_lookup_complete by eauto; simplify_option_equality.
  Qed.
  Global Instance: TypeOfSpec M (type Ti) (ptr Ti).
  Proof. by destruct 1. Qed.

  Lemma ptr_typed_freeze m p τ : m ⊢ freeze p : τ ↔ m ⊢ p : τ.
  Proof.
    split.
    * destruct p; inversion_clear 1; try (by constructor).
      eapply Ptr_typed; eauto. by apply bref_typed_freeze.
    * destruct 1; try (by constructor).
      eapply Ptr_typed; eauto. by apply bref_typed_freeze.
  Qed.
  Lemma ptr_type_check_freeze m p : type_check m (freeze p) = type_check m p.
  Proof.
    apply option_eq. intros. by rewrite !type_check_correct, ptr_typed_freeze.
  Qed.
  Lemma ptr_freeze_type_of p : type_of (freeze p) = type_of p.
  Proof. by destruct p. Qed.

  Global Instance ptr_frozen_dec p : Decision (ptr_frozen p).
  Proof.
   refine (
    match p with
    | NULL _ => left _
    | Ptr _ _ r _ _ _ => cast_if (decide (frozen r))
    end); first [by constructor | abstract by inversion 1].
  Defined.

  Lemma ptr_base_idempotent p : ptr_base (ptr_base p) = ptr_base p.
  Proof. by destruct p. Qed.
  Lemma ptr_offset_base p : ptr_offset (ptr_base p) = 0.
  Proof. by destruct p. Qed.
  Lemma ptr_offset_base_alt p : ptr_base p = p → ptr_offset p = 0.
  Proof. intros Hp. by rewrite <-Hp, ptr_offset_base. Qed.
  Lemma ptr_size_base p : ptr_size (ptr_base p) = ptr_size p.
  Proof. by destruct p. Qed.
  Lemma ptr_size_same_base p p' :
    ptr_base p = ptr_base p' → ptr_size p = ptr_size p'.
  Proof.
    intros Hp. by rewrite <-(ptr_size_base p), <-(ptr_size_base p'), Hp.
  Qed.

  Lemma ptr_eq p1 p2 :
    type_of p1 = type_of p2 → ptr_base p1 = ptr_base p2 →
    ptr_offset p1 = ptr_offset p2 → p1 = p2.
  Proof.
    destruct p1, p2; simpl; intros; simplify_equality; eauto with f_equal.
  Qed.

  Lemma ptr_base_typed (m : M) p τ : m ⊢ p : τ → m ⊢ ptr_base p : τ.
  Proof. destruct 1; econstructor (by eauto). Qed.
  Lemma ptr_offset_size p : ptr_offset p ≤ ptr_size p.
  Proof. destruct p; simpl; lia. Qed.
  Lemma ptr_offset_size_alt p : (ptr_offset p ≤ ptr_size p)%Z.
  Proof. apply Nat2Z.inj_le, ptr_offset_size. Qed.

  Lemma ptr_base_freeze p : ptr_base (freeze p) = freeze (ptr_base p).
  Proof. destruct p; simpl; rewrite ?lval_base_freeze; auto with f_equal. Qed.
  Lemma ptr_offset_freeze p : ptr_offset (freeze p) = ptr_offset p.
  Proof. by destruct p. Qed.
  Lemma ptr_size_freeze p : ptr_size (freeze p) = ptr_size p.
  Proof. by destruct p; simpl; rewrite ?bref_size_freeze. Qed.
  Lemma ptr_plus_freeze p i : ptr_plus (freeze p) i = freeze <$> ptr_plus p i.
  Proof.
    destruct p; simplify_option_equality;
      eauto with f_equal; exfalso; by rewrite ?bref_size_freeze in *.
  Qed.
  Lemma ptr_minus_freeze_l p1 p2 : ptr_minus (freeze p1) p2 = ptr_minus p1 p2.
  Proof.
    by destruct p1, p2; simplify_option_equality;
      rewrite ?bref_freeze_idempotent in *.
  Qed.
  Lemma ptr_minus_freeze_r p1 p2 : ptr_minus p1 (freeze p2) = ptr_minus p1 p2.
  Proof.
    by destruct p1, p2; simplify_option_equality;
      rewrite ?bref_freeze_idempotent in *.
  Qed.

  Lemma ptr_minus_freeze p1 p2 :
    ptr_minus (freeze p1) (freeze p2) = ptr_minus p1 p2.
  Proof. by rewrite ptr_minus_freeze_l, ptr_minus_freeze_r. Qed.

  Lemma ptr_base_plus p i p' :
    ptr_plus p i = Some p' →  ptr_base p' = ptr_base p.
  Proof. intros. by destruct p; simplify_option_equality. Qed.
  Lemma ptr_size_plus p i p' :
    ptr_plus p i = Some p' → ptr_size p' = ptr_size p.
  Proof. intros. by destruct p; simplify_option_equality. Qed.

  Lemma ptr_offset_plus p i p' :
    ptr_plus p i = Some p' → Z.of_nat (ptr_offset p') = (ptr_offset p + i)%Z.
  Proof.
    intros. destruct p; simplify_option_equality; rewrite ?Z2Nat.id; intuition.
  Qed.
  Lemma ptr_offset_plus_range p i p' :
    ptr_plus p i = Some p' → (0 ≤ ptr_offset p + i ≤ ptr_size p)%Z.
  Proof.
    intros. rewrite <-(ptr_offset_plus _ _ p'), <-(ptr_size_plus p i p');
      auto using ptr_offset_size_alt with lia.
  Qed.
  Lemma ptr_plus_is_Some p i :
    is_Some (ptr_plus p i) ↔ (0 ≤ ptr_offset p + i ≤ ptr_size p)%Z.
  Proof.
    rewrite is_Some_alt. split.
    { intros [??]. eauto using ptr_offset_plus_range. }
    intros [??]. destruct p; simplify_option_equality; eauto with lia.
  Qed.

  Lemma ptr_plus_Some_2 p i p' :
    (0 ≤ ptr_offset p + i ≤ ptr_size p)%Z → ptr_base p = ptr_base p' →
    Z.of_nat (ptr_offset p') = (ptr_offset p + i)%Z → ptr_plus p i = Some p'.
  Proof.
    intros [??] ??. destruct p, p'; simplify_option_equality.
    * done.
    * f_equal; apply Ptr_eq; auto. apply Nat2Z.inj. rewrite Z2Nat.id; lia.
    * lia.
  Qed.
  Lemma ptr_plus_Some p i p' :
    ptr_plus p i = Some p' ↔
      (0 ≤ ptr_offset p + i ≤ ptr_size p)%Z ∧ ptr_base p' = ptr_base p ∧
      Z.of_nat (ptr_offset p') = (ptr_offset p + i)%Z.
  Proof.
    split.
    * eauto 6 using ptr_base_plus, ptr_offset_plus, ptr_offset_plus_range.
    * intros [[??] [??]]. eauto using ptr_plus_Some_2.
  Qed.

  Lemma ptr_plus_typed m p τ i p' :
    m ⊢ p : τ → ptr_plus p i = Some p' → m ⊢ p' : τ.
  Proof.
    destruct 1; intros; simplify_option_equality; econstructor (by eauto).
  Qed.

  Lemma ptr_plus_base_offset p :
    ptr_plus (ptr_base p) (ptr_offset p) = Some p.
  Proof.
    apply ptr_plus_Some_2.
    * rewrite ptr_offset_base, ptr_size_base.
      pose proof (ptr_offset_size p). lia.
    * by rewrite !ptr_base_idempotent.
    * rewrite ptr_offset_base. lia.
  Qed.

  Lemma ptr_minus_Some_2 p1 p2 j :
    ptr_base (freeze p1) = ptr_base (freeze p2) →
    j = (ptr_offset p1 - ptr_offset p2)%Z → ptr_minus p1 p2 = Some j.
  Proof. intros. by destruct p1, p2; simplify_option_equality. Qed.
  Lemma ptr_minus_Some_base p1 p2 j :
    ptr_minus p1 p2 = Some j → type_of p1 = type_of p2 →
    ptr_base (freeze p1) = ptr_base (freeze p2).
  Proof.
    destruct p1, p2; intros; simplify_option_equality; eauto with f_equal.
  Qed.
  Lemma ptr_minus_Some_offset p1 p2 j :
    ptr_minus p1 p2 = Some j →  j = (ptr_offset p1 - ptr_offset p2)%Z.
  Proof. by destruct p1, p2; intros; simplify_option_equality. Qed.
  Lemma ptr_minus_Some p1 p2 j :
    type_of p1 = type_of p2 → ptr_minus p1 p2 = Some j ↔
      ptr_base (freeze p1) = ptr_base (freeze p2) ∧
      j = (ptr_offset p1 - ptr_offset p2)%Z.
  Proof.
    intuition eauto using ptr_minus_Some_2,
      ptr_minus_Some_base, ptr_minus_Some_offset.
  Qed.
  Lemma ptr_minus_plus p1 p2 i :
    ptr_minus p2 p1 = Some i → type_of p1 = type_of p2 →
    ptr_plus (freeze p1) i = Some (freeze p2).
  Proof.
    intros Hlv ?. rewrite ptr_minus_Some in Hlv.
    destruct Hlv; subst. apply ptr_plus_Some_2.
    * erewrite <-ptr_size_same_base by eassumption.
      rewrite !ptr_offset_freeze, !ptr_size_freeze.
      pose proof (ptr_offset_size_alt p2). lia.
    * done.
    * rewrite !ptr_offset_freeze. lia.
    * done.
  Qed.

  Lemma to_lval_Some p : is_Some (to_lval p) ∨ ptr_offset p = ptr_size p.
  Proof.
    destruct p as [|τ x r i n Hlv]; simpl; auto.
    destruct (decide (i = bref_size r)); auto.
    rewrite fmap_is_Some, bref_plus_is_Some, bref_offset_base_alt by done. lia.
  Qed.

  Lemma to_of_lval τ lv : to_lval (of_lval τ lv) = Some lv.
  Proof.
    destruct lv; simplify_option_equality. by rewrite bref_plus_base_offset.
  Qed.

  Lemma of_to_lval p lv : to_lval p = Some lv → of_lval (type_of p) lv = p.
  Proof.
    unfold to_lval, of_lval. intros.
    destruct p as [|? lv' i n]; simplify_option_equality. apply Ptr_eq; auto.
    * erewrite bref_base_plus; eauto.
    * apply Nat2Z.inj. erewrite bref_offset_plus by eauto.
      rewrite bref_offset_base_alt by done. lia.
  Qed.
  Lemma type_of_of_lval τ lv : type_of (of_lval τ lv) = τ.
  Proof. by destruct lv. Qed.
  Global Instance: ∀ τ, Injective (=) (=) (of_lval τ).
  Proof.
    intros ? [??] [??]. injection 1; intros; subst.
    eapply lval_eq; simpl; eauto with congruence.
 Qed.

  Lemma of_lval_base τ lv : ptr_base (of_lval τ lv) = of_lval τ (lval_base lv).
  Proof.
    destruct lv; simpl. apply Ptr_eq; auto.
    * by rewrite bref_base_idempotent.
    * by rewrite bref_offset_base.
  Qed.
  Lemma of_lval_offset τ lv : ptr_offset (of_lval τ lv) = lval_offset lv.
  Proof. by destruct lv. Qed.
  Lemma of_lval_size τ lv : ptr_size (of_lval τ lv) = lval_size lv.
  Proof. destruct lv; simpl. by rewrite bref_size_base. Qed.
  Lemma of_lval_freeze τ lv : freeze (of_lval τ lv) = of_lval τ (freeze lv).
  Proof.
    destruct lv; simpl. apply Ptr_eq; auto.
    * by rewrite bref_base_freeze.
    * by rewrite bref_offset_freeze.
  Qed.
  Lemma of_lval_frozen τ lv : frozen (of_lval τ lv) ↔ frozen lv.
  Proof.
    rewrite ptr_frozen_alt, lval_frozen_alt, of_lval_freeze.
    split. apply (injective _). congruence.
  Qed.

  Global Instance is_NULL_dec p : Decision (is_NULL p).
  Proof.
   refine (match p with NULL _ => left _ | _ => right _ end);
     first [by constructor | abstract by inversion 1].
  Defined.
End ptr.

Definition frozen_ptr (Ti : Set) := dsig (@frozen (ptr Ti) _).
Definition mk_frozen_ptr {Ti} (p : ptr Ti) : frozen_ptr Ti :=
  dexist _ (ptr_freeze_frozen p).
Notation ptr_seg Ti := (segment (frozen_ptr Ti)).

Definition ptr_seg_valid `{PtrEnv Ti} `{IntEnv Ti Vi}
    `{TypeOfIndex Ti M} (m : M) (ps : ptr_seg Ti) : Prop :=
  ∃ τ, m ⊢ proj1_sig (segment_item ps) : τ.

Definition to_ptr_segs `{PtrEnv Ti} (p : ptr Ti) : list (ptr_seg Ti) :=
  to_segments (size_of (type_of p.*)) (mk_frozen_ptr p).
Definition of_ptr_segs `{PtrEnv Ti} `{IntEnv Ti Vi} (τ : type Ti)
    (pps : list (ptr_seg Ti)) : option (ptr Ti) :=
  p ← of_segments (size_of (τ.*)) pps;
  guard (type_of (`p) = τ);
  Some (`p).

Section ptr_segs.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.
  Implicit Types m : M.
  Implicit Types τ : type Ti.
  Implicit Types p : ptr Ti.
  Implicit Types q : frozen_ptr Ti.
  Implicit Types ps : ptr_seg Ti.

  Global Instance ptr_seg_valid_dec m ps : Decision (ptr_seg_valid m ps).
  Proof.
   refine
    match Some_dec (type_check m (proj1_sig (segment_item ps))) with
    | inleft (τ↾Hτ) => left _
    | inright Hτ => right _
    end.
    * abstract (rewrite type_check_correct in Hτ; econstructor; eauto).
    * abstract (inversion 1; eapply type_check_None in Hτ; eauto).
  Defined.

  Lemma frozen_ptr_frozen q : frozen (`q).
  Proof. apply proj2_dsig. Qed.
  Lemma mk_frozen_ptr_inj p1 p2 :
    mk_frozen_ptr p1 = mk_frozen_ptr p2 → freeze p1 = freeze p2.
  Proof. intros Heq. by apply dsig_eq in Heq. Qed.
  Lemma mk_frozen_ptr_proj1 q : mk_frozen_ptr (`q) = q.
  Proof.
    apply dsig_eq. simpl.
    rewrite ptr_frozen_freeze; auto using frozen_ptr_frozen.
  Qed.
  Lemma mk_frozen_ptr_freeze p : mk_frozen_ptr (freeze p) = mk_frozen_ptr p.
  Proof. apply dsig_eq. simpl. apply ptr_freeze_idempotent. Qed.

  Lemma to_ptr_segs_freeze p : to_ptr_segs (freeze p) = to_ptr_segs p.
  Proof.
    unfold to_ptr_segs. by rewrite mk_frozen_ptr_freeze, ptr_freeze_type_of.
  Qed.
  Lemma to_ptr_segs_inj p1 p2 :
    type_of p1 = type_of p2 → to_ptr_segs p1 = to_ptr_segs p2 →
    freeze p1 = freeze p2.
  Proof.
    unfold to_ptr_segs. simpl. intros Htype E.
    apply mk_frozen_ptr_inj. revert E. rewrite Htype. apply (injective _).
  Qed.
  Lemma to_ptr_segs_length p : length (to_ptr_segs p) = size_of (type_of p.*).
  Proof. unfold to_ptr_segs. by rewrite (to_segments_length _). Qed.

  Lemma of_ptr_segs_frozen p τ pss : of_ptr_segs τ pss = Some p → frozen p.
  Proof.
    unfold of_ptr_segs. intros. destruct pss as [|[]];
      repeat (simplify_option_equality || case_match);
      auto using frozen_ptr_frozen.
  Qed.
  Lemma of_ptr_segs_type_of p τ pss :
    of_ptr_segs τ pss = Some p → τ = type_of p.
  Proof. unfold of_ptr_segs. intros. by simplify_option_equality. Qed.
  Lemma to_of_ptr_segs p τ pss :
    of_ptr_segs τ pss = Some p → to_ptr_segs p = pss.
  Proof.
    intros. feed pose proof (of_ptr_segs_frozen p τ pss); trivial.
    unfold of_ptr_segs, to_ptr_segs in *. simplify_option_equality.
    by rewrite mk_frozen_ptr_proj1, (of_to_segments_1 _ _ pss).
  Qed.
  Lemma of_to_ptr_segs p :
    of_ptr_segs (type_of p) (to_ptr_segs p) = Some (freeze p).
  Proof.
    unfold of_ptr_segs, to_ptr_segs. rewrite (of_to_segments_2 _).
    simpl. rewrite ptr_freeze_type_of. by simplify_option_equality.
  Qed.

  Lemma to_ptr_segs_valid m p τ :
    m ⊢ p : τ → Forall (ptr_seg_valid m) (to_ptr_segs p).
  Proof.
    intros. apply (Forall_to_segments _ (λ q, ∃ τ, m ⊢ `q : τ)).
    exists τ. by apply ptr_typed_freeze.
  Qed.

  Lemma of_ptr_segs_typed m p τ pss :
    of_ptr_segs τ pss = Some p → Forall (ptr_seg_valid m) pss → m ⊢ p : τ.
  Proof.
    unfold of_ptr_segs. intros.
    destruct (of_segments _ _) as [q|] eqn:?; simplify_option_equality.
    destruct (Forall_of_segments (size_of (type_of (`q).*))
      (λ q, ∃ τ, m ⊢ `q : τ) q pss); eauto using type_of_typed.
  Qed.
End ptr_segs.
