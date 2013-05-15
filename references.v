(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export abstract_integers types.
Local Open Scope ctype_scope.

(** * Pointers environments *)
Section env.
Local Unset Elimination Schemes.

Class PtrEnv (Ti : Set) := {
  get_env : env Ti;
  size_of : type Ti → nat;
  struct_fields : list (type Ti) → list nat
}.

Class EnvSpec (Ti Vi : Set) `{IntEnv Ti Vi} `{PtrEnv Ti} := {
  int_env_spec :>> IntEnvSpec Ti Vi;
  get_env_valid :> EnvValid get_env;
  size_of_base_ne_0 τ : size_of (base τ) ≠ 0;
  size_of_int τ : size_of (intt τ) = int_type_size τ;
  size_of_array τ n : size_of (τ.[n]) = n * size_of τ;
  size_of_struct s τs :
    get_env !! s = Some τs → size_of (struct s) = sum_list (struct_fields τs);
  size_of_struct_fields τs :
    Forall2 (λ τ sz, size_of τ ≤ sz) τs (struct_fields τs);
  size_of_union s τs :
    get_env !! s = Some τs → Forall (λ τ, size_of τ ≤ size_of (union s)) τs
}.
End env.

Section env_spec.
  Context `{EnvSpec Ti Vi}.

  Definition struct_offset (τs : list (type Ti))
    (i : nat) : nat := sum_list $ take i $ struct_fields τs.

  Lemma size_of_union_lookup s τs i τ :
    get_env !! s = Some τs → τs !! i = Some τ → size_of τ ≤ size_of (union s).
  Proof.
    intros. assert (Forall (λ τ, size_of τ ≤ size_of (union s)) τs) as Hτs
      by eauto using size_of_union.
    rewrite Forall_lookup in Hτs. eauto.
  Qed.
  Lemma size_of_union_singleton s τ :
    get_env !! s = Some [τ] → size_of τ ≤ size_of (union s).
  Proof. intros. by apply (size_of_union_lookup s [τ] 0). Qed.

  Lemma struct_fields_same_length τs : τs `same_length` struct_fields τs.
  Proof. eauto using Forall2_same_length, size_of_struct_fields. Qed.

  Global Instance: ∀ τ, PropHolds (size_of (base τ) ≠ 0).
  Proof. apply size_of_base_ne_0. Qed.
  Lemma size_of_ne_0 τ : type_valid get_env τ → size_of τ ≠ 0.
  Proof.
    revert τ. refine (type_env_ind _ _ _ _).
    * auto using size_of_base_ne_0.
    * intros. rewrite size_of_array. by apply NPeano.Nat.neq_mul_0.
    * intros [] s τs Hs Hτs Hsz Hlen.
      + erewrite size_of_struct by eauto.
        clear Hs. induction (size_of_struct_fields τs);
          simpl; decompose_Forall; auto with lia.
      + apply size_of_union in Hs.
        destruct Hs; decompose_Forall; auto with lia.
  Qed.
  Lemma size_of_pos τ : type_valid get_env τ → 0 < size_of τ.
  Proof. intros. by apply NPeano.Nat.neq_0_lt_0, size_of_ne_0. Qed.
End env_spec.

(** * References *)
Inductive ref_seg :=
  | RArray : ∀ i n, i < n → ref_seg
  | RStruct : nat → ref_seg
  | RUnion : nat → bool → ref_seg.
Notation ref := (list ref_seg).

Lemma RArray_eq i1 n1 Hi1 i2 n2 Hi2 :
  i1 = i2 → n1 = n2 → RArray i1 n1 Hi1 = RArray i2 n2 Hi2.
Proof. intros. subst. f_equal. apply (proof_irrel _). Qed.
Hint Resolve RArray_eq : f_equal.

Instance ref_seg_eq_dec (r1 r2 : ref_seg) : Decision (r1 = r2).
Proof.
 refine
  match r1, r2 with
  | RArray i1 n1 _, RArray i2 n2 _ =>
     cast_if_and (decide (i1 = i2)) (decide (n1 = n2))
  | RStruct i1, RStruct i2 => cast_if (decide (i1 = i2))
  | RUnion i1 b1, RUnion i2 b2 =>
     cast_if_and (decide (i1 = i2)) (decide (b1 = b2))
  | _, _ => right _
  end; abstract (auto with f_equal; try injection 1; congruence).
Defined.

Inductive ref_seg_typed `{PtrEnv Ti} : PathTyped (type Ti) ref_seg :=
  | RArray_typed τ i n Hi : τ.[n] ∙ RArray i n Hi ↝ τ
  | RStruct_typed s i τs τ :
     get_env !! s = Some τs → τs !! i = Some τ → struct s ∙ RStruct i ↝ τ
  | RUnion_typed s i b τs τ :
     get_env !! s = Some τs → τs !! i = Some τ → union s ∙ RUnion i b ↝ τ.
Existing Instance ref_seg_typed.
Inductive ref_typed `{PtrEnv Ti} : PathTyped (type Ti) ref :=
  | ref_nil_2 τ : τ ∙ [] ↝ τ
  | ref_typed_cons_2 (r : ref) (rs : ref_seg) τ1 τ2 τ3 :
     τ2 ∙ rs ↝ τ3 → τ1 ∙ r ↝ τ2 → τ1 ∙ rs :: r ↝ τ3.
Existing Instance ref_typed.

Instance ref_seg_lookup `{PtrEnv Ti} :
    Lookup ref_seg (type Ti) (type Ti) := λ rs τ,
  match rs, τ with
  | RArray i n' _, τ.[n] => guard (n = n'); Some τ
  | RStruct i, struct s => get_env !! s ≫= (!! i)
  | RUnion i _, union s => get_env !! s ≫= (!! i)
  | _, _ => None
  end.
Instance ref_lookup `{PtrEnv Ti} : Lookup ref (type Ti) (type Ti) :=
  fix go r τ :=
  match r with
  | [] => Some τ
  | rs :: r => @lookup _ _ _ go r τ ≫= ref_seg_lookup rs
  end.

Class Frozen A := frozen: A → Prop.
Class Freeze A := freeze: A → A.
Arguments freeze {_ _} !_ / : simpl nomatch.

Inductive ref_seg_frozen: Frozen ref_seg :=
  | RArray_frozen i n Hi : frozen (RArray i n Hi)
  | RStruct_frozen i : frozen (RStruct i)
  | RUnion_frozen i : frozen (RUnion i false).
Existing Instance ref_seg_frozen.

Instance ref_seg_freeze: Freeze ref_seg:= λ rs,
  match rs with
  | RArray i n Hi => RArray i n Hi
  | RStruct i => RStruct i
  | RUnion i _ => RUnion i false
  end.

Lemma ref_base_prf i n : i < n → 0 < n.
Proof. lia. Qed.
Definition ref_base (r : ref) : ref :=
  match r with
  | RArray _ n Hi :: r => RArray 0 n (ref_base_prf _ _ Hi) :: r
  | _ => r
  end.
Definition ref_offset (r : ref) : nat :=
  match r with RArray i _ _ :: r => i | _ => 0 end.
Definition ref_size (r : ref) : nat :=
  match r with RArray _ n _ :: _ => n | _ => 1 end.

Lemma ref_plus_prf (i n : nat) (j : Z) :
  (0 ≤ i + j < n)%Z →
  Z.to_nat (i + j) < n.
Proof. intros. rewrite <-(Nat2Z.id n). apply Z2Nat.inj_lt; lia. Qed.
Definition ref_plus (r : ref) (j : Z) : option ref :=
  match r with
  | RArray i n _ :: r =>
     guard (0 <= i + j < n)%Z as H;
     Some (RArray (Z.to_nat (i + j)) n (ref_plus_prf _ _ _ H) :: r)
  | _ => guard (j = 0); Some r
  end%Z.

Definition ref_minus (r1 r2 : ref) : option Z :=
  guard (ref_base (freeze <$> r1) = ref_base (freeze <$> r2));
  Some (ref_offset r1 - ref_offset r2)%Z.
Arguments ref_minus !_ !_ /.

Definition ref_seg_byte_offset `{PtrEnv Ti} (τ : type Ti) (rs : ref_seg) :
    option (type Ti * nat) :=
  match rs, τ with
  | RArray i _ _, τ.[_] =>
     Some (τ, i * size_of τ)
  | RStruct i, struct s =>
     τs ← get_env !! s;
     τ ← τs !! i;
     Some (τ, struct_offset τs i)
  | RUnion i _, union s =>
     τs ← get_env !! s;
     τ ← τs !! i;
     Some (τ, 0)
  | _, _ => None
  end.
Fixpoint ref_byte_offset `{PtrEnv Ti} (τ : type Ti) (r : ref) :
    option (type Ti * nat) :=
  match r with
  | [] => Some (τ, 0)
  | rs :: r =>
     σi ← ref_byte_offset τ r;
     ρj ← ref_seg_byte_offset (fst σi) rs;
     Some (fst ρj, snd σi + snd ρj)
  end.

Inductive ref_seg_disjoint: Disjoint ref_seg :=
  | RArray_disjoint i1 i2 n Hi1 Hi2 :
     i1 ≠ i2 → RArray i1 n Hi1 ⊥ RArray i2 n Hi2
  | RStruct_disjoint i1 i2 : i1 ≠ i2 → RStruct i1 ⊥ RStruct i2.
Existing Instance ref_seg_disjoint.
Inductive ref_disjoint: Disjoint ref :=
  | ref_disjoint_here (r1 r2 : ref) rs1 rs2 :
     rs1 ⊥ rs2 → r1 ++ [rs1] ⊥ r2 ++ [rs2]
  | ref_disjoint_further (r1 r2 : ref) rs1 rs2 :
     r1 ⊥ r2 → freeze rs1 = freeze rs2 → r1 ++ [rs1] ⊥ r2 ++ [rs2].
Existing Instance ref_disjoint.

Section refs.
  Context `{EnvSpec Ti Vi}.
  Implicit Types τ : type Ti.
  Implicit Types rs : ref_seg.
  Implicit Types r : ref.
  
  Lemma ref_typed_nil τ1 τ2 : τ1 ∙ [] ↝ τ2 ↔ τ1 = τ2.
  Proof.
    split.
    * by inversion 1; simplify_list_equality.
    * intros. subst. constructor.
  Qed.
  Lemma ref_typed_cons rs r τ1 τ3 :
    τ1 ∙ rs :: r ↝ τ3 ↔ ∃ τ2, τ1 ∙ r ↝ τ2 ∧ τ2 ∙ rs ↝ τ3.
  Proof.
    split.
    * inversion 1; subst; eauto.
    * intros (?&?&?). econstructor; eauto.
  Qed.
  Lemma ref_typed_app r1 r2 τ1 τ3 :
    τ1 ∙ r1 ++ r2 ↝ τ3 ↔ ∃ τ2, τ1 ∙ r2 ↝ τ2 ∧ τ2 ∙ r1 ↝ τ3.
  Proof.
    revert τ1 τ3. induction r1; simpl; intros.
    * setoid_rewrite ref_typed_nil. naive_solver.
    * setoid_rewrite ref_typed_cons. naive_solver.
  Qed.
  Lemma ref_typed_singleton rs τ1 τ2 :
    τ1 ∙ [rs] ↝ τ2 ↔ τ1 ∙ rs ↝ τ2.
  Proof.
    rewrite ref_typed_cons. setoid_rewrite ref_typed_nil. naive_solver.
  Qed.
  Lemma ref_typed_snoc r rs τ1 τ3 :
    τ1 ∙ r ++ [rs] ↝ τ3 ↔ ∃ τ2, τ1 ∙ rs ↝ τ2 ∧ τ2 ∙ r ↝ τ3.
  Proof.
    setoid_rewrite ref_typed_app. by setoid_rewrite ref_typed_singleton.
  Qed.
  Lemma ref_typed_snoc_2 r rs τ1 τ2 τ3 :
    τ1 ∙ rs ↝ τ2 ∧ τ2 ∙ r ↝ τ3 → τ1 ∙ r ++ [rs] ↝ τ3.
  Proof. rewrite ref_typed_snoc. eauto. Qed.

  Lemma ref_seg_typed_type_valid rs τ σ :
    τ ∙ rs ↝ σ → type_valid get_env τ → type_valid get_env σ.
  Proof.
    destruct 1; inversion 1; subst; eauto using env_valid_lookup_lookup.
  Qed.
  Lemma ref_typed_type_valid r τ σ :
    τ ∙ r ↝ σ → type_valid get_env τ → type_valid get_env σ.
  Proof. induction 1; eauto using ref_seg_typed_type_valid. Qed.

  Lemma ref_lookup_nil τ : τ !! [] = Some τ.
  Proof. done. Qed.
  Lemma ref_lookup_cons rs r τ : τ !! (rs :: r) = (τ !! r) ≫= (!! rs).
  Proof. done. Qed.
  Lemma ref_lookup_app r1 r2 τ : τ !! (r1 ++ r2) = (τ !! r2) ≫= (!! r1).
  Proof.
    induction r1 as [|rs1 r1 IH]; simpl.
    * by destruct (τ !! r2).
    * rewrite ref_lookup_cons. by rewrite IH, option_bind_assoc.
  Qed.
  Lemma ref_lookup_snoc r rs τ : τ !! (r ++ [rs]) = (τ !! rs) ≫= (!! r).
  Proof. apply ref_lookup_app. Qed.

  Lemma ref_seg_typed_valid τ rs σ :
    type_valid get_env τ → τ ∙ rs ↝ σ → type_valid get_env σ.
  Proof.
    intros Hτ.
    destruct 1; inversion_clear Hτ; eauto using env_valid_lookup_lookup.
  Qed.
  Lemma ref_valid_typed_valid τ r σ :
    type_valid get_env τ → τ ∙ r ↝ σ → type_valid get_env σ.
  Proof. induction 2; eauto using ref_seg_typed_valid. Qed.

  Lemma ref_seg_lookup_correct τ rs σ : τ ∙ rs ↝ σ ↔ τ !! rs = Some σ.
  Proof.
    split.
    * by destruct 1; simplify_option_equality.
    * destruct rs, τ as [| | |[]]; intros;
        simplify_option_equality; econstructor; eauto.
  Qed.
  Lemma ref_lookup_correct τ r σ : τ ∙ r ↝ σ ↔ τ !! r = Some σ.
  Proof.
    split.
    * induction 1 as [|????? Hrs]; [done |].
      rewrite ref_lookup_cons. simplify_option_equality.
      by rewrite <-ref_seg_lookup_correct.
    * revert σ. induction r; intros σ.
      + intros. simplify_equality. constructor.
      + rewrite ref_lookup_cons. intros. simplify_option_equality.
        econstructor; eauto. by apply ref_seg_lookup_correct.
  Qed.
  Lemma ref_lookup_sound τ r σ : τ !! r = Some σ → τ ∙ r ↝ σ.
  Proof. by rewrite ref_lookup_correct. Qed.
  Lemma ref_lookup_complete τ r σ : τ ∙ r ↝ σ → τ !! r = Some σ.
  Proof. by rewrite ref_lookup_correct. Qed.

  Lemma ref_seg_typed_void rs σ : ¬void ∙ rs ↝ σ.
  Proof. inversion 1. Qed.
  Lemma ref_typed_void r σ : void ∙ r ↝ σ → σ = void ∧ r = [].
  Proof.
    destruct r as [|rs r] using rev_ind.
    * rewrite ref_typed_nil. by intros; subst.
    * rewrite ref_typed_snoc. intros (?&Hrs&_).
      edestruct ref_seg_typed_void; eauto.
  Qed.

  Lemma ref_seg_freeze_frozen rs : frozen (freeze rs).
  Proof. destruct rs; constructor. Qed.
  Lemma ref_freeze_frozen r : Forall frozen (freeze <$> r).
  Proof. apply Forall_fmap, Forall_true, ref_seg_freeze_frozen. Qed.

  Lemma ref_seg_frozen_freeze rs : frozen rs → freeze rs = rs.
  Proof. by destruct 1. Qed.
  Lemma ref_frozen_freeze r : Forall frozen r → freeze <$> r = r.
  Proof. induction 1; simpl; f_equal; auto using ref_seg_frozen_freeze. Qed.

  Lemma ref_seg_freeze_idempotent rs : freeze (freeze rs) = freeze rs.
  Proof. apply ref_seg_frozen_freeze, ref_seg_freeze_frozen. Qed.
  Lemma ref_freeze_idempotent r :freeze <$> (freeze <$> r) = freeze <$> r.
  Proof. apply ref_frozen_freeze, ref_freeze_frozen. Qed.

  Lemma ref_seg_typed_freeze τ rs σ : τ ∙ freeze rs ↝ σ ↔ τ ∙ rs ↝ σ.
  Proof.
    split.
    * destruct rs; inversion_clear 1; econstructor; eauto.
    * destruct 1; econstructor; eauto.
  Qed.
  Lemma ref_typed_freeze τ r σ : τ ∙ freeze <$> r ↝ σ ↔ τ ∙ r ↝ σ.
  Proof.
    revert τ σ. induction r as [|rs r IH]; intros τ σ; simpl.
    * by rewrite ref_typed_nil.
    * rewrite !ref_typed_cons.
      setoid_rewrite ref_seg_typed_freeze. by setoid_rewrite IH.
  Qed.
  Lemma ref_seg_lookup_freeze τ rs : τ !! freeze rs = τ !! rs.
  Proof.
    apply option_eq. intros.
    rewrite <-!ref_seg_lookup_correct. apply ref_seg_typed_freeze.
  Qed.
  Lemma ref_lookup_freeze τ r : τ !! (freeze <$> r) = τ !! r.
  Proof.
    apply option_eq. intros.
    rewrite <-!ref_lookup_correct. apply ref_typed_freeze.
  Qed.

  Lemma ref_disjoint_snoc r1 r2 rs1 rs2 :
    r1 ++ [rs1] ⊥ r2 ++ [rs2] ↔ rs1 ⊥ rs2 ∨ (r1 ⊥ r2 ∧ freeze rs1 = freeze rs2).
  Proof.
    split.
    * inversion 1; simplify_list_equality; auto.
    * intros [?|[??]]; constructor (solve [auto]).
  Qed.
  Lemma ref_disjoint_app r1 r2 r1' r2' :
    r1 ⊥ r2 → freeze <$> r1' = freeze <$> r2' → r1 ++ r1' ⊥ r2 ++ r2'.
  Proof.
    intros Hr. revert r2'.
    induction r1' as [|rs1 r1' IH] using rev_ind; simpl; intros ? Hr'.
    * simplify_list_fmap_equality. by rewrite !(right_id_L [] (++)).
    * rewrite fmap_app in Hr'. simpl in Hr'.
      simplify_list_fmap_equality. rewrite !(associative_L (++)).
      constructor (by auto).
  Qed.
  Lemma ref_disjoint_alt r1 r2 :
    r1 ⊥ r2 ↔ ∃ r1' rs1 r1'' r2' rs2 r2'',
      r1 = r1' ++ [rs1] ++ r1'' ∧ r2 = r2' ++ [rs2] ++ r2'' ∧
      rs1 ⊥ rs2 ∧ freeze <$> r1'' = freeze <$> r2''.
  Proof.
    split.
    * induction 1 as [|r1 r2 rs1 rs2 _ (r1'&rs1'&r1''&r2'&rs2'&r2''&?&?&?&?)].
      + naive_solver.
      + subst. exists r1' rs1' (r1'' ++ [rs1]). exists r2' rs2' (r2'' ++ [rs2]).
        rewrite !(associative_L (++)), !fmap_app. simpl. intuition congruence.
    * intros (r1'&rs1'&r1''&r2'&rs2'&r2''&?&?&?&?). subst.
      rewrite !(associative_L (++)).
      auto using ref_disjoint_app, ref_disjoint_here.
  Qed.

  Lemma ref_disjoint_singleton rs1 rs2 : [rs1] ⊥ [rs2] ↔ rs1 ⊥ rs2.
  Proof.
    rewrite ref_disjoint_alt. split.
    * by intros ([]&?&?&[]&?&?&?&?&?&?); simplify_list_equality.
    * intros. eexists [], rs1, []. by eexists [], rs2, [].
  Qed.

  Lemma ref_disjoint_cons rs1 rs2 r1' r2' :
    rs1 ⊥ rs2 → freeze <$> r1' = freeze <$> r2' → rs1 :: r1' ⊥ rs2 :: r2'.
  Proof.
    intros. eapply (ref_disjoint_app [_] [_]); [|done].
    by rewrite ref_disjoint_singleton.
  Qed.

  Global Instance: Commutative (↔) (@disjoint ref_seg _).
  Proof. split; destruct 1; constructor; auto. Qed.
  Global Instance: Commutative (↔) (@disjoint ref _).
  Proof.
    red. setoid_rewrite ref_disjoint_alt.
    pose proof (commutative (@disjoint ref_seg _)). naive_solver auto.
  Qed.

  Lemma ref_seg_disjoint_freeze_l rs1 rs2 :freeze rs1 ⊥ rs2 ↔ rs1 ⊥ rs2.
  Proof.
    split.
    * by destruct rs1; inversion_clear 1; constructor.
    * by destruct 1; constructor.
  Qed.
  Lemma ref_seg_disjoint_freeze_r rs1 rs2 : rs1 ⊥ freeze rs2 ↔ rs1 ⊥ rs2.
  Proof. by rewrite !(commutative _ rs1), ref_seg_disjoint_freeze_l. Qed.
  Lemma ref_disjoint_freeze_l r1 r2 : freeze <$> r1 ⊥ r2 ↔ r1 ⊥ r2.
  Proof.
    setoid_rewrite ref_disjoint_alt.
    by split; intros (?&?&?&?&?&?&?&?&?&?);
      simplify_list_fmap_equality; rewrite ?fmap_app; repeat esplit; eauto;
      rewrite 1?ref_seg_disjoint_freeze_l, 1?ref_freeze_idempotent in *.
  Qed.
  Lemma ref_disjoint_freeze_r r1 r2 : r1 ⊥ freeze <$> r2 ↔ r1 ⊥ r2.
  Proof. by rewrite !(commutative _ r1), ref_disjoint_freeze_l. Qed.
  Lemma ref_disjoint_freeze r1 r2 : freeze <$> r1 ⊥ freeze <$> r2 ↔ r1 ⊥ r2.
  Proof. by rewrite ref_disjoint_freeze_l, ref_disjoint_freeze_r. Qed.

  Global Instance ref_seg_frozen_dec rs : Decision (ref_seg_frozen rs).
  Proof.
   refine (
    match rs with
    | RUnion _ true => right _
    | _ => left _
    end); first [constructor | inversion 1].
  Defined.
  Global Instance ref_seg_disjoint_dec rs1 rs2 :
    Decision (ref_seg_disjoint rs1 rs2).
  Proof.
   refine (
    match rs1, rs2 with
    | RArray i n1 _, RArray j n2 _ =>
       if decide (n1 = n2) then cast_if_not (decide (i = j)) else right _
    | RStruct i, RStruct j => cast_if_not (decide (i = j))
    | _, _ => right _
    end);first [by subst; constructor | abstract by inversion 1].
  Defined.

  Inductive ref_disjoint_rev: ref → ref → Prop :=
    | ref_disjoint_rev_here rs1 rs2 r1' r2' :
       rs1 ⊥ rs2 → ref_disjoint_rev (rs1 :: r1') (rs2 :: r2')
    | ref_disjoint_rev_cons rs1 rs2 r1 r2 :
       freeze rs1 = freeze rs2 →
       ref_disjoint_rev r1 r2 → ref_disjoint_rev (rs1 :: r1) (rs2 :: r2).

  Global Instance ref_disjoint_rev_dec: ∀ r1 r2,
    Decision (ref_disjoint_rev r1 r2).
  Proof.
   refine (
    fix go r1 r2 :=
    match r1, r2 return Decision (ref_disjoint_rev r1 r2) with
    | rs1 :: r1, rs2 :: r2 =>
       if decide (rs1 ⊥ rs2) then left _
       else cast_if_and (decide (freeze rs1 = freeze rs2)) (go r1 r2)
    | _, _ => right _
    end); clear go;
     first [econstructor (by auto) | abstract (inversion 1; auto)].
  Defined.

  Lemma ref_disjoint_rev_correct_1 r1 r2 :
    ref_disjoint_rev r1 r2 → reverse r1 ⊥ reverse r2.
  Proof. induction 1; rewrite !reverse_cons; constructor (by auto). Qed.
  Lemma ref_disjoint_rev_correct_2 r1 r2 :
    r1 ⊥ r2 → ref_disjoint_rev (reverse r1) (reverse r2).
  Proof. induction 1; rewrite !reverse_snoc; constructor (by auto). Qed.
  Lemma ref_disjoint_rev_correct r1 r2 :
    r1 ⊥ r2 ↔ ref_disjoint_rev (reverse r1) (reverse r2).
  Proof.
    split.
    * apply ref_disjoint_rev_correct_2.
    * intros. rewrite <-(reverse_involutive r1), <-(reverse_involutive r2).
      by apply ref_disjoint_rev_correct_1.
  Qed.

  Global Instance ref_disjoint_dec r1 r2 : Decision (r1 ⊥ r2).
  Proof.
    refine (cast_if (decide (ref_disjoint_rev (reverse r1) (reverse r2))));
     by rewrite ref_disjoint_rev_correct.
  Qed.

  Lemma RArray_snoc_inv r1 r2 i1 i2 n Hi1 Hi2 :
    r1 ++ [RArray i1 n Hi1] ⊥ r2 ++ [RArray i2 n Hi2] ↔ i1 ≠ i2 ∨ r1 ⊥ r2.
  Proof.
    rewrite ref_disjoint_snoc. split.
    * intros [Harr|[??]]; [inversion Harr|]; tauto.
    * destruct (decide (i1 = i2)); intros [?|?];
        eauto using RArray_disjoint with f_equal.
  Qed.
  Lemma RArray_snoc_not r1 r2 i1 i2 n Hi1 Hi2 :
    ¬r1 ++ [RArray i1 n Hi1] ⊥ r2 ++ [RArray i2 n Hi2] ↔ i1 = i2 ∧ ¬r1 ⊥ r2.
  Proof. rewrite RArray_snoc_inv. destruct (decide (i1 = i2)); tauto. Qed.

  Lemma RStruct_snoc_inv r1 r2 i1 i2 :
    r1 ++ [RStruct i1] ⊥ r2 ++ [RStruct i2] ↔ i1 ≠ i2 ∨ r1 ⊥ r2.
  Proof.
    rewrite ref_disjoint_snoc. split.
    * intros [Harr|[??]]; [inversion Harr|]; tauto.
    * destruct (decide (i1 = i2)); intros [?|?];
        eauto using RStruct_disjoint with f_equal.
  Qed.
  Lemma RStruct_snoc_not r1 r2 i1 i2 :
    ¬r1 ++ [RStruct i1] ⊥ r2 ++ [RStruct i2] ↔ i1 = i2 ∧ ¬r1 ⊥ r2.
  Proof. rewrite RStruct_snoc_inv. destruct (decide (i1 = i2)); tauto. Qed.

  Lemma RUnion_snoc_inv r1 r2 i1 b1 i2 b2 :
    r1 ++ [RUnion i1 b1] ⊥ r2 ++ [RUnion i2 b2] ↔
      i1 = i2 ∧ r1 ⊥ r2.
  Proof.
    rewrite ref_disjoint_snoc. split.
    * by intros [Hu|[??]]; [inversion Hu|]; simplify_equality.
    * intros [??]; subst; eauto using RStruct_disjoint with f_equal.
  Qed.
  Lemma RUnion_snoc_not r1 r2 i1 b1 i2 b2 :
    ¬r1 ++ [RUnion i1 b1] ⊥ r2 ++ [RUnion i2 b2] ↔
      i1 ≠ i2 ∨ (i1 = i2 ∧ ¬r1 ⊥ r2).
  Proof. rewrite RUnion_snoc_inv. destruct (decide (i1 = i2)); tauto. Qed.

  Lemma ref_not_disjoint τ r1 r2 σ1 σ2 :
    τ ∙ r1 ↝ σ1 →
    τ ∙ r2 ↝ σ2 →
    ¬r1 ⊥ r2 →
    freeze <$> r1 `suffix_of` freeze <$> r2 ∨
    freeze <$> r2 `suffix_of` freeze <$> r1 ∨
    ∃ r1' i1 b1 r1'' r2' i2 b2 r2'',
      r1 = r1' ++ [RUnion i1 b1] ++ r1'' ∧
      r2 = r2' ++ [RUnion i2 b2] ++ r2'' ∧
      i1 ≠ i2 ∧
      freeze <$> r1'' = freeze <$> r2''.
  Proof.
    intros Hτ1. revert τ σ1 Hτ1 r2 σ2.
    induction r1 as [|rs1 r1 IH] using rev_ind; intros τ σ1.
    { simpl. eauto using suffix_of_nil. }
    rewrite ref_typed_snoc. intros (τ1 & Hrs1 & Hr1).
    intros r2. destruct r2 as [|rs2 r2 _] using rev_ind; intros σ2.
    { simpl. eauto using suffix_of_nil. }
    rewrite ref_typed_snoc. intros (τ2 & Hrs2 & Hr2). rewrite !fmap_app. simpl.
    destruct Hrs1; inversion Hrs2; simplify_option_equality.
    * rewrite RArray_snoc_not. intros [??]. subst.
      destruct (IH _ _ Hr1 _ _ Hr2) as
        [?|[?|(r1'&?&?&r1''&r2'&?&?&r2''&?&?&?&?)]];
        eauto using suffix_of_snoc_alt with f_equal.
      subst. do 2 right. eexists r1', _, _, (r1'' ++ [_]).
      eexists r2', _, _, (r2'' ++ [_]).
      rewrite !app_comm_cons, !(associative_L (++)), !fmap_app.
      split_ands; eauto with f_equal.
    * rewrite RStruct_snoc_not. intros [??]. simplify_option_equality.
      destruct (IH _ _ Hr1 _ _ Hr2)
        as [?|[?|(r1'&?&?&r1''&r2'&?&?&r2''&?&?&?&?)]];
        eauto using suffix_of_snoc_alt with f_equal.
      subst. do 2 right. eexists r1', _, _, (r1'' ++ [_]).
      eexists r2', _, _, (r2'' ++ [_]).
      rewrite !app_comm_cons, !(associative_L (++)), !fmap_app.
      split_ands; eauto with f_equal.
    * rewrite RUnion_snoc_not. intros [?|[??]]; [by eauto 15 |].
      simplify_option_equality.
      destruct (IH _ _ Hr1 _ _ Hr2)
        as [?|[?|(r1'&?&?&r1''&r2'&?&?&r2''&?&?&?&?)]];
        eauto using suffix_of_snoc_alt with f_equal.
      subst. do 2 right. eexists r1', _, _, (r1'' ++ [_]).
      eexists r2', _, _, (r2'' ++ [_]).
      rewrite !app_comm_cons, !(associative_L (++)), !fmap_app.
      split_ands; eauto with f_equal.
  Qed.
  Lemma ref_not_disjoint_frozen τ r1 r2 σ1 σ2 :
    τ ∙ r1 ↝ σ1 →
    τ ∙ r2 ↝ σ2 →
    ¬r1 ⊥ r2 →
    Forall frozen r1 →
    Forall frozen r2 →
    r1 `suffix_of` r2 ∨ r2 `suffix_of` r1 ∨ ∃ r1' i1 b1 r2' i2 b2 r,
      r1 = r1' ++ [RUnion i1 b1] ++ r ∧
      r2 = r2' ++ [RUnion i2 b2] ++ r ∧
      i1 ≠ i2.
  Proof.
    intros ??? Hr1 Hr2. generalize (ref_not_disjoint τ r1 r2 σ1 σ2).
    rewrite !ref_frozen_freeze by done.
    intros [?|[?|(r1'&?&?&r1''&r2'&?&?&r2''&?&?&?&Hr)]]; eauto.
    subst. rewrite !Forall_app in Hr1, Hr2.
    rewrite !ref_frozen_freeze in Hr by intuition. subst. eauto 15.
  Qed.

  Lemma ref_base_idempotent r : ref_base (ref_base r) = ref_base r.
  Proof. destruct r as [|[]]; simpl; auto with f_equal. Qed.
  Lemma ref_offset_base r : ref_offset (ref_base r) = 0.
  Proof. by destruct r as [|[]]. Qed.
  Lemma ref_size_base r : ref_size (ref_base r) = ref_size r.
  Proof. by destruct r as [|[]]. Qed.
  Lemma ref_size_same_base r r' :
    ref_base r = ref_base r' → ref_size r = ref_size r'.
  Proof.
    intros Hr. by rewrite <-(ref_size_base r), <-(ref_size_base r'), Hr.
  Qed.

  Lemma ref_typed_size r rs σ τ :
    σ ∙ rs ↝ τ → ref_size (rs :: r) = array_size σ.
  Proof. by intros []. Qed.

  Lemma ref_eq r1 r2 :
    ref_base r1 = ref_base r2 → ref_offset r1 = ref_offset r2 → r1 = r2.
  Proof.
    destruct r1 as [|[]], r2 as [|[]]; simpl; intros;
      simplify_equality; auto with f_equal.
  Qed.
  Lemma ref_base_typed τ r σ : τ ∙ r ↝ σ → τ ∙ ref_base r ↝ σ.
  Proof. destruct 1 as [|????? []]; repeat econstructor; eauto with lia. Qed.
  Lemma ref_offset_size r : ref_offset r < ref_size r.
  Proof. destruct r as [|[]]; auto with lia. Qed.
  Lemma ref_offset_size_alt r : (ref_offset r < ref_size r)%Z.
  Proof. apply Nat2Z.inj_lt, ref_offset_size. Qed.

  Lemma ref_typed_alt τ r σ : τ ∙ r ↝ σ ↔ τ ∙ ref_base r ↝ σ.
  Proof.
    split.
    * eauto using ref_base_typed.
    * intros Hr. destruct r as [|[]]; inversion Hr as [|????? Hrs];
        try inversion Hrs; subst; repeat econstructor; eauto.
  Qed.

  Lemma ref_base_freeze r : ref_base (freeze <$> r) = freeze <$> ref_base r.
  Proof. by destruct r as [|[]]. Qed.
  Lemma ref_offset_freeze r : ref_offset (freeze <$> r) = ref_offset r.
  Proof. by destruct r as [|[]]. Qed.
  Lemma ref_size_freeze r : ref_size (freeze <$> r) = ref_size r.
  Proof. by destruct r as [|[]]; simpl; rewrite ?ref_lookup_freeze. Qed.
  Lemma ref_plus_freeze r i :
    ref_plus (freeze <$> r) i = fmap (M:=list) freeze <$> ref_plus r i.
  Proof. by destruct r as [|[]]; simplify_option_equality. Qed.
  Lemma ref_minus_freeze_l r1 r2 :
    ref_minus (freeze <$> r1) r2 = ref_minus r1 r2.
  Proof.
    unfold ref_minus. by rewrite !ref_offset_freeze, ref_freeze_idempotent.
  Qed.
  Lemma ref_minus_freeze_r r1 r2 :
    ref_minus r1 (freeze <$> r2) = ref_minus r1 r2.
  Proof.
    unfold ref_minus.
    by rewrite !ref_offset_freeze, ref_base_freeze, ref_freeze_idempotent.
  Qed.
  Lemma ref_minus_freeze r1 r2 :
    ref_minus (freeze <$> r1) (freeze <$> r2) = ref_minus r1 r2.
  Proof. by rewrite ref_minus_freeze_l, ref_minus_freeze_r. Qed.

  Lemma ref_base_plus r i r' :
    ref_plus r i = Some r' → ref_base r' = ref_base r.
  Proof.
    destruct r as [|[]]; intros; simplify_option_equality; auto with f_equal.
  Qed.
  Lemma ref_size_plus r i r' :
    ref_plus r i = Some r' → ref_size r' = ref_size r.
  Proof. by destruct r as [|[]]; intros; simplify_option_equality. Qed.
  Lemma ref_offset_plus r i r' :
    ref_plus r i = Some r' → Z.of_nat (ref_offset r') = (ref_offset r + i)%Z.
  Proof.
    destruct r as [|[]]; intros; simplify_option_equality;
      rewrite ?Z2Nat.id; auto with lia.
  Qed.
  Lemma ref_offset_plus_range r i r' :
    ref_plus r i = Some r' → (0 ≤ ref_offset r + i < ref_size r)%Z.
  Proof.
    intros. rewrite <-(ref_offset_plus _ _ r'), <-(ref_size_plus r i r');
      auto using ref_offset_size_alt with lia.
  Qed.
  Lemma ref_plus_is_Some r i :
    is_Some (ref_plus r i) ↔ (0 ≤ ref_offset r + i < ref_size r)%Z.
  Proof.
    split; intros [??]; eauto using ref_offset_plus_range.
    destruct r as [|[]]; simplify_option_equality; eauto with lia.
  Qed.

  Lemma ref_plus_Some_2 r i r' :
    (0 ≤ ref_offset r + i < ref_size r)%Z →
    ref_base r' = ref_base r →
    Z.of_nat (ref_offset r') = (ref_offset r + i)%Z →
    ref_plus r i = Some r'.
  Proof.
    intros [??] ? Hi. destruct r as [|[]], r' as [|[]]; simpl;
      simplify_option_equality; repeat f_equal; try apply RArray_eq;
      rewrite <-?Hi, ?Nat2Z.id; auto with lia.
  Qed.
  Lemma ref_plus_Some r i r' :
    ref_plus r i = Some r' ↔
      (0 ≤ ref_offset r + i < ref_size r)%Z ∧
      ref_base r' = ref_base r ∧
      Z.of_nat (ref_offset r') = (ref_offset r + i)%Z.
  Proof.
    split.
    * eauto 6 using ref_base_plus, ref_offset_plus, ref_offset_plus_range.
    * intros [[??] [? Hi]]. eauto using ref_plus_Some_2.
  Qed.

  Lemma ref_plus_typed τ r σ i r' :
    τ ∙ r ↝ σ → ref_plus r i = Some r' → τ ∙ r' ↝ σ.
  Proof.
    intros. apply ref_typed_alt. erewrite ref_base_plus by eauto.
    by apply ref_base_typed.
  Qed.

  Lemma ref_plus_base_offset r : ref_plus (ref_base r) (ref_offset r) = Some r.
  Proof.
    apply ref_plus_Some_2.
    * rewrite ref_offset_base, ref_size_base.
      pose proof (ref_offset_size r); lia.
    * by rewrite !ref_base_idempotent.
    * rewrite ref_offset_base. lia.
  Qed.

  Lemma ref_minus_Some r1 r2 j :
    ref_minus r1 r2 = Some j ↔
      ref_base (freeze <$> r1) = ref_base (freeze <$> r2) ∧
      j = (ref_offset r1 - ref_offset r2)%Z.
  Proof. unfold ref_minus. by intuition idtac; simplify_option_equality. Qed.
  Lemma ref_minus_Some_2 r1 r2 j :
    ref_base (freeze <$> r1) = ref_base (freeze <$> r2) →
    j = (ref_offset r1 - ref_offset r2)%Z → ref_minus r1 r2 = Some j.
  Proof. by rewrite ref_minus_Some. Qed.
  Lemma ref_minus_Some_base r1 r2 j :
    ref_minus r1 r2 = Some j →
    ref_base (freeze <$> r1) = ref_base (freeze <$> r2).
  Proof. rewrite ref_minus_Some. tauto. Qed.
  Lemma ref_minus_Some_offset r1 r2 j :
    ref_minus r1 r2 = Some j → j = (ref_offset r1 - ref_offset r2)%Z.
  Proof. rewrite ref_minus_Some. tauto. Qed.
  Lemma ref_minus_Some_plus r1 r2 j :
    ref_minus r2 r1 = Some j →
    ref_plus (freeze <$> r1) j = Some (freeze <$> r2).
  Proof.
    rewrite ref_minus_Some. intros [Hr ?]. subst. apply ref_plus_Some_2.
    * rewrite <-(ref_size_base (freeze <$> r1)), <-Hr, ref_size_base.
      rewrite !ref_offset_freeze, !ref_size_freeze.
      pose proof (ref_offset_size_alt r2). lia.
    * done.
    * rewrite !ref_offset_freeze. lia.
  Qed.
End refs.

(** * Byte references *)
Inductive bref :=
  | RObj : ref → bref
  | RByte : ref → ∀ i n, i < n → bref.

Lemma RByte_eq r1 i1 n1 Hi1 r2 i2 n2 Hi2 :
  r1 = r2 → i1 = i2 → n1 = n2 → RByte r1 i1 n1 Hi1 = RByte r2 i2 n2 Hi2.
Proof. intros. subst. f_equal. apply (proof_irrel _). Qed.
Hint Resolve RByte_eq : f_equal.

Instance bref_eq_dec (r1 r2 : bref) : Decision (r1 = r2).
Proof.
 refine
  match r1, r2 with
  | RObj r1, RObj r2 => cast_if (decide (r1 = r2))
  | RByte r1 i1 n1 _, RByte r2 i2 n2 _ =>
     cast_if_and3 (decide (r1 = r2)) (decide (i1 = i2)) (decide (n1 = n2))
  | _, _ => right _
  end; auto with f_equal; abstract (try injection 1; congruence).
Defined.

Inductive bref_typed `{PtrEnv Ti} `{IntEnv Ti Vi} :
    PathTyped (type Ti) bref :=
  | RObj_typed τ r σ : τ ∙ r ↝ σ → τ ∙ RObj r ↝ σ
  | RByte_typed τ r σ i n Hi :
     τ ∙ r ↝ σ → τ ≠ uchar → n = size_of σ →
     τ ∙ RByte r i n Hi ↝ uchar.
Existing Instance bref_typed.

Instance bref_lookup `{PtrEnv Ti} `{IntEnv Ti Vi} :
    Lookup bref (type Ti) (type Ti) := λ r τ,
  match r with
  | RObj r => τ !! r
  | RByte r i n _ =>
     σ ← τ !! r;
     guard (τ ≠ uchar);
     guard (n = size_of σ);
     Some uchar
  end.

Inductive bref_frozen: Frozen bref :=
  | RObj_frozen r : Forall frozen r → frozen (RObj r)
  | RByte_frozen r i n Hi : Forall frozen r → frozen (RByte r i n Hi).
Existing Instance bref_frozen.
Instance bref_freeze: Freeze bref := λ r,
  match r with
  | RObj r => RObj (freeze <$> r)
  | RByte r i n Hi => RByte (freeze <$> r) i n Hi
  end.

Lemma bref_base_prf i n : i < n → 0 < n.
Proof. lia. Qed.
Definition bref_base (r : bref) : bref :=
  match r with
  | RObj r => RObj (ref_base r)
  | RByte r _ n Hi => RByte (ref_base r) 0 n (bref_base_prf _ _ Hi)
  end.
Definition bref_offset (r : bref) : nat :=
  match r with
  | RObj r => ref_offset r
  | RByte r i n _ => ref_offset r * n + i
  end.
Definition bref_size (r : bref) : nat :=
  match r with
  | RObj r => ref_size r
  | RByte r _ n _ => ref_size r * n
  end.

Lemma bref_plus_prf i n x : i < n → Z.to_nat (x `mod` n) < n.
Proof.
  intros. rewrite <-(Nat2Z.id n) at 2.
  apply Z2Nat.inj_lt; auto with zpos. apply Z.mod_pos_bound; auto with zpos.
Qed.
Definition bref_plus (r : bref) (j : Z) : option bref :=
  match r with
  | RObj r => RObj <$> ref_plus r j
  | RByte r i n Hi =>
     r' ← ref_plus r ((i + j) `div` n);
     Some (RByte r' (Z.to_nat ((i + j) `mod` n)) n
       (bref_plus_prf _ _ _ Hi))
  end.
Definition bref_minus (r1 r2 : bref) : option Z :=
  match r1, r2 with
  | RObj r1, RObj r2 => ref_minus r1 r2
  | RByte r1 i1 n1 _, RByte r2 i2 n2 _ =>
     guard (n1 = n2); (* to get better properties *)
     j ← ref_minus r1 r2;
     Some (j * n1 + i1 - i2)%Z
  | _, _ => None
  end.
Inductive bref_disjoint: Disjoint bref :=
  | RObj_disjoint r1 r2 :
     r1 ⊥ r2 → RObj r1 ⊥ RObj r2
  | RByte_offset_disjoint r1 i1 r2 i2 n Hi1 Hi2 :
     freeze <$> r1 = freeze <$> r2 →
     i1 ≠ i2 → RByte r1 i1 n Hi1 ⊥ RByte r2 i2 n Hi2
  | RByte_obj_disjoint r1 i1 r2 i2 n Hi1 Hi2 :
     r1 ⊥ r2 → RByte r1 i1 n Hi1 ⊥ RByte r2 i2 n Hi2
  | RObj_RByte_disjoint r1 r2 i2 n2 Hi2 :
     r1 ⊥ r2 → RObj r1 ⊥ RByte r2 i2 n2 Hi2
  | RByte_RObj_disjoint r1 i1 n1 r2 Hi1 :
     r1 ⊥ r2 → RByte r1 i1 n1 Hi1 ⊥ RObj r2.
Existing Instance bref_disjoint.

Section bref.
  Context `{EnvSpec Ti Vi}.
  Implicit Types r : bref.

  Lemma bref_typed_type_valid τ r σ :
    τ ∙ r ↝ σ → type_valid get_env τ → type_valid get_env σ.
  Proof.
    destruct 1; eauto using ref_typed_type_valid, TBase_valid, TInt_valid.
  Qed.

  Lemma bref_lookup_correct τ r σ : τ ∙ r ↝ σ ↔ τ !! r = Some σ.
  Proof.
    unfold lookup, bref_lookup. split.
    * destruct 1.
      + by apply ref_lookup_complete.
      + erewrite ref_lookup_complete by eauto. by simplify_option_equality.
    * destruct r; intros.
      + constructor. by apply ref_lookup_sound.
      + simplify_option_equality. econstructor; eauto using ref_lookup_sound.
  Qed.
  Lemma bref_lookup_sound τ r σ : τ !! r = Some σ → τ ∙ r ↝ σ.
  Proof. by rewrite bref_lookup_correct. Qed.
  Lemma bref_lookup_complete τ r σ : τ ∙ r ↝ σ → τ !! r = Some σ.
  Proof. by rewrite bref_lookup_correct. Qed.

  Lemma bref_typed_void r σ : void ∙ r ↝ σ → σ = void ∨ σ = uchar.
  Proof.
    inversion 1 as [? r' σ'|]; subst.
    * edestruct ref_typed_void; eauto.
    * eauto.
  Qed.

  Lemma bref_typed_freeze τ r σ : τ ∙ freeze r ↝ σ ↔ τ ∙ r ↝ σ.
  Proof.
    split.
    * destruct r; inversion_clear 1;
        econstructor; eauto; by apply ref_typed_freeze.
    * destruct 1; econstructor; eauto; by apply ref_typed_freeze.
  Qed.
  Lemma bref_lookup_freeze τ r : τ !! freeze r = τ !! r.
  Proof.
    apply option_eq. intros.
    by rewrite <-!bref_lookup_correct, bref_typed_freeze.
  Qed.

  Lemma bref_freeze_frozen r : frozen (freeze r).
  Proof. destruct r; constructor; apply ref_freeze_frozen. Qed.
  Lemma bref_frozen_freeze r : frozen r → freeze r = r.
  Proof. destruct 1; simpl; intros; f_equal; by apply ref_frozen_freeze. Qed.
  Lemma bref_frozen_alt r : frozen r ↔ freeze r = r.
  Proof.
    split; intros E; eauto using bref_frozen_freeze.
    rewrite <-E. eauto using bref_freeze_frozen.
  Qed.
  Lemma bref_freeze_idempotent r : freeze (freeze r) = freeze r.
  Proof. apply bref_frozen_freeze, bref_freeze_frozen. Qed.
  Global Instance: Commutative (↔) (@disjoint bref _).
  Proof. split; destruct 1; constructor (by rewrite (commutative _)). Qed.

  Lemma bref_disjoint_freeze_l r1 r2 : freeze r1 ⊥ r2 ↔ r1 ⊥ r2.
  Proof.
    split.
    * destruct r1, r2; inversion 1; subst; econstructor
      (by rewrite <-1?ref_disjoint_freeze_l, ?ref_freeze_idempotent in *; auto).
    * destruct 1; econstructor
      (by rewrite 1?ref_disjoint_freeze_l, ?ref_freeze_idempotent; auto).
  Qed.
  Lemma bref_disjoint_freeze_r r1 r2 : r1 ⊥ freeze r2 ↔ r1 ⊥ r2.
  Proof. by rewrite !(commutative _ r1), bref_disjoint_freeze_l. Qed.
  Lemma bref_disjoint_freeze r1 r2 : freeze r1 ⊥ freeze r2 ↔ r1 ⊥ r2.
  Proof. by rewrite bref_disjoint_freeze_l, bref_disjoint_freeze_r. Qed.

  Global Instance bref_frozen_dec r : Decision (frozen r).
  Proof.
   refine
    match r with
    | RObj r | RByte r _ _ _ => cast_if (decide (Forall frozen r))
    end; first [by constructor | by inversion 1].
  Defined.
  Global Instance bref_disjoint_dec r1 r2 : Decision (r1 ⊥ r2).
  Proof.
   refine
    match r1, r2 with
    | RObj r1, RObj r2 => cast_if (decide (r1 ⊥ r2))
    | RObj r1, RByte r2 _ _ _ | RByte r1 _ _ _, RObj r2 =>
       cast_if (decide (r1 ⊥ r2))
    | RByte r1 i1 n1 _, RByte r2 i2 n2 _ =>
       if decide (n1 = n2) then
         if decide (r1 ⊥ r2) then left _
         else if decide (freeze <$> r1 = freeze <$> r2)
         then cast_if_not (decide (i1 = i2)) else right _
       else right _
    end; first [subst; constructor (done) | by inversion 1].
  Defined.

  Lemma bref_base_idempotent r : bref_base (bref_base r) = bref_base r.
  Proof.
    destruct r; simpl; rewrite ref_base_idempotent; auto with f_equal.
  Qed.
  Lemma bref_offset_base r : bref_offset (bref_base r) = 0.
  Proof. destruct 0; simpl; rewrite ref_offset_base; lia. Qed.
  Lemma bref_offset_base_alt r : bref_base r = r → bref_offset r = 0.
  Proof. intros Hr. by rewrite <-Hr, bref_offset_base. Qed.
  Lemma bref_size_base r : bref_size (bref_base r) = bref_size r.
  Proof. by destruct 0; simpl; rewrite ref_size_base. Qed.
  Lemma bref_size_same_base r r' :
    bref_base r = bref_base r' → bref_size r = bref_size r'.
  Proof.
    intros Hr. by rewrite <-(bref_size_base r), <-(bref_size_base r'), Hr.
  Qed.

  Lemma bref_eq r1 r2 :
    bref_base r1 = bref_base r2 → bref_offset r1 = bref_offset r2 → r1 = r2.
  Proof.
    destruct r1 as [|r1 i1 n1], r2 as [|r2 i2 n2];
      simpl; intros ? Hoff; simplify_equality.
    * f_equal. by apply ref_eq.
    * destruct (mult_split_eq n2 (ref_offset r1) i1
        (ref_offset r2) i2); try congruence; auto using ref_eq with f_equal.
  Qed.

  Lemma bref_base_typed τ r σ : τ ∙ r ↝ σ → τ ∙ bref_base r ↝ σ.
  Proof.
    destruct 1; repeat econstructor; eauto using ref_base_typed with lia.
  Qed.
  Lemma bref_offset_size r : bref_offset r < bref_size r.
  Proof.
    assert (∀ n i x y, i < n → x < y → x * n + i < y * n).
    { intros. assert (exists j, y = x + j /\ 0 < j) as (j&?&?)
        by (exists (y - x); lia); subst.
      rewrite NPeano.Nat.mul_add_distr_r, <-(NPeano.Nat.mul_1_l i).
      apply NPeano.Nat.add_lt_mono_l. apply NPeano.Nat.le_lt_trans with (j * i),
        NPeano.Nat.mul_lt_mono_pos_l; try lia.
      apply NPeano.Nat.mul_le_mono; lia. }
    destruct r; simpl; subst; eauto using ref_offset_size.
  Qed.
  Lemma bref_offset_size_alt r : (bref_offset r < bref_size r)%Z.
  Proof. apply Nat2Z.inj_lt, bref_offset_size. Qed.

  Lemma bref_typed_alt τ r σ : τ ∙ r ↝ σ ↔ τ ∙ bref_base r ↝ σ.
  Proof.
    split.
    * eauto using bref_base_typed.
    * destruct r; inversion 1; subst; econstructor; eauto;
        eapply ref_typed_alt; eauto.
  Qed.

  Lemma bref_base_freeze r : bref_base (freeze r) = freeze (bref_base r).
  Proof. destruct r; simpl; f_equal; apply ref_base_freeze. Qed.
  Lemma bref_offset_freeze r : bref_offset (freeze r) = bref_offset r.
  Proof. by destruct r; simpl; rewrite ref_offset_freeze. Qed.
  Lemma bref_size_freeze r : bref_size (freeze r) = bref_size r.
  Proof. by destruct r; simpl; rewrite ref_size_freeze. Qed.
  Lemma bref_plus_freeze r i :
    bref_plus (freeze r) i = freeze <$> bref_plus r i.
  Proof.
    by destruct r; simpl; rewrite ref_plus_freeze; destruct (ref_plus _ _).
  Qed.
  Lemma bref_minus_freeze_l r1 r2 :
    bref_minus (freeze r1) r2 = bref_minus r1 r2.
  Proof. by destruct r1, r2; simpl; rewrite ?ref_minus_freeze_l. Qed.
  Lemma bref_minus_freeze_r r1 r2 :
    bref_minus r1 (freeze r2) = bref_minus r1 r2.
  Proof. by destruct r1, r2; simpl; rewrite ?ref_minus_freeze_r. Qed.
  Lemma bref_minus_freeze r1 r2 :
    bref_minus (freeze r1) (freeze r2) = bref_minus r1 r2.
  Proof. by rewrite bref_minus_freeze_l, bref_minus_freeze_r. Qed.

  Lemma bref_base_plus r i r' :
    bref_plus r i = Some r' → bref_base r' = bref_base r.
  Proof.
    intros. destruct r; simplify_option_equality;
      eauto using ref_base_plus with f_equal.
  Qed.
  Lemma bref_size_plus r i r' :
    bref_plus r i = Some r' → bref_size r' = bref_size r.
  Proof.
    intros. destruct r; simplify_option_equality; eauto using ref_size_plus.
  Qed.

  Lemma bref_offset_plus r i r' :
    bref_plus r i = Some r' → Z.of_nat (bref_offset r') = (bref_offset r + i)%Z.
  Proof.
    intros. destruct r as [|o j n]; simplify_option_equality.
    { auto using ref_offset_plus. }
    zify. erewrite ref_offset_plus by eauto.
    rewrite Z.mul_add_distr_r, <-!Z.add_assoc, Z2Nat.id by auto with zpos.
    rewrite (Z.mul_comm (_ `div` _) n), <-Z.div_mod; lia.
  Qed.
  Lemma bref_offset_plus_range r i r' :
    bref_plus r i = Some r' → (0 ≤ bref_offset r + i < bref_size r)%Z.
  Proof.
    intros. rewrite <-(bref_offset_plus _ _ r'), <-(bref_size_plus r i r');
      auto using bref_offset_size_alt with lia.
  Qed.
  Lemma bref_plus_is_Some r i :
    is_Some (bref_plus r i) ↔ (0 ≤ bref_offset r + i < bref_size r)%Z.
  Proof.
    split.
    { intros [??]. eauto using bref_offset_plus_range. }
    intros [??]. destruct r as [o|o j n]; simpl.
    { apply fmap_is_Some. by apply (proj2 (ref_plus_is_Some o i)). }
    destruct (proj2 (ref_plus_is_Some o ((j + i) `div` n)));
      simplify_option_equality; eauto.
    split.
    * apply Z.le_sub_le_add_l, Z.div_le_lower_bound; lia.
    * apply Z.lt_add_lt_sub_l, Z.div_lt_upper_bound; lia.
  Qed.

  Lemma bref_plus_Some_2 r i r' :
    (0 ≤ bref_offset r + i < bref_size r)%Z → bref_base r = bref_base r' →
    Z.of_nat (bref_offset r') = (bref_offset r + i)%Z → bref_plus r i = Some r'.
  Proof.
    destruct r as [r1|r1 i1 n1], r' as [r2|r2 i2 n2]; simpl;
      intros ???; simplify_equality.
    { by rewrite (ref_plus_Some_2 r1 _ r2). }
    assert (i1 + i = i2 + (ref_offset r2 - ref_offset r1) * n2)%Z as E by lia.
    rewrite (ref_plus_Some_2 r1 _ r2); split_ands.
    * simpl. f_equal. apply RByte_eq; auto.
      rewrite E, Z.mod_add, Z.mod_small, Nat2Z.id; lia.
    * apply Z.le_sub_le_add_l, Z.div_le_lower_bound; lia.
    * erewrite ref_size_same_base by eassumption.
      pose proof (ref_offset_size_alt r2).
      rewrite E, Z.div_add, Z.div_small; lia.
    * done.
    * rewrite E, Z.div_add, Z.div_small; lia.
  Qed.
  Lemma bref_plus_Some r i r' :
    bref_plus r i = Some r' ↔
      (0 ≤ bref_offset r + i < bref_size r)%Z ∧  bref_base r' = bref_base r ∧
      Z.of_nat (bref_offset r') = (bref_offset r + i)%Z.
  Proof.
    split.
    * eauto 6 using bref_base_plus, bref_offset_plus, bref_offset_plus_range.
    * intros [[??] [??]]. eauto using bref_plus_Some_2.
  Qed.

  Lemma bref_plus_typed τ r σ i r' :
    τ ∙ r ↝ σ → bref_plus r i = Some r' → τ ∙ r' ↝ σ.
  Proof.
    destruct 1; intros; simplify_option_equality;
      econstructor; eauto using ref_plus_typed.
  Qed.

  Lemma bref_plus_base_offset r :
    bref_plus (bref_base r) (bref_offset r) = Some r.
  Proof.
    apply bref_plus_Some_2.
    * rewrite bref_offset_base, bref_size_base.
      pose proof (bref_offset_size r). lia.
    * by rewrite !bref_base_idempotent.
    * rewrite bref_offset_base. lia.
  Qed.

  Lemma bref_minus_Some_2 r1 r2 j :
    bref_base (freeze r1) = bref_base (freeze r2) →
    j = (bref_offset r1 - bref_offset r2)%Z →
    bref_minus r1 r2 = Some j.
  Proof.
    destruct r1, r2; intros; simplify_option_equality.
    * eauto using ref_minus_Some_2.
    * erewrite ref_minus_Some_2 by eauto. simpl. f_equal. lia.
  Qed.
  Lemma bref_minus_Some_base r1 r2 j :
    bref_minus r1 r2 = Some j → bref_base (freeze r1) = bref_base (freeze r2).
  Proof.
    destruct r1, r2; intros; simplify_option_equality;
      eauto using ref_minus_Some_base with f_equal.
  Qed.
  Lemma bref_minus_Some_offset r1 r2 j :
    bref_minus r1 r2 = Some j →  j = (bref_offset r1 - bref_offset r2)%Z.
  Proof.
    destruct r1, r2; intros; simplify_option_equality.
    * eauto using ref_minus_Some_offset.
    * efeed pose proof ref_minus_Some_offset; eauto. subst. lia.
  Qed.
  Lemma bref_minus_Some r1 r2 j :
    bref_minus r1 r2 = Some j ↔
      bref_base (freeze r1) = bref_base (freeze r2) ∧
      j = (bref_offset r1 - bref_offset r2)%Z.
  Proof.
    intuition eauto using bref_minus_Some_2,
      bref_minus_Some_base, bref_minus_Some_offset.
  Qed.
  Lemma bref_minus_plus r1 r2 i :
    bref_minus r2 r1 = Some i → bref_plus (freeze r1) i = Some (freeze r2).
  Proof.
    rewrite bref_minus_Some. intros [Hr ?]. subst. apply bref_plus_Some_2.
    * erewrite <-bref_size_same_base by eassumption.
      rewrite !bref_offset_freeze, !bref_size_freeze.
      pose proof (bref_offset_size_alt r2). lia.
    * done.
    * rewrite !bref_offset_freeze. lia.   
  Qed.
End bref.
