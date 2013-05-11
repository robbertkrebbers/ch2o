(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export pointers.

Inductive byte' (Ti C : Set) :=
  | BUndef : byte' Ti C
  | BChar : C → byte' Ti C
  | BPtrSeg : ptr_seg Ti → byte' Ti C.
Notation byte Ti Vi := (byte' Ti (char Ti Vi)).
Arguments BUndef {_ _}.
Arguments BChar {_ _} _.
Arguments BPtrSeg {_ _} _.

Instance byte_eq_dec {Ti C : Set}
  `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)} `{∀ c1 c2 : C, Decision (c1 = c2)}
  (b1 b2 : byte' Ti C) : Decision (b1 = b2).
Proof. solve_decision. Defined.

Definition maybe_BChar {Ti C} (b : byte' Ti C) : option C :=
  match b with BChar c => Some c | _ => None end.
Definition maybe_BPtrSeg {Ti C} (b : byte' Ti C) : option (ptr_seg Ti) :=
  match b with BPtrSeg ps => Some ps | _ => None end.

Global Instance: Injective (=) (=) (@BChar Ti C).
Proof. by injection 1. Qed.
Global Instance: Injective (=) (=) (@BPtrSeg Ti C).
Proof. by injection 1. Qed.

Inductive byte_valid `{PtrEnv Ti} `{IntEnv Ti Vi} `{TypeOfIndex Ti M}
    (m : M) : byte Ti Vi → Prop :=
  | BUndef_valid : byte_valid m BUndef
  | BChar_valid c : byte_valid m (BChar c)
  | BPtrSeg_valid (ps : ptr_seg Ti) :
     ptr_seg_valid m ps → byte_valid m (BPtrSeg ps).

Inductive byte_le' `{PtrEnv Ti} `{IntEnv Ti Vi} `{TypeOfIndex Ti M}
    (m : M) : relation (byte Ti Vi) :=
  | BUndef_le' b : byte_valid m b → byte_le' m BUndef b
  | byte_le_refl b : byte_le' m b b.
Instance byte_le `{PtrEnv Ti} `{IntEnv Ti Vi} `{TypeOfIndex Ti M} :
  SubsetEqEnv M (byte Ti Vi) := byte_le'.

Definition base_undef_bytes `{IntEnv Ti Vi} `{PtrEnv Ti} (τ : base_type Ti) :
  list (byte Ti Vi) := replicate (size_of (base τ)) BUndef.
Arguments base_undef_bytes _ _ _ _ !_ /.

Definition array_of_bytes `{PtrEnv Ti} `(f : list (byte' Ti C) → A)
    (τ : type Ti) : nat → list (byte' Ti C) → list A :=
  let sz := size_of τ in
  fix go n bs :=
  match n with
  | 0 => []
  | S n => f bs :: go n (drop sz bs)
  end.
Definition struct_of_bytes_aux `(f : type Ti → list (byte' Ti C) → A) :
    list (nat * type Ti) → list (byte' Ti C) → list A :=
  fix go τns bs :=
  match τns with
  | [] => []
  | (sz,τ) :: τns => f τ bs :: go τns (drop sz bs)
  end.
Definition struct_of_bytes `{PtrEnv Ti} `(f : type Ti → list (byte' Ti C) → A)
    (τs : list (type Ti)) : list (byte' Ti C) → list A :=
  struct_of_bytes_aux f (zip (struct_fields τs) τs).

Definition mask_byte {Ti C} (bm b : byte' Ti C) :=
  match bm with BUndef => BUndef | _ => b end.
Fixpoint mask_bytes {Ti C} (bms bs : list (byte' Ti C)) :=
  match bms, bs with
  | [], bs => bs
  | bms, [] => []
  | bm :: bms, b :: bs => mask_byte bm b :: mask_bytes bms bs
  end.

Section byte_join.
  Context {Ti C : Set}.
  Context `{∀ τ1 τ2 : Ti, Decision (τ1 = τ2)}.
  Context `{∀ c1 c2 : C, Decision (c1 = c2)}.

  Definition byte_join (b1 b2 : byte' Ti C) : option (byte' Ti C) :=
    match b1, b2 with
    | BUndef, b2 => Some b2
    | b1, BUndef => Some b1
    | b1, b2 => guard (b1 = b2); Some b1
    end.
  Fixpoint bytes_join (bs1 bs2 : list (byte' Ti C)) :
      option (list (byte' Ti C)) :=
    match bs1, bs2 with
    | [], [] => Some []
    | b1 :: bs1, b2 :: bs2 =>
       b3 ← byte_join b1 b2;
       bs3 ← bytes_join bs1 bs2;
       Some (b3 :: bs3)
    | _, _ => None
   end.
End byte_join.

Section byte.
  Context `{EnvSpec Ti Vi} `{TypeOfIndex Ti M}.
  Implicit Types m : M.
  Implicit Types b : byte Ti Vi.
  Implicit Types bs : list (byte Ti Vi).

  Global Instance byte_valid_dec m b : Decision (byte_valid m b).
  Proof.
   refine
    match b with
    | BUndef => left _
    | BChar _ => left _
    | BPtrSeg ps => cast_if (decide (ptr_seg_valid m ps))
    end; first [by constructor | abstract by inversion 1].
  Defined.

  Lemma BUndef_le m b : byte_valid m b → BUndef ⊑@{m} b.
  Proof. by constructor. Qed.
  Lemma Forall_BUndef_le m bs :
    Forall (byte_valid m) bs → Forall (subseteq_env m BUndef) bs.
  Proof. induction 1; constructor; auto using BUndef_le. Qed.
  Lemma byte_valid_ge m b1 b2 : byte_valid m b1 → b1 ⊑@{m} b2 → byte_valid m b2.
  Proof. by destruct 1; inversion 1; subst; try constructor. Qed.
  Lemma byte_valid_le m b1 b2 : byte_valid m b2 → b1 ⊑@{m} b2 → byte_valid m b1.
  Proof. by destruct 1; inversion 1; subst; try constructor. Qed.

  Lemma bytes_valid_ge m bs1 bs2 :
    Forall (byte_valid m) bs1 → bs1 ⊑@{m}* bs2 → Forall (byte_valid m) bs2.
  Proof.
    intros Hbs1 Hbs. induction Hbs; decompose_Forall; eauto using byte_valid_ge.
  Qed.
  Lemma bytes_valid_le m bs1 bs2 :
    Forall (byte_valid m) bs2 → bs1 ⊑@{m}* bs2 → Forall (byte_valid m) bs1.
  Proof.
    intros Hbs1 Hbs. induction Hbs; decompose_Forall; eauto using byte_valid_le.
  Qed.

  Lemma BPtrSeg_valid_inv m ps : byte_valid m (BPtrSeg ps) → ptr_seg_valid m ps.
  Proof. by inversion 1. Qed.

  Global Instance: PartialOrder (@subseteq_env M (byte Ti Vi) _ m).
  Proof.
    intros m. repeat split.
    * intro. constructor.
    * by do 2 destruct 1; constructor.
    * by destruct 1; inversion_clear 1.
  Qed.

  Lemma base_undef_bytes_valid m τ : Forall (byte_valid m) (base_undef_bytes τ).
  Proof. intros. apply Forall_replicate. by constructor. Qed.

  Lemma base_undef_bytes_le m τ bs :
    Forall (byte_valid m) bs → length bs = size_of (base τ) →
    base_undef_bytes τ ⊑@{m}* bs.
  Proof.
    intros. apply Forall2_replicate_l.
    * eapply Forall_impl; eauto. by constructor.
    * done.
  Qed.

  Lemma bytes_le_inv m bs1 bs2 :
    bs1 ⊑@{m}* bs2 →
    bs1 = bs2 ∨ ∃ i, bs1 !! i = Some BUndef ∧ bs2 !! i ≠ Some BUndef.
  Proof.
    induction 1 as [|b1 b2 bs1 bs2 Hb Hbs [?|[i ?]]]; [by left | |]; subst.
    * destruct Hb as [[]|b]; first [by left | by right; exists 0].
    * right. by exists (S i).
  Qed.

  Lemma bytes_le_eq_or_undef m bs1 bs2 :
    bs1 ⊑@{m}* bs2 → bs1 = bs2 ∨ BUndef ∈ bs1.
  Proof.
    intros. destruct (bytes_le_inv m bs1 bs2) as [? | [? [??]]];
      eauto using elem_of_list_lookup_2.
  Qed.
  Lemma bytes_le_no_undef m bs1 bs2 :
    bs1 ⊑@{m}* bs2 → BUndef ∉ bs1 → bs1 = bs2.
  Proof. intros. by edestruct bytes_le_eq_or_undef; eauto. Qed.
  Lemma bytes_le_undef m bs1 bs2 :
    BUndef ∈ bs1 → bs2 ⊑@{m}* bs1 → BUndef ∈ bs2.
  Proof. intros. edestruct bytes_le_eq_or_undef; eauto. by subst. Qed.

  Lemma bytes_le_resize m bs1 bs2 n :
    bs1 ⊑@{m}* bs2 → resize n BUndef bs1 ⊑@{m}* resize n BUndef bs2.
  Proof. by apply Forall2_resize. Qed.

  Lemma mask_byte_le m bm b : byte_valid m b → mask_byte bm b ⊑@{m} b.
  Proof. by destruct bm; constructor. Qed.
  Lemma mask_byte_not_undef bm b : bm ≠ BUndef → mask_byte bm b = b.
  Proof. by destruct bm. Qed.
  Lemma mask_byte_valid m bm b : byte_valid m b → byte_valid m (mask_byte bm b).
  Proof. destruct bm; simpl; auto using BUndef_valid. Qed.

  Lemma mask_bytes_length bms bs : length (mask_bytes bms bs) = length bs.
  Proof. revert bms. induction bs; intros [|??]; simpl; f_equal; auto. Qed.
  Lemma mask_bytes_le m bms bs :
    Forall (byte_valid m) bs → mask_bytes bms bs ⊑@{m}* bs.
  Proof.
    intros Hbs. revert bms.
    by induction Hbs; intros [|??]; simpl; constructor; auto using mask_byte_le.
  Qed.
  Lemma mask_bytes_undef bms bs :
    bms `same_length` bs → BUndef ∈ bms → BUndef ∈ mask_bytes bms bs.
  Proof.
    induction 1; simpl; try by rewrite elem_of_nil.
    rewrite !elem_of_cons. intros [?|?]; subst; auto.
  Qed.
  Lemma mask_bytes_no_undef bms bs : BUndef ∉ bms → mask_bytes bms bs = bs.
  Proof.
    revert bms. induction bs; intros [|??]; simpl; auto.
    rewrite not_elem_of_cons. intros [??].
    f_equal; auto using mask_byte_not_undef.
  Qed.
  Lemma mask_bytes_valid m bms bs :
    Forall (byte_valid m) bs → Forall (byte_valid m) (mask_bytes bms bs).
  Proof.
    intros Hbs. revert bms.
    induction Hbs; intros [|??]; simpl; auto using mask_byte_valid.
  Qed. 

  Lemma mask_bytes_take bms bs n :
    take n (mask_bytes bms bs) = mask_bytes (take n bms) (take n bs).
  Proof.
    revert n bms. induction bs; intros [|?] [|??]; simpl; f_equal; auto.
  Qed.
  Lemma mask_bytes_drop bms bs n :
    drop n (mask_bytes bms bs) = mask_bytes (drop n bms) (drop n bs).
  Proof.
    revert n bms. induction bs; intros [|n] [|? l]; simpl; f_equal; auto.
    by destruct (drop n l).
  Qed.

  Section array_of_bytes.
  Context `(f : list (byte Ti Vi) → A).

  Lemma array_of_bytes_ext g τ n bs :
    (∀ bs, f bs = g bs) → array_of_bytes f τ n bs = array_of_bytes g τ n bs.
  Proof. revert bs; induction n; intros; simpl; f_equal; auto. Qed.

  Lemma array_of_bytes_length τ n bs : length (array_of_bytes f τ n bs) = n.
  Proof. revert bs. induction n; simpl; auto. Qed.

  Lemma Forall_array_of_bytes (P : A → Prop) τ n bs :
    (∀ bs, P (f bs)) → Forall P (array_of_bytes f τ n bs).
  Proof. revert bs. induction n; simpl; auto. Qed.
  Lemma Forall_array_of_bytes_alt (Q: byte Ti Vi → Prop) (P: A → Prop) τ n bs :
    Forall Q bs → (∀ bs, Forall Q bs → P (f bs)) →
    Forall P (array_of_bytes f τ n bs).
  Proof.
    revert bs. induction n; simpl; intros bs Hbs Hf; auto using Forall_drop.
  Qed.

  Lemma array_of_bytes_fmap {B} (g : list (byte Ti Vi) → B) h τ n bs :
    (∀ bs, h (f bs) = g bs) →
    h <$> array_of_bytes f τ n bs = array_of_bytes g τ n bs.
  Proof. intros Hf. revert bs. induction n; simpl; intros; f_equal; auto. Qed.

  Lemma array_of_bytes_resize τ n bs sz :
    (∀ bs sz, size_of τ ≤ sz → f (resize sz BUndef bs) = f bs) →
    n * size_of τ ≤ sz →
    array_of_bytes f τ n (resize sz BUndef bs) = array_of_bytes f τ n bs.
  Proof.
    intros Hf. revert sz bs. induction n; intros; simpl in *; f_equal;
      rewrite ?drop_resize_le; auto with lia.
  Qed.

  Lemma array_of_bytes_masked m τ n bs1 bs2 cs2 :
    (∀ bs1 bs2 cs2,
      bs1 ⊑@{m}* bs2 →  Forall (byte_valid m) cs2 →
      f bs2 = f cs2 → f (mask_bytes bs1 cs2) = f bs1) →
    bs1 ⊑@{m}* bs2 → Forall (byte_valid m) cs2 →
    array_of_bytes f τ n bs2 = array_of_bytes f τ n cs2 →
    array_of_bytes f τ n (mask_bytes bs1 cs2) = array_of_bytes f τ n bs1.
  Proof.
    intros Hf. revert bs1 bs2 cs2.
    induction n; simpl; intros; simplify_equality; f_equal; [eauto |].
    rewrite mask_bytes_drop. eauto using Forall2_drop,
      same_length_drop, Forall_drop.
  Qed.
  End array_of_bytes.

  Section struct_of_bytes.
  Context `(f : type Ti → list (byte Ti Vi) → A).

  Lemma struct_of_bytes_ext g τs bs :
    Forall (λ τ, pointwise_relation (list (byte Ti Vi)) (=) (f τ) (g τ)) τs →
    struct_of_bytes f τs bs = struct_of_bytes g τs bs.
  Proof.
    unfold struct_of_bytes. intros Hfg. revert bs.
    generalize (struct_fields τs).
    induction Hfg; intros [|??] ?; simpl; f_equal; auto.
  Qed.

  Lemma Forall2_struct_of_bytes (P : A → type Ti → Prop) τs bs :
    Forall (λ τ, ∀ bs, P (f τ bs) τ) τs →
    Forall2 P (struct_of_bytes f τs bs) τs.
  Proof.
    unfold struct_of_bytes. revert bs. induction (size_of_struct_fields τs);
      intros; decompose_Forall; simpl; constructor; auto.
  Qed.
  Lemma Forall2_struct_of_bytes_alt (Q : byte Ti Vi → Prop)
      (P : A → type Ti → Prop) τs bs :
    Forall Q bs → Forall (λ τ, ∀ bs, Forall Q bs → P (f τ bs) τ) τs →
    Forall2 P (struct_of_bytes f τs bs) τs.
  Proof.
    unfold struct_of_bytes. revert bs. induction (size_of_struct_fields τs);
      intros; decompose_Forall; simpl; constructor; auto using Forall_drop.
  Qed.

  Lemma Forall_struct_of_bytes (P : A → Prop) τs bs :
    Forall (λ τ, ∀ bs, P (f τ bs)) τs → Forall P (struct_of_bytes f τs bs).
  Proof.
    unfold struct_of_bytes. intros Hf. revert bs. generalize (struct_fields τs).
    induction Hf; intros [|??] ?; simpl; auto.
  Qed.
  Lemma Forall_struct_of_bytes_alt (Q: byte Ti Vi → Prop) (P: A → Prop) τs bs :
    Forall Q bs → Forall (λ τ, ∀ bs, Forall Q bs → P (f τ bs)) τs →
    Forall P (struct_of_bytes f τs bs).
  Proof.
    unfold struct_of_bytes. intros Hbs Hf. revert bs Hbs.
    generalize (struct_fields τs).
    induction Hf; intros [|??] ?; simpl; auto using Forall_drop.
  Qed.

  Lemma struct_of_bytes_fmap `(g : type Ti → list (byte Ti Vi) → B) h τs bs :
    Forall (λ τ, ∀ bs, h (f τ bs) = g τ bs) τs →
    h <$> struct_of_bytes f τs bs = struct_of_bytes g τs bs.
  Proof.
    unfold struct_of_bytes. intros Hf. revert bs.
    generalize (struct_fields τs).
    induction Hf; intros [|??] ?; simpl; simplify_equality; f_equal; auto.
  Qed.

  Lemma struct_of_bytes_resize τs bs sz :
    Forall (λ τ, ∀ bs sz, size_of τ ≤ sz →
      f τ (resize sz BUndef bs) = f τ bs) τs →
    sum_list (struct_fields τs) ≤ sz →
    struct_of_bytes f τs (resize sz BUndef bs) = struct_of_bytes f τs bs.
  Proof.
    unfold struct_of_bytes. revert sz bs.
    induction (size_of_struct_fields τs) as [|τ sz τs ??? IH];
      intros; simpl in *; decompose_Forall; f_equal;
      rewrite ?drop_resize_le; auto with lia.
  Qed.

  Lemma struct_of_bytes_masked m τs bs1 bs2 cs2 :
    Forall (λ τ, ∀ bs1 bs2 cs2,
      bs1 ⊑@{m}* bs2 →  Forall (byte_valid m) cs2 →
      f τ bs2 = f τ cs2 → f τ (mask_bytes bs1 cs2) = f τ bs1) τs →
    bs1 ⊑@{m}* bs2 →
    Forall (byte_valid m) cs2 →
    struct_of_bytes f τs bs2 = struct_of_bytes f τs cs2 →
    struct_of_bytes f τs (mask_bytes bs1 cs2) = struct_of_bytes f τs bs1.
  Proof.
    unfold struct_of_bytes. intros Hf. revert bs1 bs2 cs2.
    generalize (struct_fields τs). induction Hf; intros [|??] ??????; simpl;
      simplify_equality; f_equal; [eauto |].
    rewrite mask_bytes_drop.
    eauto using Forall2_drop, same_length_drop, Forall_drop.
  Qed.
  End struct_of_bytes.

  Global Instance: Commutative (@eq (option (byte Ti Vi))) byte_join.
  Proof. intros [] []; intros; simplify_option_equality; auto. Qed.
  Lemma byte_join_undef_l b : byte_join BUndef b = Some b.
  Proof. by destruct b; simplify_option_equality. Qed.
  Lemma byte_join_undef_r b : byte_join b BUndef = Some b.
  Proof. by destruct b; simplify_option_equality. Qed.
  Lemma byte_join_diag b : byte_join b b = Some b.
  Proof. by destruct b; simplify_option_equality. Qed.

  Lemma byte_join_Some_l m b1 b2 b3 :
    byte_valid m b1 → byte_valid m b2 → byte_join b1 b2 = Some b3 → b1 ⊑@{m} b3.
  Proof.
    by destruct 1, 1; intros; simplify_option_equality; repeat constructor.
  Qed.
  Lemma byte_join_Some_r m b1 b2 b3 :
    byte_valid m b1 → byte_valid m b2 → byte_join b1 b2 = Some b3 → b2 ⊑@{m} b3.
  Proof. by destruct b1, b2; intros; simplify_option_equality; constructor. Qed.
  Lemma byte_join_Some m b1 b2 b3 :
    byte_valid m b1 → byte_valid m b2 → byte_join b1 b2 = Some b3 →
    b1 ⊑@{m} b3 ∧ b2 ⊑@{m} b3.
  Proof. eauto using byte_join_Some_l, byte_join_Some_r. Qed.

  Lemma byte_join_min m b1 b2 b3 b4:
    byte_join b1 b2 = Some b3 → b1 ⊑@{m} b4 → b2 ⊑@{m} b4 → b3 ⊑@{m} b4.
  Proof. destruct b1, b2; intros; simplify_option_equality; auto. Qed.
  Lemma byte_join_exists m b1 b2 b4 :
    b1 ⊑@{m} b4 → b2 ⊑@{m} b4 → ∃ b3, byte_join b1 b2 = Some b3 ∧ b3 ⊑@{m} b4.
  Proof.
    destruct 1; inversion_clear 1; simpl; eauto using byte_join_undef_l,
      byte_join_undef_r, byte_join_diag.
    by repeat econstructor.
  Qed.

  Global Instance: Commutative (@eq (option (list (byte Ti Vi)))) bytes_join.
  Proof.
    intros bs1.
    induction bs1 as [|b1 bs1 IH]; intros [|b2 bs2]; simpl; try done.
    rewrite (commutative byte_join).
    destruct (byte_join _ _); simpl; try done. by rewrite IH.
  Qed.

  Lemma bytes_join_undef_l bs :
    bytes_join (replicate (length bs) BUndef) bs = Some bs.
  Proof. induction bs as [|b bs IH]; simpl; [done|]. by rewrite IH. Qed.
  Lemma bytes_join_undef_r bs :
    bytes_join bs (replicate (length bs) BUndef) = Some bs.
  Proof. rewrite (commutative bytes_join). apply bytes_join_undef_l. Qed.
  Lemma bytes_join_diag bs : bytes_join bs bs = Some bs.
  Proof.
    induction bs as [|b bs IH]; simpl; [done|].
    rewrite byte_join_diag; simpl. by rewrite IH.
  Qed.

  Lemma bytes_join_Some_l m bs1 bs2 bs3 :
    Forall (byte_valid m) bs1 → Forall (byte_valid m) bs2 →
    bytes_join bs1 bs2 = Some bs3 → bs1 ⊑@{m}* bs3.
  Proof.
    intros Hbs1. revert bs2 bs3.
    induction Hbs1 as [|b1 bs1 IH]; intros ?? [|???] ?;
      simplify_option_equality; constructor; eauto using byte_join_Some_l.
  Qed.
  Lemma bytes_join_Some_r m bs1 bs2 bs3 :
    Forall (byte_valid m) bs1 → Forall (byte_valid m) bs2 →
    bytes_join bs1 bs2 = Some bs3 → bs2 ⊑@{m}* bs3.
  Proof.
    intros. apply bytes_join_Some_l with bs1; auto.
    by rewrite (commutative bytes_join).
  Qed.
  Lemma bytes_join_Some m bs1 bs2 bs3 :
    Forall (byte_valid m) bs1 → Forall (byte_valid m) bs2 →
    bytes_join bs1 bs2 = Some bs3 → bs1 ⊑@{m}* bs3 ∧ bs2 ⊑@{m}* bs3.
  Proof. eauto using bytes_join_Some_l, bytes_join_Some_r. Qed.

  Lemma bytes_join_min m bs1 bs2 bs3 bs4 :
    bytes_join bs1 bs2 = Some bs3 →
    bs1 ⊑@{m}* bs4 → bs2 ⊑@{m}* bs4 → bs3 ⊑@{m}* bs4.
  Proof.
    intros Hbs3 Hbs1 Hbs2. revert bs2 bs3 Hbs2 Hbs3.
    induction Hbs1; intros; decompose_Forall; simplify_option_equality;
      constructor; eauto using byte_join_min.
  Qed.

  Lemma bytes_join_exists m bs1 bs2 bs4 :
    bs1 ⊑@{m}* bs4 → bs2 ⊑@{m}* bs4 →
    ∃ bs3, bytes_join bs1 bs2 = Some bs3 ∧ bs3 ⊑@{m}* bs4.
  Proof.
    intros Hbs1. revert bs2.
    induction Hbs1 as [|b1 b4 bs1 bs4 ?? IH]; inversion_clear 1 as [|b2].
    * by eexists [].
    * edestruct IH as (?&Hbs2&?); eauto.
      edestruct (byte_join_exists m b1 b2 b4) as (?&Hb2&?); eauto.
      simpl. rewrite Hbs2. simpl. rewrite Hb2. simpl. eauto.
  Qed.

  Lemma bytes_join_length_l bs1 bs2 bs3 :
    bytes_join bs1 bs2 = Some bs3 → length bs3 = length bs1.
  Proof.
    revert bs2 bs3. induction bs1; intros [|??] ??;
      simplify_option_equality; f_equal; eauto.
  Qed.
  Lemma bytes_join_length_r bs1 bs2 bs3 :
    bytes_join bs1 bs2 = Some bs3 → length bs3 = length bs2.
  Proof. rewrite (commutative bytes_join). apply bytes_join_length_l. Qed.
End byte.
