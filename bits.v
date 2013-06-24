(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export pointers.

Inductive bit (Ti : Set) :=
  | BIndet : bit Ti
  | BBit : bool → bit Ti
  | BPtr : ptr_bit Ti → bit Ti.
Arguments BIndet {_}.
Arguments BBit {_} _.
Arguments BPtr {_} _.

Instance bit_eq_dec {Ti : Set} `{∀ k1 k2 : Ti, Decision (k1 = k2)}
  (b1 b2 : bit Ti) : Decision (b1 = b2).
Proof. solve_decision. Defined.

Definition maybe_BBit {Ti} (b : bit Ti) : option bool :=
  match b with BBit c => Some c | _ => None end.
Definition maybe_BPtr {Ti} (b : bit Ti) : option (ptr_bit Ti) :=
  match b with BPtr ps => Some ps | _ => None end.

Global Instance: Injective (=) (=) (@BBit Ti).
Proof. by injection 1. Qed.
Global Instance: Injective (=) (=) (@BPtr Ti).
Proof. by injection 1. Qed.

Section operations.
  Context `{MemorySpec Ti M}.

  Inductive bit_valid' (m : M) : bit Ti → Prop :=
    | BIndet_valid' : bit_valid' m BIndet
    | BBit_valid' β : bit_valid' m (BBit β)
    | BPtr_valid' ps : m ⊢ valid ps → bit_valid' m (BPtr ps).
  Global Instance bit_valid: Valid M (bit Ti) := bit_valid'.

  Inductive bit_le' (m : M) : relation (bit Ti) :=
    | BIndet_le' b : m ⊢ valid b → bit_le' m BIndet b
    | bit_le_refl b : bit_le' m b b.
  Global Instance bit_le: SubsetEqEnv M (bit Ti) := bit_le'.

  Definition base_indet_bits (τ : base_type Ti) : list (bit Ti) :=
    replicate (bit_size_of (base τ)) BIndet.
  Global Arguments base_indet_bits !_ /.

  Definition array_of_bits {A} (f : list (bit Ti) → A)
      (τ : type Ti) : nat → list (bit Ti) → list A :=
    let sz := bit_size_of τ in
    fix go n bs :=
    match n with
    | 0 => []
    | S n => f bs :: go n (drop sz bs)
    end.
  Definition struct_of_bits_aux {A} (f : type Ti → list (bit Ti) → A) :
      list (nat * type Ti) → list (bit Ti) → list A :=
    fix go τns bs :=
    match τns with
    | [] => []
    | (sz,τ) :: τns => f τ bs :: go τns (drop sz bs)
    end.
  Definition struct_of_bits {A} (f : type Ti → list (bit Ti) → A)
      (τs : list (type Ti)) : list (bit Ti) → list A :=
    struct_of_bits_aux f (zip (field_bit_sizes τs) τs).

  Definition mask_bit (bm b : bit Ti) : bit Ti :=
    match bm with BIndet => BIndet | _ => b end.
  Fixpoint mask_bits (bms bs : list (bit Ti)) : list (bit Ti) :=
    match bms, bs with
    | [], bs => []
    | bms, [] => replicate (length bms) BIndet
    | bm :: bms, b :: bs => mask_bit bm b :: mask_bits bms bs
    end.

  Definition bit_join (b1 b2 : bit Ti) : option (bit Ti) :=
    match b1, b2 with
    | BIndet, b2 => Some b2
    | b1, BIndet => Some b1
    | b1, b2 => guard (b1 = b2); Some b1
    end.
  Fixpoint bits_join (bs1 bs2 : list (bit Ti)) : option (list (bit Ti)) :=
    match bs1, bs2 with
    | [], [] => Some []
    | b1 :: bs1, b2 :: bs2 =>
       b3 ← bit_join b1 b2;
       bs3 ← bits_join bs1 bs2;
       Some (b3 :: bs3)
    | _, _ => None
    end.
End operations.

Section properties.
Context `{MemorySpec Ti M}.
Implicit Types m : M.
Implicit Types b bm : bit Ti.
Implicit Types bs bms : list (bit Ti).

Lemma BIndet_valid m : m ⊢ valid BIndet.
Proof. constructor. Qed.
Lemma BBit_valid m β : m ⊢ valid (BBit β).
Proof. by constructor. Qed.
Lemma BPtr_valid m ps : m ⊢ valid ps → m ⊢ valid (BPtr ps).
Proof. by constructor. Qed.
Lemma BPtr_valid_inv m ps : m ⊢ valid (BPtr ps) → m ⊢ valid ps.
Proof. by inversion 1. Qed.

Global Instance bit_valid_dec m b : Decision (m ⊢ valid b).
Proof.
 refine
  match b with
  | BIndet => left _
  | BBit _ => left _
  | BPtr ps => cast_if (decide (m ⊢ valid ps))
  end; first [by constructor | abstract by inversion 1].
Defined.

Lemma BIndet_le m b : m ⊢ valid b → BIndet ⊑@{m} b.
Proof. by constructor. Qed.
Lemma Forall_BIndet_le m bs : m ⊢* valid bs → Forall (subseteq_env m BIndet) bs.
Proof. induction 1; constructor; auto using BIndet_le. Qed.
Lemma BIndet_le_inv m b : b ⊑@{m} BIndet → b = BIndet.
Proof. by inversion 1. Qed.
Lemma Forall_BIndet_le_inv m bs1 bs2 :
  Forall (BIndet =) bs2 → bs1 ⊑@{m}* bs2 → Forall (BIndet =) bs1.
Proof.
  induction 2; decompose_Forall_hyps; subst;
    constructor; eauto using BIndet_le_inv, eq_sym.
Qed.

Lemma bit_valid_ge m b1 b2 : m ⊢ valid b1 → b1 ⊑@{m} b2 → m ⊢ valid b2.
Proof. by destruct 1; inversion 1; subst; try constructor. Qed.
Lemma bit_valid_le m b1 b2 : m ⊢ valid b2 → b1 ⊑@{m} b2 → m ⊢ valid b1.
Proof. by destruct 1; inversion 1; subst; try constructor. Qed.
Lemma bits_valid_ge m bs1 bs2 :
  m ⊢* valid bs1 → bs1 ⊑@{m}* bs2 → m ⊢* valid bs2.
Proof.
  intros Hbs1 Hbs. induction Hbs; decompose_Forall; eauto using bit_valid_ge.
Qed.
Lemma bits_valid_le m bs1 bs2 :
  m ⊢* valid bs2 → bs1 ⊑@{m}* bs2 → m ⊢* valid bs1.
Proof.
  intros Hbs1 Hbs. induction Hbs; decompose_Forall; eauto using bit_valid_le.
Qed.

Lemma bit_valid_weaken_mem m1 m2 b :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  m1 ⊢ valid b → m2 ⊢ valid b.
Proof. destruct 2; econstructor; eauto using ptr_bit_valid_weaken_mem. Qed.
Lemma bits_valid_weaken_mem m1 m2 bs :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  m1 ⊢* valid bs → m2 ⊢* valid bs.
Proof. intros. eapply Forall_impl; eauto using bit_valid_weaken_mem. Qed.
Lemma bit_le_weaken_mem m1 m2 b1 b2 :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  b1 ⊑@{m1} b2 → b1 ⊑@{m2} b2.
Proof. destruct 2; econstructor; eauto using bit_valid_weaken_mem. Qed.
Lemma bits_le_weaken_mem m1 m2 bs1 bs2 :
  (∀ x σ, type_of_index m1 x = Some σ → type_of_index m2 x = Some σ) →
  bs1 ⊑@{m1}* bs2 → bs1 ⊑@{m2}* bs2.
Proof. intros. eapply Forall2_impl; eauto using bit_le_weaken_mem. Qed.

Global Instance: PartialOrder (@subseteq_env M (bit Ti) _ m).
Proof.
  intros m. repeat split.
  * intro. constructor.
  * by do 2 destruct 1; constructor.
  * by destruct 1; inversion_clear 1.
Qed.

Lemma base_indet_bits_valid m τ : m ⊢* valid (base_indet_bits τ).
Proof. intros. apply Forall_replicate. by constructor. Qed.
Lemma base_indet_bits_le m τ bs :
  m ⊢* valid bs → length bs = bit_size_of (base τ) →
  base_indet_bits τ ⊑@{m}* bs.
Proof.
  intros. apply Forall2_replicate_l.
  * eapply Forall_impl; eauto. by constructor.
  * done.
Qed.

Lemma bits_le_inv m bs1 bs2 :
  bs1 ⊑@{m}* bs2 →
  bs1 = bs2 ∨ ∃ i, bs1 !! i = Some BIndet ∧ bs2 !! i ≠ Some BIndet.
Proof.
  induction 1 as [|b1 b2 bs1 bs2 Hb Hbs [?|[i ?]]]; [by left | |]; subst.
  * destruct Hb as [[]|b]; first [by left | by right; exists 0].
  * right. by exists (S i).
Qed.
Lemma bits_le_eq_or_indet m bs1 bs2 : bs1 ⊑@{m}* bs2 → bs1 = bs2 ∨ BIndet ∈ bs1.
Proof.
  intros. destruct (bits_le_inv m bs1 bs2) as [?|[?[??]]];
    eauto using elem_of_list_lookup_2.
Qed.
Lemma bits_le_no_indet m bs1 bs2 : bs1 ⊑@{m}* bs2 → BIndet ∉ bs1 → bs1 = bs2.
Proof. intros. by edestruct bits_le_eq_or_indet; eauto. Qed.
Lemma bits_le_indet m bs1 bs2 : BIndet ∈ bs1 → bs2 ⊑@{m}* bs1 → BIndet ∈ bs2.
Proof. intros. edestruct bits_le_eq_or_indet; eauto. by subst. Qed.
Lemma bits_le_resize m bs1 bs2 n :
  bs1 ⊑@{m}* bs2 → resize n BIndet bs1 ⊑@{m}* resize n BIndet bs2.
Proof. by apply Forall2_resize. Qed.

Lemma maybe_BBit_Some_le m b1 b2 β :
  maybe_BBit b1 = Some β → b1 ⊑@{m} b2 → maybe_BBit b2 = Some β.
Proof. by destruct 2; simplify_equality. Qed.
Lemma mapM_maybe_BBit_Some_le m bs1 bs2 βs :
  mapM maybe_BBit bs1 = Some βs → bs1 ⊑@{m}* bs2 →
  mapM maybe_BBit bs2 = Some βs.
Proof.
  intros Hbs1 Hbs. revert βs Hbs1. induction Hbs as [|b1 b2 bs1 bs2 ?? IH];
    intros; simplify_option_equality; auto.
  by erewrite maybe_BBit_Some_le, IH by eauto.
Qed.
Lemma mapM_maybe_BBit_is_Some_le m bs1 bs2 :
  Forall (is_Some ∘ maybe_BBit) bs1 → bs1 ⊑@{m}* bs2 →
  Forall (is_Some ∘ maybe_BBit) bs2.
Proof.
  rewrite <-!mapM_is_Some. intros [βs ?] ?.
  exists βs. eauto using mapM_maybe_BBit_Some_le.
Qed.

Lemma mask_bit_le m bm b : m ⊢ valid b → mask_bit bm b ⊑@{m} b.
Proof. by destruct bm; constructor. Qed.
Lemma mask_bit_non_indet_mask bm b : bm ≠ BIndet → mask_bit bm b = b.
Proof. by destruct bm. Qed.
Lemma mask_bit_valid m bm b : m ⊢ valid b → m ⊢ valid (mask_bit bm b).
Proof. destruct bm; simpl; auto using BIndet_valid. Qed.
Lemma mask_bit_ge m bm b : bm ⊑@{m} b → mask_bit bm b = bm.
Proof. by destruct 1, b. Qed.

Lemma mask_bits_nil bms : mask_bits bms [] = replicate (length bms) BIndet.
Proof. by destruct bms. Qed.
Lemma mask_bits_length bms bs : length (mask_bits bms bs) = length bms.
Proof.
  revert bms. induction bs; intros [|??]; simpl;
    auto using replicate_length with f_equal.
Qed.
Lemma mask_bits_le m bms bs n :
  m ⊢* valid bs → n = length bms → mask_bits bms bs ⊑@{m}* resize n BIndet bs.
Proof.
  intros Hbs ->. revert bms.
  by induction Hbs; intros [|??]; simpl; constructor; auto using mask_bit_le.
Qed.
Lemma mask_bits_le_same_length m bms bs :
  length bms = length bs → m ⊢* valid bs → mask_bits bms bs ⊑@{m}* bs.
Proof.
  intros Hbs ?.
  transitivity (resize (length bms) BIndet bs); auto using mask_bits_le.
  by rewrite Hbs, resize_all.
Qed.
Lemma mask_bits_indet bms bs :
  length bms = length bs → BIndet ∈ bms → BIndet ∈ mask_bits bms bs.
Proof.
  rewrite <-same_length_length. induction 1; simpl; try by rewrite elem_of_nil.
  rewrite !elem_of_cons. intros [?|?]; subst; auto.
Qed.
Lemma mask_bits_no_indet bms bs :
  length bms = length bs → BIndet ∉ bms → mask_bits bms bs = bs.
Proof.
  rewrite <-same_length_length.
  induction 1; simpl; [done|]. rewrite not_elem_of_cons.
  intros [??]; auto using mask_bit_non_indet_mask with f_equal.
Qed.
Lemma mask_bits_valid m bms bs : m ⊢* valid bs → m ⊢* valid (mask_bits bms bs).
Proof.
  intros Hbs. revert bms.
  induction Hbs; intros [|??]; simpl; auto using mask_bit_valid.
  constructor; auto using Forall_replicate, BIndet_valid.
Qed.
Lemma mask_bits_ge m bms bs : bms ⊑@{m}* bs → mask_bits bms bs = bms.
Proof. induction 1; simpl; f_equal; eauto using mask_bit_ge. Qed.

Lemma mask_bits_replicate bms n :
  mask_bits bms (replicate n BIndet) = replicate (length bms) BIndet.
Proof.
  revert n. induction bms as [|bm bms]; intros [|?]; simpl; f_equal; auto.
  by destruct bm.
Qed.
Lemma mask_bits_indet_mask bs n :
  mask_bits (replicate n BIndet) bs = replicate n BIndet.
Proof.
  revert n. induction bs; intros [|?]; simpl; f_equal; auto.
  by rewrite replicate_length.
Qed.
Lemma mask_bits_non_indet_mask bs n bm :
  bm ≠ BIndet → mask_bits (replicate n bm) bs = resize n BIndet bs.
Proof.
  intros ?. revert n. induction bs; intros [|?]; simpl; f_equal;
    rewrite ?replicate_length; auto using mask_bit_non_indet_mask.
Qed.

Lemma mask_bits_app bms1 bms2 bs :
  mask_bits (bms1 ++ bms2) bs =
    mask_bits bms1 bs ++ mask_bits bms2 (drop (length bms1) bs).
Proof.
  revert bs. induction bms1; intros [|??]; simpl; f_equal; auto.
  by rewrite app_length, replicate_plus, mask_bits_nil.
Qed.
Lemma mask_bits_take bms bs n :
  take n (mask_bits bms bs) = mask_bits (take n bms) (take n bs).
Proof.
  revert n bms. induction bs; intros [|?] [|??]; simpl; f_equal; auto.
  by rewrite take_replicate, take_length.
Qed.
Lemma mask_bits_drop bms bs n :
  drop n (mask_bits bms bs) = mask_bits (drop n bms) (drop n bs).
Proof.
  revert n bms. induction bs; intros [|n] [|? l]; simpl; f_equal; auto.
  by rewrite drop_replicate, mask_bits_nil, drop_length.
Qed.
Lemma mask_bits_resize bms bs n :
  resize n BIndet (mask_bits bms bs) =
    mask_bits (resize n BIndet bms) (resize n BIndet bs).
Proof.
  revert n bms.
  induction bs as [|b bs]; intros [|n] [|bm bms]; simpl; f_equal; auto.
  * by rewrite mask_bits_indet_mask by (by rewrite replicate_length).
  * by destruct bm.
  * by rewrite resize_replicate, mask_bits_replicate, resize_length.
  * by rewrite mask_bits_indet_mask by (by rewrite resize_length).
Qed.
Lemma mask_bits_resize_mask bms bs n :
  mask_bits (resize n BIndet bms) bs = resize n BIndet (mask_bits bms bs).
Proof.
  revert n bms.
  induction bs as [|b bs]; intros [|n] [|bm bms]; simpl; f_equal; auto.
  * by rewrite replicate_length.
  * by rewrite resize_replicate, resize_length.
  * by rewrite mask_bits_indet_mask.
Qed.
Lemma lookup_mask_bits_None bms bs i :
  bms !! i = None → mask_bits bms bs !! i = None.
Proof.
  revert i bms. induction bs; intros [|?] [|??] ?; simplify_equality'; auto.
  by apply lookup_replicate_None, lookup_ge_None.
Qed.
Lemma lookup_mask_bits_indet bms bs i :
  bms !! i = Some BIndet → mask_bits bms bs !! i = Some BIndet.
Proof.
  revert i bms. induction bs; intros [|?] [|??] ?; simplify_equality'; auto.
  by apply lookup_replicate, lookup_lt_Some with BIndet.
Qed.
Lemma lookup_mask_bits bms bm bs i :
  bms !! i = Some bm → bm ≠ BIndet → i < length bs →
  mask_bits bms bs !! i = bs !! i.
Proof.
  revert i bms. induction bs; intros [|?] [|??] ???;
    simplify_equality'; auto with lia. by rewrite mask_bit_non_indet_mask.
Qed.
Lemma mask_bits_sublist_insert bms bs1 bs2 j :
  length bms = length bs2 →
  mask_bits bms (sublist_insert j bs1 (mask_bits bms bs2)) =
    mask_bits bms (sublist_insert j bs1 bs2).
Proof.
  intros Hbs. apply list_eq. intros i.
  destruct (bms !! i) as [bm|] eqn:Hbm; [|by rewrite !lookup_mask_bits_None].
  destruct (decide (bm = BIndet)); subst; [by rewrite !lookup_mask_bits_indet|].
  assert (i < length bms) by eauto using lookup_lt_Some.
  erewrite !lookup_mask_bits by
    (rewrite ?sublist_insert_length, ?mask_bits_length; eauto with lia).
  apply lookup_sublist_proper. by erewrite !lookup_mask_bits by eauto with lia.
Qed.

Section array_of_bits.
  Context `(f : list (bit Ti) → A).

  Lemma array_of_bits_ext g τ n bs :
    (∀ bs, f bs = g bs) → array_of_bits f τ n bs = array_of_bits g τ n bs.
  Proof. revert bs; induction n; intros; simpl; f_equal; auto. Qed.

  Lemma array_of_bits_length τ n bs : length (array_of_bits f τ n bs) = n.
  Proof. revert bs. induction n; simpl; auto. Qed.

  Lemma array_of_bits_fmap {B} (g : list (bit Ti) → B) h τ n bs :
    (∀ bs, h (f bs) = g bs) →
    h <$> array_of_bits f τ n bs = array_of_bits g τ n bs.
  Proof. intros Hf. revert bs. induction n; simpl; intros; f_equal; auto. Qed.

  Lemma array_of_bits_resize τ n bs sz :
    (∀ bs sz, bit_size_of τ ≤ sz → f (resize sz BIndet bs) = f bs) →
    n * bit_size_of τ ≤ sz →
    array_of_bits f τ n (resize sz BIndet bs) = array_of_bits f τ n bs.
  Proof.
    intros Hf. revert sz bs. induction n; intros; simpl in *; f_equal;
      rewrite ?drop_resize_le; auto with lia.
  Qed.
End array_of_bits.

Section struct_of_bits.
  Context `(f : type Ti → list (bit Ti) → A).

  Lemma struct_of_bits_ext g τs bs :
    Forall (λ τ, pointwise_relation (list (bit Ti)) (=) (f τ) (g τ)) τs →
    struct_of_bits f τs bs = struct_of_bits g τs bs.
  Proof.
    unfold struct_of_bits. intros Hfg. revert bs.
    generalize (field_bit_sizes τs).
    induction Hfg; intros [|??] ?; simpl; f_equal; auto.
  Qed.

  Lemma struct_of_bits_fmap `(g : type Ti → list (bit Ti) → B) h τs bs :
    Forall (λ τ, ∀ bs, h (f τ bs) = g τ bs) τs →
    h <$> struct_of_bits f τs bs = struct_of_bits g τs bs.
  Proof.
    unfold struct_of_bits. intros Hf. revert bs.
    generalize (field_bit_sizes τs).
    induction Hf; intros [|??] ?; simpl; simplify_equality; f_equal; auto.
  Qed.

  Lemma struct_of_bits_resize τs bs sz :
    Forall (λ τ, ∀ bs sz, bit_size_of τ ≤ sz →
      f τ (resize sz BIndet bs) = f τ bs) τs →
    sum_list (field_bit_sizes τs) ≤ sz →
    struct_of_bits f τs (resize sz BIndet bs) = struct_of_bits f τs bs.
  Proof.
    unfold struct_of_bits. revert sz bs.
    induction (bit_size_of_fields τs) as [|τ sz τs ??? IH];
      intros; simpl in *; decompose_Forall; f_equal;
      rewrite ?drop_resize_le; auto with lia.
  Qed.
End struct_of_bits.

Global Instance: Commutative (@eq (option (bit Ti))) bit_join.
Proof. intros [] []; intros; simplify_option_equality; auto. Qed.
Lemma bit_join_indet_l b : bit_join BIndet b = Some b.
Proof. by destruct b; simplify_option_equality. Qed.
Lemma bit_join_indet_r b : bit_join b BIndet = Some b.
Proof. by destruct b; simplify_option_equality. Qed.
Lemma bit_join_diag b : bit_join b b = Some b.
Proof. by destruct b; simplify_option_equality. Qed.

Lemma bit_join_Some_l m b1 b2 b3 :
  m ⊢ valid b1 → m ⊢ valid b2 → bit_join b1 b2 = Some b3 → b1 ⊑@{m} b3.
Proof.
  by destruct 1, 1; intros; simplify_option_equality; repeat constructor.
Qed.
Lemma bit_join_Some_r m b1 b2 b3 :
  m ⊢ valid b1 → m ⊢ valid b2 → bit_join b1 b2 = Some b3 → b2 ⊑@{m} b3.
Proof. by destruct b1, b2; intros; simplify_option_equality; constructor. Qed.
Lemma bit_join_Some m b1 b2 b3 :
  m ⊢ valid b1 → m ⊢ valid b2 → bit_join b1 b2 = Some b3 →
  b1 ⊑@{m} b3 ∧ b2 ⊑@{m} b3.
Proof. eauto using bit_join_Some_l, bit_join_Some_r. Qed.

Lemma bit_join_min m b1 b2 b3 b4:
  bit_join b1 b2 = Some b3 → b1 ⊑@{m} b4 → b2 ⊑@{m} b4 → b3 ⊑@{m} b4.
Proof. destruct b1, b2; intros; simplify_option_equality; auto. Qed.
Lemma bit_join_exists m b1 b2 b4 :
  b1 ⊑@{m} b4 → b2 ⊑@{m} b4 → ∃ b3, bit_join b1 b2 = Some b3 ∧ b3 ⊑@{m} b4.
Proof.
  destruct 1; inversion_clear 1; simpl; eauto using bit_join_indet_l,
    bit_join_indet_r, bit_join_diag. by repeat econstructor.
Qed.

Global Instance: Commutative (@eq (option (list (bit Ti)))) bits_join.
Proof.
  intros bs1. induction bs1 as [|b1 bs1 IH]; intros [|b2 bs2]; simpl; try done.
  rewrite (commutative bit_join).
  destruct (bit_join _ _); simpl; try done. by rewrite IH.
Qed.

Lemma bits_join_indet_l bs :
  bits_join (replicate (length bs) BIndet) bs = Some bs.
Proof. induction bs as [|b bs IH]; simpl; [done|]. by rewrite IH. Qed.
Lemma bits_join_indet_r bs :
  bits_join bs (replicate (length bs) BIndet) = Some bs.
Proof. rewrite (commutative bits_join). apply bits_join_indet_l. Qed.
Lemma bits_join_diag bs : bits_join bs bs = Some bs.
Proof.
  induction bs as [|b bs IH]; simpl; [done|].
  rewrite bit_join_diag; simpl. by rewrite IH.
Qed.

Lemma bits_join_Some_l m bs1 bs2 bs3 :
  m ⊢* valid bs1 → m ⊢* valid bs2 →
  bits_join bs1 bs2 = Some bs3 → bs1 ⊑@{m}* bs3.
Proof.
  intros Hbs1. revert bs2 bs3.
  induction Hbs1 as [|b1 bs1 IH]; intros ?? [|???] ?;
    simplify_option_equality; constructor; eauto using bit_join_Some_l.
Qed.
Lemma bits_join_Some_r m bs1 bs2 bs3 :
  m ⊢* valid bs1 → m ⊢* valid bs2 →
  bits_join bs1 bs2 = Some bs3 → bs2 ⊑@{m}* bs3.
Proof.
  intros. apply bits_join_Some_l with bs1; auto.
  by rewrite (commutative bits_join).
Qed.
Lemma bits_join_Some m bs1 bs2 bs3 :
  m ⊢* valid bs1 → m ⊢* valid bs2 →
  bits_join bs1 bs2 = Some bs3 → bs1 ⊑@{m}* bs3 ∧ bs2 ⊑@{m}* bs3.
Proof. eauto using bits_join_Some_l, bits_join_Some_r. Qed.

Lemma bits_join_min m bs1 bs2 bs3 bs4 :
  bits_join bs1 bs2 = Some bs3 →
  bs1 ⊑@{m}* bs4 → bs2 ⊑@{m}* bs4 → bs3 ⊑@{m}* bs4.
Proof.
  intros Hbs3 Hbs1 Hbs2. revert bs2 bs3 Hbs2 Hbs3.
  induction Hbs1; intros; decompose_Forall; simplify_option_equality;
    constructor; eauto using bit_join_min.
Qed.

Lemma bits_join_exists m bs1 bs2 bs4 :
  bs1 ⊑@{m}* bs4 → bs2 ⊑@{m}* bs4 →
  ∃ bs3, bits_join bs1 bs2 = Some bs3 ∧ bs3 ⊑@{m}* bs4.
Proof.
  intros Hbs1. revert bs2.
  induction Hbs1 as [|b1 b4 bs1 bs4 ?? IH]; inversion_clear 1 as [|b2].
  { by eexists []. }
  edestruct IH as (?&Hbs2&?); eauto.
  edestruct (bit_join_exists m b1 b2 b4) as (?&Hb2&?); eauto.
  simpl. rewrite Hbs2. simpl. rewrite Hb2. simpl. eauto.
Qed.

Lemma bits_join_length_l bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → length bs3 = length bs1.
Proof.
  revert bs2 bs3. induction bs1; intros [|??] ??;
    simplify_option_equality; f_equal; eauto.
Qed.
Lemma bits_join_length_r bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → length bs3 = length bs2.
Proof. rewrite (commutative bits_join). apply bits_join_length_l. Qed.
End properties.
