(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export pointer_bits.

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
  match b with BBit b => Some b | _ => None end.
Definition maybe_BPtr {Ti}  (b : bit Ti) : option (ptr_bit Ti) :=
  match b with BPtr pb => Some pb | _ => None end.

Section operations.
  Context `{TypeCheck M (type Ti) index, Refine Ti M, IndexAlive M,
    Env Ti, ∀ m x, Decision (index_alive m x)}.

  Inductive bit_valid' (Γ : env Ti) (m : M) : bit Ti → Prop :=
    | BIndet_valid' : bit_valid' Γ m BIndet
    | BBit_valid' β : bit_valid' Γ m (BBit β)
    | BPtr_valid' pb : ✓{Γ,m} pb → bit_valid' Γ m (BPtr pb).
  Global Instance bit_valid: Valid (env Ti * M) (bit Ti) := curry bit_valid'.

  Inductive bit_weak_refine : relation (bit Ti) :=
    | bit_weak_refine_refl b : bit_weak_refine b b
    | BIndet_weak_refine b : bit_weak_refine BIndet b.
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
       b3 ← bit_join b1 b2; bs3 ← bits_join bs1 bs2; Some (b3 :: bs3)
    | _, _ => None
    end.
  Fixpoint bits_list_join (sz : nat)
      (bss : list (list (bit Ti))) : option (list (bit Ti)) :=
    match bss with
    | [] => Some (replicate sz BIndet)
    | bs :: bss => bits_list_join sz bss ≫= bits_join (resize sz BIndet bs)
    end.

  Inductive bit_refine' (Γ : env Ti) (f : mem_inj Ti) (m1 m2 : M) :
       relation (bit Ti) :=
    | BIndet_refine' b2 : ✓{Γ,m2} b2 → bit_refine' Γ f m1 m2 BIndet b2
    | BBit_refine' β : bit_refine' Γ f m1 m2 (BBit β) (BBit β)
    | BPtr_refine' pb1 pb2 :
       pb1 ⊑{Γ,f@m1↦m2} pb2 → bit_refine' Γ f m1 m2 (BPtr pb1) (BPtr pb2)
    | BPtr_BIndet_refine' pb1 b2 :
       ✓{Γ,m1} pb1 → ¬ptr_alive m1 (fragmented.frag_item pb1) →
       ✓{Γ,m2} b2 → bit_refine' Γ f m1 m2 (BPtr pb1) b2.
  Global Instance bit_refine: Refine Ti M (bit Ti) := bit_refine'.
End operations.

Section properties.
Context `{MemSpec Ti M}.
Implicit Types Γ : env Ti.
Implicit Types m : M.
Implicit Types β : bool.
Implicit Types βs : list bool.
Implicit Types pb : ptr_bit Ti.
Implicit Types b : bit Ti.
Implicit Types bs : list (bit Ti).

Local Infix "⊑" := bit_weak_refine (at level 70).
Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Hint Extern 0 (_ ⊑ _) => reflexivity.
Hint Extern 0 (_ ⊑* _) => reflexivity.

Global Instance bit_valid_dec Γm (b : bit Ti) : Decision (✓{Γm} b).
Proof.
 refine
  match b with
  | BIndet | BBit _ => left _ | BPtr pb => cast_if (decide (✓{Γm} pb))
  end; destruct Γm; first [by constructor | abstract by inversion 1].
Defined.
Global Instance: Injective (=) (=) (@BBit Ti).
Proof. by injection 1. Qed.
Global Instance: Injective (=) (=) (@BPtr Ti).
Proof. by injection 1. Qed.
Lemma BIndet_valid Γ m : ✓{Γ,m} BIndet.
Proof. constructor. Qed.
Lemma BIndets_valid Γ m bs : Forall (BIndet =) bs → ✓{Γ,m}* bs.
Proof. by induction 1; simplify_equality'; repeat constructor. Qed.
Lemma BBit_valid Γ m β : ✓{Γ,m} (BBit β).
Proof. constructor. Qed.
Lemma BPtr_valid Γ m pb : ✓{Γ,m} pb → ✓{Γ,m} (BPtr pb).
Proof. by constructor. Qed.
Lemma BPtrs_valid Γ m pbs : ✓{Γ,m}* pbs → ✓{Γ,m}* (BPtr <$> pbs).
Proof. induction 1; csimpl; auto using BPtr_valid. Qed.
Lemma BPtr_valid_inv Γ m pb : ✓{Γ,m} (BPtr pb) → ✓{Γ,m} pb.
Proof. by inversion 1. Qed.
Lemma BPtrs_valid_inv Γ m pbs : ✓{Γ,m}* (BPtr <$> pbs) → ✓{Γ,m}* pbs.
Proof.
  induction pbs; inversion_clear 1; constructor; auto using BPtr_valid_inv.
Qed.
Lemma bit_valid_weaken Γ1 Γ2 m1 m2 b :
  ✓ Γ1 → ✓{Γ1,m1} b → Γ1 ⊆ Γ2 → (∀ o σ, m1 ⊢ o : σ → m2 ⊢ o : σ) → ✓{Γ2,m2} b.
Proof. destruct 2; econstructor; eauto using ptr_bit_valid_weaken. Qed.

Lemma maybe_BBits_spec bs βs : mapM maybe_BBit bs = Some βs ↔ bs = BBit <$> βs.
Proof.
  split.
  * apply mapM_fmap_Some_inv. by intros ? [] ?; simplify_equality'.
  * intros ->. by apply mapM_fmap_Some.
Qed.
Global Instance BBits_dec bs : Decision (∃ βs, bs = BBit <$> βs).
Proof.
 refine (cast_if (decide (is_Some (mapM maybe_BBit bs))));
  abstract (by setoid_rewrite <-maybe_BBits_spec).
Defined.
Lemma maybe_BPtrs_spec bs pbs :
  mapM maybe_BPtr bs = Some pbs ↔ bs = BPtr <$> pbs.
Proof.
  split.
  * apply mapM_fmap_Some_inv. by intros ? [] ?; simplify_equality'.
  * intros ->. by apply mapM_fmap_Some.
Qed.
Global Instance BPtrs_dec bs : Decision (∃ pbs, bs = BPtr <$> pbs).
Proof.
 refine (cast_if (decide (is_Some (mapM maybe_BPtr bs))));
  abstract (by setoid_rewrite <-maybe_BPtrs_spec).
Defined.

(** ** Refinements *)
Lemma bit_refine_valid_l Γ f m1 m2 b1 b2 :
  ✓ Γ → b1 ⊑{Γ,f@m1↦m2} b2 → ✓{Γ,m1} b1.
Proof. destruct 2; constructor; eauto using ptr_bit_refine_valid_l. Qed.
Lemma bits_refine_valid_l Γ f m1 m2 bs1 bs2 :
  ✓ Γ → bs1 ⊑{Γ,f@m1↦m2}* bs2 → ✓{Γ,m1}* bs1.
Proof. induction 2; eauto using bit_refine_valid_l. Qed.
Lemma bit_refine_valid_r Γ f m1 m2 b1 b2 :
  ✓ Γ → b1 ⊑{Γ,f@m1↦m2} b2 → ✓{Γ,m2} b2.
Proof. destruct 2; try constructor; eauto using ptr_bit_refine_valid_r. Qed.
Lemma bits_refine_valid_r Γ f m1 m2 bs1 bs2 :
  ✓ Γ → bs1 ⊑{Γ,f@m1↦m2}* bs2 → ✓{Γ,m2}* bs2.
Proof. induction 2; eauto using bit_refine_valid_r. Qed.
Lemma bit_refine_id Γ m b : ✓{Γ,m} b → b ⊑{Γ@m} b.
Proof.
  destruct 1; constructor; eauto using ptr_bit_refine_id, BIndet_valid.
Qed.
Lemma bits_refine_id Γ m bs : ✓{Γ,m}* bs → bs ⊑{Γ@m}* bs.
Proof. induction 1; eauto using bit_refine_id. Qed.
Lemma bit_refine_compose Γ f g m1 m2 m3 b1 b2 b3 :
  ✓ Γ → b1 ⊑{Γ,f@m1↦m2} b2 → b2 ⊑{Γ,g@m2↦m3} b3 → b1 ⊑{Γ,f ◎ g@m1↦m3} b3.
Proof.
  destruct 2 as [| |pb1 pb2 Hpb|]; inversion 1; simplify_equality';
    try constructor (by eauto using ptr_bit_refine_compose, bit_refine_valid_r).
  constructor; eauto using ptr_bit_refine_valid_l.
  destruct Hpb as (?&?&?&?); eauto using ptr_alive_refine.
Qed.
Lemma bits_refine_compose Γ f g m1 m2 m3 bs1 bs2 bs3 :
  ✓ Γ → bs1 ⊑{Γ,f@m1↦m2}* bs2 → bs2 ⊑{Γ,g@m2↦m3}* bs3 →
  bs1 ⊑{Γ,f ◎ g@m1↦m3}* bs3.
Proof.
  intros ? Hbs. revert bs3. induction Hbs; inversion_clear 1;
    constructor; eauto using bit_refine_compose.
Qed.
Global Instance:
  PropHolds (✓ Γ) → Transitive (refine Γ mem_inj_id m m : relation (bit Ti)).
Proof. intros Γ m ? b1 b2 b3. by apply bit_refine_compose. Qed.
Lemma bit_refine_weaken Γ Γ' f f' m1 m2 m1' m2' b1 b2 :
  ✓ Γ → b1 ⊑{Γ,f@m1↦m2} b2 → Γ ⊆ Γ' →
  (∀ o o2 r τ, m1 ⊢ o : τ → f !! o = Some (o2,r) → f' !! o = Some (o2,r)) →
  (∀ o τ, m1 ⊢ o : τ → m1' ⊢ o : τ) → (∀ o τ, m2 ⊢ o : τ → m2' ⊢ o : τ) →
  (∀ o τ, m1 ⊢ o : τ → index_alive m1' o → index_alive m1 o) →
  (∀ o1 o2 r, f !! o1 = Some (o2,r) → index_alive m1' o1 → index_alive m2' o2) →
  b1 ⊑{Γ',f'@m1'↦m2'} b2.
Proof.
  destruct 2 as [| | |pb1 b2 Hpb]; constructor; eauto using bit_valid_weaken,
    ptr_bit_refine_weaken, ptr_bit_valid_weaken, ptr_dead_weaken.
  destruct Hpb as (?&?&?&?); eauto using ptr_dead_weaken.
Qed.
Lemma BIndet_refine Γ m1 m2 f b : ✓{Γ,m2} b → BIndet ⊑{Γ,f@m1↦m2} b.
Proof. by constructor. Qed.
Lemma BIndets_refine Γ m1 m2 f bs1 bs2 :
  Forall (BIndet =) bs1 → ✓{Γ,m2}* bs2 →
  length bs1 = length bs2 → bs1 ⊑{Γ,f@m1↦m2}* bs2.
Proof.
  rewrite <-Forall2_same_length.
  induction 3; decompose_Forall_hyps; repeat constructor; auto.
Qed.
Lemma BIndet_BIndet_refine Γ f m1 m2 : BIndet ⊑{Γ,f@m1↦m2} BIndet.
Proof. repeat constructor. Qed.
Lemma BBit_refine Γ f m1 m2 β : BBit β ⊑{Γ,f@m1↦m2} BBit β.
Proof. by constructor. Qed.
Lemma BPtr_refine Γ f m1 m2 pb1 pb2 :
  pb1 ⊑{Γ,f@m1↦m2} pb2 → BPtr pb1 ⊑{Γ,f@m1↦m2} BPtr pb2.
Proof. by constructor. Qed.
Lemma BBits_refine Γ f m1 m2 βs : BBit <$> βs ⊑{Γ,f@m1↦m2}* BBit <$> βs.
Proof. induction βs; constructor; auto using BBit_refine. Qed.
Lemma BPtrs_refine Γ f m1 m2 pbs1 pbs2 :
  pbs1 ⊑{Γ,f@m1↦m2}* pbs2 → BPtr <$> pbs1 ⊑{Γ,f@m1↦m2}* BPtr <$> pbs2.
Proof. induction 1; constructor; auto using BPtr_refine. Qed.
Lemma BIndets_refine_l_inv Γ f m1 m2 bs1 bs2 :
  Forall (BIndet =) bs1 → bs1 ⊑{Γ,f@m1↦m2}* bs2 → ✓{Γ,m2}* bs2.
Proof. induction 2 as [|???? []]; decompose_Forall_hyps; eauto. Qed.
Lemma BPtrs_BIndets_refine Γ f m1 m2 pbs1 bs2 :
  ✓{Γ,m1}* pbs1 → Forall (λ pb, ¬ptr_alive m1 (fragmented.frag_item pb)) pbs1 →
  ✓{Γ,m2}* bs2 → length pbs1 = length bs2 → BPtr <$> pbs1 ⊑{Γ,f@m1↦m2}* bs2.
Proof.
  rewrite <-Forall2_same_length.
  induction 4; decompose_Forall_hyps; repeat constructor; auto.
Qed.
Lemma BIndet_refine_r_inv Γ f m1 m2 b1 b3 :
  b1 ⊑{Γ,f@m1↦m2} BIndet → ✓{Γ,m2} b3 → b1 ⊑{Γ,f@m1↦m2} b3.
Proof. inversion 1; constructor; auto. Qed.
Lemma BIndets_refine_r_inv Γ f m1 m2 bs1 bs2 bs3 :
  bs1 ⊑{Γ,f@m1↦m2}* bs2 → Forall (BIndet =) bs2 →
  ✓{Γ,m2}* bs3 → length bs1 = length bs3 → bs1 ⊑{Γ,f@m1↦m2}* bs3.
Proof.
  rewrite <-Forall2_same_length. intros Hbs Hbs2. revert bs3.
  induction Hbs; intros; decompose_Forall_hyps; auto using BIndet_refine_r_inv.
Qed.
Lemma BBits_refine_inv_l Γ f m1 m2 βs bs :
  BBit <$> βs ⊑{Γ,f@m1↦m2}* bs → bs = BBit <$> βs.
Proof.
  rewrite Forall2_fmap_l.
  induction 1 as [|???? Hb]; [|inversion Hb]; simplify_equality'; auto.
Qed.
Lemma BPtrs_refine_inv_l Γ f m1 m2 pbs1 bs2 :
  BPtr <$> pbs1 ⊑{Γ,f@m1↦m2}* bs2 →
  Forall (λ pb, ptr_alive m1 (fragmented.frag_item pb)) pbs1 →
  ∃ pbs2, bs2 = BPtr <$> pbs2 ∧ pbs1 ⊑{Γ,f@m1↦m2}* pbs2.
Proof.
  rewrite Forall2_fmap_l. induction 1 as [|pb1 b2 pbs1 bs2 Hb ? IH];
    intros; decompose_Forall_hyps.
  { by eexists []. }
  destruct IH as (pbs2&->&?); auto. inversion Hb; simplify_equality'; try done.
  eexists (_ :: _); csimpl; eauto.
Qed.
Lemma BPtrs_refine_inv_r Γ f m1 m2 bs1 pbs2 :
  ¬(∃ pbs, bs1 = BPtr <$> pbs) → bs1 ⊑{Γ,f@m1↦m2}* BPtr <$> pbs2 →
  Exists (✓{Γ,m2}) pbs2.
Proof.
  intros Hbps. rewrite Forall2_fmap_r. induction 1 as [|???? Hb ? IH].
  { destruct Hbps. by eexists []. }
  inversion Hb; subst; eauto using BPtr_valid_inv.
  right. apply IH. intros [?->]. destruct Hbps; eexists (_ :: _); csimpl; eauto.
Qed.

(** ** Weak Refinements *)
Global Instance: PartialOrder (@bit_weak_refine Ti).
Proof.
  repeat split.
  * intros ?; constructor.
  * destruct 1. done. constructor.
  * by destruct 1; inversion 1.
Qed.
Lemma bit_subseteq_refine Γ m b1 b2 : ✓{Γ,m} b2 → b1 ⊑ b2 → b1 ⊑{Γ@m} b2.
Proof. destruct 2; eauto using BIndet_refine, bit_refine_id. Qed.
Lemma bits_subseteq_refine Γ m bs1 bs2 :
  ✓{Γ,m}* bs2 → bs1 ⊑* bs2 → bs1 ⊑{Γ@m}* bs2.
Proof.
  induction 2; decompose_Forall_hyps; eauto using bit_subseteq_refine.
Qed.
Lemma bits_subseteq_eq bs1 bs2 : bs1 ⊑* bs2 → bs1 = bs2 ∨ BIndet ∈ bs1.
Proof.
  induction 1 as [|???? [] ? IH]; rewrite ?elem_of_cons; naive_solver.
Qed.
Lemma bits_subseteq_indet bs1 bs2 : BIndet ∈ bs1 → bs2 ⊑* bs1 → BIndet ∈ bs2.
Proof.
  intros Hbs. induction 1 as [|????[]];
    rewrite ?elem_of_cons in Hbs |- *; naive_solver.
Qed.
Lemma bit_join_valid Γ m b1 b2 b3 :
  bit_join b1 b2 = Some b3 → ✓{Γ,m} b1 → ✓{Γ,m} b2 → ✓{Γ,m} b3.
Proof. destruct 2,1; simplify_option_equality; constructor; auto. Qed.
Global Instance: Commutative (@eq (option (bit Ti))) bit_join.
Proof. intros [] []; intros; simplify_option_equality; auto. Qed.
Lemma bit_join_indet_l b : bit_join BIndet b = Some b.
Proof. by destruct b; simplify_option_equality. Qed.
Lemma bit_join_indet_r b : bit_join b BIndet = Some b.
Proof. by destruct b; simplify_option_equality. Qed.
Lemma bit_join_diag b : bit_join b b = Some b.
Proof. by destruct b; simplify_option_equality. Qed.
Lemma bit_join_Some_l b1 b2 b3 : bit_join b1 b2 = Some b3 → b1 ⊑ b3.
Proof. destruct b1, b2; intros; simplify_option_equality; constructor. Qed.
Lemma bit_join_Some_r b1 b2 b3 : bit_join b1 b2 = Some b3 → b2 ⊑ b3.
Proof. destruct b1, b2; intros; simplify_option_equality; constructor. Qed.
Lemma bit_join_exists b1 b2 b4 :
  b1 ⊑ b4 → b2 ⊑ b4 → ∃ b3, bit_join b1 b2 = Some b3 ∧ b3 ⊑ b4.
Proof.
  destruct 1; inversion_clear 1; eauto using
    bit_join_diag, bit_join_indet_l, bit_join_indet_r, BIndet_weak_refine.
Qed.
Lemma bit_join_refine Γ f m1 m2 b1 b2 b3 b1' b2' b3' :
  bit_join b1 b2 = Some b3 → bit_join b1' b2' = Some b3' →
  b1 ⊑{Γ,f@m1↦m2} b1' → b2 ⊑{Γ,f@m1↦m2} b2' → b3 ⊑{Γ,f@m1↦m2} b3'.
Proof.
  destruct 3, 1; repeat
    match goal with
    | H : bit_join ?b _ = _ |- _ => is_var b; destruct b
    | H : bit_join _ ?b = _ |- _ => is_var b; destruct b
    | _ => case_option_guard || simplify_equality'
    end; constructor (by eauto using bit_join_valid).
Qed.

Lemma bits_join_valid Γ m bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → ✓{Γ,m}* bs1 → ✓{Γ,m}* bs2 → ✓{Γ,m}* bs3.
Proof.
  intros Hbs Hbs1. revert bs2 bs3 Hbs. induction Hbs1; destruct 2;
    simplify_option_equality; constructor; eauto using bit_join_valid.
Qed.
Global Instance: Commutative (@eq (option (list (bit Ti)))) bits_join.
Proof.
  intros bs1. induction bs1 as [|b1 bs1 IH]; intros [|b2 bs2]; simpl; try done.
  rewrite (commutative bit_join). by destruct bit_join; simpl; rewrite ?IH.
Qed.
Lemma bits_join_indet_l bs :
  bits_join (replicate (length bs) BIndet) bs = Some bs.
Proof. induction bs as [|b bs IH]; simpl; [done|]. by rewrite IH. Qed.
Lemma bits_join_indet_r bs :
  bits_join bs (replicate (length bs) BIndet) = Some bs.
Proof. rewrite (commutative bits_join). apply bits_join_indet_l. Qed.
Lemma bits_join_diag bs : bits_join bs bs = Some bs.
Proof. by induction bs as [|b bs IH]; simpl; rewrite ?bit_join_diag, ?IH. Qed.
Lemma bits_join_Some_l bs1 bs2 bs3 : bits_join bs1 bs2 = Some bs3 → bs1 ⊑* bs3.
Proof.
  revert bs2 bs3. induction bs1; intros [|??] [|??] ?;
    simplify_option_equality; constructor; eauto using bit_join_Some_l.
Qed.
Lemma bits_join_Some_r bs1 bs2 bs3 : bits_join bs1 bs2 = Some bs3 → bs2 ⊑* bs3.
Proof.
  revert bs2 bs3. induction bs1; intros [|??] [|??] ?;
    simplify_option_equality; constructor; eauto using bit_join_Some_r.
Qed.
Lemma bits_join_exists bs1 bs2 bs4 :
  bs1 ⊑* bs4 → bs2 ⊑* bs4 → ∃ bs3, bits_join bs1 bs2 = Some bs3 ∧ bs3 ⊑* bs4.
Proof.
  intros Hbs14. revert bs2. induction Hbs14 as [|b1 b4 bs1 bs4 ?? IH];
    inversion_clear 1 as [|b2]; [by eexists []|].
  edestruct IH as (?&Hbs2&?); eauto.
  edestruct (bit_join_exists b1 b2 b4) as (?&Hb2&?); eauto.
  simpl; rewrite Hbs2; simpl; rewrite Hb2; csimpl; eauto.
Qed.
Lemma bits_join_min bs1 bs2 bs3 bs4 :
  bits_join bs1 bs2 = Some bs3 → bs1 ⊑* bs4 → bs2 ⊑* bs4 → bs3 ⊑* bs4.
Proof. intros. destruct (bits_join_exists bs1 bs2 bs4); naive_solver. Qed.
Lemma bits_join_length_l bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → length bs3 = length bs1.
Proof.
  revert bs2 bs3. induction bs1; intros [|??] ??;
    simplify_option_equality; f_equal; eauto.
Qed.
Lemma bits_join_length_r bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → length bs3 = length bs2.
Proof. rewrite (commutative bits_join). apply bits_join_length_l. Qed.
Lemma bits_join_refine Γ f m1 m2 bs1 bs2 bs3 bs1' bs2' bs3' :
  bits_join bs1 bs2 = Some bs3 → bits_join bs1' bs2' = Some bs3' →
  bs1 ⊑{Γ,f@m1↦m2}* bs1' → bs2 ⊑{Γ,f@m1↦m2}* bs2' → bs3 ⊑{Γ,f@m1↦m2}* bs3'.
Proof.
  intros Hbs Hbs' Hbs1. revert bs2 bs2' bs3 bs3' Hbs Hbs'.
  induction Hbs1; destruct 3; simplify_option_equality;
    constructor; eauto using bit_join_refine.
Qed.

Lemma bits_list_join_length sz bss bs :
  bits_list_join sz bss = Some bs → length bs = sz.
Proof.
  revert bs. induction bss; intros; simplify_option_equality.
  * by rewrite replicate_length.
  * erewrite bits_join_length_r by eauto; eauto.
Qed.
Lemma bits_list_join_valid Γ m sz bss bs :
  bits_list_join sz bss = Some bs → Forall (✓{Γ,m}*) bss → ✓{Γ,m}* bs.
Proof.
  intros Hbs Hbss. revert bs Hbs.
  induction Hbss as [|bs' bss IH]; intros bs Hbs; simplify_equality'.
  { eauto using Forall_replicate, BIndet_valid. }
  destruct (bits_list_join sz bss) as [bs''|] eqn:Hbs'; simplify_equality'.
  eapply bits_join_valid; eauto using Forall_resize, BIndet_valid.
Qed.
Lemma bits_list_join_Some sz bss bs bs' :
  bits_list_join sz bss = Some bs → bs' ∈ bss → resize sz BIndet bs' ⊑* bs.
Proof.
  intros Hbs Hbs'. revert bs Hbs. induction Hbs'; intros;
    simplify_option_equality; eauto using bits_join_Some_l.
  etransitivity; [|eapply bits_join_Some_r; eauto]; eauto.
Qed.
Lemma bits_list_join_Some_alt sz bss bs :
  bits_list_join sz bss = Some bs →
  Forall (λ bs', resize sz BIndet bs' ⊑* bs) bss.
Proof. rewrite Forall_forall. eauto using bits_list_join_Some. Qed.
Lemma bits_list_join_exists sz bss bs' :
  length bs' = sz → Forall (λ bs, resize sz BIndet bs ⊑* bs') bss →
  ∃ bs, bits_list_join sz bss = Some bs ∧ bs ⊑* bs'.
Proof.
  induction 2 as [|bs bss ?? (bs2&Hbs2&?)]; simpl.
  { eauto using Forall2_replicate_l, Forall_true, BIndet_weak_refine. }
  destruct (bits_join_exists (resize sz BIndet bs) bs2 bs')
    as (bs3&Hbs3&?); auto. simplify_option_equality; eauto.
Qed.
Lemma bits_list_join_min sz bss bs bs' :
  length bs' = sz → bits_list_join sz bss = Some bs →
  Forall (λ bs'', resize sz BIndet bs'' ⊑* bs') bss → bs ⊑* bs'.
Proof.
  intros ? Hbs Hbss. revert bs Hbs.
  induction Hbss; intros; simplify_option_equality; eauto using
    Forall2_replicate_l, Forall_true, BIndet_weak_refine, bits_join_min.
Qed.
Lemma bits_list_join_refine Γ f m1 m2 sz bss1 bss2 bs1 bs2 :
  bits_list_join sz bss1 = Some bs1 → bits_list_join sz bss2 = Some bs2 →
  Forall2 (Forall2 (refine Γ f m1 m2 )) bss1 bss2 → bs1 ⊑{Γ,f@m1↦m2}* bs2.
Proof.
  intros Hbs1 Hbs2 Hbss. revert bs1 bs2 Hbs1 Hbs2.
  induction Hbss; intros; simplify_option_equality; eauto using
    bits_join_refine, Forall2_replicate, Forall2_resize, BIndet_BIndet_refine.
Qed.
End properties.
