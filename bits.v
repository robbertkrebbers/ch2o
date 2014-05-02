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

Section operations.
  Context `{TypeOfIndex Ti M, Refine Ti M, IndexAlive M, IntEnv Ti, PtrEnv Ti,
    ∀ m x, Decision (index_alive m x)}.

  Inductive bit_valid' (Γ : env Ti) (mm : option M) : bit Ti → Prop :=
    | BIndet_valid' : bit_valid' Γ mm BIndet
    | BBit_valid' β : bit_valid' Γ mm (BBit β)
    | BPtr_valid' pb : ✓{Γ,mm} pb → bit_valid' Γ mm (BPtr pb).
  Global Instance bit_valid :
    Valid (env Ti * option M) (bit Ti) := curry bit_valid'.

  Global Instance bit_valid_dec Γmm (b : bit Ti) : Decision (✓{Γmm} b).
  Proof.
   refine
    match b with
    | BIndet | BBit _ => left _ | BPtr pb => cast_if (decide (✓{Γmm} pb))
    end; destruct Γmm; first [by constructor | abstract by inversion 1].
  Defined.
  Definition bit_indet (b : bit Ti) : bool :=
    match b with BIndet => true | _ => false end.

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

  Inductive bit_refine' (Γ : env Ti) (f : mem_inj Ti) : relation (bit Ti) :=
    | BIndet_refine' b : ✓{Γ,None} b → bit_refine' Γ f BIndet b
    | BBit_refine' β : bit_refine' Γ f (BBit β) (BBit β)
    | BPtr_refine' pb1 pb2 :
       pb1 ⊑{Γ,f} pb2 → bit_refine' Γ f (BPtr pb1) (BPtr pb2).
  Global Instance bit_refine : Refine Ti (bit Ti) := bit_refine'.
End operations.

Section properties.
Context `{MemSpec Ti M}.
Implicit Types Γ : env Ti.
Implicit Types m : M.
Implicit Types mm : option M.
Implicit Types β : bool.
Implicit Types βs : list bool.
Implicit Types pb : ptr_bit Ti.
Implicit Types b : bit Ti.
Implicit Types bs : list (bit Ti).

Local Infix "⊑" := bit_weak_refine (at level 70).
Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Hint Extern 0 (_ ⊑ _) => reflexivity.
Hint Extern 0 (_ ⊑* _) => reflexivity.

Definition maybe_BBit (b : bit Ti) : option bool :=
  match b with BBit b => Some b | _ => None end.
Definition maybe_BPtr (b : bit Ti) : option (ptr_bit Ti) :=
  match b with BPtr pb => Some pb | _ => None end.
Global Instance: Injective (=) (=) (@BBit Ti).
Proof. by injection 1. Qed.
Global Instance: Injective (=) (=) (@BPtr Ti).
Proof. by injection 1. Qed.
Lemma BIndet_valid Γ mm : ✓{Γ,mm} BIndet.
Proof. constructor. Qed.
Lemma BBit_valid Γ mm β : ✓{Γ,mm} (BBit β).
Proof. constructor. Qed.
Lemma BPtr_valid Γ mm pb : ✓{Γ,mm} pb → ✓{Γ,mm} (BPtr pb).
Proof. by constructor. Qed.
Lemma BPtrs_valid Γ mm pbs : ✓{Γ,mm}* pbs → ✓{Γ,mm}* (BPtr <$> pbs).
Proof. induction 1; simpl; auto using BPtr_valid. Qed.
Lemma BPtr_valid_inv Γ mm pb : ✓{Γ,mm} (BPtr pb) → ✓{Γ,mm} pb.
Proof. by inversion 1. Qed.
Lemma BPtrs_valid_inv Γ mm pbs : ✓{Γ,mm}* (BPtr <$> pbs) → ✓{Γ,mm}* pbs.
Proof.
  induction pbs; inversion_clear 1; constructor; auto using BPtr_valid_inv.
Qed.
Lemma bit_valid_weakly_valid Γ m b : ✓{Γ,Some m} b → ✓{Γ,None} b.
Proof. destruct 1; constructor; eauto using ptr_bit_valid_weakly_valid. Qed.
Lemma bit_valid_weaken Γ1 Γ2 m1 m2 b :
  ✓ Γ1 → ✓{Γ1,Some m1} b → Γ1 ⊆ Γ2 →
  (∀ o σ, type_of_index m1 o = Some σ → type_of_index m2 o = Some σ) →
  ✓{Γ2,Some m2} b.
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
Lemma bit_refine_valid_l Γ f b1 b2 : ✓ Γ →  b1 ⊑{Γ,f} b2 → ✓{Γ,None} b1.
Proof. destruct 2; constructor; eauto using ptr_bit_refine_valid_l. Qed.
Lemma bits_refine_valid_l Γ f bs1 bs2 : ✓ Γ → bs1 ⊑{Γ,f}* bs2 → ✓{Γ,None}* bs1.
Proof. induction 2; eauto using bit_refine_valid_l. Qed.
Lemma bit_refine_valid_r Γ f b1 b2 : ✓ Γ → b1 ⊑{Γ,f} b2 → ✓{Γ,None} b2.
Proof. destruct 2; try constructor; eauto using ptr_bit_refine_valid_r. Qed.
Lemma bits_refine_valid_r Γ f bs1 bs2 : ✓ Γ → bs1 ⊑{Γ,f}* bs2 → ✓{Γ,None}* bs2.
Proof. induction 2; eauto using bit_refine_valid_r. Qed.
Lemma bit_refine_id Γ mm b : ✓{Γ,mm} b → b ⊑{Γ} b.
Proof. destruct 1; constructor; eauto using ptr_bit_refine_id, BIndet_valid. Qed.
Lemma bits_refine_id Γ mm bs : ✓{Γ,mm}* bs → bs ⊑{Γ}* bs.
Proof. induction 1; eauto using bit_refine_id. Qed.
Lemma bit_refine_compose Γ f g b1 b2 b3 :
  ✓ Γ → b1 ⊑{Γ,f} b2 → b2 ⊑{Γ,g} b3 → b1 ⊑{Γ,f ◎ g} b3.
Proof.
  destruct 2; inversion 1; simplify_equality'; constructor; eauto using
    ptr_bit_refine_compose, bit_refine_valid_r.
Qed.
Lemma bits_refine_compose Γ f g bs1 bs2 bs3 :
  ✓ Γ → bs1 ⊑{Γ,f}* bs2 → bs2 ⊑{Γ,g}* bs3 → bs1 ⊑{Γ,f ◎ g}* bs3.
Proof.
  intros ? Hbs. revert bs3. induction Hbs; inversion_clear 1;
    constructor; eauto using bit_refine_compose.
Qed.
Global Instance:
  PropHolds (✓ Γ) → Transitive (refine Γ mem_inj_id : relation (bit Ti)).
Proof. intros Γ ? b1 b2 b3. by apply bit_refine_compose. Qed.
Global Instance: AntiSymmetric (=) (refine Γ mem_inj_id : relation (bit Ti)).
Proof.
  destruct 1; inversion 1; simplify_equality';
    f_equal; eauto using ptr_bit_refine_eq.
Qed.
Lemma BIndet_refine Γ mm f b : ✓{Γ,mm} b → BIndet ⊑{Γ,f} b.
Proof. constructor. destruct mm; eauto using bit_valid_weakly_valid. Qed.
Lemma BIndet_BIndet_refine Γ f : BIndet ⊑{Γ,f} BIndet.
Proof. auto using (BIndet_refine _ None), BIndet_valid. Qed.
Lemma BBit_refine Γ f β : BBit β ⊑{Γ,f} BBit β.
Proof. by constructor. Qed.
Lemma BPtr_refine Γ f pb1 pb2 : pb1 ⊑{Γ,f} pb2 → BPtr pb1 ⊑{Γ,f} BPtr pb2.
Proof. by constructor. Qed.
Lemma BBits_refine Γ f βs : BBit <$> βs ⊑{Γ,f}* BBit <$> βs.
Proof. induction βs; constructor; auto using BBit_refine. Qed.
Lemma BPtrs_refine Γ f pbs1 pbs2 :
  pbs1 ⊑{Γ,f}* pbs2 → BPtr <$> pbs1 ⊑{Γ,f}* BPtr <$> pbs2.
Proof. induction 1; constructor; auto using BPtr_refine. Qed.
Lemma BIndets_refine_l_inv Γ f bs1 bs2 :
  Forall (BIndet =) bs1 → bs1 ⊑{Γ,f}* bs2 → ✓{Γ,None}* bs2.
Proof. induction 2 as [|???? []]; decompose_Forall_hyps'; eauto. Qed.
Lemma BIndet_refine_r_inv Γ f b : b ⊑{Γ,f} BIndet → b = BIndet.
Proof. by inversion 1. Qed.
Lemma BIndets_refine_r_inv Γ f bs1 bs2 :
  Forall (BIndet =) bs2 → bs1 ⊑{Γ,f}* bs2 → Forall (BIndet =) bs1.
Proof. induction 2 as [|????[]]; decompose_Forall_hyps'; eauto. Qed.
Lemma BBits_refine_inv_l Γ f βs bs : BBit <$> βs ⊑{Γ,f}* bs → bs = BBit <$> βs.
Proof.
  rewrite Forall2_fmap_l.
  induction 1 as [|???? Hb]; [|inversion Hb]; simplify_equality'; auto.
Qed.
Lemma BPtrs_refine_inv Γ f pbs1 pbs2 :
  BPtr <$> pbs1 ⊑{Γ,f}* BPtr <$> pbs2 → pbs1 ⊑{Γ,f}* pbs2.
Proof.
  rewrite Forall2_fmap. induction 1 as [|???? Hb]; [|inversion Hb]; auto.
Qed.
Lemma BPtrs_refine_inv_l Γ f pbs1 bs2 :
  BPtr <$> pbs1 ⊑{Γ,f}* bs2 → ∃ pbs2, bs2 = BPtr <$> pbs2 ∧ pbs1 ⊑{Γ,f}* pbs2.
Proof.
  rewrite Forall2_fmap_l. induction 1 as [|???? Hb ? (?&->&?)]; simpl.
  { by eexists []. }
  inversion Hb; subst. eexists (_ :: _); simpl; eauto.
Qed.
Lemma BPtrs_refine_inv_r Γ f bs1 pbs2 :
  ¬(∃ pbs, bs1 = BPtr <$> pbs) → bs1 ⊑{Γ,f}* BPtr <$> pbs2 →
  Exists (✓{Γ,None}) pbs2.
Proof.
  intros Hbps. rewrite Forall2_fmap_r. induction 1 as [|???? Hb ? IH].
  { destruct Hbps. by eexists []. }
  inversion Hb; subst; eauto using BPtr_valid_inv.
  right. apply IH. intros [? ->]. destruct Hbps; eexists (_ :: _); simpl; eauto.
Qed.
Lemma bits_refine_resize Γ f bs1 bs2 n :
  bs1 ⊑{Γ,f}* bs2 → resize n BIndet bs1 ⊑{Γ,f}* resize n BIndet bs2.
Proof. apply Forall2_resize. constructor; auto using BIndet_valid. Qed.

(** ** Weak Refinements *)
Global Instance: PartialOrder (@bit_weak_refine Ti).
Proof.
  repeat split.
  * intros ?; constructor.
  * destruct 1. done. constructor.
  * by destruct 1; inversion 1.
Qed.
Lemma bit_refine_subseteq Γ b1 b2 : b1 ⊑{Γ} b2 → b1 ⊑ b2.
Proof.
  destruct 1; try constructor.
  by apply reflexive_eq, f_equal, (ptr_bit_refine_eq Γ).
Qed.
Lemma bit_subseteq_refine Γ mm b1 b2 : ✓{Γ,mm} b2 → b1 ⊑ b2 → b1 ⊑{Γ} b2.
Proof. destruct 2; eauto using BIndet_refine, bit_refine_id. Qed.
Lemma bits_subseteq_refine Γ mm bs1 bs2 :
  ✓{Γ,mm}* bs2 → bs1 ⊑* bs2 → bs1 ⊑{Γ}* bs2.
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
Lemma bit_join_valid Γ mm b1 b2 b3 :
  bit_join b1 b2 = Some b3 → ✓{Γ,mm} b1 → ✓{Γ,mm} b2 → ✓{Γ,mm} b3.
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
Lemma bit_join_refine Γ f b1 b2 b3 b1' b2' b3' :
  bit_join b1 b2 = Some b3 → bit_join b1' b2' = Some b3' →
  b1 ⊑{Γ,f} b1' → b2 ⊑{Γ,f} b2' → b3 ⊑{Γ,f} b3'.
Proof.
  destruct 3, 1; repeat
    match goal with
    | H : bit_join ?b _ = _ |- _ => is_var b; destruct b
    | H : bit_join _ ?b = _ |- _ => is_var b; destruct b
    | _ => case_option_guard || simplify_equality'
    end; constructor; eauto using bit_join_valid.
Qed.

Lemma bits_join_valid Γ mm bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → ✓{Γ,mm}* bs1 → ✓{Γ,mm}* bs2 → ✓{Γ,mm}* bs3.
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
  simpl; rewrite Hbs2; simpl; rewrite Hb2; simpl; eauto.
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
Lemma bits_join_refine Γ f bs1 bs2 bs3 bs1' bs2' bs3' :
  bits_join bs1 bs2 = Some bs3 → bits_join bs1' bs2' = Some bs3' →
  bs1 ⊑{Γ,f}* bs1' → bs2 ⊑{Γ,f}* bs2' → bs3 ⊑{Γ,f}* bs3'.
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
Lemma bits_list_join_valid Γ mm sz bss bs :
  bits_list_join sz bss = Some bs → Forall (✓{Γ,mm}*) bss → ✓{Γ,mm}* bs.
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
Lemma bits_list_join_refine Γ f sz bss1 bss2 bs1 bs2 :
  bits_list_join sz bss1 = Some bs1 → bits_list_join sz bss2 = Some bs2 →
  Forall2 (Forall2 (refine Γ f)) bss1 bss2 → bs1 ⊑{Γ,f}* bs2.
Proof.
  intros Hbs1 Hbs2 Hbss. revert bs1 bs2 Hbs1 Hbs2.
  induction Hbss; intros; simplify_option_equality; eauto using
    bits_join_refine, Forall2_replicate, Forall2_resize, BIndet_BIndet_refine.
Qed.
End properties.

