(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export pointer_bits.

Inductive bit (K : iType) : iType :=
  | BIndet : bit K
  | BBit : bool → bit K
  | BPtr : ptr_bit K → bit K.
Arguments BIndet {_}.
Arguments BBit {_} _.
Arguments BPtr {_} _.
#[global] Instance bit_eq_dec `{EqDecision K}: EqDecision (bit K).
Proof. solve_decision. Defined.

#[global] Instance maybe_BBit {K} : Maybe (@BBit K) := λ b,
  match b with BBit b => Some b | _ => None end.
#[global] Instance maybe_BPtr {K} : Maybe (@BPtr K) := λ b,
  match b with BPtr pb => Some pb | _ => None end.

Section operations.
  Context `{Env K}.

  Inductive bit_valid' (Γ : env K) (Δ : memenv K) : bit K → Prop :=
    | BIndet_valid' : bit_valid' Γ Δ BIndet
    | BBit_valid' β : bit_valid' Γ Δ (BBit β)
    | BPtr_valid' pb : ✓{Γ,Δ} pb → bit_valid' Γ Δ (BPtr pb).
  Global Instance bit_valid:
    Valid (env K * memenv K) (bit K) := uncurry bit_valid'.

  Inductive bit_weak_refine : relation (bit K) :=
    | bit_weak_refine_refl b : bit_weak_refine b b
    | BIndet_weak_refine b : bit_weak_refine BIndet b.
  Definition bit_join (b1 b2 : bit K) : option (bit K) :=
    match b1, b2 with
    | BIndet, b2 => Some b2
    | b1, BIndet => Some b1
    | b1, b2 => guard (b1 = b2); Some b1
    end.
  Fixpoint bits_join (bs1 bs2 : list (bit K)) : option (list (bit K)) :=
    match bs1, bs2 with
    | [], [] => Some []
    | b1 :: bs1, b2 :: bs2 =>
       b3 ← bit_join b1 b2; bs3 ← bits_join bs1 bs2; Some (b3 :: bs3)
    | _, _ => None
    end.
  Fixpoint bits_list_join (sz : nat)
      (bss : list (list (bit K))) : option (list (bit K)) :=
    match bss with
    | [] => Some (replicate sz BIndet)
    | bs :: bss => bits_list_join sz bss ≫= bits_join (resize sz BIndet bs)
    end.
End operations.

Section bits.
Context `{EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types α β : bool.
Implicit Types βs : list bool.
Implicit Types pb : ptr_bit K.
Implicit Types b : bit K.
Implicit Types bs : list (bit K).

Local Infix "⊑" := bit_weak_refine (at level 70).
Local Infix "⊑*" := (Forall2 bit_weak_refine) (at level 70).
Local Hint Extern 0 (_ ⊑ _) => reflexivity: core.
Local Hint Extern 0 (_ ⊑* _) => reflexivity: core.

#[global] Instance bit_valid_dec ΓΔ (b : bit K) : Decision (✓{ΓΔ} b).
Proof.
 refine
  match b with
  | BIndet | BBit _ => left _ | BPtr pb => cast_if (decide (✓{ΓΔ} pb))
  end; destruct ΓΔ; first [by constructor | abstract by inversion 1].
Defined.
#[global] Instance: Inj (=) (=) (@BBit K).
Proof. by injection 1. Qed.
#[global] Instance: Inj (=) (=) (@BPtr K).
Proof. by injection 1. Qed.
Lemma BIndet_valid Γ Δ : ✓{Γ,Δ} BIndet.
Proof. constructor. Qed.
Lemma BIndets_valid Γ Δ bs : Forall (BIndet =.) bs → ✓{Γ,Δ}* bs.
Proof. by induction 1; simplify_equality'; repeat constructor. Qed.
Lemma BBit_valid Γ Δ β : ✓{Γ,Δ} (BBit β).
Proof. constructor. Qed.
Lemma BPtr_valid Γ Δ pb : ✓{Γ,Δ} pb → ✓{Γ,Δ} (BPtr pb).
Proof. by constructor. Qed.
Lemma BPtrs_valid Γ Δ pbs : ✓{Γ,Δ}* pbs → ✓{Γ,Δ}* (BPtr <$> pbs).
Proof. induction 1; csimpl; auto using BPtr_valid. Qed.
Lemma BPtr_valid_inv Γ Δ pb : ✓{Γ,Δ} (BPtr pb) → ✓{Γ,Δ} pb.
Proof. by inversion 1. Qed.
Lemma BPtrs_valid_inv Γ Δ pbs : ✓{Γ,Δ}* (BPtr <$> pbs) → ✓{Γ,Δ}* pbs.
Proof.
  induction pbs; inversion_clear 1; constructor; auto using BPtr_valid_inv.
Qed.
Lemma bit_valid_weaken Γ1 Γ2 Δ1 Δ2 b :
  ✓ Γ1 → ✓{Γ1,Δ1} b → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → ✓{Γ2,Δ2} b.
Proof. destruct 2; econstructor; eauto using ptr_bit_valid_weaken. Qed.

Lemma maybe_BBits_spec bs βs : mapM (maybe BBit) bs = Some βs ↔ bs = BBit <$> βs.
Proof.
  split.
  * intros ?. symmetry; apply (mapM_fmap_Some_inv _ _ _ _ H1). 
    by intros [] ? ?; simplify_equality'.
  * intros ->. by apply mapM_fmap_Some.
Qed.
#[global] Instance BBits_dec bs : Decision (∃ βs, bs = BBit <$> βs).
Proof.
 refine (cast_if (decide (is_Some (mapM (maybe BBit) bs))));
  abstract (by setoid_rewrite <-maybe_BBits_spec).
Defined.
Lemma maybe_BPtrs_spec bs pbs :
  mapM (maybe BPtr) bs = Some pbs ↔ bs = BPtr <$> pbs.
Proof.
  split.
  * intros ?. symmetry; apply (mapM_fmap_Some_inv _ _ _ _ H1). 
    by intros [] ? ?; simplify_equality'.
  * intros ->. by apply mapM_fmap_Some.
Qed.
#[global] Instance BPtrs_dec bs : Decision (∃ pbs, bs = BPtr <$> pbs).
Proof.
 refine (cast_if (decide (is_Some (mapM (maybe BPtr) bs))));
  abstract (by setoid_rewrite <-maybe_BPtrs_spec).
Defined.

(** ** Weak Refinements *)
#[global] Instance: PartialOrder (@bit_weak_refine K).
Proof.
  repeat split.
  * intros ?; constructor.
  * destruct 1. done. constructor.
  * by destruct 1; inversion 1.
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
Lemma bits_subseteq_indets bs1 bs2 :
  Forall (BIndet =.) bs2 → bs1 ⊑* bs2 → bs1 = bs2.
Proof. induction 2 as [|???? []]; decompose_Forall_hyps; f_equal; auto. Qed.
Lemma bit_join_valid Γ Δ b1 b2 b3 :
  bit_join b1 b2 = Some b3 → ✓{Γ,Δ} b1 → ✓{Γ,Δ} b2 → ✓{Γ,Δ} b3.
Proof. destruct 2,1; simplify_option_eq; constructor; auto. Qed.
#[global] Instance: Comm (@eq (option (bit K))) bit_join.
Proof. intros [] []; intros; simplify_option_eq; auto. Qed.
Lemma bit_join_indet_l b : bit_join BIndet b = Some b.
Proof. by destruct b; simplify_option_eq. Qed.
Lemma bit_join_indet_r b : bit_join b BIndet = Some b.
Proof. by destruct b; simplify_option_eq. Qed.
Lemma bit_join_diag b : bit_join b b = Some b.
Proof. by destruct b; simplify_option_eq. Qed.
Lemma bit_join_Some_l b1 b2 b3 : bit_join b1 b2 = Some b3 → b1 ⊑ b3.
Proof. destruct b1, b2; intros; simplify_option_eq; constructor. Qed.
Lemma bit_join_Some_r b1 b2 b3 : bit_join b1 b2 = Some b3 → b2 ⊑ b3.
Proof. destruct b1, b2; intros; simplify_option_eq; constructor. Qed.
Lemma bit_join_exists b1 b2 b4 :
  b1 ⊑ b4 → b2 ⊑ b4 → ∃ b3, bit_join b1 b2 = Some b3 ∧ b3 ⊑ b4.
Proof.
  destruct 1; inversion_clear 1; eauto using
    bit_join_diag, bit_join_indet_l, bit_join_indet_r, BIndet_weak_refine.
Qed.

Lemma bits_join_valid Γ Δ bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → ✓{Γ,Δ}* bs1 → ✓{Γ,Δ}* bs2 → ✓{Γ,Δ}* bs3.
Proof.
  intros Hbs Hbs1. revert bs2 bs3 Hbs. induction Hbs1; destruct 2;
    simplify_option_eq; constructor; eauto using bit_join_valid.
Qed.
#[global] Instance: Comm (@eq (option (list (bit K)))) bits_join.
Proof.
  intros bs1. induction bs1 as [|b1 bs1 IH]; intros [|b2 bs2]; simpl; try done.
  rewrite (comm bit_join). by destruct bit_join; simpl; rewrite ?IH.
Qed.
Lemma bits_join_indet_l bs :
  bits_join (replicate (length bs) BIndet) bs = Some bs.
Proof. induction bs as [|b bs IH]; simpl; [done|]. by rewrite IH. Qed.
Lemma bits_join_indet_r bs :
  bits_join bs (replicate (length bs) BIndet) = Some bs.
Proof. rewrite (comm bits_join). apply bits_join_indet_l. Qed.
Lemma bits_join_diag bs : bits_join bs bs = Some bs.
Proof. by induction bs as [|b bs IH]; simpl; rewrite ?bit_join_diag, ?IH. Qed.
Lemma bits_join_Some_l bs1 bs2 bs3 : bits_join bs1 bs2 = Some bs3 → bs1 ⊑* bs3.
Proof.
  revert bs2 bs3. induction bs1; intros [|??] [|??] ?;
    simplify_option_eq; constructor; eauto using bit_join_Some_l.
Qed.
Lemma bits_join_Some_r bs1 bs2 bs3 : bits_join bs1 bs2 = Some bs3 → bs2 ⊑* bs3.
Proof.
  revert bs2 bs3. induction bs1; intros [|??] [|??] ?;
    simplify_option_eq; constructor; eauto using bit_join_Some_r.
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
    simplify_option_eq; f_equal; eauto.
Qed.
Lemma bits_join_length_r bs1 bs2 bs3 :
  bits_join bs1 bs2 = Some bs3 → length bs3 = length bs2.
Proof. rewrite (comm bits_join). apply bits_join_length_l. Qed.

Lemma bits_list_join_length sz bss bs :
  bits_list_join sz bss = Some bs → length bs = sz.
Proof.
  revert bs. induction bss; intros; simplify_option_eq.
  * by rewrite replicate_length.
  * erewrite bits_join_length_r by eauto; eauto.
Qed.
Lemma bits_list_join_valid Γ Δ sz bss bs :
  bits_list_join sz bss = Some bs → Forall (✓{Γ,Δ}*) bss → ✓{Γ,Δ}* bs.
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
    simplify_option_eq; eauto using bits_join_Some_l.
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
    as (bs3&Hbs3&?); auto. simplify_option_eq; eauto.
Qed.
Lemma bits_list_join_min sz bss bs bs' :
  length bs' = sz → bits_list_join sz bss = Some bs →
  Forall (λ bs'', resize sz BIndet bs'' ⊑* bs') bss → bs ⊑* bs'.
Proof.
  intros ? Hbs Hbss. revert bs Hbs.
  induction Hbss; intros; simplify_option_eq; eauto using
    Forall2_replicate_l, Forall_true, BIndet_weak_refine, bits_join_min.
Qed.
End bits.
