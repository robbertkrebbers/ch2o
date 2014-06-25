(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects some trivial facts on the Coq types [nat] and [N] for
natural numbers, and the type [Z] for integers. It also declares some useful
notations. *)
Require Export Eqdep PArith NArith ZArith NPeano.
Require Import QArith Qcanon.
Require Export base decidable.
Open Scope nat_scope.

Coercion Z.of_nat : nat >-> Z.

(** * Notations and properties of [nat] *)
Reserved Notation "x ≤ y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y ≤ z ≤ z'"
  (at level 70, y at next level, z at next level).

Infix "≤" := le : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat : nat_scope.
Notation "x < y < z" := (x < y ∧ y < z)%nat : nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%nat : nat_scope.
Notation "(≤)" := le (only parsing) : nat_scope.
Notation "(<)" := lt (only parsing) : nat_scope.

Infix "`div`" := NPeano.div (at level 35) : nat_scope.
Infix "`mod`" := NPeano.modulo (at level 35) : nat_scope.

Instance nat_eq_dec: ∀ x y : nat, Decision (x = y) := eq_nat_dec.
Instance nat_le_dec: ∀ x y : nat, Decision (x ≤ y) := le_dec.
Instance nat_lt_dec: ∀ x y : nat, Decision (x < y) := lt_dec.
Instance nat_inhabited: Inhabited nat := populate 0%nat.
Instance: Injective (=) (=) S.
Proof. by injection 1. Qed.
Instance: PartialOrder (≤).
Proof. repeat split; repeat intro; auto with lia. Qed.

Instance nat_le_pi: ∀ x y : nat, ProofIrrel (x ≤ y).
Proof.
  assert (∀ x y (p : x ≤ y) y' (q : x ≤ y'),
    y = y' → eq_dep nat (le x) y p y' q) as aux.
  { fix 3. intros x ? [|y p] ? [|y' q].
    * done.
    * clear nat_le_pi. intros; exfalso; auto with lia.
    * clear nat_le_pi. intros; exfalso; auto with lia.
    * injection 1. intros Hy. by case (nat_le_pi x y p y' q Hy). }
  intros x y p q.
  by apply (eq_dep_eq_dec (λ x y, decide (x = y))), aux.
Qed.
Instance nat_lt_pi: ∀ x y : nat, ProofIrrel (x < y).
Proof. apply _. Qed.

Definition sum_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x + go l
  end.
Notation sum_list := (sum_list_with id).

Lemma Nat_lt_succ_succ n : n < S (S n).
Proof. auto with arith. Qed.
Lemma Nat_mul_split_l n x1 x2 y1 y2 :
  x2 < n → y2 < n → x1 * n + x2 = y1 * n + y2 → x1 = y1 ∧ x2 = y2.
Proof.
  intros Hx2 Hy2 E. cut (x1 = y1); [intros; subst;lia |].
  revert y1 E. induction x1; simpl; intros [|?]; simpl; auto with lia.
Qed.
Lemma Nat_mul_split_r n x1 x2 y1 y2 :
  x1 < n → y1 < n → x1 + x2 * n = y1 + y2 * n → x1 = y1 ∧ x2 = y2.
Proof. intros. destruct (Nat_mul_split_l n x2 x1 y2 y1); auto with lia. Qed.

Notation lcm := Nat.lcm.
Notation divide := Nat.divide.
Notation "( x | y )" := (divide x y) : nat_scope.
Instance: PartialOrder divide.
Proof.
  repeat split; try apply _. intros ??. apply Nat.divide_antisym_nonneg; lia.
Qed.
Hint Extern 0 (_ | _) => reflexivity.
Lemma Nat_divide_ne_0 x y : (x | y) → y ≠ 0 → x ≠ 0.
Proof. intros Hxy Hy ->. by apply Hy, Nat.divide_0_l. Qed.

(** * Notations and properties of [positive] *)
Open Scope positive_scope.

Infix "≤" := Pos.le : positive_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : positive_scope.
Notation "x < y < z" := (x < y ∧ y < z) : positive_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : positive_scope.
Notation "(≤)" := Pos.le (only parsing) : positive_scope.
Notation "(<)" := Pos.lt (only parsing) : positive_scope.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Arguments Pos.of_nat _ : simpl never.
Instance positive_eq_dec: ∀ x y : positive, Decision (x = y) := Pos.eq_dec.
Instance positive_inhabited: Inhabited positive := populate 1.

Instance: Injective (=) (=) (~0).
Proof. by injection 1. Qed.
Instance: Injective (=) (=) (~1).
Proof. by injection 1. Qed.

(** Since [positive] represents lists of bits, we define list operations
on it. These operations are in reverse, as positives are treated as snoc
lists instead of cons lists. *)
Fixpoint Papp (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => (Papp p1 p2)~0
  | p2~1 => (Papp p1 p2)~1
  end.
Infix "++" := Papp : positive_scope.
Notation "(++)" := Papp (only parsing) : positive_scope.
Notation "( p ++)" := (Papp p) (only parsing) : positive_scope.
Notation "(++ q )" := (λ p, Papp p q) (only parsing) : positive_scope.

Fixpoint Preverse_go (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => Preverse_go (p1~0) p2
  | p2~1 => Preverse_go (p1~1) p2
  end.
Definition Preverse : positive → positive := Preverse_go 1.

Global Instance: LeftId (=) 1 (++).
Proof. intros p. by induction p; intros; f_equal'. Qed.
Global Instance: RightId (=) 1 (++).
Proof. done. Qed.
Global Instance: Associative (=) (++).
Proof. intros ?? p. by induction p; intros; f_equal'. Qed.
Global Instance: ∀ p : positive, Injective (=) (=) (++ p).
Proof. intros p ???. induction p; simplify_equality; auto. Qed.

Lemma Preverse_go_app_cont p1 p2 p3 :
  Preverse_go (p2 ++ p1) p3 = p2 ++ Preverse_go p1 p3.
Proof.
  revert p1. induction p3; simpl; intros.
  * apply (IHp3 (_~1)).
  * apply (IHp3 (_~0)).
  * done.
Qed.
Lemma Preverse_go_app p1 p2 p3 :
  Preverse_go p1 (p2 ++ p3) = Preverse_go p1 p3 ++ Preverse_go 1 p2.
Proof.
  revert p1. induction p3; intros p1; simpl; auto.
  by rewrite <-Preverse_go_app_cont.
Qed.
Lemma Preverse_app p1 p2 :
  Preverse (p1 ++ p2) = Preverse p2 ++ Preverse p1.
Proof. unfold Preverse. by rewrite Preverse_go_app. Qed.

Lemma Preverse_xO p : Preverse (p~0) = (1~0) ++ Preverse p.
Proof Preverse_app p (1~0).
Lemma Preverse_xI p : Preverse (p~1) = (1~1) ++ Preverse p.
Proof Preverse_app p (1~1).

Fixpoint Plength (p : positive) : nat :=
  match p with 1 => 0%nat | p~0 | p~1 => S (Plength p) end.
Lemma Papp_length p1 p2 :
  Plength (p1 ++ p2) = (Plength p2 + Plength p1)%nat.
Proof. by induction p2; f_equal'. Qed.

Close Scope positive_scope.

(** * Notations and properties of [N] *)
Infix "≤" := N.le : N_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%N : N_scope.
Notation "x < y < z" := (x < y ∧ y < z)%N : N_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%N : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.
Notation "(<)" := N.lt (only parsing) : N_scope.
Infix "`div`" := N.div (at level 35) : N_scope.
Infix "`mod`" := N.modulo (at level 35) : N_scope.

Arguments N.add _ _ : simpl never.

Instance: Injective (=) (=) Npos.
Proof. by injection 1. Qed.

Instance N_eq_dec: ∀ x y : N, Decision (x = y) := N.eq_dec.
Program Instance N_le_dec (x y : N) : Decision (x ≤ y)%N :=
  match Ncompare x y with
  | Gt => right _
  | _ => left _
  end.
Next Obligation. congruence. Qed.
Program Instance N_lt_dec (x y : N) : Decision (x < y)%N :=
  match Ncompare x y with
  | Lt => left _
  | _ => right _
  end.
Next Obligation. congruence. Qed.
Instance N_inhabited: Inhabited N := populate 1%N.
Instance: PartialOrder (≤)%N.
Proof.
  repeat split; red. apply N.le_refl. apply N.le_trans. apply N.le_antisymm.
Qed.
Hint Extern 0 (_ ≤ _)%N => reflexivity.

(** * Notations and properties of [Z] *)
Open Scope Z_scope.

Infix "≤" := Z.le : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Z_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Notation "(<)" := Z.lt (only parsing) : Z_scope.

Infix "`div`" := Z.div (at level 35) : Z_scope.
Infix "`mod`" := Z.modulo (at level 35) : Z_scope.
Infix "`quot`" := Z.quot (at level 35) : Z_scope.
Infix "`rem`" := Z.rem (at level 35) : Z_scope.
Infix "≪" := Z.shiftl (at level 35) : Z_scope.
Infix "≫" := Z.shiftr (at level 35) : Z_scope.

Instance: Injective (=) (=) Zpos.
Proof. by injection 1. Qed.
Instance: Injective (=) (=) Zneg.
Proof. by injection 1. Qed.

Instance Z_eq_dec: ∀ x y : Z, Decision (x = y) := Z.eq_dec.
Instance Z_le_dec: ∀ x y : Z, Decision (x ≤ y) := Z_le_dec.
Instance Z_lt_dec: ∀ x y : Z, Decision (x < y) := Z_lt_dec.
Instance Z_inhabited: Inhabited Z := populate 1.
Instance: PartialOrder (≤).
Proof.
  repeat split; red. apply Z.le_refl. apply Z.le_trans. apply Z.le_antisymm.
Qed.

Lemma Z_pow_pred_r n m : 0 < m → n * n ^ (Z.pred m) = n ^ m.
Proof.
  intros. rewrite <-Z.pow_succ_r, Z.succ_pred. done. by apply Z.lt_le_pred.
Qed.
Lemma Z_quot_range_nonneg k x y : 0 ≤ x < k → 0 < y → 0 ≤ x `quot` y < k.
Proof.
  intros [??] ?.
  destruct (decide (y = 1)); subst; [rewrite Z.quot_1_r; auto |].
  destruct (decide (x = 0)); subst; [rewrite Z.quot_0_l; auto with lia |].
  split. apply Z.quot_pos; lia. transitivity x; auto. apply Z.quot_lt; lia.
Qed.

(* Note that we cannot disable simpl for [Z.of_nat] as that would break
tactics as [lia]. *)
Arguments Z.to_nat _ : simpl never.
Arguments Z.mul _ _ : simpl never.
Arguments Z.add _ _ : simpl never.
Arguments Z.opp _ : simpl never.
Arguments Z.pow _ _ : simpl never.
Arguments Z.div _ _ : simpl never.
Arguments Z.modulo _ _ : simpl never.
Arguments Z.quot _ _ : simpl never.
Arguments Z.rem _ _ : simpl never.

Lemma Z_mod_pos a b : 0 < b → 0 ≤ a `mod` b.
Proof. apply Z.mod_pos_bound. Qed.

Hint Resolve Z.lt_le_incl : zpos.
Hint Resolve Z.add_nonneg_pos Z.add_pos_nonneg Z.add_nonneg_nonneg : zpos.
Hint Resolve Z.mul_nonneg_nonneg Z.mul_pos_pos : zpos.
Hint Resolve Z.pow_pos_nonneg Z.pow_nonneg: zpos.
Hint Resolve Z_mod_pos Z.div_pos : zpos.
Hint Extern 1000 => lia : zpos.

Lemma Z2Nat_inj_pow (x y : nat) : Z.of_nat (x ^ y) = x ^ y.
Proof.
  induction y as [|y IH].
  * by rewrite Z.pow_0_r, Nat.pow_0_r.
  * by rewrite Nat.pow_succ_r, Nat2Z.inj_succ, Z.pow_succ_r,
      Nat2Z.inj_mul, IH by auto with zpos.
Qed.
Lemma Z2Nat_inj_div x y : Z.of_nat (x `div` y) = x `div` y.
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.div_unique with (x `mod` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Lemma Z2Nat_inj_mod x y : Z.of_nat (x `mod` y) = x `mod` y.
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.mod_unique with (x `div` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Close Scope Z_scope.

(** * Notations and properties of [Qc] *)
Open Scope Qc_scope.
Delimit Scope Qc_scope with Qc.
Notation "1" := (Q2Qc 1) : Qc_scope.
Notation "2" := (1+1) : Qc_scope.
Notation "- 1" := (Qcopp 1) : Qc_scope.
Notation "- 2" := (Qcopp 2) : Qc_scope.
Notation "x - y" := (x + -y) : Qc_scope.
Notation "x / y" := (x * /y) : Qc_scope.
Infix "≤" := Qcle : Qc_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Qc_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Qc_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Qc_scope.
Notation "(≤)" := Qcle (only parsing) : Qc_scope.
Notation "(<)" := Qclt (only parsing) : Qc_scope.

Hint Extern 1 (_ ≤ _) => reflexivity || discriminate.
Arguments Qred _ : simpl never.

Instance Qc_eq_dec: ∀ x y : Qc, Decision (x = y) := Qc_eq_dec.
Program Instance Qc_le_dec (x y : Qc) : Decision (x ≤ y) :=
  if Qclt_le_dec y x then right _ else left _.
Next Obligation. by apply Qclt_not_le. Qed.
Program Instance Qc_lt_dec (x y : Qc) : Decision (x < y) :=
  if Qclt_le_dec x y then left _ else right _.
Next Obligation. by apply Qcle_not_lt. Qed.

Instance: PartialOrder (≤).
Proof.
  repeat split; red. apply Qcle_refl. apply Qcle_trans. apply Qcle_antisym.
Qed.
Instance: StrictOrder (<).
Proof.
  split; red. intros x Hx. by destruct (Qclt_not_eq x x). apply Qclt_trans.
Qed.
Lemma Qcmult_0_l x : 0 * x = 0.
Proof. ring. Qed.
Lemma Qcmult_0_r x : x * 0 = 0.
Proof. ring. Qed.
Lemma Qcle_ngt (x y : Qc) : x ≤ y ↔ ¬y < x.
Proof. split; auto using Qcle_not_lt, Qcnot_lt_le. Qed.
Lemma Qclt_nge (x y : Qc) : x < y ↔ ¬y ≤ x.
Proof. split; auto using Qclt_not_le, Qcnot_le_lt. Qed.
Lemma Qcplus_le_mono_l (x y z : Qc) : x ≤ y ↔ z + x ≤ z + y.
Proof.
  split; intros.
  * by apply Qcplus_le_compat.
  * replace x with ((0 - z) + (z + x)) by ring.
    replace y with ((0 - z) + (z + y)) by ring.
    by apply Qcplus_le_compat.
Qed.
Lemma Qcplus_le_mono_r (x y z : Qc) : x ≤ y ↔ x + z ≤ y + z.
Proof. rewrite !(Qcplus_comm _ z). apply Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_l (x y z : Qc) : x < y ↔ z + x < z + y.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_r (x y z : Qc) : x < y ↔ x + z < y + z.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_r. Qed.
Instance: Injective (=) (=) Qcopp.
Proof.
  intros x y H. by rewrite <-(Qcopp_involutive x), H, Qcopp_involutive.
Qed.
Instance: ∀ z, Injective (=) (=) (Qcplus z).
Proof.
  intros z x y H. by apply (anti_symmetric (≤));
    rewrite (Qcplus_le_mono_l _ _ z), H.
Qed.
Instance: ∀ z, Injective (=) (=) (λ x, x + z).
Proof.
  intros z x y H. by apply (anti_symmetric (≤));
    rewrite (Qcplus_le_mono_r _ _ z), H.
Qed.
Lemma Qcplus_pos_nonneg (x y : Qc) : 0 < x → 0 ≤ y → 0 < x + y.
Proof.
  intros. apply Qclt_le_trans with (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonneg_pos (x y : Qc) : 0 ≤ x → 0 < y → 0 < x + y.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_pos_nonneg. Qed. 
Lemma Qcplus_pos_pos (x y : Qc) : 0 < x → 0 < y → 0 < x + y.
Proof. auto using Qcplus_pos_nonneg, Qclt_le_weak. Qed.
Lemma Qcplus_nonneg_nonneg (x y : Qc) : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
Proof.
  intros. transitivity (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_neg_nonpos (x y : Qc) : x < 0 → y ≤ 0 → x + y < 0.
Proof.
  intros. apply Qcle_lt_trans with (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonpos_neg (x y : Qc) : x ≤ 0 → y < 0 → x + y < 0.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_neg_nonpos. Qed.
Lemma Qcplus_neg_neg (x y : Qc) : x < 0 → y < 0 → x + y < 0.
Proof. auto using Qcplus_nonpos_neg, Qclt_le_weak. Qed.
Lemma Qcplus_nonpos_nonpos (x y : Qc) : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
Proof.
  intros. transitivity (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcmult_le_mono_nonneg_l x y z : 0 ≤ z → x ≤ y → z * x ≤ z * y.
Proof. intros. rewrite !(Qcmult_comm z). by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_nonneg_r x y z : 0 ≤ z → x ≤ y → x * z ≤ y * z.
Proof. intros. by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_pos_l x y z : 0 < z → x ≤ y ↔ z * x ≤ z * y.
Proof.
  split; auto using Qcmult_le_mono_nonneg_l, Qclt_le_weak.
  rewrite !Qcle_ngt, !(Qcmult_comm z).
  intuition auto using Qcmult_lt_compat_r.
Qed.
Lemma Qcmult_le_mono_pos_r x y z : 0 < z → x ≤ y ↔ x * z ≤ y * z.
Proof. rewrite !(Qcmult_comm _ z). by apply Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_l x y z : 0 < z → x < y ↔ z * x < z * y.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_r x y z : 0 < z → x < y ↔ x * z < y * z.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_r. Qed.
Lemma Qcmult_pos_pos x y : 0 < x → 0 < y → 0 < x * y.
Proof.
  intros. apply Qcle_lt_trans with (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_lt_mono_pos_r.
Qed.
Lemma Qcmult_nonneg_nonneg x y : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof.
  intros. transitivity (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_le_mono_nonneg_r.
Qed.

Lemma inject_Z_Qred n : Qred (inject_Z n) = inject_Z n.
Proof. apply Qred_identity; auto using Z.gcd_1_r. Qed.
Coercion Qc_of_Z (n : Z) : Qc := Qcmake _ (inject_Z_Qred n).
Lemma Z2Qc_inj_0 : Qc_of_Z 0 = 0.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj n m : Qc_of_Z n = Qc_of_Z m → n = m.
Proof. by injection 1. Qed.
Lemma Z2Qc_inj_iff n m : Qc_of_Z n = Qc_of_Z m ↔ n = m.
Proof. split. auto using Z2Qc_inj. by intros ->. Qed.
Lemma Z2Qc_inj_le n m : (n ≤ m)%Z ↔ Qc_of_Z n ≤ Qc_of_Z m.
Proof. by rewrite Zle_Qle. Qed.
Lemma Z2Qc_inj_lt n m : (n < m)%Z ↔ Qc_of_Z n < Qc_of_Z m.
Proof. by rewrite Zlt_Qlt. Qed.
Lemma Z2Qc_inj_add n m : Qc_of_Z (n + m) = Qc_of_Z n + Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_plus. Qed.
Lemma Z2Qc_inj_mul n m : Qc_of_Z (n * m) = Qc_of_Z n * Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_mult. Qed.
Lemma Z2Qc_inj_opp n : Qc_of_Z (-n) = -Qc_of_Z n.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_opp. Qed.
Lemma Z2Qc_inj_sub n m : Qc_of_Z (n - m) = Qc_of_Z n - Qc_of_Z m.
Proof.
  apply Qc_is_canon; simpl.
  by rewrite !Qred_correct, <-inject_Z_opp, <-inject_Z_plus.
Qed.
Close Scope Qc_scope.

(** * Conversions *)
Lemma Z_to_nat_nonpos x : (x ≤ 0)%Z → Z.to_nat x = 0.
Proof. destruct x; simpl; auto using Z2Nat.inj_neg. by intros []. Qed.

(** The function [Z_to_option_N] converts an integer [x] into a natural number
by giving [None] in case [x] is negative. *)
Definition Z_to_option_N (x : Z) : option N :=
  match x with
  | Z0 => Some N0 | Zpos p => Some (Npos p) | Zneg _ => None
  end.
Definition Z_to_option_nat (x : Z) : option nat :=
  match x with
  | Z0 => Some 0 | Zpos p => Some (Pos.to_nat p) | Zneg _ => None
  end.

Lemma Z_to_option_N_Some x y :
  Z_to_option_N x = Some y ↔ (0 ≤ x)%Z ∧ y = Z.to_N x.
Proof.
  split.
  * intros. by destruct x; simpl in *; simplify_equality;
      auto using Zle_0_pos.
  * intros [??]. subst. destruct x; simpl; auto; lia.
Qed.
Lemma Z_to_option_N_Some_alt x y :
  Z_to_option_N x = Some y ↔ (0 ≤ x)%Z ∧ x = Z.of_N y.
Proof.
  rewrite Z_to_option_N_Some.
  split; intros [??]; subst; auto using N2Z.id, Z2N.id, eq_sym.
Qed.

Lemma Z_to_option_nat_Some x y :
  Z_to_option_nat x = Some y ↔ (0 ≤ x)%Z ∧ y = Z.to_nat x.
Proof.
  split.
  * intros. by destruct x; simpl in *; simplify_equality;
      auto using Zle_0_pos.
  * intros [??]. subst. destruct x; simpl; auto; lia.
Qed.
Lemma Z_to_option_nat_Some_alt x y :
  Z_to_option_nat x = Some y ↔ (0 ≤ x)%Z ∧ x = Z.of_nat y.
Proof.
  rewrite Z_to_option_nat_Some.
  split; intros [??]; subst; auto using Nat2Z.id, Z2Nat.id, eq_sym.
Qed.
Lemma Z_to_option_of_nat x : Z_to_option_nat (Z.of_nat x) = Some x.
Proof. apply Z_to_option_nat_Some_alt. auto using Nat2Z.is_nonneg. Qed.

(** Some correspondence lemmas between [nat] and [N] that are not part of the
standard library. We declare a hint database [natify] to rewrite a goal
involving [N] into a corresponding variant involving [nat]. *)
Lemma N_to_nat_lt x y : N.to_nat x < N.to_nat y ↔ (x < y)%N.
Proof. by rewrite <-N.compare_lt_iff, nat_compare_lt, N2Nat.inj_compare. Qed.
Lemma N_to_nat_le x y : N.to_nat x ≤ N.to_nat y ↔ (x ≤ y)%N.
Proof. by rewrite <-N.compare_le_iff, nat_compare_le, N2Nat.inj_compare. Qed.
Lemma N_to_nat_0 : N.to_nat 0 = 0.
Proof. done. Qed.
Lemma N_to_nat_1 : N.to_nat 1 = 1.
Proof. done. Qed.
Lemma N_to_nat_div x y : N.to_nat (x `div` y) = N.to_nat x `div` N.to_nat y.
Proof.
  destruct (decide (y = 0%N)); [by subst; destruct x |].
  apply Nat.div_unique with (N.to_nat (x `mod` y)).
  { by apply N_to_nat_lt, N.mod_lt. }
  rewrite (N.div_unique_exact (x * y) y x), N.div_mul by lia.
  by rewrite <-N2Nat.inj_mul, <-N2Nat.inj_add, <-N.div_mod.
Qed.
(* We have [x `mod` 0 = 0] on [nat], and [x `mod` 0 = x] on [N]. *)
Lemma N_to_nat_mod x y :
  y ≠ 0%N → N.to_nat (x `mod` y) = N.to_nat x `mod` N.to_nat y.
Proof.
  intros. apply Nat.mod_unique with (N.to_nat (x `div` y)).
  { by apply N_to_nat_lt, N.mod_lt. }
  rewrite (N.div_unique_exact (x * y) y x), N.div_mul by lia.
  by rewrite <-N2Nat.inj_mul, <-N2Nat.inj_add, <-N.div_mod.
Qed.

Hint Rewrite <-N2Nat.inj_iff : natify.
Hint Rewrite <-N_to_nat_lt : natify.
Hint Rewrite <-N_to_nat_le : natify.
Hint Rewrite Nat2N.id : natify.
Hint Rewrite N2Nat.inj_add : natify.
Hint Rewrite N2Nat.inj_mul : natify.
Hint Rewrite N2Nat.inj_sub : natify.
Hint Rewrite N2Nat.inj_succ : natify.
Hint Rewrite N2Nat.inj_pred : natify.
Hint Rewrite N_to_nat_div : natify.
Hint Rewrite N_to_nat_0 : natify.
Hint Rewrite N_to_nat_1 : natify.
Ltac natify := repeat autorewrite with natify in *.

Hint Extern 100 (Nlt _ _) => natify : natify.
Hint Extern 100 (Nle _ _) => natify : natify.
Hint Extern 100 (@eq N _ _) => natify : natify.
Hint Extern 100 (lt _ _) => natify : natify.
Hint Extern 100 (le _ _) => natify : natify.
Hint Extern 100 (@eq nat _ _) => natify : natify.

Instance: ∀ x, PropHolds (0 < x)%N → PropHolds (0 < N.to_nat x).
Proof. unfold PropHolds. intros. by natify. Qed.
Instance: ∀ x, PropHolds (0 ≤ x)%N → PropHolds (0 ≤ N.to_nat x).
Proof. unfold PropHolds. intros. by natify. Qed.
