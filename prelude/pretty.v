(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export numbers option.
Require Import Ascii String relations.

Infix "+:+" := String.append (at level 60, right associativity) : C_scope.
Arguments String.append _ _ : simpl never.

Instance assci_eq_dec : ∀ a1 a2, Decision (a1 = a2) := ascii_dec.
Instance string_eq_dec (s1 s2 : string) : Decision (s1 = s2).
Proof. solve_decision. Defined.
Instance: Injective (=) (=) (String.append s1).
Proof. intros s1 ???. induction s1; simplify_equality'; f_equal'; auto. Qed.

Class Pretty A := pretty : A → string.
Definition pretty_N_char (x : N) : ascii :=
  match x with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
  end%char%N.
Fixpoint pretty_N_go_help (x : N) (acc : Acc (<)%N x) (s : string) : string :=
  match decide (0 < x)%N with
  | left H => pretty_N_go_help (x `div` 10)%N
     (Acc_inv acc (N.div_lt x 10 H eq_refl))
     (String (pretty_N_char (x `mod` 10)) s)
  | right _ => s
  end.
Definition pretty_N_go (x : N) : string → string :=
  pretty_N_go_help x (wf_guard 32 N.lt_wf_0 x).
Lemma pretty_N_go_0 s : pretty_N_go 0 s = s.
Proof. done. Qed.
Lemma pretty_N_go_help_irrel x acc1 acc2 s :
  pretty_N_go_help x acc1 s = pretty_N_go_help x acc2 s.
Proof.
  revert x acc1 acc2 s; fix 2; intros x [acc1] [acc2] s; simpl.
  destruct (decide (0 < x)%N); auto.
Qed.
Lemma pretty_N_go_step x s :
  (0 < x)%N → pretty_N_go x s
  = pretty_N_go (x `div` 10) (String (pretty_N_char (x `mod` 10)) s).
Proof.
  unfold pretty_N_go; intros; destruct (wf_guard 32 N.lt_wf_0 x).
  unfold pretty_N_go_help; fold pretty_N_go_help.
  by destruct (decide (0 < x)%N); auto using pretty_N_go_help_irrel.
Qed.
Instance pretty_N : Pretty N := λ x, pretty_N_go x ""%string.
Instance pretty_N_injective : Injective (@eq N) (=) pretty.
Proof.
  assert (∀ x y, x < 10 → y < 10 →
    pretty_N_char x =  pretty_N_char y → x = y)%N.
  { compute; intros. by repeat (discriminate || case_match). }
  cut (∀ x y s s', pretty_N_go x s = pretty_N_go y s' →
    length s = length s' → x = y ∧ s = s').
  { intros help x y ?. eapply help; eauto. }
  assert (∀ x s, ¬length (pretty_N_go x s) < length s) as help.
  { setoid_rewrite <-Nat.le_ngt.
    intros x; induction (N.lt_wf_0 x) as [x _ IH]; intros s.
    assert (x = 0 ∨ 0 < x)%N as [->|?] by lia; [by rewrite pretty_N_go_0|].
    rewrite pretty_N_go_step by done.
    etransitivity; [|by eapply IH, N.div_lt]; simpl; lia. }
  intros x; induction (N.lt_wf_0 x) as [x _ IH]; intros y s s'.
  assert ((x = 0 ∨ 0 < x) ∧ (y = 0 ∨ 0 < y))%N as [[->|?] [->|?]] by lia;
    rewrite ?pretty_N_go_0, ?pretty_N_go_step, ?(pretty_N_go_step y) by done.
  { done. }
  { intros -> Hlen; edestruct help; rewrite Hlen; simpl; lia. }
  { intros <- Hlen; edestruct help; rewrite <-Hlen; simpl; lia. }
  intros Hs Hlen; apply IH in Hs; destruct Hs;
    simplify_equality'; split_ands'; auto using N.div_lt_upper_bound with lia.
  rewrite (N.div_mod x 10), (N.div_mod y 10) by done.
  auto using N.mod_lt with f_equal.
Qed.
Instance pretty_Z : Pretty Z := λ x,
  match x with
  | Z0 => "" | Zpos x => pretty (Npos x) | Zneg x => "-" +:+ pretty (Npos x)
  end%string.
