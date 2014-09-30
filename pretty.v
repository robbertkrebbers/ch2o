(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export numbers option.
Require Import Ascii String ars.

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
Definition pretty_N_go (x : N)
    (go : ∀ y, (y < x)%N → string → string) (s : string) : string :=
  match decide (0 < x)%N with
  | left H => go (x `div` 10)%N (N.div_lt x 10 H eq_refl)
     (String (pretty_N_char (x `mod` 10)) s)
  | right _ => s
  end.
Instance pretty_N : Pretty N := λ x,
  Fix_F _ pretty_N_go (wf_guard 32 N.lt_wf_0 x) ""%string.
Instance pretty_N_injective : Injective (@eq N) (=) pretty.
Proof.
  assert (∀ x y, x < 10 → y < 10 →
    pretty_N_char x =  pretty_N_char y → x = y)%N.
  { compute; intros. by repeat (discriminate || case_match). }
  set (f x (acc : Acc _ x) := Fix_F _ pretty_N_go acc).
  cut (∀ x acc y acc' s s', length s = length s' →
    f x acc s = f y acc' s' → x = y ∧ s = s').
  { intros help x y ?. eapply help; eauto. }
  assert (∀ x acc s, ¬length (f x acc s) < length s) as help.
  { setoid_rewrite <-Nat.le_ngt.
    fix 2; intros x [?] s; simpl. unfold pretty_N_go; fold pretty_N_go.
    destruct (decide (0 < x))%N; [|auto].
    etransitivity; [|eauto]. simpl; lia. }
  fix 2; intros x [?] y [?] s s' ?; simpl.
  unfold pretty_N_go; fold pretty_N_go; intros Hs.
  destruct (decide (0 < x))%N, (decide (0 < y))%N;
    try match goal with
    | H : f ?x ?acc ?s = _ |- _ =>
       destruct (help x acc s); rewrite H; simpl; lia
    | H : _ = f ?x ?acc ?s |- _ =>
       destruct (help x acc s); rewrite <-H; simpl; lia
    end; auto with lia.
  apply pretty_N_injective in Hs; [|by f_equal']; destruct Hs.
  simplify_equality; split; [|done].
  rewrite (N.div_mod x 10), (N.div_mod y 10) by done.
  auto using N.mod_lt with f_equal.
Qed.
Instance pretty_Z : Pretty Z := λ x,
  match x with
  | Z0 => "" | Zpos x => pretty (Npos x) | Zneg x => "-" +:+ pretty (Npos x)
  end%string.
