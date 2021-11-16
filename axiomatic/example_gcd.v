(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String axiomatic_simple.

Section gcd.
Context `{EnvSpec K}.
Hint Extern 10 (Some Readable ⊆ _) => transitivity (Some Writable): core.
Hint Extern 0 (perm_locked _ = _) =>
  apply perm_Readable_locked; auto : typeclass_instances.

Hint Resolve ax_load' ax_var' assert_memext_l' assert_eval_int_cast_self'
  assert_memext_r' assert_and_l assert_singleton_eval assert_int_typed_eval
  assert_eval_singleton_r assert_eval_singleton_l assert_and_intro : exec.
Ltac exec :=
  repeat match goal with A := _ : assert _ |- _ => progress unfold A end;
  simpl; eauto 20 with exec.

Definition gcd_stmt : stmt K :=
  "l" :; if{load (var 1)} local{uintT} (
    !(var 2 ::= (
        var 0 ::= load (var 1) .{ArithOp ModOp} load (var 2),,
        var 1 ::= load (var 2),,
        load (var 0)));;
    goto "l"
  ) else skip.
Lemma gcd_typed : (∅,∅,[uintT%T;uintT%T]) ⊢ gcd_stmt : (false,None).
Proof.
  change false with (true && false).
  repeat (apply SLocal_typed || typed_constructor
                             || constructor); try set_solver.
  apply base_binop_type_of_sound; simpl.
  by rewrite (idemp_L _), int_promote_int.
Qed.
Lemma gcd_correct Γ δ R J T C y z μ1 γ1 μ2 γ2 :
  sep_valid γ1 → Some Writable ⊆ perm_kind γ1 →
  sep_valid γ2 → Some Writable ⊆ perm_kind γ2 →
  J "l"%string ≡{Γ,δ} (∃ y' z',
    ⌜ Z.gcd y' z' = Z.gcd y z ⌝%Z ★
    var 0 ↦{μ1,γ1} #intV{uintT} y' : uintT ★
    var 1 ↦{μ2,γ2} #intV{uintT} z' : uintT)%A →
  Γ\ δ\ R\ J\ T\ C ⊨ₛ
    {{ var 0 ↦{μ1,γ1} #intV{uintT} y : uintT ★
       var 1 ↦{μ2,γ2} #intV{uintT} z : uintT }}
      gcd_stmt
    {{ var 0 ↦{μ1,γ1} #intV{uintT} (Z.gcd y z) : uintT ★
       var 1 ↦{μ2,γ2} #intV{uintT} 0 : uintT }}.
Proof.
  intros ???? HJ; eapply ax_comp.
  { eapply ax_stmt_weaken_pre, ax_label; rewrite HJ.
    apply assert_exist_intro with y, assert_exist_intro with z.
    by rewrite assert_Prop_l by done. }
  eapply ax_stmt_weaken_pre; [by rewrite HJ|].
  apply ax_stmt_exist_pre; intros y'; apply ax_stmt_exist_pre; intros z'.
  apply ax_stmt_Prop_pre; try set_solver; intros Hgcd.
  eapply ax_stmt_weaken_pre.
  { by rewrite (assert_singleton_int_typed' _ _ (var 0)),
      (assert_singleton_int_typed' _ _ (var 1)), (assoc (★)%A),
      (comm _ _ (⌜ int_typed z' _ ⌝)%A), <-!(assoc (★)%A). }
  apply ax_stmt_Prop_pre; try set_solver; intros Hz'.
  apply ax_stmt_Prop_pre; try set_solver; intros Hy'.
  eapply ax_if'' with (intV{uintT} z')%B; auto.
  { apply ax_expr_frame_l'.
    rewrite (assert_singleton_l _ _ (var 1)) at 1.
    apply ax_expr_exist_pre; intros a1.
    eapply ax_expr_weaken_post';
      [by rewrite <-(assert_singleton_l_2 Γ _ (var 1) _ _ _ a1)|exec]. }
  { by eapply assert_exist_intro, assert_eval_int_unop';
      auto using assert_memext_r', assert_eval_singleton_r. }
  { apply ax_stmt_Prop_pre; try set_solver; simpl; intros.
    apply ax_local.
    set (R' v := (var 0 ↦{false,perm_full} - : uintT%BT ★ R v↑)%A).
    set (J' l := (var 0 ↦{false,perm_full} - : uintT%BT ★ (J l)↑)%A).
    set (T' n := (var 0 ↦{false,perm_full} - : uintT%BT ★ (T n)↑)%A).
    set (C' mz := (var 0 ↦{false,perm_full} - : uintT%BT ★ (C mz)↑)%A).
    rewrite !assert_lift_sep, !assert_lift_singleton; simpl.
    apply ax_comp with (
        var 0 ↦{false,perm_full} #intV{uintT} (y' `mod` z') : uintT
      ★ var 1 ↦{μ1,γ1} #intV{uintT} z' : uintT
      ★ var 2 ↦{μ2,γ2} #intV{uintT} (y' `mod` z') : uintT)%A.
    * eapply ax_do' with _ (inr (intV{uintT} (y' `mod` z')));
        [|by rewrite <-!assert_unlock_sep,
                     <-(assert_lock_singleton _ _ (var 2)), <-2!unlock_indep].
      rewrite (assert_singleton_l_ _ _ (var 0)), assert_exist_sep.
      apply ax_expr_exist_pre; intros a_tmp.
      eapply ax_expr_weaken_post';
        [by rewrite <-(assert_singleton_l_2 Γ _ (var 0) _ _ _ a_tmp)|].
      rewrite <-!(assoc (★)%A); apply ax_expr_invariant_l'.
      rewrite (right_id _ (★)%A), (assert_singleton_l _ _ (var 1)),
        (assert_exist_sep (A:=ptr _)), (assert_sep_exist (A:=ptr _)).
      apply ax_expr_exist_pre; intros a_y.
      eapply ax_expr_weaken_post';
        [by rewrite <-(assert_singleton_l_2 Γ _ (var 1) _ _ _ a_y)|].
      rewrite !(assoc (★)%A), !(comm (★)%A _ (_ ∧ _)%A).
      rewrite <-!(assoc (★)%A); apply ax_expr_invariant_l'.
      rewrite (assert_singleton_l _ _ (var 2)), !(assert_sep_exist (A:=ptr _)).
      apply ax_expr_exist_pre; intros a_z.
      eapply ax_expr_weaken_post';
        [by rewrite <-(assert_singleton_l_2 Γ _ (var 2) _ _ _ a_z)|].
      rewrite <-!(comm (★)%A _ (var 2 ⇓ _ ∧ _)%A), !(assoc (★)%A).
      apply ax_expr_invariant_r'.
      set (A' := ((var 2 ⇓ inl a_z ∧ emp) ★
        (var 1 ⇓ inl a_y ∧ emp) ★ var 0 ⇓ inl a_tmp ∧ emp)%A).
      rewrite <-!(assoc (★)%A).
      eapply ax_assign_r' with
        (%a_tmp ↦{false,perm_full} #intV{uintT} (y' `mod` z') : uintT
        ★ %a_y ↦{μ1,γ1} #intV{uintT} z' : uintT
        ★ %a_z ↦{μ2,γ2} #intV{uintT} z' : uintT)%A
        μ2 γ2 uintT%T a_z (intV{uintT} (y' `mod` z')) _; try by exec.
      { eapply ax_expr_comma' with
          (%a_tmp ↦{false,perm_full} #intV{uintT} (y' `mod` z') : uintT
          ★ %a_y ↦{μ1,γ1} #intV{uintT} y' : uintT
          ★ %a_z ↦{μ2,γ2} #intV{uintT} z' : uintT)%A
          (inr (intV{uintT} (y' `mod` z'))).
        { eapply ax_expr_weaken_post'; [by rewrite <-!assert_unlock_sep,
            <-(assert_lock_singleton _ _ (%a_tmp)), <-2!unlock_indep by done|].
          apply ax_expr_invariant_r'.
          set (A'' := ((%a_y ↦{μ1,γ1} #intV{uintT} y' : uintT%BT
            ★ %a_z ↦{μ2,γ2} #intV{uintT} z' : uintT%BT) ★ A')%A).
          eapply ax_assign_r' with _ _ perm_full
            uintT%T _ (intV{uintT} (y' `mod` z')) _.
          * exec.
          * eapply ax_binop_r'; try by exec.
            eapply assert_eval_int_arithop'; try by exec.
            + by simpl; rewrite (idemp_L _), int_promote_int.
            + by simpl; rewrite int_pre_cast_self by done.
            + simpl; rewrite !int_pre_cast_self by done.
              apply int_typed_unsigned_nonneg in Hy'.
              apply int_typed_unsigned_nonneg in Hz'.
              by rewrite Z.rem_mod_nonneg by lia.
          * cut (int_typed (y' `mod` z') uintT); [exec|].
            rewrite int_typed_spec_alt in Hz', Hy' |- *; simpl in *.
            split; [apply Z.mod_pos_bound;lia|].
            transitivity z'; [apply Z.mod_pos_bound|]; lia.
          * rewrite <-(right_id _ (★)%A) at 1.
            apply assert_sep_preserving, assert_wand_intro;
              rewrite ?(left_id _ (★)%A); eauto using assert_exist_intro.
          * done. }
        eapply ax_expr_comma' with _ (inr (intV{uintT} z')); [|exec].
        eapply ax_expr_weaken_post'; [by rewrite <-!assert_unlock_sep,
          <-(assert_lock_singleton _ _ (%a_y)), <-2!unlock_indep by done|].
        apply ax_expr_frame_l', ax_expr_invariant_r'.
        set (A'' := (%a_z ↦{μ2,γ2} #intV{uintT} z' : uintT%BT ★ A')%A).
        eapply ax_assign_r' with _ _ γ1 uintT%T _ (intV{uintT} z') _; try exec.
        * rewrite <-(right_id _ (★)%A);
          apply assert_sep_preserving, assert_wand_intro;
            rewrite ?(left_id _ (★)%A); eauto using assert_exist_intro. }
      { rewrite !(assoc (★)%A),
          (comm (★)%A _ (%a_z ↦{_,_} _ : _)%A).
        eauto using assert_sep_preserving,
          assert_wand_intro, assert_exist_intro. }
    * eapply ax_stmt_weaken_pre, ax_goto.
      apply assert_sep_preserving; eauto using assert_exist_intro.
      rewrite HJ; repeat setoid_rewrite (assert_lift_exists Γ δ).
      apply assert_exist_intro with z', assert_exist_intro with (y' `mod` z')%Z.
      rewrite !assert_lift_sep, !assert_lift_singleton, stack_indep; simpl.
      assert (Z.gcd z' (y' `mod` z') = Z.gcd y z).
      { by rewrite Z.gcd_comm, Z.gcd_mod, Z.gcd_comm by lia. }
      by rewrite assert_Prop_l by auto using Z_mod_pos, Z.gcd_mod with lia. }
  { eapply ax_stmt_weaken_pre, ax_skip; simpl.
    apply assert_Prop_intro_l; intros ->.
    by rewrite Z.gcd_0_r_nonneg in Hgcd
      by eauto using int_typed_unsigned_nonneg; subst. }
Qed.
End gcd.
