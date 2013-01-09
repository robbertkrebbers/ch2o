(* Copyright (c) 2012, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This contains a verification of Euclid's algorithm to compute the greatest
common divisor using the axiomatic semantics. *)
Require Import axiomatic.
Coercion EVar : nat >-> expr.
Coercion EVal : value >-> expr.
Ltac simplify := repeat
  match goal with
  | |- _ => progress simplify_option_equality
  | |- _ => progress simplify_map_equality
  | H : context [ lookup (A:=?A) ?i ?m ] |- _ => progress (
     let x := fresh in evar (x:A);
     let x' := eval unfold x in x in clear x;
     let E := fresh in
     assert (m !! i = Some x') as E by (clear H; eauto with simpl_map);
     rewrite E in H; clear E)
  end.

(** * The program *)
Definition swap_stmt := block (
  0 ::= load (load 1);;
  load 1 ::= load (load 2);;
  load 2 ::= load 0).
Definition gcd_stmt L SWAP :=
  L :; (IF load (var 1)
  then 0 ::= load 0 `mod` load 1;;
    call SWAP @ [var 0; var 1];;
    goto L
  else skip);;
  ret (Some (load (var 0))).

(** * Verification *)
Lemma swap_spec δ Δ (p q x y : value) :
  δ \ Δ ⊨ₜ {{ 0 ↦ p ★ 1 ↦ q ★ p ↦ x ★ q ↦ y }}
             swap_stmt
           {{ λ _, 0 ↦ p ★ 1 ↦ q ★ p ↦ y ★ q ↦ x }}.
Proof.
  apply ax_stmt_top_unfold, ax_block. repeat
    (setoid_rewrite assert_lift_sep
  || setoid_rewrite stack_indep_lift
  || setoid_rewrite assert_lift_singleton). simpl.
  setoid_rewrite (right_absorb False%A (★)%A).
  set (R := (λ _ : option value, 0 ↦ - ★ 1 ↦ p ★ 2 ↦ q ★ p ↦ y ★ q ↦ x)%A).
  set (J:= (λ _ : label, False)%A).
  apply ax_comp with (0 ↦ x ★ 1 ↦ p ★ 2 ↦ q ★ p ↦ x ★ q ↦ y)%A.
  { rewrite !(associative (★) (2 ↦ q))%A,
      (commutative (★) (2 ↦ q))%A, <-(associative (★))%A.
    apply ax_assign_sep; [done |].
    rewrite (associative (★))%A. apply (assert_sep_elim_l _ _ _ _).
    rewrite <-(assert_expr_load _ p), <-!assert_assign_load.
    apply assert_and_intro.
    * apply (assert_sep_elim_l _ _ _ _), assert_singleton_assign.
    * apply (assert_sep_elim_r _ _ _ _), assert_singleton_assign. }
  apply ax_comp with (0 ↦ x ★ 1 ↦ p ★ 2 ↦ q ★ p ↦ y ★ q ↦ y)%A.
  { rewrite !(commutative (★) (0 ↦ x))%A,
      !(associative (★) (2 ↦ q))%A, !(commutative (★) (2 ↦ q))%A.
    rewrite <-!(associative (★)%A).
    apply ax_stmt_weak_pre with (1 ↦ p ★ p ↦ - ★ 2 ↦ q ★ q ↦ y ★ 0 ↦ x)%A.
    { by rewrite (assert_singleton_forget p x). }
    apply ax_assign_load_sep; [done | done |].
    rewrite (associative (★))%A. apply (assert_sep_elim_l _ _ _ _).
    rewrite <-(assert_expr_load _ q), <-!assert_assign_load.
    apply assert_and_intro.
    * apply (assert_sep_elim_l _ _ _ _), assert_singleton_assign.
    * apply (assert_sep_elim_r _ _ _ _), assert_singleton_assign. }
  rewrite !(commutative (★) (p ↦ y))%A, !(associative (★) (2 ↦ q))%A.
  rewrite !(commutative (★) (1 ↦ p))%A, (commutative (★) (0 ↦ _))%A.
  rewrite (commutative (★) (0 ↦ -))%A, <-!(associative (★))%A.
  apply ax_stmt_weak_pre with (2 ↦ q ★ q ↦ - ★ p ↦ y ★ 1 ↦ p ★ 0 ↦ x)%A.
  { by rewrite (assert_singleton_forget q y). }
  apply ax_stmt_weak_post with (2 ↦ q ★ q ↦ x ★ p ↦ y ★ 1 ↦ p ★ 0 ↦ x)%A.
  { by rewrite (assert_singleton_forget 0 x). }
  apply ax_assign_load_sep; [done | done |].
  rewrite <-assert_assign_load. do 2 apply (assert_sep_elim_r _ _ _ _).
  apply assert_singleton_assign.
Qed.

Definition swap_fassert : fassert.
 refine {|
  fcommon := value * value;
  fpre := λ vs ps,
    match vs,ps with (v0,v1), [p0;p1] => p0 ↦ v0 ★ p1 ↦ v1 | _,_ => False end%A;
  fpost := λ vs ps _,
    match vs,ps with (v0,v1), [p0;p1] => p0 ↦ v1 ★ p1 ↦ v0 | _,_ => False end%A
  |}; intros; apply _.
Defined.

Lemma swap_call δ Δ J R SWAP e1 e2 (x y : value) :
  expr_load_free e1 →
  expr_load_free e2 →
  δ !! SWAP = Some swap_stmt →
  δ\ Δ\ J\ R ⊨ {{ e1 ↦ x ★ e2 ↦ y }} call SWAP @ [e1;e2] {{ e1 ↦ y ★ e2 ↦ x }}.
Proof.
  intros. set (Δ' := {[ (SWAP, swap_fassert) ]} : fassert_env).
  apply ax_stmt_add_funs with Δ'.
  { intros f Pf. unfold Δ'.
    rewrite lookup_singleton_Some. intros [??]; subst; eauto. }
  { intros f Pf sf c vs. unfold Δ'.
    rewrite lookup_singleton_Some. intros [??] ?. simplify_map_equality.
    destruct c as [v w], vs as [|p [|q [|??]]]; simpl; try
      (setoid_rewrite (right_absorb False (★))%A;
       auto using ax_stmt_top_false_pre).
    setoid_rewrite (right_id emp (★))%A. setoid_rewrite <-(associative (★))%A.
    eapply ax_stmt_top_weak with
      (R:=(λ _, 0 ↦ p ★ 1 ↦ q ★ p ↦ w ★ q ↦ v)%A), swap_spec; [|done].
    intro. by rewrite !(assert_singleton_forget (var _)). }
  eapply ax_stmt_weak_pre, ax_stmt_weak_post, ax_call_alt
    with (Pf:=swap_fassert) (P:=λ vs,
    match vs with
    | [a1;a2] => e1 ⇓ a1 ∧ e2 ⇓ a2
    | _ => False
    end%A) (c:=(x,y)).
  * simpl. intros ?? (?&?&?&?&(a1&?&?&?&?)&(a2&?&?&?&?)). subst.
    exists [ptr a1;ptr a2]%V. simpl. split.
    + unfold_assert. simpl. repeat split; eauto with cstep.
    + solve_assert.
  * simpl. apply assert_exists_elim. intro vs.
    apply assert_exists_elim. simpl. intros _.
    destruct vs as [|p1 [| p2 [|??]]]; try solve_assert.
    rewrite <-(assert_singleton_eval_l e1 p1).
    rewrite <-(assert_singleton_eval_l e2 p2).
    rewrite <-(associative (∧))%A, (commutative (∧) (e2 ⇓ _))%A.
    rewrite <-assert_and_sep_assoc, assert_sep_and_assoc by apply _.
    by rewrite (commutative (∧) (e2 ⇓ _))%A.
  * intros [|? [| ? [|??]]]; apply _.
  * unfold Δ'. by simpl_map.
  * intros [|? [| ? [|??]]]; solve_assert.
Qed.

Lemma gcd_spec δ Δ L SWAP (x y : Z) :
  δ !! SWAP = Some swap_stmt →
  (0 ≤ x)%Z → (0 ≤ y)%Z →
  δ\ Δ ⊨ₜ {{ 0 ↦ (int x)%V ★ 1 ↦ (int y)%V }}
    gcd_stmt L SWAP
  {{ λ mv, (0 ↦ - ★ 1 ↦ -) ∧
      match mv with Some (int z)%V => ⌜ z = Z.gcd x y ⌝ | _ => False end }}.
Proof.
  intros Hδ ??. apply ax_stmt_top_unfold.
  set (R := (λ mv, (0 ↦ - ★ 1 ↦ -) ∧
    match mv with Some (VInt z) => ⌜ z = Z.gcd x y ⌝ | _ => False end)%A).
  set (J := (λ l, if decide (l = L)
    then ∃ x' y', (0 ↦ (int x')%V ★ 1 ↦ (int y')%V) ∧
      ⌜ (0 ≤ x')%Z ∧ (0 ≤ y')%Z ∧ Z.gcd x' y' = Z.gcd x y ⌝
    else False)%A).
  apply ax_stmt_weak_jmp with J.
  { solve_assert. }
  { intro. unfold J, gcd_stmt. case_decide; solve_elem_of. }
  assert (J L ≡ ∃ x' y',(0 ↦ (int x')%V ★ 1 ↦ (int y')%V) ∧
    ⌜ (0 ≤ x')%Z ∧ (0 ≤ y')%Z ∧ Z.gcd x' y' = Z.gcd x y ⌝)%A as HJ.
  { unfold J. case_decide; intuition. }
  unfold gcd_stmt. apply ax_label_alt.
  { rewrite HJ. intros ρ m ?. exists x y. split; solve_assert. }
  apply ax_comp with (0 ↦ (int (Z.gcd x y))%V ★ 1 ↦ int 0)%A.
  { apply ax_if_alt.
    { rewrite HJ. apply assert_exists_elim. intros x'.
      apply assert_exists_elim. intros y'.
      apply assert_and_elim_l. apply (assert_sep_elim_r _ _ _ _).
      by rewrite assert_singleton_forget, assert_singleton_load_. }
    { rewrite HJ. repeat setoid_rewrite assert_and_exists.
      apply (ax_stmt_ex_pre _ _). intro x'.
      apply (ax_stmt_ex_pre _ _). intro y'.
      eapply ax_comp with ((0 ↦ (int (x' `mod` y'))%V ★ 1 ↦ (int y')%V)
        ∧ ⌜ (0 ≤ x')%Z ∧ (0 < y')%Z ∧ Z.gcd x' y' = Z.gcd x y ⌝)%A.
      { eapply ax_stmt_weak_pre, ax_assign_alt.
        intros ρ m ((?&?&?)&(?&?&?&?&(a0&?&?&?&?)&(a1&?&?&?&?))&?&?&?).
        unfold_assert in *. simplify.
        exists a0 (int (x' `mod` y'))%V. repeat split; auto.
        * exists a0 (int x')%V. by simplify.
        * exists {[(a0, (int (x' `mod` y'))%V)]} {[(a1, (int y')%V)]}.
            repeat split.
          + by rewrite insert_union_l, insert_singleton.
          + solve_mem_disjoint.
          + exists a0 (int (x' `mod` y'))%V. by simplify.
          + exists a1 (int y')%V. by simplify.
        * lia. }
      eapply ax_comp with (J L), ax_goto.
      apply ax_stmt_weak_post with ((0 ↦ (int y')%V ★ 1 ↦ (int (x' `mod` y'))%V)
        ∧ ⌜ (0 ≤ x')%Z ∧ (0 < y')%Z ∧ Z.gcd x' y' = Z.gcd x y ⌝)%A.
      { rewrite HJ. intros ?? (?&?&?&?). exists y' (x' `mod` y')%Z.
        split; [done |]. repeat split.
        * lia.
        * apply Z_mod_lt. lia.
        * rewrite Z.gcd_comm, Z.gcd_mod, Z.gcd_comm; lia. }
      rewrite !(assert_and_sep_emp_r _ ⌜ _ ⌝%A _).
      apply ax_stmt_weak_ret with (λ _, False)%A; [done |].
      apply ax_stmt_weak_jmp with (λ _, False)%A.
      { simpl. solve_elem_of. }
      { simpl. by repeat intro. }
      by apply ax_stmt_frame_simple_r, swap_call. }
    eapply ax_stmt_weak_pre, ax_skip. rewrite HJ.
    intros ρ m (Heq & x'&y' & (m1&m2&?&?&Hx&Hy) & Hx'&Hy'& Hgcd).
    assert (y' = 0)%Z.
    { destruct Hy as (?&?&?&?&?). destruct Heq as (?&?&?).
      unfold_assert in *. by simplify. }
    subst. exists m1 m2. repeat split; auto.
    by rewrite <-Hgcd, Z.gcd_0_r_nonneg by done. }
  eapply ax_stmt_weak_pre, ax_return_Some with (v:=(int (Z.gcd x y))%V).
  simpl. repeat apply assert_and_intro.
  * apply (assert_sep_elim_l _ _ _ _), assert_singleton_load.
  * by rewrite !assert_singleton_forget.
  * done.
Qed.

Definition gcd_fassert : fassert.
 refine {|
  fcommon := unit;
  fpre := λ _ vs,
    match vs with
    | [VInt x; VInt y] => ⌜ (0 ≤ x)%Z ∧ (0 ≤ y)%Z ⌝ ∧ emp
    | _ => False%A
    end%A;
  fpost := λ _ vs mv,
    (match vs, mv with
    | [VInt x; VInt y], Some (VInt z) => ⌜ z = Z.gcd x y ⌝
    | _,_ => False
    end ∧ emp)%A
  |}; intros; repeat case_match; apply _.
Defined.

Lemma gcd_call δ Δ J R Q SWAP L GCD e e1 e2 a x y :
  expr_load_free e1 →
  expr_load_free e2 →
  (0 ≤ x)%Z → (0 ≤ y)%Z →
  δ !! SWAP = Some swap_stmt →
  δ !! GCD = Some (gcd_stmt L SWAP) →
  δ\ Δ\ J\ R ⊨ {{ e⇓ptr a ∧ e1⇓int x ∧ e2⇓int y
                          ∧ ptr a ↪ - ∧ <[a:=int (Z.gcd x y)]>Q }}
                 e ::= call GCD @ [e1;e2]
               {{ Q }}.
Proof.
  intros. set (Δ' := {[ (GCD, gcd_fassert) ]} : fassert_env).
  apply ax_stmt_add_funs with Δ'.
  { intros f Pf. unfold Δ'.
    rewrite lookup_singleton_Some. intros [??]; subst; eauto. }
  { intros f Pf sf c vs. unfold Δ'.
    rewrite lookup_singleton_Some. intros [??] ?. simplify_map_equality.
    destruct vs as [|[] [|[] [|??]]]; simpl; try
      (setoid_rewrite (right_absorb False (★))%A;
       auto using ax_stmt_top_false_pre).
    setoid_rewrite (right_id emp (★))%A.
    setoid_rewrite <-(assert_and_sep_emp_r _ _ _).
    apply ax_stmt_top_and_Prop_pre. intros [??]. by apply gcd_spec. }
  eapply ax_stmt_weak_pre, ax_call_Some with
    (Pf:=gcd_fassert) (c:=()) (vs:=[int x; int y]%V)
    (B:=True%A) (A:=(e⇓ptr a ∧ ptr a↪- ∧ <[a:=int (Z.gcd x y)]>Q)%A)
    (a:=a) (v:=(int (Z.gcd x y))%V).
  * simpl. rewrite <-(assert_and_sep_emp_r _ _ _). solve_assert.
  * apply _.
  * unfold Δ'. by simpl_map.
  * solve_assert.
  * simpl. intros [[|z|]|];
      rewrite <-?(assert_and_sep_emp_r _ _ _); solve_assert.
Qed.
