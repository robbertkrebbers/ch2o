From stdpp Require Import prelude.

Tactic Notation "simpl_option_monad" "by" tactic3(tac) :=
  let assert_Some_None A o H := first
    [ let x := fresh in evar (x:A); let x' := eval unfold x in x in clear x;
      assert (o = Some x') as H by tac
    | assert (o = None) as H by tac ]
  in repeat match goal with
  | H : context [@mret _ _ ?A] |- _ =>
     change (@mret _ _ A) with (@Some A) in H
  | |- context [@mret _ _ ?A] => change (@mret _ _ A) with (@Some A)
  | H : context [mbind (M:=option) (A:=?A) ?f ?o] |- _ =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
  | H : context [fmap (M:=option) (A:=?A) ?f ?o] |- _ =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
  | H : context [from_option (A:=?A) _ _ ?o] |- _ =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
  | H : context [from_option (A:=?A) _ _ ?o] |- _ =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
  | H : context [ match ?o with _ => _ end ] |- _ =>
    match type of o with
    | option ?A =>
      let Hx := fresh in assert_Some_None A o Hx; rewrite Hx in H; clear Hx
    end
  | |- context [mbind (M:=option) (A:=?A) ?f ?o] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [fmap (M:=option) (A:=?A) ?f ?o] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [from_option (A:=?A) _ _ ?o] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [from_option (A:=?A) _ _ ?o] =>
    let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
  | |- context [ match ?o with _ => _ end ] =>
    match type of o with
    | option ?A =>
      let Hx := fresh in assert_Some_None A o Hx; rewrite Hx; clear Hx
    end
  | H : context [decide _] |- _ => rewrite decide_True in H by tac
  | H : context [decide _] |- _ => rewrite decide_False in H by tac
  | H : context [mguard _ _] |- _ => rewrite option_guard_False in H by tac
  | H : context [mguard _ _] |- _ => rewrite option_guard_True in H by tac
  | _ => rewrite decide_True by tac
  | _ => rewrite decide_False by tac
  | _ => rewrite option_guard_True by tac
  | _ => rewrite option_guard_False by tac
  end.