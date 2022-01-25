(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import hashset streams.
Require Import String stringmap.
Require Export executable frontend architecture_spec.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope ctype_scope.
Local Coercion Z.of_nat: nat >-> Z.

Record istate (K E : iType) : iType := IState {
  events_new : list E; (**i the events generated in the last step *)
  events_all : list E; (**i all previously generated events,
    including those in the last step *)
  sem_state : state K
}.
Arguments IState {_ _} _ _ _.
#[global] Instance istate_dec {K E} `{Env K, EqDecision E}: EqDecision (istate K E).
Proof. solve_decision. Defined.

Section interpreter.
Context (A : architecture).
Notation K := (arch_rank A).
Context `{EqDecision E}.
Context (e : ∀ `{Env K}, env K → state K → list E).
Notation M := (error (frontend_state K) string).

Fixpoint interpreter_args_go (args : list (list Z)) : M (list (val K)) :=
  match args with
  | [] => mret [ptrV (NULL (charT{K}))]
  | zs :: args =>
     '(v,n) ← error_of_option (to_string_const zs)
       "char of string constant out of range";
     o ← insert_object perm_full v;
     vs ← interpreter_args_go args;
     mret (ptrV (Ptr (addr_top_array o (charT{K}) (Z.of_nat n))) :: vs)
  end.
Definition interpreter_args (σs : list (type K))
    (args : list (list Z)) : M (list (val K)) :=
  if decide (σs = []) then mret (M := M) []
  else if decide (σs = [sintT; charT{K}.*.*])%T then
    vs ← interpreter_args_go args;
    o ← insert_object perm_full (VArray (charT{K}.*) vs);
    mret (M := M) [intV{sintT} (length vs);
          ptrV (Ptr (addr_top_array o (charT{K}.*) (length vs)))]
  else fail "function `main` should have argument types `int` and `char*`".
Definition interpreter_initial (Θ : list (string * decl))
    (args : list (list Z)) : M (istate K E) :=
  _ ← alloc_program Θ;
  Δg ← gets to_globals;
  '(_,σs,σ,_) ← error_of_option (Δg !! "main" ≫= maybe4 Fun)
    ("function `main` undeclared`");
  guard (σ = sintT%T ∨ σ = uintT%T) with
    ("function `main` should have return type `int`");
  vs ← interpreter_args σs args;
  m ← gets to_mem;
  mret (IState [] [] (initial_state m "main" vs)).
Definition interpreter_initial_eval (Θ : list (string * decl))
    (args : list (list Z)) : string + istate K E :=
  error_eval (interpreter_initial Θ args) ∅.

Definition cexec' (Γ : env K) (δ : funenv K)
    (iS : istate K E) : listset (istate K E) :=
  let (_,εs,S) := iS in
  (λ S_new,
    let εs_new := e _ Γ S_new in IState εs_new (εs ++ εs_new) S_new
  ) <$> cexec Γ δ S.

Context (hash : istate K E → Z).
Definition cexec_all (Γ : env K) (δ : funenv K) (iS : istate K E) :
    listset (istate K E) * listset (istate K E) :=
  let nexts := cexec' Γ δ iS in
  if decide (nexts ≡ ∅) then (∅, {[ iS ]}) else (nexts, ∅).
Definition csteps_exec_all (Γ : env K) (δ : funenv K) :
    listset (istate K E) →
    stream (listset (istate K E) * listset (istate K E)) :=
  cofix go iSs :=
  let nexts := cexec_all Γ δ <$> iSs in
  let reds := listset_normalize hash (nexts ≫= fst) in
  let nfs := listset_normalize hash (nexts ≫= snd) in
  (reds,nfs) :.: go reds.
Definition interpreter_all
    (Θ : list (string * decl)) (args : list (list Z)) :
    M (stream (listset (istate K E) * listset (istate K E))) :=
  iS ← interpreter_initial Θ args;
  Γ ← gets to_env; δ ← gets to_funenv;
  mret (csteps_exec_all Γ δ {[ iS ]}).
Definition interpreter_all_eval
    (Θ : list (string * decl)) (args : list (list Z)) :
    string + stream (listset (istate K E) * listset (istate K E)) :=
  error_eval (interpreter_all Θ args) ∅.

Context (rand : nat → nat).
Definition csteps_exec_rand (Γ : env K) (δ : funenv K) :
    istate K E → stream (istate K E + istate K E) :=
  cofix go iS :=
  match listset_car (cexec' Γ δ iS) with
  | [] => srepeat (inr iS)
  | (iS' :: _) as iSs =>
     let next := default iS' (iSs !! rand (length iSs)) in
     inl next :.: go next
  end.
Definition interpreter_rand
    (Θ : list (string * decl)) (args : list (list Z)) :
    M (stream (istate K E + istate K E)) :=
  iS ← interpreter_initial Θ args;
  Γ ← gets to_env; δ ← gets to_funenv;
  mret (csteps_exec_rand Γ δ iS).
Definition interpreter_rand_eval
    (Θ : list (string * decl)) (args : list (list Z)) :
    string + stream (istate K E + istate K E) :=
  error_eval (interpreter_rand Θ args) ∅.
End interpreter.
