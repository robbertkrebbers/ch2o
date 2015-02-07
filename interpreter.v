(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String hashset streams stringmap.
Require Export executable frontend architecture_spec.
Local Open Scope string_scope.
Local Open Scope list_scope.

Record istate (K E : Set) := IState {
  events_new : list E; (**i the events generated in the last step *)
  events_all : list E; (**i all previously generated events,
    including those in the last step *)
  sem_state : state K
}.
Arguments IState {_ _} _ _ _.
Instance istate_dec {K E : Set} `{Env K, ∀ ε1 ε2 : E, Decision (ε1 = ε2)}
  (iS1 iS2 : istate K E) : Decision (iS1 = iS2).
Proof. solve_decision. Defined.

Local Notation M := (error (frontend_state _) string).

Section interpreter.
Context (A : architecture).
Notation K := (arch_rank A).
Context {E : Set} `{∀ ε1 ε2 : E, Decision (ε1 = ε2)}.
Context (e : ∀ `{Env K}, env K → state K → list E).

Definition cexec' (Γ : env K) (δ : funenv K)
    (iS : istate K E) : listset (istate K E) :=
  let (_,εs,S) := iS in
  (λ S_new,
    let εs_new := e _ Γ S_new in IState εs_new (εs ++ εs_new) S_new
  ) <$> cexec Γ δ S.
Definition interpreter_initial (Θ : list (string * decl))
    (f : string) (ces : list cexpr) : M (istate K E) :=
  _ ← alloc_program Θ;
  Δg ← gets to_globals;
  '(_,σs,_,_) ← error_of_option (Δg !! f ≫= maybe_Fun)
    ("interpreter called with undeclared function `" +:+ f +:+ "`");
  eσlrs ← mapM (to_expr []) ces;
  let σes := zip_with to_R_NULL σs eσlrs in
  Γ ← gets to_env; m ← gets to_mem;
  guard (Forall2 (cast_typed Γ) (snd <$> σes) σs)
    with "interpreter called with arguments of incorrect type";
  let es := (cast{σs}* (fst <$> σes))%E in
  vs ← error_of_option (mapM (λ e, ⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr) es)
    "interpreter called with non-constant expressions";
  mret (IState [] [] (initial_state m f vs)).
Definition interpreter_initial_eval (Θ : list (string * decl))
    (f : string) (ces : list cexpr) : string + istate K E :=
  error_eval (interpreter_initial Θ f ces) ∅.

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
    (Θ : list (string * decl)) (f : string) (ces : list cexpr) :
    M (stream (listset (istate K E) * listset (istate K E))) :=
  iS ← interpreter_initial Θ f ces;
  Γ ← gets to_env; δ ← gets to_funenv;
  mret (csteps_exec_all Γ δ {[ iS ]}).
Definition interpreter_all_eval
    (Θ : list (string * decl)) (f : string) (ces : list cexpr) :
    string + stream (listset (istate K E) * listset (istate K E)) :=
  error_eval (interpreter_all Θ f ces) ∅.

Context (rand : nat → nat).
Definition csteps_exec_rand (Γ : env K) (δ : funenv K) :
    istate K E → stream (istate K E + istate K E) :=
  cofix go iS :=
  match listset_car (cexec' Γ δ iS) with
  | [] => srepeat (inr iS)
  | (iS' :: _) as iSs =>
     let next := from_option iS' (iSs !! rand (length iSs)) in
     inl next :.: go next
  end.
Definition interpreter_rand
    (Θ : list (string * decl)) (f : string) (ces : list cexpr) :
    M (stream (istate K E + istate K E)) :=
  iS ← interpreter_initial Θ f ces;
  Γ ← gets to_env; δ ← gets to_funenv;
  mret (csteps_exec_rand Γ δ iS).
Definition interpreter_rand_eval
    (Θ : list (string * decl)) (f : string) (ces : list cexpr) :
    string + stream (istate K E + istate K E) :=
  error_eval (interpreter_rand Θ f ces) ∅.
End interpreter.
