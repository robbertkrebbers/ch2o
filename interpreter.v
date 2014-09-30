(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String hashset streams stringmap.
Require Export executable frontend architecture_spec.
Local Open Scope string_scope.
Local Open Scope list_scope.

Record istate (Ti E : Set) := IState {
  events_new : list E; (**i the events generated in the last step *)
  events_all : list E; (**i all previously generated events,
    including those in the last step *)
  sem_state : state Ti
}.
Arguments IState {_ _} _ _ _.
Instance istate_dec {Ti E : Set}
  `{∀ k1 k2 : Ti, Decision (k1 = k2), ∀ ε1 ε2 : E, Decision (ε1 = ε2)}
  (iS1 iS2 : istate Ti E) : Decision (iS1 = iS2).
Proof. solve_decision. Defined.

Section interpreter.
Context (A : architecture).
Notation Ti := (irank A).
Context {E : Set} `{∀ ε1 ε2 : E, Decision (ε1 = ε2)}.
Context (e : ∀ `{Env Ti}, env Ti → state Ti → list E).

Definition cexec' (Γ : env Ti) (δ : funenv Ti)
    (iS : istate Ti E) : listset (istate Ti E) :=
  let (_,εs,S) := iS in
  (λ S_new,
    let εs_new := e _ Γ S_new in IState εs_new (εs ++ εs_new) S_new
  ) <$> cexec Γ δ S.
Definition interpreter_initial
    (Θ : list (string * decl)) (f : string) (ces : list cexpr) :
    string + (env Ti * funenv Ti * istate Ti E) :=
  '(Γn,Γ,m,Δg) ← to_envs Θ;
  '(_,σs,_,_) ← error_of_option (Δg !! f ≫= maybe_Fun)
    ("interpreter called with undeclared function `" +:+ f +:+ "`");
  eσlrs ← mapM (to_expr Γn Γ m Δg []) ces;
  let σes := zip_with to_R_NULL σs eσlrs in 
  guard (Forall2 (cast_typed Γ) (snd <$> σes) σs)
    with "interpreter called with arguments of incorrect type";
  let es := (cast{σs}* (fst <$> σes))%E in
  vs ← error_of_option (mapM (λ e, ⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr) es)
    "interpreter called with non-constant expressions";
  inr (Γ, to_funenv Δg, IState [] [] (initial_state m f vs)).

Context (hash : istate Ti E → Z).
Definition cexec_all (Γ : env Ti) (δ : funenv Ti) (iS : istate Ti E) :
    listset (istate Ti E) * listset (istate Ti E) :=
  let nexts := cexec' Γ δ iS in
  if decide (nexts ≡ ∅) then (∅, {[ iS ]}) else (nexts, ∅).
Definition csteps_exec_all (Γ : env Ti) (δ : funenv Ti) :
    listset (istate Ti E) →
    stream (listset (istate Ti E) * listset (istate Ti E)) :=
  cofix go iSs :=
  let nexts := cexec_all Γ δ <$> iSs in
  let reds := listset_normalize hash (nexts ≫= fst) in
  let nfs := listset_normalize hash (nexts ≫= snd) in
  (reds,nfs) :.: go reds.
Definition interpreter_all
    (Θ : list (string * decl)) (f : string) (ces : list cexpr) :
    string + stream (listset (istate Ti E) * listset (istate Ti E)) :=
  '(Γ,δ,iS) ← interpreter_initial Θ f ces;
  inr (csteps_exec_all Γ δ {[ iS ]}).

Context (rand : nat → nat).

Definition csteps_exec_rand (Γ : env Ti) (δ : funenv Ti) :
    istate Ti E → stream (istate Ti E + istate Ti E) :=
  cofix go iS :=
  match listset_car (cexec' Γ δ iS) with
  | [] => srepeat (inr iS)
  | (iS' :: _) as iSs =>
     let next := from_option iS' (iSs !! rand (length iSs)) in
     inl next :.: go next
  end.
Definition interpreter_rand
    (Θ : list (string * decl)) (f : string) (ces : list cexpr) :
    string + stream (istate Ti E + istate Ti E) :=
  '(Γ,δ,iS) ← interpreter_initial Θ f ces;
  inr (csteps_exec_rand Γ δ iS).
End interpreter.
