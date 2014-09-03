(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String hashset streams.
Require Export executable frontend natural_type_environment two_complement.
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
Context (be : bool) (Csz : nat).
Notation Ti := (irank be Csz).
Context (ptr_size : type Ti → nat) (align_base : base_type Ti → nat).
Context {E : Set} `{∀ ε1 ε2 : E, Decision (ε1 = ε2)}.
Context (e : state Ti → list E).

Let interpreter_env := (natural_env ptr_size align_base).
Existing Instance interpreter_env.

Definition cstep_exec' (Γ : env Ti) (δ : funenv Ti)
    (iS : istate Ti E) : listset (istate Ti E) :=
  let (_,εs,S) := iS in
  (λ S_new,
    let εs_new := e S_new in IState εs_new (εs ++ εs_new) S_new
  ) <$> cstep_exec Γ δ S.
Definition interpreter_initial
    (Θ : list (N * decl Ti)) (f : funname) (ces : list (cexpr Ti)) :
    string + (env Ti * funenv Ti * istate Ti E) :=
  '(Γn,Γ,Γf,δ,m,xs) ← to_envs Θ;
  '(σs,_) ← error_of_option (Γf !! f)
    "interpreter called with undeclared function";
  eσlrs ← mapM (to_expr Γn Γ Γf m xs) ces;
  let σes := zip_with to_R_NULL σs eσlrs in 
  guard (Forall2 (cast_typed Γ) (snd <$> σes) σs)
    with "interpreter called with arguments of incorrect type";
  let es := (cast{σs}* (fst <$> σes))%E in
  vs ← error_of_option (mapM (λ e, ⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr) es)
    "interpreter called with non-constant expressions";
  inr (Γ, δ, IState [] [] (initial_state m f vs)).

Context (hash : istate Ti E → Z).
Definition cstep_exec_all (Γ : env Ti) (δ : funenv Ti) (iS : istate Ti E) :
    listset (istate Ti E) * listset (istate Ti E) :=
  let nexts := cstep_exec' Γ δ iS in
  if decide (nexts ≡ ∅) then (∅, {[ iS ]}) else (nexts, ∅).
Definition csteps_exec_all (Γ : env Ti) (δ : funenv Ti) :
    listset (istate Ti E) →
    stream (listset (istate Ti E) * listset (istate Ti E)) :=
  cofix go iSs :=
  let nexts := cstep_exec_all Γ δ <$> iSs in
  let nfs := listset_normalize hash (nexts ≫= fst) in
  let reds := listset_normalize hash (nexts ≫= snd) in
  (nfs,reds) :.: go reds.
Definition interpreter_all
    (Θ : list (N * decl Ti)) (f : funname) (ces : list (cexpr Ti)) :
    string +
    stream (listset (istate Ti E) * listset (istate Ti E)) :=
  '(Γ,δ,iS) ← interpreter_initial Θ f ces;
  inr (csteps_exec_all Γ δ {[ iS ]}).

Context (rand : nat → nat).

Definition csteps_exec_rand (Γ : env Ti) (δ : funenv Ti) :
    istate Ti E → stream (istate Ti E + istate Ti E) :=
  cofix go iS :=
  match listset_car (cstep_exec' Γ δ iS) with
  | [] => srepeat (inr iS)
  | (iS' :: _) as iSs =>
     let next := from_option iS' (iSs !! rand (length iSs)) in
     inl next :.: go next
  end.
Definition interpreter_rand
    (Θ : list (N * decl Ti)) (f : funname) (ces : list (cexpr Ti)) :
    string + stream (istate Ti E + istate Ti E) :=
  '(Γ,δ,iS) ← interpreter_initial Θ f ces;
  inr (csteps_exec_rand Γ δ iS).
End interpreter.
