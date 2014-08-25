(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String hashset streams.
Require Export executable frontend natural_type_environment two_complement.
Local Open Scope string_scope.

Section interpreter.
Context (be : bool) (Csz : nat).
Notation Ti := (irank be Csz).
Context (ptr_size : type Ti → nat) (align_base : base_type Ti → nat).
Context  (hash : state Ti → Z).

Let interpreter_env := (natural_env ptr_size align_base).
Existing Instance interpreter_env.

Definition cstep_exec' (Γ : env Ti) (δ : funenv Ti)
    (S : state Ti) : listset (state Ti) * listset (state Ti) :=
  let Ss := cstep_exec Γ δ S in
  if decide (listset_car Ss = []) then ({[ S ]}, ∅) else (∅, Ss).
Definition csteps_exec (Γ : env Ti) (δ : funenv Ti) :
    listset (state Ti) → stream (listset (state Ti) * listset (state Ti)) :=
  cofix go Ss :=
  let Sss := cstep_exec' Γ δ <$> Ss in
  let nfs := listset_normalize hash (Sss ≫= fst) in
  let reds := listset_normalize hash (Sss ≫= snd) in
  (nfs,reds) :.: go reds.
Definition interpreter (Θ : list (N * decl Ti))
    (f : funname) (ces : list (cexpr Ti)) :
    string + stream (listset (state Ti) * listset (state Ti)) :=
  '(Γn,Γ,Γf,δ,m,xs) ← to_envs Θ;
  '(σs,_) ← error_of_option (Γf !! f)
    "interpreter called for undeclared function";
  eσlrs ← mapM (to_expr Γn Γ Γf m xs) ces;
  let σes := zip_with to_R_NULL σs eσlrs in 
  guard (Forall2 (cast_typed Γ) (snd <$> σes) σs)
    with "interpreter called with arguments of incorrect type";
  let es := (cast{σs}* (fst <$> σes))%E in
  vs ← error_of_option (mapM (λ e, ⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr) es)
    "interpreter called with non-constant expressions";
  inr (csteps_exec Γ δ {[ initial_state m f vs ]}).
End interpreter.
