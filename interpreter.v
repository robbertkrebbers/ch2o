(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export executable frontend natural_type_environment two_complement.

Section interpreter.
Context (be : bool) (Csz : nat).
Notation Ti := (irank be Csz).
Context (ptr_size : type Ti → nat) (align_base : base_type Ti → nat).
Context  (hash : state Ti → Z).

Let ptr_env := (natural_ptr_env ptr_size align_base).
Existing Instance ptr_env.

Definition interpreter (Θ : list (N * decl Ti))
    (f : funname) (vs : list (val Ti)) :
    option (stream (listset (state Ti) * listset (state Ti))) :=
  '(_,Γ,Γf,δ,m,_) ← to_envs Θ;
  '(σs,_) ← Γf !! f;
  σs' ← mapM (type_check (Γ,m)) vs;
  guard (σs' = (σs : list (type Ti)));
  Some (csteps_exec hash Γ δ {[ initial_state m f vs ]}).
End interpreter.
