(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export memory_injections.

(** The boolean argument is [false] in case the refinement is just a renaming,
and [true] in the case for example indeterminate bits may be refined into
actual bits. We combine renamings and actual refinements to avoid the need for
duplication. *)
Class RefineM K E A := refineM: E → bool → meminj K → relation A.
Class Refine K E A :=
  refine: E → bool → meminj K → memenv K → memenv K → A → A → Prop.
Class RefineTM K E T A :=
  refineTM: E → bool → meminj K → A → A → T → Prop.
Class RefineT K E T A :=
  refineT: E → bool → meminj K → memenv K → memenv K → A → A → T → Prop.
Class PathRefine K E T1 T2 A :=
  path_refine: E → bool →
    meminj K → memenv K → memenv K → A → A → T1 → T2 → Prop.
#[global] Instance: Params (@refineM) 5 := {}.
#[global] Instance: Params (@refine) 5 := {}.
#[global] Instance: Params (@refineTM) 6 := {}.
#[global] Instance: Params (@refineT) 6 := {}.
#[global] Instance: Params (@path_refine) 7 := {}.

Notation "X ⊑{ Γ , α , f } Y" := (refineM Γ α f X Y)
  (at level 70, format "X  ⊑{ Γ , α , f }  Y") : C_scope.
Notation "X ⊑{ Γ , α } Y" := (X ⊑{Γ,α,meminj_id} Y)
  (at level 70, format "X  ⊑{ Γ , α }  Y") : C_scope.

Notation "X ⊑{ Γ , α , f } Y : τ" := (refineTM Γ α f X Y τ)
  (at level 70, Y at next level,
   format "X  ⊑{ Γ , α , f }  Y  :  τ") : C_scope.
Notation "X ⊑{ Γ , α } Y : τ" := (X ⊑{Γ,α,meminj_id} Y : τ)
  (at level 70, Y at next level, format "X  ⊑{ Γ , α }  Y  :  τ") : C_scope.

Notation "X ⊑{ Γ , α , f @ m1 ↦ m2 } Y" := (refine Γ α f m1 m2 X Y)
  (at level 70, format "X  ⊑{ Γ , α , f  @  m1 ↦ m2 }  Y") : C_scope.
Notation "Xs ⊑{ Γ , α , f @ m1 ↦ m2 }* Ys" :=
  (Forall2 (refine Γ α f m1 m2) Xs Ys)
  (at level 70, format "Xs  ⊑{ Γ , α , f  @  m1 ↦ m2 }*  Ys") : C_scope.
Notation "Xss ⊑{ Γ , α , f @ m1 ↦ m2 }2** Yss" :=
  (Forall2 (λ Xs Ys, Xs.2 ⊑{Γ,α,f @ m1↦m2}* Ys.2) Xss Yss)
  (at level 70, format "Xss  ⊑{ Γ , α , f  @  m1 ↦ m2 }2**  Yss") : C_scope.
Notation "X ⊑{ Γ , α @ m } Y" := (X ⊑{Γ,α,meminj_id @ m↦m} Y)
  (at level 70, format "X  ⊑{ Γ , α  @  m }  Y") : C_scope.
Notation "Xs ⊑{ Γ , α @ m }* Ys" := (Xs ⊑{Γ,α,meminj_id @ m↦m}* Ys)
  (at level 70, format "Xs  ⊑{ Γ , α  @  m }*  Ys") : C_scope.
Notation "Xss ⊑{ Γ , α @ m }2** Yss" := (Xss ⊑{Γ,α,meminj_id @ m↦m}2** Yss)
  (at level 70, format "Xss  ⊑{ Γ , α  @  m }2**  Yss") : C_scope.

Notation "X ⊑{ Γ , α , f @ m1 ↦ m2 } Y : τ" := (refineT Γ α f m1 m2 X Y τ)
  (at level 70, Y at next level,
   format "X  ⊑{ Γ , α , f  @  m1 ↦ m2 }  Y  :  τ") : C_scope.
Notation "Xs ⊑{ Γ , α , f @ m1 ↦ m2 }* Ys : τ" :=
  (Forall2 (λ X Y, X ⊑{Γ,α,f @ m1↦m2} Y : τ) Xs Ys)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , α , f  @  m1 ↦ m2 }*  Ys  :  τ") : C_scope.
Notation "Xs ⊑{ Γ , α , f @ m1 ↦ m2 }* Ys :* τs" :=
  (Forall3 (refineT Γ α f m1 m2) Xs Ys τs)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , α , f  @  m1 ↦ m2 }*  Ys  :*  τs") : C_scope.
Notation "Xs ⊑{ Γ , α , f @ m1 ↦ m2 }1* Ys :* τs" :=
  (Forall3 (λ X Y τ, X.1 ⊑{Γ,α,f @ m1↦m2} Y.1 : τ) Xs Ys τs)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , α , f  @  m1 ↦ m2 }1*  Ys  :*  τs") : C_scope.
Notation "X ⊑{ Γ , α @ m } Y : τ" := (X ⊑{Γ,α,meminj_id @ m↦m} Y : τ)
  (at level 70, Y at next level,
   format "X  ⊑{ Γ , α  @  m }  Y  :  τ") : C_scope.
Notation "Xs ⊑{ Γ , α @ m }* Ys : τ" := (Xs ⊑{Γ,α,meminj_id@m↦m}* Ys : τ)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , α  @  m }*  Ys  :  τ") : C_scope.
Notation "Xs ⊑{ Γ , α @ m }* Ys :* τs" := (Xs ⊑{Γ,α,meminj_id@m↦m}* Ys :* τs)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , α @  m }*  Ys  :*  τs") : C_scope.
Notation "Xs ⊑{ Γ , α @ m }1* Ys :* τs" := (Xs ⊑{Γ,α,meminj_id@m↦m}1* Ys :* τs)
  (at level 70, Ys at next level,
   format "Xs  ⊑{ Γ , α  @  m }1*  Ys  :*  τs") : C_scope.

Notation "X ⊑{ Γ , α , f @ m1 ↦ m2 } Y : τ ↣ σ" :=
  (path_refine Γ α f m1 m2 X Y τ σ)
  (at level 70, Y at next level, τ at next level, σ at next level,
   format "X  ⊑{ Γ , α , f  @  m1 ↦ m2 }  Y  :  τ  ↣  σ") : C_scope.
Notation "X ⊑{ Γ , α @ m } Y : τ ↣ σ" :=
  (X ⊑{Γ,α,meminj_id@m↦m} Y : τ ↣ σ)
  (at level 70, Y at next level, τ at next level, σ at next level,
   format "X  ⊑{ Γ , α  @  m }  Y  :  τ  ↣  σ") : C_scope.

Ltac refine_constructor :=
  intros; match goal with
  | |- refineTM (RefineTM:=?T) ?Γ ?α ?f _ _ _ =>
    let T' := eval hnf in (T Γ α f) in
    econstructor; change T' with (refineTM (RefineTM:=T) Γ α f)
  | |- refineT (RefineT:=?T) ?Γ ?α ?f ?m1 ?m2 _ _ _ =>
    let T' := eval hnf in (T Γ α f m1 m2) in
    econstructor; change T' with (refineT (RefineT:=T) Γ α f m1 m2)
  | |- path_refine (PathRefine:=?T) ?Γ ?α ?f ?m1 ?m2 _ _ _ _ =>
    let T' := eval hnf in (T Γ α f m1 m2) in
    econstructor; change T' with (path_refine (PathRefine:=T) Γ α f m1 m2)
  end.
Ltac refine_inversion H :=
  match type of H with
  | refineTM (RefineTM:=?T) ?Γ ?α ?f _ _ _ =>
    let T' := eval hnf in (T Γ α f) in
    inversion H; clear H; simplify_equality'; try contradiction;
    try change T' with (refineTM (RefineTM:=T) Γ α f) in *
  | refineT (RefineT:=?T) ?Γ ?α ?f ?m1 ?m2 _ _ _ =>
    let T' := eval hnf in (T Γ α f m1 m2) in
    inversion H; clear H; simplify_equality'; try contradiction;
    try change T' with (refineT (RefineT:=T) Γ α f m1 m2) in *
  | path_refine (PathRefine:=?T) ?Γ ?α ?f ?m1 ?m2 _ _ _ _ =>
    let T' := eval hnf in (T Γ α f m1 m2) in
    inversion H; clear H; simplify_equality'; try contradiction;
    try change T' with (path_refine (PathRefine:=T) Γ α f m1 m2) in *
  end.
Ltac refine_inversion_all :=
  repeat match goal with
  | H : ?X ⊑{_,_,_} ?Y : _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  | H : ?X ⊑{_,_,_@_↦_} ?Y : _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  | H : ?X ⊑{_,_,_@_↦_} ?Y : _ ↣ _ |- _ =>
     first [is_var X; is_var Y; fail 1|refine_inversion H]
  end.
