(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export addresses.

Local Open Scope ctype_scope.

Inductive ptr (K : iType) : iType :=
  | NULL : ptr_type K → ptr K
  | Ptr : addr K → ptr K
  | FunPtr : funname → list (type K) → type K → ptr K.
Arguments NULL {_} _.
Arguments Ptr {_} _.
Arguments FunPtr {_} _ _ _.

#[global] Instance ptr_eq_dec `{EqDecision K}: EqDecision (ptr K).
Proof. solve_decision. Defined.

#[global] Instance maybe_NULL {K} : Maybe (@NULL K) := λ p,
  match p with NULL τ => Some τ | _ => None end.
#[global] Instance maybe_Ptr {K} : Maybe (@Ptr K) := λ p,
  match p with Ptr a => Some a | _ => None end.
#[global] Instance maybe_FunPtr {K} : Maybe3 (@FunPtr K) := λ p,
  match p with FunPtr f τs τ => Some (f,τs,τ) | _ => None end.

Section pointer_operations.
  Context `{EqDecision K, Env K}.

  Inductive ptr_typed' (Γ : env K) (Δ : memenv K) :
      ptr K → ptr_type K → Prop :=
    | NULL_typed τp : ✓{Γ} τp → ptr_typed' Γ Δ (NULL τp) τp
    | Ptr_typed a τp : (Γ,Δ) ⊢ a : τp → ptr_typed' Γ Δ (Ptr a) τp
    | FunPtr_typed f τs τ :
       Γ !! f = Some (τs,τ) → ptr_typed' Γ Δ (FunPtr f τs τ) (τs ~> τ).
  Global Instance ptr_typed:
    Typed (env K * memenv K) (ptr_type K) (ptr K) := uncurry ptr_typed'.
  Global Instance ptr_freeze : Freeze (ptr K) := λ β p,
    match p with Ptr a => Ptr (freeze β a) | _ => p end.

  Global Instance type_of_ptr: TypeOf (ptr_type K) (ptr K) := λ p,
    match p with
    | NULL τp => τp
    | Ptr a => type_of a
    | FunPtr _ τs τ => τs ~> τ
    end.
   Global Instance ptr_type_check:
      TypeCheck (env K * memenv K) (ptr_type K) (ptr K) := λ ΓΔ p,
    let (Γ,Δ) := ΓΔ in
    match p with
    | NULL τp => guard (✓{Γ} τp); Some τp
    | Ptr a => type_check (Γ,Δ) a
    | FunPtr f τs τ =>
       '(τs',τ') ← Γ !! f; guard (τs' = τs); guard (τ' = τ); Some (τs ~> τ)
    end.
  Inductive is_NULL : ptr K → Prop := mk_is_NULL τ : is_NULL (NULL τ).
  Definition ptr_alive (Δ : memenv K) (p : ptr K) : Prop :=
    match p with Ptr a => index_alive Δ (addr_index a) | _ => True end.
End pointer_operations.

Section pointers.
Context `{EqDecision K, EnvSpec K}.
Implicit Types Γ : env K.
Implicit Types Δ : memenv K.
Implicit Types τp : ptr_type K.
Implicit Types a : addr K.
Implicit Types p : ptr K.

Lemma Ptr_typed_inv Γ Δ a τp : (Γ, Δ) ⊢ Ptr a : τp → (Γ, Δ) ⊢ a : τp.
Proof. by inversion 1. Qed.
#[global] Instance: Inj (=) (=) (@Ptr K).
Proof. by injection 1. Qed.
Lemma ptr_typed_type_valid Γ Δ p τp : ✓ Γ → (Γ,Δ) ⊢ p : τp → ✓{Γ} τp.
Proof.
  destruct 2; eauto using addr_typed_ptr_type_valid, TFun_ptr_valid,
    env_valid_args_valid, env_valid_ret_valid, type_valid_ptr_type_valid.
Qed.
#[global] Instance: TypeOfSpec (env K * memenv K) (ptr_type K) (ptr K).
Proof.
  intros [??]. by destruct 1; simpl; erewrite ?type_of_correct by eauto.
Qed.
#[global] Instance:
  TypeCheckSpec (env K * memenv K) (ptr_type K) (ptr K) (λ _, True).
Proof.
  intros [Γ Δm] p τ _. split.
  * destruct p; intros; repeat (case_match || simplify_option_eq);
      constructor; auto; by apply type_check_sound.
  * by destruct 1; simplify_option_eq;
      erewrite ?type_check_complete by eauto.
Qed.
Lemma ptr_typed_weaken Γ1 Γ2 Δ1 Δ2 p τp :
  ✓ Γ1 → (Γ1,Δ1) ⊢ p : τp → Γ1 ⊆ Γ2 → Δ1 ⇒ₘ Δ2 → (Γ2,Δ2) ⊢ p : τp.
Proof.
  destruct 2; constructor;
    eauto using ptr_type_valid_weaken, addr_typed_weaken, lookup_fun_weaken.
Qed.
Lemma ptr_freeze_freeze β1 β2 p : freeze β1 (freeze β2 p) = freeze β1 p.
Proof. destruct p; f_equal'; auto using addr_freeze_freeze. Qed.
Lemma ptr_typed_freeze Γ Δ β p τp : (Γ,Δ) ⊢ freeze β p : τp ↔ (Γ,Δ) ⊢ p : τp.
Proof.
  split.
  * destruct p; inversion_clear 1; constructor; auto.
    by apply addr_typed_freeze with β.
  * destruct 1; constructor; auto. by apply addr_typed_freeze.
Qed.
Lemma ptr_type_of_freeze β p : type_of (freeze β p) = type_of p.
Proof. by destruct p; simpl; rewrite ?addr_type_of_freeze. Qed.
#[global] Instance is_NULL_dec p : Decision (is_NULL p).
Proof.
 refine match p with NULL _ => left _ | _ => right _ end;
   first [by constructor | abstract by inversion 1].
Defined.
Lemma ptr_alive_weaken Δ1 Δ2 p :
  ptr_alive Δ1 p → (∀ o, index_alive Δ1 o → index_alive Δ2 o) →
  ptr_alive Δ2 p.
Proof. destruct p; simpl; auto. Qed.
Lemma ptr_dead_weaken Γ Δ1 Δ2 p τp :
  (Γ,Δ1) ⊢ p : τp → ptr_alive Δ2 p → Δ1 ⇒ₘ Δ2 → ptr_alive Δ1 p.
Proof. destruct 1; simpl; eauto using addr_dead_weaken. Qed.
#[global] Instance ptr_alive_dec Δ p : Decision (ptr_alive Δ p).
Proof. destruct p; apply _. Defined.
End pointers.
