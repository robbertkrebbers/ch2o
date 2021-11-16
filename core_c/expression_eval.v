(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file defines a denotational semantics [⟦ _ ⟧] for pure expressions as
an expression evaluator. It is parametrized by a map of function names to
denotations. We use this to enable convenient reasoning about pure functions
in our axiomatic semantics. *)
Require Export expressions type_system.

Local Open Scope expr_scope.

(** * Definition of the semantics *)
Reserved Notation "⟦ e ⟧" (format "⟦  e  ⟧").

Fixpoint expr_eval `{Env K} (e : expr K) (Γ : env K)
    (ρ : stack K) (m : mem K) : option (lrval K) :=
  match e with
  | var x =>
     '(o,τ) ← ρ !! x;
     Some (inl (Ptr (addr_top o τ)))
  | %#{Ω} ν => guard (Ω = ∅); Some ν
  | .* e =>
     v ← ⟦ e ⟧ Γ ρ m ≫= maybe inr;
     p ← maybe (VBase ∘ VPtr) v;
     guard (ptr_alive' m p);
     Some (inl p)
  | & e =>
     p ← ⟦ e ⟧ Γ ρ m ≫= maybe inl;
     Some (inr (ptrV p))
  | load e =>
     a ← ⟦ e ⟧ Γ ρ m ≫= maybe (inl ∘ Ptr);
     guard (mem_forced Γ a m);
     inr <$> m !!{Γ} a
  | e %> rs =>
     a ← ⟦ e ⟧ Γ ρ m ≫= maybe (inl ∘ Ptr);
     guard (addr_strict Γ a);
     Some (inl (Ptr (addr_elt Γ rs a)))
  | e #> rs =>
     v ← ⟦ e ⟧ Γ ρ m ≫= maybe inr;
     v' ← v !!{Γ} rs;
     Some (inr v')
  | .{op} e =>
     v ← ⟦ e ⟧ Γ ρ m ≫= maybe inr;
     guard (val_unop_ok m op v);
     Some (inr (val_unop op v))
  | e1 .{op} e2 =>
     v1 ← ⟦ e1 ⟧ Γ ρ m ≫= maybe inr;
     v2 ← ⟦ e2 ⟧ Γ ρ m ≫= maybe inr;
     guard (val_binop_ok Γ m op v1 v2);
     Some (inr (val_binop Γ op v1 v2))
  | if{e1} e2 else e3 =>
     vb ← ⟦ e1 ⟧ Γ ρ m ≫= maybe (inr ∘ VBase);
     guard (base_val_branchable m vb);
     if decide (base_val_is_0 vb) then ⟦ e3 ⟧ Γ ρ m else ⟦ e2 ⟧ Γ ρ m
  | e1 ,, e2 =>
     _ ← ⟦ e1 ⟧ Γ ρ m; ⟦ e2 ⟧ Γ ρ m
  | cast{τ} e =>
     v ← ⟦ e ⟧ Γ ρ m ≫= maybe inr;
     guard (val_cast_ok Γ m (TType τ) v);
     Some (inr (val_cast (TType τ) v))
  | #[r:=e1] e2 =>
     v1 ← ⟦ e1 ⟧ Γ ρ m ≫= maybe inr;
     v2 ← ⟦ e2 ⟧ Γ ρ m ≫= maybe inr;
     guard (is_Some (v2 !!{Γ} r));
     Some (inr (val_alter Γ (λ _, v1) r v2))
  | _ => None
  end
where "⟦ e ⟧" := (expr_eval e) : C_scope.

(** * Theorems *)
Section expression_eval.
Context `{EnvSpec K}.
Implicit Types Δ : memenv K.
Implicit Types e : expr K.
Implicit Types a : addr K.
Implicit Types v : val K.
Implicit Types ν : lrval K.
Implicit Types E : ectx K.

Hint Extern 0 (_ ⊢ _ : _) => typed_constructor: core.

Section expr_eval_ind.
Context (Γ : env K) (ρ : stack K) (m : mem K).
Context (P : expr K → lrval K → Prop).
Context (Pvar : ∀ τ x o,
  ρ !! x = Some (o,τ) → P (var x) (inl (Ptr (addr_top o τ)))).
Context (Pval : ∀ ν, P (%# ν) ν).
Context (Prtol : ∀ e p,
  ⟦ e ⟧ Γ ρ m = Some (inr (ptrV p)) → P e (inr (ptrV p)) →
  ptr_alive' m p → P (.* e) (inl p)).
Context (Profl : ∀ e p,
  ⟦ e ⟧ Γ ρ m = Some (inl p) → P e (inl p) → P (&e) (inr (ptrV p))).
Context (Peltl : ∀ e rs a,
  ⟦ e ⟧ Γ ρ m = Some (inl (Ptr a)) → P e (inl (Ptr a)) → addr_strict Γ a →
  P (e %> rs) (inl (Ptr (addr_elt Γ rs a)))).
Context (Pload : ∀ e a v,
  ⟦ e ⟧ Γ ρ m = Some (inl (Ptr a)) → P e (inl (Ptr a)) → mem_forced Γ a m →
  m !!{Γ} a = Some v → P (load e) (inr v)).
Context (Peltr : ∀ e rs v v',
  ⟦ e ⟧ Γ ρ m = Some (inr v) → P e (inr v) →
  v !!{Γ} rs = Some v' → P (e #> rs) (inr v')).
Context (Punop : ∀ op e v,
  ⟦ e ⟧ Γ ρ m = Some (inr v) → P e (inr v) →
  val_unop_ok m op v → P (.{op} e) (inr (val_unop op v))).
Context (Pbinop : ∀ op e1 e2 v1 v2,
  ⟦ e1 ⟧ Γ ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ ρ m = Some (inr v2) → P e2 (inr v2) →
  val_binop_ok Γ m op v1 v2 →
  P (e1 .{op} e2) (inr (val_binop Γ op v1 v2))).
Context (Pif1 : ∀ e1 e2 e3 vb ν2,
  ⟦ e1 ⟧ Γ ρ m = Some (inr (VBase vb)) → P e1 (inr (VBase vb)) →
  ⟦ e2 ⟧ Γ ρ m = Some ν2 → P e2 ν2 →
  base_val_branchable m vb → ¬base_val_is_0 vb → P (if{e1} e2 else e3) ν2).
Context (Pif2 : ∀ e1 e2 e3 vb ν3,
  ⟦ e1 ⟧ Γ ρ m = Some (inr (VBase vb)) → P e1 (inr (VBase vb)) →
  ⟦ e3 ⟧ Γ ρ m = Some ν3 → P e3 ν3 →
  base_val_branchable m vb → base_val_is_0 vb → P (if{e1} e2 else e3) ν3).
Context (Pcomma : ∀ e1 e2 ν1 ν2,
  ⟦ e1 ⟧ Γ ρ m = Some ν1 → P e1 ν1 →
  ⟦ e2 ⟧ Γ ρ m = Some ν2 → P e2 ν2 → P (e1,, e2) ν2).
Context (Pcast : ∀ τ e v,
  ⟦ e ⟧ Γ ρ m = Some (inr v) → P e (inr v) →
  val_cast_ok Γ m (TType τ) v → P (cast{τ} e) (inr (val_cast (TType τ) v))).
Context (Pinsert : ∀ r e1 e2 v1 v2,
  ⟦ e1 ⟧ Γ ρ m = Some (inr v1) → P e1 (inr v1) →
  ⟦ e2 ⟧ Γ ρ m = Some (inr v2) → P e2 (inr v2) → is_Some (v2 !!{Γ} r) →
  P (#[r:=e1] e2) (inr (val_alter Γ (λ _, v1) r v2))).
Lemma expr_eval_ind : ∀ e ν, ⟦ e ⟧ Γ ρ m = Some ν → P e ν.
Proof.
  induction e using @expr_ind_alt; intros;
    repeat first [progress simplify_option_eq | case_match]; eauto.
Qed.
End expr_eval_ind.

Lemma EVal_expr_eval Γ ρ m v : ⟦ #v ⟧ Γ ρ m = Some (inr v).
Proof. done. Qed.
Lemma EVals_expr_eval Γ ρ m Ωs vs :
  length Ωs = length vs →
  ⋃ Ωs = ∅ → mapM (λ e, ⟦ e ⟧ Γ ρ m ≫= maybe inr) (#{Ωs}* vs) = Some vs.
Proof.
  rewrite empty_union_list_L. rewrite <-Forall2_same_length.
  induction 1; intros; decompose_Forall; simplify_option_eq; auto.
Qed.
Lemma Forall2_expr_eval_val_inv Γ ρ m Ωs vs vs' :
  length Ωs = length vs →
  Forall2 (λ e v, ⟦ e ⟧ Γ ρ m ≫= maybe inr = Some v) (#{Ωs}* vs) vs' →
  vs = vs'.
Proof.
  rewrite <-Forall2_same_length. intros HΩvs. revert vs'.
  induction HΩvs; simpl; intros; decompose_Forall;
    simplify_option_eq; f_equal; eauto.
Qed.
Lemma expr_eval_typed_aux Γ Δ τs ρ m e ν τlr :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ ρ m = Some ν → ✓{Δ}* ρ →
  ρ.*2 `prefix_of` τs → (Γ,Δ,τs) ⊢ e : τlr → (Γ,Δ) ⊢ ν : τlr.
Proof.
  intros ?? Hν ? [τs' ->] He. revert e ν Hν τlr He.
  apply (expr_eval_ind Γ ρ m (λ e _, ∀ τlr, _ ⊢ e : τlr → (_:Prop))); intros;
    repeat match goal with
    | _ => progress typed_inversion_all
    | _ => progress decompose_Forall_hyps
    | H : (?ρ.*2 ++ ?τs) !! ?i = Some ?τ1, H2 : ?ρ !! _ = Some (_,?τ2) |- _ =>
      assert ((ρ.*2 ++ τs) !! i = Some τ) by
        (apply lookup_app_l_Some; by rewrite list_lookup_fmap, H2)
    | H : _ ⊢ ?e : _, H2 : ∀ _, _ ⊢ ?e : _  → _ |- _ => specialize (H2 _ H)
    end; try typed_constructor; eauto using
      val_unop_typed, val_binop_typed, val_cast_typed, addr_top_typed,
      cmap_index_typed_valid, addr_top_strict,
      addr_elt_typed, addr_elt_strict, addr_elt_typed, addr_elt_strict,
      val_lookup_seg_typed, val_alter_const_typed, mem_lookup_typed.
Qed.
Lemma expr_eval_typed Γ Δ ρ m e ν τlr :
  ✓ Γ → ✓{Γ,Δ} m → ⟦ e ⟧ Γ ρ m = Some ν → ✓{Δ}* ρ →
  (Γ,Δ,ρ.*2) ⊢ e : τlr → (Γ,Δ) ⊢ ν : τlr.
Proof. intros. eapply expr_eval_typed_aux; eauto. Qed.

Lemma expr_eval_weaken Γ1 Γ2 Δ1 ρ1 ρ2 m1 m2 e ν τlr :
  ✓ Γ1 → ✓{Γ1,Δ1} m1 → ✓{Δ1}* ρ1 →
  (Γ1,Δ1,ρ1.*2) ⊢ e : τlr → ⟦ e ⟧ Γ1 ρ1 m1 = Some ν → Γ1 ⊆ Γ2 →
  (∀ o, index_alive '{m1} o → index_alive '{m2} o) →
  (∀ a v σ, (Γ1,Δ1) ⊢ a : TType σ →
    m1 !!{Γ1} a = Some v → m2 !!{Γ2} a = Some v) →
  (∀ a σ, (Γ1,Δ1) ⊢ a : TType σ →
    mem_forced Γ1 a m1 → is_Some (m1 !!{Γ1} a) → mem_forced Γ2 a m2) →
  ρ1 `prefix_of` ρ2 → ⟦ e ⟧ Γ2 ρ2 m2 = Some ν.
Proof.
  intros ??? He Hν ???? [ρ3 ->]. revert e ν Hν τlr He.
  apply (expr_eval_ind Γ1 ρ1 m1
    (λ e _, ∀ τlr, _ ⊢ e : τlr → (_:Prop))); simpl; intros; typed_inversion_all;
    repeat match goal with
    | H: ⟦ ?e ⟧ Γ1 ρ1 m1 = Some ?ν,  _: (Γ1,Δ1,ρ1.*2) ⊢ ?e : ?τlr |- _ =>
      feed pose proof (expr_eval_typed Γ1 Δ1 ρ1 m1 e ν τlr); auto;
      clear H
    end; typed_inversion_all; auto.
  * rewrite lookup_app_l by eauto using lookup_lt_Some.
    by simplify_option_eq.
  * by simplify_option_eq by eauto using ptr_alive_weaken'.
  * by simplify_option_eq.
  * simplify_option_eq by eauto using addr_strict_weaken.
    by erewrite <-addr_elt_weaken by eauto.
  * by simplify_option_eq.
  * by simplify_option_eq by eauto using val_lookup_seg_weaken.
  * by simplify_option_eq by eauto using val_unop_ok_weaken.
  * simplify_option_eq by eauto using val_binop_ok_weaken.
    by erewrite <-val_binop_weaken by eauto.
  * simplify_option_eq by eauto using base_val_branchable_weaken; eauto.
  * simplify_option_eq by eauto using base_val_branchable_weaken; eauto.
  * simplify_option_eq; eauto.
  * by simplify_option_eq by eauto using val_cast_ok_weaken.
  * simplify_option_eq by eauto using val_lookup_weaken_is_Some.
    by erewrite <-val_alter_weaken by eauto.
Qed.
Lemma expr_eval_weaken_empty Γ1 Γ2 Δ1 ρ1 ρ2 e ν τlr :
  ✓ Γ1 → ✓{Γ1} Δ1 → ✓{Δ1}* ρ1 →
  (Γ1,Δ1,ρ1.*2) ⊢ e : τlr → ⟦ e ⟧ Γ1 ρ1 ∅ = Some ν → Γ1 ⊆ Γ2 →
  ρ1 `prefix_of` ρ2 → ⟦ e ⟧ Γ2 ρ2 ∅ = Some ν.
Proof.
  intros; eapply expr_eval_weaken; eauto using cmap_empty_valid;
    by intros *; rewrite mem_lookup_empty, <-?not_eq_None_Some.
Qed.
Lemma expr_eval_erase Γ ρ m e : ⟦ e ⟧ Γ ρ (cmap_erase m) = ⟦ e ⟧ Γ ρ m.
Proof.
  by destruct e using @expr_ind_alt; simpl;
    repeat match goal with
    | H : ⟦ _ ⟧ _ _ _ = _ |- _ => rewrite H
    | H : context [ptr_alive'] |- _ => rewrite ptr_alive_erase' in H
    | H : context [base_val_branchable] |- _ => rewrite base_val_branchable_erase in H
    | H : context [val_unop_ok] |- _ => rewrite val_unop_ok_erase in H
    | H : context [val_binop_ok] |- _ => rewrite val_binop_ok_erase in H
    | H : context [val_cast_ok] |- _ => rewrite val_cast_ok_erase in H
    | H : context [mem_forced] |- _ => rewrite mem_forced_erase in H
    | _ => apply option_bind_ext_fun; intros
    | _ => case_option_guard; try done
    | _ => rewrite mem_lookup_erase
    | _ => case_match
    end.
Qed.

(** Pure expressions without variables do not refer to the stack, so their
semantics is preserved under changes to the stack. *)
Lemma expr_eval_var_free Γ ρ1 ρ2 m e : vars e = ∅ → ⟦ e ⟧ Γ ρ1 m = ⟦ e ⟧ Γ ρ2 m.
Proof.
  induction e using expr_ind_alt; simpl; intro; repeat
    match goal with
    | H : vars _ = ∅ → ⟦ _ ⟧ _ _ _ = _ |- _ => rewrite H
    | H : ⋃ _ = ∅ |- _ => rewrite empty_union_list_L in H
    | _ => done
    end; set_solver.
Qed.

(** Lifting DeBruijn indexes distributes over expression evaluation. *)
Lemma expr_eval_lift Γ ρ m e : ⟦ e↑ ⟧ Γ ρ m = ⟦ e ⟧ Γ (tail ρ) m.
Proof.
  induction e using expr_ind_alt; intros; simpl; repeat
    match goal with
    | H : ⟦ _↑ ⟧ _ _ _ = _ |- _ => rewrite H
    end; rewrite <-?lookup_tail; auto.
Qed.

(** The semantics is preserved under substitution. *)
Lemma subst_preserves_expr_eval Γ ρ m E e1 e2 :
  ⟦ e1 ⟧ Γ ρ m = ⟦ e2 ⟧ Γ ρ m → ⟦ subst E e1 ⟧ Γ ρ m = ⟦ subst E e2 ⟧ Γ ρ m.
Proof.
  intros. induction E as [|E' ? IH] using rev_ind; [done |].
  destruct E'; rewrite ?subst_snoc; simpl; rewrite ?IH; auto.
Qed.

(** If an expression has a semantics, then each sub-expression of that
expression has a semantics too. *)
Lemma expr_eval_subst Γ ρ m E e ν :
  ⟦ subst E e ⟧ Γ ρ m = Some ν ↔
  ∃ ν', ⟦ e ⟧ Γ ρ m = Some ν' ∧ ⟦ subst E (%# ν') ⟧ Γ ρ m = Some ν.
Proof.
  split; [|by intros (ν'&?&<-); apply subst_preserves_expr_eval].
  revert ν. induction E as [|E' E IH] using rev_ind; simpl; intros ν; eauto.
  setoid_rewrite subst_snoc.
  intros; destruct E';
    repeat match goal with
    | _ => progress simplify_option_eq
    | H : mapM _ _ = Some _ |- _ => apply mapM_Some in H; decompose_Forall_hyps
    | H : ∀ _, Some _ = Some _  → _ |- _ =>
       specialize (H _ eq_refl); destruct H as (?&->&?); eexists; split; eauto
    end; auto.
Qed.
End expression_eval.
