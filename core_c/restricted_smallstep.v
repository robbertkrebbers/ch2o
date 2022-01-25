(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** To give a model of our axiomatic semantics, among other things, we
consider the traversal through the program with a restriction of the
program context. The local variable part of the part we cut off is still
relevant, and is thus added as an additional parameter. *)
Require Import tactics.
Require Export smallstep.

Fixpoint rlocals {K} (ρ : stack K) (k : ctx K) : stack K :=
  match k with
  | [] => ρ
  | CStmt _ :: k | CExpr _ _ :: k => rlocals ρ k
  | CLocal o τ :: k => (o,τ) :: rlocals ρ k
  | CFun _ :: _ => []
  | CParams _ oτs :: _ => oτs
  end.

Reserved Notation "Γ \ δ \ ρ ⊢ₛ S1 ⇒ S2"
  (at level 74, δ at next level, ρ at next level,
   format "Γ \  δ \  ρ  ⊢ₛ  '[' S1  ⇒ '/'  S2 ']'").
Inductive rcstep `{Env K} (Γ : env K)
    (δ : funenv K) (ρ : stack K) : relation (state K) :=
  (**i For simple statements: *)
  | rcstep_skip m k :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ skip) m ⇒
                State k (Stmt ↗ skip) m
  | rcstep_goto m k l :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (goto l)) m ⇒
                State k (Stmt (↷ l) (goto l)) m
  | rcstep_throw m k n :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (throw n)) m ⇒
                State k (Stmt (↑ n) (throw n)) m
  | cstep_case m k mx :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (scase mx)) m ⇒
                State k (Stmt ↗ (scase mx)) m
  | rcstep_in_label m k l :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (label l)) m ⇒
                State k (Stmt ↗ (label l)) m
  | rcstep_expr m k E e :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (subst E e)) m ⇒
                State (CExpr e E :: k) (Expr e) m

  (**i For expressions: *)
  | rcstep_expr_head m1 m2 k (E : ectx K) e1 e2 :
     Γ\ rlocals ρ k ⊢ₕ e1, m1 ⇒ e2, m2 →
     Γ\ δ\ ρ ⊢ₛ State k (Expr (subst E e1)) m1 ⇒
                State k (Expr (subst E e2)) m2
  | rcstep_expr_call m k Ω f τs τ E Ωs vs :
     length Ωs = length vs →
     let e := (call %{Ω} (FunPtr f τs τ) @ #{Ωs}* vs)%E in
     Γ\ δ\ ρ ⊢ₛ State k (Expr (subst E e)) m ⇒
                State (CFun E :: k) (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m)
  | rcstep_expr_undef m k (E : ectx K) e :
     is_redex e → ¬Γ \ rlocals ρ k ⊢ₕ safe e, m →
     Γ\ δ\ ρ ⊢ₛ State k (Expr (subst E e)) m ⇒
                State k (Undef (UndefExpr E e)) m

  (**i For finished expressions: *)
  | rcstep_expr_do m k e Ω v :
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (! □) :: k) (Expr (#{Ω} v)) m ⇒
                State k (Stmt ↗ (! e)) (mem_unlock Ω m)
  | rcstep_expr_ret m k e Ω v :
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (ret □) :: k) (Expr (#{Ω} v)) m ⇒
                State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m)
  | rcstep_expr_if_true m k e Ω vb s1 s2 :
     base_val_branchable m vb → ¬base_val_is_0 vb →
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} VBase vb)) m ⇒
                State (CStmt (if{e} □ else s2) :: k)
                  (Stmt ↘ s1) (mem_unlock Ω m)
  | rcstep_expr_if_false m k e Ω vb s1 s2 :
     base_val_branchable m vb → base_val_is_0 vb →
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} VBase vb)) m ⇒
                State (CStmt (if{e} s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m)
  | rcstep_expr_if_indet m k e Ω vb s1 s2 :
     ¬base_val_branchable m vb →
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} VBase vb)) m ⇒
                State k (Undef (UndefBranch (if{□} s1 else s2) Ω (VBase vb))) m
  | rcstep_switch_case m k e Ω τi x s :
     Some x ∈ cases s →
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} (intV{τi} x))) m ⇒
                State (CStmt (switch{e} □) :: k)
                      (Stmt (↓ (Some x)) s) (mem_unlock Ω m)
  | rcstep_switch_default m k e Ω τi x s :
     Some x ∉ cases s → None ∈ cases s →
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} (intV{τi} x))) m ⇒
                State (CStmt (switch{e} □) :: k)
                      (Stmt (↓ None) s) (mem_unlock Ω m)
  | rcstep_switch_out m k e Ω τi x s :
     Some x ∉ cases s → None ∉ cases s →
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} (intV{τi} x))) m ⇒
                State k (Stmt ↗ (switch{e} s)) (mem_unlock Ω m)
  | rcstep_switch_indet m k e Ω vb s :
     ¬base_val_branchable m vb →
     Γ\ δ\ ρ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} VBase vb)) m ⇒
                State k (Undef (UndefBranch (switch{□} s) Ω (VBase vb))) m

  (**i For compound statements: *)
  | rcstep_in_comp m k s1 s2 :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (s1 ;; s2)) m ⇒
                State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m
  | rcstep_out_comp1 m k s1 s2 :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (□ ;; s2) :: k) (Stmt ↗ s1) m ⇒
                State (CStmt (s1 ;; □) :: k) (Stmt ↘ s2) m
  | rcstep_out_comp2 m k s1 s2 :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (s1 ;; □) :: k) (Stmt ↗ s2) m ⇒
                State k (Stmt ↗ (s1 ;; s2)) m
  | rcstep_in_catch m k s :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (catch s)) m ⇒
                State (CStmt (catch □) :: k) (Stmt ↘ s) m
  | rcstep_out_catch m k s :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (catch □) :: k) (Stmt ↗ s) m ⇒
                State k (Stmt ↗ (catch s)) m
  | rcstep_in_loop m k s :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt ↘ (loop s)) m ⇒
                State (CStmt (loop □) :: k) (Stmt ↘ s) m
  | rcstep_out_loop m k s :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (loop □) :: k) (Stmt ↗ s) m ⇒
                State k (Stmt ↘ (loop s)) m
  | rcstep_out_if1 m k e s1 s2 :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (if{e} □ else s2) :: k) (Stmt ↗ s1) m ⇒
                State k (Stmt ↗ (if{e} s1 else s2)) m
  | rcstep_out_if2 m k e s1 s2 :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (if{e} s1 else □) :: k) (Stmt ↗ s2) m ⇒
                State k (Stmt ↗ (if{e} s1 else s2)) m
  | rcstep_out_switch m k e s :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (switch{e} □) :: k) (Stmt ↗ s) m ⇒
                State k (Stmt ↗ (switch{e} s)) m

  (**i For function calls *)
  | rcstep_call m k f s os vs :
     δ !! f = Some s → Forall_fresh (dom indexset m) os →
     length os = length vs →
     Γ\ δ\ ρ ⊢ₛ State k (Call f vs) m ⇒
                State (CParams f (zip os (type_of <$> vs)) :: k)
                  (Stmt ↘ s) (mem_alloc_list Γ os vs m)
  | rcstep_free_params m k f oτs s :
     Γ\ δ\ ρ ⊢ₛ State (CParams f oτs :: k) (Stmt ↗ s) m ⇒
                State k (Return f voidV) (foldr mem_free m (oτs.*1))
  | rcstep_free_params_top m k f oτs v s :
     Γ\ δ\ ρ ⊢ₛ State (CParams f oτs :: k) (Stmt (⇈ v) s) m ⇒
                State k (Return f v) (foldr mem_free m (oτs.*1))
  | rcstep_return m k f E v :
     Γ\ δ\ ρ ⊢ₛ State (CFun E :: k) (Return f v) m ⇒
                State k (Expr (subst E (#v)%E)) m

  (**i For non-local control flow: *)
  | rcstep_label_here m k l :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt (↷ l) (label l)) m ⇒
                State k (Stmt ↗ (label l)) m
  | rcstep_throw_here m k s :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (catch □) :: k) (Stmt (↑ 0) s) m ⇒
                State k (Stmt ↗ (catch s)) m
  | rcstep_throw_further m k s n :
     Γ\ δ\ ρ ⊢ₛ State (CStmt (catch □) :: k) (Stmt (↑ (S n)) s) m ⇒
                State k (Stmt (↑ n) (catch s)) m
  | cstep_case_here m k mx :
     Γ\ δ\ ρ ⊢ₛ State k (Stmt (↓ mx) (scase mx)) m ⇒
                State k (Stmt ↗ (scase mx)) m
  | rcstep_goto_in m k Es l s :
     l ∈ labels s →
     Γ\ δ\ ρ ⊢ₛ State k (Stmt (↷ l) (subst Es s)) m ⇒
                State (CStmt Es :: k) (Stmt (↷ l) s) m
  | rcstep_switch_in m k Es mx s :
     maybe CSwitch Es = None → mx ∈ cases s →
     Γ\ δ\ ρ ⊢ₛ State k (Stmt (↓ mx) (subst Es s)) m ⇒
                State (CStmt Es :: k) (Stmt (↓ mx) s) m
  | rcstep_top_out m k Es v s :
     Γ\ δ\ ρ ⊢ₛ State (CStmt Es :: k) (Stmt (⇈ v) s) m ⇒
                State k (Stmt (⇈ v) (subst Es s)) m
  | rcstep_goto_out m k Es l s :
     l ∉ labels s →
     Γ\ δ\ ρ ⊢ₛ State (CStmt Es :: k) (Stmt (↷ l) s) m ⇒
                State k (Stmt (↷ l) (subst Es s)) m
  | rcstep_throw_out m k Es n s :
     Es ≠ catch □ →
     Γ\ δ\ ρ ⊢ₛ State (CStmt Es :: k) (Stmt (↑ n) s) m ⇒
                State k (Stmt (↑ n) (subst Es s)) m

  (**i For block scopes: *)
  | rcstep_in_block m k d o τ s :
     direction_in d s → o ∉ dom indexset m →
     Γ\ δ\ ρ ⊢ₛ State k (Stmt d (local{τ} s)) m ⇒
                State (CLocal o τ :: k) (Stmt d s)
                  (mem_alloc Γ o false perm_full (val_new Γ τ) m)
  | rcstep_out_block m k d o τ s :
     direction_out d s →
     Γ\ δ\ ρ ⊢ₛ State (CLocal o τ :: k) (Stmt d s) m ⇒
                State k (Stmt d (local{τ} s)) (mem_free o m)
where "Γ \ δ \ ρ ⊢ₛ S1 ⇒ S2" := (@rcstep _ _ Γ δ ρ S1%S S2%S) : C_scope.

(** The reflexive transitive closure. *)
Notation "Γ \ δ \ ρ ⊢ₛ S1 ⇒* S2" := (rtc (rcstep Γ δ ρ) S1 S2)
  (at level 74, δ at next level, ρ at next level,
   format "Γ \  δ \  ρ  ⊢ₛ '['  S1  '⇒*' '/'  S2 ']'") : C_scope.
Notation "Γ \ δ \ ρ ⊢ₛ S1 ⇒^ n S2" := (bsteps (rcstep Γ δ ρ) n S1 S2)
  (at level 74, δ at next level, ρ at next level, n at level 1,
   format "Γ \  δ \  ρ  ⊢ₛ '['  S1  '⇒^' n '/'  S2 ']'") : C_scope.

(** * Inversions *)
(** Coq's [inversion] tactic is rather slow for large inductive types (as our
[cstep]). We therefore define some special purpose inversion schemes. The way
of defining these schemes is based on small inversions (Monin, 2010). *)
Section inversion.
  Context `{Env K} (Γ : env K) (δ : funenv K) (ρ : stack K).

  Lemma rcstep_focus_inv (P : state K → Prop) S1 S2 :
    Γ\ δ\ ρ ⊢ₛ S1 ⇒ S2 →
    let 'State k φ m := S1 in
    match φ with
    | Stmt ↘ skip => P (State k (Stmt ↗ skip) m) → P S2
    | Stmt ↘ (goto l) => P (State k (Stmt (↷ l) (goto l)) m) → P S2
    | Stmt ↘ (throw n) => P (State k (Stmt (↑ n) (throw n)) m) → P S2
    | Stmt ↘ (label l) => P (State k (Stmt ↗ (label l)) m) → P S2
    | Stmt ↘ (scase mx) => P (State k (Stmt ↗ (scase mx)) m) → P S2
    | Stmt ↘ (! e) => P (State (CExpr e (! □) :: k) (Expr e) m) → P S2
    | Stmt ↘ (ret e) => P (State (CExpr e (ret □) :: k) (Expr e) m) → P S2
    | Stmt ↘ (loop s) => P (State (CStmt (loop □) :: k) (Stmt ↘ s) m) → P S2
    | Stmt ↘ (if{e} s1 else s2) =>
       P (State (CExpr e (if{□} s1 else s2) :: k) (Expr e) m) → P S2
    | Stmt ↘ (switch{e} s) =>
       P (State (CExpr e (switch{□} s) :: k) (Expr e) m) → P S2
    | Expr e =>
       (∀ Ω v k' e',
         e = (#{Ω} v)%E → k = CExpr e' (! □) :: k' →
         P (State k' (Stmt ↗ (! e')) (mem_unlock Ω m))) →
       (∀ Ω v k' e',
         e = (#{Ω} v)%E → k = CExpr e' (ret □) :: k' →
         P (State k' (Stmt (⇈ v) (ret e')) (mem_unlock Ω m))) →
       (∀ Ω vb k' e' s1 s2,
         e = (#{Ω} VBase vb)%E → base_val_branchable m vb → ¬base_val_is_0 vb →
         k = CExpr e' (if{□} s1 else s2) :: k' →
         P (State (CStmt (if{e'} □ else s2) :: k')
           (Stmt ↘ s1) (mem_unlock Ω m))) →
       (∀ Ω vb k' e' s1 s2,
         e = (#{Ω} VBase vb)%E → base_val_branchable m vb → base_val_is_0 vb →
         k = CExpr e' (if{□} s1 else s2) :: k' →
         P (State (CStmt (if{e'} s1 else □) :: k')
           (Stmt ↘ s2) (mem_unlock Ω m))) →
       (∀ Ω vb k' e' s1 s2,
         e = (#{Ω} VBase vb)%E → ¬base_val_branchable m vb →
         k = CExpr e' (if{□} s1 else s2) :: k' →
         P (State k' (Undef (UndefBranch (if{□} s1 else s2) Ω (VBase vb))) m)) →
       (∀ Ω τi x k' e' s,
         e = (#{Ω} (intV{τi} x))%E → Some x ∈ cases s →
         k = CExpr e' (switch{□} s) :: k' →
         P (State (CStmt (switch{e'} □) :: k')
                  (Stmt (↓ (Some x)) s) (mem_unlock Ω m))) →
       (∀ Ω τi x k' e' s,
         e = (#{Ω} (intV{τi} x))%E → Some x ∉ cases s → None ∈ cases s →
         k = CExpr e' (switch{□} s) :: k' →
         P (State (CStmt (switch{e'} □) :: k')
                  (Stmt (↓ None) s) (mem_unlock Ω m))) →
       (∀ Ω τi x k' e' s,
         e = (#{Ω} (intV{τi} x))%E → Some x ∉ cases s → None ∉ cases s →
         k = CExpr e' (switch{□} s) :: k' →
         P (State k' (Stmt ↗ (switch{e'} s)) (mem_unlock Ω m))) →
       (∀ Ω vb k' e' s,
         e = (#{Ω} VBase vb)%E → ¬base_val_branchable m vb →
         k = CExpr e' (switch{□} s) :: k' →
         P (State k' (Undef (UndefBranch (switch{□} s) Ω (VBase vb))) m)) →
       (∀ (E : ectx K) e1 e2 m2,
         e = subst E e1 → Γ\ rlocals ρ k ⊢ₕ e1, m ⇒ e2, m2 →
         P (State k (Expr (subst E e2)) m2)) →
       (∀ (E : ectx K) Ω f τs τ Ωs vs,
         e = subst E (call %{Ω} FunPtr f τs τ @ #{Ωs}* vs)%E →
         length Ωs = length vs →
         P (State (CFun E :: k) (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m))) →
       (∀ (E : ectx K) e1,
         e = subst E e1 → is_redex e1 → ¬Γ\ rlocals ρ k ⊢ₕ safe e1, m →
         P (State k (Undef (UndefExpr E e1)) m)) →
       P S2
    | Return f v =>
       (∀ k' E,
         k = CFun E :: k' → P (State k' (Expr (subst E (#v)%E)) m)) →
       P S2
    | Stmt ↘ (local{τ} s) =>
       (∀ o,
         o ∉ dom indexset m →
         P (State (CLocal o τ :: k) (Stmt ↘ s)
           (mem_alloc Γ o false perm_full (val_new Γ τ) m))) →
       P S2
    | Stmt ↘ (s1 ;; s2) => P (State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m) → P S2
    | Stmt ↘ (catch s) =>
       P (State (CStmt (catch □) :: k) (Stmt ↘ s) m) → P S2
    | Stmt ↗ s =>
       (∀ k' o τ,
         k = CLocal o τ :: k' →
         P (State k' (Stmt ↗ (local{τ} s)) (mem_free o m))) →
       (∀ k' s2,
         k = CStmt (□ ;; s2) :: k' →
         P (State (CStmt (s ;; □) :: k') (Stmt ↘ s2) m)) →
       (∀ k' s1,
         k = CStmt (s1 ;; □) :: k' → P (State k' (Stmt ↗ (s1 ;; s)) m)) →
       (∀ k',
         k = CStmt (catch □) :: k' → P (State k' (Stmt ↗ (catch s)) m)) →
       (∀ k',
         k = CStmt (loop □) :: k' → P (State k' (Stmt ↘ (loop s)) m)) →
       (∀ k' e s2,
         k = CStmt (if{e} □ else s2) :: k' →
         P (State k' (Stmt ↗ (if{e} s else s2)) m)) →
       (∀ k' e s1,
         k = CStmt (if{e} s1 else □) :: k' →
         P (State k' (Stmt ↗ (if{e} s1 else s)) m)) →
       (∀ k' e,
         k = CStmt (switch{e} □) :: k' →
         P (State k' (Stmt ↗ (switch{e} s)) m)) →
       (∀ k' f oτs,
         k = CParams f oτs :: k' →
         P (State k' (Return f voidV) (foldr mem_free m (oτs.*1)))) →
       P S2
    | Call f vs =>
       (∀ s os,
         δ !! f = Some s → Forall_fresh (dom indexset m) os →
         length os = length vs →
         P (State (CParams f (zip os (type_of <$> vs)) :: k)
           (Stmt ↘ s) (mem_alloc_list Γ os vs m))) →
       P S2
    | Stmt (⇈ v) s =>
       (∀ k' f oτs,
         k = CParams f oτs :: k' →
         P (State k' (Return f v) (foldr mem_free m (oτs.*1)))) →
       (∀ k' o τ,
         k = CLocal o τ :: k' →
         P (State k' (Stmt (⇈ v) (local{τ} s)) (mem_free o m))) →
       (∀ k' Es,
         k = CStmt Es :: k' → P (State k' (Stmt (⇈ v) (subst Es s)) m)) →
       P S2
    | Stmt (↑ n) s =>
       (∀ k',
         k = CStmt (catch □) :: k' → n = 0 → 
         P (State k' (Stmt ↗ (catch s)) m)) →
       (∀ k' n',
         k = CStmt (catch □) :: k' → n = S n' →
         P (State k' (Stmt (↑ n') (catch s)) m)) →
       (∀ k' o τ,
         k = CLocal o τ :: k' →
         P (State k' (Stmt (↑ n) (local{τ} s)) (mem_free o m))) →
       (∀ k' Es,
         k = CStmt Es :: k' → Es ≠ catch □ →
         P (State k' (Stmt (↑ n) (subst Es s)) m)) →
       P S2
    | Stmt (↷ l) s =>
       (s = label l → P (State k (Stmt ↗ s) m)) →
       (∀ s' o τ,
         s = local{τ} s' → l ∈ labels s → o ∉ dom indexset m →
         P (State (CLocal o τ :: k) (Stmt (↷ l) s')
           (mem_alloc Γ o false perm_full (val_new Γ τ) m))) →
       (∀ k' o τ,
         k = CLocal o τ :: k' → l ∉ labels s →
         P (State k' (Stmt (↷ l) (local{τ} s)) (mem_free o m))) →
       (∀ s' Es,
         s = subst Es s' → l ∈ labels s' →
         P (State (CStmt Es :: k) (Stmt (↷ l) s') m)) →
       (∀ k' Es,
         k = CStmt Es :: k' → l ∉ labels s →
         P (State k' (Stmt (↷ l) (subst Es s)) m)) →
       P S2
    | Stmt (↓ mx) s =>
       (s = scase mx → P (State k (Stmt ↗ s) m)) →
       (∀ s' o τ,
         s = local{τ} s' → mx ∈ cases s → o ∉ dom indexset m →
         P (State (CLocal o τ :: k) (Stmt (↓ mx) s')
           (mem_alloc Γ o false perm_full (val_new Γ τ) m))) →
       (∀ s' Es,
         s = subst Es s' → maybe CSwitch Es = None → mx ∈ cases s' →
         P (State (CStmt Es :: k) (Stmt (↓ mx) s') m)) →
       P S2
    | Undef _ => P S2
    end.
  Proof.
    intros p; case p; simpl; eauto 2.
    * by intros ?? [] ?; simpl; eauto.
    * by intros ?? []; simpl; eauto.
    * by intros ?? []; simpl; eauto.
  Qed.
  Lemma rcstep_expr_inv (P : state K → Prop) m k Ek Ω v S2 :
    Γ\ δ\ ρ ⊢ₛ State (Ek :: k) (Expr (#{Ω} v)) m ⇒ S2 →
    match Ek with
    | CExpr e (! □) =>
       P (State k (Stmt ↗ (! e)) (mem_unlock Ω m)) → P S2
    | CExpr e (ret □) =>
       P (State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m)) → P S2
    | CExpr e (if{□} s1 else s2) =>
      (∀ vb,
        v = VBase vb → base_val_branchable m vb → ¬base_val_is_0 vb →
        P (State (CStmt (if{e} □ else s2) :: k) (Stmt ↘ s1) (mem_unlock Ω m))) →
      (∀ vb,
        v = VBase vb → base_val_branchable m vb → base_val_is_0 vb →
        P (State (CStmt (if{e} s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m))) →
      (∀ vb,
        v = VBase vb → ¬base_val_branchable m vb →
        P (State k (Undef (UndefBranch (if{□} s1 else s2) Ω v)) m)) → P S2
    | CExpr e (switch{□} s) =>
      (∀ τi x,
        v = intV{τi} x → Some x ∈ cases s →
        P (State (CStmt (switch{e} □) :: k)
                 (Stmt (↓ (Some x)) s) (mem_unlock Ω m))) →
      (∀ τi x,
        v = intV{τi} x → Some x ∉ cases s → None ∈ cases s →
        P (State (CStmt (switch{e} □) :: k)
                        (Stmt (↓ None) s) (mem_unlock Ω m))) →
      (∀ τi x,
        v = intV{τi} x → Some x ∉ cases s → None ∉ cases s →
        P (State k (Stmt ↗ (switch{e} s)) (mem_unlock Ω m))) →
      (∀ vb s,
        v = VBase vb → ¬base_val_branchable m vb →
        P (State k (Undef (UndefBranch (switch{□} s) Ω (VBase vb))) m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2.
    apply (rcstep_focus_inv _ _ _ p);
      try solve [intros; simplify_equality; eauto].
    * intros Ee e1 e2 m2 Hv p'. simplify_list_subst_equality Hv. inversion p'.
    * intros Ee Ω' f τs τ Ωs vs Hv. simplify_list_subst_equality Hv.
    * intros Ee e1 Hv ? _. simplify_list_subst_equality Hv.
      by destruct (EVal_not_redex Ω (inr v)).
  Qed.
  Lemma rcstep_stmt_up_inv (P : state K → Prop) m k Ek s S2 :
    Γ\ δ\ ρ ⊢ₛ State (Ek :: k) (Stmt ↗ s) m ⇒ S2 →
    match Ek with
    | CStmt (□ ;; s2) => P (State (CStmt (s ;; □) :: k) (Stmt ↘ s2) m) → P S2
    | CStmt (s1 ;; □) => P (State k (Stmt ↗ (s1 ;; s)) m) → P S2
    | CStmt (catch □) => P (State k (Stmt ↗ (catch s)) m) → P S2
    | CStmt (loop □) => P (State k (Stmt ↘ (loop s)) m) → P S2
    | CStmt (if{e} □ else s2) => P (State k (Stmt ↗ (if{e} s else s2)) m) → P S2
    | CStmt (if{e} s1 else □) => P (State k (Stmt ↗ (if{e} s1 else s)) m) → P S2
    | CStmt (switch{e} □) => P (State k (Stmt ↗ (switch{e} s)) m) → P S2
    | CLocal o τ => P (State k (Stmt ↗ (local{τ} s)) (mem_free o m)) → P S2
    | CParams f oτs =>
       P (State k (Return f voidV) (foldr mem_free m (oτs.*1))) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2. apply (rcstep_focus_inv _ _ _ p);
      intros; simplify_equality; eauto.
  Qed.
  Lemma rcstep_stmt_top_inv (P : state K → Prop) m k Ek v s S2 :
    Γ\ δ\ ρ ⊢ₛ State (Ek :: k) (Stmt (⇈ v) s) m ⇒ S2 →
    match Ek with
    | CStmt Es => P (State k (Stmt (⇈ v) (subst Es s)) m) → P S2
    | CParams f oτs =>
       P (State k (Return f v) (foldr mem_free m (oτs.*1))) → P S2
    | CLocal o τ => P (State k (Stmt (⇈ v) (local{τ} s)) (mem_free o m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2.
    apply (rcstep_focus_inv _ _ _ p); intros; simplify_equality; eauto.
  Qed.
End inversion.

(** The previously defined inversion schemes all work for reductions of
a different shape. We therefore define the tactic [fast_inv_rcstep] to
automatically pick the most suitable inversion scheme. It also performs the
necessary generalization of assumptions. *)
Ltac fast_inv_rcstep H :=
  match type of H with
  | _\ _\ _ ⊢ₛ ?S1 ⇒ ?S2 =>
    try match S1 with
    | State _ (Stmt ?d _) _ => is_var d; destruct d; try done
    end;
    is_var S2;
    block_goal;
    repeat match goal with
    | H' : context [ S2 ] |- _ => var_neq H H'; revert H'
    end;
    pattern S2; first
    [ apply (rcstep_expr_inv _ _ _ _ _ _ _ _ _ _ H)
    | apply (rcstep_stmt_up_inv _ _ _ _ _ _ _ _ _  H)
    | apply (rcstep_stmt_top_inv _ _ _ _ _ _ _ _ _ _ H)
    | apply (rcstep_focus_inv _ _ _ _ _ _ H)];
    clear H; intros; unblock_goal
  end.
(** Some reduction are not of a shape that fits any of the previously defined
inversion schemes. The tactic [slow_inv_rcstep] inverts a reduction using Coq's
standard [inversion] tactic and works for reductions of all shapes. *)
Ltac slow_inv_rcstep H :=
  match type of H with _\ _\ _ ⊢ₛ ?S1 ⇒ ?S2 => inversion H; clear H end.

(** The tactic [inv_rcstep] inverts a reduction step and performs some clean up
and discharges impossible cases afterwards. *)
Tactic Notation "inv_rcstep" hyp(H) :=
  match type of H with
  | _\ _\ _ ⊢ₛ ?S1 ⇒ ?S2 =>
    (**i perform the actual inversion, and print a message (for debugging) in
    case slow inversion has been used *)
    first
      [ fast_inv_rcstep H
      | idtac "slow inversion on" S1; slow_inv_rcstep H ];

    (**i clean up, and discharge impossible cases *)
    simplify_list_subst_equality;
    repeat match goal with
    | _ => done
    | H : suffix _ _ |- _ => progress (simpl in H; simplify_suffix)
    | H : _\ _ ⊢ₕ %#{_} _, _ ⇒ _, _ |- _ => by inversion H
    | H : is_redex (%#{_} _) |- _ => inversion H
    | H : direction_in ?d ?s, _ : direction_out ?d ?s |- _ =>
       by destruct (direction_in_out d s)
    | H : _ ∉ labels (subst _ _) |- _ => rewrite sctx_item_subst_labels in H
    | _ => first [by decompose_elem_of|decompose_elem_of; [idtac]]
    end
  end.
Tactic Notation "inv_rcstep" :=
  match goal with
  | H : _\ _\ _ ⊢ₛ _ ⇒ _ |- _ => inv_rcstep H
  end.

Tactic Notation "inv_rcsteps" hyp(H) "as" simple_intropattern(H2) :=
  (* use a fresh name so we do not clear the wrong hypothesis *)
  let H' := fresh in
  rename H into H';
  inversion H' as H2; clear H'; try subst.
Tactic Notation "inv_rcsteps" hyp(H) := inv_rcsteps H as [].

Tactic Notation "last_rcstep" hyp(H) :=
  let H' := fresh in
  inv_rcsteps H as [| ???? H' ?]; [| solve [inv_rcstep H']].

(** * Step tactics *)
Ltac do_rcstep :=
  let go := first
    [ econstructor; by (eauto with cstep)
    | by (eauto with cstep)] in
  match goal with
  | |- ?Γ\ ?δ\ ?ρ ⊢ₛ State ?k (Stmt ?d ?s) ?m ⇒ ?S =>
     iter (fun s' => change (Γ\ δ\ ρ ⊢ₛ State k (Stmt d s') m ⇒ S); go)
          (quote_stmt s)
  | |- ?Γ\ ?δ\ ?ρ ⊢ₛ State ?k (Expr ?e) ?m ⇒ ?S =>
     iter (fun e' => change (Γ\ δ\ ρ ⊢ₛ State k (Expr e') m ⇒ S); go)
          (quote_expr e)
  | _ => go
  end.

Ltac solve_rcred :=
  repeat match goal with
  | |- red (rcstep _ _ _) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; simplify_equality'; try contradiction
  | H : ?l ∈ _ |- red (rcstep _ _ _) (State _ (Stmt (↷ ?l) _) _) =>
    progress decompose_elem_of H
  | H : ?mx ∈ _ |- red (rcstep _ _ _) (State _ (Stmt (↓ ?mx) _) _) =>
    progress decompose_elem_of H
  end;
  match goal with
  | |- red (rcstep _ _ _) _ => eexists; do_rcstep
  | |- _ => by (eauto with cstep)
  end.

(** * Theorems *)
Section theorems.
Context `{Env K} (Γ : env K) (δ : funenv K).
Implicit Types k : ctx K.

Lemma rlocals_nil k : rlocals [] k = locals k.
Proof. by induction k as [|[]]; f_equal'. Qed.
Lemma rlocals_app k1 k2 ρ : rlocals ρ (k1 ++ k2) = rlocals (rlocals ρ k2) k1.
Proof. induction k1 as [|[]]; simpl; auto with f_equal. Qed.

Lemma cstep_rcstep S1 S2 : Γ\ δ ⊢ₛ S1 ⇒ S2 → Γ\ δ\ [] ⊢ₛ S1 ⇒ S2.
Proof. by destruct 1; constructor; rewrite ?rlocals_nil. Qed.
Lemma csteps_rcsteps S1 S2 : Γ\ δ ⊢ₛ S1 ⇒* S2 → Γ\ δ\ [] ⊢ₛ S1 ⇒* S2.
Proof. induction 1; econstructor; eauto using cstep_rcstep. Qed.
Lemma rcstep_cstep S1 S2 : Γ\ δ\ [] ⊢ₛ S1 ⇒ S2 → Γ\ δ ⊢ₛ S1 ⇒ S2.
Proof. by destruct 1; constructor; rewrite <-?rlocals_nil. Qed.

Lemma rcred_ectx (E : ectx K) ρ e m :
  red (rcstep Γ δ ρ) (State [] (Expr e) m) →
  red (rcstep Γ δ ρ) (State [] (Expr (subst E e)) m).
Proof. intros [S p]. inv_rcstep p; rewrite <-subst_app; solve_rcred. Qed.

Lemma rcstep_app ρ k k1 k2 φ1 φ2 m1 m2 :
  Γ\ δ\ rlocals ρ k ⊢ₛ State k1 φ1 m1 ⇒ State k2 φ2 m2 →
  Γ\ δ\ ρ ⊢ₛ State (k1 ++ k) φ1 m1 ⇒ State (k2 ++ k) φ2 m2.
Proof.
  cut (∀ S1 S2, Γ\ δ\ rlocals ρ k ⊢ₛ S1 ⇒ S2 →
    Γ\ δ\ ρ ⊢ₛ State (SCtx S1 ++ k) (SFoc S1) (SMem S1) ⇒
               State (SCtx S2 ++ k) (SFoc S2) (SMem S2)).
  { intros help; apply help. }
  destruct 1; repeat match goal with
    | H : context [rlocals _ _] |- _ => rewrite <-rlocals_app in H
    end; do_cstep.
Qed.
Lemma rcred_app ρ k1 k2 φ m :
  red (rcstep Γ δ (rlocals ρ k2)) (State k1 φ m) →
  red (rcstep Γ δ ρ) (State (k1 ++ k2) φ m).
Proof. intros [[???] ?]; eexists; eauto using rcstep_app. Qed.
Lemma rcstep_app_inv ρ k k1 k2 φ1 φ2 m1 m2 :
  Γ\ δ\ ρ ⊢ₛ State (k1 ++ k) φ1 m1 ⇒ State (k2 ++ k) φ2 m2 →
  Γ\ δ\ rlocals ρ k ⊢ₛ State k1 φ1 m1 ⇒ State k2 φ2 m2.
Proof.
  intros p; inv_rcstep p;
    repeat match goal with
    | H : context [rlocals _ _] |- _ => rewrite rlocals_app in H
    | H : _ :: _ ++ _ = _ ++ _ |- _ => rewrite app_comm_cons in H
    | H : _ ++ _ = _ ++ _ |- _ => apply (inj (.++ _)) in H; subst
    | H : _ :: _ = ?k ++ _ |- _ =>
       destruct k; simplify_equality'; try discriminate_list_equality
    end; do_rcstep.
Qed.
Lemma cstep_app_suffix_of ρ k1 k2 φ m S' :
  red (rcstep Γ δ (rlocals ρ k2)) (State k1 φ m) →
  Γ\ δ\ ρ ⊢ₛ State (k1 ++ k2) φ m ⇒ S' → suffix k2 (SCtx S').
Proof.
  cut (∀ S, red (rcstep Γ δ (rlocals ρ k2)) S →
    Γ\ δ\ ρ ⊢ₛ State (SCtx S ++ k2) (SFoc S) (SMem S) ⇒ S' →
    suffix k2 (SCtx S')); eauto.
  intros S [S'' p1] p2.
  destruct p1; simplify_equality'; inv_rcstep; try solve_suffix; set_solver.
Qed.

Lemma rcstep_expr_depsubst_inv {n} (P : state K → Prop)
    m ρ (E : ectx_full K n) (es : vec (expr K) n) S' :
  Γ\ δ\ ρ ⊢ₛ State [] (Expr (depsubst E es)) m ⇒ S' →
  (∀ i e' m',
    Γ\ δ\ ρ ⊢ₛ State [] (Expr (es !!! i)) m ⇒ State [] (Expr e') m' →
    P (State [] (Expr (depsubst E (vinsert i e' es))) m')) →
  (∀ i E' Ω f τs τ Ωs vs,
    length Ωs = length vs →
    es !!! i = subst E' (call %{Ω} FunPtr f τs τ @ #{Ωs}* vs)%E →
    Γ\ δ\ ρ ⊢ₛ State [] (Expr (es !!! i)) m ⇒
               State [CFun E'] (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m) →
    P (State [CFun (E' ++ [ectx_full_to_item E es i])]
      (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m))) →
  (Forall is_nf es → P S') →
  (∀ i E' e, es !!! i = subst E' e →
    Γ\ δ\ ρ ⊢ₛ State [] (Expr (es !!! i)) m ⇒
              State [] (Undef (UndefExpr E' e)) m →
    P (State [] (Undef (UndefExpr (E' ++ [ectx_full_to_item E es i]) e)) m)) →
  P S'.
Proof.
  intros p. pattern S'.
  apply (rcstep_focus_inv _ _ _ _ _ _ p); clear p; simpl; try done.
  * intros E' e1 e2 m2 HE p HP1 _ HP3 _.
    destruct E' as [|E'' E' _] using rev_ind; simplify_equality'.
    { eapply HP3, is_redex_ectx_full, ehstep_is_redex; eauto. }
    rewrite !subst_snoc in HE |- *.
    apply ectx_full_item_subst in HE. destruct HE as [i [HE1 ->]].
    rewrite <-ectx_full_to_item_correct_alt; apply HP1.
    rewrite <-HE1; do_cstep.
  * intros E' Ω' f τs τ Ωs vs HE Hvs _ HP2 HP3 _.
    destruct E' as [|E'' E' _] using rev_ind.
    { destruct E; simplify_equality'. apply HP3. clear HP2 HP3.
      inv_vec es; intros e es ??; simplify_equality'; repeat constructor.
      eapply EVals_nf_alt; eauto. }
    rewrite !subst_snoc in HE.
    apply ectx_full_item_subst in HE; destruct HE as [i [HE1 ->]].
    eapply HP2; eauto. rewrite <-?HE1; trivial. do_cstep.
  * intros E' e1 HE Hred Hsafe HP1 HP2 HP3 HP4.
    destruct E' as [|E'' E' _] using rev_ind; simplify_equality'.
    { eapply HP3, is_redex_ectx_full; eauto. }
    rewrite !subst_snoc in HE.
    apply ectx_full_item_subst in HE. destruct HE as [i [HE1 ->]].
    apply HP4; auto. rewrite <-HE1; do_cstep.
Qed.
Lemma rcstep_expr_call_inv (P : state K → Prop) ρ Ω f τs τ Ωs vs m S' :
  let e := (call %{Ω} FunPtr f τs τ @ #{Ωs}* vs)%E in
  Γ\ δ\ ρ ⊢ₛ State [] (Expr e) m ⇒ S' →
  length Ωs = length vs →
  P (State [CFun []] (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m)) → P S'.
Proof.
  simpl; intros p ?. pattern S'.
  apply (rcstep_focus_inv _ _ _ _ _ _ p); simpl; clear p; try done.
  * intros E e1 v2 m2 Hvs ? _.
    simplify_list_subst_equality Hvs; simplify_list_subst_equality; inv_ehstep.
  * intros E Ω' f' τs' τ' Ωs' vs' Hvs ? HP;
      simplify_list_subst_equality Hvs.
    + edestruct (zip_with_inj (λ Ω v, #{Ω} v)%E Ωs Ωs' vs vs');
        eauto with congruence.
    + simplify_list_subst_equality.
    + simplify_list_subst_equality.
  * intros E e1 Hvs Hred Hsafe _; simplify_list_subst_equality Hvs.
    + destruct Hsafe. by constructor.
    + simplify_list_subst_equality; inversion Hred.
    + simplify_list_subst_equality; inversion Hred.
Qed.
Lemma rcstep_ctx_irrel ρ l l' k1 φ1 m1 k2 φ2 m2 :
  Γ\ δ\ ρ ⊢ₛ State (k1 ++ l) φ1 m1 ⇒ State (k2 ++ l) φ2 m2 →
  rlocals ρ l = rlocals ρ l' →
  Γ\ δ\ ρ ⊢ₛ State (k1 ++ l') φ1 m1 ⇒ State (k2 ++ l') φ2 m2.
Proof.
  intros p Hloc. inv_rcstep p;
    rewrite ?app_comm_cons in *; simplify_list_eq;
    repeat match goal with
    | H : context [rlocals _ (_ ++ _)] |- _ =>
       rewrite rlocals_app, Hloc, <-rlocals_app in H
    | _ => do_rcstep
    | H : _ :: _ = ?k ++ _ |- _ =>
       destruct k; simplify_list_eq; try discriminate_list_equality
    end.
Qed.
Lemma rcstep_call_inv (P : state K → Prop) E E' ρ k1 φ1 m1 S' :
  Γ\ δ\ ρ ⊢ₛ State (k1 ++ [CFun E]) φ1 m1 ⇒ S' →
  (∀ k2 φ2 m2,
     Γ\ δ\ ρ ⊢ₛ State (k1 ++ [CFun E']) φ1 m1 ⇒
                State (k2 ++ [CFun E']) φ2 m2 →
     P (State (k2 ++ [CFun E]) φ2 m2)) →
  (∀ f v,
     k1 = [] → φ1 = Return f v →
     Γ\ δ\ ρ ⊢ₛ State [CFun E'] (Return f v) m1 ⇒
                State [] (Expr (subst E' (# v)%E)) m1 →
     P (State [] (Expr (subst E (# v)%E)) m1)) →
  P S'.
Proof.
  intros p HP1 HP2. destruct S' as [k2 φ2 m2].
  destruct (decide ([CFun E] `suffix_of` k2)) as [[k2' ->]|?].
  * by apply HP1, rcstep_ctx_irrel with [CFun E].
  * inv_rcstep p; destruct k1; try solve_suffix; simplify_list_eq.
    eapply HP2; trivial. do_cstep.
Qed.

(** ** Cutting reduction paths *)
(** Given a reduction path, we can cut off the maximal prefix that is restricted
by a more restrictive program context. *)
(*
Lemma cstep_subctx_step_or_nf k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒ S2 → k `suffix` SCtx S1 →
  k `suffix` SCtx S2 ∨ nf (cstep_in_ctx Γ δ k) S1.
Proof.
  intros p1 ?. destruct (decide (k `suffix` SCtx S2)) as [|Hk]; [by left|].
  right; intros [S2' [p2 ?]]; destruct Hk.
  destruct p1; simpl in *; try solve_suffix_of; inv_cstep p2; set_solver.
Qed.
Lemma cred_preserves_subctx k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒ S2 → red (cstep_in_ctx Γ δ k) S1 →
  k `suffix` SCtx S1 → k `suffix` SCtx S2.
Proof. intros. by destruct (cstep_subctx_step_or_nf k S1 S2). Qed.
Lemma cstep_subctx_nf k S1 S2 :
  nf (cstep_in_ctx Γ δ k) S1 →
  Γ\ δ ⊢ₛ S1 ⇒ S2 → k `suffix` SCtx S1 → SCtx S1 = k.
Proof.
  intros Hnf p ?. destruct (decide (suffix k (SCtx S2))).
  * destruct Hnf. exists S2. by split.
  * destruct p; simpl in *; destruct k; solve_suffix_of.
Qed.
Lemma cstep_subctx_cut l k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒{k} S2 → l ++ k `suffix` SCtx S1 →
  Γ\ δ ⊢ₛ S1 ⇒{l ++ k} S2 ∨ SCtx S1 = l ++ k ∧ nf (cstep_in_ctx Γ δ (l ++ k)) S1.
Proof.
  intros [p ?] ?. destruct (cstep_subctx_step_or_nf (l ++ k) S1 S2); trivial.
  * left. do_cstep.
  * right. split. by apply cstep_subctx_nf with S2. done.
Qed.
Lemma cstep_bsteps_subctx_cut n l k S1 S3 :
  Γ\ δ ⊢ₛ S1 ⇒{k}^n S3 → l ++ k `suffix` SCtx S1 →
  (**i 1.) *) Γ\ δ ⊢ₛ S1 ⇒{l ++ k}^n S3 ∨
  (**i 2.) *) ∃ S2,
    Γ\ δ ⊢ₛ S1 ⇒{l ++ k}^n S2 ∧ SCtx S2 = l ++ k ∧
    nf (cstep_in_ctx Γ δ (l ++ k)) S2 ∧ Γ\ δ ⊢ₛ S2 ⇒{k}^n S3.
Proof.
  intros p ?. induction p as [n S1|n S1 S2 S3 p1 p2 IH]; [auto with ars|].
  destruct (cstep_subctx_cut l _ _ _ p1) as [[??]|[??]]; trivial.
  * destruct IH as [?|[S2' ?]]; trivial; [left; do_csteps|].
    right. exists S2'. intuition trivial; do_csteps.
  * right. exists S1. intuition eauto with ars.
Qed.
Lemma cstep_bsteps_subctx_cut_alt n l k φ1 m1 S3 :
  Γ\ δ\ ρ ⊢ₛ State l φ1 m1 ⇒^n S3 →
  (**i 1.) *) Γ\ δ\ rlocals ρ l ⊢ₛ State [] φ1 m1 ⇒^n S3 ∨
  (**i 2.) *) ∃ φ2 m2,
    Γ\ δ ⊢ₛ State (l ++ k) φ1 m1 ⇒{l ++ k}^n State (l ++ k) φ2 m2 ∧
    nf (cstep_in_ctx Γ δ (l ++ k)) (State (l ++ k) φ2 m2) ∧
    Γ\ δ ⊢ₛ State (l ++ k) φ2 m2 ⇒{k}^n S3.
Proof.
  intros p. destruct (cstep_bsteps_subctx_cut _ l _ _ _ p)
    as [?|([]&?&?&?)]; naive_solver.
Qed.

(** ** Preservation of statements *)
(** We prove that small step reduction behaves as traversing through a zipper.
That is, if [Γ\ δ ⊢ₛ State k (Stmt d1 s1) m1 ⇒{k}* State k (Stmt d2 s2) m2],
then [s1 = s2]. This proven on the length of the reduction path. When a
transition to the expression state occurs, we cut of the prefix corresponding
to execution of that expression. *)
Instance ctx_item_subst {K} :
    Subst (ctx_item K) (stmt K) (stmt K) := λ Ek s,
  match Ek with
  | CStmt E => subst E s | CLocal _ τ => local{τ} s
  | _ => s (* dummy *)
  end.
Definition is_CStmt_or_CLocal (Ek : ctx_item K) : Prop :=
  match Ek with CStmt _ | CLocal _ _ => True | _ => False end.
Definition in_fun_ctx (k1 k2 : ctx K) : Prop := ∃ l,
  Forall is_CStmt_or_CLocal l ∧ k2 = l ++ k1.

Instance: ∀ Ek : ctx_item K, Inj (=) (=) (subst Ek).
Proof.
  destruct Ek; intros ???; auto.
  * eapply (inj (subst (CStmt _))); eauto.
  * eapply (inj (SLocal _)); eauto.
Qed.
Instance: Reflexive in_fun_ctx.
Proof. intros k. eexists []. intuition trivial. Qed.
Lemma in_fun_ctx_r k1 k2 Ek :
  is_CStmt_or_CLocal Ek → in_fun_ctx k1 k2 → in_fun_ctx k1 (Ek :: k2).
Proof. intros ? [l [??]]. subst. exists (Ek :: l). intuition. Qed.
Lemma in_fun_ctx_app_r k1 k2 k :
  Forall is_CStmt_or_CLocal k → in_fun_ctx k1 k2 → in_fun_ctx k1 (k ++ k2).
Proof. induction 1; simpl; auto using in_fun_ctx_r. Qed.
Lemma in_fun_ctx_r_inv k1 k2 Ek :
  is_CStmt_or_CLocal Ek →
  k1 `suffix` k2 → in_fun_ctx k1 (Ek :: k2) → in_fun_ctx k1 k2.
Proof.
  intros ? [l1 ->] [l2 [Hc1 Hc2]].
  rewrite app_comm_cons in Hc2; apply app_inv_tail in Hc2; decompose_Forall_hyps.
  by exists l1.
Qed.
Lemma in_fun_ctx_change k1 k2 Ek1 Ek2 :
  is_CStmt_or_CLocal Ek2 → k1 `suffix` Ek2 :: k2 →
  in_fun_ctx k1 (Ek1 :: k2) → in_fun_ctx k1 (Ek2 :: k2).
Proof.
  intros ? [[|Ek2' l1] ?] [l2 [Hc1 Hc2]]; [by eexists []|].
  destruct l2 as [|? l2]; list_simplifier; [discriminate_list_equality|].
  exists (Ek2' :: l1); auto.
Qed.
Lemma in_fun_ctx_not_item_or_block k1 k2 Ek :
  ¬is_CStmt_or_CLocal Ek → k1 `suffix` k2 → ¬in_fun_ctx k1 (Ek :: k2).
Proof.
  intros ? [l1 ->] [l2 [Hc1 Hc2]]. by rewrite app_comm_cons in Hc2;
    apply app_inv_tail in Hc2; decompose_Forall_hyps.
Qed.
Lemma cstep_bsteps_preserves_stmt_help n k1 d1 s1 m1 k2 d2 s2 m2 :
  Γ\ δ ⊢ₛ State k1 (Stmt d1 s1) m1 ⇒{k2}^n State k2 (Stmt d2 s2) m2 →
  in_fun_ctx k2 k1 → subst k1 s1 = subst k2 s2.
Proof.
  revert k1 s1 d1 m1. induction n as [n1 IH] using lt_wf_ind.
  intros k1 s1 d1 m1 p1 Hin_fun. inv_csteps p1 as [|n2 ? S' ? p2h p2]; [done|].
  inv_cstep p2h;
   try apply (IH _ (lt_n_Sn n2) _ _ _ _ p2);
   try first
    [ done
    | by apply in_fun_ctx_r; eauto
    | by eapply in_fun_ctx_r_inv; eauto
    | by eapply in_fun_ctx_change; eauto
    | edestruct in_fun_ctx_not_item_or_block; eauto; inversion 1 ].
  destruct Hin_fun as [l [? ->]]. rewrite app_comm_cons in p2.
  destruct (cstep_bsteps_subctx_cut_alt _ _ _ _ _ _ p2)
    as [p|(?&?&_&?&p3)]; clear p2.
  * destruct (cstep_in_ctx_bsteps _ _ _ _ p)
      as [[??]|?]; by simplify_list_eq; discriminate_list_equality.
  * inv_csteps p3 as [| n4 ??? p4h p4]; [discriminate_list_equality|].
    inv_cstep p4h; try solve_cnf; first
    [ apply (IH _ (Nat_lt_succ_succ n4) _ _ _ _ p4);
       by repeat first
        [ apply in_fun_ctx_app_r
        | apply in_fun_ctx_r; [constructor|]]
    | by inv_csteps p4 as [| ???? p5h p5]; inv_cstep p5h ].
Qed.
Lemma cstep_bsteps_preserves_stmt n k d1 s1 m1 d2 s2 m2 :
  Γ\ δ ⊢ₛ State k (Stmt d1 s1) m1 ⇒{k}^n State k (Stmt d2 s2) m2 → s1 = s2.
Proof.
  intros p. apply (inj (subst k)).
  by eapply cstep_bsteps_preserves_stmt_help; eauto.
Qed.
*)
End theorems.
