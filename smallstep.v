(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** The small step reduction is a binary relation between execution states,
and computation is defined as the reflexive transitive closure of this
reduction relation. This file also defines tactics to automatically perform and
invert reduction steps. These tactics use the hint database [cstep] to solve
side-conditions. *)
Require Export state.

(** * Head reduction for expressions *)
(** We define head reduction for all redexes whose reduction is local (i.e.
does not change the current program context). Only function calls are non-local,
as they change to the call state, and store the current expression evaluation
context on the program context. These will be included in the whole reduction
relation [cstep].*)
(* The level is just below logical negation (whose level is 75). *)
Reserved Notation "ρ ⊢ₕ e1 , m1 ⇒ e2 , m2"
  (at level 74, format "ρ  '⊢ₕ' '['  e1 ,  m1  ⇒ '/'  e2 ,  m2 ']'").
Inductive ehstep (ρ : stack) : expr → mem → expr → mem → Prop :=
  | estep_var x a m :
     ρ !! x = Some a →
     ρ ⊢ₕ var x, m ⇒ ptrc a, m
  | estep_assign Ωl Ωr b v m :
     is_writable m b →
     ρ ⊢ₕ ptrc@{Ωl} b ::= valc@{Ωr} v, m ⇒
          valc@{ {[b]} ∪ Ωl ∪ Ωr} v, mem_lock b (<[b:=v]>m)
  | estep_load Ω a v m :
     m !! a = Some v →
     ρ ⊢ₕ load (ptrc@{Ω} a), m ⇒ valc@{Ω} v, m
  | estep_alloc a m :
     is_free m a →
     ρ ⊢ₕ alloc, m ⇒ ptrc a, mem_alloc a voidc%V Freeable m
  | estep_free Ω b m :
     is_freeable m b →
     ρ ⊢ₕ free (ptrc@{Ω} b), m ⇒ voidc@{Ω}, delete b m
  | estep_unop op Ω v v' m :
     eval_unop op v = Some v' →
     ρ ⊢ₕ ⊙{op} valc@{Ω} v, m ⇒ valc@{Ω} v', m
  | estep_binop op Ωl Ωr vl vr v' m :
     eval_binop op vl vr = Some v' →
     ρ ⊢ₕ valc@{Ωl} vl ⊙{op} valc@{Ωr} vr, m ⇒ valc@{Ωl ∪ Ωr} v', m
  | estep_if1 Ω v el er m :
     val_true v →
     ρ ⊢ₕ IF valc@{Ω} v then el else er, m ⇒ el, mem_unlock Ω m
  | estep_if2 Ω v el er m :
     val_false v →
     ρ ⊢ₕ IF valc@{Ω} v then el else er, m ⇒ er, mem_unlock Ω m
  | estep_cast τ Ω v v' m :
     eval_cast τ v = Some v' →
     ρ ⊢ₕ cast@{τ} (valc@{Ω} v), m ⇒ valc@{Ω} v', m
where "ρ  ⊢ₕ e1 , m1 '⇒' e2 , m2" :=
  (ehstep ρ e1%E m1 e2%E m2) : C_scope.

Lemma ehstep_pure_pure fs ρ e1 m1 e2 m2 :
  ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  is_pure fs e1 →
  is_pure fs e2.
Proof.
  intros p He1. pose proof (is_pure_locks _ _ He1) as HΩ.
  destruct p; inversion He1; simpl in *; rewrite ?HΩ;
    try constructor; auto.
Qed.
Lemma ehstep_pure_mem fs ρ e1 m1 e2 m2 :
  ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  is_pure fs e1 →
  m1 = m2.
Proof.
  by destruct 1; inversion 1;
    try match goal with
    | H : is_pure _ (valc@{_} _) |- _ =>
      apply is_pure_locks in H; simpl in H;
      rewrite H, mem_unlock_empty_locks
    end.
Qed.
Lemma ehstep_pure_locks fs ρ e1 m1 e2 m2 :
  ρ ⊢ₕ e1, m1 ⇒ e2, m2 →
  is_pure fs e1 →
  locks e1 = locks e2.
Proof.
  destruct 1; inversion 1; simpl;
    repeat match goal with
    | H : is_pure _ _ |- _ =>
      apply is_pure_locks in H; simpl in H; rewrite H
    end; solve_elem_of.
Qed.
Lemma ehstep_is_redex ρ e1 m1 v2 m2 :
  ρ ⊢ₕ e1, m1 ⇒ v2, m2 →
  is_redex e1.
Proof. destruct 1; repeat constructor. Qed.

Lemma estep_if1_no_locks ρ v el er m :
  val_true v →
  ρ ⊢ₕ IF valc v then el else er, m ⇒ el, m.
Proof. rewrite <-(mem_unlock_empty_locks m) at 2. by constructor. Qed.
Lemma estep_if2_no_locks ρ v el er m :
  val_false v →
  ρ ⊢ₕ IF valc v then el else er, m ⇒ er, m.
Proof. rewrite <-(mem_unlock_empty_locks m) at 2. by constructor. Qed.

(** An expression is safe if a head reduction step is possible. This relation
is adapted from CompCert and is used to capture undefined behavior. If the
whole expression contains a redex that is not safe, the semantics transitions
to the [Undef] state. *)
Reserved Notation "ρ  '⊢ₕ' 'safe' e , m" (at level 74, Ω at next level).
Inductive ehsafe (ρ : stack) : expr → mem → Prop :=
  | ehsafe_call f es m :
     ρ ⊢ₕ safe call f @ es, m
  | ehsafe_step e1 m1 v2 m2 :
     ρ ⊢ₕ e1, m1 ⇒ v2, m2 →
     ρ ⊢ₕ safe e1, m1
where "ρ  ⊢ₕ 'safe' e ,  m" := (ehsafe ρ e m) : C_scope.

Lemma ehstep_val ρ Ω v1 m1 v2 m2 :
  ¬ρ ⊢ₕ valc@{Ω} v1, m1 ⇒ v2, m2.
Proof. intros p. eapply is_redex_val, ehstep_is_redex, p. Qed.

(** The tactic [inv_ehstep] is used to invert an arbitrary expression head
reduction step, and [do_ehstep] is used to perform a step. *)
Ltac inv_ehstep :=
  match goal with
  | H : _ ⊢ₕ _, _ ⇒ _, _ |- _ => inversion H; subst; clear H
  end.
Ltac do_ehstep :=
  match goal with
  | |- _ ⊢ₕ _, _ ⇒ _, _ => constructor (solve [eauto with cstep])
  | |- _ ⊢ₕ _, _ ⇒ _, _ => solve [eauto with cstep]
  end.

Hint Constructors ehstep : cstep.
Hint Constructors ehsafe : cstep.
Hint Resolve estep_if1_no_locks estep_if2_no_locks : cstep.
Hint Extern 100 (_ !! _ = _) => progress simpl_mem : cstep.
Hint Extern 100 (is_writable (_ ∪ _) _) => apply is_writable_union_l : cstep.
Hint Extern 100 (is_writable (_ ∪ _) _) => apply is_writable_union_r : cstep.
Hint Extern 100 (is_writable {[ _ ]} _) => apply is_writable_singleton : cstep.
Hint Extern 100 (is_freeable (_ ∪ _) _) => apply is_freeable_union_l : cstep.
Hint Extern 100 (is_freeable (_ ∪ _) _) => apply is_freeable_union_r : cstep.
Hint Extern 100 (is_freeable {[ _ ]} _) => apply is_freeable_singleton : cstep.

(** * The reduction relation *)
(** Small step reduction works by traversal of the focus. Each step the focus
is executed, after which a transition to the next program state is performed. *)
Reserved Notation "δ ⊢ₛ S1 ⇒ S2"
  (at level 74, format "δ  ⊢ₛ '[' S1  ⇒ '/'  S2 ']'").
Inductive cstep (δ : funenv) : relation state :=
  (**i For simple statements: *)
  | cstep_in_skip k m :
     δ ⊢ₛ State k (Stmt ↘ skip) m ⇒
          State k (Stmt ↗ skip) m
  | cstep_in_goto l k m :
     δ ⊢ₛ State k (Stmt ↘ (goto l)) m ⇒
          State k (Stmt (↷ l) (goto l)) m
  | cstep_in_expr k E e m :
     δ ⊢ₛ State k (Stmt ↘ (subst E e)) m ⇒
          State (CExpr e E :: k) (Expr e) m

  (**i For expressions: *)
  | cstep_expr_head k (E : ectx) e1 e2 m1 m2 :
     get_stack k ⊢ₕ e1, m1 ⇒ e2, m2 →
     δ ⊢ₛ State k (Expr (subst E e1)) m1 ⇒
          State k (Expr (subst E e2)) m2
  | cstep_expr_call k f E Ωs vs m :
     same_length Ωs vs →
     δ ⊢ₛ State k (Expr (subst E (call f @ zip_with EVal Ωs vs))%E) m ⇒
          State (CFun E :: k) (Call f vs) (mem_unlock (⋃ Ωs) m)
  | cstep_expr_undef k (E : ectx) e m :
     is_redex e →
     ¬get_stack k ⊢ₕ safe e, m →
     δ ⊢ₛ State k (Expr (subst E e)) m ⇒
          State k Undef m

  (**i For finished expressions: *)
  | cstep_expr_do k Ω v e m :
     δ ⊢ₛ State (CExpr e (do □) :: k) (Expr (valc@{Ω} v)) m ⇒
          State k (Stmt ↗ (do e)) (mem_unlock Ω m)
  | cstep_expr_ret k e Ω v m :
     δ ⊢ₛ State (CExpr e (ret □) :: k) (Expr (valc@{Ω} v)) m ⇒
          State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m)
  | cstep_expr_while1 k e s Ω v m :
     val_true v →
     δ ⊢ₛ State (CExpr e (while (□) s) :: k) (Expr (valc@{Ω} v)) m ⇒
          State (CStmt (while (e) □) :: k) (Stmt ↘ s) (mem_unlock Ω m)
  | cstep_expr_while2 k e s Ω v m :
     val_false v →
     δ ⊢ₛ State (CExpr e (while (□) s) :: k) (Expr (valc@{Ω} v)) m ⇒
          State k (Stmt ↗ (while (e) s)) (mem_unlock Ω m)
  | cstep_expr_if1 k e s1 s2 Ω v m :
     val_true v →
     δ ⊢ₛ State (CExpr e (IF □ then s1 else s2) :: k) (Expr (valc@{Ω} v)) m ⇒
          State (CStmt (IF e then □ else s2) :: k) (Stmt ↘ s1) (mem_unlock Ω m)
  | cstep_expr_if2 k e s1 s2 Ω v m :
     val_false v →
     δ ⊢ₛ State (CExpr e (IF □ then s1 else s2) :: k) (Expr (valc@{Ω} v)) m ⇒
          State (CStmt (IF e then s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m)

  (**i For compound statements: *)
  | cstep_in_block k b s m :
     is_free m b →
     δ ⊢ₛ State k (Stmt ↘ (blk s)) m ⇒
          State (CBlock b :: k) (Stmt ↘ s)
            (mem_alloc b voidc%V Writable m)
  | cstep_in_comp k s1 s2 m :
     δ ⊢ₛ State k (Stmt ↘ (s1 ;; s2)) m ⇒
          State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m
  | cstep_in_label k l s m :
     δ ⊢ₛ State k (Stmt ↘ (l :; s)) m ⇒
          State (CStmt (l :; □) :: k) (Stmt ↘ s) m

  | cstep_out_block k b s m :
     δ ⊢ₛ State (CBlock b :: k) (Stmt ↗ s) m ⇒
          State k (Stmt ↗ (blk s)) (delete b m)
  | cstep_out_comp1 k s1 s2 m :
     δ ⊢ₛ State (CStmt (□ ;; s2) :: k) (Stmt ↗ s1) m ⇒
          State (CStmt (s1 ;; □) :: k) (Stmt ↘ s2) m
  | cstep_out_comp2 k s1 s2 m :
     δ ⊢ₛ State (CStmt (s1 ;; □) :: k) (Stmt ↗ s2) m ⇒
          State k (Stmt ↗ (s1 ;; s2)) m
  | cstep_out_loop k e s m :
     δ ⊢ₛ State (CStmt (while (e) □) :: k) (Stmt ↗ s) m ⇒
          State k (Stmt ↘ (while (e) s)) m
  | cstep_out_if1 k e s1 s2 m :
     δ ⊢ₛ State (CStmt (IF e then □ else s2) :: k) (Stmt ↗ s1) m ⇒
          State k (Stmt ↗ (IF e then s1 else s2)) m
  | cstep_out_if2 k e s1 s2 m :
     δ ⊢ₛ State (CStmt (IF e then s1 else □) :: k) (Stmt ↗ s2) m ⇒
          State k (Stmt ↗ (IF e then s1 else s2)) m
  | cstep_out_label k s l m :
     δ ⊢ₛ State (CStmt (l :; □) :: k) (Stmt ↗ s) m ⇒
          State k (Stmt ↗ (l :; s)) m

  (**i For function calls *)
  | cstep_call k f s m1 bs vs m2 :
     δ !! f = Some s →
     alloc_params Writable m1 bs vs m2 →
     δ ⊢ₛ State k (Call f vs) m1 ⇒
          State (CParams bs :: k) (Stmt ↘ s) m2
  | cstep_free_params k s m bs :
     δ ⊢ₛ State (CParams bs :: k) (Stmt ↗ s) m ⇒
          State k (Return voidc) (delete_list bs m)
  | cstep_free_params_top k v s m bs :
     δ ⊢ₛ State (CParams bs :: k) (Stmt (⇈ v) s) m ⇒
          State k (Return v) (delete_list bs m)
  | cstep_return k E v m :
     δ ⊢ₛ State (CFun E :: k) (Return v) m ⇒
          State k (Expr (subst E (valc v)%E)) m

  (**i For non-local control flow: *)
  | cstep_top_block v k b s m :
     δ ⊢ₛ State (CBlock b :: k) (Stmt (⇈ v) s) m ⇒
          State k (Stmt (⇈ v) (blk s)) (delete b m)
  | cstep_top_item v E k s m :
     δ ⊢ₛ State (CStmt E :: k) (Stmt (⇈ v) s) m ⇒
          State k (Stmt (⇈ v) (subst E s)) m
  | cstep_label_here l k s m :
     δ ⊢ₛ State k (Stmt (↷ l) (l :; s)) m ⇒
          State (CStmt (l :; □) :: k) (Stmt ↘ s) m
  | cstep_label_block_down l k b s m :
     l ∈ labels s →
     is_free m b →
     δ ⊢ₛ State k (Stmt (↷ l) (blk s)) m ⇒
          State (CBlock b :: k) (Stmt (↷ l) s)
            (mem_alloc b voidc Writable m)
  | cstep_label_block_up l k b s m : 
     (**i Not [l ∈ labels k] so as to avoid it going back and forth between 
     double occurrences of labels. *)
     l ∉ labels s →
     δ ⊢ₛ State (CBlock b :: k) (Stmt (↷ l) s) m ⇒
          State k (Stmt (↷l) (blk s)) (delete b m)
  | cstep_label_down l E k s m :
     l ∈ labels s →
     δ ⊢ₛ State k (Stmt (↷ l) (subst E s)) m ⇒
          State (CStmt E :: k) (Stmt (↷ l) s) m
  | cstep_label_up l E k s m :
     l ∉ labels s →
     δ ⊢ₛ State (CStmt E :: k) (Stmt (↷ l) s) m ⇒
          State k (Stmt (↷ l) (subst E s)) m
where "δ  ⊢ₛ S1 ⇒ S2" := (cstep δ S1%S S2%S) : C_scope.

(** The reflexive transitive closure. *)
Notation "δ ⊢ₛ S1 ⇒* S2" := (rtc (cstep δ) S1 S2)
  (at level 74, format "δ  ⊢ₛ '['  S1  '⇒*' '/'  S2 ']'") : C_scope.

(** Reduction paths of bounded length. *)
Notation "δ ⊢ₛ S1 ⇒^ n S2" := (bsteps (cstep δ) n S1 S2)
  (at level 74, n at level 1,
   format "δ  ⊢ₛ '['  S1  '⇒^' n '/'  S2 ']'") : C_scope.

(** Coq's [inversion] tactic is rather slow for large inductive types (as our
[cstep]). We therefore define some special purpose inversion schemes. The way
of defining these schemes is based on small inversions (Monin, 2010). *)
Section inversion.
  Context (δ : funenv).

  Lemma cstep_focus_inv (P : state → Prop) S1 S2 :
    δ ⊢ₛ S1 ⇒ S2 →
    let (k, φ, m) := S1 in
    match φ with
    | Stmt ↘ skip =>
       P (State k (Stmt ↗ skip) m) → P S2
    | Stmt ↘ (goto l) =>
       P (State k (Stmt (↷ l) (goto l)) m) → P S2
    | Stmt ↘ (do e) =>
       P (State (CExpr e (do □) :: k) (Expr e) m) → P S2
    | Stmt ↘ (ret e) =>
       P (State (CExpr e (ret □) :: k) (Expr e) m) → P S2
    | Stmt ↘ (while (e) s) => 
       P (State (CExpr e (while (□) s) :: k) (Expr e) m) → P S2
    | Stmt ↘ (IF e then s1 else s2) =>
       P (State (CExpr e (IF □ then s1 else s2) :: k) (Expr e) m) → P S2
    | Expr e =>
       (∀ Ω v k' e',
         e = (valc@{Ω} v)%E →
         k = CExpr e' (do □) :: k' →
         P (State k' (Stmt ↗ (do e')) (mem_unlock Ω m))) →
       (∀ Ω v k' e',
         e = (valc@{Ω} v)%E →
         k = CExpr e' (ret □) :: k' →
         P (State k' (Stmt (⇈ v) (ret e')) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s,
         e = (valc@{Ω} v)%E →
         val_true v →
         k = CExpr e' (while (□) s) :: k' →
         P (State (CStmt (while (e') □) :: k')
           (Stmt ↘ s) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s,
         e = (valc@{Ω} v)%E →
         val_false v →
         k = CExpr e' (while (□) s) :: k' →
         P (State k' (Stmt ↗ (while (e') s)) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s1 s2,
         e = (valc@{Ω} v)%E →
         val_true v →
         k = CExpr e' (IF □ then s1 else s2) :: k' →
         P (State (CStmt (IF e' then □ else s2) :: k')
           (Stmt ↘ s1) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s1 s2,
         e = (valc@{Ω} v)%E →
         val_false v →
         k = CExpr e' (IF □ then s1 else s2) :: k' →
         P (State (CStmt (IF e' then s1 else □) :: k')
           (Stmt ↘ s2) (mem_unlock Ω m))) →
       (∀ (E : ectx) e1 e2 m2,
         e = subst E e1 →
         get_stack k ⊢ₕ e1, m ⇒ e2, m2 →
         P (State k (Expr (subst E e2)) m2)) →
       (∀ (E : ectx) f Ωs vs,
         e = subst E (call f @ zip_with EVal Ωs vs)%E →
         same_length Ωs vs →
         P (State (CFun E :: k)
           (Call f vs) (mem_unlock (⋃ Ωs) m))) →
       (∀ (E : ectx) e1,
         e = subst E e1 →
         is_redex e1 →
         ¬get_stack k ⊢ₕ safe e1, m →
         P (State k Undef m)) →
       P S2
    | Return v =>
       (∀ k' E,
         k = CFun E :: k' →
         P (State k' (Expr (subst E (valc v)%E)) m)) →
       P S2
    | Stmt ↘ (blk s) =>
       (∀ b,
         is_free m b →
         P (State (CBlock b :: k) (Stmt ↘ s)
           (mem_alloc b voidc Writable m))) →
       P S2
    | Stmt ↘ (s1 ;; s2) =>
       P (State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m) → P S2
    | Stmt ↘ (l :; s) =>
       P (State (CStmt (l :; □) :: k) (Stmt ↘ s) m) → P S2
    | Stmt ↗ s =>
       (∀ k' b,
         k = CBlock b :: k' →
         P (State k' (Stmt ↗ (blk s)) (delete b m))) →
       (∀ k' s2,
         k = CStmt (□ ;; s2) :: k' →
         P (State (CStmt (s ;; □) :: k') (Stmt ↘ s2) m)) →
       (∀ k' s1,
         k = CStmt (s1 ;; □) :: k' →
         P (State k' (Stmt ↗ (s1 ;; s)) m)) →
       (∀ k' e,
         k = CStmt (while (e) □) :: k' →
         P (State k' (Stmt ↘ (while (e) s)) m)) →
       (∀ k' e s2,
         k = CStmt (IF e then □ else s2) :: k' →
         P (State k' (Stmt ↗ (IF e then s else s2)) m)) →
       (∀ k' e s1,
         k = CStmt (IF e then s1 else □) :: k' →
         P (State k' (Stmt ↗ (IF e then s1 else s)) m)) →
       (∀ k' l,
         k = CStmt (l :; □) :: k' →
         P (State k' (Stmt ↗ (l :; s)) m)) →
       (∀ k' bs,
         k = CParams bs :: k' →
         P (State k' (Return voidc) (delete_list bs m))) →
       P S2
    | Call f vs =>
       (∀ s bs m2,
         δ !! f = Some s →
         alloc_params Writable m bs vs m2 →
         P (State (CParams bs :: k) (Stmt ↘ s) m2)) →
       P S2
    | Stmt (⇈ v) s =>
       (∀ k' bs,
         k = CParams bs :: k' →
         P (State k' (Return v) (delete_list bs m))) →
       (∀ k' b,
         k = CBlock b :: k' →
         P (State k' (Stmt (⇈ v) (blk s)) (delete b m))) →
       (∀ k' E,
         k = CStmt E :: k' →
         P (State k' (Stmt (⇈ v) (subst E s)) m)) →
       P S2
    | Stmt (↷ l) s =>
       (∀ s',
         s = (l :; s') →
         P (State (CStmt (l :; □) :: k) (Stmt ↘ s') m)) →
       (∀ s' b,
         s = blk s' →
         l ∈ labels s →
         is_free m b →
         P (State (CBlock b :: k) (Stmt (↷ l) s')
           (mem_alloc b voidc Writable m))) →
       (∀ k' b,
         k = CBlock b :: k' →
         l ∉ labels s →
         P (State k' (Stmt (↷l) (blk s)) (delete b m))) →
       (∀ s' E,
         s = subst E s' →
         l ∈ labels s' →
         P (State (CStmt E :: k) (Stmt (↷ l) s') m)) →
       (∀ k' E,
         k = CStmt E :: k' →
         l ∉ labels s →
         P (State k' (Stmt (↷ l) (subst E s)) m)) →
       P S2
    | Undef => P S2
    end.
  Proof.
    intros p. case p; eauto.
    intros ? [] ??; simpl; eauto.
  Qed.

  Lemma cstep_expr_inv (P : state → Prop) E k Ω v m S2 :
    δ ⊢ₛ State (E :: k) (Expr (valc@{Ω} v)) m ⇒ S2 →
    match E with
    | CExpr e (do □) =>
       P (State k (Stmt ↗ (do e)) (mem_unlock Ω m)) → P S2
    | CExpr e (ret □) =>
       P (State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m)) → P S2
    | CExpr e (while (□) s) =>
      (val_true v →
        P (State (CStmt (while (e) □) :: k) (Stmt ↘ s) (mem_unlock Ω m))) →
      (val_false v →
        P (State k (Stmt ↗ (while (e) s)) (mem_unlock Ω m))) →
      P S2
    | CExpr e (IF □ then s1 else s2) =>
      (val_true v →
        P (State (CStmt (IF e then □ else s2) :: k)
          (Stmt ↘ s1) (mem_unlock Ω m))) →
      (val_false v →
        P (State (CStmt (IF e then s1 else □) :: k)
          (Stmt ↘ s2) (mem_unlock Ω m))) →
      P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2.
    apply (cstep_focus_inv _ _ _ p);
      try solve [intros; simplify_equality; eauto].
    * intros Ee e1 v2 m2 Hv p'. simplify_list_subst_equality Hv.
      edestruct ehstep_val; eauto.
    * intros Ee f Ωs vs Hv. simplify_list_subst_equality Hv.
    * intros Ee e1 Hv ? _. simplify_list_subst_equality Hv.
      by destruct (is_redex_val Ω v).
  Qed.

  Lemma cstep_stmt_up_inv (P : state → Prop) E k s m S2 :
    δ ⊢ₛ State (E :: k) (Stmt ↗ s) m ⇒ S2 →
    match E with
    | CStmt (□ ;; s2) =>
       P (State (CStmt (s ;; □) :: k) (Stmt ↘ s2) m) → P S2
    | CStmt (s1 ;; □) =>
       P (State k (Stmt ↗ (s1 ;; s)) m) → P S2
    | CStmt (while (e) □) =>
       P (State k (Stmt ↘ (while (e) s)) m) → P S2
    | CStmt (IF e then □ else s2) =>
       P (State k (Stmt ↗ (IF e then s else s2)) m) → P S2
    | CStmt (IF e then s1 else □) =>
       P (State k (Stmt ↗ (IF e then s1 else s)) m) → P S2
    | CStmt (l :; □) =>
       P (State k (Stmt ↗ (l :; s)) m) → P S2
    | CBlock b =>
       P (State k (Stmt ↗ (blk s)) (delete b m)) → P S2
    | CParams bs =>
       P (State k (Return voidc) (delete_list bs m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2.
    apply (cstep_focus_inv _ _ _ p);
      intros; simplify_equality; eauto.
  Qed.

  Lemma cstep_stmt_top_inv (P : state → Prop) E k v s m S2 :
    δ ⊢ₛ State (E :: k) (Stmt (⇈ v) s) m ⇒ S2 →
    match E with
    | CStmt E =>
       P (State k (Stmt (⇈ v) (subst E s)) m) → P S2
    | CParams bs =>
       P (State k (Return v) (delete_list bs m)) → P S2
    | CBlock b =>
       P (State k (Stmt (⇈ v) (blk s)) (delete b m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2.
    apply (cstep_focus_inv _ _ _ p);
      intros; simplify_equality; eauto.
  Qed.

  Lemma cstep_stmt_jump_down_inv (P : state → Prop) k l s m S2 :
    δ ⊢ₛ State k (Stmt (↷ l) s) m ⇒ S2 →
    l ∈ labels s →
    match s with
    | blk s =>
       (∀ b,
         is_free m b → l ∈ labels s →
         P (State (CBlock b :: k) (Stmt (↷ l) s)
           (mem_alloc b voidc Writable m))) →
       P S2
    | s1 ;; s2 =>
       (l ∈ labels s1 → P (State (CStmt (□ ;; s2) :: k) (Stmt (↷ l) s1) m)) →
       (l ∈ labels s2 → P (State (CStmt (s1 ;; □) :: k) (Stmt (↷ l) s2) m)) →
       P S2
    | l' :; s =>
       (l = l' → P (State (CStmt (l' :; □) :: k) (Stmt ↘ s) m)) →
       (l ∈ labels s → P (State (CStmt (l' :; □) :: k) (Stmt (↷ l) s) m)) →
       P S2
    | while (e) s =>
       (l ∈ labels s → P (State (CStmt (while (e) □) :: k) (Stmt (↷ l) s) m)) →
       P S2
    | (IF e then s1 else s2) =>
       (l ∈ labels s1 →
         P (State (CStmt (IF e then □ else s2) :: k) (Stmt (↷ l) s1) m)) →
       (l ∈ labels s2 →
         P (State (CStmt (IF e then s1 else □) :: k) (Stmt (↷ l) s2) m)) →
       P S2
    | _ => P S2
    end.
  Proof.
    intros p ?. pattern S2.
    apply (cstep_focus_inv _ _ _ p); try solve_elem_of.
    intros ? []; solve_elem_of.
  Qed.

  Lemma cstep_stmt_jump_up_inv (P : state → Prop) E k l s m S2 :
    δ ⊢ₛ State (E :: k) (Stmt (↷ l) s) m ⇒ S2 →
    l ∉ labels s →
    match E with
    | CStmt E =>
       P (State k (Stmt (↷ l) (subst E s)) m) → P S2
    | CBlock b =>
       P (State k (Stmt (↷ l) (blk s)) (delete b m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p ?. pattern S2.
    apply (cstep_focus_inv _ _ _ p);
      try solve [intros; subst; try solve_elem_of].
    intros ? [] ?; subst; solve_elem_of.
  Qed.
End inversion.

(** The previously defined inversion schemes all work for reductions of
a different shape. We therefore define the tactic [fast_inv_cstep] to
automatically pick the most suitable inversion scheme. It also performs the
necessary generalization of assumptions. *)
Ltac fast_inv_cstep H :=
  match type of H with
  | _ ⊢ₛ _ ⇒ ?S2 =>
    is_var S2;
    block_goal;
    repeat match goal with
    | H' : context [ S2 ] |- _ => var_neq H H'; revert H'
    end;
    pattern S2; first
    [ apply (cstep_expr_inv _ _ _ _ _ _ _ _ H)
    | apply (cstep_stmt_up_inv _ _ _ _ _ _ _  H)
    | apply (cstep_stmt_top_inv _ _ _ _ _ _ _ _ H)
    | first_of
        ltac:(apply (cstep_stmt_jump_down_inv _ _ _ _ _ _ _ H))
        assumption
        idtac
    | first_of
        ltac:(apply (cstep_stmt_jump_up_inv _ _ _ _ _ _ _ _ H))
        assumption
        idtac
    | apply (cstep_focus_inv _ _ _ _ H)];
    clear H; intros; unblock_goal
  end.

(** Some reduction are not of a shape that fits any of the previously defined
inversion schemes. The tactic [slow_inv_cstep] inverts a reduction using Coq's
standard [inversion] tactic and works for reductions of all shapes. *)
Ltac slow_inv_cstep H :=
  match type of H with
  | _ ⊢ₛ ?S1 ⇒ ?S2 => inversion H; clear H
  end.

(** * Restricting small step reduction *)
(** To give a model of our axiomatic semantics (see the file [axiomatic]) we
need to restrict the traversal through the program context to remain below a
certain context. *)
Definition cstep_in_ctx δ k : relation state := λ S1 S2,
  δ ⊢ₛ S1 ⇒ S2 ∧ suffix_of k (SCtx S2).
Notation "δ ⊢ₛ S1 ⇒{ k } S2" := (cstep_in_ctx δ k S1 S2)
  (at level 74,
   format "δ  ⊢ₛ '['  S1  '/' '⇒{' k '}' '/'  S2 ']'") : C_scope.
Notation "δ ⊢ₛ S1 ⇒{ k }* S2" := (rtc (cstep_in_ctx δ k) S1 S2)
  (at level 74,
   format "δ  ⊢ₛ '['  S1  '/' '⇒{' k '}*' '/'  S2 ']'") : C_scope.
Notation "δ ⊢ₛ S1 ⇒{ k }^ n S2" := (bsteps (cstep_in_ctx δ k) n S1 S2)
  (at level 74, n at level 1,
   format "δ  ⊢ₛ '['  S1  '/' '⇒{' k '}^' n '/'  S2 ']'") : C_scope.

Instance cstep_subrel_suffix_of δ k1 k2 :
  PropHolds (suffix_of k1 k2) →
  subrelation (cstep_in_ctx δ k2) (cstep_in_ctx δ k1).
Proof. intros ? S1 S2 [??]. split. done. by transitivity k2. Qed.
Instance cstep_subrel δ k : subrelation (cstep_in_ctx δ k) (cstep δ).
Proof. firstorder. Qed.
Instance cstep_subrel_nil δ : subrelation (cstep δ) (cstep_in_ctx δ []).
Proof. intros S1 S2 ?. split. done. solve_suffix_of. Qed.

Lemma cstep_in_ctx_rtc δ k S1 S2 :
  δ ⊢ₛ S1 ⇒{k}* S2 →
  suffix_of k (SCtx S2) ∨ S1 = S2.
Proof.
  revert S1 S2. apply rtc_ind_r.
  * by right.
  * intros ??? _ [??] _. by left.
Qed.
Lemma cstep_in_ctx_bsteps δ n k S1 S2 :
  δ ⊢ₛ S1 ⇒{k}^n S2 →
  suffix_of k (SCtx S2) ∨ S1 = S2.
Proof.
  intros p. apply bsteps_rtc in p.
  eapply cstep_in_ctx_rtc; eauto.
Qed.

(** * Tactics *)
(** The small step semantics is non-deterministic when entering a block or
function scope as variables are given an arbitrary memory index. The following
lemmas, that are useful to automatically perform reduction steps, pick a fully
determined one. *)
Lemma ehstep_alloc_fresh ρ m :
  let b := fresh (dom indexset m) in
  ρ ⊢ₕ alloc, m ⇒ ptrc b, (mem_alloc b voidc Freeable m)%V.
Proof. constructor. eapply not_elem_of_mem_dom, is_fresh. Qed.

Lemma cstep_in_block_fresh δ k s m :
  let b := fresh (dom indexset m) in
  δ ⊢ₛ State k (Stmt ↘ (blk s)) m ⇒
       State (CBlock b :: k) (Stmt ↘ s) (mem_alloc b voidc Writable m).
Proof. constructor. eapply not_elem_of_mem_dom, is_fresh. Qed.

Lemma cstep_label_block_down_fresh δ l k s m :
  l ∈ labels s →
  let b := fresh (dom indexset m) in
  δ ⊢ₛ State k (Stmt (↷ l) (blk s)) m ⇒
       State (CBlock b :: k) (Stmt (↷ l) s) (mem_alloc b voidc Writable m).
Proof. constructor. done. eapply not_elem_of_mem_dom, is_fresh. Qed.

Lemma cstep_alloc_params_fresh δ k f s m vs :
  δ !! f = Some s →
  let bs := fresh_list (length vs) (dom indexset m) in
  δ ⊢ₛ State k (Call f vs) m ⇒
       State (CParams bs :: k) (Stmt ↘ s)
             (mem_alloc_list Writable (zip bs vs) m).
Proof.
  constructor. done. apply alloc_params_alloc_list. split_ands.
  * done.
  * apply is_free_list_alt. split.
    + apply fresh_list_nodup.
    + apply Forall_forall. intros.
      eapply not_elem_of_mem_dom, fresh_list_is_fresh; eauto.
  * apply same_length_length. by rewrite fresh_list_length.
Qed.

Hint Resolve
  ehstep_alloc_fresh
  cstep_in_block_fresh cstep_label_block_down_fresh
  cstep_alloc_params_fresh : cstep.

(** The [quote_stmt s] tactic yields a list of possible ways to write a
statement [s] as:

- [subst E s'] where [E] is a singular statement context, and [s'] a statement,
- [subst E s'] where [E] is a singular expression in statement context, and
  [s'] a statement.

This tactic is useful to automatically perform reductions, as for example
[cstep_label_down] whose starting state is [State k (Stmt (↷ l) (subst E s)) m].
*)
Ltac quote_stmt s :=
  lazymatch s with
  | do ?e => constr:[subst (do □) e]
  | ret ?e => constr:[subst (ret □) e]
  | ?s1 ;; ?s2 => constr:[subst (s1 ;; □) s2; subst (□ ;; s2) s1]
  | ?l :; ?s => constr:[subst (l :; □) s]
  | while (?e) ?s =>
    constr:[subst (while (e) □) s; subst (while (□) s) e]
  | IF ?e then ?s1 else ?s2 =>
    constr:[subst (IF e then s1 else □) s2;
            subst (IF e then □ else s2) s1;
            subst (IF □ then s1 else s2) e]
  end.

(** The [quote_expr e] tactic yields a list of possible ways to write an
expression [e] as [subst E e'] where [E] is an expression evaluation context,
and [e'] an expression. This tactic may be seen as an [Ltac] variant of the
function [expr_redexes], but whereas [expr_redexes] only includes
subexpressions [e'] that are redexes, all subexpressions are included here. We
omit function calls for the moment. *)
Local Open Scope expr_scope.
Ltac quote_expr e :=
  let rec go2 k1 e1 k2 e2 :=
    let  q1 := go k1 e1
    with q2 := go k2 e2
    in constr:(q1 ++ q2)
  with go k e :=
    let q :=
    match e with
    | ?el ::= ?er => go2 (□ ::= er :: k) el (el ::= □ :: k) er
    | load ?e => go (load □ :: k) e
    | free ?e => go (free □ :: k) e
    | ⊙{?op} ?e => go (⊙{op} □ :: k) e
    | ?el ⊙{?op} ?er => go2 (□ ⊙{op} er :: k) el (el ⊙{op} □ :: k) er
    | IF ?e then ?el else ?er => go (IF □ then el else er :: k) e
    | _ => constr:(@nil expr)
    end in constr:(subst k e :: q)
  in go (@nil ectx_item) e.
Local Close Scope expr_scope.

(** The [do_cstep] tactic is used to solve goals of the shape [δ ⊢ₛ S1 ⇒ S2] or
as [δ ⊢ₛ S1 ⇒{k} S2] by applying a matching reduction rule, or by using the
hint database [cstep]. *)
Ltac do_cstep :=
  let go1 := first
    [ econstructor (solve [intuition eauto with cstep])
    | solve [intuition eauto with cstep]]
  in let go2 := idtac;
    match goal with
    | |- ?δ ⊢ₛ State ?k (Stmt ?d ?s) ?m ⇒ ?S => iter
      (fun s' => change (δ ⊢ₛ State k (Stmt d s') m ⇒ S); go1)
      (quote_stmt s)
    | |- ?δ ⊢ₛ State ?k (Expr ?e) ?m ⇒ ?S => iter
      (fun e' => change (δ ⊢ₛ State k (Expr e') m ⇒ S); go1)
      (quote_expr e)
    | _ => go1
  end in
  simpl;
  match goal with
  | |- _ ⊢ₛ _ ⇒{_} _ => first
    [ split; [go2 | simpl; solve_suffix_of]
    | solve [intuition eauto with cstep]]
  | |- _ ⊢ₛ _ ⇒ _ => go2
  end.

Ltac do_csteps :=
  match goal with
  | |- _ ⊢ₛ _ ⇒* _ => apply rtc_refl
  | |- _ ⊢ₛ _ ⇒* _ => eapply rtc_l; [do_cstep | do_csteps]
  | |- _ ⊢ₛ _ ⇒{_}* _ => apply rtc_refl
  | |- _ ⊢ₛ _ ⇒{_}* _ => eapply rtc_l; [do_cstep | do_csteps]
  | |- _ ⊢ₛ _ ⇒^_ _ => apply bsteps_refl
  | |- _ ⊢ₛ _ ⇒^(S _) _ => eapply bsteps_l; [do_cstep | do_csteps]
  | |- _ ⊢ₛ _ ⇒{_}^(S _) _ => apply bsteps_S; do_csteps
  | |- _ ⊢ₛ _ ⇒{_}^_ _ => apply bsteps_refl
  | |- _ ⊢ₛ _ ⇒{_}^(S _) _ => eapply bsteps_l; [do_cstep | do_csteps]
  | |- _ ⊢ₛ _ ⇒{_}^(S _) _ => apply bsteps_S; do_csteps
  | |- _ => solve [intuition eauto with cstep]
  end.

(** The tactic [inv_cstep] inverts a reduction step and performs some clean up
and discharges impossible cases afterwards. *)
Tactic Notation "inv_cstep" hyp(H) :=
  try match type of H with
  | _ ⊢ₛ _ ⇒{_} _ => destruct H as [H ?]
  end;
  match type of H with
  | _ ⊢ₛ ?S1 ⇒ ?S2 =>
    (**i perform the actual inversion, and print a message (for debugging) in
    case slow inversion has been used *)
    first
      [ fast_inv_cstep H
      | idtac "slow inversion on" S1; slow_inv_cstep H ];

    (**i clean up, and discharge impossible cases *)
    simplify_list_subst_equality;
    repeat match goal with
    | _ => done
    | _ => progress discriminate_down_up
    | Ht : val_true ?v, Hf : val_false ?v |- _ =>
      destruct (val_true_false v Ht Hf)
    | H : suffix_of _ _ |- _ =>
      progress (simpl in H; simplify_suffix_of)
    | H : _ ⊢ₕ valc@{_} _, _ ⇒ _, _ |- _ =>
      by apply ehstep_val in H
    | H : is_redex (valc@{_} ?v) |- _ =>
      by apply is_redex_val in H
    end
  end.
Tactic Notation "inv_cstep" :=
  match goal with
  | H : _ ⊢ₛ _ ⇒ _ |- _ => inv_cstep H
  | H : _ ⊢ₛ _ ⇒{_} _ |- _ => inv_cstep H
  end.

Tactic Notation "inv_csteps" hyp(H) "as" simple_intropattern(H2) :=
  (* use a fresh name so we do not clear the wrong hypothesis *)
  let H' := fresh in
  rename H into H';
  inversion H' as H2; clear H'; try subst.
Tactic Notation "inv_csteps" hyp(H) := inv_csteps H as [].

Tactic Notation "last_cstep" hyp(H) :=
  let H' := fresh in
  inv_csteps H as [| ???? H' ?]; [| solve [inv_cstep H']].

(** The [solve_cred] tactic solves goals of the shape [red (δ⇒ₛ) S] and
[red (δ⇒ₛ{k}) S] by performing case distinctions on [S] and using the
[do_cstep] tactic to perform the actual step. *)
Ltac solve_cred :=
  repeat match goal with
  | H : down _ _ |- _ => progress simpl in H
  | H : up _ _ |- _ => progress simpl in H
  | |- red (cstep _) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; try contradiction
  | |- red (cstep_in_ctx _ _) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; try contradiction
  | H : ?l ∈ _ |- red (cstep _) (State _ (Stmt (↷ ?l) _) _) =>
    progress decompose_elem_of H
  | H : ?l ∈ _ |- red (cstep_in_ctx _ _) (State _ (Stmt (↷ ?l) _) _) =>
    progress decompose_elem_of H
  end;
  match goal with
  | H : red (cstep_in_ctx _ _) ?S |- red (cstep_in_ctx _ _ _) ?S =>
    by apply (red_subrel _ _ _ _ H)
  | |- red (cstep _) _ => eexists; do_cstep
  | |- red (cstep_in_ctx _ _) _ => eexists; do_cstep
  | |- _ => solve [intuition eauto with cstep]
  end.

Ltac solve_cnf :=
  lazymatch goal with
  | H : nf (cstep _) _ |- _ => destruct H; solve_cred
  | H : nf (cstep_in_ctx _ _) _ |- _ => destruct H; solve_cred
  end.

(** * Theorems *)
Section smallstep_properties.
Context (δ : funenv).

Lemma cstep_expr_depsubst_inv {n} (P : state → Prop)
    k (E : ectx_full n) (es : vec expr n) m S' :
  δ ⊢ₛ State k (Expr (depsubst E es)) m ⇒{k} S' →
  (∀ i e' m',
    δ ⊢ₛ State k (Expr (es !!! i)) m ⇒{k} State k (Expr e') m' →
    P (State k (Expr (depsubst E (vinsert i e' es))) m')) →
  (∀ i E' f Ωs vs,
    same_length Ωs vs →
    es !!! i = subst E' (call f @ zip_with EVal Ωs vs)%E →
    δ ⊢ₛ State k (Expr (es !!! i)) m ⇒{k}
         State (CFun E' :: k) (Call f vs) (mem_unlock (⋃ Ωs) m) →
    P (State (CFun (E' ++ [ectx_full_to_item E es i]) :: k)
      (Call f vs) (mem_unlock (⋃ Ωs) m))) →
  (∀ Ωs vs,
    es = vzip_with EVal Ωs vs →
    P S') →
  (∀ i,
    δ ⊢ₛ State k (Expr (es !!! i)) m ⇒{k} State k Undef m →
    P (State k Undef m)) →
  P S'.
Proof.
  intros [p Hsuffix]. revert Hsuffix. pattern S'.
  apply (cstep_focus_inv _ _ _ _ p); simpl; try solve_suffix_of.
  * intros E' e1 e2 m2 HE pe _ HP1 _ HP3 _.
    destruct E' as [|E'' E' _] using rev_ind.
    + simpl in *. subst.
      destruct (proj1 (Forall_is_value_alt_vec es)) as (Ωs & vs & ?).
      { eapply is_redex_ectx_full, ehstep_is_redex; eauto. }
      by apply (HP3 Ωs vs).
    + rewrite !subst_snoc in HE |- *.
      apply ectx_full_item_subst in HE. destruct HE as [i [HE1 HE2]].
      rewrite HE2, <-ectx_full_to_item_correct_alt.
      apply HP1. rewrite <-HE1. do_cstep.
  * intros E' f Ωs vs HE Hvs _ _ HP2 HP3 _.
    destruct E' as [|E'' E' _] using rev_ind.
    + simpl in *. destruct E; simplify_equality.
      destruct (proj1 (Forall_is_value_alt_vec es)) as (Ωs' & vs' & ?).
      { apply Forall_is_value_alt. by exists Ωs vs. }
      by apply (HP3 Ωs' vs').
    + rewrite !subst_snoc in HE.
      apply ectx_full_item_subst in HE. destruct HE as [i [HE1 HE2]].
      rewrite HE2. apply HP2; rewrite <-?HE1; trivial. do_cstep.
  * intros E' e1 HE Hred Hsafe _ HP1 HP2 HP3 HP4.
    destruct E' as [|E'' E' _] using rev_ind.
    + simpl in *. subst. 
      destruct (proj1 (Forall_is_value_alt_vec es)) as (Ωs & vs & ?).
      { eapply is_redex_ectx_full; eauto. }
      by apply (HP3 Ωs vs).
    + rewrite !subst_snoc in HE.
      apply ectx_full_item_subst in HE. destruct HE as [i [HE1 HE2]].
      apply (HP4 i). rewrite <-HE1. do_cstep.
Qed.

Lemma cstep_expr_call_inv (P : state → Prop) k f Ωs vs m S' :
  δ ⊢ₛ State k (Expr (call f @ zip_with EVal Ωs vs)) m ⇒{k} S' →
  same_length Ωs vs →
  P (State (CFun [] :: k) (Call f vs) (mem_unlock (⋃ Ωs) m)) →
  (¬get_stack k ⊢ₕ safe call f @ zip_with EVal Ωs vs, m →
    P (State k Undef m)) →
  P S'.
Proof.
  intros [p Hsuffix] ?. revert Hsuffix. pattern S'.
  apply (cstep_focus_inv _ _ _ _ p); simpl; try solve_suffix_of.
  * intros E e1 v2 m2 Hvs ? _ _ _.
    simplify_list_subst_equality Hvs; [by inv_ehstep |].
    simplify_zip_equality.
    simplify_list_subst_equality. inv_ehstep.
  * intros E f' Ωs' vs' Hvs ? _ HP1 _.
    simplify_list_subst_equality Hvs.
    { edestruct (zip_with_inj EVal Ωs vs Ωs' vs');
        eauto with congruence. }
    simplify_zip_equality.
    simplify_list_subst_equality.
  * intros E e1 Hvs ?? _ _ HP2.
    simplify_list_subst_equality Hvs; [eauto |].
    simplify_zip_equality.
    simplify_list_subst_equality.
    edestruct is_redex_val; eauto.
Qed.

Lemma cnf_undef k m : nf (cstep δ) (State k Undef m).
Proof. intros [? p]. inv_cstep p. Qed.
Lemma cnf_in_ctx_undef l k m : nf (cstep_in_ctx δ l) (State k Undef m).
Proof. apply (nf_subrel _ (cstep δ) _), cnf_undef. Qed.

Lemma cnf_val l Ω v m :
  nf (cstep_in_ctx δ l) (State l (Expr (valc@{Ω} v)) m).
Proof. intros [? p]. inv_cstep p. Qed.

Lemma cstep_ctx_irrel l l' k1 φ1 m1 k2 φ2 m2 :
  δ ⊢ₛ State (k1 ++ l) φ1 m1 ⇒ State (k2 ++ l) φ2 m2 →
  get_stack l = get_stack l' →
  δ ⊢ₛ State (k1 ++ l') φ1 m1 ⇒ State (k2 ++ l') φ2 m2.
Proof.
  intros p Hstack.
  change (proj_relation (=) get_stack l l') in Hstack.
  inv_cstep p;
    rewrite ?app_comm_cons in *; simplify_list_equality; first
    [ do_cstep
    | destruct k2,k1; simpl in *; simplify_list_equality; do_cstep
    | rewrite ?Hstack in *; do_cstep ].
Qed.

Lemma cred_ctx_irrel l l' k φ m :
  red (cstep_in_ctx δ l) (State (k ++ l) φ m) →
  get_stack l = get_stack l' →
  red (cstep_in_ctx δ l') (State (k ++ l') φ m).
Proof.
  intros [[? φ' m'] [p [k' ?]]] ?; simpl in *; subst.
  exists (State (k' ++ l') φ' m'). split.
  * by apply cstep_ctx_irrel with l.
  * simpl. solve_suffix_of.
Qed.

Lemma cstep_call_inv (P : state → Prop) E E' l k1 φ1 m1 S' :
  δ ⊢ₛ State (k1 ++ [CFun E] ++ l) φ1 m1 ⇒{l} S' →
  (∀ k2 φ2 m2,
     δ ⊢ₛ State (k1 ++ [CFun E'] ++ l) φ1 m1 ⇒{l}
          State (k2 ++ [CFun E'] ++ l) φ2 m2 →
     P (State (k2 ++ [CFun E] ++ l) φ2 m2)) →
  (∀ v,
     k1 = [] →
     φ1 = Return v →
     δ ⊢ₛ State (CFun E' :: l) (Return v) m1 ⇒{l}
          State l (Expr (subst E' (valc v)%E)) m1 →
     P (State l (Expr (subst E (valc v)%E)) m1)) →
  P S'.
Proof.
  intros [p ?] HP1 HP2. destruct S' as [k2 φ2 m2].
  destruct (decide (suffix_of (CFun E :: l) k2)) as [[k2' ?]|?]; subst.
  * apply HP1. split; [| simpl; solve_suffix_of].
    by apply cstep_ctx_irrel with (CFun E :: l).
  * inv_cstep p; destruct k1;
      try solve_suffix_of; simplify_list_equality.
    apply HP2; trivial. do_cstep.
Qed.

Lemma cred_ectx (E : ectx) k e m :
  red (cstep_in_ctx δ k) (State k (Expr e) m) →
  red (cstep_in_ctx δ k) (State k (Expr (subst E e)) m).
Proof. intros [S p]. inv_cstep p; rewrite <-subst_app; eexists; do_cstep. Qed.

(** ** Cutting reduction paths *)
(** Given a reduction path, we can cut off the maximal prefix that is restricted
by a more restrictive program context. *)
Lemma cstep_subctx_step_or_nf k S1 S2 :
  δ ⊢ₛ S1 ⇒ S2 →
  suffix_of k (SCtx S1) →
  suffix_of k (SCtx S2) ∨ nf (cstep_in_ctx δ k) S1.
Proof.
  intros p1 ?.
  destruct (decide (suffix_of k (SCtx S2))) as [Hk|Hk].
  * by left.
  * right. intros [S2' [p2 ?]]. destruct Hk.
    destruct p1; simpl in *; try solve_suffix_of; by inv_cstep p2.
Qed.

Lemma cred_preserves_subctx k S1 S2 :
  δ ⊢ₛ S1 ⇒ S2 →
  red (cstep_in_ctx δ k) S1 →
  suffix_of k (SCtx S1) →
  suffix_of k (SCtx S2).
Proof. intros. by destruct (cstep_subctx_step_or_nf k S1 S2). Qed.

Lemma cstep_subctx_nf k S1 S2 :
  nf (cstep_in_ctx δ k) S1 →
  δ ⊢ₛ S1 ⇒ S2 →
  suffix_of k (SCtx S1) →
  SCtx S1 = k.
Proof.
  intros Hnf p ?.
  destruct (decide (suffix_of k (SCtx S2))) as [Hk|Hk].
  * destruct Hnf. exists S2. by split.
  * destruct p; simpl in *; destruct k; solve_suffix_of.
Qed.

Lemma cstep_subctx_cut l k S1 S2 :
  δ ⊢ₛ S1 ⇒{k} S2 →
  suffix_of (l ++ k) (SCtx S1) →
  δ ⊢ₛ S1 ⇒{l ++ k} S2
    ∨
  SCtx S1 = l ++ k ∧ nf (cstep_in_ctx δ (l ++ k)) S1.
Proof.
  intros [p ?] ?.
  destruct (cstep_subctx_step_or_nf (l ++ k) S1 S2); trivial.
  + left. do_cstep.
  + right. split. by apply cstep_subctx_nf with S2. done.
Qed.

Lemma cstep_bsteps_subctx_cut n l k S1 S3 :
  δ ⊢ₛ S1 ⇒{k}^n S3 →
  suffix_of (l ++ k) (SCtx S1) →
  δ ⊢ₛ S1 ⇒{l ++ k}^n S3
    ∨
  ∃ S2, δ ⊢ₛ S1 ⇒{l ++ k}^n S2
    ∧ SCtx S2 = l ++ k
    ∧ nf (cstep_in_ctx δ (l ++ k)) S2
    ∧ δ ⊢ₛ S2 ⇒{k}^n S3.
Proof.
  intros p ?. induction p as [ n S1 | n S1 S2 S3 p1 p2].
  { left. auto with ars. }
  destruct (cstep_subctx_cut l _ _ _ p1) as [[??] | [??]]; trivial.
  * destruct IHp2 as [? | [S2' ?]]; trivial.
    + left. do_csteps.
    + right. exists S2'. intuition trivial; do_csteps.
  * right. exists S1. intuition eauto with ars.
Qed.

Lemma cstep_bsteps_subctx_cut_alt n l k φ1 m1 S3 :
  δ ⊢ₛ State (l ++ k) φ1 m1 ⇒{k}^n S3 →
  δ ⊢ₛ State (l ++ k) φ1 m1 ⇒{l ++ k}^n S3
    ∨
  ∃ φ2 m2,
      δ ⊢ₛ State (l ++ k) φ1 m1 ⇒{l ++ k}^n State (l ++ k) φ2 m2
    ∧ nf (cstep_in_ctx δ (l ++ k)) (State (l ++ k) φ2 m2)
    ∧ δ ⊢ₛ State (l ++ k) φ2 m2 ⇒{k}^n S3.
Proof.
  intros p. destruct (cstep_bsteps_subctx_cut _ l _ _ _ p)
    as [? | ([] & ? & ? & ?)]; naive_solver.
Qed.

(** ** Preservation of statements *)
(** We prove that small step reduction behaves as traversing through a zipper.
That is, if [δ ⊢ₛ State k (Stmt d1 s1) m1 ⇒{k}* State k (Stmt d2 s2) m2], then
[s1 = s2]. This proven on the length of the reduction path. When a transition
to the expression state occurs, we cut of the prefix corresponding to execution
of that expression. *)
Definition in_fun_ctx (k1 k2 : ctx) : Prop := ∃ l,
  Forall ctx_item_or_block l ∧ k2 = l ++ k1.

Instance: Reflexive in_fun_ctx.
Proof. intros k. eexists []. intuition trivial. Qed.

Lemma in_fun_ctx_r k1 k2 E :
  ctx_item_or_block E →
  in_fun_ctx k1 k2 →
  in_fun_ctx k1 (E :: k2).
Proof. intros ? [l [??]]. subst. exists (E :: l). intuition. Qed.
Lemma in_fun_ctx_app_r k1 k2 k :
  Forall ctx_item_or_block k →
  in_fun_ctx k1 k2 →
  in_fun_ctx k1 (k ++ k2).
Proof. induction 1; simpl; auto using in_fun_ctx_r. Qed.
Lemma in_fun_ctx_r_inv k1 k2 E :
  ctx_item_or_block E →
  suffix_of k1 k2 →
  in_fun_ctx k1 (E :: k2) →
  in_fun_ctx k1 k2.
Proof.
  intros ? [l1 ?] [l2 [Hc1 Hc2]]. subst.
  rewrite app_comm_cons in Hc2. apply app_inv_tail in Hc2. subst.
  inversion_clear Hc1. exists l1. intuition.
Qed.
Lemma in_fun_ctx_change k1 k2 E1 E2 :
  ctx_item_or_block E2 →
  suffix_of k1 (E2 :: k2) →
  in_fun_ctx k1 (E1 :: k2) →
  in_fun_ctx k1 (E2 :: k2).
Proof.
  intros ? [[|E2' l1] ?] [l2 [Hc1 Hc2]].
  { eexists []. intuition. }
  destruct l2; simpl in *; simplify_equality.
  * discriminate_list_equality.
  * inversion_clear Hc1. eexists (E2' :: l2). intuition.
Qed.
Lemma in_fun_ctx_not_item_or_block k1 k2 E :
  ¬ctx_item_or_block E →
  suffix_of k1 k2 →
  ¬in_fun_ctx k1 (E :: k2).
Proof.
  intros ? [l1 ?] [l2 [Hc1 Hc2]]. subst.
  rewrite app_comm_cons in Hc2. apply app_inv_tail in Hc2. subst.
  by inversion Hc1.
Qed.

Lemma cstep_bsteps_preserves_stmt_help n k1 d1 s1 m1 k2 d2 s2 m2 :
  δ ⊢ₛ State k1 (Stmt d1 s1) m1 ⇒{k2}^n State k2 (Stmt d2 s2) m2 →
  in_fun_ctx k2 k1 →
  subst k1 s1 = subst k2 s2.
Proof.
  revert k1 s1 d1 m1.
  induction n as [n1 IH] using lt_wf_ind.
  intros k1 s1 d1 m1 p1 Hin_fun.
  inv_csteps p1 as [|n2 ? S' ? p2h p2]; [done|].
  inv_cstep p2h;
   try apply (IH _ (lt_n_Sn n2) _ _ _ _ p2);
   try first
    [ done
    | apply in_fun_ctx_r; eauto; constructor
    | eapply in_fun_ctx_r_inv; eauto; constructor
    | eapply in_fun_ctx_change; eauto; constructor
    | edestruct in_fun_ctx_not_item_or_block; eauto; inversion 1 ].
  destruct Hin_fun as [l [??]]. subst.
  rewrite app_comm_cons in p2.
  destruct (cstep_bsteps_subctx_cut_alt _ _ _ _ _ _ p2)
     as [p | (? & ? & _ & ? & p3)]; clear p2.
  * destruct (cstep_in_ctx_bsteps _ _ _ _ _ p)
      as [[??]|?]; by simplify_list_equality.
  * inv_csteps p3 as [| n4 ??? p4h p4].
    { discriminate_list_equality. }
    inv_cstep p4h; try solve_cnf;
     apply (IH _ (lt_n_SS n4) _ _ _ _ p4);
     by repeat first
      [ apply in_fun_ctx_app_r
      | apply in_fun_ctx_r; [constructor|]].
Qed.

Lemma cstep_bsteps_preserves_stmt n k d1 s1 m1 d2 s2 m2 :
  δ ⊢ₛ State k (Stmt d1 s1) m1 ⇒{k}^n State k (Stmt d2 s2) m2 →
  s1 = s2.
Proof.
  intros p. apply (injective (subst k)).
  by eapply cstep_bsteps_preserves_stmt_help; eauto.
Qed.
End smallstep_properties.
