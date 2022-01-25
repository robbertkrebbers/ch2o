(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** The small step reduction is a binary relation between execution states,
and computation is defined as the reflexive transitive closure of this
reduction relation. This file also defines tactics to automatically perform and
invert reduction steps. These tactics use the hint database [cstep] to solve
side-conditions. *)
Require Export operations state.

(** * Head reduction for expressions *)
(** We define head reduction for all redexes whose reduction is local (i.e.
does not change the current program context). Only function calls are non-local,
as they change to the call state, and store the current expression evaluation
context on the program context. These will be included in the whole reduction
relation [cstep].*)
(* The level is just below logical negation (whose level is 75). *)
Reserved Notation "Γ \ ρ ⊢ₕ e1 , m1 ⇒ e2 , m2"
  (at level 74, ρ at next level,
   format "Γ \  ρ  '⊢ₕ' '['  e1 ,  m1  ⇒ '/'  e2 ,  m2 ']'").
Inductive ehstep `{Env K} (Γ : env K) (ρ : stack K) :
     expr K → mem K → expr K → mem K → Prop :=
  | ehstep_var x τ o m :
     ρ !! x = Some (o,τ) →
     Γ\ ρ ⊢ₕ var x, m ⇒ %(Ptr (addr_top o τ)), m
  | ehstep_rtol m Ω p :
     ptr_alive' m p →
     Γ\ ρ ⊢ₕ .* (#{Ω} (ptrV p)), m ⇒ %{Ω} p, m
  | ehstep_rofl m Ω p :
     Γ\ ρ ⊢ₕ & (%{Ω} p), m ⇒ #{Ω} (ptrV p), m
  | ehstep_assign m ass Ω1 Ω2 a v v' va :
     mem_writable Γ a m → assign_sem Γ m a v ass va v' →
     Γ\ ρ ⊢ₕ %{Ω1} (Ptr a) ::={ass} #{Ω2} v, m ⇒
             #{lock_singleton Γ a ∪ Ω1 ∪ Ω2} v', mem_lock Γ a (<[a:=va]{Γ}>m)
  | ehstep_load m Ω a v :
     m !!{Γ} a = Some v →
     Γ\ ρ ⊢ₕ load (%{Ω} (Ptr a)), m ⇒ #{Ω} v, mem_force Γ a m
  | ehstep_eltl m Ω a rs :
     addr_strict Γ a →
     Γ\ ρ ⊢ₕ %{Ω} (Ptr a) %> rs, m ⇒ %{Ω} (Ptr (addr_elt Γ rs a)), m
  | ehstep_eltr m Ω v rs v' :
     v !!{Γ} rs = Some v' → Γ\ ρ ⊢ₕ #{Ω} v #> rs, m ⇒ #{Ω} v', m
  | ehstep_alloc_NULL m Ω τi τ n :
     alloc_can_fail → Z.to_nat n ≠ 0 →
     Γ\ ρ ⊢ₕ alloc{τ} (#{Ω} intV{τi} n), m ⇒ %{Ω} NULL (TType τ), m
  | ehstep_alloc m Ω o τi τ n :
     o ∉ dom indexset m → Z.to_nat n ≠ 0 →
     Γ\ ρ ⊢ₕ alloc{τ} (#{Ω} intV{τi} n), m ⇒
             %{Ω} Ptr (addr_top_array o τ n),
             mem_alloc Γ o true perm_full (val_new Γ (τ.[Z.to_nat n])) m
  | ehstep_free m Ω a :
     mem_freeable a m →
     Γ\ ρ ⊢ₕ free (%{Ω} (Ptr a)), m ⇒ #{Ω} voidV, mem_free (addr_index a) m
  | ehstep_unop op Ω v m :
     val_unop_ok m op v →
     Γ\ ρ ⊢ₕ .{op} #{Ω} v, m ⇒ #{Ω} val_unop op v, m
  | ehstep_binop op m Ω1 Ω2 v1 v2 :
     val_binop_ok Γ m op v1 v2 →
     Γ\ ρ ⊢ₕ #{Ω1} v1 .{op} #{Ω2} v2, m ⇒ #{Ω1 ∪ Ω2} val_binop Γ op v1 v2, m
  | ehstep_if_true m Ω vb e1 e2 :
     base_val_branchable m vb → ¬base_val_is_0 vb →
     Γ\ ρ ⊢ₕ if{#{Ω} VBase vb} e1 else e2, m ⇒ e1, mem_unlock Ω m
  | ehstep_if_false m Ω vb e1 e2 :
     base_val_branchable m vb → base_val_is_0 vb →
     Γ\ ρ ⊢ₕ if{#{Ω} VBase vb} e1 else e2, m ⇒ e2, mem_unlock Ω m
  | ehstep_comma m Ω ν e2 :
     Γ\ ρ ⊢ₕ %#{Ω} ν,,e2, m ⇒ e2, mem_unlock Ω m
  | ehstep_cast m τ Ω v :
     val_cast_ok Γ m (TType τ) v →
     Γ\ ρ ⊢ₕ cast{τ} (#{Ω} v), m ⇒ #{Ω} val_cast (TType τ) v, m
  | ehstep_insert m r v1 Ω1 v2 Ω2 :
     is_Some (v2 !!{Γ} r) →
     Γ\ ρ ⊢ₕ #[r:=#{Ω1} v1] (#{Ω2} v2), m ⇒
             #{Ω1 ∪ Ω2} val_alter Γ (λ _, v1) r v2, m
where "Γ \ ρ  ⊢ₕ e1 , m1 '⇒' e2 , m2" :=
  (@ehstep _ _ Γ ρ e1%E m1 e2%E m2) : C_scope.

(** An expression is safe if a head reduction step is possible. This relation
is adapted from CompCert and is used to capture undefined behavior. If the
whole expression contains a redex that is not safe, the semantics transitions
to the [Undef] state. *)
Reserved Notation "Γ \ ρ  '⊢ₕ' 'safe' e , m" (at level 74, ρ at next level).
Inductive ehsafe `{Env K} (Γ : env K) (ρ : stack K) : expr K → mem K → Prop :=
  | ehsafe_call Ω f τs τ Ωs vs m :
     length Ωs = length vs →
     Γ \ ρ ⊢ₕ safe (call %{Ω} (FunPtr f τs τ) @ #{Ωs}* vs), m
  | ehsafe_step e1 m1 e2 m2 : Γ \ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → Γ \ ρ ⊢ₕ safe e1, m1
where "Γ \ ρ  ⊢ₕ 'safe' e ,  m" := (@ehsafe _ _ Γ ρ e m) : C_scope.

(** * The reduction relation *)
(** Small step reduction works by traversal of the focus. Each step the focus
is executed, after which a transition to the next program state is performed. *)
Reserved Notation "Γ \ δ ⊢ₛ S1 ⇒ S2"
  (at level 74, δ at next level,
   format "Γ \  δ  ⊢ₛ  '[' S1  ⇒ '/'  S2 ']'").
Inductive cstep `{Env K} (Γ : env K) (δ : funenv K) : relation (state K) :=
  (**i For simple statements: *)
  | cstep_skip m k :
     Γ\ δ ⊢ₛ State k (Stmt ↘ skip) m ⇒
             State k (Stmt ↗ skip) m
  | cstep_goto m k l :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (goto l)) m ⇒
             State k (Stmt (↷ l) (goto l)) m
  | cstep_throw m k n :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (throw n)) m ⇒
             State k (Stmt (↑ n) (throw n)) m
  | cstep_case m k mx :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (scase mx)) m ⇒
             State k (Stmt ↗ (scase mx)) m
  | cstep_in_label m k l :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (label l)) m ⇒
             State k (Stmt ↗ (label l)) m
  | cstep_expr m k E e :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (subst E e)) m ⇒
             State (CExpr e E :: k) (Expr e) m

  (**i For expressions: *)
  | cstep_expr_head m1 m2 k (E : ectx K) e1 e2 :
     Γ\ locals k ⊢ₕ e1, m1 ⇒ e2, m2 →
     Γ\ δ ⊢ₛ State k (Expr (subst E e1)) m1 ⇒
             State k (Expr (subst E e2)) m2
  | cstep_expr_call m k Ω f τs τ E Ωs vs :
     length Ωs = length vs →
     let e := (call %{Ω} (FunPtr f τs τ) @ #{Ωs}* vs)%E in
     Γ\ δ ⊢ₛ State k (Expr (subst E e)) m ⇒
             State (CFun E :: k) (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m)
  | cstep_expr_undef m k (E : ectx K) e :
     is_redex e → ¬Γ \ locals k ⊢ₕ safe e, m →
     Γ\ δ ⊢ₛ State k (Expr (subst E e)) m ⇒
             State k (Undef (UndefExpr E e)) m

  (**i For finished expressions: *)
  | cstep_expr_do m k e Ω v :
     Γ\ δ ⊢ₛ State (CExpr e (! □) :: k) (Expr (#{Ω} v)) m ⇒
             State k (Stmt ↗ (! e)) (mem_unlock Ω m)
  | cstep_expr_ret m k e Ω v :
     Γ\ δ ⊢ₛ State (CExpr e (ret □) :: k) (Expr (#{Ω} v)) m ⇒
             State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m)
  | cstep_expr_if_true m k e Ω vb s1 s2 :
     base_val_branchable m vb → ¬base_val_is_0 vb →
     Γ\ δ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} VBase vb)) m ⇒
             State (CStmt (if{e} □ else s2) :: k) (Stmt ↘ s1) (mem_unlock Ω m)
  | cstep_expr_if_false m k e Ω vb s1 s2 :
     base_val_branchable m vb → base_val_is_0 vb →
     Γ\ δ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} VBase vb)) m ⇒
             State (CStmt (if{e} s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m)
  | cstep_expr_if_indet m k e Ω vb s1 s2 :
     ¬base_val_branchable m vb →
     Γ\ δ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} VBase vb)) m ⇒
             State k (Undef (UndefBranch (if{□} s1 else s2) Ω (VBase vb))) m
  | cstep_switch_case m k e Ω τi x s :
     Some x ∈ cases s →
     Γ\ δ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} (intV{τi} x))) m ⇒
             State (CStmt (switch{e} □) :: k)
                   (Stmt (↓ (Some x)) s) (mem_unlock Ω m)
  | cstep_switch_default m k e Ω τi x s :
     Some x ∉ cases s → None ∈ cases s →
     Γ\ δ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} (intV{τi} x))) m ⇒
             State (CStmt (switch{e} □) :: k) (Stmt (↓ None) s) (mem_unlock Ω m)
  | cstep_switch_out m k e Ω τi x s :
     Some x ∉ cases s → None ∉ cases s →
     Γ\ δ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} (intV{τi} x))) m ⇒
             State k (Stmt ↗ (switch{e} s)) (mem_unlock Ω m)
  | cstep_switch_indet m k e Ω vb s :
     ¬base_val_branchable m vb →
     Γ\ δ ⊢ₛ State (CExpr e (switch{□} s) :: k) (Expr (#{Ω} VBase vb)) m ⇒
             State k (Undef (UndefBranch (switch{□} s) Ω (VBase vb))) m

  (**i For compound statements: *)
  | cstep_in_comp m k s1 s2 :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (s1 ;; s2)) m ⇒
             State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m
  | cstep_out_comp1 m k s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (□ ;; s2) :: k) (Stmt ↗ s1) m ⇒
             State (CStmt (s1 ;; □) :: k) (Stmt ↘ s2) m
  | cstep_out_comp2 m k s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (s1 ;; □) :: k) (Stmt ↗ s2) m ⇒
             State k (Stmt ↗ (s1 ;; s2)) m
  | cstep_in_catch m k s :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (catch s)) m ⇒
             State (CStmt (catch □) :: k) (Stmt ↘ s) m
  | cstep_out_catch m k s :
     Γ\ δ ⊢ₛ State (CStmt (catch □) :: k) (Stmt ↗ s) m ⇒
             State k (Stmt ↗ (catch s)) m
  | cstep_in_loop m k s :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (loop s)) m ⇒
             State (CStmt (loop □) :: k) (Stmt ↘ s) m
  | cstep_out_loop m k s :
     Γ\ δ ⊢ₛ State (CStmt (loop □) :: k) (Stmt ↗ s) m ⇒
             State k (Stmt ↘ (loop s)) m
  | cstep_out_if1 m k e s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (if{e} □ else s2) :: k) (Stmt ↗ s1) m ⇒
             State k (Stmt ↗ (if{e} s1 else s2)) m
  | cstep_out_if2 m k e s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (if{e} s1 else □) :: k) (Stmt ↗ s2) m ⇒
             State k (Stmt ↗ (if{e} s1 else s2)) m
  | cstep_out_switch m k e s :
     Γ\ δ ⊢ₛ State (CStmt (switch{e} □) :: k) (Stmt ↗ s) m ⇒
             State k (Stmt ↗ (switch{e} s)) m

  (**i For function calls *)
  | cstep_call m k f s os vs :
     δ !! f = Some s → Forall_fresh (dom indexset m) os →
     length os = length vs →
     Γ\ δ ⊢ₛ State k (Call f vs) m ⇒
             State (CParams f (zip os (type_of <$> vs)) :: k)
               (Stmt ↘ s) (mem_alloc_list Γ os vs m)
  | cstep_free_params m k f oτs s :
     Γ\ δ ⊢ₛ State (CParams f oτs :: k) (Stmt ↗ s) m ⇒
             State k (Return f voidV) (foldr mem_free m (oτs.*1))
  | cstep_free_params_top m k f oτs v s :
     Γ\ δ ⊢ₛ State (CParams f oτs :: k) (Stmt (⇈ v) s) m ⇒
             State k (Return f v) (foldr mem_free m (oτs.*1))
  | cstep_return m k f E v :
     Γ\ δ ⊢ₛ State (CFun E :: k) (Return f v) m ⇒
             State k (Expr (subst E (#v)%E)) m

  (**i For non-local control flow: *)
  | cstep_label_here m k l :
     Γ\ δ ⊢ₛ State k (Stmt (↷ l) (label l)) m ⇒
             State k (Stmt ↗ (label l)) m
  | cstep_throw_here m k s :
     Γ\ δ ⊢ₛ State (CStmt (catch □) :: k) (Stmt (↑ 0) s) m ⇒
             State k (Stmt ↗ (catch s)) m
  | cstep_throw_further m k s n :
     Γ\ δ ⊢ₛ State (CStmt (catch □) :: k) (Stmt (↑ (S n)) s) m ⇒
             State k (Stmt (↑ n) (catch s)) m
  | cstep_case_here m k mx :
     Γ\ δ ⊢ₛ State k (Stmt (↓ mx) (scase mx)) m ⇒
             State k (Stmt ↗ (scase mx)) m
  | cstep_goto_in m k Es l s :
     l ∈ labels s →
     Γ\ δ ⊢ₛ State k (Stmt (↷ l) (subst Es s)) m ⇒
             State (CStmt Es :: k) (Stmt (↷ l) s) m
  | cstep_switch_in m k Es mx s :
     maybe CSwitch Es = None → mx ∈ cases s →
     Γ\ δ ⊢ₛ State k (Stmt (↓ mx) (subst Es s)) m ⇒
             State (CStmt Es :: k) (Stmt (↓ mx) s) m
  | cstep_top_out m k Es v s :
     Γ\ δ ⊢ₛ State (CStmt Es :: k) (Stmt (⇈ v) s) m ⇒
             State k (Stmt (⇈ v) (subst Es s)) m
  | cstep_goto_out m k Es l s :
     l ∉ labels s →
     Γ\ δ ⊢ₛ State (CStmt Es :: k) (Stmt (↷ l) s) m ⇒
             State k (Stmt (↷ l) (subst Es s)) m
  | cstep_throw_out m k Es n s :
     Es ≠ catch □ →
     Γ\ δ ⊢ₛ State (CStmt Es :: k) (Stmt (↑ n) s) m ⇒
             State k (Stmt (↑ n) (subst Es s)) m

  (**i For block scopes: *)
  | cstep_in_block m k d o τ s :
     direction_in d s → o ∉ dom indexset m →
     Γ\ δ ⊢ₛ State k (Stmt d (local{τ} s)) m ⇒
             State (CLocal o τ :: k) (Stmt d s)
               (mem_alloc Γ o false perm_full (val_new Γ τ) m)
  | cstep_out_block m k d o τ s :
     direction_out d s →
     Γ\ δ ⊢ₛ State (CLocal o τ :: k) (Stmt d s) m ⇒
             State k (Stmt d (local{τ} s)) (mem_free o m)
where "Γ \ δ  ⊢ₛ S1 ⇒ S2" := (@cstep _ _ Γ δ S1%S S2%S) : C_scope.

(** The reflexive transitive closure. *)
Notation "Γ \ δ ⊢ₛ S1 ⇒* S2" := (rtc (cstep Γ δ) S1 S2)
  (at level 74, δ at next level,
   format "Γ \  δ  ⊢ₛ '['  S1  '⇒*' '/'  S2 ']'") : C_scope.

(** * Inversion tactics *)
Ltac inv_assign_sem :=
  match goal with
  | H : assign_sem _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  end.
Ltac inv_ehstep :=
  match goal with
  | H : _ \ _ ⊢ₕ _, _ ⇒ _, _ |- _ => inversion H; subst; clear H
  end.

(** * Step tactics *)
Global Hint Constructors assign_sem ehstep ehsafe cstep : cstep.
Ltac do_ehstep :=
  match goal with
  | |- _ \ _ ⊢ₕ _, _ ⇒ _, _ => solve [constructor; eauto with cstep]
  | |- _ \ _ ⊢ₕ _, _ ⇒ _, _ => solve [eauto with cstep]
  end.

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
  | ! ?e => constr:([subst (! □) e])
  | ret ?e => constr:([subst (ret □) e])
  | (?s1 ;; ?s2)%S => constr:([subst (s1 ;; □)%S s2; subst (□ ;; s2)%S s1])
  | loop ?s => constr:([subst (loop □) s])
  | catch ?s => constr:([subst (catch □) s])
  | if{?e} ?s1 else ?s2 =>
    constr:([subst (if{e} s1 else □) s2;
            subst (if{e} □ else s2) s1; subst (if{□} s1 else s2) e])
  | switch{?e} ?s => constr:([subst (switch{e} □) s; subst (switch{□} s) e])
  end.

(** The [quote_expr e] tactic yields a list of possible ways to write an
expression [e] as [subst E e'] where [E] is an expression evaluation context,
and [e'] an expression. This tactic may be seen as an [Ltac] variant of the
function [expr_redexes], but whereas [expr_redexes] only includes
subexpressions [e'] that are redexes, all subexpressions are included here. We
omit function calls for the moment. *)
Local Open Scope expr_scope.
Ltac ranks_of_expr e := match type of e with expr ?K => K end.
Ltac quote_expr e :=
  let K := ranks_of_expr e in
  let rec go2 k1 e1 k2 e2 :=
    let  q1 := go k1 e1
    with q2 := go k2 e2
    in constr:(q1 ++ q2)
  with go k e :=
    let q :=
    match e with
    | .* ?e => go (.* □ :: k) e
    | & ?e => go (& □ :: k) e
    | ?e1 ::=.{?ass} ?e2 =>
       go2 (□ ::={ass} e2 :: k) e1 (e1 ::=.{ass} □ :: k) e2
    | load ?e => go (load □ :: k) e
    | ?e %> ?i => go (□ %> i :: k) e
    | ?e #> ?i => go (□ #> i :: k) e
    | #[?r:=?e1] ?e2 => go2 (#[r:=□] e2 :: k) e1 (#[r:=e1] □ :: k) e2
    | free ?e => go (free □ :: k) e
    | alloc{?τ} ?e => go (alloc{τ} □ :: k) e
    | .{?op} ?e => go (.{op} □ :: k) e
    | ?e1 .{?op} ?e2 => go2 (□ .{op} e2 :: k) e1 (e1 .{op} □ :: k) e2
    | if{?e1} ?e2 else ?e3 => go (if{□} e2 else e3 :: k) e1
    | ?e1 ,, ?e2 => go (□ ,, e2 :: k) e1
    | _ => constr:(@nil (expr K))
    end in constr:(subst k e :: q)
  in go (@nil (ectx_item K)) e.
Local Close Scope expr_scope.

(** The [do_cstep] tactic is used to solve goals of the shape [δ ⊢ₛ S1 ⇒ S2] or
as [δ ⊢ₛ S1 ⇒{k} S2] by applying a matching reduction rule, or by using the
hint database [cstep]. *)
Ltac do_cstep :=
  let go := first
    [ solve [econstructor; intuition eauto with cstep]
    | solve [intuition eauto with cstep]] in
  match goal with
  | |- ?Γ\ ?δ ⊢ₛ State ?k (Stmt ?d ?s) ?m ⇒ ?S =>
     iter (fun s' => change (Γ\ δ ⊢ₛ State k (Stmt d s') m ⇒ S); go)
          (quote_stmt s)
  | |- ?Γ\ ?δ ⊢ₛ State ?k (Expr ?e) ?m ⇒ ?S =>
     iter (fun e' => change (Γ\ δ ⊢ₛ State k (Expr e') m ⇒ S); go)
          (quote_expr e)
  | _ => go
  end.

(** * Theorems *)
Section smallstep_properties.
Context `{Env K} (Γ : env K) (δ : funenv K).

Lemma ehstep_is_redex ρ e1 m1 v2 m2 : Γ\ ρ ⊢ₕ e1, m1 ⇒ v2, m2 → is_redex e1.
Proof. destruct 1; repeat constructor. Qed.
Lemma ehstep_val ρ Ω v1 m1 v2 m2 : ¬Γ \ ρ ⊢ₕ #{Ω} v1, m1 ⇒ v2, m2.
Proof. inversion 1. Qed.
Lemma ehstep_pure_pure ρ e1 m1 e2 m2 :
  Γ \ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure e1 → is_pure e2.
Proof.
  intros p He1. pose proof (is_pure_locks _ He1) as HΩ.
  destruct p; inversion He1; simpl in *; rewrite ?HΩ; try constructor; auto.
Qed.
Lemma ehstep_pure_mem ρ e1 m1 e2 m2 :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure e1 → m1 = m2.
Proof.
  destruct 1; inversion 1; subst;
    repeat match goal with
    | H : is_pure (%#{_} _) |- _ =>
      apply is_pure_locks in H; simpl in H; rewrite H
    end; auto using mem_unlock_empty.
Qed.
Lemma ehstep_pure_locks ρ e1 m1 e2 m2 :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure e1 → locks e1 = locks e2.
Proof.
  destruct 1; auto; inversion 1; simpl;
    repeat match goal with
    | H : is_pure _ |- _ => apply is_pure_locks in H; simpl in H; rewrite H
    end; set_solver.
Qed.
Lemma ehstep_size ρ e1 m1 e2 m2 :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → size e2 < size e1.
Proof. destruct 1; simpl; lia. Qed.
Lemma ehstep_if_true_no_locks ρ m vb e2 e3 :
  base_val_branchable m vb → ¬base_val_is_0 vb →
  Γ\ ρ ⊢ₕ if{# (VBase vb)} e2 else e3, m ⇒ e2, m.
Proof. rewrite <-(mem_unlock_empty m) at 3. by constructor. Qed.
Lemma ehstep_if_false_no_locks ρ vb e2 e3 m :
  base_val_branchable m vb → base_val_is_0 vb →
  Γ\ ρ ⊢ₕ if{# (VBase vb)} e2 else e3, m ⇒ e3, m.
Proof. intros. rewrite <-(mem_unlock_empty m) at 2. by constructor. Qed.
Lemma ehstep_comma_no_locks ρ m ν e2 : Γ\ ρ ⊢ₕ %# ν ,, e2, m ⇒ e2, m.
Proof. rewrite <-(mem_unlock_empty m) at 2. by constructor. Qed.
Lemma ehstep_deterministic ρ e m e1 m1 e2 m2 :
  maybe2 EAlloc e = None →
  Γ\ ρ ⊢ₕ e, m ⇒ e1, m1 → Γ\ ρ ⊢ₕ e, m ⇒ e2, m2 → e1 = e2 ∧ m1 = m2.
Proof.
  destruct 2; inversion 1; simplify_option_eq;
    try match goal with
    | H1 : assign_sem _ _ _ _ _ _ _, H2 : assign_sem _ _ _ _ _ _ _ |- _ =>
       destruct (assign_sem_deterministic _ _ _ _ _ _ _ _ _ H1 H2); subst
    end; by auto.
Qed.

Lemma cnf_undef m k e : nf (cstep Γ δ) (State k (Undef e) m).
Proof. intros [? p]. by inversion_clear p. Qed.
Lemma cnf_undef_state S : is_undef_state S → nf (cstep Γ δ) S.
Proof.
  intros [??]; destruct S as [? [] ?]; simplify_equality'; auto using cnf_undef.
Qed.

(** ** Preservation of validity of labels *)
Fixpoint ctx_labels_valid (k : ctx K) : Prop :=
  match k with
  | [] => True
  | CFun _ :: k => gotos k ⊆ labels k ∧ ctx_labels_valid k
  | _ :: k => ctx_labels_valid k
  end.
Definition direction_gotos (d : direction K) : labelset :=
  match d with ↷ l => {[ l ]} | _ => ∅ end.
Definition state_labels_valid (S : state K) : Prop :=
  let (k,φ,m) := S in
  match φ with
  | Stmt d s => gotos s ∪ gotos k ⊆ labels s ∪ labels k ∧
     direction_gotos d ⊆ gotos s ∪ gotos k ∧ ctx_labels_valid k
  | Expr e => gotos k ⊆ labels k ∧ ctx_labels_valid k
  | Call _ _ => gotos k ⊆ labels k ∧ ctx_labels_valid k
  | _ => ctx_labels_valid k
  end.
Lemma cstep_gotos_labels S1 S2 :
  (∀ f s, δ !! f = Some s → gotos s ⊆ labels s) →
  Γ\ δ ⊢ₛ S1 ⇒ S2 → state_labels_valid S1 → state_labels_valid S2.
Proof.
  (* slow... *)
  destruct 2; simpl; repeat case_match; subst;
    rewrite ?esctx_item_subst_gotos, ?esctx_item_subst_labels,
      ?sctx_item_subst_gotos, ?sctx_item_subst_labels;
    rewrite ?(left_id_L ∅ (∪)), ?(assoc_L (∪));
    intuition idtac;
    try (apply subseteq_empty);
    try (by apply union_preserving; eauto);
    let l := fresh in apply elem_of_subseteq; intros l;
    repeat match goal with
    | H : _ ⊆ _ |- _ => apply elem_of_subseteq in H; specialize (H l); revert H
    end; set_solver.
Qed.
Lemma csteps_gotos_labels S1 S2 :
  (∀ f s, δ !! f = Some s → gotos s ⊆ labels s) →
  Γ\ δ ⊢ₛ S1 ⇒* S2 → state_labels_valid S1 → state_labels_valid S2.
Proof. induction 2; eauto using cstep_gotos_labels. Qed.
Lemma csteps_initial_gotos m1 m2 f vs k s l :
  (∀ f s, δ !! f = Some s → gotos s ⊆ labels s) →
  Γ\ δ ⊢ₛ initial_state m1 f vs ⇒* State k (Stmt (↷ l) s) m2 →
  l ∈ labels s ∪ labels k.
Proof.
  intros. destruct (csteps_gotos_labels (initial_state m1 f vs)
    (State k (Stmt (↷ l) s) m2)); set_solver.
Qed.

Fixpoint ctx_catches_valid (k : ctx K) : Prop :=
  match k with
  | [] => True
  | CExpr _ (if{□} s1 else s2) :: k =>
     throws_valid (ctx_catches k) s1 ∧
     throws_valid (ctx_catches k) s2 ∧ ctx_catches_valid k
  | CExpr _ (switch{□} s) :: k =>
     throws_valid (ctx_catches k) s ∧ ctx_catches_valid k
  | CStmt (□ ;; s | s ;; □ | if{_} □ else s | if{_} s else □) :: k =>
     throws_valid (ctx_catches k) s ∧ ctx_catches_valid k
  | _ :: k => ctx_catches_valid k
  end.
Definition direction_throws_valid (n : nat) (d : direction K) :=
  match d with ↑ i => i < n | _ => True end.
Definition state_throws_valid (S : state K) : Prop :=
  let (k,φ,m) := S in
  match φ with
  | Stmt d s => throws_valid (ctx_catches k) s ∧
      direction_throws_valid (ctx_catches k) d ∧ ctx_catches_valid k
  | _ => ctx_catches_valid k
  end.
Lemma cstep_throws S1 S2 :
  (∀ f s, δ !! f = Some s → throws_valid 0 s) →
  Γ\ δ ⊢ₛ S1 ⇒ S2 → state_throws_valid S1 → state_throws_valid S2.
Proof.
  destruct 2; repeat (case_match || simplify_equality');
    intuition eauto with lia.
Qed.
Lemma csteps_throws S1 S2 :
  (∀ f s, δ !! f = Some s → throws_valid 0 s) →
  Γ\ δ ⊢ₛ S1 ⇒* S2 → state_throws_valid S1 → state_throws_valid S2.
Proof. induction 2; eauto using cstep_throws. Qed.
Lemma csteps_initial_throws m1 m2 f vs k s n :
  (∀ f s, δ !! f = Some s → throws_valid 0 s) →
  Γ\ δ ⊢ₛ initial_state m1 f vs ⇒* State k (Stmt (↑ n) s) m2 →
  n < ctx_catches k.
Proof.
  intros. destruct (csteps_throws (initial_state m1 f vs)
    (State k (Stmt (↑ n) s) m2)); naive_solver.
Qed.

Definition state_switch_valid (S : state K) : Prop :=
  match SFoc S with Stmt (↓ mx) s => mx ∈ cases s | _ => True end.
Lemma cstep_switch S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒ S2 → state_switch_valid S1 → state_switch_valid S2.
Proof. by destruct 1. Qed.
Lemma csteps_switch S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒* S2 → state_switch_valid S1 → state_switch_valid S2.
Proof. induction 1; eauto using cstep_switch. Qed.
Lemma csteps_initial_switch m1 m2 f vs k s mx :
  Γ\ δ ⊢ₛ initial_state m1 f vs ⇒* State k (Stmt (↓ mx) s) m2 →
  mx ∈ cases s.
Proof. intros p. by apply (csteps_switch _ _ p). Qed.
End smallstep_properties.

Global Hint Resolve ehstep_if_true_no_locks ehstep_if_false_no_locks
  ehstep_comma_no_locks : cstep.
