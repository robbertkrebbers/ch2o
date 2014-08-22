(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** The small step reduction is a binary relation between execution states,
and computation is defined as the reflexive transitive closure of this
reduction relation. This file also defines tactics to automatically perform and
invert reduction steps. These tactics use the hint database [cstep] to solve
side-conditions. *)
Require Export state.

(** * Semantics of assignments *)
(** The judgment [assign_sem Γ m a v ass v' va'] describes the resulting value
[v'] of an assignment [%{Ω1} a ::={ass} #{Ω2} v], and the value [va'] that needs
to be stored at [a] in [m]. *)
Inductive assign_sem `{Env Ti} (Γ : env Ti) (m : mem Ti)
     (a : addr Ti) (v : val Ti) : assign → val Ti → val Ti → Prop :=
  | Assign_sem :
     val_cast_ok Γ ('{m}) (type_of a) v →
     let v' := val_cast (type_of a) v in assign_sem Γ m a v Assign v' v'
  | PreOp_sem op va :
     m !!{Γ} a = Some va → val_binop_ok Γ ('{m}) op va v →
     val_cast_ok Γ ('{m}) (type_of a) (val_binop Γ op va v) →
     let v' := val_cast (type_of a) (val_binop Γ op va v) in
     assign_sem Γ m a v (PreOp op) v' v'
  | PostOp_sem op va :
     m !!{Γ} a = Some va → val_binop_ok Γ ('{m}) op va v →
     val_cast_ok Γ ('{m}) (type_of a) (val_binop Γ op va v) →
     let v' := val_cast (type_of a) (val_binop Γ op va v) in
     assign_sem Γ m a v (PostOp op) va v'.

(** * Head reduction for expressions *)
(** We define head reduction for all redexes whose reduction is local (i.e.
does not change the current program context). Only function calls are non-local,
as they change to the call state, and store the current expression evaluation
context on the program context. These will be included in the whole reduction
relation [cstep].*)
(* The level is just below logical negation (whose level is 75). *)
Reserved Notation "Γ \ ρ ⊢ₕ e1 , m1 ⇒ e2 , m2"
  (at level 74, format "Γ \  ρ  '⊢ₕ' '['  e1 ,  m1  ⇒ '/'  e2 ,  m2 ']'").
Inductive ehstep `{Env Ti} (Γ : env Ti) (ρ : stack) :
     expr Ti → mem Ti → expr Ti → mem Ti → Prop :=
  | estep_var x τ o m :
     ρ !! x = Some o →
     Γ\ ρ ⊢ₕ var{τ} x, m ⇒ %(addr_top o τ), m
  | estep_rtol m Ω a :
     addr_strict Γ a →
     Γ\ ρ ⊢ₕ .* (#{Ω} (ptrV (Ptr a))), m ⇒ %{Ω} a, m
  | estep_rofl m Ω a :
     Γ\ ρ ⊢ₕ & (%{Ω} a), m ⇒ #{Ω} (ptrV (Ptr a)), m
  | estep_assign m ass Ω1 Ω2 a v v' va :
     mem_writable Γ a m → assign_sem Γ m a v ass v' va →
     Γ\ ρ ⊢ₕ %{Ω1} a ::={ass} #{Ω2} v, m ⇒
             #{lock_singleton Γ a ∪ Ω1 ∪ Ω2} v', mem_lock Γ a (<[a:=va]{Γ}>m)
  | estep_load m Ω a v :
     m !!{Γ} a = Some v → Γ\ ρ ⊢ₕ load (%{Ω} a), m ⇒ #{Ω} v, mem_force Γ a m
  | estep_eltl m Ω a rs :
     Γ\ ρ ⊢ₕ %{Ω} a %> rs, m ⇒ %{Ω} (addr_elt Γ rs a), m
  | estep_eltr m Ω v rs v' :
     v !! rs = Some v' → Γ\ ρ ⊢ₕ #{Ω} v #> rs, m ⇒ #{Ω} v', m
  | estep_alloc m Ω o τi τ n :
     mem_allocable o m → (0 < n)%Z → int_typed (n * size_of Γ τ) sptrT →
     Γ\ ρ ⊢ₕ alloc{τ} (#{Ω} (intV{τi} n)), m ⇒
             %{Ω} (addr_top_array o τ n), mem_alloc Γ o true (τ.[Z.to_nat n]) m
  | estep_free m Ω a :
     mem_freeable a m →
     Γ\ ρ ⊢ₕ free (%{Ω} a), m ⇒ #{Ω} voidV, mem_free (addr_index a) m
  | estep_unop op Ω v m :
     val_unop_ok ('{m}) op v →
     Γ\ ρ ⊢ₕ @{op} #{Ω} v, m ⇒ #{Ω} (val_unop op v), m
  | estep_binop op m Ω1 Ω2 v1 v2 :
     val_binop_ok Γ ('{m}) op v1 v2 →
     Γ\ ρ ⊢ₕ #{Ω1} v1 @{op} #{Ω2} v2, m ⇒ #{Ω1 ∪ Ω2} (val_binop Γ op v1 v2), m
  | estep_if_true m Ω v e1 e2 :
     val_true ('{m}) v →
     Γ\ ρ ⊢ₕ if{#{Ω} v} e1 else e2, m ⇒ e1, mem_unlock Ω m
  | estep_if_false m Ω v e1 e2 :
     val_false v →
     Γ\ ρ ⊢ₕ if{#{Ω} v} e1 else e2, m ⇒ e2, mem_unlock Ω m
  | estep_comma m Ω v e2 :
     Γ\ ρ ⊢ₕ #{Ω} v,,e2, m ⇒ e2, mem_unlock Ω m
  | estep_cast m τ Ω v :
     val_cast_ok Γ ('{m}) τ v →
     Γ\ ρ ⊢ₕ cast{τ} (#{Ω} v), m ⇒ #{Ω} (val_cast τ v), m
where "Γ \ ρ  ⊢ₕ e1 , m1 '⇒' e2 , m2" :=
  (@ehstep _ _ Γ ρ e1%E m1 e2%E m2) : C_scope.

(** An expression is safe if a head reduction step is possible. This relation
is adapted from CompCert and is used to capture undefined behavior. If the
whole expression contains a redex that is not safe, the semantics transitions
to the [Undef] state. *)
Reserved Notation "Γ \ ρ  '⊢ₕ' 'safe' e , m" (at level 74).
Inductive ehsafe `{Env Ti} (Γ : env Ti) (ρ : stack) : expr Ti → mem Ti → Prop :=
  | ehsafe_call f Ωs vs m :
     length Ωs = length vs → Γ \ ρ ⊢ₕ safe call f @ #{Ωs}* vs, m
  | ehsafe_step e1 m1 e2 m2 : Γ \ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → Γ \ ρ ⊢ₕ safe e1, m1
where "Γ \ ρ  ⊢ₕ 'safe' e ,  m" := (@ehsafe _ _ Γ ρ e m) : C_scope.

(** * The reduction relation *)
(** Small step reduction works by traversal of the focus. Each step the focus
is executed, after which a transition to the next program state is performed. *)
Reserved Notation "Γ \ δ ⊢ₛ S1 ⇒ S2"
  (at level 74, format "Γ \  δ  ⊢ₛ  '[' S1  ⇒ '/'  S2 ']'").
Inductive cstep `{Env Ti} (Γ : env Ti) (δ : funenv Ti) : relation (state Ti) :=
  (**i For simple statements: *)
  | cstep_in_skip m k :
     Γ\ δ ⊢ₛ State k (Stmt ↘ skip) m ⇒
             State k (Stmt ↗ skip) m
  | cstep_in_label m k l :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (label l)) m ⇒
             State k (Stmt ↗ (label l)) m
  | cstep_in_goto m k l :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (goto l)) m ⇒
             State k (Stmt (↷ l) (goto l)) m
  | cstep_in_expr m k E e :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (subst E e)) m ⇒
             State (CExpr e E :: k) (Expr e) m

  (**i For expressions: *)
  | cstep_expr_head m1 m2 k (E : ectx Ti) e1 e2 :
     Γ\ get_stack k ⊢ₕ e1, m1 ⇒ e2, m2 →
     Γ\ δ ⊢ₛ State k (Expr (subst E e1)) m1 ⇒
             State k (Expr (subst E e2)) m2
  | cstep_expr_call m k f E Ωs vs :
     length Ωs = length vs →
     Γ\ δ ⊢ₛ State k (Expr (subst E (call f @ #{Ωs}* vs))%E) m ⇒
             State (CFun E :: k) (Call f vs) (mem_unlock (⋃ Ωs) m)
  | cstep_expr_undef m k (E : ectx Ti) e :
     is_redex e → ¬Γ \ get_stack k ⊢ₕ safe e, m →
     Γ\ δ ⊢ₛ State k (Expr (subst E e)) m ⇒
             State k (Undef (UndefExpr E e)) m

  (**i For finished expressions: *)
  | cstep_expr_do m k e Ω v :
     Γ\ δ ⊢ₛ State (CExpr e (! □) :: k) (Expr (#{Ω} v)) m ⇒
             State k (Stmt ↗ (! e)) (mem_unlock Ω m)
  | cstep_expr_ret m k e Ω v :
     Γ\ δ ⊢ₛ State (CExpr e (ret □) :: k) (Expr (#{Ω} v)) m ⇒
             State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m)
  | cstep_expr_while_true m k e Ω v s :
     val_true ('{m}) v →
     Γ\ δ ⊢ₛ State (CExpr e (while{□} s) :: k) (Expr (#{Ω} v)) m ⇒
             State (CStmt (while{e} □) :: k) (Stmt ↘ s) (mem_unlock Ω m)
  | cstep_expr_while_false m k e Ω v s :
     val_false v →
     Γ\ δ ⊢ₛ State (CExpr e (while{□} s) :: k) (Expr (#{Ω} v)) m ⇒
             State k (Stmt ↗ (while{e} s)) (mem_unlock Ω m)
  | cstep_expr_while_indet m k e Ω v s :
     ¬val_true ('{m}) v → ¬val_false v →
     Γ\ δ ⊢ₛ State (CExpr e (while{□} s) :: k) (Expr (#{Ω} v)) m ⇒
             State k (Undef (UndefBranch e (while{□} s) Ω v)) m
  | cstep_expr_if_true m k e Ω v s1 s2 :
     val_true ('{m}) v →
     Γ\ δ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} v)) m ⇒
             State (CStmt (if{e} □ else s2) :: k) (Stmt ↘ s1) (mem_unlock Ω m)
  | cstep_expr_if_false m k e Ω v s1 s2 :
     val_false v →
     Γ\ δ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} v)) m ⇒
             State (CStmt (if{e} s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m)
  | cstep_expr_if_indet m k e Ω v s1 s2 :
     ¬val_true ('{m}) v → ¬val_false v →
     Γ\ δ ⊢ₛ State (CExpr e (if{□} s1 else s2) :: k) (Expr (#{Ω} v)) m ⇒
             State k (Undef (UndefBranch e (if{□} s1 else s2) Ω v)) m

  (**i For compound statements: *)
  | cstep_in_block m k o τ s :
     mem_allocable o m →
     Γ\ δ ⊢ₛ State k (Stmt ↘ (blk{τ} s)) m ⇒
             State (CBlock o τ :: k) (Stmt ↘ s) (mem_alloc Γ o false τ m)
  | cstep_in_comp m k s1 s2 :
     Γ\ δ ⊢ₛ State k (Stmt ↘ (s1 ;; s2)) m ⇒
             State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m
  | cstep_out_block m k o τ s :
     Γ\ δ ⊢ₛ State (CBlock o τ :: k) (Stmt ↗ s) m ⇒
             State k (Stmt ↗ (blk{τ} s)) (mem_free o m)
  | cstep_out_comp1 m k s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (□ ;; s2) :: k) (Stmt ↗ s1) m ⇒
             State (CStmt (s1 ;; □) :: k) (Stmt ↘ s2) m
  | cstep_out_comp2 m k s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (s1 ;; □) :: k) (Stmt ↗ s2) m ⇒
             State k (Stmt ↗ (s1 ;; s2)) m
  | cstep_out_loop m k e s :
     Γ\ δ ⊢ₛ State (CStmt (while{e} □) :: k) (Stmt ↗ s) m ⇒
             State k (Stmt ↘ (while{e} s)) m
  | cstep_out_if1 m k e s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (if{e} □ else s2) :: k) (Stmt ↗ s1) m ⇒
             State k (Stmt ↗ (if{e} s1 else s2)) m
  | cstep_out_if2 m k e s1 s2 :
     Γ\ δ ⊢ₛ State (CStmt (if{e} s1 else □) :: k) (Stmt ↗ s2) m ⇒
             State k (Stmt ↗ (if{e} s1 else s2)) m

  (**i For function calls *)
  | cstep_call m k f s os vs :
     δ !! f = Some s → mem_allocable_list m os → length os = length vs →
     Γ\ δ ⊢ₛ State k (Call f vs) m ⇒
             State (CParams (zip os (type_of <$> vs)) :: k)
               (Stmt ↘ s) (mem_alloc_val_list Γ (zip os vs) m)
  | cstep_free_params m k oτs s :
     Γ\ δ ⊢ₛ State (CParams oτs :: k) (Stmt ↗ s) m ⇒
             State k (Return voidV) (foldr mem_free m (fst <$> oτs))
  | cstep_free_params_top m k oτs v s :
     Γ\ δ ⊢ₛ State (CParams oτs :: k) (Stmt (⇈ v) s) m ⇒
             State k (Return v) (foldr mem_free m (fst <$> oτs))
  | cstep_return m k E v :
     Γ\ δ ⊢ₛ State (CFun E :: k) (Return v) m ⇒
             State k (Expr (subst E (#v)%E)) m

  (**i For non-local control flow: *)
  | cstep_top_block m k o τ v s :
     Γ\ δ ⊢ₛ State (CBlock o τ :: k) (Stmt (⇈ v) s) m ⇒
             State k (Stmt (⇈ v) (blk{τ} s)) (mem_free o m)
  | cstep_top_item m k E v s :
     Γ\ δ ⊢ₛ State (CStmt E :: k) (Stmt (⇈ v) s) m ⇒
             State k (Stmt (⇈ v) (subst E s)) m
  | cstep_label_here m k l :
     Γ\ δ ⊢ₛ State k (Stmt (↷ l) (label l)) m ⇒
             State k (Stmt ↗ (label l)) m
  | cstep_label_block_down m k l o τ s :
     l ∈ labels s → mem_allocable o m →
     Γ\ δ ⊢ₛ State k (Stmt (↷ l) (blk{τ} s)) m ⇒
             State (CBlock o τ :: k) (Stmt (↷ l) s) (mem_alloc Γ o false τ m)
  | cstep_label_block_up m k l o τ s : 
     (**i Not [l ∈ labels k] so as to avoid it going back and forth between 
     double occurrences of labels. *)
     l ∉ labels s →
     Γ\ δ ⊢ₛ State (CBlock o τ :: k) (Stmt (↷ l) s) m ⇒
             State k (Stmt (↷l) (blk{τ} s)) (mem_free o m)
  | cstep_label_down m k Es l s :
     l ∈ labels s →
     Γ\ δ ⊢ₛ State k (Stmt (↷ l) (subst Es s)) m ⇒
             State (CStmt Es :: k) (Stmt (↷ l) s) m
  | cstep_label_up m k Es l s :
     l ∉ labels s →
     Γ\ δ ⊢ₛ State (CStmt Es :: k) (Stmt (↷ l) s) m ⇒
             State k (Stmt (↷ l) (subst Es s)) m
where "Γ \ δ  ⊢ₛ S1 ⇒ S2" := (@cstep _ _ Γ δ S1%S S2%S) : C_scope.

Definition initial_state {Ti} (m : mem Ti)
  (f : funname) (vs : list (val Ti)) : state Ti := State [] (Call f vs) m.
Inductive final_state {Ti} (v : val Ti) : state Ti → Prop :=
  | Return_final m : final_state v (State [] (Return v) m).
Inductive undef_state {Ti} : state Ti → Prop :=
  | Undef_undef k Su m : undef_state (State k (Undef Su) m).

(** The reflexive transitive closure. *)
Notation "Γ \ δ ⊢ₛ S1 ⇒* S2" := (rtc (cstep Γ δ) S1 S2)
  (at level 74, format "Γ \  δ  ⊢ₛ '['  S1  '⇒*' '/'  S2 ']'") : C_scope.
(** Reduction paths of bounded length. *)
Notation "Γ \ δ ⊢ₛ S1 ⇒^ n S2" := (bsteps (cstep Γ δ) n S1 S2)
  (at level 74, n at level 1,
   format "Γ \  δ  ⊢ₛ '['  S1  '⇒^' n '/'  S2 ']'") : C_scope.

(** * Restricting small step reduction *)
(** To give a model of our axiomatic semantics (see the file [axiomatic]) we
need to restrict the traversal through the program context to remain below a
certain context. *)
Definition cstep_in_ctx `{Env Ti} Γ δ k : relation (state Ti) := λ S1 S2,
  Γ \ δ ⊢ₛ S1 ⇒ S2 ∧ k `suffix_of` SCtx S2.
Notation "Γ \ δ ⊢ₛ S1 ⇒{ k } S2" := (cstep_in_ctx Γ δ k S1 S2)
  (at level 74,
   format "Γ \  δ  ⊢ₛ '['  S1  '/' '⇒{' k '}' '/'  S2 ']'") : C_scope.
Notation "Γ \ δ ⊢ₛ S1 ⇒{ k }* S2" := (rtc (cstep_in_ctx Γ δ k) S1 S2)
  (at level 74,
   format "Γ \  δ  ⊢ₛ '['  S1  '/' '⇒{' k '}*' '/'  S2 ']'") : C_scope.
Notation "Γ \ δ ⊢ₛ S1 ⇒{ k }^ n S2" := (bsteps (cstep_in_ctx Γ δ k) n S1 S2)
  (at level 74, n at level 1,
   format "Γ \ δ  ⊢ₛ '['  S1  '/' '⇒{' k '}^' n '/'  S2 ']'") : C_scope.

(** * Inversions *)
(** Coq's [inversion] tactic is rather slow for large inductive types (as our
[cstep]). We therefore define some special purpose inversion schemes. The way
of defining these schemes is based on small inversions (Monin, 2010). *)
Section inversion.
  Context `{Env Ti} (Γ : env Ti) (δ : funenv Ti).

  Lemma cstep_focus_inv (P : state Ti → Prop) S1 S2 :
    Γ\ δ ⊢ₛ S1 ⇒ S2 →
    let 'State k φ m := S1 in
    match φ with
    | Stmt ↘ skip =>
       P (State k (Stmt ↗ skip) m) → P S2
    | Stmt ↘ (label l) =>
       P (State k (Stmt ↗ (label l)) m) → P S2
    | Stmt ↘ (goto l) =>
       P (State k (Stmt (↷ l) (goto l)) m) → P S2
    | Stmt ↘ (! e) =>
       P (State (CExpr e (! □) :: k) (Expr e) m) → P S2
    | Stmt ↘ (ret e) =>
       P (State (CExpr e (ret □) :: k) (Expr e) m) → P S2
    | Stmt ↘ (while{e} s) => 
       P (State (CExpr e (while{□} s) :: k) (Expr e) m) → P S2
    | Stmt ↘ (if{e} s1 else s2) =>
       P (State (CExpr e (if{□} s1 else s2) :: k) (Expr e) m) → P S2
    | Expr e =>
       (∀ Ω v k' e',
         e = (#{Ω} v)%E → k = CExpr e' (! □) :: k' →
         P (State k' (Stmt ↗ (! e')) (mem_unlock Ω m))) →
       (∀ Ω v k' e',
         e = (#{Ω} v)%E → k = CExpr e' (ret □) :: k' →
         P (State k' (Stmt (⇈ v) (ret e')) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s,
         e = (#{Ω} v)%E → val_true ('{m}) v →
         k = CExpr e' (while{□} s) :: k' →
         P (State (CStmt (while{e'} □) :: k')
           (Stmt ↘ s) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s,
         e = (#{Ω} v)%E → val_false v → k = CExpr e' (while{□} s) :: k' →
         P (State k' (Stmt ↗ (while{e'} s)) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s,
         e = (#{Ω} v)%E → ¬val_true ('{m}) v → ¬val_false v →
         k = CExpr e' (while{□} s) :: k' →
         P (State k' (Undef (UndefBranch e' (while{□} s) Ω v)) m)) →
       (∀ Ω v k' e' s1 s2,
         e = (#{Ω} v)%E → val_true ('{m}) v →
         k = CExpr e' (if{□} s1 else s2) :: k' →
         P (State (CStmt (if{e'} □ else s2) :: k')
           (Stmt ↘ s1) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s1 s2,
         e = (#{Ω} v)%E → val_false v →
         k = CExpr e' (if{□} s1 else s2) :: k' →
         P (State (CStmt (if{e'} s1 else □) :: k')
           (Stmt ↘ s2) (mem_unlock Ω m))) →
       (∀ Ω v k' e' s1 s2,
         e = (#{Ω} v)%E → ¬val_true ('{m}) v → ¬val_false v →
         k = CExpr e' (if{□} s1 else s2) :: k' →
         P (State k' (Undef (UndefBranch e' (if{□} s1 else s2) Ω v)) m)) →
       (∀ (E : ectx Ti) e1 e2 m2,
         e = subst E e1 → Γ\ get_stack k ⊢ₕ e1, m ⇒ e2, m2 →
         P (State k (Expr (subst E e2)) m2)) →
       (∀ (E : ectx Ti) f Ωs vs,
         e = subst E (call f @ #{Ωs}* vs)%E → length Ωs = length vs →
         P (State (CFun E :: k)
           (Call f vs) (mem_unlock (⋃ Ωs) m))) →
       (∀ (E : ectx Ti) e1,
         e = subst E e1 → is_redex e1 → ¬Γ\ get_stack k ⊢ₕ safe e1, m →
         P (State k (Undef (UndefExpr E e1)) m)) →
       P S2
    | Return v =>
       (∀ k' E,
         k = CFun E :: k' →
         P (State k' (Expr (subst E (#v)%E)) m)) →
       P S2
    | Stmt ↘ (blk{τ} s) =>
       (∀ o,
         mem_allocable o m →
         P (State (CBlock o τ :: k) (Stmt ↘ s)
           (mem_alloc Γ o false τ m))) →
       P S2
    | Stmt ↘ (s1 ;; s2) =>
       P (State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m) → P S2
    | Stmt ↗ s =>
       (∀ k' o τ,
         k = CBlock o τ :: k' →
         P (State k' (Stmt ↗ (blk{τ} s)) (mem_free o m))) →
       (∀ k' s2,
         k = CStmt (□ ;; s2) :: k' →
         P (State (CStmt (s ;; □) :: k') (Stmt ↘ s2) m)) →
       (∀ k' s1,
         k = CStmt (s1 ;; □) :: k' →
         P (State k' (Stmt ↗ (s1 ;; s)) m)) →
       (∀ k' e,
         k = CStmt (while{e} □) :: k' →
         P (State k' (Stmt ↘ (while{e} s)) m)) →
       (∀ k' e s2,
         k = CStmt (if{e} □ else s2) :: k' →
         P (State k' (Stmt ↗ (if{e} s else s2)) m)) →
       (∀ k' e s1,
         k = CStmt (if{e} s1 else □) :: k' →
         P (State k' (Stmt ↗ (if{e} s1 else s)) m)) →
       (∀ k' oτs,
         k = CParams oτs :: k' →
         P (State k' (Return voidV) (foldr mem_free m (fst <$> oτs)))) →
       P S2
    | Call f vs =>
       (∀ s os,
         δ !! f = Some s → mem_allocable_list m os → length os = length vs →
         P (State (CParams (zip os (type_of <$> vs)) :: k)
           (Stmt ↘ s) (mem_alloc_val_list Γ (zip os vs) m))) →
       P S2
    | Stmt (⇈ v) s =>
       (∀ k' oτs,
         k = CParams oτs :: k' →
         P (State k' (Return v) (foldr mem_free m (fst <$> oτs)))) →
       (∀ k' o τ,
         k = CBlock o τ :: k' →
         P (State k' (Stmt (⇈ v) (blk{τ} s)) (mem_free o m))) →
       (∀ k' Es,
         k = CStmt Es :: k' →
         P (State k' (Stmt (⇈ v) (subst Es s)) m)) →
       P S2
    | Stmt (↷ l) s =>
       (s = label l → P (State k (Stmt ↗ s) m)) →
       (∀ s' o τ,
         s = blk{τ} s' → l ∈ labels s → mem_allocable o m →
         P (State (CBlock o τ :: k) (Stmt (↷ l) s')
           (mem_alloc Γ o false τ m))) →
       (∀ k' o τ,
         k = CBlock o τ :: k' → l ∉ labels s →
         P (State k' (Stmt (↷l) (blk{τ} s)) (mem_free o m))) →
       (∀ s' Es,
         s = subst Es s' → l ∈ labels s' →
         P (State (CStmt Es :: k) (Stmt (↷ l) s') m)) →
       (∀ k' Es,
         k = CStmt Es :: k' → l ∉ labels s →
         P (State k' (Stmt (↷ l) (subst Es s)) m)) →
       P S2
    | Undef _ => P S2
    end.
  Proof. intros p. case p; eauto 2. intros ?? [] ?; simpl; eauto. Qed.
  Lemma cstep_expr_inv (P : state Ti → Prop) m k Ek Ω v S2 :
    Γ\ δ ⊢ₛ State (Ek :: k) (Expr (#{Ω} v)) m ⇒ S2 →
    match Ek with
    | CExpr e (! □) =>
       P (State k (Stmt ↗ (! e)) (mem_unlock Ω m)) → P S2
    | CExpr e (ret □) =>
       P (State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m)) → P S2
    | CExpr e (while{□} s) =>
      (val_true ('{m}) v →
        P (State (CStmt (while{e} □) :: k) (Stmt ↘ s) (mem_unlock Ω m))) →
      (val_false v →
        P (State k (Stmt ↗ (while{e} s)) (mem_unlock Ω m))) →
      (¬val_true ('{m}) v → ¬val_false v →
        P (State k (Undef (UndefBranch e (while{□} s) Ω v)) m)) → P S2
    | CExpr e (if{□} s1 else s2) =>
      (val_true ('{m}) v →
        P (State (CStmt (if{e} □ else s2) :: k) (Stmt ↘ s1) (mem_unlock Ω m))) →
      (val_false v →
        P (State (CStmt (if{e} s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m))) →
      (¬val_true ('{m}) v → ¬val_false v →
        P (State k (Undef (UndefBranch e (if{□} s1 else s2) Ω v)) m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2.
    apply (cstep_focus_inv _ _ _ p);
      try solve [intros; simplify_equality; eauto].
    * intros Ee e1 e2 m2 Hv p'. simplify_list_subst_equality Hv. inversion p'.
    * intros Ee f Ωs vs Hv. simplify_list_subst_equality Hv.
    * intros Ee e1 Hv ? _. simplify_list_subst_equality Hv.
      by destruct (EVal_not_redex Ω v).
  Qed.
  Lemma cstep_stmt_up_inv (P : state Ti → Prop) m k Ek s S2 :
    Γ\ δ ⊢ₛ State (Ek :: k) (Stmt ↗ s) m ⇒ S2 →
    match Ek with
    | CStmt (□ ;; s2) => P (State (CStmt (s ;; □) :: k) (Stmt ↘ s2) m) → P S2
    | CStmt (s1 ;; □) => P (State k (Stmt ↗ (s1 ;; s)) m) → P S2
    | CStmt (while{e} □) => P (State k (Stmt ↘ (while{e} s)) m) → P S2
    | CStmt (if{e} □ else s2) => P (State k (Stmt ↗ (if{e} s else s2)) m) → P S2
    | CStmt (if{e} s1 else □) => P (State k (Stmt ↗ (if{e} s1 else s)) m) → P S2
    | CBlock o τ => P (State k (Stmt ↗ (blk{τ} s)) (mem_free o m)) → P S2
    | CParams oτs =>
       P (State k (Return voidV) (foldr mem_free m (fst <$> oτs))) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2. apply (cstep_focus_inv _ _ _ p);
      intros; simplify_equality; eauto.
  Qed.
  Lemma cstep_stmt_top_inv (P : state Ti → Prop) m k Ek v s S2 :
    Γ\ δ ⊢ₛ State (Ek :: k) (Stmt (⇈ v) s) m ⇒ S2 →
    match Ek with
    | CStmt Es => P (State k (Stmt (⇈ v) (subst Es s)) m) → P S2
    | CParams oτs =>
       P (State k (Return v) (foldr mem_free m (fst <$> oτs))) → P S2
    | CBlock o τ => P (State k (Stmt (⇈ v) (blk{τ} s)) (mem_free o m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p. pattern S2.
    apply (cstep_focus_inv _ _ _ p); intros; simplify_equality; eauto.
  Qed.
  Lemma cstep_stmt_jump_down_inv (P : state Ti → Prop) m k l s S2 :
    Γ\ δ ⊢ₛ State k (Stmt (↷ l) s) m ⇒ S2 →
    l ∈ labels s →
    match s with
    | label l' => (l = l' → P (State k (Stmt ↗ s) m)) → P S2
    | blk{τ} s =>
       (∀ o, mem_allocable o m → l ∈ labels s →
         P (State (CBlock o τ :: k) (Stmt (↷ l) s) (mem_alloc Γ o false τ m))) →
       P S2
    | s1 ;; s2 =>
       (l ∈ labels s1 → P (State (CStmt (□ ;; s2) :: k) (Stmt (↷ l) s1) m)) →
       (l ∈ labels s2 → P (State (CStmt (s1 ;; □) :: k) (Stmt (↷ l) s2) m)) →
       P S2
    | while{e} s =>
       (l ∈ labels s → P (State (CStmt (while{e} □) :: k) (Stmt (↷ l) s) m)) →
       P S2
    | if{e} s1 else s2 =>
       (l ∈ labels s1 →
         P (State (CStmt (if{e} □ else s2) :: k) (Stmt (↷ l) s1) m)) →
       (l ∈ labels s2 →
         P (State (CStmt (if{e} s1 else □) :: k) (Stmt (↷ l) s2) m)) →
       P S2
    | _ => P S2
    end.
  Proof.
    intros p ?. pattern S2. apply (cstep_focus_inv _ _ _ p); try solve_elem_of.
    intros ? []; solve_elem_of.
  Qed.
  Lemma cstep_stmt_jump_up_inv (P : state Ti → Prop) m k Ek l s S2 :
    Γ\ δ ⊢ₛ State (Ek :: k) (Stmt (↷ l) s) m ⇒ S2 →
    l ∉ labels s →
    match Ek with
    | CStmt Es => P (State k (Stmt (↷ l) (subst Es s)) m) → P S2
    | CBlock o τ => P (State k (Stmt (↷ l) (blk{τ} s)) (mem_free o m)) → P S2
    | _ => P S2
    end.
  Proof.
    intros p ?. pattern S2. apply (cstep_focus_inv _ _ _ p);
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
  | _\ _ ⊢ₛ _ ⇒ ?S2 =>
    is_var S2;
    block_goal;
    repeat match goal with
    | H' : context [ S2 ] |- _ => var_neq H H'; revert H'
    end;
    pattern S2; first
    [ apply (cstep_expr_inv _ _ _ _ _ _ _ _ _ H)
    | apply (cstep_stmt_up_inv _ _ _ _ _ _ _ _  H)
    | apply (cstep_stmt_top_inv _ _ _ _ _ _ _ _ _ H)
    | first_of
        ltac:(apply (cstep_stmt_jump_down_inv _ _ _ _ _ _ _ _ H))
        assumption
        idtac
    | first_of
        ltac:(apply (cstep_stmt_jump_up_inv _ _ _ _ _ _ _ _ _ H))
        assumption
        idtac
    | apply (cstep_focus_inv _ _ _ _ _ H)];
    clear H; intros; unblock_goal
  end.
(** Some reduction are not of a shape that fits any of the previously defined
inversion schemes. The tactic [slow_inv_cstep] inverts a reduction using Coq's
standard [inversion] tactic and works for reductions of all shapes. *)
Ltac slow_inv_cstep H :=
  match type of H with _\ _ ⊢ₛ ?S1 ⇒ ?S2 => inversion H; clear H end.

Ltac inv_assign_sem :=
  match goal with
  | H : assign_sem _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
  end.
Ltac inv_ehstep :=
  match goal with
  | H : _ \ _ ⊢ₕ _, _ ⇒ _, _ |- _ => inversion H; subst; clear H
  end.

(** The tactic [inv_cstep] inverts a reduction step and performs some clean up
and discharges impossible cases afterwards. *)
Tactic Notation "inv_cstep" hyp(H) :=
  try match type of H with
  | _\ _ ⊢ₛ _ ⇒{_} _ => destruct H as [H ?]
  end;
  match type of H with
  | _\ _ ⊢ₛ ?S1 ⇒ ?S2 =>
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
    | _ : val_true ?m ?v, _ : val_false ?v |- _ =>
       by destruct (val_true_false m v)
    | H : suffix_of _ _ |- _ => progress (simpl in H; simplify_suffix_of)
    | H : _\ _ ⊢ₕ #{_} _, _ ⇒ _, _ |- _ => by inversion H
    | H : _\ _ ⊢ₕ %{_} _, _ ⇒ _, _ |- _ => by inversion H
    | H : is_redex (#{_} _) |- _ => inversion H
    | H : is_redex (%{_} _) |- _ => inversion H
    end
  end.
Tactic Notation "inv_cstep" :=
  match goal with
  | H : _\ _ ⊢ₛ _ ⇒ _ |- _ => inv_cstep H
  | H : _\ _ ⊢ₛ _ ⇒{_} _ |- _ => inv_cstep H
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

(** * Step tactics *)
Hint Constructors assign_sem ehstep ehsafe cstep : cstep.
Ltac do_ehstep :=
  match goal with
  | |- _ \ _ ⊢ₕ _, _ ⇒ _, _ => constructor (solve [eauto with cstep])
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
  | ! ?e => constr:[subst (! □) e]
  | ret ?e => constr:[subst (ret □) e]
  | ?s1 ;; ?s2 => constr:[subst (s1 ;; □) s2; subst (□ ;; s2) s1]
  | while{?e} ?s =>
    constr:[subst (while{e} □) s; subst (while{□} s) e]
  | if{?e} ?s1 else ?s2 =>
    constr:[subst (if{e} s1 else □) s2;
            subst (if{e} □ else s2) s1; subst (if{□} s1 else s2) e]
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
    | .* ?e => go (.* □ :: k) e
    | & ?e => go (& □ :: k) e
    | ?e1 ::=@{?ass} ?e2 =>
       go2 (□ ::={ass} e2 :: k) e1 (e1 ::=@{ass} □ :: k) e2
    | load ?e => go (load □ :: k) e
    | ?e %> ?i => go (□ %> i :: k) e
    | ?e #> ?i => go (□ #> i :: k) e
    | free ?e => go (free □ :: k) e
    | alloc{?τ} ?e => go (alloc{τ} □ :: k) e
    | @{?op} ?e => go (@{op} □ :: k) e
    | ?e1 @{?op} ?e2 => go2 (□ @{op} e2 :: k) e1 (e1 @{op} □ :: k) e2
    | if{?e1} ?e2 else ?e3 => go (if{□} e2 else e3 :: k) e1
    | ?e1 ,, ?e2 => go (□ ,, e2 :: k) e1
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
    | |- ?Γ\ ?δ ⊢ₛ State ?k (Stmt ?d ?s) ?m ⇒ ?S => iter
      (fun s' => change (Γ\ δ ⊢ₛ State k (Stmt d s') m ⇒ S); go1)
      (quote_stmt s)
    | |- ?Γ\ ?δ ⊢ₛ State ?k (Expr ?e) ?m ⇒ ?S => iter
      (fun e' => change (Γ\ δ ⊢ₛ State k (Expr e') m ⇒ S); go1)
      (quote_expr e)
    | _ => go1
  end in
  simpl;
  match goal with
  | |- _\ _ ⊢ₛ _ ⇒{_} _ => first
    [ split; [go2 | simpl; solve_suffix_of]
    | solve [intuition eauto with cstep]]
  | |- _\ _ ⊢ₛ _ ⇒ _ => go2
  end.

Ltac do_csteps :=
  match goal with
  | |- _\ _ ⊢ₛ _ ⇒* _ => apply rtc_refl
  | |- _\ _ ⊢ₛ _ ⇒* _ => eapply rtc_l; [do_cstep | do_csteps]
  | |- _\ _ ⊢ₛ _ ⇒{_}* _ => apply rtc_refl
  | |- _\ _ ⊢ₛ _ ⇒{_}* _ => eapply rtc_l; [do_cstep | do_csteps]
  | |- _\ _ ⊢ₛ _ ⇒^_ _ => apply bsteps_refl
  | |- _\ _ ⊢ₛ _ ⇒^(S _) _ => eapply bsteps_l; [do_cstep | do_csteps]
  | |- _\ _ ⊢ₛ _ ⇒{_}^(S _) _ => apply bsteps_S; do_csteps
  | |- _\ _ ⊢ₛ _ ⇒{_}^_ _ => apply bsteps_refl
  | |- _\ _ ⊢ₛ _ ⇒{_}^(S _) _ => eapply bsteps_l; [do_cstep | do_csteps]
  | |- _\ _ ⊢ₛ _ ⇒{_}^(S _) _ => apply bsteps_S; do_csteps
  | |- _ => solve [intuition eauto with cstep]
  end.

(** The [solve_cred] tactic solves goals of the shape [red (δ⇒ₛ) S] and
[red (δ⇒ₛ{k}) S] by performing case distinctions on [S] and using the
[do_cstep] tactic to perform the actual step. *)
Ltac solve_cred :=
  repeat match goal with
  | H : down _ _ |- _ => progress simpl in H
  | H : up _ _ |- _ => progress simpl in H
  | |- red (cstep _ _) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; try contradiction
  | |- red (cstep_in_ctx _ _ _) (State _ (Stmt ?d _) _) =>
    is_var d; destruct d; try contradiction
  | H : ?l ∈ _ |- red (cstep _ _) (State _ (Stmt (↷ ?l) _) _) =>
    progress decompose_elem_of H
  | H : ?l ∈ _ |- red (cstep_in_ctx _ _ _) (State _ (Stmt (↷ ?l) _) _) =>
    progress decompose_elem_of H
  end;
  match goal with
  | H : red (cstep_in_ctx _ _ _) ?S |- red (cstep_in_ctx _ _ _) ?S =>
    by apply (red_subrel _ _ _ _ H)
  | |- red (cstep _ _) _ => eexists; do_cstep
  | |- red (cstep_in_ctx _ _ _) _ => eexists; do_cstep
  | |- _ => solve [intuition eauto with cstep]
  end.
Ltac solve_cnf :=
  lazymatch goal with
  | H : nf (cstep _ _) _ |- _ => destruct H; solve_cred
  | H : nf (cstep_in_ctx _ _ _) _ |- _ => destruct H; solve_cred
  end.

(** * Theorems *)
Section smallstep_properties.
Context `{Env Ti} (Γ : env Ti) (δ : funenv Ti).

Lemma ehstep_is_redex ρ e1 m1 v2 m2 : Γ\ ρ ⊢ₕ e1, m1 ⇒ v2, m2 → is_redex e1.
Proof. destruct 1; repeat constructor. Qed.
Lemma ehstep_val ρ Ω v1 m1 v2 m2 : ¬Γ \ ρ ⊢ₕ #{Ω} v1, m1 ⇒ v2, m2.
Proof. inversion 1. Qed.
Lemma ehstep_pure_pure fs ρ e1 m1 e2 m2 :
  Γ \ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure fs e1 → is_pure fs e2.
Proof.
  intros p He1. pose proof (is_pure_locks _ _ He1) as HΩ.
  destruct p; inversion He1; simpl in *; rewrite ?HΩ; try constructor; auto.
Qed.
Lemma ehstep_pure_mem fs ρ e1 m1 e2 m2 :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure fs e1 → m1 = m2.
Proof.
  destruct 1; inversion 1;
    repeat match goal with
    | H : is_pure _ (#{_} _) |- _ =>
      apply is_pure_locks in H; simpl in H; rewrite H
    end; auto using mem_unlock_empty.
Qed.
Lemma ehstep_pure_locks fs ρ e1 m1 e2 m2 :
  Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2 → is_pure fs e1 → locks e1 = locks e2.
Proof.
  destruct 1; auto; inversion 1; simpl;
    repeat match goal with
    | H : is_pure _ _ |- _ =>
      apply is_pure_locks in H; simpl in H; rewrite H
    end; solve_elem_of.
Qed.
Lemma estep_if_true_no_locks ρ m v e2 e3 :
  val_true ('{m}) v → Γ\ ρ ⊢ₕ if{# v} e2 else e3, m ⇒ e2, m.
Proof. rewrite <-(mem_unlock_empty m) at 3. by constructor. Qed.
Lemma estep_if_false_no_locks ρ v e2 e3 m :
  val_false v → Γ\ ρ ⊢ₕ if{# v} e2 else e3, m ⇒ e3, m.
Proof. rewrite <-(mem_unlock_empty m) at 2. by constructor. Qed.
Lemma estep_comma_no_locks ρ m v e2 : Γ\ ρ ⊢ₕ # v ,, e2, m ⇒ e2, m.
Proof. rewrite <-(mem_unlock_empty m) at 2. by constructor. Qed.

(** The small step semantics is non-deterministic when entering a block or
function scope as variables are given an arbitrary memory index. The following
lemmas, that are useful to automatically perform reduction steps, pick a fully
determined one. *)
Lemma estep_alloc_fresh ρ m Ω τ τi n :
  let o := fresh (dom indexset m) in
  (0 < n)%Z → int_typed (n * size_of Γ τ) sptrT →
  Γ\ ρ ⊢ₕ alloc{τ} (#{Ω} (intV{τi} n)), m ⇒
          %{Ω} (addr_top_array o τ n), mem_alloc Γ o true (τ.[Z.to_nat n]) m.
Proof. constructor; auto. eapply mem_allocable_alt, is_fresh. Qed.
Lemma cstep_in_block_fresh m k τ s :
  let o := fresh (dom indexset m) in
  Γ\ δ ⊢ₛ State k (Stmt ↘ (blk{τ} s)) m ⇒
          State (CBlock o τ :: k) (Stmt ↘ s) (mem_alloc Γ o false τ m).
Proof. constructor. eapply mem_allocable_alt, is_fresh. Qed.
Lemma cstep_label_block_down_fresh m k l τ s :
  l ∈ labels s →
  let o := fresh (dom indexset m) in
  Γ\ δ ⊢ₛ State k (Stmt (↷l) (blk{τ} s)) m ⇒
          State (CBlock o τ :: k) (Stmt (↷l) s) (mem_alloc Γ o false τ m).
Proof. constructor. done. eapply mem_allocable_alt, is_fresh. Qed.
Lemma cstep_call_fresh m k f s vs :
  δ !! f = Some s →
  let os := fresh_list (length vs) (dom indexset m) in
  Γ\ δ ⊢ₛ State k (Call f vs) m ⇒
          State (CParams (zip os (type_of <$> vs)) :: k)
            (Stmt ↘ s) (mem_alloc_val_list Γ (zip os vs) m).
Proof.
  constructor; auto using fresh_list_length.
  apply mem_allocable_list_alt; split; [apply fresh_list_nodup|].
  apply Forall_forall. intros o; simpl. rewrite mem_allocable_alt.
  apply fresh_list_is_fresh.
Qed.

Global Instance cstep_subrel_suffix_of δ k1 k2 :
  PropHolds (k1 `suffix_of` k2) →
  subrelation (cstep_in_ctx Γ δ k2) (cstep_in_ctx Γ δ k1).
Proof. intros ? S1 S2 [??]. split. done. by transitivity k2. Qed.
Global Instance cstep_subrel δ k : subrelation (cstep_in_ctx Γ δ k) (cstep Γ δ).
Proof. firstorder. Qed.
Global Instance cstep_subrel_nil δ :
  subrelation (cstep Γ δ) (cstep_in_ctx Γ δ []).
Proof. intros S1 S2 ?. split. done. solve_suffix_of. Qed.
Lemma cstep_in_ctx_rtc k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒{k}* S2 → k `suffix_of` SCtx S2 ∨ S1 = S2.
Proof.
  revert S1 S2. apply rtc_ind_r; [by right|]. intros ??? _ [??] _. by left.
Qed.
Lemma cstep_in_ctx_bsteps n k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒{k}^n S2 → k `suffix_of` SCtx S2 ∨ S1 = S2.
Proof. intros p. apply bsteps_rtc in p. eapply cstep_in_ctx_rtc; eauto. Qed.

Lemma cnf_undef m k e : nf (cstep Γ δ) (State k (Undef e) m).
Proof. intros [? p]. inv_cstep p. Qed.
Lemma cnf_in_ctx_undef m l k e : nf (cstep_in_ctx Γ δ l) (State k (Undef e) m).
Proof. apply (nf_subrel _ (cstep Γ δ) _), cnf_undef. Qed.
Lemma cnf_val m l Ω v : nf (cstep_in_ctx Γ δ l) (State l (Expr (#{Ω} v)) m).
Proof. intros [S p]; inv_cstep p. Qed.
Lemma cred_ectx (E : ectx Ti) k e m :
  red (cstep_in_ctx Γ δ k) (State k (Expr e) m) →
  red (cstep_in_ctx Γ δ k) (State k (Expr (subst E e)) m).
Proof. intros [S p]. inv_cstep p; rewrite <-subst_app; eexists; do_cstep. Qed.

Lemma cstep_expr_depsubst_inv {n} (P : state Ti → Prop)
    m k (E : ectx_full Ti n) (es : vec (expr Ti) n) S' :
  Γ\ δ ⊢ₛ State k (Expr (depsubst E es)) m ⇒{k} S' →
  (∀ i e' m', Γ\ δ ⊢ₛ State k (Expr (es !!! i)) m ⇒{k} State k (Expr e') m' →
    P (State k (Expr (depsubst E (vinsert i e' es))) m')) →
  (∀ i E' f Ωs vs, length Ωs = length vs →
    es !!! i = subst E' (call f @ #{Ωs}* vs)%E →
    Γ\ δ ⊢ₛ State k (Expr (es !!! i)) m ⇒{k}
            State (CFun E' :: k) (Call f vs) (mem_unlock (⋃ Ωs) m) →
    P (State (CFun (E' ++ [ectx_full_to_item E es i]) :: k)
      (Call f vs) (mem_unlock (⋃ Ωs) m))) →
  (Forall is_nf es → P S') →
  (∀ i E' e, es !!! i = subst E' e →
    Γ\ δ ⊢ₛ State k (Expr (es !!! i)) m ⇒{k}
            State k (Undef (UndefExpr E' e)) m →
    P (State k (Undef (UndefExpr (E' ++ [ectx_full_to_item E es i]) e)) m)) →
  P S'.
Proof.
  intros [p Hsuffix]. revert Hsuffix. pattern S'.
  apply (cstep_focus_inv _ _ _ _ _ p); simpl; try solve_suffix_of.
  * intros E' e1 e2 m2 HE pe _ HP1 _ HP3 _.
    destruct E' as [|E'' E' _] using rev_ind; simplify_equality'.
    { eapply HP3, is_redex_ectx_full, ehstep_is_redex; eauto. }
    rewrite !subst_snoc in HE |- *.
    apply ectx_full_item_subst in HE. destruct HE as [i [HE1 ->]].
    rewrite <-ectx_full_to_item_correct_alt. apply HP1. rewrite <-HE1. do_cstep.
  * intros E' f Ωs vs HE Hvs _ _ HP2 HP3 _.
    destruct E' as [|E'' E' _] using rev_ind.
    { destruct E; simplify_equality'. eapply HP3, EVals_nf_alt; eauto. }
    rewrite !subst_snoc in HE.
    apply ectx_full_item_subst in HE. destruct HE as [i [HE1 ->]].
    apply HP2; auto. rewrite <-?HE1; trivial. do_cstep.
  * intros E' e1 HE Hred Hsafe _ HP1 HP2 HP3 HP4.
    destruct E' as [|E'' E' _] using rev_ind; simplify_equality'.
    { eapply HP3, is_redex_ectx_full; eauto. }
    rewrite !subst_snoc in HE.
    apply ectx_full_item_subst in HE. destruct HE as [i [HE1 ->]].
    apply HP4; auto. rewrite <-HE1. do_cstep.
Qed.
Lemma cstep_expr_call_inv (P : state Ti → Prop) k f Ωs vs m S' :
  Γ\ δ ⊢ₛ State k (Expr (call f @ #{Ωs}* vs)) m ⇒{k} S' →
  length Ωs = length vs →
  P (State (CFun [] :: k) (Call f vs) (mem_unlock (⋃ Ωs) m)) →
  (¬Γ\ get_stack k ⊢ₕ safe call f @ #{Ωs}* vs, m →
    P (State k (Undef (UndefExpr [] (call f @ #{Ωs}* vs))) m)) →
  P S'.
Proof.
  intros [p Hsuffix] ?. revert Hsuffix. pattern S'.
  apply (cstep_focus_inv _ _ _ _ _ p); simpl; try solve_suffix_of.
  * intros E e1 v2 m2 Hvs ? _ _ _.
    simplify_list_subst_equality Hvs; [by inv_ehstep |].
    simplify_zip_equality; simplify_list_subst_equality. inv_ehstep.
  * intros E f' Ωs' vs' Hvs ? _ HP1 _; simplify_list_subst_equality Hvs.
    { edestruct (zip_with_inj EVal Ωs Ωs' vs vs'); eauto with congruence. }
    simplify_zip_equality; simplify_list_subst_equality.
  * intros E e1 Hvs ?? _ _ HP2.
    simplify_list_subst_equality Hvs; [eauto |].
    simplify_zip_equality; simplify_list_subst_equality.
    edestruct @is_redex_nf; eauto. constructor.
Qed.
Lemma cstep_ctx_irrel l l' k1 φ1 m1 k2 φ2 m2 :
  Γ\ δ ⊢ₛ State (k1 ++ l) φ1 m1 ⇒ State (k2 ++ l) φ2 m2 →
  get_stack l = get_stack l' →
  Γ\ δ ⊢ₛ State (k1 ++ l') φ1 m1 ⇒ State (k2 ++ l') φ2 m2.
Proof.
  intros p Hstack. inv_cstep p;
    rewrite ?app_comm_cons in *; simplify_list_equality;
    repeat match goal with
    | H : _\ get_stack (_ ++ _) ⊢ₕ _, _ ⇒ _, _ |- _ =>
       erewrite get_stack_app in H by eapply Hstack
    | H : ¬_\ get_stack (_ ++ _) ⊢ₕ safe _, _ |- _ =>
       erewrite get_stack_app in H by eapply Hstack
    | _ => do_cstep
    | _ => destruct k2, k1; simplify_list_equality'
    end.
Qed.
Lemma cred_ctx_irrel l l' k φ m :
  red (cstep_in_ctx Γ δ l) (State (k ++ l) φ m) →
  get_stack l = get_stack l' →
  red (cstep_in_ctx Γ δ l') (State (k ++ l') φ m).
Proof.
  intros [[? φ' m'] [p [k' ?]]] ?; simpl in *; subst.
  exists (State (k' ++ l') φ' m'). split; [|simpl; solve_suffix_of].
  by apply cstep_ctx_irrel with l.
Qed.
Lemma cstep_call_inv (P : state Ti → Prop) E E' l k1 φ1 m1 S' :
  Γ\ δ ⊢ₛ State (k1 ++ [CFun E] ++ l) φ1 m1 ⇒{l} S' →
  (∀ k2 φ2 m2,
     Γ\ δ ⊢ₛ State (k1 ++ [CFun E'] ++ l) φ1 m1 ⇒{l}
          State (k2 ++ [CFun E'] ++ l) φ2 m2 →
     P (State (k2 ++ [CFun E] ++ l) φ2 m2)) →
  (∀ v,
     k1 = [] → φ1 = Return v →
     Γ\ δ ⊢ₛ State (CFun E' :: l) (Return v) m1 ⇒{l}
          State l (Expr (subst E' (# v)%E)) m1 →
     P (State l (Expr (subst E (# v)%E)) m1)) →
  P S'.
Proof.
  intros [p ?] HP1 HP2. destruct S' as [k2 φ2 m2].
  destruct (decide (CFun E :: l `suffix_of` k2)) as [[k2' ?]|?]; subst.
  * apply HP1. split; [| simpl; solve_suffix_of].
    by apply cstep_ctx_irrel with (CFun E :: l).
  * inv_cstep p; destruct k1; try solve_suffix_of; simplify_list_equality.
    apply HP2; trivial. do_cstep.
Qed.

(** ** Cutting reduction paths *)
(** Given a reduction path, we can cut off the maximal prefix that is restricted
by a more restrictive program context. *)
Lemma cstep_subctx_step_or_nf k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒ S2 → k `suffix_of` SCtx S1 →
  k `suffix_of` SCtx S2 ∨ nf (cstep_in_ctx Γ δ k) S1.
Proof.
  intros p1 ?. destruct (decide (k `suffix_of` SCtx S2)) as [|Hk]; [by left|].
  right. intros [S2' [p2 ?]]. destruct Hk.
  destruct p1; simpl in *; try solve_suffix_of; inv_cstep p2.
Qed.
Lemma cred_preserves_subctx k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒ S2 → red (cstep_in_ctx Γ δ k) S1 →
  k `suffix_of` SCtx S1 → k `suffix_of` SCtx S2.
Proof. intros. by destruct (cstep_subctx_step_or_nf k S1 S2). Qed.
Lemma cstep_subctx_nf k S1 S2 :
  nf (cstep_in_ctx Γ δ k) S1 →
  Γ\ δ ⊢ₛ S1 ⇒ S2 → k `suffix_of` SCtx S1 → SCtx S1 = k.
Proof.
  intros Hnf p ?. destruct (decide (suffix_of k (SCtx S2))).
  * destruct Hnf. exists S2. by split.
  * destruct p; simpl in *; destruct k; solve_suffix_of.
Qed.
Lemma cstep_subctx_cut l k S1 S2 :
  Γ\ δ ⊢ₛ S1 ⇒{k} S2 → l ++ k `suffix_of` SCtx S1 →
  Γ\ δ ⊢ₛ S1 ⇒{l ++ k} S2 ∨ SCtx S1 = l ++ k ∧ nf (cstep_in_ctx Γ δ (l ++ k)) S1.
Proof.
  intros [p ?] ?. destruct (cstep_subctx_step_or_nf (l ++ k) S1 S2); trivial.
  * left. do_cstep.
  * right. split. by apply cstep_subctx_nf with S2. done.
Qed.
Lemma cstep_bsteps_subctx_cut n l k S1 S3 :
  Γ\ δ ⊢ₛ S1 ⇒{k}^n S3 → l ++ k `suffix_of` SCtx S1 →
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
  Γ\ δ ⊢ₛ State (l ++ k) φ1 m1 ⇒{k}^n S3 →
  (**i 1.) *) Γ\ δ ⊢ₛ State (l ++ k) φ1 m1 ⇒{l ++ k}^n S3 ∨
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
Instance ctx_item_subst {Ti} :
    Subst (ctx_item Ti) (stmt Ti) (stmt Ti) := λ Ek s,
  match Ek with
  | CStmt E => subst E s | CBlock _ τ => blk{τ} s
  | _ => s (* dummy *)
  end.
Definition is_CStmt_or_CBlock (Ek : ctx_item Ti) : Prop :=
  match Ek with CStmt _ | CBlock _ _ => True | _ => False end.
Definition in_fun_ctx (k1 k2 : ctx Ti) : Prop := ∃ l,
  Forall is_CStmt_or_CBlock l ∧ k2 = l ++ k1.

Instance: ∀ Ek : ctx_item Ti, Injective (=) (=) (subst Ek).
Proof.
  destruct Ek; intros ???; auto.
  * eapply (injective (subst (CStmt _))); eauto.
  * eapply (injective (SBlock _)); eauto.
Qed.
Instance: Reflexive in_fun_ctx.
Proof. intros k. eexists []. intuition trivial. Qed.
Lemma in_fun_ctx_r k1 k2 Ek :
  is_CStmt_or_CBlock Ek → in_fun_ctx k1 k2 → in_fun_ctx k1 (Ek :: k2).
Proof. intros ? [l [??]]. subst. exists (Ek :: l). intuition. Qed.
Lemma in_fun_ctx_app_r k1 k2 k :
  Forall is_CStmt_or_CBlock k → in_fun_ctx k1 k2 → in_fun_ctx k1 (k ++ k2).
Proof. induction 1; simpl; auto using in_fun_ctx_r. Qed.
Lemma in_fun_ctx_r_inv k1 k2 Ek :
  is_CStmt_or_CBlock Ek →
  k1 `suffix_of` k2 → in_fun_ctx k1 (Ek :: k2) → in_fun_ctx k1 k2.
Proof.
  intros ? [l1 ->] [l2 [Hc1 Hc2]].
  rewrite app_comm_cons in Hc2; simplify_list_equality; decompose_Forall_hyps.
  by exists l1.
Qed.
Lemma in_fun_ctx_change k1 k2 Ek1 Ek2 :
  is_CStmt_or_CBlock Ek2 → k1 `suffix_of` Ek2 :: k2 →
  in_fun_ctx k1 (Ek1 :: k2) → in_fun_ctx k1 (Ek2 :: k2).
Proof.
  intros ? [[|Ek2' l1] ?] [l2 [Hc1 Hc2]]; [by eexists []|].
  destruct l2 as [|? l2]; decompose_Forall_hyps; [discriminate_list_equality|].
  exists (Ek2' :: l2); auto.
Qed.
Lemma in_fun_ctx_not_item_or_block k1 k2 Ek :
  ¬is_CStmt_or_CBlock Ek → k1 `suffix_of` k2 → ¬in_fun_ctx k1 (Ek :: k2).
Proof.
  intros ? [l1 ->] [l2 [Hc1 Hc2]].
  rewrite app_comm_cons in Hc2; simplify_list_equality; by inversion Hc1.
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
      as [[??]|?]; by simplify_list_equality.
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
  intros p. apply (injective (subst k)).
  by eapply cstep_bsteps_preserves_stmt_help; eauto.
Qed.

(** ** Preservation of validity of labels *)
Fixpoint ctx_labels_valid (k : ctx Ti) : Prop :=
  match k with
  | [] => True
  | CFun _ :: k => gotos k ⊆ labels k ∧ ctx_labels_valid k
  | _ :: k => ctx_labels_valid k
  end.
Definition direction_gotos (d : direction Ti) : labelset :=
  match d with ↷ l => {[ l ]} | _ => ∅ end.
Definition state_labels_valid (S : state Ti) : Prop :=
  let (k,φ,m) := S in
  match φ with
  | Stmt d s => gotos s ∪ gotos k ⊆ labels s ∪ labels k ∧
     direction_gotos d ⊆ gotos s ∪ gotos k
  | Expr e => gotos k ⊆ labels k
  | Call _ _ => gotos k ⊆ labels k
  | _ => True
  end.
Lemma cstep_gotos_labels S1 S2 :
  (∀ f s, δ !! f = Some s → gotos s ⊆ labels s) →
  Γ\ δ ⊢ₛ S1 ⇒ S2 → ctx_labels_valid (SCtx S1) → state_labels_valid S1 →
  ctx_labels_valid (SCtx S2) ∧ state_labels_valid S2.
Proof.
  (* slow... *)
  destruct 2; simpl;
    rewrite ?esctx_item_subst_gotos, ?esctx_item_subst_labels,
      ?sctx_item_subst_gotos, ?sctx_item_subst_labels;
    rewrite ?(left_id_L ∅ (∪)), ?(associative_L (∪));
    intuition idtac;
    try (apply subseteq_empty);
    try (by apply union_preserving; eauto);
    let l := fresh in apply elem_of_subseteq; intros l;
    repeat match goal with
    | H : _ ⊆ _ |- _ => apply elem_of_subseteq in H; specialize (H l); revert H
    end; rewrite !elem_of_union; tauto.
Qed.
Lemma csteps_gotos_labels S1 S2 :
  (∀ f s, δ !! f = Some s → gotos s ⊆ labels s) →
  Γ\ δ ⊢ₛ S1 ⇒* S2 → ctx_labels_valid (SCtx S1) → state_labels_valid S1 →
  ctx_labels_valid (SCtx S2) ∧ state_labels_valid S2.
Proof.
  induction 2 as [|S1 S2 S3]; intros; [done|].
  destruct (cstep_gotos_labels S1 S2); auto.
Qed.
Lemma csteps_initial_gotos m1 m2 f vs k s l :
  (∀ f s, δ !! f = Some s → gotos s ⊆ labels s) →
  Γ\ δ ⊢ₛ initial_state m1 f vs ⇒* State k (Stmt (↷ l) s) m2 →
  l ∈ labels s ∪ labels k.
Proof.
  intros. destruct (csteps_gotos_labels (initial_state m1 f vs)
    (State k (Stmt (↷ l) s) m2)); solve_elem_of.
Qed.
End smallstep_properties.

Hint Resolve estep_if_true_no_locks estep_if_false_no_locks
  estep_comma_no_locks : cstep.
Hint Resolve estep_alloc_fresh cstep_in_block_fresh
  cstep_label_block_down_fresh cstep_call_fresh : cstep.
 
