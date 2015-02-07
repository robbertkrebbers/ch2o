(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export state operations.

Section executable.
Context `{Env Ti}.

Definition assign_exec (Γ : env Ti) (m : mem Ti) (a : addr Ti)
    (v : val Ti) (ass : assign) : option (val Ti * val Ti) :=
  match ass with
  | Assign =>
     guard (val_cast_ok Γ m (type_of a) v);
     let v' := val_cast (type_of a) v in
     Some (v',v')
  | PreOp op =>
     va ← m !!{Γ} a;
     guard (val_binop_ok Γ m op va v);
     let v' := val_binop Γ op va v in
     guard (val_cast_ok Γ m (type_of a) v');
     let v'' := val_cast (type_of a) v' in
     Some (v'', v'')
  | PostOp op =>
     va ← m !!{Γ} a;
     guard (val_binop_ok Γ m op va v);
     let v' := val_binop Γ op va v in
     guard (val_cast_ok Γ m (type_of a) v');
     Some (va, val_cast (type_of a) v')
  end.
Fixpoint ctx_lookup (x : nat) (k : ctx Ti) : option index :=
  match k with
  | (CStmt _ | CExpr _ _) :: k => ctx_lookup x k
  | CLocal o _ :: k =>
     match x with 0 => Some o | S x => ctx_lookup x k end
  | CParams _ oτs :: _ => fst <$> oτs !! x
  | _ => None
  end.
Definition ehexec (Γ : env Ti) (k : ctx Ti)
    (e : expr Ti) (m : mem Ti) : listset (expr Ti * mem Ti) :=
  match e with
  | var{τ} x =>
     o ← of_option (ctx_lookup x k);
     {[ %(addr_top o τ), m ]}
  | .* (#{Ω} (ptrV (Ptr a))) =>
     guard (addr_strict Γ a);
     guard (index_alive' m (addr_index a));
     {[ %{Ω} a, m ]}
  | & (%{Ω} a) =>
     {[ #{Ω} (ptrV (Ptr a)), m ]}
  | %{Ωl} a ::={ass} #{Ωr} v =>
     guard (mem_writable Γ a m);
     '(v',va) ← of_option (assign_exec Γ m a v ass);
     {[ #{lock_singleton Γ a ∪ Ωl ∪ Ωr} v',
        mem_lock Γ a (<[a:=va]{Γ}>m) ]}
  | load (%{Ω} a) =>
     v ← of_option (m !!{Γ} a);
     {[ #{Ω} v, mem_force Γ a m ]}
  | %{Ω} a %> rs => {[ %{Ω} (addr_elt Γ rs a), m ]}
  | #{Ω} v #> rs =>
     v' ← of_option (v !!{Γ} rs);
     {[ #{Ω} v', m ]}
  | alloc{τ} (#{Ω} (intV{_} n)) =>
     let o := fresh (dom indexset m) in
     let n' := Z.to_nat n in
     guard (n' ≠ 0);
     guard (int_typed (n * size_of Γ τ) sptrT);
     {[ #{Ω}(ptrV (Ptr (addr_top_array o τ n))),
        mem_alloc Γ o true perm_full (val_new Γ (τ.[n'])) m ]}
     ∪  (if alloc_can_fail then {[ #{Ω}(ptrV (NULL (TType τ))), m ]} else ∅)
  | free (%{Ω} a) =>
     guard (mem_freeable a m);
     {[ #{Ω} voidV, mem_free (addr_index a) m ]}
  | @{op} #{Ω} v =>
     guard (val_unop_ok m op v);
     {[ #{Ω} (val_unop op v), m ]}
  | #{Ωl} vl @{op} #{Ωr} vr =>
     guard (val_binop_ok Γ m op vl vr);
     {[ #{Ωl ∪ Ωr} (val_binop Γ op vl vr), m ]}
  | if{#{Ω} v} e2 else e3 =>
     match val_true_false_dec m v with
     | inleft (left _) => {[ e2, mem_unlock Ω m ]}
     | inleft (right _) => {[ e3, mem_unlock Ω m ]}
     | inright _ => ∅
     end
  | #{Ω} v,, er =>
     {[ er, mem_unlock Ω m ]}
  | cast{τ} (#{Ω} v) =>
     guard (val_cast_ok Γ m (TType τ) v);
     {[ #{Ω} (val_cast (TType τ) v), m ]}
  | #[r:=#{Ω1} v1] (#{Ω2} v2) =>
     guard (is_Some (v2 !!{Γ} r));
     {[ #{Ω1 ∪ Ω2} (val_alter Γ (λ _, v1) r v2), m ]}
  | _ => ∅
  end%E.
Definition cexec (Γ : env Ti) (δ : funenv Ti)
    (S : state Ti) : listset (state Ti) :=
  let 'State k φ m := S in
  match φ with
  | Stmt ↘ s =>
    match s with
    | skip => {[ State k (Stmt ↗ skip) m ]}
    | goto l => {[ State k (Stmt (↷ l) (goto l)) m ]}
    | throw n => {[ State k (Stmt (↑ n) (throw n)) m ]}
    | label l => {[ State k (Stmt ↗ (label l)) m ]}
    | ! e => {[ State (CExpr e (! □) :: k) (Expr e) m ]}
    | ret e => {[ State (CExpr e (ret □) :: k) (Expr e) m ]}
    | loop s => {[ State (CStmt (loop □) :: k) (Stmt ↘ s) m ]}
    | if{e} s1 else s2 =>
       {[ State (CExpr e (if{□} s1 else s2) :: k) (Expr e) m ]}
    | s1 ;; s2 => {[ State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m ]}
    | catch s => {[ State (CStmt (catch □) :: k) (Stmt ↘ s) m ]}
    | local{τ} s =>
       let o := fresh (dom indexset m) in
       {[ State (CLocal o τ :: k) (Stmt ↘ s)
                (mem_alloc Γ o false perm_full (val_new Γ τ) m) ]}
    end
  | Stmt ↗ s =>
    match k with
    | CLocal o τ :: k => {[ State k (Stmt ↗ (local{τ} s)) (mem_free o m) ]}
    | CStmt (□ ;; s2) :: k => {[ State (CStmt (s ;; □) :: k) (Stmt ↘ s2) m ]}
    | CStmt (s1 ;; □) :: k => {[ State k (Stmt ↗ (s1 ;; s)) m ]}
    | CStmt (catch □) :: k => {[ State k (Stmt ↗ (catch s)) m ]}
    | CStmt (loop □) :: k => {[ State k (Stmt ↘ (loop s)) m ]}
    | CStmt (if{e} □ else s2) :: k =>
       {[ State k (Stmt ↗ (if{e} s else s2)) m ]}
    | CStmt (if{e} s1 else □) :: k =>
       {[ State k (Stmt ↗ (if{e} s1 else s)) m ]}
    | CParams f oτs :: k =>
       {[ State k (Return f voidV) (foldr mem_free m (fst <$> oτs)) ]}
    | _ => ∅
    end
  | Stmt (⇈ v) s =>
    match k with
    | CParams f oτs :: k =>
       {[ State k (Return f v) (foldr mem_free m (fst <$> oτs)) ]}
    | CLocal o τ :: k => {[ State k (Stmt (⇈ v) (local{τ} s)) (mem_free o m) ]}
    | CStmt E :: k => {[ State k (Stmt (⇈ v) (subst E s)) m ]}
    | _ => ∅
    end
  | Stmt (↷ l) s =>
    if decide (l ∈ labels s) then
      match s with
      | label l' => {[ State k (Stmt ↗ s) m ]}
      | local{τ} s =>
         let o := fresh (dom indexset m) in
         {[ State (CLocal o τ :: k) (Stmt (↷ l) s)
                  (mem_alloc Γ o false perm_full (val_new Γ τ) m) ]}
      | catch s => {[ State (CStmt (catch □) :: k) (Stmt (↷ l) s) m ]}
      | s1 ;; s2 =>
         (guard (l ∈ labels s1);
            {[ State (CStmt (□ ;; s2) :: k) (Stmt (↷ l) s1) m ]})
         ∪ (guard (l ∈ labels s2);
            {[ State (CStmt (s1 ;; □) :: k) (Stmt (↷ l) s2) m ]})
      | loop s => {[ State (CStmt (loop □) :: k) (Stmt (↷ l) s) m ]}
      | if{e} s1 else s2 =>
         (guard (l ∈ labels s1);
             {[ State (CStmt (if{e} □ else s2) :: k) (Stmt (↷ l) s1) m ]})
         ∪ (guard (l ∈ labels s2);
             {[ State (CStmt (if{e} s1 else □) :: k) (Stmt (↷ l) s2) m ]})
      | _ => ∅
      end
    else
      match k with
      | CLocal o τ :: k => {[ State k (Stmt (↷ l) (local{τ} s)) (mem_free o m) ]}
      | CStmt Es :: k => {[ State k (Stmt (↷ l) (subst Es s)) m ]}
      | _ => ∅
      end
  | Stmt (↑ n) s =>
    match k with
    | CLocal o τ :: k => {[ State k (Stmt (↑ n) (local{τ} s)) (mem_free o m) ]}
    | CStmt Es :: k =>
       if decide (Es = catch □) then
         match n with
         | 0 => {[ State k (Stmt ↗ (catch s)) m ]}
         | S n => {[ State k (Stmt (↑ n) (catch s)) m ]}
         end
       else {[ State k (Stmt (↑ n) (subst Es s)) m ]}
    | _ => ∅
    end
  | Call f vs =>
    s ← of_option (δ !! f);
    let os := fresh_list (length vs) (dom indexset m) in
    let m2 := mem_alloc_list Γ (zip os vs) m in
    {[ State (CParams f (zip os (type_of <$> vs)) :: k) (Stmt ↘ s) m2 ]}
  | Return f v =>
    match k with
    | CFun E :: k => {[ State k (Expr (subst E (# v)%E)) m ]}
    | _ => ∅
    end
  | Expr e =>
    match maybe2 EVal e with
    | Some (Ω,v) =>
      match k with
      | CExpr e (! □) :: k => {[ State k (Stmt ↗ (! e)) (mem_unlock Ω m) ]}
      | CExpr e (ret □) :: k =>
         {[ State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m) ]}
      | CExpr e (if{□} s1 else s2) :: k =>
        match val_true_false_dec m v with
        | inleft (left _) =>
           {[State (CStmt (if{e} □ else s2) :: k) (Stmt ↘ s1) (mem_unlock Ω m)]}
        | inleft (right _) =>
           {[State (CStmt (if{e} s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m)]}
        | inright _ =>
           {[ State k (Undef (UndefBranch (if{□} s1 else s2) Ω v)) m ]}
         end
      | _ => ∅
      end
    | None =>
      '(E,e') ← expr_redexes e;
      let es := ehexec Γ k e' m in
      if decide (es ≡ ∅) then
        match maybe_ECall_redex e' with
        | Some (Ω, f, _, _, Ωs, vs) =>
           {[ State (CFun E :: k) (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m) ]}
        | _ => {[ State k (Undef (UndefExpr E e')) m ]}
        end
      else '(e2,m2) ← es; {[ State k (Expr (subst E e2)) m2 ]}
    end
  | Undef _ => ∅
  end.
End executable.

Notation "Γ \ δ ⊢ₛ S1 ⇒ₑ S2" := (S2 ∈ cexec Γ δ S1)
  (at level 74, format "Γ \  δ  ⊢ₛ '['  S1  '⇒ₑ' '/'  S2 ']'") : C_scope.
Notation "Γ \ δ ⊢ₛ S1 ⇒ₑ* S2" := (rtc (λ S1' S2', Γ \ δ ⊢ₛ S1' ⇒ₑ S2') S1 S2)
  (at level 74, format "Γ \  δ  ⊢ₛ '['  S1  '⇒ₑ*' '/'  S2 ']'") : C_scope.
