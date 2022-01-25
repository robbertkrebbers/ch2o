(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export state operations.

Section executable.
Context `{Env K}.

Definition assign_exec (Γ : env K) (m : mem K) (a : addr K)
    (v : val K) (ass : assign) : option (val K * val K) :=
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
     Some (val_cast (type_of a) v', va)
  end.
Fixpoint ctx_lookup (x : nat) (k : ctx K) : option (index * type K) :=
  match k with
  | (CStmt _ | CExpr _ _) :: k => ctx_lookup x k
  | CLocal o τ :: k =>
     match x with 0 => Some (o,τ) | S x => ctx_lookup x k end
  | CParams _ oτs :: _ => oτs !! x
  | _ => None
  end.
Definition ehexec (Γ : env K) (k : ctx K)
    (e : expr K) (m : mem K) : listset (expr K * mem K) :=
  match e with
  | var x =>
     '(o,τ) ← option_to_set (ctx_lookup x k);
     {[ (%(Ptr (addr_top o τ)), m) ]}
  | .* (#{Ω} (ptrV p)) =>
     guard (ptr_alive' m p);
     {[ (%{Ω} p, m) ]}
  | & (%{Ω} p) =>
     {[ (#{Ω} (ptrV p), m) ]}
  | %{Ωl} (Ptr a) ::={ass} #{Ωr} v =>
     guard (mem_writable Γ a m);
     '(va,v') ← option_to_set (assign_exec Γ m a v ass);
     {[ (#{lock_singleton Γ a ∪ Ωl ∪ Ωr} v',
        mem_lock Γ a (<[a:=va]{Γ}>m)) ]}
  | load (%{Ω} (Ptr a)) =>
     v ← option_to_set (m !!{Γ} a);
     {[ (#{Ω} v, mem_force Γ a m) ]}
  | %{Ω} (Ptr a) %> rs =>
     guard (addr_strict Γ a);
     {[ (%{Ω} (Ptr (addr_elt Γ rs a)), m) ]}
  | #{Ω} v #> rs =>
     v' ← option_to_set (v !!{Γ} rs);
     {[ (#{Ω} v', m) ]}
  | alloc{τ} (#{Ω} intV{_} n) =>
     let o := fresh (dom indexset m) in
     let n' := Z.to_nat n in
     guard (n' ≠ 0);
     {[ (%{Ω} Ptr (addr_top_array o τ n),
        mem_alloc Γ o true perm_full (val_new Γ (τ.[n'])) m) ]}
     ∪ (if alloc_can_fail then {[ (%{Ω} NULL (TType τ), m) ]} else ∅)
  | free (%{Ω} (Ptr a)) =>
     guard (mem_freeable a m);
     {[ (#{Ω} voidV, mem_free (addr_index a) m) ]}
  | .{op} #{Ω} v =>
     guard (val_unop_ok m op v);
     {[ (#{Ω} val_unop op v, m) ]}
  | #{Ωl} vl .{op} #{Ωr} vr =>
     guard (val_binop_ok Γ m op vl vr);
     {[ (#{Ωl ∪ Ωr} val_binop Γ op vl vr, m) ]}
  | if{#{Ω} VBase vb} e2 else e3 =>
     guard (base_val_branchable m vb);
     if decide (base_val_is_0 vb)
     then {[ (e3, mem_unlock Ω m) ]} else {[ (e2, mem_unlock Ω m) ]}
  | %#{Ω} _,, er =>
     {[ (er, mem_unlock Ω m) ]}
  | cast{τ} (#{Ω} v) =>
     guard (val_cast_ok Γ m (TType τ) v);
     {[ (#{Ω} val_cast (TType τ) v, m) ]}
  | #[r:=#{Ω1} v1] (#{Ω2} v2) =>
     guard (is_Some (v2 !!{Γ} r));
     {[ (#{Ω1 ∪ Ω2} val_alter Γ (λ _, v1) r v2, m) ]}
  | _ => ∅
  end%E.
Definition cexec (Γ : env K) (δ : funenv K)
    (S : state K) : listset (state K) :=
  let 'State k φ m := S in
  match φ with
  | Stmt ↘ s =>
    match s with
    | skip => {[ State k (Stmt ↗ skip) m ]}
    | goto l => {[ State k (Stmt (↷ l) (goto l)) m ]}
    | throw n => {[ State k (Stmt (↑ n) (throw n)) m ]}
    | label l => {[ State k (Stmt ↗ (label l)) m ]}
    | scase mx => {[ State k (Stmt ↗ (scase mx)) m ]}
    | ! e => {[ State (CExpr e (! □) :: k) (Expr e) m ]}
    | ret e => {[ State (CExpr e (ret □) :: k) (Expr e) m ]}
    | loop s => {[ State (CStmt (loop □) :: k) (Stmt ↘ s) m ]}
    | (s1 ;; s2)%S => {[ State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m ]}
    | catch s => {[ State (CStmt (catch □) :: k) (Stmt ↘ s) m ]}
    | if{e} s1 else s2 =>
       {[ State (CExpr e (if{□} s1 else s2) :: k) (Expr e) m ]}
    | switch{e} s =>
       {[ State (CExpr e (switch{□} s) :: k) (Expr e) m ]}
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
    | CStmt (if{e} □ else s2) :: k => {[ State k (Stmt ↗ (if{e} s else s2)) m ]}
    | CStmt (if{e} s1 else □) :: k => {[ State k (Stmt ↗ (if{e} s1 else s)) m ]}
    | CStmt (switch{e} □) :: k => {[ State k (Stmt ↗ (switch{e} s)) m ]}
    | CParams f oτs :: k =>
       {[ State k (Return f voidV) (foldr mem_free m (oτs.*1)) ]}
    | _ => ∅
    end
  | Stmt (⇈ v) s =>
    match k with
    | CParams f oτs :: k =>
       {[ State k (Return f v) (foldr mem_free m (oτs.*1)) ]}
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
      | (s1 ;; s2)%S =>
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
      | switch{e} s => {[ State (CStmt (switch{e} □) :: k) (Stmt (↷ l) s) m ]}
      | _ => ∅
      end
    else
      match k with
      | CLocal o τ :: k => {[ State k (Stmt (↷ l) (local{τ} s)) (mem_free o m) ]}
      | CStmt Es :: k => {[ State k (Stmt (↷ l) (subst Es s)) m ]}
      | _ => ∅
      end
  | Stmt (↓ mx) s =>
    match s with
    | scase mx' =>
       guard (mx = mx');
       {[ State k (Stmt ↗ s) m ]}
    | local{τ} s =>
       guard (mx ∈ cases s);
       let o := fresh (dom indexset m) in
       {[ State (CLocal o τ :: k) (Stmt (↓ mx) s)
                (mem_alloc Γ o false perm_full (val_new Γ τ) m) ]}
    | catch s =>
       guard (mx ∈ cases s);
       {[ State (CStmt (catch □) :: k) (Stmt (↓ mx) s) m ]}
    | (s1 ;; s2)%S =>
       (guard (mx ∈ cases s1);
          {[ State (CStmt (□ ;; s2) :: k) (Stmt (↓ mx) s1) m ]})
       ∪ (guard (mx ∈ cases s2);
          {[ State (CStmt (s1 ;; □) :: k) (Stmt (↓ mx) s2) m ]})
    | loop s =>
       guard (mx ∈ cases s);
       {[ State (CStmt (loop □) :: k) (Stmt (↓ mx) s) m ]}
    | if{e} s1 else s2 =>
       (guard (mx ∈ cases s1);
           {[ State (CStmt (if{e} □ else s2) :: k) (Stmt (↓ mx) s1) m ]})
       ∪ (guard (mx ∈ cases s2);
           {[ State (CStmt (if{e} s1 else □) :: k) (Stmt (↓ mx) s2) m ]})
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
    s ← option_to_set (δ !! f);
    let os := fresh_list (length vs) (dom indexset m) in
    let m2 := mem_alloc_list Γ os vs m in
    {[ State (CParams f (zip os (type_of <$> vs)) :: k) (Stmt ↘ s) m2 ]}
  | Return f v =>
    match k with
    | CFun E :: k => {[ State k (Expr (subst E (# v)%E)) m ]}
    | _ => ∅
    end
  | Expr e =>
    match maybe2 EVal e with
    | Some (Ω,inr v) =>
      match k return listset (state K) with
      | CExpr e (! □) :: k => {[ State k (Stmt ↗ (! e)) (mem_unlock Ω m) ]}
      | CExpr e (ret □) :: k =>
         {[ State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m) ]}
      | CExpr e (if{□} s1 else s2) :: k =>
         vb ← option_to_set (maybe VBase v);
         if decide (base_val_branchable m vb) return listset (state K) then
           if decide (base_val_is_0 vb) return listset (state K) then
             {[State (CStmt (if{e} s1 else □) :: k) (Stmt ↘ s2) (mem_unlock Ω m)]}
           else 
             {[State (CStmt (if{e} □ else s2) :: k) (Stmt ↘ s1) (mem_unlock Ω m)]}
         else {[ State k (Undef (UndefBranch (if{□} s1 else s2) Ω v)) m ]}
      | CExpr e (switch{□} s) :: k =>
         vb ← option_to_set (maybe VBase v);
         if decide (base_val_branchable m vb) return listset (state K) then
           '(τi,x) ← option_to_set (maybe2 VInt vb);
           let m' := mem_unlock Ω m in
           if decide (Some x ∈ cases s) return listset (state K) then
             {[ State (CStmt (switch{e} □) :: k) (Stmt (↓ (Some x)) s) m' ]}
           else if decide (None ∈ cases s) return listset (state K) then
             {[ State (CStmt (switch{e} □) :: k) (Stmt (↓ None) s) m' ]}
           else {[ State k (Stmt ↗ (switch{e} s)) m' ]}
         else {[ State k (Undef (UndefBranch (switch{□} s) Ω v)) m ]}
      | _ => ∅
      end
    | Some (_,inl _) => ∅
    | None =>
      '(E,e') ← expr_redexes e;
      match maybe_ECall_redex e' with
      | Some (Ω, f, _, _, Ωs, vs) =>
         {[ State (CFun E :: k) (Call f vs) (mem_unlock (Ω ∪ ⋃ Ωs) m) ]}
      | None =>
         let es := ehexec Γ k e' m in
         if decide (es ≡ ∅) then {[ State k (Undef (UndefExpr E e')) m ]}
         else '(e2,m2) ← es; {[ State k (Expr (subst E e2)) m2 ]}
      end
    end
  | Undef _ => ∅
  end.
End executable.

Notation "Γ \ δ ⊢ₛ S1 ⇒ₑ S2" := (S2 ∈ cexec Γ δ S1)
  (at level 74, δ at next level,
   format "Γ \  δ  ⊢ₛ '['  S1  '⇒ₑ' '/'  S2 ']'") : C_scope.
Notation "Γ \ δ ⊢ₛ S1 ⇒ₑ* S2" := (rtc (λ S1' S2', Γ \ δ ⊢ₛ S1' ⇒ₑ S2') S1 S2)
  (at level 74, δ at next level,
   format "Γ \  δ  ⊢ₛ '['  S1  '⇒ₑ*' '/'  S2 ']'") : C_scope.
