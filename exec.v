(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Export smallstep.

Section exec.
Context `{EnvSpec Ti}.

Definition assign_exec (Γ : env Ti) (m : mem Ti) (a : addr Ti)
    (v : val Ti) (ass : assign) : option (val Ti * val Ti) :=
  match ass with
  | Assign => Some (v,v)
  | PreOp op =>
    vb ← m !!{Γ} a;
    guard (val_binop_ok Γ m op vb v);
    Some (val_binop Γ op vb v, val_binop Γ op vb v)
  | PostOp op =>
    vb ← m !!{Γ} a;
    guard (val_binop_ok Γ m op vb v);
    Some (vb, val_binop Γ op vb v)
  end.
Definition ehstep_exec (Γ : env Ti) (ρ : stack)
    (e : expr Ti) (m : mem Ti) : option (expr Ti * mem Ti) :=
  match e with
  | var{τ} x =>
     o ← ρ !! x;
     Some (%(addr_top o τ), m)
  | .* (#{Ω} (ptrV (Ptr a))) =>
     guard (addr_strict Γ a);
     Some (%{Ω} a, m)
  | & (%{Ω} a) =>
     Some (#{Ω} (ptrV (Ptr a)), m)
  | %{Ωl} a ::={ass} #{Ωr} v =>
     guard (mem_writable Γ a m);
     '(v',va) ← assign_exec Γ m a v ass;
     Some (#{lock_singleton Γ a ∪ Ωl ∪ Ωr} v',
           mem_lock Γ a (<[a:=va]{Γ}>m))
  | load (%{Ω} a) =>
     match maybe_TArray (type_of a) with
     | Some _ => Some (#{Ω} (ptrV (Ptr (addr_elt Γ a))), m)
     | None => v ← m !!{Γ} a; Some (#{Ω} v, mem_force Γ a m)
     end
  | alloc τ =>
     let o := fresh (dom indexset m) in
     Some (#(ptrV (Ptr (addr_top o τ))), mem_alloc Γ o true τ m)
  | free (#{Ω} (ptrV (Ptr a))) =>
     guard (mem_freeable a m);
     Some (#{Ω} voidV, mem_free (addr_index a) m)
  | @{op} #{Ω} v =>
     guard (val_unop_ok op v);
     Some (#{Ω} (val_unop op v), m)
  | #{Ωl} vl @{op} #{Ωr} vr =>
     guard (val_binop_ok Γ m op vl vr);
     Some (#{Ωl ∪ Ωr} (val_binop Γ op vl vr), m)
  | (IF #{Ω} v then e2 else e3) =>
     match val_true_false_dec v with
     | inleft (left _) => Some (e2, mem_unlock Ω m)
     | inleft (right _) => Some (e3, mem_unlock Ω m)
     | inright _ => None
     end
  | #{Ω} v,, er =>
     Some (er, mem_unlock Ω m)
  | cast{τ} (#{Ω} v) =>
     guard (val_cast_ok Γ τ v);
     Some (#{Ω} (val_cast τ v), m)
  | %{Ω} a .> i => Some (%{Ω} (addr_field Γ i a), m)
  | _ => None
  end%E.
Definition cstep_exec (Γ : env Ti) (δ : funenv Ti)
    (S : state Ti) : listset (state Ti) :=
  let 'State k φ m := S in
  match φ with
  | Stmt ↘ s =>
    match s with
    | skip => {[ State k (Stmt ↗ skip) m ]}
    | goto l => {[ State k (Stmt (↷ l) (goto l)) m ]}
    | do e => {[ State (CExpr e (do □) :: k) (Expr e) m ]}
    | ret e => {[ State (CExpr e (ret □) :: k) (Expr e) m ]}
    | while (e) s => {[ State (CExpr e (while (□) s) :: k) (Expr e) m ]}
    | (IF e then s1 else s2) =>
       {[ State (CExpr e (IF □ then s1 else s2) :: k) (Expr e) m ]}
    | s1 ;; s2 => {[ State (CStmt (□ ;; s2) :: k) (Stmt ↘ s1) m ]}
    | l :; s => {[ State (CStmt (l :; □) :: k) (Stmt ↘ s) m ]}
    | blk{τ} s =>
       let o := fresh (dom indexset m) in
       {[ State (CBlock o τ :: k) (Stmt ↘ s)
            (mem_alloc Γ o false τ m) ]}
    end
  | Stmt ↗ s =>
    match k with
    | CBlock o τ :: k =>
       {[ State k (Stmt ↗ (blk{τ} s)) (mem_free o m) ]}
    | CStmt (□ ;; s2) :: k =>
       {[ State (CStmt (s ;; □) :: k) (Stmt ↘ s2) m ]}
    | CStmt (s1 ;; □) :: k => {[ State k (Stmt ↗ (s1 ;; s)) m ]}
    | CStmt (while (e) □) :: k => {[ State k (Stmt ↘ (while (e) s)) m ]}
    | CStmt (IF e then □ else s2) :: k =>
       {[ State k (Stmt ↗ (IF e then s else s2)) m ]}
    | CStmt (IF e then s1 else □) :: k =>
       {[ State k (Stmt ↗ (IF e then s1 else s)) m ]}
    | CStmt (l :; □) :: k => {[ State k (Stmt ↗ (l :; s)) m ]}
    | CParams os :: k => {[ State k (Return voidV) (foldr mem_free m os) ]}
    | _ => ∅
    end
  | Stmt (⇈ v) s =>
    match k with
    | CParams os :: k => {[ State k (Return v) (foldr mem_free m os) ]}
    | CBlock o τ :: k => {[ State k (Stmt (⇈ v) (blk{τ} s)) (mem_free o m) ]}
    | CStmt E :: k => {[ State k (Stmt (⇈ v) (subst E s)) m ]}
    | _ => ∅
    end
  | Stmt (↷ l) s =>
    if decide (l ∈ labels s) then
      match s with
      | l' :; s =>
         if decide (l = l')
         then {[ State (CStmt (l' :; □) :: k) (Stmt ↘ s) m ]}
         else {[ State (CStmt (l' :; □) :: k) (Stmt (↷ l) s) m ]}
      | blk{τ} s =>
         let o := fresh (dom indexset m) in
         {[ State (CBlock o τ :: k) (Stmt (↷ l) s)
             (mem_alloc Γ o false τ m) ]}
      | s1 ;; s2 =>
         (guard (l ∈ labels s1);
            {[ State (CStmt (□ ;; s2) :: k) (Stmt (↷ l) s1) m ]})
         ∪ (guard (l ∈ labels s2);
            {[ State (CStmt (s1 ;; □) :: k) (Stmt (↷ l) s2) m ]})
      | while (e) s => {[ State (CStmt (while (e) □) :: k) (Stmt (↷ l) s) m ]}
      | (IF e then s1 else s2) =>
         (guard (l ∈ labels s1);
             {[ State (CStmt (IF e then □ else s2) :: k) (Stmt (↷ l) s1) m ]})
         ∪ (guard (l ∈ labels s2);
             {[ State (CStmt (IF e then s1 else □) :: k) (Stmt (↷ l) s2) m ]})
      | _ => ∅
      end
    else
      match k with
      | CBlock o τ :: k => {[ State k (Stmt (↷l) (blk{τ} s)) (mem_free o m) ]}
      | CStmt E :: k => {[ State k (Stmt (↷ l) (subst E s)) m ]}
      | _ => ∅
      end
  | Call f vs =>
     s ← of_option (δ !! f);
     let os := fresh_list (length vs) (dom indexset m) in
     let m2 := mem_alloc_list Γ (zip os vs) m in
     {[ State (CParams os :: k) (Stmt ↘ s) m2 ]}
  | Return v =>
    match k with
    | CFun E :: k => {[ State k (Expr (subst E (# v)%E)) m ]}
    | _ => ∅
    end
  | Expr e =>
    match maybe_EVal e with
    | Some (Ω,v) =>
      match k with
      | CExpr e (do □) :: k => {[ State k (Stmt ↗ (do e)) (mem_unlock Ω m) ]}
      | CExpr e (ret □) :: k =>
         {[ State k (Stmt (⇈ v) (ret e)) (mem_unlock Ω m) ]}
      | CExpr e (while (□) s) :: k =>
        match val_true_false_dec v with
        | inleft (left _) =>
           {[ State (CStmt (while (e) □) :: k) (Stmt ↘ s) (mem_unlock Ω m) ]}
        | inleft (right _) =>
           {[ State k (Stmt ↗ (while (e) s)) (mem_unlock Ω m) ]}
        | inright _ => ∅
         end
      | CExpr e (IF □ then s1 else s2) :: k =>
        match val_true_false_dec v with
        | inleft (left _) =>
           {[ State (CStmt (IF e then □ else s2) :: k)
                (Stmt ↘ s1) (mem_unlock Ω m) ]}
        | inleft (right _) =>
           {[ State (CStmt (IF e then s1 else □) :: k)
                (Stmt ↘ s2) (mem_unlock Ω m) ]}
        | inright _ => ∅
         end
      | _ => ∅
      end
    | None =>
      '(E,e') ← expr_redexes (listset _) e;
      match ehstep_exec Γ (get_stack k) e' m with
      | Some (e2,m2) => {[ State k (Expr (subst E e2)) m2 ]}
      | None =>
        match maybe_CCall_redex e' with
        | Some (f, Ωs, vs) =>
           {[ State (CFun E :: k) (Call f vs) (mem_unlock (⋃ Ωs) m) ]}
        | _ => {[ State k Undef m ]}
        end
      end
    end
  | Undef => ∅
  end.
(*
Fixpoint csteps_exec (δ : funenv) (n : nat)
    (Ss : listset state) : listset state :=
  match n with 0 => Ss | S n => csteps_exec δ n (Ss ≫= cstep_exec δ) end.
*)

Definition assign_exec_correct Γ m a v ass v' va' :
  assign_exec Γ m a v ass = Some (v',va') ↔ assign_sem Γ m a v ass v' va'.
Proof.
  split.
  * intros. destruct ass; simplify_option_equality; econstructor; eauto.
  * by destruct 1; simplify_option_equality.
Qed.
Definition ehstep_exec_sound Γ ρ m1 m2 e1 e2 :
  ehstep_exec Γ ρ e1 m1 = Some (e2, m2) → Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2.
Proof.
  intros. destruct e1;
    repeat match goal with
    | H : assign_exec _ _ _ _ _ = Some _ |- _ =>
      apply assign_exec_correct in H
    | _ => progress simplify_option_equality
    | _ => destruct (val_true_false_dec _) as [[[??]|[??]]|[??]]
    | _ => case_match
    end; do_ehstep.
Qed.
Definition ehstep_exec_weak_complete Γ ρ e1 m1 e2 m2 :
  ehstep_exec Γ ρ e1 m1 = None → ¬Γ\ ρ ⊢ₕ e1, m1 ⇒ e2, m2.
Proof.
  destruct 2; 
    repeat match goal with
    | H : assign_sem _ _ _ _ _ _ _ |- _ =>
      apply assign_exec_correct in H
    | H : is_Some _ |- _ => destruct H as [??]
    | _ => progress simplify_option_equality
    | _ => destruct (val_true_false_dec _) as [[[??]|[??]]|[??]]
    | _ => case_match
    end; auto.
Qed.
Definition cstep_exec_sound Γ δ S1 S2 :
  S2 ∈ cstep_exec Γ δ S1 → Γ\ δ ⊢ₛ S1 ⇒ S2.
Proof.
  intros. assert (∀ (k : ctx Ti) e m,
    ehstep_exec Γ (get_stack k) e m = None → maybe_CCall_redex e = None →
    is_redex e → ¬Γ\ get_stack k ⊢ₕ safe e, m).
  { intros k e m He. rewrite eq_None_not_Some.
    intros Hmaybe Hred Hsafe; apply Hmaybe; destruct Hsafe.
    * eexists; apply maybe_CCall_redex_Some; eauto.
    * edestruct ehstep_exec_weak_complete; eauto. }
  destruct S1;
    repeat match goal with
    | H : ehstep_exec _ _ _ _ = Some _ |- _ =>
      apply ehstep_exec_sound in H
    | H : _ ∈ expr_redexes _ _ |- _ =>
      apply (expr_redexes_correct _) in H; destruct H
    | H : maybe_EVal _ = Some _ |- _ => apply maybe_EVal_Some in H
    | H : maybe_CCall_redex _ = Some _ |- _ =>
      apply maybe_CCall_redex_Some in H; destruct H
    | _ => progress decompose_elem_of
    | _ => case_decide
    | _ => destruct (val_true_false_dec _) as [[[??]|[??]]|[??]]
    | _ => case_match
    | _ => progress simplify_equality'
    end; do_cstep.
Qed.
End exec.
