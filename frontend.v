(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String nmap.
Require Export type_system expression_eval error.
Local Open Scope string_scope.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Local Open Scope list_scope.

Inductive cexpr (Ti : Set) : Set :=
  | CEVar : N → cexpr Ti
  | CEConst : int_type Ti → Z → cexpr Ti
  | CESizeOf : ctype Ti → cexpr Ti
  | CEAddrOf : cexpr Ti → cexpr Ti
  | CEDeref : cexpr Ti → cexpr Ti
  | CEAssign : assign → cexpr Ti → cexpr Ti → cexpr Ti
  | CECall : N → list (cexpr Ti) → cexpr Ti
  | CEAlloc : ctype Ti → cexpr Ti → cexpr Ti
  | CEFree : cexpr Ti → cexpr Ti
  | CEUnOp : unop → cexpr Ti → cexpr Ti
  | CEBinOp : binop → cexpr Ti → cexpr Ti → cexpr Ti
  | CEIf : cexpr Ti → cexpr Ti → cexpr Ti → cexpr Ti
  | CEComma : cexpr Ti → cexpr Ti → cexpr Ti
  | CEAnd : cexpr Ti → cexpr Ti → cexpr Ti
  | CEOr : cexpr Ti → cexpr Ti → cexpr Ti
  | CECast : ctype Ti → cexpr Ti → cexpr Ti
  | CEField : cexpr Ti → N → cexpr Ti
with ctype (Ti : Set) : Set :=
  | CTVoid : ctype Ti
  | CTDef : N → ctype Ti
  | CTEnum : N → ctype Ti
  | CTInt : int_type Ti → ctype Ti
  | CTPtr : ctype Ti → ctype Ti
  | CTArray : ctype Ti → cexpr Ti → ctype Ti
  | CTCompound : compound_kind → N → ctype Ti
  | CTTypeOf : cexpr Ti → ctype Ti.
Arguments CEVar {_} _.
Arguments CEConst {_} _ _.
Arguments CESizeOf {_} _.
Arguments CEAddrOf {_} _.
Arguments CEDeref {_} _.
Arguments CEAssign {_} _ _ _.
Arguments CECall {_} _ _.
Arguments CEAlloc {_} _ _.
Arguments CEFree {_} _.
Arguments CEUnOp {_} _ _.
Arguments CEBinOp {_} _ _ _.
Arguments CEIf {_} _ _ _.
Arguments CEComma {_} _ _.
Arguments CEAnd {_} _ _.
Arguments CEOr {_} _ _.
Arguments CECast {_} _ _.
Arguments CEField {_} _ _.
Arguments CTArray {_} _ _.
Arguments CTCompound {_} _ _.
Arguments CTVoid {_}.
Arguments CTDef {_} _.
Arguments CTEnum {_} _.
Arguments CTInt {_} _.
Arguments CTPtr {_} _.
Arguments CTTypeOf {_} _.

Inductive cstmt (Ti : Set) : Set :=
  | CSDo : cexpr Ti → cstmt Ti
  | CSSkip : cstmt Ti
  | CSGoto : labelname → cstmt Ti
  | CSBreak : cstmt Ti
  | CSContinue : cstmt Ti
  | CSReturn : option (cexpr Ti) → cstmt Ti
  (* true = static, false = not static *)
  | CSBlock : bool → N → ctype Ti → option (cexpr Ti) → cstmt Ti → cstmt Ti
  | CSTypeDef : N → ctype Ti → cstmt Ti → cstmt Ti
  | CSComp : cstmt Ti → cstmt Ti → cstmt Ti
  | CSLabel : labelname → cstmt Ti → cstmt Ti
  | CSWhile : cexpr Ti → cstmt Ti → cstmt Ti
  | CSFor : cexpr Ti → cexpr Ti → cexpr Ti → cstmt Ti → cstmt Ti
  | CSDoWhile : cstmt Ti → cexpr Ti → cstmt Ti
  | CSIf : cexpr Ti → cstmt Ti → cstmt Ti → cstmt Ti.
Arguments CSDo {_} _.
Arguments CSSkip {_}.
Arguments CSGoto {_} _.
Arguments CSBreak {_}.
Arguments CSContinue {_}.
Arguments CSReturn {_} _.
Arguments CSBlock {_} _ _ _ _ _.
Arguments CSTypeDef {_} _ _ _.
Arguments CSComp {_} _ _.
Arguments CSLabel {_} _ _.
Arguments CSWhile {_} _ _.
Arguments CSFor {_} _ _ _ _.
Arguments CSDoWhile {_} _ _.
Arguments CSIf {_} _ _ _.

Inductive decl (Ti : Set) : Set :=
  | CompoundDecl : compound_kind → list (N * ctype Ti) → decl Ti
  | EnumDecl : int_type Ti → list (N * Z) → decl Ti
  | TypeDefDecl : ctype Ti → decl Ti
  | GlobDecl : ctype Ti → option (cexpr Ti) → decl Ti
  | FunDecl : list (N * ctype Ti) → ctype Ti → option (cstmt Ti) → decl Ti.
Arguments CompoundDecl {_} _ _.
Arguments TypeDefDecl {_} _.
Arguments GlobDecl {_} _ _.
Arguments FunDecl {_} _ _ _.

Inductive var_decl (Ti : Set) : Set :=
  | Global : index → var_decl Ti
  | Local : type Ti → var_decl Ti
  | EnumVal : int_type Ti → Z → var_decl Ti
  | TypeDef : type Ti → var_decl Ti.
Arguments Global {_} _.
Arguments Local {_} _.
Arguments EnumVal {_} _ _.
Arguments TypeDef {_} _.
Notation var_env Ti := (list (N * var_decl Ti)).

Inductive compound_type (Ti : Set) : Set :=
  | CompoundType : compound_kind → list N → compound_type Ti
  | EnumType : int_type Ti → compound_type Ti.
Arguments CompoundType {_} _ _.
Arguments EnumType {_} _.
Definition maybe_CompoundType {Ti}
    (t : compound_type Ti) : option (compound_kind * list N) :=
  match t with CompoundType c xs => Some (c,xs) | _ => None end.
Definition maybe_EnumType {Ti} (t : compound_type Ti) : option (int_type Ti) :=
  match t with EnumType τi => Some τi | _ => None end.
Notation compound_env Ti := (tagmap (compound_type Ti)).

Section frontend.
Context `{Env Ti}.

Fixpoint var_fresh (x : N) (xs : var_env Ti) : bool :=
  match xs with
  | [] => true | (y,_) :: xs => bool_decide (x ≠ y) && var_fresh x xs
  end.
Fixpoint lookup_var (m : mem Ti) (x : N)
    (i : nat) (xs : var_env Ti) : option (expr Ti * lrtype Ti) :=
  match xs with
  | [] => None
  | (y,Global o) :: xs =>
     if decide (x = y)
     then τ ← type_check m o; Some (% (addr_top o τ), inl τ)
     else lookup_var m x i xs
  | (y,Local τ) :: xs =>
     if decide (x = y) then Some (var{τ} i, inl τ)
     else lookup_var m x (S i) xs
  | (y,EnumVal τi z) :: xs =>
     if decide (x = y) then Some (# intV{τi} z, inr (intT τi))
     else lookup_var m x i xs
  | (y,TypeDef _) :: xs =>
     if decide (x = y) then None else lookup_var m x i xs
  end.
Fixpoint lookup_typedef (x : N) (xs : var_env Ti) : option (type Ti) :=
  match xs with
  | [] => None
  | (y,d) :: xs =>
     if decide (x = y)
     then match d with TypeDef τ => Some τ | _ => None end
     else lookup_typedef x xs
  end.
Definition is_pseudo_NULL (e : expr Ti) : bool :=
  match e with #{_} (intV{_} 0) => true | _ => false end.
Definition to_R (eτlr : expr Ti * lrtype Ti) : expr Ti * type Ti :=
  match eτlr with
  | (e, inl τ) =>
    match maybe_TArray τ with
    | Some (τ',n) => (& (e %> RArray 0 τ' n), τ'.*) | None => (load e, τ)
    end
  | (e, inr τ) => (e,τ)
  end.
Definition to_R_NULL (σ : type Ti)
    (eτlr : expr Ti * lrtype Ti) : expr Ti * type Ti :=
  let (e,τ) := to_R eτlr in
  match σ with
  | τp.* => if is_pseudo_NULL e then (# (ptrV (NULL τp)), τp.*) else (e,τ)
  | _ => (e,τ)
  end.
Definition convert_ptrs (eτ1 eτ2 : expr Ti * type Ti) :
    option (expr Ti * expr Ti * type Ti) :=
  let (e1,τ1) := eτ1 in let (e2,τ2) := eτ2 in
  match τ1, τ2 with
  | τp1.*, τp2.* =>
     if decide (τp1 = voidT) then Some (e1, cast{voidT.*} e2, voidT.*)
     else if decide (τp2 = voidT) then Some (cast{voidT.*} e1, e2, voidT.*)
     else None
  | τp1.*, intT _ =>
     guard (is_pseudo_NULL e2); Some (e1, # (ptrV (NULL τp1)), τp1.*)
  | intT _, τp2.* =>
     guard (is_pseudo_NULL e1); Some (# (ptrV (NULL τp2)), e2, τp2.*)
  | _, _ => None
  end.
Definition to_if_expr (e1 : expr Ti)
    (eτ2 eτ3 : expr Ti * type Ti) : option (expr Ti * lrtype Ti) :=
  (** 1.) *) (
    (** same types *)
    let (e2,τ2) := eτ2 in let (e3,τ3) := eτ3 in
    guard (τ2 = τ3); Some (if{e1} e2 else e3, inr τ2)) ∪
  (** 2.) *) (
    (** common arithmetic conversions *)
    let (e2,τ2) := eτ2 in let (e3,τ3) := eτ3 in
    match τ2, τ3 with
    | intT τi2, intT τi3 =>
       let τi' := int_promote τi2 ∪ int_promote τi3 in
       Some (if{e1} cast{intT τi'} e2 else cast{intT τi'} e3, inr (intT τi'))
    | _, _ => None
    end) ∪
  (** 3.) *) (
    (** one side is NULL or void *)
    '(e2,e3,τ) ← convert_ptrs eτ2 eτ3;
    Some (if{e1} e2 else e3, inr τ)).
Definition to_binop_expr (op : binop)
    (eτ1 eτ2 : expr Ti * type Ti) : option (expr Ti * lrtype Ti) :=
  (** 1.) *) (
    let (e1,τ1) := eτ1 in let (e2,τ2) := eτ2 in
    σ ← binop_type_of op τ1 τ2; Some (e1 @{op} e2, inr σ)) ∪
  (** 2.) *) (
    (** one side is NULL or void *)
    guard (op = CompOp EqOp);
    '(e1,e2,τ) ← convert_ptrs eτ1 eτ2;
    σ ← binop_type_of (CompOp EqOp) τ τ;
    Some (e1 @{op} e2, inr σ)).
End frontend.

(* not in the section because of bug #3488 *)
Fixpoint to_expr `{Env Ti} (Γn : compound_env Ti) (Γ : env Ti)
    (Γf : funtypes Ti) (m : mem Ti) (xs : var_env Ti)
    (ce : cexpr Ti) : string + expr Ti * lrtype Ti :=
  match ce with
  | CEVar x =>
     error_of_option (lookup_var m x 0 xs) "variable not found"
  | CEConst τi x =>
     guard (int_typed x τi) with "integer constant not in range";
     inr (# (intV{τi} x), inr (intT τi))
  | CESizeOf cτ =>
     τ ← to_type Γn Γ Γf m xs false cτ;
     let sz := size_of Γ τ in
     guard (int_typed sz sptrT) with "argument of size of not in range";
     inr (# (intV{sptrT} sz), inr sptrT)
  | CEDeref ce =>
     '(e,τ) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     τp ← error_of_option (maybe_TBase τ ≫= maybe_TPtr)
       "dereferencing non-pointer type";
     guard (✓{Γ} τp) with "dereferencing incomplete pointer type";
     inr (.* e, inl τp)
  | CEAddrOf ce =>
     '(e,τlr) ← to_expr Γn Γ Γf m xs ce;
     τ ← error_of_option (maybe_inl τlr) "taking address of r-value";
     inr (& e, inr (τ.*))
  | CEAssign ass ce1 ce2 =>
     '(e1,τlr1) ← to_expr Γn Γ Γf m xs ce1;
     τ1 ← error_of_option (maybe_inl τlr1) "assigning to r-value";
     '(e2,τ2) ← to_R_NULL τ1 <$> to_expr Γn Γ Γf m xs ce2;
     σ ← error_of_option (assign_type_of Γ τ1 τ2 ass) "assignment cannot be typed";
     inr (e1 ::={ass} e2, inr σ)
  | CECall f ces =>
     let f : funname := f in
     '(τs,σ) ← error_of_option (Γf !! f) "function not declared";
     guard (length ces = length τs)
       with "function applied to wrong number of arguments";
     eτlrs ← mapM (to_expr Γn Γ Γf m xs) ces;
     let τes := zip_with to_R_NULL τs eτlrs in 
     guard (Forall2 (cast_typed Γ) (snd <$> τes) τs)
       with "function applied to arguments of incorrect type";
     inr (call f @ cast{τs}* (fst <$> τes), inr σ)
  | CEAlloc cτ ce =>
     τ ← to_type Γn Γ Γf m xs false cτ;
     '(e,τe) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     _ ← error_of_option (maybe_TBase τe ≫= maybe_TInt)
       "alloc applied to argument of non-integer type";
     inr (& (alloc{τ} e), inr (τ.* ))
  | CEFree ce =>
     '(e,τ) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     τp ← error_of_option (maybe_TBase τ ≫= maybe_TPtr)
       "free applied to argument of non-pointer type";
     guard (✓{Γ} τp) with "free applied to argument of incomplete pointer type";
     inr (free (.* e), inr voidT)
  | CEUnOp op ce =>
     '(e,τ) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     σ ← error_of_option (unop_type_of op τ) "unary operator cannot be typed";
     inr (@{op} e, inr σ)
  | CEBinOp op ce1 ce2 =>
     eτ1 ← to_R <$> to_expr Γn Γ Γf m xs ce1;
     eτ2 ← to_R <$> to_expr Γn Γ Γf m xs ce2;
     error_of_option (to_binop_expr op eτ1 eτ2) "binary operator cannot be typed"
  | CEIf ce1 ce2 ce3 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ Γf m xs ce1;
     _ ← error_of_option (maybe_TBase τ1)
       "conditional argument of if expression of non-base type";
     eτ2 ← to_R <$> to_expr Γn Γ Γf m xs ce2;
     eτ3 ← to_R <$> to_expr Γn Γ Γf m xs ce3;
     error_of_option (to_if_expr e1 eτ2 eτ3) "if expression cannot be typed"
  | CEComma ce1 ce2 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ Γf m xs ce1;
     '(e2,τ2) ← to_R <$> to_expr Γn Γ Γf m xs ce2;
     inr (e1,, e2, inr τ2)
  | CEAnd ce1 ce2 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ Γf m xs ce1;
     _ ← error_of_option (maybe_TBase τ1) "first argument of && of non-base type";
     '(e2,τ2) ← to_R <$> to_expr Γn Γ Γf m xs ce2;
     _ ← error_of_option (maybe_TBase τ2) "second argument of && of non-base type";
     inr (if{e1} if{e2} #(intV{sintT} 1) else #(intV{sintT} 0)
           else #(intV{sintT} 0), inr sintT)
  | CEOr ce1 ce2 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ Γf m xs ce1;
     _ ← error_of_option (maybe_TBase τ1) "first argument of || of non-base type";
     '(e2,τ2) ← to_R <$> to_expr Γn Γ Γf m xs ce2;
     _ ← error_of_option (maybe_TBase τ2) "second argument of || of non-base type";
     inr (if{e1} #(intV{sintT} 0)
           else (if{e2} #(intV{sintT} 1) else #(intV{sintT} 0)), inr sintT)
  | CECast cσ ce =>
     σ ← to_type Γn Γ Γf m xs true cσ;
     '(e,τ) ← to_R_NULL σ <$> to_expr Γn Γ Γf m xs ce;
     guard (maybe_TCompound σ = None) with "cannot cast to struct/union";
     guard (cast_typed Γ τ σ) with "cast cannot be typed";
     inr (cast{σ} e, inr σ)
  | CEField ce x =>
     '(e,τrl) ← to_expr Γn Γ Γf m xs ce;
     '(c,s) ← error_of_option (maybe_TCompound (lrtype_type τrl))
       "field operator applied to argument of non-compound type";
     σs ← error_of_option (Γ !! s)
       "field operator applied to argument of incomplete compound type";
     '(_,xs) ← error_of_option (Γn !! s ≫= maybe_CompoundType)
       "please report: incompatible environments at field operator";
     i ← error_of_option (list_find (x =) xs)
       "field operator used with invalid index";
     σ ← error_of_option (σs !! i)
       "please report: incompatible environments at field operator";
     let rs :=
       match c with
       | Struct_kind => RStruct i s | Union_kind => RUnion i s false
       end in
     match τrl with
     | inl _ => inr (e %> rs, inl σ) | inr _ => inr (e #> rs, inr σ)
     end
  end
with to_type `{Env Ti} (Γn : compound_env Ti) (Γ : env Ti)
    (Γf : funtypes Ti) (m : mem Ti) (xs : var_env Ti)
    (ptr : bool) (cτ : ctype Ti) : string + type Ti :=
  match cτ with
  | CTVoid => inr voidT
  | CTDef x =>
     error_of_option (lookup_typedef x xs) "typedef not found"
  | CTEnum s =>
     let s : tag := s in
     τi ← error_of_option (Γn !! s ≫= maybe_EnumType) "enum not found";
     inr (intT τi)
  | CTInt τi => inr (intT τi)
  | CTPtr cτ => τ ← to_type Γn Γ Γf m xs true cτ; inr (τ.* )
  | CTArray cτ ce =>
     τ ← to_type Γn Γ Γf m xs false cτ;
     '(e,_) ← to_expr Γn Γ Γf m xs ce;
     v ← error_of_option (⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr)
       "array with non-constant size expression";
     '(_,x) ← error_of_option (maybe_VBase v ≫= maybe_VInt)
       "array non-integer size expression";
     let n := Z.to_nat x in
     guard (n ≠ 0) with "array with negative or zero size expression";
     inr (τ.[n])
  | CTCompound c s =>
     let s : tag := s in
     guard (¬ptr → is_Some (Γ !! s)) with "complete compound type expected";
     inr (compoundT{c} s)
  | CTTypeOf ce =>
     '(_,τ) ← to_expr Γn Γ Γf m xs ce;
     inr (lrtype_type τ)
  end.

Section frontend_more.
Context `{Env Ti}.

Global Instance cstmt_labels : Labels (cstmt Ti) :=
  fix go cs := let _ : Labels _ := @go in
  match cs with
  | CSBlock _ _ _ _ cs => labels cs
  | CSComp cs1 cs2 => labels cs1 ∪ labels cs2
  | CSLabel l cs => {[ l ]} ∪ labels cs
  | CSWhile _ cs => labels cs
  | CSIf _ cs1 cs2 => labels cs1 ∪ labels cs2
  | _ => ∅
  end.
Definition alloc_global (Γn : compound_env Ti) (Γ : env Ti) (m : mem Ti)
    (xs : var_env Ti) (x : N) (τ : type Ti)
    (mce : option (cexpr Ti)) : string + mem Ti * var_env Ti :=
  match mce with
  | Some ce =>
     guard (int_typed (size_of Γ τ) sptrT)
       with "size of global/static not in range";
     '(e,τ') ← to_R_NULL τ <$> to_expr Γn Γ ∅ m xs ce;
     guard (cast_typed Γ τ' τ)
       with "global/static with initializer of incorrect type";
     v ← error_of_option (⟦ cast{τ} e ⟧ Γ ∅ [] m ≫= maybe_inr)
       "global/static with non-constant initializer";
     let o := fresh (dom _ m) in
     inr (<[addr_top o τ:=v]{Γ}>(mem_alloc Γ o false τ m), (x,Global o) :: xs)
  | None =>
     guard (int_typed (size_of Γ τ) sptrT)
       with "global/static with out of range type";
     let o := fresh (dom _ m) in
     inr (<[addr_top o τ:=val_0 Γ τ]{Γ}>(mem_alloc Γ o false τ m),
           (x,Global o) :: xs)
  end.
Definition to_stmt (Γn : compound_env Ti) (Γ : env Ti)
    (Γf : funtypes Ti) (τret : type Ti) :
    mem Ti → var_env Ti → labelset → option labelname → option labelname →
    cstmt Ti → string + mem Ti * stmt Ti * rettype Ti :=
  fix go m xs Ls mLc mLb cs {struct cs} :=
  match cs with
  | CSDo ce =>
     '(e,_) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     inr (m, !e, (false, None))
  | CSSkip => inr (m, skip, (false, None))
  | CSGoto l => inr (m, goto l, (true, None))
  | CSContinue =>
     Lc ← error_of_option mLc "continue not allowed";
     inr (m, goto Lc, (true, None))
  | CSBreak =>
     Lb ← error_of_option mLb "break not allowed";
     inr (m, goto Lb, (true, None))
  | CSReturn (Some ce) =>
     '(e,τ') ← to_R <$> to_expr Γn Γ Γf m xs ce;
     guard (cast_typed Γ τ' τret) with "return expression of incorrect type";
     inr (m, ret (cast{τret} e), (true, Some τret))
  | CSReturn None => inr (m, ret (#voidV), (true, Some voidT))
  | CSBlock false x cτ None cs =>
     τ ← to_type Γn Γ Γf m xs false cτ;
     guard (int_typed (size_of Γ τ) sptrT) with "block with out of range type";
     '(m,s,cmσ) ← go m ((x,Local τ) :: xs) Ls mLc mLb cs;
     inr (m, blk{τ} s, cmσ)
  | CSBlock false x cτ (Some ce) cs =>
     τ ← to_type Γn Γ Γf m xs false cτ;
     guard (int_typed (size_of Γ τ) sptrT) with "block with out of range type";
     '(e,τ') ← to_R <$> to_expr Γn Γ Γf m ((x,Local τ) :: xs) ce;
     guard (cast_typed Γ τ' τ) with "block with initializer of incorrect type";
     '(m,s,cmσ) ← go m ((x,Local τ) :: xs) Ls mLc mLb cs;
     inr (m, blk{τ} (var{τ} 0 ::= e ;; s), cmσ)
  | CSBlock true x cτ mce cs =>
     τ ← to_type Γn Γ Γf m xs false cτ;
     '(m,xs) ← alloc_global Γn Γ m xs x τ mce;
     go m xs Ls mLc mLb cs
  | CSTypeDef x cτ cs =>
     τ ← to_type Γn Γ Γf m xs false cτ;
     go m ((x,TypeDef τ) :: xs) Ls mLc mLb cs
  | CSComp cs1 cs2 =>
     '(m,s1,cmσ1) ← go m xs Ls mLc mLb cs1;
     '(m,s2,cmσ2) ← go m xs Ls mLc mLb cs2;
     mσ ← error_of_option (rettype_union (cmσ1.2) (cmσ2.2))
       "composition with non-matching return types";
     inr (m, s1 ;; s2, (cmσ2.1, mσ))
  | CSLabel l cs =>
     '(m,s,cmσ) ← go m xs Ls mLc mLb cs; inr (m, l :; s, cmσ)
  | CSWhile ce cs =>
     '(e,τ) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     _ ← error_of_option (maybe_TBase τ)
       "while loop with conditional expression of non-base type";
     let LC := fresh Ls in let LB := fresh ({[ LC ]} ∪ Ls) in
     let Ls := {[ LC ; LB ]} ∪ Ls in
     '(m,s,cmσ) ← go m xs Ls (Some LC) (Some LB) cs;
     inr (m, while{e} (s;; label LC);; label LB, (false, cmσ.2))
  | CSFor ce1 ce2 ce3 cs =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ Γf m xs ce1;
     '(e2,τ2) ← to_R <$> to_expr Γn Γ Γf m xs ce2;
     _ ← error_of_option (maybe_TBase τ2)
       "for loop with conditional expression of non-base type";
     '(e3,τ3) ← to_R <$> to_expr Γn Γ Γf m xs ce3;
     let LC := fresh Ls in let LB := fresh ({[ LC ]} ∪ Ls) in
     let Ls := {[ LC ; LB ]} ∪ Ls in
     '(m,s,cmσ) ← go m xs Ls (Some LC) (Some LB) cs;
     inr (m, !e1 ;; while{e2} (s;; label LC;; !e3);; label LB, (false, cmσ.2))
  | CSDoWhile cs ce =>
     let LC := fresh Ls in let LB := fresh ({[ LC ]} ∪ Ls) in
     let Ls := {[ LC ; LB ]} ∪ Ls in
     '(m,s,cmσ) ← go m xs Ls (Some LC) (Some LB) cs;
     '(e,τ) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     _ ← error_of_option (maybe_TBase τ)
       "do-while loop with conditional expression of non-base type";
     inr (m, while{#intV{sintT} 1}
       (s;; label LC;; if{e} skip else goto LB);; label LB, (false, cmσ.2))
  | CSIf ce cs1 cs2 =>
     '(e,τ) ← to_R <$> to_expr Γn Γ Γf m xs ce;
     _ ← error_of_option (maybe_TBase τ) "if with expression of non-base type";
     '(m,s1,cmσ1) ← go m xs Ls mLc mLb cs1;
     '(m,s2,cmσ2) ← go m xs Ls mLc mLb cs2;
     mσ ← error_of_option (rettype_union (cmσ1.2) (cmσ2.2))
       "if statement with non-matching return types";
     inr (m, if{e} s1 else s2, (cmσ1.1 && cmσ2.1, mσ))%S
  end%T.

Definition extend_funtypes (Γ : env Ti) (f : funname) (τs : list (type Ti))
    (τ : type Ti) (Γf : funtypes Ti) : string + funtypes Ti :=
  match Γf !! f with
  | Some (τs',τ') =>
     guard (τs' = τs) with "function with arguments that do not match prototype";
     guard (τ' = τ) with "function with return type that does not match prototype";
     inr Γf
  | None =>
     guard (Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs)
       with "function with argument of out of range type";
     inr (<[f:=(τs,τ)]>Γf)
  end.
Fixpoint to_envs_go (Θ : list (N * decl Ti)) : string +
    compound_env Ti * env Ti * funtypes Ti * funenv Ti * mem Ti * var_env Ti :=
  match Θ with
  | [] => inr (∅,∅,∅,∅,∅,[])
  | (s,CompoundDecl c cτys) :: Θ =>
     '(Γn,Γ,Γf,δ,m,xs) ← to_envs_go Θ;
     let s : tag := s in
     let ys := fst <$> cτys in
     τs ← mapM (to_type Γn Γ Γf m xs false) (snd <$> cτys);
     guard (Γ !! s = None) with "compound type with previously declared name";
     guard (NoDup ys) with "compound type with non-unique fields";
     guard (τs ≠ []) with "compound type should have atleast 1 field";
     inr (<[s:=CompoundType c ys]>Γn, <[s:=τs]>Γ, Γf, δ, m, xs)
  | (s,EnumDecl τi yzs) :: Θ =>
     '(Γn,Γ,Γf,δ,m,xs) ← to_envs_go Θ;
     let s : tag := s in
     let ys := fst <$> yzs in
     guard (Γn !! s = None) with "enum type with previously declared name";
     guard (NoDup ys) with "enum type with non-unique fields";
     guard (Forall (λ x, var_fresh x xs) ys)
       with "enum type with field name that has previously been declared";
     guard (Forall (λ z, int_typed z τi) (snd <$> yzs))
       with "enum with field of out of range type";
     let xs' := ((prod_map id (EnumVal τi) <$> yzs) ++ xs)%list in
     inr (<[s:=EnumType τi]>Γn, Γ, Γf, δ, m, xs')
  | (x,TypeDefDecl cτ) :: Θ =>
     '(Γn,Γ,Γf,δ,m,xs) ← to_envs_go Θ;
     guard (var_fresh x xs) with "typedef with previously declared name";
     τ ← to_type Γn Γ Γf m xs false cτ;
     inr (Γn, Γ, Γf, δ, m, (x,TypeDef τ) :: xs)
  | (x,GlobDecl cτ me) :: Θ =>
     '(Γn,Γ,Γf,δ,m,xs) ← to_envs_go Θ;
     guard (var_fresh x xs) with "global with previously declared name";
     τ ← to_type Γn Γ Γf m xs false cτ;
     '(m,xs) ← alloc_global Γn Γ m xs x τ me;
     inr (Γn, Γ, Γf, δ, m, xs)
  | (f,FunDecl cτys cσ mcs) :: Θ =>
     (* todo: functions and globals cannot have the same name *)
     '(Γn,Γ,Γf,δ,m,xs) ← to_envs_go Θ;
     let f : funname := f in
     let ys := fst <$> cτys in
     τs ← mapM (to_type Γn Γ Γf m xs false) (snd <$> cτys);
     guard (NoDup ys) with "function with non-unique arguments";
     σ ← to_type Γn Γ Γf m xs false cσ;
     Γf ← extend_funtypes Γ f τs σ Γf;
     match mcs with
     | Some cs =>
        guard (δ !! f = None) with "function previously declared";
        let xs' := zip_with (λ y τ, (y, Local τ)) ys τs ++ xs in
        '(m,s,cmσ) ← to_stmt Γn Γ Γf σ m xs' (labels cs) None None cs;
        guard (gotos s ⊆ labels s) with "function with unbound gotos";
        guard (rettype_match cmσ σ) with "function with incorrect return type";
        inr (Γn, Γ, Γf, <[f:=s]>δ, m, xs)
     | None => inr (Γn, Γ, Γf, δ, m, xs)
     end
  end.
Definition to_envs (Θ : list (N * decl Ti)) :
    string + env Ti * funtypes Ti * funenv Ti * mem Ti :=
  '(_,Γ,Γf,δ,m,_) ← to_envs_go Θ;
  guard (dom funset Γf ⊆ dom funset δ)
    with "not all function prototypes completed";
  inr (Γ,Γf,δ,m).
End frontend_more.

Section cexpr_ind.
Context {Ti : Set} (P : cexpr Ti → Prop) (Q : ctype Ti → Prop).
Context (Pvar : ∀ x, P (CEVar x)).
Context (Pconst : ∀ τi x, P (CEConst τi x)).
Context (Psizeof : ∀ cτ, Q cτ → P (CESizeOf cτ)).
Context (Paddrof : ∀ ce, P ce → P (CEAddrOf ce)).
Context (Pderef : ∀ ce, P ce → P (CEDeref ce)).
Context (Passign : ∀ ass ce1 ce2, P ce1 → P ce2 → P (CEAssign ass ce1 ce2)).
Context (Pcall : ∀ f ces, Forall P ces → P (CECall f ces)).
Context (Palloc : ∀ cτ ce, Q cτ → P ce → P (CEAlloc cτ ce)).
Context (Pfree : ∀ ce, P ce → P (CEFree ce)).
Context (Punop : ∀ op ce, P ce → P (CEUnOp op ce)).
Context (Pbinop : ∀ op ce1 ce2, P ce1 → P ce2 → P (CEBinOp op ce1 ce2)).
Context (Pif : ∀ ce1 ce2 ce3, P ce1 → P ce2 → P ce3 → P (CEIf ce1 ce2 ce3)).
Context (Pcomma : ∀ ce1 ce2, P ce1 → P ce2 → P (CEComma ce1 ce2)).
Context (Pand : ∀ ce1 ce2, P ce1 → P ce2 → P (CEAnd ce1 ce2)).
Context (Por : ∀ ce1 ce2, P ce1 → P ce2 → P (CEOr ce1 ce2)).
Context (Pcast : ∀ cτ ce, Q cτ → P ce → P (CECast cτ ce)).
Context (Pfield : ∀ ce i, P ce → P (CEField ce i)).
Context (Qvoid : Q CTVoid).
Context (Qdef : ∀ x, Q (CTDef x)).
Context (Qenum : ∀ s, Q (CTEnum s)).
Context (Qint : ∀ τi, Q (CTInt τi)).
Context (Qptr : ∀ cτ, Q cτ → Q (CTPtr cτ)).
Context (Qarray : ∀ cτ ce, Q cτ → P ce → Q (CTArray cτ ce)).
Context (Qcompound : ∀ c s, Q (CTCompound c s)).
Context (Qtypeof : ∀ ce, P ce → Q (CTTypeOf ce)).

Fixpoint cexpr_ind_alt ce : P ce :=
  match ce return P ce with
  | CEVar _ => Pvar _
  | CEConst _ _ => Pconst _ _
  | CESizeOf cτ => Psizeof _ (ctype_ind_alt cτ)
  | CEAddrOf ce => Paddrof _ (cexpr_ind_alt ce)
  | CEDeref ce => Pderef _ (cexpr_ind_alt ce)
  | CEAssign _ ce1 ce2 => Passign _ _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CECall f ces => Pcall _ ces $ list_ind (Forall P)
      (Forall_nil_2 _) (λ ce _, Forall_cons_2 _ _ _ (cexpr_ind_alt ce)) ces
  | CEAlloc cτ ce => Palloc _ _ (ctype_ind_alt cτ) (cexpr_ind_alt ce)
  | CEFree ce => Pfree _ (cexpr_ind_alt ce)
  | CEUnOp _ ce => Punop _ _ (cexpr_ind_alt ce)
  | CEBinOp _ ce1 ce2 => Pbinop _ _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CEIf ce1 ce2 ce3 =>
     Pif _ _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2) (cexpr_ind_alt ce3)
  | CEComma ce1 ce2 => Pcomma _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CEAnd ce1 ce2 => Pand _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CEOr ce1 ce2 => Por _ _ (cexpr_ind_alt ce1) (cexpr_ind_alt ce2)
  | CECast cτ ce => Pcast _ _ (ctype_ind_alt cτ) (cexpr_ind_alt ce)
  | CEField ce _ => Pfield _ _ (cexpr_ind_alt ce)
  end
with ctype_ind_alt cτ : Q cτ :=
  match cτ with
  | CTVoid => Qvoid
  | CTDef _ => Qdef _
  | CTEnum _ => Qenum _
  | CTInt _ => Qint _
  | CTPtr cτ => Qptr _ (ctype_ind_alt cτ)
  | CTArray cτ ce => Qarray _ _ (ctype_ind_alt cτ) (cexpr_ind_alt ce)
  | CTCompound _ _ => Qcompound _ _
  | CTTypeOf ce => Qtypeof _ (cexpr_ind_alt ce)
  end.
Lemma cexpr_ctype_ind : (∀ ce, P ce) ∧ (∀ cτ, Q cτ).
Proof. auto using cexpr_ind_alt, ctype_ind_alt. Qed.
End cexpr_ind.

Section properties.
Context `{EnvSpec Ti}.
Implicit Types Γ : env Ti.
Implicit Types Γf : funtypes Ti.
Implicit Types o : index.
Implicit Types m : mem Ti.
Implicit Types e : expr Ti.
Implicit Types ce : cexpr Ti.
Implicit Types s : stmt Ti.
Implicit Types τi : int_type Ti.
Implicit Types τ σ : type Ti.
Implicit Types cτ : ctype Ti.
Implicit Types τlr : lrtype Ti.

Arguments to_R _ _ : simpl never.
Arguments convert_ptrs _ _ _ _ : simpl never.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.
Hint Extern 1 (int_typed _ _) => by apply int_typed_small.
Hint Extern 10 (cast_typed _ _ _) => constructor.
Hint Extern 10 (base_cast_typed _ _ _) => constructor.

Definition var_decl_valid (Γ : env Ti) (d : var_decl Ti) :=
  match d with
  | Global _ => True
  | Local τ => ✓{Γ} τ
  | EnumVal τi z => int_typed z τi
  | TypeDef τ => ✓{Γ} τ
  end.
Notation var_env_valid Γ := (Forall (var_decl_valid Γ ∘ snd)).
Lemma var_decl_valid_weaken Γ1 Γ2 d :
  var_decl_valid Γ1 d → Γ1 ⊆ Γ2 → var_decl_valid Γ2 d.
Proof. destruct d; simpl; eauto using type_valid_weaken. Qed.
Lemma typedef_lookup_valid Γ xs x τ :
  var_env_valid Γ xs → lookup_typedef x xs = Some τ → ✓{Γ} τ.
Proof. induction 1 as [|[? []]]; intros; simplify_option_equality; eauto. Qed.
Lemma var_env_valid_locals Γ (ys : list N) (τs : list (type Ti)) :
  ✓{Γ}* τs → var_env_valid Γ (zip_with (λ y τ, (y, Local τ)) ys τs).
Proof. intros Hτs. revert ys. induction Hτs; intros [|??]; simpl; auto. Qed.
Lemma var_env_valid_enums Γ τi (yzs : list (N * Z)) :
  Forall (λ z, int_typed z τi) (snd <$> yzs) →
  var_env_valid Γ (prod_map id (EnumVal τi) <$> yzs).
Proof. rewrite !Forall_fmap; eauto using Forall_impl. Qed.

Fixpoint var_env_stack_types (xs : var_env Ti) : list (type Ti) :=
  match xs with
  | [] => []
  | (_,Local τ) :: xs => τ :: var_env_stack_types xs
  | (_,_) :: xs => var_env_stack_types xs
  end.
Lemma var_env_stack_types_app xs1 xs2 :
  var_env_stack_types (xs1 ++ xs2)
  = var_env_stack_types xs1 ++ var_env_stack_types xs2.
Proof. induction xs1 as [|[?[]] ??]; f_equal'; auto. Qed.
Lemma var_env_stack_types_locals (ys : list N) (τs : list (type Ti)) :
  length ys = length τs →
  var_env_stack_types (zip_with (λ y τ, (y, Local τ)) ys τs) = τs.
Proof. rewrite <-Forall2_same_length. induction 1; f_equal'; auto. Qed.
Lemma var_env_stack_types_enums τi (yzs : list (N * Z)) :
  var_env_stack_types ((prod_map id (EnumVal τi) <$> yzs)) = [].
Proof. induction yzs; f_equal'; auto. Qed.
Lemma var_env_stack_types_valid Γ xs :
  var_env_valid Γ xs → ✓{Γ}* (var_env_stack_types xs).
Proof. induction 1 as [|[? []]]; simpl; auto. Qed.

Lemma to_R_typed Γ Γf m τs e τlr e' τ' :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs →
  to_R (e,τlr) = (e',τ') → (Γ,Γf,m,τs) ⊢ e : τlr → (Γ,Γf,m,τs) ⊢ e' : inr τ'.
Proof.
  unfold to_R; intros; destruct τlr as [τl|τr]; simplify_equality'; auto.
  destruct (maybe_TArray τl) as [[τ n]|] eqn:Hτ; simplify_equality'.
  { destruct τl; simplify_equality'. repeat typed_constructor; eauto.
    apply Nat.neq_0_lt_0.
    eauto using TArray_valid_inv_size, expr_inl_typed_type_valid. }
  by typed_constructor.
Qed.
Lemma to_R_NULL_typed Γ Γf m τs σ e τlr e' τ' :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs →
  to_R_NULL σ (e,τlr) = (e',τ') → ptr_type_valid Γ σ →
  (Γ,Γf,m,τs) ⊢ e : τlr → (Γ,Γf,m,τs) ⊢ e' : inr τ'.
Proof.
  unfold to_R_NULL. destruct (to_R (e,τlr)) as [e'' τ''] eqn:?.
  destruct 5 as [σb Hσb| |]; simplify_equality'; eauto 2 using to_R_typed.
  destruct Hσb; repeat case_match; simplify_equality'; eauto 2 using to_R_typed.
  by repeat typed_constructor.
Qed.
Lemma var_lookup_typed Γ Γf m xs x e τlr :
  ✓ Γ → ✓{Γ} m → var_env_valid Γ xs → lookup_var m x 0 xs = Some (e,τlr) →
  (Γ,Γf,m,var_env_stack_types xs) ⊢ e : τlr.
Proof.
  intros ?? Hxs. cut (∀ τs', lookup_var m x (length τs') xs = Some (e,τlr) →
    (Γ,Γf,m,τs' ++ var_env_stack_types xs) ⊢ e : τlr).
  { intros help. apply (help []). }
  induction Hxs as [|[x' [o|τ|τi z|]] ? xs ? IH];
    intros τs' ?; simplify_option_equality; eauto 2.
  * typed_constructor; eauto using addr_top_typed, addr_top_strict,
      index_typed_valid, index_typed_representable.
  * typed_constructor. by rewrite list_lookup_middle.
  * rewrite cons_middle, (associative_L (++)). apply (IH (τs' ++ [τ])).
    rewrite app_length; simpl. by rewrite Nat.add_comm.
  * by repeat typed_constructor.
Qed.
Lemma convert_ptrs_typed Γ Γf m τs e1 τ1 e2 τ2 e1' e2' τ' :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs →
  convert_ptrs (e1,τ1) (e2,τ2) = Some (e1', e2', τ') →
  (Γ,Γf,m,τs) ⊢ e1 : inr τ1 → (Γ,Γf,m,τs) ⊢ e2 : inr τ2 →
  (Γ,Γf,m,τs) ⊢ e1' : inr τ' ∧ (Γ,Γf,m,τs) ⊢ e2' : inr τ'.
Proof.
  unfold convert_ptrs; destruct τ1 as [[|τp1|]| |], τ2 as [[|τp2|]| |]; intros;
    simplify_option_equality; split; repeat typed_constructor;
    eauto using TPtr_valid_inv, TBase_valid_inv, expr_inr_typed_type_valid.
Qed.
Lemma to_if_expr_typed Γ Γf m τs e1 τb e2 τ2 e3 τ3 e τlr :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs →
  to_if_expr e1 (e2,τ2) (e3,τ3) = Some (e,τlr) →
  (Γ,Γf,m,τs) ⊢ e1 : inr (baseT τb) → (Γ,Γf,m,τs) ⊢ e2 : inr τ2 →
  (Γ,Γf,m,τs) ⊢ e3 : inr τ3 → (Γ,Γf,m,τs) ⊢ e : τlr.
Proof.
  unfold to_if_expr; intros;
    repeat match goal with
    | _ => progress simplify_option_equality
    | _ => case_match
    | x : (_ * _)%type |- _ => destruct x
    | H : convert_ptrs _ _ = Some _ |- _ =>
       eapply convert_ptrs_typed in H; eauto; destruct H
    end; typed_constructor; eauto.
Qed.
Lemma to_binop_expr_typed Γ Γf m τs op e1 τ1 e2 τ2 e τlr :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs →
  to_binop_expr op (e1,τ1) (e2,τ2) = Some (e,τlr) →
  (Γ,Γf,m,τs) ⊢ e1 : inr τ1 → (Γ,Γf,m,τs) ⊢ e2 : inr τ2 →
  (Γ,Γf,m,τs) ⊢ e : τlr.
Proof.
  unfold to_binop_expr; intros;
    repeat match goal with
    | _ => progress simplify_option_equality
    | x : (_ * _)%type |- _ => destruct x
    | H: binop_type_of _ _ _ = Some _ |- _ => apply binop_type_of_correct in H
    | H : convert_ptrs _ _ = Some _ |- _ =>
       eapply convert_ptrs_typed in H; eauto; destruct H
    end; typed_constructor; eauto.
Qed.
Lemma to_expr_type_typed Γn Γ Γf m xs :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ} m → var_env_valid Γ xs →
  (∀ ce e τlr, to_expr Γn Γ Γf m xs ce = inr (e,τlr) →
    (Γ,Γf,m,var_env_stack_types xs) ⊢ e : τlr) ∧
  (∀ cτ,
    (∀ τ, to_type Γn Γ Γf m xs false cτ = inr τ → ✓{Γ} τ) ∧
    (∀ τ, to_type Γn Γ Γf m xs true cτ = inr τ → ptr_type_valid Γ τ)).
Proof.
  intros ????. assert (∀ f ces τs τ eτlrs,
     Γf !! f = Some (τs, τ) →
     Forall (λ ce, ∀ e τlr, to_expr Γn Γ Γf m xs ce = inr (e,τlr) →
       (Γ,Γf,m,var_env_stack_types xs) ⊢ e : τlr) ces →
     Forall2 (cast_typed Γ) (snd <$> zip_with to_R_NULL τs eτlrs) τs →
     mapM (to_expr Γn Γ Γf m xs) ces = inr eτlrs →
     (Γ,Γf,m,var_env_stack_types xs) ⊢*
       cast{τs}* (fst <$> zip_with to_R_NULL τs eτlrs) :* inr <$> τs).
  { intros f ces τs τ eτlrs. rewrite mapM_inr. intros Hf ? Hcast Hces.
    assert (Forall (ptr_type_valid Γ) τs) as Hτs by eauto using Forall_impl,
      type_valid_ptr_type_valid, funtypes_valid_args_valid; clear Hf.
    revert τs Hτs Hcast.
    induction Hces as [|? [??]]; intros [|??] ??; decompose_Forall_hyps;
      constructor; eauto using ECast_typed, to_R_NULL_typed,
      surjective_pairing, var_env_stack_types_valid. }
  assert (✓{Γ}* (var_env_stack_types xs))
    by eauto using var_env_stack_types_valid.
  apply cexpr_ctype_ind; intros; split_ands; intros;
    repeat match goal with
    | H : _ ∧ _ |- _ => destruct H
    | _ : maybe_inl ?τlr = Some _ |- _ => is_var τlr; destruct τlr
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ : maybe_TPtr ?τb = Some _ |- _ => is_var τb; destruct τb
    | _ : maybe_TInt ?τb = Some _ |- _ => is_var τb; destruct τb
    | _ : maybe_TCompound ?τ = Some _ |- _ => is_var τ; destruct τ
    | H : ∀ _, inr _ = inr _ → _ |- _ => specialize (H _ eq_refl)
    | H : ∀ _ _, inr _ = inr _ → _ |- _ => specialize (H _ _ eq_refl)
    | H: assign_type_of _ _ _ _ = Some _ |- _ =>
       apply assign_type_of_correct in H
    | H: unop_type_of _ _ = Some _ |- _ => apply unop_type_of_correct in H
    | H: binop_type_of _ _ _ = Some _ |- _ => apply binop_type_of_correct in H
    | H: to_R_NULL _ _ = _ |- _ =>
       first_of ltac:(eapply to_R_NULL_typed in H) idtac
         ltac:(by eauto using type_valid_ptr_type_valid)
    | _ => progress simplify_error_equality
    | _ => progress (simplify_option_equality by fail)
    | _ => progress case_match
    | x : (_ * _)%type |- _ => destruct x
    | _ : _ ⊢ _ : ?τlr |- _ =>
       unless (✓{Γ} (lrtype_type τlr)) by assumption;
       assert (✓{Γ} (lrtype_type τlr)) by eauto using expr_typed_type_valid
    | _ : context [to_R ?eτlr] |- _ => 
       let H := fresh in destruct (to_R eτlr) eqn:H;
       first_of ltac:(eapply to_R_typed in H) idtac ltac:(by eauto)
    end;
    try match goal with
    | |- _ ⊢ _ : _ =>
       repeat typed_constructor; eauto using to_binop_expr_typed,
         to_if_expr_typed, var_lookup_typed, type_valid_ptr_type_valid
    | |- ✓{_} _ =>
       repeat constructor; eauto using typedef_lookup_valid, TBase_valid_inv
    | |- ptr_type_valid _ _ =>
       repeat constructor; eauto using type_valid_ptr_type_valid,
         typedef_lookup_valid
    end.
Qed.
Lemma to_expr_typed Γn Γ Γf m xs ce e τlr :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ} m → var_env_valid Γ xs →
  to_expr Γn Γ Γf m xs ce = inr (e,τlr) →
  (Γ,Γf,m,var_env_stack_types xs) ⊢ e : τlr.
Proof. intros. eapply to_expr_type_typed; eauto. Qed.
Lemma to_type_valid Γn Γ Γf m xs cτ τ :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ} m → var_env_valid Γ xs →
  to_type Γn Γ Γf m xs false cτ = inr τ → ✓{Γ} τ.
Proof. intros. eapply to_expr_type_typed; eauto. Qed.
Lemma to_types_valid Γn Γ Γf m xs cτs τs :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ} m → var_env_valid Γ xs →
  mapM (to_type Γn Γ Γf m xs false) cτs = inr τs → ✓{Γ}* τs.
Proof. rewrite mapM_inr. induction 5; eauto using to_type_valid. Qed.

Lemma alloc_global_typed Γn Γ m xs x τ mce m' xs' :
  ✓ Γ → alloc_global Γn Γ m xs x τ mce = inr (m',xs') →
  ✓{Γ} m → var_env_valid Γ xs → ✓{Γ} τ →
  (**i 1.) *) ✓{Γ} m' ∧
  (**i 2.) *) (∀ o σ, m ⊢ o : σ → m' ⊢ o : σ) ∧
  (**i 3.) *) var_env_valid Γ xs' ∧
  (**i 4.) *) var_env_stack_types xs = var_env_stack_types xs'.
Proof.
  assert (mem_allocable (fresh (dom indexset m)) m).
  { eapply mem_allocable_alt, is_fresh. }
  destruct mce as [ce|]; intros; simplify_equality'.
  * repeat case_error_guard; simplify_equality'.
    destruct (to_expr Γn Γ ∅ m xs ce) as [|[e τlr]] eqn:?; simplify_equality'.
    destruct (to_R_NULL τ (e, τlr)) as [e' τ'] eqn:?.
    repeat case_error_guard; simplify_equality'.
    destruct (⟦ e' ⟧ Γ ∅ [] m) as [[?|v]|] eqn:?; simplify_equality'.
    repeat case_option_guard; simplify_equality'.
    assert ((Γ,m) ⊢ inr v : inr τ'); [|typed_inversion_all].
    { eapply (expr_eval_typed_aux Γ ∅ [] (var_env_stack_types xs) ∅);
        eauto using to_R_NULL_typed, type_valid_ptr_type_valid, to_expr_typed,
        prefix_of_nil, funtypes_valid_empty, var_env_stack_types_valid.
      by intros ?; simpl_map. }
    split_ands; eauto using mem_alloc_val_valid,
      index_typed_alloc_val, val_cast_typed; by repeat constructor.
  * repeat case_error_guard; simplify_equality'.
    split_ands; eauto using mem_alloc_val_valid,
      index_typed_alloc_val, val_0_typed; by repeat constructor.
Qed.
Lemma to_stmt_typed Γn Γ Γf τret m xs Ls mLc mLb cs m' s cmτ :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ} m → var_env_valid Γ xs →
  to_stmt Γn Γ Γf τret m xs Ls mLc mLb cs = inr (m',s,cmτ) →
  (**i 1.) *) (Γ,Γf,m',var_env_stack_types xs) ⊢ s : cmτ ∧
  (**i 2.) *) ✓{Γ} m' ∧
  (**i 3.) *) (∀ o σ, m ⊢ o : σ → m' ⊢ o : σ).
Proof.
  intros ??. revert m m' s cmτ xs Ls mLc mLb. induction cs; intros;
    repeat match goal with
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ => progress simplify_error_equality
    | _ => progress (simplify_option_equality by fail)
    | x : (_ * _)%type |- _ => destruct x
    | IH : ∀ _ _ _ _ _ _ _ _,
        ✓{_} _ → _ → to_stmt _ _ _ _ _ _ _ _ _ ?cs = inr _ → _,
      H : to_stmt _ _ _ _ _ _ _ _ _ ?cs = inr _ |- _ =>
       destruct (λ Hm Hxs, IH _ _ _ _ _ _ _ _ Hm Hxs H) as (?&?&?); clear IH;
         simpl; [by auto|by auto with congruence|]
    | H : to_expr _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply to_expr_typed in H; simpl) idtac ltac:(by auto)
    | H : to_type _ _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply to_type_valid in H; simpl) idtac ltac:(by auto)
    | H: to_R _ = _, _ : (_,_,_,?τs) ⊢ _ : _ |- _ =>
       first_of ltac:(eapply (to_R_typed _ _ _ τs) in H) idtac
         ltac:(by eauto using var_env_stack_types_valid)
    | H : alloc_global _ _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply alloc_global_typed in H) idtac ltac:(by auto);
       destruct H as (?&?&?&?)
    | _ => case_match
    end; try solve [split_ands; eauto using to_R_typed, to_expr_typed].
  * split_ands; eauto with congruence.
  * split_ands; eauto 2. eapply SBlock_typed; eauto 2.
    repeat typed_constructor; eauto using expr_typed_weaken, subseteq_empty.
    by constructor.
  * split_ands; eauto using stmt_typed_weaken.
  * split_ands; repeat typed_constructor;
      eauto using expr_typed_weaken, rettype_union_l.
  * split_ands; repeat typed_constructor;
      eauto using expr_typed_weaken, rettype_union_l.
  * split_ands; repeat typed_constructor;
      eauto using expr_typed_weaken, rettype_union_l.
  * split_ands; repeat typed_constructor;
      eauto using stmt_typed_weaken, expr_typed_weaken.
Qed.
Lemma extend_funtypes_typed Γ m f τs τ Γf Γf' :
  ✓{Γ} Γf → extend_funtypes Γ f τs τ Γf = inr Γf' → ✓{Γ}* τs → ✓{Γ} τ →
  (**i 1.) *) Γf ⊆ Γf' ∧
  (**i 2.) *) ✓{Γ} Γf' ∧
  (**i 3.) *) Γf' !! f = Some (τs,τ) ∧
  (**i 4.) *) Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs.
Proof.
  unfold extend_funtypes; intros HΓf ???.
  destruct (Γf !! f) as [[]|] eqn:?; simplify_error_equality; auto.
  { destruct (HΓf f (τs,τ)); naive_solver. }
  simpl_map; split_ands; eauto using insert_subseteq, funtypes_valid_insert.
Qed.
Lemma to_envs_go_typed Θ Γn Γ Γf δ m xs :
  to_envs_go Θ = inr (Γn,Γ,Γf,δ,m,xs) →
  (**i 1.) *) ✓ Γ ∧
  (**i 2.) *) ✓{Γ} Γf ∧
  (**i 3.) *) funenv_pretyped Γ m δ Γf ∧
  (**i 4.) *) ✓{Γ} m ∧
  (**i 5.) *) var_env_valid Γ xs ∧
  (**i 6.) *) var_env_stack_types xs = [].
Proof.
  revert Γn Γ Γf δ m xs.
  induction Θ as [|[x [cτys|τi yzs|cτ|cτ mce|cτys cσ mcs]] Θ IH];
    intros Γn Γ Γf δ m xs ?; simplify_equality'.
  * split_ands; eauto using env_empty_valid,
      cmap_empty_valid, funtypes_valid_empty, funenv_pretyped_empty.
  * destruct (to_envs_go Θ) as [|[[[[[Γn2 Γ2] ?] ?] ?] ?]]; simplify_equality'.
    destruct (mapM _ _) as [|τs] eqn:?; simplify_error_equality.
    destruct (IH Γn2 Γ2 Γf δ m xs) as (?&?&?&?&?&?); eauto.
    assert (✓ (<[x:tag:=τs]> Γ2)) by (constructor; eauto using to_types_valid).
    simpl in *; split_ands; auto.
    + eauto using funtypes_valid_weaken, insert_subseteq.
    + eauto using funenv_pretyped_weaken, insert_subseteq.
    + eauto using cmap_valid_weaken, insert_subseteq.
    + eauto using Forall_impl, var_decl_valid_weaken, insert_subseteq.
  * destruct (to_envs_go Θ) as [|[[[[[Γn2 ?] ?] ?] ?] xs2]]; simplify_equality'.
    repeat case_error_guard; simplify_equality'.
    destruct (IH Γn2 Γ Γf δ m xs2) as (?&?&?&?&?&Hxs); eauto.
    split_ands; auto.
    + auto using Forall_app_2, var_env_valid_enums.
    + by rewrite var_env_stack_types_app, Hxs, var_env_stack_types_enums.
  * destruct (to_envs_go Θ) as [|[[[[[??] ?] ?] ?] xs2]]; simplify_equality'.
    repeat case_error_guard; simplify_equality'.
    destruct (to_type _ _ _ _ _ _ _) as [τ|] eqn:?; simplify_equality'.
    destruct (IH Γn Γ Γf δ m xs2) as (?&?&?&?&?&?); eauto.
    split_ands; auto. constructor; simpl; eauto using to_type_valid.
  * destruct (to_envs_go Θ)
      as [|[[[[[Γn2 Γ2] Γf2] δ2] m2] xs2]]; simplify_equality'.
    repeat case_error_guard; simplify_equality'.
    destruct (to_type _ _ _ _ _ _ _) as [|τ] eqn:?; simplify_equality'.
    destruct (alloc_global _ _ _ _ _ _ _) as [|[??]] eqn:?; simplify_equality'.
    destruct (IH Γn Γ Γf δ m2 xs2) as (?&?&?&?&?&?); eauto.
    destruct (alloc_global_typed Γn Γ m2 xs2 x τ mce m xs)
      as (?&?&?&<-); eauto 7 using funenv_pretyped_weaken, to_type_valid.
  * destruct (to_envs_go Θ)
      as [|[[[[[Γn2 Γ2] Γf2] δ2] m2] xs2]]; simplify_equality'.
    destruct (mapM _ _) as [|τs] eqn:?; simplify_equality'.
    destruct (IH Γn2 Γ2 Γf2 δ2 m2 xs2) as (?&?&?&?&?&?Hxs2); eauto.
    repeat case_error_guard; simplify_equality'.
    destruct (to_type _ _ _ _ _ _ _) as [|σ] eqn:?; simplify_equality'.
    destruct (extend_funtypes _ _ _ _ _) as [|Γf3] eqn:?; simplify_equality'.
    destruct (extend_funtypes_typed Γ2 m2 x τs σ Γf2 Γf3) as (?&?&?&?);
      eauto using to_types_valid, to_type_valid.
    destruct mcs as [cs|]; simplify_equality';
      [|split_ands; eauto using funenv_pretyped_weaken].
    destruct (to_stmt _ _ _ _ _ _ _ _ _ _)
      as [|[[m3 s] cmσ]] eqn:?; simplify_error_equality.
    assert (length (fst <$> cτys) = length τs).
    { by erewrite <-(error_mapM_length _ _ τs), !fmap_length by eauto. }
    destruct (to_stmt_typed Γn Γ Γf σ m2
      (zip_with (λ y τ, (y, Local τ)) (fst <$> cτys) τs ++ xs)
      (labels cs) None None cs m s cmσ) as (Hs&?&?); auto.
    { eauto using Forall_app_2, var_env_valid_locals, to_types_valid. }
    rewrite var_env_stack_types_app,
      var_env_stack_types_locals, Hxs2, (right_id_L [] (++)) in Hs by done.
    split_ands; eauto using funenv_pretyped_weaken,
      funenv_pretyped_insert, to_types_valid, to_type_valid.
Qed.
Lemma to_envs_typed Θ Γ Γf δ m :
  to_envs Θ = inr (Γ,Γf,δ,m) → ✓ Γ ∧ (Γ,m) ⊢ δ : Γf ∧ ✓{Γ} m.
Proof.
  unfold to_envs. intros. destruct (to_envs_go _)
    as [|[[[[[Γn Γ2] Γf2] δ2] m2] xs]] eqn:?; simplify_error_equality.
  destruct (to_envs_go_typed Θ Γn Γ Γf δ m xs) as (?&?&?&?&?); auto.
Qed.
End properties.
