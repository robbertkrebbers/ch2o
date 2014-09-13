(* Copyright (c) 2012-2014, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String stringmap.
Require Export type_system_decidable expression_eval error.
Local Open Scope string_scope.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Local Open Scope list_scope.

Inductive cint_rank : Set :=
  | CCharRank | CShortRank | CIntRank | CLongRank : nat → cint_rank | CPtrRank.
Inductive cint_type :=
  CIntType { csign : option signedness; crank : cint_rank }.

Inductive cexpr : Set :=
  | CEVar : string → cexpr
  | CEConst : signedness → nat → Z → cexpr
  | CESizeOf : ctype → cexpr
  | CEMin : cint_type → cexpr
  | CEMax : cint_type → cexpr
  | CEBits : cint_type → cexpr
  | CEAddrOf : cexpr → cexpr
  | CEDeref : cexpr → cexpr
  | CEAssign : assign → cexpr → cexpr → cexpr
  | CECall : string → list cexpr → cexpr
  | CEAlloc : ctype → cexpr → cexpr
  | CEFree : cexpr → cexpr
  | CEUnOp : unop → cexpr → cexpr
  | CEBinOp : binop → cexpr → cexpr → cexpr
  | CEIf : cexpr → cexpr → cexpr → cexpr
  | CEComma : cexpr → cexpr → cexpr
  | CEAnd : cexpr → cexpr → cexpr
  | CEOr : cexpr → cexpr → cexpr
  | CECast : ctype → cexpr → cexpr
  | CEField : cexpr → string → cexpr
with ctype : Set :=
  | CTVoid : ctype
  | CTDef : string → ctype
  | CTEnum : string → ctype
  | CTInt : cint_type → ctype
  | CTPtr : ctype → ctype
  | CTArray : ctype → cexpr → ctype
  | CTCompound : compound_kind → string → ctype
  | CTTypeOf : cexpr → ctype.

Inductive cstorage := StaticStorage | ExternStorage | AutoStorage.

Inductive cstmt : Set :=
  | CSDo : cexpr → cstmt
  | CSSkip : cstmt
  | CSGoto : string → cstmt
  | CSBreak : cstmt
  | CSContinue : cstmt
  | CSReturn : option cexpr → cstmt
  | CSBlock : cstorage → string → ctype → option cexpr → cstmt → cstmt
  | CSTypeDef : string → ctype → cstmt → cstmt
  | CSComp : cstmt → cstmt → cstmt
  | CSLabel : string → cstmt → cstmt
  | CSWhile : cexpr → cstmt → cstmt
  | CSFor : cexpr → cexpr → cexpr → cstmt → cstmt
  | CSDoWhile : cstmt → cexpr → cstmt
  | CSIf : cexpr → cstmt → cstmt → cstmt.

Inductive decl : Set :=
  | CompoundDecl : compound_kind → list (string * ctype) → decl
  | EnumDecl : cint_type → list (string * option cexpr) → decl
  | TypeDefDecl : ctype → decl
  | GlobDecl : ctype → option cexpr → decl
  | FunDecl : list (option string * ctype) → ctype → option cstmt → decl.

Inductive global_decl (Ti : Set): Set :=
  | Global : index → type Ti → bool → global_decl Ti
  | Fun : list (type Ti) → type Ti → option (stmt Ti) → global_decl Ti
  | GlobalTypeDef : type Ti → global_decl Ti
  | EnumVal : int_type Ti → Z → global_decl Ti.
Arguments Global {_} _ _ _.
Arguments Fun {_} _ _ _.
Arguments GlobalTypeDef {_} _.
Arguments EnumVal {_} _ _.
Definition maybe_Fun {Ti} (d : global_decl Ti) :
    option (list (type Ti) * type Ti * option (stmt Ti)) :=
  match d with Fun τs τ ms => Some (τs,τ,ms) | _ => None end.
Definition maybe_GlobalTypeDef {Ti} (d : global_decl Ti) : option (type Ti) :=
  match d with GlobalTypeDef τ => Some τ | _ => None end.
Notation global_env Ti := (stringmap (global_decl Ti)).

Inductive local_decl (Ti : Set) : Set :=
  | Static : index → type Ti → local_decl Ti
  | Local : type Ti → local_decl Ti
  | TypeDef : type Ti → local_decl Ti.
Arguments Static {_} _ _.
Arguments Local {_} _.
Arguments TypeDef {_} _.
Definition maybe_TypeDef {Ti} (d : local_decl Ti) : option (type Ti) :=
  match d with TypeDef τ => Some τ | _ => None end.
Notation local_env Ti := (list (string * local_decl Ti))%type.

Inductive compound_type (Ti : Set) : Set :=
  | CompoundType : compound_kind → list string → compound_type Ti
  | EnumType : int_type Ti → compound_type Ti.
Arguments CompoundType {_} _ _.
Arguments EnumType {_} _.
Definition maybe_CompoundType {Ti}
    (t : compound_type Ti) : option (compound_kind * list string) :=
  match t with CompoundType c xs => Some (c,xs) | _ => None end.
Definition maybe_EnumType {Ti} (t : compound_type Ti) : option (int_type Ti) :=
  match t with EnumType τi => Some τi | _ => None end.
Notation compound_env Ti := (tagmap (compound_type Ti)).

Section frontend.
Context `{Env Ti}.

Definition to_funtypes : global_env Ti → funtypes Ti :=
  omap (λ d, '(τs,τ,_) ← maybe_Fun d; Some (τs,τ)).
Definition to_funenv : global_env Ti → funenv Ti :=
  omap (λ d, '(_,_,ms) ← maybe_Fun d; ms).
Definition global_decl_complete (d : global_decl Ti) : bool :=
  match d with Fun _ _ None => false | _ => true end.
Definition global_env_complete : global_env Ti → Prop :=
  map_Forall (λ _, global_decl_complete).

Fixpoint lookup_var (x : string) (i : nat)
    (Δl : local_env Ti) : option (expr Ti * type Ti) :=
  match Δl with
  | [] => None
  | (y,Static o τ) :: Δl =>
     if decide (x = y) then Some (% (addr_top o τ), τ) else lookup_var x i Δl
  | (y,Local τ) :: Δl =>
     if decide (x = y) then Some (var{τ} i, τ) else lookup_var x (S i) Δl
  | (y,TypeDef _) :: Δl =>
     if decide (x = y) then None else lookup_var x i Δl
  end.
Fixpoint lookup_typedef (x : string) (Δl : local_env Ti) : option (type Ti) :=
  match Δl with
  | [] => None
  | (y,d) :: Δl =>
     if decide (x = y) then maybe_TypeDef d else lookup_typedef x Δl
  end.
Definition lookup_var' (x : string)
    (Δg : global_env Ti) (Δl : local_env Ti) : option (expr Ti * lrtype Ti) :=
  match lookup_var x 0 Δl with
  | Some (e,τ) => Some (e,inl τ)
  | None =>
     match Δg !! x with
     | Some (Global o τ _) => Some (% (addr_top o τ), inl τ)
     | Some (EnumVal τi z) => Some (# intV{τi} z, inr (intT τi))
     | _ => None
     end
  end.
Definition lookup_typedef' (x : string)
    (Δg : global_env Ti) (Δl : local_env Ti) : option (type Ti) :=
  match lookup_typedef x Δl with
  | Some τ => Some τ | None => Δg !! x ≫= maybe_GlobalTypeDef
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

Definition int_const_types (s : signedness) (n : nat) : list (int_type Ti) :=
  match n with
  | 0 => [IntType s int_rank; IntType s (long_rank 0); IntType s (long_rank 1)]
  | 1 => [IntType s (long_rank 0); IntType s (long_rank 1)]
  | S n => [IntType s (long_rank n)]
  end.
Definition to_int_const (x : Z) : list (int_type Ti) → option (int_type Ti) :=
  fix go τis :=
  match τis with
  | [] => None
  | τi :: τis => if decide (int_typed x τi) then Some τi else go τis
  end.

Definition to_inttype (cτi : cint_type) : int_type Ti :=
  let (ms,k) := cτi in
  match k with
  | CCharRank => IntType (from_option char_signedness ms) char_rank
  | CShortRank => IntType (from_option Signed ms) short_rank
  | CIntRank => IntType (from_option Signed ms) int_rank
  | CLongRank n => IntType (from_option Signed ms) (long_rank n)
  | CPtrRank => IntType (from_option Signed ms) ptr_rank
  end.
End frontend.

(* not in the section because of bug #3488 *)
Inductive to_type_kind := to_Ptr | to_Type (can_be_void : bool).
Instance to_type_kind_dec (k1 k2 : to_type_kind) : Decision (k1 = k2).
Proof. solve_decision. Defined.

Fixpoint to_expr `{Env Ti} (Γn : compound_env Ti) (Γ : env Ti)
    (m : mem Ti) (Δg : global_env Ti) (Δl : local_env Ti)
    (ce : cexpr) : string + expr Ti * lrtype Ti :=
  match ce with
  | CEVar x => error_of_option (lookup_var' x Δg Δl)
      ("variable `" +:+ x +:+ "` not found")
  | CEConst s longs x =>
     let cτis := int_const_types s longs in
     τi ← error_of_option (to_int_const x cτis) "integer constant too large";
     inr (# (intV{τi} x), inr (intT τi))
  | CESizeOf cτ =>
     τ ← to_type Γn Γ m Δg Δl (to_Type false) cτ;
     let sz := size_of Γ τ in
     guard (int_typed sz sptrT) with "argument of size of not in range";
     inr (# (intV{sptrT} sz), inr sptrT)
  | CEMin cτi =>
     let τi := to_inttype cτi in
     inr (#(intV{τi} (int_lower τi)), inr (intT τi))
  | CEMax cτi =>
     let τi := to_inttype cτi in
     inr (#(intV{τi} (int_upper τi - 1)), inr (intT τi))
  | CEBits cτi =>
     let τi := to_inttype cτi in
     inr (#(intV{τi} (int_bits τi)), inr (intT τi))
  | CEDeref ce =>
     '(e,τ) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     τp ← error_of_option (maybe_TBase τ ≫= maybe_TPtr)
       "dereferencing non-pointer type";
     guard (τp ≠ voidT) with "dereferencing pointer with void type";
     guard (type_complete Γ τp) with "dereferencing pointer with incomplete type";
     inr (.* e, inl τp)
  | CEAddrOf ce =>
     '(e,τlr) ← to_expr Γn Γ m Δg Δl ce;
     τ ← error_of_option (maybe_inl τlr) "taking address of r-value";
     inr (& e, inr (τ.*))
  | CEAssign ass ce1 ce2 =>
     '(e1,τlr1) ← to_expr Γn Γ m Δg Δl ce1;
     τ1 ← error_of_option (maybe_inl τlr1) "assigning to r-value";
     '(e2,τ2) ← to_R_NULL τ1 <$> to_expr Γn Γ m Δg Δl ce2;
     σ ← error_of_option (assign_type_of Γ τ1 τ2 ass) "assignment cannot be typed";
     inr (e1 ::={ass} e2, inr σ)
  | CECall f ces =>
     '(τs,σ,_) ← error_of_option (Δg !! f ≫= maybe_Fun)
       ("function `" +:+ f +:+ "` not declared");
     guard (length ces = length τs) with
       ("function `" +:+ f +:+ "` applied to wrong number of arguments");
     eτlrs ← mapM (to_expr Γn Γ m Δg Δl) ces;
     let τes := zip_with to_R_NULL τs eτlrs in 
     guard (Forall2 (cast_typed Γ) (snd <$> τes) τs) with
       ("function `" +:+ f +:+ "` applied to arguments of incorrect type");
     inr (call f @ cast{τs}* (fst <$> τes), inr σ)
  | CEAlloc cτ ce =>
     τ ← to_type Γn Γ m Δg Δl (to_Type false) cτ;
     '(e,τe) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     _ ← error_of_option (maybe_TBase τe ≫= maybe_TInt)
       "alloc applied to argument of non-integer type";
     inr (& (alloc{τ} e), inr (τ.* ))
  | CEFree ce =>
     '(e,τ) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     τp ← error_of_option (maybe_TBase τ ≫= maybe_TPtr)
       "free applied to argument of non-pointer type";
     guard (type_complete Γ τp)
       with "free applied to argument of incomplete pointer type";
     inr (free (.* e), inr voidT)
  | CEUnOp op ce =>
     '(e,τ) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     σ ← error_of_option (unop_type_of op τ) "unary operator cannot be typed";
     inr (@{op} e, inr σ)
  | CEBinOp op ce1 ce2 =>
     eτ1 ← to_R <$> to_expr Γn Γ m Δg Δl ce1;
     eτ2 ← to_R <$> to_expr Γn Γ m Δg Δl ce2;
     error_of_option (to_binop_expr op eτ1 eτ2) "binary operator cannot be typed"
  | CEIf ce1 ce2 ce3 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ m Δg Δl ce1;
     _ ← error_of_option (maybe_TBase τ1)
       "conditional argument of if expression of non-base type";
     eτ2 ← to_R <$> to_expr Γn Γ m Δg Δl ce2;
     eτ3 ← to_R <$> to_expr Γn Γ m Δg Δl ce3;
     error_of_option (to_if_expr e1 eτ2 eτ3) "if expression cannot be typed"
  | CEComma ce1 ce2 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ m Δg Δl ce1;
     '(e2,τ2) ← to_R <$> to_expr Γn Γ m Δg Δl ce2;
     inr (cast{voidT} e1,, e2, inr τ2)
  | CEAnd ce1 ce2 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ m Δg Δl ce1;
     _ ← error_of_option (maybe_TBase τ1) "first argument of && of non-base type";
     '(e2,τ2) ← to_R <$> to_expr Γn Γ m Δg Δl ce2;
     _ ← error_of_option (maybe_TBase τ2) "second argument of && of non-base type";
     inr (if{e1} if{e2} #(intV{sintT} 1) else #(intV{sintT} 0)
           else #(intV{sintT} 0), inr sintT)
  | CEOr ce1 ce2 =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ m Δg Δl ce1;
     _ ← error_of_option (maybe_TBase τ1) "first argument of || of non-base type";
     '(e2,τ2) ← to_R <$> to_expr Γn Γ m Δg Δl ce2;
     _ ← error_of_option (maybe_TBase τ2) "second argument of || of non-base type";
     inr (if{e1} #(intV{sintT} 0)
           else (if{e2} #(intV{sintT} 1) else #(intV{sintT} 0)), inr sintT)
  | CECast cσ ce =>
     σ ← to_type Γn Γ m Δg Δl to_Ptr cσ;
     '(e,τ) ← to_R_NULL σ <$> to_expr Γn Γ m Δg Δl ce;
     guard (maybe_TCompound σ = None) with "cast to struct/union";
     guard (cast_typed Γ τ σ) with "cast cannot be typed";
     inr (cast{σ} e, inr σ)
  | CEField ce x =>
     '(e,τrl) ← to_expr Γn Γ m Δg Δl ce;
     '(c,s) ← error_of_option (maybe_TCompound (lrtype_type τrl))
       "field operator applied to argument of non-compound type";
     σs ← error_of_option (Γ !! s)
       "field operator applied to argument of incomplete compound type";
     '(_,xs) ← error_of_option (Γn !! s ≫= maybe_CompoundType)
       "please report: incompatible environments at field operator";
     i ← error_of_option (list_find (x =) xs)
       ("field operator used with unknown index `" +:+ x +:+ "`");
     σ ← error_of_option (σs !! i)
       "please report: incompatible environments at field operator";
     let rs :=
       match c with
       | Struct_kind => RStruct i s | Union_kind => RUnion i s false
       end in
     match τrl with
     | inl _ => inr (e %> rs, inl σ)
     | inr _ =>
        guard (maybe_TArray σ = None) with
          "indexing array field of r-value struct/union not supported";
        inr (e #> rs, inr σ)
     end
  end
with to_type `{Env Ti} (Γn : compound_env Ti) (Γ : env Ti)
    (m : mem Ti) (Δg : global_env Ti) (Δl : local_env Ti)
    (kind : to_type_kind) (cτ : ctype) : string + type Ti :=
  match cτ with
  | CTVoid =>
     guard (kind ≠ to_Type false) with "non-void type expected";
     inr voidT
  | CTDef x =>
     τ ← error_of_option (lookup_typedef' x Δg Δl)
       ("typedef `" +:+ x +:+ "` not found");
     guard (kind ≠ to_Ptr → type_complete Γ τ) with "complete typedef expected";
     guard (τ = voidT → kind ≠ to_Type false) with "non-void typedef expected";
     inr τ
  | CTEnum s =>
     let s : tag := s in
     τi ← error_of_option (Γn !! s ≫= maybe_EnumType)
       ("enum `" +:+ s +:+ "`not found");
     inr (intT τi)
  | CTInt cτi => inr (intT (to_inttype cτi))
  | CTPtr cτ => τ ← to_type Γn Γ m Δg Δl to_Ptr cτ; inr (τ.* )
  | CTArray cτ ce =>
     τ ← to_type Γn Γ m Δg Δl (to_Type false) cτ;
     '(e,_) ← to_expr Γn Γ m Δg Δl ce;
     v ← error_of_option (⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr)
       "array with non-constant or undefined size expression";
     '(_,x) ← error_of_option (maybe_VBase v ≫= maybe_VInt)
       "array with non-integer size expression";
     let n := Z.to_nat x in
     guard (n ≠ 0) with "array with negative or zero size expression";
     inr (τ.[n])
  | CTCompound c s =>
     let s : tag := s in
     guard (kind ≠ to_Ptr → is_Some (Γ !! s))
       with "complete compound type expected";
     inr (compoundT{c} s)
  | CTTypeOf ce =>
     '(_,τ) ← to_expr Γn Γ m Δg Δl ce;
     inr (lrtype_type τ)
  end.

Section frontend_more.
Context `{Env Ti}.

Definition to_val (Γn : compound_env Ti) (Γ : env Ti)
    (m : mem Ti) (Δg : global_env Ti) (Δl : local_env Ti)
    (ce : cexpr) (τ : type Ti) : string + val Ti :=
  '(e,τ') ← to_R_NULL τ <$> to_expr Γn Γ m Δg Δl ce;
   guard (cast_typed Γ τ' τ)
     with "constant expression of incorrect type";
   error_of_option (⟦ cast{τ} e ⟧ Γ ∅ [] m ≫= maybe_inr)
     "undefined constant expression".
Definition alloc_global (Γn : compound_env Ti) (Γ : env Ti) (m : mem Ti)
    (Δg : global_env Ti) (Δl : local_env Ti) (x : string) (cτ : ctype)
    (mce : option cexpr) : string + mem Ti * global_env Ti * index * type Ti :=
  τ ← to_type Γn Γ m Δg Δl (to_Type false) cτ;
  match Δg !! x with
  | Some (Global o τ' init) =>
     guard (τ = τ') with
       ("global `" +:+ x +:+ "` previously defined with different type");
     match mce with
     | Some ce =>
        guard (init = false) with
          ("global `" +:+ x +:+ "` already initialized");
        v ← to_val Γn Γ m Δg Δl ce τ;
        inr (<[addr_top o τ:=v]{Γ}>m, <[x:=Global o τ true]>Δg, o, τ)
     | None => inr (m, Δg, o, τ)
     end
  | Some (Fun _ _ _) =>
     inl ("global `" +:+ x +:+ "` previously declared as function")
  | Some (GlobalTypeDef _) =>
     inl ("global `" +:+ x +:+ "` previously declared as typedef")
  | Some (EnumVal _ _) =>
     inl ("global `" +:+ x +:+ "` previously declared as enum tag")
  | None =>
     guard (int_typed (size_of Γ τ) sptrT) with
       ("global `" +:+ x +:+ "` whose type that is too large");
     match mce with
     | Some ce =>
        let o := fresh (dom _ m) in
        let m := mem_alloc Γ o false τ m in
        let Δg := <[x:=Global o τ true]>Δg in
        v ← to_val Γn Γ m Δg Δl ce τ;
        inr (<[addr_top o τ:=v]{Γ}>m, Δg, o, τ)
     | None =>
        let o := fresh (dom _ m) in
        inr (<[addr_top o τ:=val_0 Γ τ]{Γ}>(mem_alloc Γ o false τ m),
             <[x:=Global o τ false]>Δg, o, τ)
     end
  end.
Definition alloc_static (Γn : compound_env Ti) (Γ : env Ti) (m : mem Ti)
    (Δg : global_env Ti) (Δl : local_env Ti) (x : string) (cτ : ctype)
    (mce : option cexpr) : string + mem Ti * index * type Ti :=
  τ ← to_type Γn Γ m Δg Δl (to_Type false) cτ;
  guard (int_typed (size_of Γ τ) sptrT) with
    ("static `" +:+ x +:+ "` whose type that is too large");
  match mce with
  | Some ce =>
     let o := fresh (dom _ m) in
     let m := mem_alloc Γ o false τ m in
     let Δl := (x,Local τ) :: Δl in
     v ← to_val Γn Γ m Δg Δl ce τ;
     inr (<[addr_top o τ:=v]{Γ}>m, o, τ)
  | None =>
     let o := fresh (dom _ m) in
     let Δl := (x,Local τ) :: Δl in
     inr (<[addr_top o τ:=val_0 Γ τ]{Γ}>(mem_alloc Γ o false τ m), o, τ)
  end.
Definition to_stmt (Γn : compound_env Ti) (Γ : env Ti) (τret : type Ti) :
    mem Ti → global_env Ti → local_env Ti →
    cstmt → string + mem Ti * global_env Ti * stmt Ti * rettype Ti :=
  fix go m Δg Δl cs {struct cs} :=
  match cs with
  | CSDo ce =>
     '(e,_) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     inr (m, Δg, !(cast{voidT} e), (false, None))
  | CSSkip => inr (m, Δg, skip, (false, None))
  | CSGoto l => inr (m, Δg, goto l, (true, None))
  | CSContinue => inr (m, Δg, break 0, (true, None))
  | CSBreak => inr (m, Δg, break 1, (true, None))
  | CSReturn (Some ce) =>
     '(e,τ') ← to_R_NULL τret <$> to_expr Γn Γ m Δg Δl ce;
     guard (cast_typed Γ τ' τret) with "return expression of incorrect type";
     inr (m, Δg, ret (cast{τret} e), (true, Some τret))
  | CSReturn None => inr (m, Δg, ret (#voidV), (true, Some voidT))
  | CSBlock AutoStorage x cτ None cs =>
     τ ← to_type Γn Γ m Δg Δl (to_Type false) cτ;
     guard (int_typed (size_of Γ τ) sptrT)
       with "block scope declaration whose type is too large";
     '(m,Δg,s,cmσ) ← go m Δg ((x,Local τ) :: Δl) cs;
     inr (m, Δg, block{τ} s, cmσ)
  | CSBlock AutoStorage x cτ (Some ce) cs =>
     τ ← to_type Γn Γ m Δg Δl (to_Type false) cτ;
     guard (int_typed (size_of Γ τ) sptrT) with
       "block scope declaration whose type is too large";
     let Δl := (x,Local τ) :: Δl in
     '(e,τ') ← to_R_NULL τ <$> to_expr Γn Γ m Δg Δl ce;
     guard (cast_typed Γ τ' τ) with
       ("block scope `" +:+ x +:+
                      "` declaration with initializer of incorrect type");
     '(m,Δg,s,cmσ) ← go m Δg Δl cs;
     inr (m, Δg, block{τ} (var{τ} 0 ::= e ;; s), cmσ)
  | CSBlock StaticStorage x cτ mce cs =>
     '(m,o,τ) ← alloc_static Γn Γ m Δg Δl x cτ mce;
     go m Δg ((x,Static o τ) :: Δl) cs
  | CSBlock ExternStorage x cτ mce cs =>
     guard (mce = None) with
       ("extern block scope declaration `" +:+ x +:+ "` with an initializer");
     '(m,Δg,o,τ) ← alloc_global Γn Γ m Δg Δl x cτ None;
     go m Δg ((x,Static o τ) :: Δl) cs
  | CSTypeDef x cτ cs =>
     τ ← to_type Γn Γ m Δg Δl to_Ptr cτ;
     go m Δg ((x,TypeDef τ) :: Δl) cs
  | CSComp cs1 cs2 =>
     '(m,Δg,s1,cmσ1) ← go m Δg Δl cs1;
     '(m,Δg,s2,cmσ2) ← go m Δg Δl cs2;
     mσ ← error_of_option (rettype_union (cmσ1.2) (cmσ2.2))
       "composition of statements with non-matching return types";
     inr (m, Δg, s1 ;; s2, (cmσ2.1, mσ))
  | CSLabel l cs =>
     '(m,Δg,s,cmσ) ← go m Δg Δl cs;
     inr (m, Δg, l :; s, cmσ)
  | CSWhile ce cs =>
     '(e,τ) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     _ ← error_of_option (maybe_TBase τ)
       "while loop with conditional expression of non-base type";
     '(m,Δg,s,cmσ) ← go m Δg Δl cs;
     inr (m, Δg,
       breakto (loop (if{e} skip else break 0 ;; breakto s)),
       (false, cmσ.2))
  | CSFor ce1 ce2 ce3 cs =>
     '(e1,τ1) ← to_R <$> to_expr Γn Γ m Δg Δl ce1;
     '(e2,τ2) ← to_R <$> to_expr Γn Γ m Δg Δl ce2;
     _ ← error_of_option (maybe_TBase τ2)
       "for loop with conditional expression of non-base type";
     '(e3,τ3) ← to_R <$> to_expr Γn Γ m Δg Δl ce3;
     '(m,Δg,s,cmσ) ← go m Δg Δl cs;
     inr (m, Δg,
       !(cast{voidT} e1) ;;
       breakto (loop (
         if{e2} skip else break 0 ;; breakto s ;; !(cast{voidT} e3)
       )),
       (false, cmσ.2))
  | CSDoWhile cs ce =>
     '(m,Δg,s,cmσ) ← go m Δg Δl cs;
     '(e,τ) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     _ ← error_of_option (maybe_TBase τ)
       "do-while loop with conditional expression of non-base type";
     inr (m, Δg,
       breakto (loop (breakto s ;; if{e} skip else break 0)),
       (false, cmσ.2))
  | CSIf ce cs1 cs2 =>
     '(e,τ) ← to_R <$> to_expr Γn Γ m Δg Δl ce;
     _ ← error_of_option (maybe_TBase τ) "if with expression of non-base type";
     '(m,Δg,s1,cmσ1) ← go m Δg Δl cs1;
     '(m,Δg,s2,cmσ2) ← go m Δg Δl cs2;
     mσ ← error_of_option (rettype_union (cmσ1.2) (cmσ2.2))
       "if statement with non-matching return types";
     inr (m, Δg, if{e} s1 else s2, (cmσ1.1 && cmσ2.1, mσ))%S
  end.
Definition to_fun_stmt (Γn : compound_env Ti) (Γ : env Ti)
     (m : mem Ti) (Δg : global_env Ti) (f : string) (mys : list (option string))
     (τs : list (type Ti)) (σ : type Ti) (cs : cstmt) :
     string + mem Ti * global_env Ti * stmt Ti :=
  ys ← error_of_option (mapM id mys)
    ("function `" +:+ f +:+ "` has unnamed arguments");
  let Δl := zip_with (λ y τ, (y, Local τ)) ys τs in
  '(m,Δg,s,cmσ) ← to_stmt Γn Γ σ m Δg Δl cs;
  guard (gotos s ⊆ labels s) with
    ("function `" +:+ f +:+ "` has unbound gotos");
  guard (breaks_valid 0 s) with
    ("function `" +:+ f +:+ "` has unbound breaks/continues");
  guard (rettype_match cmσ σ) with
    ("function `" +:+ f +:+ "` has incorrect return type");
  inr (m,Δg,s).
Definition alloc_fun (Γn : compound_env Ti) (Γ : env Ti)
    (m : mem Ti) (Δg : global_env Ti) (f : string)
    (mys : list (option string)) (cτs : list ctype) (cσ : ctype)
    (mcs : option cstmt)  : string + mem Ti * global_env Ti :=
  τs ← mapM (to_type Γn Γ m Δg [] (to_Type false)) cτs;
  σ ← to_type Γn Γ m Δg [] (to_Type true) cσ;
  guard (NoDup (omap id mys)) with
    ("function `" +:+ f +:+ "` has duplicate argument names");
  match Δg !! f with
  | Some (Fun τs' σ' ms) =>
     guard (τs' = τs) with
       ("arguments of function `" +:+ f
         +:+ "` do not match previously declared prototype");
     guard (σ' = σ) with
       ("return type of function `" +:+ f
         +:+ "` does not match previously declared prototype");
     match mcs with
     | Some cs =>
        guard (ms = None) with
          ("function `" +:+ f +:+ "` previously completed");
        '(m,Δg,s) ← to_fun_stmt Γn Γ m Δg f mys τs σ cs;
        inr (m,<[f:=Fun τs σ (Some s)]>Δg)
     | None => inr (m,Δg)
     end
  | Some (Global _ _ _) =>
     inl ("function `" +:+ f +:+ "` previously declared as global")
  | Some (GlobalTypeDef _) =>
     inl ("function `" +:+ f +:+ "` previously declared as typedef")
  | Some (EnumVal _ _) =>
     inl ("function `" +:+ f +:+ "` previously declared as enum tag")
  | None =>
     guard (Forall (λ τ, int_typed (size_of Γ τ) sptrT) τs) with
       ("function `" +:+ f +:+ "` has arguments whose type is too large");
     match mcs with
     | Some cs => 
        let Δg := <[f:=Fun τs σ None]>Δg in
        '(m,Δg,s) ← to_fun_stmt Γn Γ m Δg f mys τs σ cs;
        inr (m,<[f:=Fun τs σ (Some s)]>Δg)
     | None => inr (m,<[f:=Fun τs σ None]>Δg)
     end
  end.
Definition to_enum (Γn : compound_env Ti) (Γ : env Ti) (m : mem Ti)
    (τi : int_type Ti) : global_env Ti → list (string * option cexpr) → Z →
    string + global_env Ti :=
  fix go Δg xces z {struct xces} :=
  match xces with
  | [] => inr Δg
  | (x,None) :: xces =>
     guard (Δg !! x = None) with
       ("enum field `" +:+ x +:+ "` previously declared");
     guard (int_typed z τi) with
       ("enum field `" +:+ x +:+ "` has value out of range");
     go (<[x:=EnumVal τi z]>Δg) xces (z + 1)%Z
  | (x,Some ce) :: xces =>
     guard (Δg !! x = None) with
       ("enum field `" +:+ x +:+ "` previously declared");
     '(e,_) ← to_expr Γn Γ m Δg [] ce;
     v ← error_of_option (⟦ e ⟧ Γ ∅ [] m ≫= maybe_inr)
       ("enum field `" +:+ x +:+ "` has non-constant or undefined value");
     '(_,z') ← error_of_option (maybe_VBase v ≫= maybe_VInt)
       ("enum field `" +:+ x +:+ "` has non-integer value");
     guard (int_typed z' τi) with "enum field with value out of range";
     go (<[x:=EnumVal τi z']>Δg) xces (z' + 1)%Z
  end.
Fixpoint to_envs_go (Γn : compound_env Ti) (Γ : env Ti) (m : mem Ti)
    (Δg : global_env Ti) (Θ : list (string * decl)) : string +
    compound_env Ti * env Ti * mem Ti * global_env Ti :=
  match Θ with
  | [] => inr (Γn,Γ,m,Δg)
  | (s,CompoundDecl c cτys) :: Θ =>
     let s : tag := s in
     let ys := fst <$> cτys in
     τs ← mapM (to_type Γn Γ m Δg [] (to_Type false)) (snd <$> cτys);
     guard (Γ !! s = None) with
       ("compound type `" +:+ s +:+ "`  previously declared");
     guard (NoDup ys) with
       ("compound type `" +:+ s +:+ "` has non-unique fields");
     guard (τs ≠ []) with
       ("compound type `" +:+ s +:+ "` declared without any fields");
     to_envs_go (<[s:=CompoundType c ys]>Γn) (<[s:=τs]>Γ) m Δg Θ
  | (s,EnumDecl cτi yces) :: Θ =>
     let s : tag := s in
     let τi := to_inttype cτi in
     guard (Γn !! s = None) with
       ("enum type `" +:+ s +:+ "` previously declared");
     Δg ← to_enum Γn Γ m τi Δg yces 0;
     to_envs_go (<[s:=EnumType τi]>Γn) Γ m Δg Θ
  | (x,TypeDefDecl cτ) :: Θ =>
     guard (Δg !! x = None) with
       ("typedef `" +:+ x +:+ "` previously declared");
     τ ← to_type Γn Γ m Δg [] to_Ptr cτ;
     to_envs_go Γn Γ m (<[x:=GlobalTypeDef τ]>Δg) Θ
  | (x,GlobDecl cτ me) :: Θ =>
     '(m,Δg,_,_) ← alloc_global Γn Γ m Δg [] x cτ me;
     to_envs_go Γn Γ m Δg Θ
  | (f,FunDecl cτys cσ mcs) :: Θ =>
     '(m,Δg) ← alloc_fun Γn Γ m Δg f (fst <$> cτys) (snd <$> cτys) cσ mcs;
     to_envs_go Γn Γ m Δg Θ
  end.
Definition to_envs (Θ : list (string * decl)) :  string +
    compound_env Ti * env Ti * mem Ti * global_env Ti :=
  '(Γn,Γ,m,Δg) ← to_envs_go ∅ ∅ ∅ ∅ Θ;
  guard (global_env_complete Δg)
    with "not all function prototypes completed";
  inr (Γn,Γ,m,Δg).
End frontend_more.

Section cexpr_ind.
Context (P : cexpr → Prop) (Q : ctype → Prop).
Context (Pvar : ∀ x, P (CEVar x)).
Context (Pconst : ∀ s n x, P (CEConst s n x)).
Context (Psizeof : ∀ cτ, Q cτ → P (CESizeOf cτ)).
Context (Pmin : ∀ τi, P (CEMin τi)).
Context (Pmax : ∀ τi, P (CEMax τi)).
Context (Pbits : ∀ τi, P (CEBits τi)).
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
  | CEConst _ _ _ => Pconst _ _ _
  | CESizeOf cτ => Psizeof _ (ctype_ind_alt cτ)
  | CEMin _ => Pmin _
  | CEMax _ => Pmax _
  | CEBits _ => Pbits _
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
Implicit Types ce : cexpr.
Implicit Types s : stmt Ti.
Implicit Types τi : int_type Ti.
Implicit Types τ σ : type Ti.
Implicit Types cτ : ctype.
Implicit Types τlr : lrtype Ti.
Implicit Types Δg : global_env Ti.

Arguments to_R _ _ : simpl never.
Arguments convert_ptrs _ _ _ _ : simpl never.
Hint Extern 0 (_ ⊢ _ : _) => typed_constructor.
Hint Extern 1 (int_typed _ _) => by apply int_typed_small.
Hint Extern 10 (cast_typed _ _ _) => constructor.
Hint Extern 10 (base_cast_typed _ _ _) => constructor.
Hint Extern 2 (to_funtypes _ ⊆ _) => etransitivity; [|by eassumption].
Hint Extern 2 (_ ⊆{⇒} _) => etransitivity; [|by eassumption].

Definition local_decl_valid (Γ : env Ti) (Γm : memenv Ti) (d : local_decl Ti) :=
  match d with
  | Static o τ => Γm ⊢ o : τ
  | Local τ => ✓{Γ} τ
  | TypeDef τ => ptr_type_valid Γ τ
  end.
Notation local_env_valid Γ Γm := (Forall (local_decl_valid Γ Γm ∘ snd)).
Lemma local_decl_valid_weaken Γ1 Γ2 Γm1 Γm2 d :
  local_decl_valid Γ1 Γm1 d → Γ1 ⊆ Γ2 → Γm1 ⊆{⇒} Γm2 → local_decl_valid Γ2 Γm2 d.
Proof.
  destruct d; simpl; eauto using ptr_type_valid_weaken,
    type_valid_weaken, memenv_extend_typed.
Qed.
Lemma local_env_valid_params Γ Γm (ys : list string) (τs : list (type Ti)) :
  ✓{Γ}* τs → local_env_valid Γ Γm (zip_with (λ y τ, (y, Local τ)) ys τs).
Proof. intros Hτs. revert ys. induction Hτs; intros [|??]; simpl; auto. Qed.

Fixpoint local_env_stack_types (Δl : local_env Ti) : list (type Ti) :=
  match Δl with
  | [] => []
  | (_,Local τ) :: Δl => τ :: local_env_stack_types Δl
  | (_,_) :: Δl => local_env_stack_types Δl
  end.
Lemma local_env_stack_types_params (ys : list string) (τs : list (type Ti)) :
  length ys = length τs →
  local_env_stack_types (zip_with (λ y τ, (y, Local τ)) ys τs) = τs.
Proof. rewrite <-Forall2_same_length. induction 1; f_equal'; auto. Qed.
Lemma local_env_stack_types_valid Γ Γm Δl :
  local_env_valid Γ Γm Δl → ✓{Γ}* (local_env_stack_types Δl).
Proof. induction 1 as [|[? []]]; simpl; auto. Qed.
Hint Immediate local_env_stack_types_valid.

Lemma lookup_var_typed Γ Γf m τs Δl x e τ :
  ✓ Γ → ✓{Γ} m → local_env_valid Γ ('{m}) Δl →
  lookup_var x (length τs) Δl = Some (e,τ) →
  (Γ,Γf,'{m},τs ++ local_env_stack_types Δl) ⊢ e : inl τ.
Proof.
  intros ?? HΔl. revert τs. induction HΔl as [|[x' [o|τ'|]] ? Δl ? IH];
    intros τs' ?; simplify_option_equality; simplify_type_equality; eauto 2.
  * typed_constructor; eauto using addr_top_typed, addr_top_strict,
      index_typed_valid, index_typed_representable, lockset_empty_valid.
  * typed_constructor. by rewrite list_lookup_middle.
  * rewrite cons_middle, (associative_L (++)). apply (IH (τs' ++ [τ'])).
    rewrite app_length; simpl. by rewrite Nat.add_comm.
Qed.
Lemma lookup_typedef_valid Γ Γm Δl x τ :
  local_env_valid Γ Γm Δl → lookup_typedef x Δl = Some τ → ptr_type_valid Γ τ.
Proof. induction 1 as [|[? []]]; intros; simplify_option_equality; eauto. Qed.

Definition global_decl_valid (Γ : env Ti) (Γf : funtypes Ti) (Γm : memenv Ti)
    (d : global_decl Ti) :=
  match d with
  | Global o τ _ => Γm ⊢ o : τ
  | Fun τs τ None =>
     ✓{Γ}* τs ∧ Forall (λ τ', int_typed (size_of Γ τ') sptrT) τs ∧ ✓{Γ} τ
  | Fun τs τ (Some s) => ∃ cmτ,
     ✓{Γ}* τs ∧ Forall (λ τ', int_typed (size_of Γ τ') sptrT) τs ∧ ✓{Γ} τ ∧
     (Γ,Γf,Γm,τs) ⊢ s : cmτ ∧ rettype_match cmτ τ ∧
     gotos s ⊆ labels s ∧ breaks_valid 0 s
  | GlobalTypeDef τ => ptr_type_valid Γ τ
  | EnumVal τi z => int_typed z τi
  end.
Hint Extern 0 (global_decl_valid _ _ _ _) => progress simpl.
Notation global_env_valid Γ Γm Δg :=
  (map_Forall (λ _, global_decl_valid Γ (to_funtypes Δg) Γm) Δg).
Lemma global_decl_valid_weaken Γ1 Γ2 Γf1 Γf2 Γm1 Γm2 d :
  ✓ Γ1 → global_decl_valid Γ1 Γf1 Γm1 d → Γ1 ⊆ Γ2 → Γf1 ⊆ Γf2 →
  Γm1 ⊆{⇒} Γm2 → global_decl_valid Γ2 Γf2 Γm2 d.
Proof.
  destruct d as [|??[]| |]; naive_solver eauto using
    ptr_type_valid_weaken, type_valid_weaken, memenv_extend_typed,
    stmt_typed_weaken, types_valid_weaken, sizes_of_weaken.
Qed.
Lemma global_env_valid_weaken Γ1 Γ2 Γm1 Γm2 Δg :
  ✓ Γ1 → global_env_valid Γ1 Γm1 Δg → Γ1 ⊆ Γ2 →
  Γm1 ⊆{⇒} Γm2 → global_env_valid Γ2 Γm2 Δg.
Proof. unfold map_Forall; eauto using global_decl_valid_weaken. Qed.
Lemma global_env_empty_valid Γ Γm : global_env_valid Γ Γm ∅.
Proof. by intros ??; simpl_map. Qed.

Lemma lookup_to_funtypes Δg (x : string) τs τ :
  to_funtypes Δg !! (x:funname) = Some (τs,τ) ↔
    ∃ ms, Δg !! x = Some (Fun τs τ ms).
Proof.
  unfold to_funtypes; rewrite lookup_omap, !bind_Some.
  split; [intros [[] ?]|]; naive_solver.
Qed.
Lemma lookup_to_funtypes_1 Δg (x : string) τs τ :
  to_funtypes Δg !! (x:funname) = Some (τs,τ) →
  ∃ ms, Δg !! x = Some (Fun τs τ ms).
Proof. by rewrite lookup_to_funtypes. Qed.
Lemma lookup_to_funtypes_2 Δg (x : string) τs τ ms :
  Δg !! x = Some (Fun τs τ ms) → to_funtypes Δg !! (x:funname) = Some (τs,τ).
Proof. rewrite lookup_to_funtypes; eauto. Qed.
Hint Immediate lookup_to_funtypes_2.
Lemma to_funtypes_valid Γ Γm Δg :
  global_env_valid Γ Γm Δg → ✓{Γ} (to_funtypes Δg).
Proof.
  intros HΔg f [τs τ]. rewrite lookup_to_funtypes.
  intros [[] Hd]; specialize (HΔg _ _ Hd); naive_solver.
Qed.
Hint Immediate to_funtypes_valid.
Lemma to_funtypes_insert Δg x d :
  Δg !! x = None → to_funtypes Δg ⊆ to_funtypes (<[x:=d]> Δg).
Proof.
  rewrite !map_subseteq_spec; intros ? f [τs τ]; rewrite !lookup_to_funtypes.
  destruct (decide_rel (=) x f) as []; simplify_map_equality; naive_solver.
Qed.
Definition global_decl_extend (d' d : global_decl Ti) : Prop :=
  match d', d with
  | Fun τs τ _, Fun τs' τ' _ => τs = τs' ∧ τ = τ'
  | Fun _ _ _, _ => False | _, _ => True
  end.
Hint Extern 2 (global_decl_extend _ _) => repeat split.
Lemma to_funtypes_insert_Some Δg x d' d :
  Δg !! x = Some d' → global_decl_extend d' d →
  to_funtypes Δg ⊆ to_funtypes (<[x:=d]> Δg).
Proof.
  rewrite !map_subseteq_spec; intros ?? f [τs τ]; rewrite !lookup_to_funtypes.
  intros [??]; destruct (decide_rel (=) x f) as []; simplify_map_equality;
    destruct d; naive_solver.
Qed.
Lemma global_env_insert_valid Γ Γm Δg x d :
  ✓ Γ → Δg !! x = None → global_decl_valid Γ (to_funtypes (<[x:=d]>Δg)) Γm d →
  global_env_valid Γ Γm Δg → global_env_valid Γ Γm (<[x:=d]>Δg).
Proof.
  intros ???? x' d'; rewrite lookup_insert_Some; intros [[??]|[??]];
    subst; eauto using global_decl_valid_weaken, to_funtypes_insert.
Qed.
Lemma global_env_insert_valid_Some Γ Γm Δg x d' d :
  ✓ Γ → Δg !! x = Some d' → global_decl_extend d' d →
  global_decl_valid Γ (to_funtypes (<[x:=d]>Δg)) Γm d →
  global_env_valid Γ Γm Δg → global_env_valid Γ Γm (<[x:=d]>Δg).
Proof.
  intros ????? x' d''; rewrite lookup_insert_Some; intros [[??]|[??]];
    subst; eauto using global_decl_valid_weaken, to_funtypes_insert_Some.
Qed.
Lemma to_funenv_pretyped Γ Γm Δg :
  global_env_valid Γ Γm Δg →
  funenv_pretyped Γ Γm (to_funenv Δg) (to_funtypes Δg).
Proof.
  intros HΔg f s. unfold to_funenv; rewrite lookup_omap, bind_Some.
  intros ([|?? [|]| |]&Hd&?); specialize (HΔg _ _ Hd); naive_solver.
Qed.
Lemma to_funenv_typed Γ Γm Δg :
  global_env_valid Γ Γm Δg → global_env_complete Δg →
  (Γ,Γm) ⊢ to_funenv Δg : to_funtypes Δg.
Proof.
  intros ? Hcomp; split; simpl; eauto using to_funenv_pretyped.
  intros f; rewrite !elem_of_dom; intros [[τs τ] Hf].
  unfold to_funenv; rewrite lookup_omap.
  unfold to_funtypes in Hf; rewrite lookup_omap, bind_Some in Hf.
  destruct Hf as ([|?? [|]| |]&Hd&?); specialize (Hcomp _ _ Hd); try done.
  setoid_rewrite Hd; simpl; eauto.
Qed.

Lemma lookup_var_typed' Γ m Δg Δl x e τrl :
  ✓ Γ → ✓{Γ} m → global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  lookup_var' x Δg Δl = Some (e,τrl) →
  (Γ,to_funtypes Δg,'{m},local_env_stack_types Δl) ⊢ e : τrl.
Proof.
  unfold lookup_var'; intros ?? HΔg ??.
  destruct (lookup_var x 0 Δl) as [[??]|] eqn:?; simplify_equality'.
  { eapply (lookup_var_typed _ _ _ []); eauto. }
  destruct (Δg !! x) as [d|] eqn:Hd; simplify_equality; specialize (HΔg x d Hd).
  destruct d; simplify_equality'.
  * typed_constructor; eauto using addr_top_typed, addr_top_strict,
      index_typed_valid, index_typed_representable, lockset_empty_valid.
  * typed_constructor; eauto using lockset_empty_valid.
Qed.
Lemma lookup_typedef_valid' Γ Γm Δg Δl x τ :
  global_env_valid Γ Γm Δg → local_env_valid Γ Γm Δl →
  lookup_typedef' x Δg Δl = Some τ → ptr_type_valid Γ τ.
Proof.
  unfold lookup_typedef'; intros HΔg ??.
  destruct (lookup_typedef x Δl) eqn:?; simplify_equality'.
  { eauto using lookup_typedef_valid. }
  destruct (Δg !! x) as [[| |τ'|]|] eqn:Hd; simplify_equality.
  by apply (HΔg x _ Hd).
Qed.

Lemma to_int_const_typed x cτis τi :
  to_int_const x cτis = Some τi → int_typed x τi.
Proof. intros; induction cτis; simplify_option_equality; auto. Qed.
Lemma to_R_typed Γ Γf m τs e τlr e' τ' :
  ✓ Γ → ✓{Γ} Γf → to_R (e,τlr) = (e',τ') → (Γ,Γf,'{m},τs) ⊢ e : τlr →
  ✓{Γ}* τs → (Γ,Γf,'{m},τs) ⊢ e' : inr τ'.
Proof.
  unfold to_R; intros; destruct τlr as [τl|τr]; simplify_equality'; auto.
  destruct (maybe_TArray τl) as [[τ n]|] eqn:Hτ; simplify_equality'.
  { destruct τl; simplify_equality'. repeat typed_constructor; eauto.
    apply Nat.neq_0_lt_0.
    eauto using TArray_valid_inv_size, expr_inl_typed_type_valid. }
  by typed_constructor.
Qed.
Lemma to_R_NULL_typed Γ Γf m τs σ e τlr e' τ' :
  ✓ Γ → ✓{Γ} Γf → to_R_NULL σ (e,τlr) = (e',τ') → (Γ,Γf,'{m},τs) ⊢ e : τlr →
  ✓{Γ}* τs → ptr_type_valid Γ σ → (Γ,Γf,'{m},τs) ⊢ e' : inr τ'.
Proof.
  unfold to_R_NULL. destruct (to_R (e,τlr)) as [e'' τ''] eqn:?.
  destruct 6 as [σb Hσb| |]; simplify_equality'; eauto 2 using to_R_typed.
  destruct Hσb; repeat case_match; simplify_equality'; eauto 2 using to_R_typed.
  repeat typed_constructor; eauto using lockset_empty_valid.
Qed.
Lemma convert_ptrs_typed Γ Γf m τs e1 τ1 e2 τ2 e1' e2' τ' :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs →
  convert_ptrs (e1,τ1) (e2,τ2) = Some (e1', e2', τ') →
  (Γ,Γf,'{m},τs) ⊢ e1 : inr τ1 → (Γ,Γf,'{m},τs) ⊢ e2 : inr τ2 →
  (Γ,Γf,'{m},τs) ⊢ e1' : inr τ' ∧ (Γ,Γf,'{m},τs) ⊢ e2' : inr τ'.
Proof.
  unfold convert_ptrs; destruct τ1 as [[|τp1|]| |], τ2 as [[|τp2|]| |]; intros;
    simplify_option_equality; split; repeat typed_constructor;
    eauto using TPtr_valid_inv, TBase_valid_inv, expr_inr_typed_type_valid,
    lockset_empty_valid.
Qed.
Lemma to_if_expr_typed Γ Γf m τs e1 τb e2 τ2 e3 τ3 e τlr :
  ✓ Γ → ✓{Γ} Γf → ✓{Γ}* τs →
  to_if_expr e1 (e2,τ2) (e3,τ3) = Some (e,τlr) →
  (Γ,Γf,'{m},τs) ⊢ e1 : inr (baseT τb) → (Γ,Γf,'{m},τs) ⊢ e2 : inr τ2 →
  (Γ,Γf,'{m},τs) ⊢ e3 : inr τ3 → (Γ,Γf,'{m},τs) ⊢ e : τlr.
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
  (Γ,Γf,'{m},τs) ⊢ e1 : inr τ1 → (Γ,Γf,'{m},τs) ⊢ e2 : inr τ2 →
  (Γ,Γf,'{m},τs) ⊢ e : τlr.
Proof.
  unfold to_binop_expr; intros;
    repeat match goal with
    | _ => progress simplify_option_equality
    | x : (_ * _)%type |- _ => destruct x
    | H: binop_type_of _ _ _ = Some _ |- _ => apply binop_type_of_sound in H
    | H : convert_ptrs _ _ = Some _ |- _ =>
       eapply convert_ptrs_typed in H; eauto; destruct H
    end; typed_constructor; eauto.
Qed.
Lemma to_expr_type_typed Γn Γ m Δg Δl :
  ✓ Γ → ✓{Γ} m → global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  (∀ ce e τlr, to_expr Γn Γ m Δg Δl ce = inr (e,τlr) →
    (Γ,to_funtypes Δg,'{m},local_env_stack_types Δl) ⊢ e : τlr) ∧
  (∀ cτ,
    (∀ τ void, to_type Γn Γ m Δg Δl (to_Type void) cτ = inr τ → ✓{Γ} τ) ∧
    (∀ τ, to_type Γn Γ m Δg Δl to_Ptr cτ = inr τ → ptr_type_valid Γ τ)).
Proof.
  intros ????. assert (∀ f ces τs τ ms eτlrs,
     Δg !! f = Some (Fun τs τ ms) →
     Forall (λ ce, ∀ e τlr, to_expr Γn Γ m Δg Δl ce = inr (e,τlr) →
       (Γ,to_funtypes Δg,'{m},local_env_stack_types Δl) ⊢ e : τlr) ces →
     Forall2 (cast_typed Γ) (snd <$> zip_with to_R_NULL τs eτlrs) τs →
     mapM (to_expr Γn Γ m Δg Δl) ces = inr eτlrs →
     (Γ,to_funtypes Δg,'{m},local_env_stack_types Δl) ⊢*
       cast{τs}* (fst <$> zip_with to_R_NULL τs eτlrs) :* inr <$> τs).
  { intros f ces τs τ ms eτlrs. rewrite mapM_inr. intros Hf ? Hcast Hces.
    assert (Forall (ptr_type_valid Γ) τs) as Hτs by eauto using Forall_impl,
      type_valid_ptr_type_valid, funtypes_valid_args_valid; clear Hf.
    revert τs Hτs Hcast.
    induction Hces as [|? [??]]; intros [|??] ??; decompose_Forall_hyps;
      constructor; eauto using ECast_typed,to_R_NULL_typed,surjective_pairing. }
  apply cexpr_ctype_ind; intros; split_ands; intros;
    repeat match goal with
    | H : _ ∧ _ |- _ => destruct H
    | _ : maybe_inl ?τlr = Some _ |- _ => is_var τlr; destruct τlr
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ : maybe_TPtr ?τb = Some _ |- _ => is_var τb; destruct τb
    | _ : maybe_TInt ?τb = Some _ |- _ => is_var τb; destruct τb
    | _ : maybe_TCompound ?τ = Some _ |- _ => is_var τ; destruct τ
    | _ : maybe_Fun ?d = Some _ |- _ => is_var d; destruct d
    | IH : ∀ _ _, to_expr _ _ _ _ _ ?ce = inr _ → _,
       H : to_expr _ _ _ _ _ ?ce = inr _ |- _ => specialize (IH _ _ H)
    | IH : ∀ _, to_type _ _ _ _ _ _ ?cτ = inr _ → _,
       H : to_type _ _ _ _ _ _ ?cτ = inr _ |- _ => specialize (IH _ H)
    | IH : ∀ _ _, to_type _ _ _ _ _ _ ?cτ = inr _ → _,
       H : to_type _ _ _ _ _ _ ?cτ = inr _ |- _ => specialize (IH _ _ H)
    | H: assign_type_of _ _ _ _ = Some _ |- _ => apply assign_type_of_sound in H
    | H: unop_type_of _ _ = Some _ |- _ => apply unop_type_of_sound in H
    | H: binop_type_of _ _ _ = Some _ |- _ => apply binop_type_of_sound in H
    | H: to_R_NULL _ _ = _ |- _ =>
       first_of ltac:(eapply to_R_NULL_typed in H) idtac
         ltac:(by eauto using type_valid_ptr_type_valid)
    | x : (_ * _)%type |- _ => destruct x
    | _ => progress simplify_error_equality
    | _ : _ ⊢ _ : ?τlr |- _ =>
       unless (✓{Γ} (lrtype_type τlr)) by assumption;
       assert (✓{Γ} (lrtype_type τlr)) by eauto using expr_typed_type_valid
    | _ : context [to_R ?eτlr] |- _ => 
       let H := fresh in destruct (to_R eτlr) eqn:H;
       first_of ltac:(eapply to_R_typed in H) idtac ltac:(by eauto)
    | _ => progress case_match
    end;
    match goal with
    | |- _ ⊢ _ : _ =>
       repeat typed_constructor; eauto using to_binop_expr_typed,
         to_if_expr_typed, lookup_var_typed', type_valid_ptr_type_valid,
         lockset_empty_valid, int_lower_typed, int_upper_typed, int_bits_typed,
         type_complete_valid, TBase_valid_inv, TPtr_valid_inv, to_int_const_typed
    | |- ✓{_} _ =>
       repeat constructor; eauto using lookup_typedef_valid',
         TBase_valid_inv, TPtr_valid_inv, type_complete_valid
    | |- ptr_type_valid _ _ =>
       repeat constructor; eauto using type_valid_ptr_type_valid,
         lookup_typedef_valid', TBase_valid_inv, TPtr_valid_inv
    end.
Qed.
Lemma to_expr_typed Γn Γ m Δg Δl ce e τlr :
  ✓ Γ → ✓{Γ} m → global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  to_expr Γn Γ m Δg Δl ce = inr (e,τlr) →
  (Γ,to_funtypes Δg,'{m},local_env_stack_types Δl) ⊢ e : τlr.
Proof. intros. eapply to_expr_type_typed; eauto. Qed.
Lemma to_type_valid Γn Γ m Δg Δl void cτ τ :
  ✓ Γ → ✓{Γ} m → global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  to_type Γn Γ m Δg Δl (to_Type void) cτ = inr τ → ✓{Γ} τ.
Proof. intros. eapply to_expr_type_typed; eauto. Qed.
Lemma to_ptr_type_valid Γn Γ m Δg Δl cτ τ :
  ✓ Γ → ✓{Γ} m → global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  to_type Γn Γ m Δg Δl to_Ptr cτ = inr τ → ptr_type_valid Γ τ.
Proof. intros. eapply to_expr_type_typed; eauto. Qed.
Lemma to_types_valid Γn Γ m Δg Δl void cτs τs :
  ✓ Γ → ✓{Γ} m → global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  mapM (to_type Γn Γ m Δg Δl (to_Type void)) cτs = inr τs → ✓{Γ}* τs.
Proof. rewrite mapM_inr. induction 5; eauto using to_type_valid. Qed.
Lemma to_val_typed Γn Γ m Δg Δl ce τ v :
  ✓ Γ → global_env_valid Γ ('{m}) Δg → ✓{Γ} m → local_env_valid Γ ('{m}) Δl →
  ✓{Γ} τ → to_val Γn Γ m Δg Δl ce τ = inr v → (Γ,'{m}) ⊢ v : τ.
Proof.
  unfold to_val; intros.
  destruct (to_expr Γn Γ m Δg Δl ce) as [|[e τlr]] eqn:?; simplify_equality'.
  destruct (to_R_NULL τ (e, τlr)) as [e' τ'] eqn:?.
  repeat case_error_guard; simplify_equality'.
  destruct (⟦ e' ⟧ Γ ∅ [] m) as [[?|v']|] eqn:?; simplify_option_equality.
  cut ((Γ,'{m}) ⊢ inr v' : inr τ').
  { intros; typed_inversion_all; eauto using val_cast_typed. }
  eapply (expr_eval_typed_aux Γ (to_funtypes Δg) [] (local_env_stack_types Δl));
    eauto using to_R_NULL_typed, type_valid_ptr_type_valid, to_expr_typed,
    prefix_of_nil, funtypes_valid_empty.
  by intro; destruct (to_funtypes _ !! _); simpl_map.
Qed.
Lemma alloc_global_typed Γn Γ m Δg Δl x cτ mce m' Δg' o τ :
  ✓ Γ → ✓{Γ} m → mem_writable_all Γ m →
  global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  alloc_global Γn Γ m Δg Δl x cτ mce = inr (m',Δg',o,τ) →
  (**i 1.) *) ✓{Γ} m' ∧
  (**i 2.) *) mem_writable_all Γ m' ∧
  (**i 3.) *) '{m} ⊆{⇒} '{m'} ∧
  (**i 4.) *) global_env_valid Γ ('{m'}) Δg' ∧
  (**i 5.) *) to_funtypes Δg ⊆ to_funtypes Δg' ∧
  (**i 6.) *) '{m'} ⊢ o : τ.
Proof.
  unfold alloc_global; intros ??? HΔg ??.
  destruct (to_type Γn Γ m Δg Δl (to_Type false) cτ)
    as [|τ'] eqn:?; simpl in *; simplify_equality.
  assert (✓{Γ} τ') by eauto using to_type_valid.
  destruct (Δg !! x) as [[o' τ'' init| | |]|] eqn:Hx; simplify_equality.
  { pose proof (HΔg _ _ Hx); repeat case_error_guard; simplify_equality'.
    destruct mce as [ce|]; simplify_equality'; [|by auto 10].
    repeat case_error_guard; simplify_equality'.
    destruct (to_val Γn Γ m Δg Δl ce τ'') as [v|] eqn:?; simplify_equality'.
    assert ('{m} ⊆{⇒} '{<[addr_top o τ:=v]{Γ}> m}).
    { eapply mem_insert_extend; eauto using to_val_typed,
        addr_top_typed, index_typed_representable. }
    split_ands; eauto 8 using mem_insert_valid', to_val_typed, addr_top_typed,
      index_typed_representable, mem_insert_top_writable_all,
      global_env_insert_valid_Some, global_decl_valid_weaken,
      memenv_extend_typed, to_funtypes_insert_Some, global_env_valid_weaken. }
  repeat case_error_guard; simplify_equality'.
  destruct mce as [ce|]; simplify_equality'.
  * set (m'':=mem_alloc Γ (fresh (dom indexset m)) false τ' m) in *.
    set (Δg'':=<[x:=Global (fresh (dom indexset m)) τ' true]> Δg) in *.
    destruct (to_val Γn Γ m'' Δg'' Δl ce τ') as [v|] eqn:?; simplify_equality'.
    set (o:=fresh (dom indexset m)) in *.
    assert (✓{Γ} m'' ∧ mem_writable_all Γ m'') as [??] by eauto using
      mem_alloc_valid', mem_allocable_fresh, mem_alloc_writable_all.
    assert ('{m''} ⊢ o : τ') by eauto using mem_alloc_index_typed'.
    assert ('{m} ⊆{⇒} '{m''}).
    { eauto using mem_alloc_extend', mem_allocable_fresh. }
    assert (global_env_valid Γ ('{m''})
      (<[x:=Global (fresh (dom indexset m)) τ' true]>Δg)).
    { eapply global_env_insert_valid; simpl; eauto using
        global_decl_valid_weaken, global_env_valid_weaken. }
    assert ('{m''} ⊆{⇒} '{<[addr_top o τ':=v]{Γ}> m''}).
    { eapply mem_insert_extend; eauto using to_val_typed, addr_top_typed,
        index_typed_representable, local_decl_valid_weaken, Forall_impl. }
    split_ands; eauto 8 using mem_insert_valid', to_val_typed, addr_top_typed,
      index_typed_representable, mem_insert_top_writable_all,
      memenv_extend_typed, to_funtypes_insert,
      global_env_valid_weaken, local_decl_valid_weaken, Forall_impl.
  * split_ands; eauto 9 using global_env_insert_valid, mem_alloc_val_valid,
      global_env_valid_weaken, mem_alloc_val_index_typed, mem_alloc_val_extend,
      val_0_typed, mem_allocable_fresh, to_funtypes_insert,
      mem_alloc_val_writable_all.
Qed.
Lemma alloc_static_typed Γn Γ m Δg Δl x cτ mce m' o τ :
  ✓ Γ → ✓{Γ} m → mem_writable_all Γ m →
  global_env_valid Γ ('{m}) Δg → local_env_valid Γ ('{m}) Δl →
  alloc_static Γn Γ m Δg Δl x cτ mce = inr (m',o,τ) →
  (**i 1.) *) ✓{Γ} m' ∧
  (**i 2.) *) mem_writable_all Γ m' ∧
  (**i 3.) *) '{m} ⊆{⇒} '{m'} ∧
  (**i 4.) *) '{m'} ⊢ o : τ.
Proof.
  unfold alloc_static; intros.
  destruct (to_type Γn Γ m Δg Δl (to_Type false) cτ)
    as [|τ'] eqn:?; simpl in *; simplify_equality.
  assert (✓{Γ} τ') by eauto using to_type_valid.
  repeat case_error_guard; simplify_equality'.
  destruct mce as [ce|]; simplify_equality'.
  * destruct (to_val Γn Γ _ Δg _ ce τ') as [v|] eqn:?; simplify_equality'.
    set (m'':=mem_alloc Γ (fresh (dom indexset m)) false τ m) in *.
    set (Δl'':=(x, Local τ) :: Δl) in *.
    set (o:=fresh (dom indexset m)) in *.
    assert (✓{Γ} m'' ∧ mem_writable_all Γ m'') as [??] by eauto using
      mem_alloc_valid', mem_allocable_fresh, mem_alloc_writable_all.
    assert ('{m''} ⊢ o : τ) by eauto using mem_alloc_index_typed'.
    assert ('{m} ⊆{⇒} '{m''}).
    { eauto using mem_alloc_extend', mem_allocable_fresh. }
    assert (local_env_valid Γ ('{m''}) Δl'').
    { constructor; eauto using local_decl_valid_weaken, Forall_impl. }
    assert ('{m''} ⊆{⇒} '{<[addr_top o τ:=v]{Γ}> m''}).
    { eapply mem_insert_extend; eauto using to_val_typed, addr_top_typed,
        index_typed_representable, global_env_valid_weaken. }
    split_ands; eauto 8 using mem_insert_valid', to_val_typed, addr_top_typed,
      mem_insert_top_writable_all, memenv_extend_typed, global_env_valid_weaken.
  * split_ands; eauto 8 using global_env_insert_valid, mem_alloc_val_valid,
      mem_alloc_val_extend, val_0_typed, mem_allocable_fresh,
      mem_alloc_val_writable_all, mem_alloc_val_index_typed.
Qed.
Lemma to_stmt_typed Γn Γ τret m Δg Δl cs m' Δg' s cmτ :
  ✓ Γ → ✓{Γ} m → mem_writable_all Γ m → global_env_valid Γ ('{m}) Δg →
  local_env_valid Γ ('{m}) Δl → ptr_type_valid Γ τret →
  to_stmt Γn Γ τret m Δg Δl cs = inr (m',Δg', s,cmτ) →
  (**i 1.) *) (Γ,to_funtypes Δg','{m'},local_env_stack_types Δl) ⊢ s : cmτ ∧
  (**i 2.) *) ✓{Γ} m' ∧
  (**i 3.) *) mem_writable_all Γ m' ∧
  (**i 4.) *) '{m} ⊆{⇒} '{m'} ∧
  (**i 5.) *) global_env_valid Γ ('{m'}) Δg' ∧
  (**i 6.) *) to_funtypes Δg ⊆ to_funtypes Δg'.
Proof.
  intros ? Hm Hm' Hg Hl Hτret Hs.
  revert m m' s cmτ Δl Δg Δg' Hs Hm Hm' Hg Hl.
  induction cs; intros;
    repeat match goal with
    | _ : maybe_TBase ?τ = Some _ |- _ => is_var τ; destruct τ
    | H : alloc_static _ _ _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply alloc_static_typed in H) idtac ltac:(by auto);
       destruct H as (?&?&?&?)
    | H : alloc_global _ _ _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply alloc_global_typed in H) idtac ltac:(by auto);
       destruct H as (?&?&?&?&?&?)
    | IH : ∀ _ _ _ _ _ _ _, to_stmt _ _ _ _ _ _ ?cs = inr _ → _,
      H : to_stmt _ _ _ _ _ _ ?cs = inr _ |- _ =>
       last_of ltac:(destruct (IH _ _ _ _ _ _ _ H) as (?&?&?&?&?&?))
         ltac:(by eauto using Forall_impl, local_decl_valid_weaken,
           global_env_valid_weaken) ltac:(clear IH H)
    | H : to_expr _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply to_expr_typed in H; simpl) idtac
         ltac:(by eauto using Forall_impl, local_decl_valid_weaken)
    | H : to_type _ _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply to_type_valid in H; simpl) idtac ltac:(by auto)
    | H : to_type _ _ _ _ _ _ _ = inr _ |- _ =>
       first_of ltac:(apply to_ptr_type_valid in H; simpl) idtac ltac:(by auto)
    | H: to_R _ = _, _ : (_,_,_,?τs) ⊢ _ : _ |- _ =>
       first_of ltac:(eapply (to_R_typed _ _ _ τs) in H) idtac ltac:(by eauto)
    | H: to_R_NULL _ _ = _ |- _ =>
       first_of ltac:(eapply to_R_NULL_typed in H) idtac
         ltac:(by eauto using type_valid_ptr_type_valid)
    | x : (_ * _)%type |- _ => destruct x
    | _ => progress simplify_error_equality
    | _ => case_match
    end; try by (split_ands; eauto using to_R_typed,
      to_expr_typed, lockset_empty_valid).
  * split_ands; eauto 2. eapply SBlock_typed; eauto 2.
    repeat typed_constructor; eauto using expr_typed_weaken, subseteq_empty.
    by constructor.
  * split_ands; eauto using stmt_typed_weaken.
  * split_ands; eauto 1.
    repeat typed_constructor; eauto using expr_typed_weaken, rettype_union_l.
  * split_ands; eauto 1. repeat typed_constructor;
     eauto using expr_typed_weaken, rettype_union_l, rettype_union_r.
  * split_ands; eauto 1. repeat typed_constructor;
     eauto using expr_typed_weaken, rettype_union_l, rettype_union_r.
  * split_ands; eauto 3. repeat typed_constructor; eauto using
      stmt_typed_weaken, expr_typed_weaken, rettype_union_l, rettype_union_r.
Qed.
Lemma to_fun_stmt_typed Γn Γ m Δg f mys τs σ cs m' Δg' s :
  ✓ Γ → ✓{Γ} m → mem_writable_all Γ m →
  global_env_valid Γ ('{m}) Δg → ✓{Γ} σ → ✓{Γ}* τs → length mys = length τs →
  to_fun_stmt Γn Γ m Δg f mys τs σ cs = inr (m',Δg',s) → ∃ cmτ,
  (**i 1.) *) (Γ,to_funtypes Δg','{m'},τs) ⊢ s : cmτ ∧
  (**i 2.) *) rettype_match cmτ σ ∧
  (**i 3.) *) gotos s ⊆ labels s ∧
  (**i 4.) *) breaks_valid 0 s ∧
  (**i 5.) *) ✓{Γ} m' ∧
  (**i 6.) *) mem_writable_all Γ m' ∧
  (**i 7.) *) '{m} ⊆{⇒} '{m'} ∧
  (**i 8.) *) global_env_valid Γ ('{m'}) Δg' ∧
  (**i 9.) *) to_funtypes Δg ⊆ to_funtypes Δg'.
Proof.
  unfold to_fun_stmt; intros.
  destruct (mapM id mys) as [ys|] eqn:?; simplify_equality'.
  assert (length ys = length τs) by (by erewrite <-mapM_length by eauto).
  destruct (to_stmt _ _ _ _ _ _ _)
    as [|[[[m'' Δg''] ?] cmτ]] eqn:?; simplify_error_equality.
  destruct (to_stmt_typed Γn Γ σ m Δg
    (zip_with (λ y τ, (y, Local τ)) ys τs) cs m' Δg' s cmτ) as (Hs&?&?&?&?&?);
    eauto using local_env_valid_params, type_valid_ptr_type_valid.
  rewrite local_env_stack_types_params in Hs by done; eauto 10.
Qed.
Lemma alloc_fun_typed Γn Γ m Δg f mys cτs cτ mcs m' Δg' :
  ✓ Γ → ✓{Γ} m → mem_writable_all Γ m → global_env_valid Γ ('{m}) Δg →
  length mys = length cτs →
  alloc_fun Γn Γ m Δg f mys cτs cτ mcs = inr (m',Δg') →
  (**i 1.) *) ✓{Γ} m' ∧
  (**i 2.) *) mem_writable_all Γ m' ∧
  (**i 3.) *) global_env_valid Γ ('{m'}) Δg' ∧
  (**i 4.) *) to_funtypes Δg ⊆ to_funtypes Δg'.
Proof.
  unfold alloc_fun; intros ??? HΔg ??.
  destruct (mapM _ _) as [|τs] eqn:?; simplify_equality'.
  assert (✓{Γ}* τs) by eauto using to_types_valid.
  assert (length mys = length τs).
  { eauto 3 using error_mapM_length, eq_trans. }
  destruct (to_type _ _ _ _ _ _ _) as [|σ] eqn:?; simplify_equality'.
  assert (✓{Γ} σ) by eauto using to_type_valid.
  case_error_guard; simplify_equality'.
  destruct (Δg !! f) as [[|τs' σ' ms| |]|] eqn:?; simplify_equality'.
  * repeat case_error_guard; simplify_equality'.
    destruct mcs as [cs|]; repeat case_error_guard; simplify_equality; eauto.
    destruct (to_fun_stmt _ _ _ _ _ _ _ _ _)
      as [|[[m'' Δg''] s]] eqn:?; simplify_equality'.
    destruct (to_fun_stmt_typed Γn Γ m Δg f mys τs σ cs m' Δg'' s)
      as (mcσ&?&?&?&?&?&?&?&?&?); auto.
    destruct (lookup_to_funtypes_1 Δg'' f τs σ); eauto using lookup_weaken.
    assert (to_funtypes Δg'' ⊆ to_funtypes (<[f:=Fun τs σ (Some s)]> Δg''))
      by eauto using to_funtypes_insert_Some.
    destruct (HΔg f (Fun τs σ None)) as (?&?&?);
      eauto 19 using global_env_insert_valid_Some, stmt_typed_weaken.
  * case_error_guard; simplify_equality'.
    destruct mcs as [cs|]; simplify_equality;
      eauto 15 using to_funtypes_insert, global_env_insert_valid.
    destruct (to_fun_stmt _ _ _ _ _ _ _ _ _)
      as [|[[m'' Δg''] s]] eqn:?; simplify_equality'.
    set (Δg':=<[f:=Fun τs σ None]> Δg) in *.
    assert (to_funtypes Δg ⊆ to_funtypes Δg').
      by eauto 10 using to_funtypes_insert.
    destruct (to_fun_stmt_typed Γn Γ m Δg' f mys τs σ cs m' Δg'' s)
      as (mcσ&?&?&?&?&?&?&?&?&?); eauto 10 using global_env_insert_valid.
    destruct (lookup_to_funtypes_1 Δg'' f τs σ).
    { eapply lookup_weaken; eauto.
      by unfold Δg'; eapply lookup_to_funtypes_2; simpl_map. }
    assert (to_funtypes Δg'' ⊆ to_funtypes (<[f:=Fun τs σ (Some s)]> Δg''))
      by eauto using to_funtypes_insert_Some.
    eauto 19 using stmt_typed_weaken, global_env_insert_valid_Some.
Qed.
Lemma to_enum_typed Γn Γ m τi Δg yces z Δg' :
  ✓ Γ → to_enum Γn Γ m τi Δg yces z = inr Δg' →
  global_env_valid Γ ('{m}) Δg →
  (**i 1.) *) global_env_valid Γ ('{m}) Δg' ∧
  (**i 2.) *) to_funtypes Δg ⊆ to_funtypes Δg'.
Proof.
  revert z Δg. induction yces as [|[x [ce|]] yces IH];
    intros z Δg ???; simplify_equality'; auto.
  * case_error_guard; simplify_equality'.
    destruct (to_expr Γn Γ m Δg [] ce) as [|[e τlr]] eqn:?; simplify_equality'.
    destruct (⟦ e ⟧ Γ ∅ [] m)
      as [[?|[[| |τi' z'| |]| | | |]]|] eqn:?; simplify_equality'.
    repeat case_error_guard; simplify_equality'.
    destruct (IH (z' + 1)%Z (<[x:=EnumVal τi z']> Δg));
      eauto using global_env_insert_valid, to_funtypes_insert.
  * repeat case_error_guard; simplify_equality'.
    destruct (IH (z + 1)%Z (<[x:=EnumVal τi z]> Δg));
      eauto using global_env_insert_valid, to_funtypes_insert.
Qed.
Lemma to_envs_go_typed Θ Γn Γ m Δg Γn' Γ' m' Δg' :
  ✓ Γ → ✓{Γ} m → mem_writable_all Γ m → global_env_valid Γ ('{m}) Δg →
  to_envs_go Γn Γ m Δg Θ = inr (Γn',Γ',m',Δg') →
  (**i 1.) *) ✓ Γ' ∧
  (**i 2.) *) ✓{Γ'} m' ∧
  (**i 3.) *) mem_writable_all Γ' m' ∧
  (**i 4.) *) global_env_valid Γ' ('{m'}) Δg' ∧
  (**i 5.) *) to_funtypes Δg ⊆ to_funtypes Δg'.
Proof.
  revert Γn Γ m Δg.
  induction Θ as [|[x [c cτys|cτi yces|cτ|cτ mce|cτys cσ mcs]] Θ IH];
    intros Γn Γ m Δg ?????; simplify_equality'.
  * done.
  * destruct (mapM _ _) as [|τs] eqn:?; simplify_error_equality.
    assert (✓ (<[x:tag:=τs]> Γ)) by (constructor; eauto using to_types_valid).
    apply (IH (<[(x:tag):=CompoundType c (fst <$> cτys)]>Γn)
      (<[(x:tag):=τs]>Γ) m Δg); simpl in *; auto.
    + eauto using cmap_valid'_weaken, insert_subseteq.
    + eauto using mem_writable_all_weaken, insert_subseteq.
    + eauto using global_env_valid_weaken, insert_subseteq.
  * repeat case_error_guard; simplify_equality'.
    destruct (to_enum Γn Γ m (to_inttype cτi) Δg yces 0)
      as [|Δg''] eqn:?; simplify_equality'.
    destruct (to_enum_typed Γn Γ m (to_inttype cτi) Δg yces 0 Δg''); eauto.
    destruct (IH (<[x:tag:=EnumType (to_inttype cτi)]> Γn) Γ m Δg'')
      as (?&?&?&?&?); eauto 10.
  * repeat case_error_guard; simplify_equality'.
    destruct (to_type _ _ _ _ _ _ _) as [τ|] eqn:?; simplify_equality'.
    destruct (IH Γn Γ m (<[x:=GlobalTypeDef t]> Δg))
      as (?&?&?&?&?); eauto 7 using global_env_insert_valid,
      to_ptr_type_valid, to_funtypes_insert.
  * repeat case_error_guard; simplify_equality'.
    destruct (alloc_global _ _ _ _ _ _ _ _)
      as [|[[[m'' Δg''] o] τ]] eqn:?; simplify_equality'.
    destruct (alloc_global_typed Γn Γ m Δg [] x cτ mce m'' Δg'' o τ)
      as (?&?&?&?&?&?); eauto using to_type_valid.
    destruct (IH Γn Γ m'' Δg'') as (?&?&?&?&?);
      eauto 10 using global_env_valid_weaken.
  * destruct (alloc_fun _ _ _ _ _ _ _ _ _)
      as [|[m'' Δg'']] eqn:?; simplify_equality'.
    destruct (alloc_fun_typed Γn Γ m Δg x (fst <$> cτys) (snd <$> cτys)
      cσ mcs m'' Δg'') as (?&?&?&?); rewrite ?fmap_length; eauto.
    destruct (IH Γn Γ m'' Δg'') as (?&?&?&?&?);
      eauto 10 using global_env_valid_weaken.
Qed.
Lemma to_envs_typed Θ Γn Γ m Δg :
  to_envs Θ = inr (Γn,Γ,m,Δg) →
  (**i 1.) *) ✓ Γ ∧
  (**i 2.) *) ✓{Γ} (to_funtypes Δg) ∧
  (**i 3.) *) (Γ,'{m}) ⊢ to_funenv Δg : to_funtypes Δg ∧
  (**i 4.) *) ✓{Γ} m ∧
  (**i 5.) *) mem_writable_all Γ m.
Proof.
  unfold to_envs. intros. destruct (to_envs_go _ _ _ _ _)
    as [|[[[??] ?] ?]] eqn:?; simplify_error_equality.
  destruct (to_envs_go_typed Θ ∅ ∅ ∅ ∅ Γn Γ m Δg)
    as (?&?&?&?&?); eauto 6 using env_empty_valid, mem_empty_writable_all,
    cmap_empty_valid, to_funenv_typed, global_env_empty_valid.
Qed.
End properties.
