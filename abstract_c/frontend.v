(* Copyright (c) 2012-2015, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
Require Import String stringmap.
Require Export type_system_decidable expression_eval error.

Local Open Scope string_scope.
Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Local Open Scope list_scope.
Local Coercion Z.of_nat: nat >-> Z.

Inductive cint_rank : iType :=
  | CCharRank | CShortRank | CIntRank | CLongRank | CLongLongRank | CPtrRank.
Inductive cint_type : iType :=
  CIntType { csign : option signedness; crank : cint_rank }.

Inductive climit : iType :=
  | CESizeOf : climit
  | CEAlignOf : climit
  | CEOffsetOf : string → climit
  | CEMin : climit
  | CEMax : climit
  | CEBits : climit.

Inductive cexpr : iType :=
  | CEVar : string → cexpr
  | CEConst : cint_type → Z → cexpr
  | CEConstString : list Z → cexpr
  | CELimit : ctype → climit → cexpr
  | CEAddrOf : cexpr → cexpr
  | CEDeref : cexpr → cexpr
  | CEAssign : assign → cexpr → cexpr → cexpr
  | CECall : cexpr → list cexpr → cexpr
  | CEAbort : cexpr
  | CEAlloc : ctype → cexpr → cexpr
  | CEFree : cexpr → cexpr
  | CEUnOp : unop → cexpr → cexpr
  | CEBinOp : binop → cexpr → cexpr → cexpr
  | CEIf : cexpr → cexpr → cexpr → cexpr
  | CEComma : cexpr → cexpr → cexpr
  | CEAnd : cexpr → cexpr → cexpr
  | CEOr : cexpr → cexpr → cexpr
  | CECast : ctype → cinit → cexpr
  | CEField : cexpr → string → cexpr
with cinit : iType :=
  | CSingleInit : cexpr → cinit
  | CCompoundInit : list (list (string + cexpr) * cinit) → cinit
with ctype : iType :=
  | CTVoid : ctype
  | CTDef : string → ctype
  | CTEnum : string → ctype
  | CTInt : cint_type → ctype
  | CTPtr : ctype → ctype
  | CTArray : ctype → cexpr → ctype
  | CTCompound : compound_kind → string → ctype
  | CTFun : list (option string * ctype) → ctype → ctype
  | CTTypeOf : cexpr → ctype.

#[global] Instance maybe_CEConstString : Maybe CEConstString := λ ce,
  match ce with CEConstString zs => Some zs | _ => None end.
#[global] Instance maybe_CTFun : Maybe2 CTFun := λ cτ,
  match cτ with CTFun cτs cτ => Some (cτs,cτ) | _ => None end.
#[global] Instance maybe_CSingleInit : Maybe CSingleInit := λ ci,
  match ci with CSingleInit ce => Some ce | _ => None end.

Inductive cstorage := StaticStorage | ExternStorage | AutoStorage.
#[global] Instance cstorage_eq_dec: EqDecision cstorage.
Proof. solve_decision. Defined.

Inductive cstmt : iType :=
  | CSDo : cexpr → cstmt
  | CSSkip : cstmt
  | CSGoto : string → cstmt
  | CSBreak : cstmt
  | CSContinue : cstmt
  | CSReturn : option cexpr → cstmt
  | CSCase : cexpr → cstmt → cstmt
  | CSDefault : cstmt → cstmt
  | CSScope : cstmt → cstmt
  | CSLocal : list cstorage → string → ctype → option cinit → cstmt → cstmt
  | CSTypeDef : string → ctype → cstmt → cstmt
  | CSComp : cstmt → cstmt → cstmt
  | CSLabel : string → cstmt → cstmt
  | CSWhile : cexpr → cstmt → cstmt
  | CSFor : cexpr → cexpr → cexpr → cstmt → cstmt
  | CSDoWhile : cstmt → cexpr → cstmt
  | CSIf : cexpr → cstmt → cstmt → cstmt
  | CSSwitch : cexpr → cstmt → cstmt.

Inductive decl : iType :=
  | CompoundDecl : compound_kind → list (string * ctype) → decl
  | EnumDecl : cint_type → list (string * option cexpr) → decl
  | TypeDefDecl : ctype → decl
  | GlobDecl : list cstorage → ctype → option cinit → decl
  | FunDecl : list cstorage → ctype → cstmt → decl.

Inductive type_decl (K : iType) : iType :=
  | Compound : compound_kind → list (string * type K) → type_decl K
  | Enum : int_type K → type_decl K.
Arguments Compound {_} _ _.
Arguments Enum {_} _.
#[global] Instance maybe_Compound {K} : Maybe2 (@Compound K) := λ t,
  match t with Compound c xs => Some (c,xs) | _ => None end.
#[global] Instance maybe_Enum {K} : Maybe (@Enum K) := λ t,
  match t with Enum τi => Some τi | _ => None end.

Inductive global_decl (K : iType): iType :=
  | Global : cstorage → index → type K → bool → global_decl K
  | Fun: cstorage → list (type K) → type K → option (stmt K) → global_decl K
  | GlobalTypeDef : ptr_type K → global_decl K
  | EnumVal : int_type K → Z → global_decl K.
Arguments Global {_} _ _ _ _.
Arguments Fun {_} _ _ _ _.
Arguments GlobalTypeDef {_} _.
Arguments EnumVal {_} _ _.
#[global] Instance maybe_Fun {K} : Maybe4 (@Fun K) := λ d,
  match d with Fun sto τs τ ms => Some (sto,τs,τ,ms) | _ => None end.
#[global] Instance maybe_GlobalTypeDef {K} : Maybe (@GlobalTypeDef K) := λ d,
  match d with GlobalTypeDef τ => Some τ | _ => None end.

Inductive local_decl (K : iType) : iType :=
  | Extern : (index * type K + list (type K) * type K) → local_decl K
  | Local : type K → local_decl K
  | TypeDef : ptr_type K → local_decl K.
Arguments Extern {_} _.
Arguments Local {_} _.
Arguments TypeDef {_} _.
#[global] Instance maybe_TypeDef {K} : Maybe (@TypeDef K) := λ d,
  match d with TypeDef τ => Some τ | _ => None end.
(** [None] delimits scopes *)
Notation local_env K := (list (option (string * local_decl K))).

Record frontend_state (K : iType) : iType := FState {
  to_compounds : tagmap (type_decl K);
  to_env : env K;
  to_mem : mem K;
  to_globals : stringmap (global_decl K)
}.
Arguments FState {_} _ _ _ _.
Arguments to_compounds {_} _.
Arguments to_env {_} _.
Arguments to_mem {_} _.
Arguments to_globals {_} _.

Local Notation M := (error (frontend_state _) string).

Section frontend.
Context `{Env K}.
Local Notation M := (error (frontend_state K) string).

#[global] Instance empty_frontend_state : Empty (frontend_state K) :=
  FState ∅ ∅ ∅ ∅.

Definition to_funenv (S : frontend_state K) : funenv K :=
  omap (λ d, '(_,_,ms) ← maybe4 Fun d; ms) (to_globals S).
Definition incomplete_fun_decls (S : frontend_state K) : funset :=
  dom _ (env_f (to_env S)) ∖ dom _ (to_funenv S).
Definition extern_global_decls (S : frontend_state K) : stringset :=
  mapset.mapset_dom_with (λ d,
    match d with Global ExternStorage _ _ _ => true | _ => false end)
    (to_globals S).

Definition lookup_compound (t : tag) (x : string) : M (nat * type K) :=
  Γn ← gets to_compounds;
  d ← error_of_option (Γn !! t)
    ("struct/union `" +:+ t +:+ "` undeclared");
  '(_,xτs) ← error_of_option (maybe2 Compound d)
    ("struct/union `" +:+ t +:+ "` instead of enum expected");
  '(i,xτ) ← error_of_option (list_find (λ xτ, x = xτ.1) xτs)
    ("struct/union `" +:+ t +:+ "` does not have index `" +:+ x +:+ "`");
  mret (i,xτ.2).

Fixpoint local_fresh (x : string) (Δl : local_env K) : bool :=
  match Δl with
  | [] | None :: _ => true
  | Some (y,_) :: Δl => if decide (x = y) then false else local_fresh x Δl
  end.

Fixpoint lookup_local_var (Δl : local_env K)
    (x : string) (i : nat) : option (expr K * lrtype K) :=
  match Δl with
  | [] => None
  | Some (y, Extern (inl (o,τ))) :: Δl =>
     if decide (x = y) then Some (% (Ptr (addr_top o τ)), inl (TType τ))
     else lookup_local_var Δl x i
  | Some (y, Extern (inr (τs,τ))) :: Δl =>
     if decide (x = y) then Some (% (FunPtr x τs τ), inl (τs ~> τ))
     else lookup_local_var Δl x i
  | Some (y, Local τ) :: Δl =>
     if decide (x = y) then Some (var i, inl (TType τ))
     else lookup_local_var Δl x (S i)
  | Some (y, TypeDef _) :: Δl =>
     if decide (x = y) then None else lookup_local_var Δl x i
  | None :: Δl => lookup_local_var Δl x i
  end.
Definition lookup_var (Δl : local_env K)
    (x : string) : M (expr K * lrtype K) :=
  match lookup_local_var Δl x 0 with
  | Some (e,τlr) => mret (e,τlr)
  | None =>
     Δg ← gets to_globals;
     match Δg !! x with
     | Some (Global _ o τ _) => mret (% (Ptr (addr_top o τ)), inl (TType τ))
     | Some (EnumVal τi z) => mret (# intV{τi} z, inr (intT τi))
     | Some (Fun _ τs τ _) => mret (% (FunPtr x τs τ), inl (τs ~> τ))
     | _ => fail ("variable `" +:+ x +:+ "` not found")
     end
  end.

Fixpoint lookup_local_typedef (Δl : local_env K)
    (x : string) : option (ptr_type K) :=
  match Δl with
  | [] => None
  | Some (y,d) :: Δl =>
     if decide (x = y) then maybe TypeDef d else lookup_local_typedef Δl x
  | None :: Δl => lookup_local_typedef Δl x
  end.
Definition lookup_typedef (Δl : local_env K) (x : string) : M (ptr_type K) :=
  match lookup_local_typedef Δl x with
  | Some τp => mret τp
  | None =>
     Δg ← gets to_globals;
     error_of_option (Δg !! x ≫= maybe GlobalTypeDef)
       ("typedef `" +:+ x +:+ "` not found")
  end.

Definition is_pseudo_NULL (e : expr K) : bool :=
  match e with #{_} (intV{_} 0) => true | _ => false end.
Definition to_R (e : expr K) (τlr : lrtype K) : M (expr K * type K) :=
  match τlr with
  | inl (TType τ) =>
     match maybe2 TArray τ with
     | Some (τ',n) => mret (&(e %> RArray 0 τ' n), TType τ'.*)
     | None =>
        Γ ← gets to_env;
        guard (type_complete Γ τ) with
          "l-value conversion of expression with incomplete type";
        mret (load e, τ)
     end
  | inl (τs ~> τ) => mret (&e, (τs ~> τ).*)
  | inl TAny => fail "l-value conversion of expression with void type"
  | inr τ => mret (e,τ)
  end.
Definition to_R_NULL (σ : type K)
    (e : expr K) (τlr : lrtype K) : M (expr K * type K) :=
  '(e,τ) ← to_R e τlr;
  match σ with
  | σp.* =>
     if is_pseudo_NULL e then mret (# ptrV (NULL σp), σp.*) else mret (e,τ)
  | _ => mret (e,τ)
  end.
Definition convert_ptrs (eτ1 eτ2 : expr K * type K) :
    option (expr K * expr K * type K) :=
  let (e1,τ1) := eτ1 in let (e2,τ2) := eτ2 in
  match τ1, τ2 with
  | TAny.*, TType _.* => Some (e1, cast{TAny.*} e2, TAny.*)
  | TType _.*, TAny.* => Some (cast{TAny.*} e1, e2, TAny.*)
  | τp1.*, intT _ =>
     guard (is_pseudo_NULL e2); Some (e1, # ptrV (NULL τp1), τp1.*)
  | intT _, τp2.* =>
     guard (is_pseudo_NULL e1); Some (# ptrV (NULL τp2), e2, τp2.*)
  | _, _ => None
  end.
Definition to_if_expr (e1 : expr K)
    (eτ2 eτ3 : expr K * type K) : option (expr K * lrtype K) :=
  (**i 1.) *) (
    (** same types *)
    let (e2,τ2) := eτ2 in let (e3,τ3) := eτ3 in
    guard (τ2 = τ3); Some (if{e1} e2 else e3, inr τ2)) ∪
  (**i 2.) *) (
    (** common arithmetic conversions *)
    let (e2,τ2) := eτ2 in let (e3,τ3) := eτ3 in
    match τ2, τ3 with
    | intT τi2, intT τi3 =>
       let τi' := int_promote τi2 ∪ int_promote τi3 in
       Some (if{e1} cast{intT τi'} e2 else cast{intT τi'} e3, inr (intT τi'))
    | _, _ => None
    end) ∪
  (**i 3.) *) (
    (** one side is NULL or void *)
    '(e2,e3,τ) ← convert_ptrs eτ2 eτ3;
    Some (if{e1} e2 else e3, inr τ)).
Definition to_binop_expr (op : binop)
    (eτ1 eτ2 : expr K * type K) : option (expr K * lrtype K) :=
  (**i 1.) *) (
    let (e1,τ1) := eτ1 in let (e2,τ2) := eτ2 in
    σ ← binop_type_of op τ1 τ2; Some (e1 .{op} e2, inr σ)) ∪
  (**i 2.) *) (
    (** one side is NULL or void *)
    guard (op = CompOp EqOp);
    '(e1,e2,τ) ← convert_ptrs eτ1 eτ2;
    σ ← binop_type_of (CompOp EqOp) τ τ;
    Some (e1 .{op} e2, inr σ)).

Definition int_const_types (cτi : cint_type) : list (int_type K) :=
  let (ms,k) := cτi in
  let s := default Signed ms in
  match k with
  | CLongLongRank => [IntType s longlong_rank]
  | CLongRank => [IntType s long_rank; IntType s longlong_rank]
  | _ => [IntType s int_rank; IntType s long_rank; IntType s longlong_rank]
  end.
Definition to_int_const (x : Z) : list (int_type K) → option (int_type K) :=
  fix go τis :=
  match τis with
  | [] => None
  | τi :: τis => if decide (int_typed x τi) then Some τi else go τis
  end.
Definition to_inttype (cτi : cint_type) : int_type K :=
  let (ms,k) := cτi in
  match k with
  | CCharRank => IntType (default char_signedness ms) char_rank
  | CShortRank => IntType (default Signed ms) short_rank
  | CIntRank => IntType (default Signed ms) int_rank
  | CLongRank => IntType (default Signed ms) long_rank
  | CLongLongRank => IntType (default Signed ms) longlong_rank
  | CPtrRank => IntType (default Signed ms) ptr_rank
  end.
Definition to_string_const (zs : list Z) : option (val K * nat) :=
  guard (Forall (λ z, int_typed z charT) zs);
  mret (VArray (intT charT)
    (VBase <$> (VInt charT <$> (zs ++ [0%Z]))), S (length zs)).
Definition to_limit_const (τ : type K) (li : climit) : M (Z * int_type K) :=
  match li with
  | CESizeOf =>
     guard (τ ≠ voidT) with "sizeof of void type";
     Γ ← gets to_env; let sz := size_of Γ τ in
     guard (int_typed sz uptrT) with "argument of sizeof not in range";
     mret (Z.of_nat sz, uptrT%IT)
  | CEAlignOf =>
     guard (τ ≠ voidT) with "alignof of void type";
     Γ ← gets to_env; let sz := align_of Γ τ in
     guard (int_typed sz uptrT) with "argument of sizeof not in range";
     mret (Z.of_nat sz, uptrT%IT)
  | CEOffsetOf x =>
     '(c,t) ← error_of_option (maybe2 TCompound τ)
       "argument of offsetof not of struct type";
     if decide (c = Union_kind) then mret (0%Z, sptrT%IT) else
     '(i,_) ← lookup_compound t x;
     Γ ← gets to_env;
     τs ← error_of_option (Γ !! t) "argument of offsetof incomplete";
     let off := offset_of Γ τs i in
     guard (int_typed off uptrT) with "argument of offsetof not in range";
     mret (Z.of_nat off, uptrT%IT)
  | CEMin =>
     τi ← error_of_option (maybe (TBase ∘ TInt) τ) "min of non integer type";
     mret (int_lower τi, τi)
  | CEMax =>
     τi ← error_of_option (maybe (TBase ∘ TInt) τ) "max of non integer type";
     mret ((int_upper τi - 1)%Z, τi)
  | CEBits =>
     τi ← error_of_option (maybe (TBase ∘ TInt) τ) "bits of non integer type";
     mret (Z.of_nat (int_width τi), τi)
  end.

Definition insert_object (γ : perm) (v : val K) : M index :=
  m ← gets to_mem; Γ ← gets to_env;
  let o := fresh (dom indexset m) in
  _ ← modify (λ S : frontend_state K,
    let (Γn,Γ,m,Δg) := S in FState Γn Γ (mem_alloc Γ o false γ v m) Δg);
  mret o.
Definition update_object (o : index) (γ : perm) (v : val K) : M () :=
  modify (λ S : frontend_state K,
    let (Γn,Γ,m,Δg) := S in FState Γn Γ (mem_alloc Γ o false γ v m) Δg).
Definition insert_global_decl (x : string) (d : global_decl K) : M () :=
  modify (λ S : frontend_state K,
    let (Γn,Γ,m,Δg) := S in FState Γn Γ m (<[x:=d]>Δg)).
Definition insert_fun (f : funname) (sto : cstorage)
    (τs : list (type K)) (σ : type K) (ms : option (stmt K)) : M () :=
  modify (λ S : frontend_state K,
    let (Γn,Γ,m,Δg) := S in
    FState Γn (<[f:=(τs,σ)]>Γ) m (<[(f:string):=Fun sto τs σ ms]>Δg)).
Definition insert_compound (c : compound_kind) (t : tag)
    (xτs : list (string * type K)) : M () :=
  modify (λ S : frontend_state K,
    let (Γn,Γ,m,Δg) := S in
    FState (<[t:=Compound c xτs]>Γn) (<[t:=xτs.*2]>Γ) m Δg).
Definition insert_enum (t : tag) (τi : int_type K) : M () :=
  modify (λ S : frontend_state K,
    let (Γn,Γ,m,Δg) := S in FState (<[t:=Enum τi]>Γn) Γ m Δg).

Definition first_init_ref (Γ : env K)
    (τ : type K) : option (ref K * type K) :=
  match τ with
  | τ.[n] => Some ([RArray 0 τ n], τ)
  | structT t => τ ← Γ !! t ≫= (.!! 0); Some ([RStruct 0 t],τ)
  | unionT t => τ ← Γ !! t ≫= (.!! 0); Some ([RUnion 0 t false],τ)
  | _ => None
  end.
Fixpoint next_init_ref (Γ : env K)
    (r : ref K) : option (ref K * type K) :=
  match r with
  | RArray i τ n :: r =>
     if decide (S i < n)
     then Some (RArray (S i) τ n :: r, τ) else next_init_ref Γ r
  | RStruct i t :: r =>
     match Γ !! t ≫= (.!! (S i)) with
     | Some τ => Some (RStruct (S i) t :: r,τ) | None => next_init_ref Γ r
     end
  | RUnion _ _ _ :: r => next_init_ref Γ r
  | _ => None
  end.
Definition to_ref
    (to_expr : cexpr → M (expr K * lrtype K)) :
    ref K → type K → list (string + cexpr) → M (ref K * type K) :=
  fix go r (τ : type K) xces {struct xces} :=
  match xces with
  | [] => mret (r,τ)
  | inl x :: xces =>
     '(c,t) ← error_of_option (maybe2 TCompound τ)
       "struct/union initializer used for non-compound type";
     '(i,τ) ← lookup_compound t x;
     let rs :=
       match c with
       | Struct_kind => RStruct i t | Union_kind => RUnion i t false
       end in
     go (rs :: r) τ xces
  | inr ce :: xces =>
     '(σ,n) ← error_of_option (maybe2 TArray τ)
       "array initializer used for non-array type";
     '(e,_) ← to_expr ce;
     guard (is_pure e) with
       "array initializer with non-constant index";
     Γ ← gets to_env; m ← gets to_mem;
     v ← error_of_option (⟦ e ⟧ Γ [] m ≫= maybe inr)
       "array initializer with undefined index";
     '(_,x) ← error_of_option (maybe VBase v ≫= maybe2 VInt)
       "array initializer with non-integer index";
     let i := Z.to_nat x in
     guard (i < n) with "array initializer with index out of bounds";
     go (RArray i σ n :: r) σ xces
  end.

Definition to_compound_init
    (to_expr : cexpr → M (expr K * lrtype K))
    (to_init_expr : type K → cinit → M (expr K))
    (τ : type K) : expr K → list (ref K) →
    list (list (string + cexpr) * cinit) → M (expr K) :=
  fix go e seen inits {struct inits} :=
  match inits with
  | [] => mret e
  | (xces,ci) :: inits =>
     Γ ← gets to_env;
     '(r,σ) ← if decide (xces = [])
        then error_of_option
               match seen with
               | [] => first_init_ref Γ τ | r :: _ => next_init_ref Γ r
               end "excess elements in compound initializer"
        else to_ref to_expr [] τ xces;
     guard (Forall (r ##.) seen) with "element initialized before";
     e1 ← to_init_expr σ ci;
     go (#[r:=e1] e) (r :: seen) inits
  end.
Definition to_call_fun (e : expr K) (τlr : lrtype K) :
    option (expr K * list (type K) * type K) :=
  match τlr with
  | inl (τs ~> σ) => Some (e,τs,σ)
  | inl (TType τ) =>
     '(τs,σ) ← maybe (TBase ∘ TPtr) τ ≫= maybe2 TFun; Some (.*(load e),τs,σ)
  | inl TAny => None
  | inr τ => '(τs,σ) ← maybe (TBase ∘ TPtr) τ ≫= maybe2 TFun; Some (.*e,τs,σ)
  end.
Definition to_call_args
    (to_expr : cexpr → M (expr K * lrtype K)) :
    list cexpr → list (type K) → M (list (expr K)) :=
  fix go ces τs :=
  match ces, τs with
  | [], [] => mret []
  | ce :: ces, τ :: τs =>
     '(e,σ) ← to_expr ce ≫= uncurry (to_R_NULL τ);
     Γ ← gets to_env;
     guard (cast_typed σ τ)
       with "function applied to arguments of incorrect type";
     (cast{τ} e ::.) <$> go ces τs
  | _, _ => fail "function applied to the wrong number of arguments"
  end.
Definition convert_fun_arg_type (τp : ptr_type K) : option (type K) :=
  match τp with
  | TType (τ.[_]) => Some (TType τ.*)
  | TType τ => Some τ
  | τs ~> τ => Some ((τs ~> τ).*)
  | TAny => None
  end.
Definition convert_fun_ret_type (τp : ptr_type K) : option (type K) :=
  match τp with
  | TType τ => Some τ
  | TAny => Some voidT
  | _ => None
  end.
Definition to_fun_type_args
    (to_ptr_type : ctype → M (ptr_type K)) :
    list (option string * ctype) → M (list (option string * type K)) :=
  fix go cτs :=
  match cτs with
  | [] => mret []
  | (mx,cτ) :: cτs =>
     τp ← to_ptr_type cτ;
     τ ← error_of_option (convert_fun_arg_type τp)
       "function type with argument of void type";
     ((mx,τ) ::.) <$> go cτs
  end.
Definition fun_empty_args (xτs : list (option string * ctype)) : bool :=
  match xτs with [(None,CTVoid)] => true | _ => false end.
Definition to_fun_type (to_ptr_type : ctype → M (ptr_type K))
    (cτs : list (option string * ctype)) (cτ : ctype) :
    M (list (option string * type K) * type K) :=
  τp ← to_ptr_type cτ;
  τ ← error_of_option (convert_fun_ret_type τp)
    "function type returning function or array";
  if fun_empty_args cτs then mret ([],τ) else
  xτs ← to_fun_type_args to_ptr_type cτs;
  guard (NoDup (omap fst xτs)) with
    "function type with duplicate argument names";
  mret (xτs,τ).

Definition rhs_6_5_16_1p3_safe : expr K → bool :=
  fix go e :=
  match e with
  | load (var _) => true (* local *)
  | load (%{_} _) => true (* global/static *)
  | load _ => false (* load of pointer *)
  | #{_} _ => true
  | & e => true
  | _ ::={_} _ => true
  | call _ @ _ => true
  | abort _ => true
  | e #> (RArray _ _ _ | RStruct _ _) => go e
  | e #> (RUnion _ _ _) => false
  | alloc{_} _ => true
  | free e => true
  | .{_} e => go e
  | e1 .{_} e2 => go e1 && go e2
  | if{_} e2 else e3 => go e2 && go e3
  | _,, e2 => go e2
  | cast{_} e => go e
  | #[_:=_ ] _ => true (* compound literal *)
  | _ => false (* l-values, cannot occur *)
  end.
Definition to_field_ref_seg
    (c : compound_kind) (i : nat) (t : tag) : ref_seg K :=
  match c with
  | Struct_kind => RStruct i t | Union_kind => RUnion i t false
  end.

Inductive to_type_kind := to_Type | to_Ptr.
Definition to_type_type {K} (k : to_type_kind) :=
  match k with to_Type => type K | to_Ptr => ptr_type K end.
Definition to_type_ret {k} (τ : type K) : M (to_type_type k) :=
  match k return M (to_type_type k)
  with to_Type => mret τ | to_Ptr => mret (TType τ) end.
End frontend.

(* not in the section because of bug #3488 *)
Fixpoint to_expr `{Env K} (Δl : local_env K)
    (ce : cexpr) : M (expr K * lrtype K) :=
  match ce return M (expr K * lrtype K) with
  | CEVar x => lookup_var Δl x
  | CEConst cτi z =>
     τi ← error_of_option (to_int_const z (int_const_types cτi))
       ("integer constant " +:+ pretty z +:+ " too large");
     mret (# (intV{τi} z), inr (intT τi))
  | CEConstString zs =>
     '(v,n) ← error_of_option (to_string_const zs)
       "char of string constant out of range";
     o ← insert_object perm_readonly v;
     mret (% (Ptr (addr_top o (charT.[n]))), inl (TType (charT.[n])))
  | CELimit cτ li =>
     τ ← to_type to_Type Δl cτ;
     '(z,τi) ← to_limit_const τ li;
     mret (# intV{τi} z, inr (intT τi))
  | CEDeref ce =>
     '(e,τ) ← to_expr Δl ce ≫= uncurry to_R;
     τp ← error_of_option (maybe (TBase ∘ TPtr) τ)
       "dereferencing non-pointer type";
     mret (.* e, inl τp)
  | CEAddrOf ce =>
     '(e,τlr) ← to_expr Δl ce;
     τp ← error_of_option (maybe inl τlr) "taking address of r-value";
     mret (& e, inr (τp.*))
  | CEAssign ass ce1 ce2 =>
     '(e1,τlr1) ← to_expr Δl ce1;
     τ1 ← error_of_option (maybe (inl ∘ TType) τlr1) "assigning to r-value";
     '(e2,τ2) ← to_expr Δl ce2 ≫= uncurry (to_R_NULL τ1);
     Γ ← gets to_env;
     guard (assign_typed τ1 τ2 ass) with "assignment cannot be typed";
     let e1 :=
       if decide (ass = Assign ∧ ¬rhs_6_5_16_1p3_safe e2)
       then freeze true e1 else e1 in
     mret (e1 ::={ass} e2, inr τ1)
  | CECall ce ces =>
     '(e,τlr) ← to_expr Δl ce;
     '(e,τs,σ) ← error_of_option (to_call_fun e τlr)
       "called object is not a function";
     Γ ← gets to_env;
     guard (type_complete Γ σ) with "function called with incomplete type";
     es ← to_call_args (to_expr Δl) ces τs;
     mret (call e @ es, inr σ)
  | CEAbort => mret (abort voidT, inr voidT)
  | CEAlloc cτ ce =>
     τ ← to_type to_Type Δl cτ;
     guard (τ ≠ voidT) with "alloc of void type";
     '(e,τsz) ← to_expr Δl ce ≫= uncurry to_R;
     _ ← error_of_option (maybe (TBase ∘ TInt) τsz)
       "alloc applied to argument of non-integer type";
     mret (&(alloc{τ} e), inr (TType τ.*))
  | CEFree ce =>
     '(e,τ) ← to_expr Δl ce ≫= uncurry to_R;
     τp ← error_of_option (maybe (TBase ∘ TPtr ∘ TType) τ)
       "free applied to argument of non-pointer type";
     Γ ← gets to_env;
     guard (type_complete Γ τp)
       with "free applied to argument of incomplete pointer type";
     mret (free (.* e), inr voidT)
  | CEUnOp op ce =>
     '(e,τ) ← to_expr Δl ce ≫= uncurry to_R;
     σ ← error_of_option (unop_type_of op τ) "unary operator cannot be typed";
     mret (.{op} e, inr σ)
  | CEBinOp op ce1 ce2 =>
     eτ1 ← to_expr Δl ce1 ≫= uncurry to_R;
     eτ2 ← to_expr Δl ce2 ≫= uncurry to_R;
     error_of_option (to_binop_expr op eτ1 eτ2)
       "binary operator cannot be typed"
  | CEIf ce1 ce2 ce3 =>
     '(e1,τ1) ← to_expr Δl ce1 ≫= uncurry to_R;
     τb ← error_of_option (maybe TBase τ1)
       "conditional argument of if expression of non-base type";
     guard (τb ≠ TVoid) with
       "conditional argument of if expression of void type";
     eτ2 ← to_expr Δl ce2 ≫= uncurry to_R;
     eτ3 ← to_expr Δl ce3 ≫= uncurry to_R;
     error_of_option (to_if_expr e1 eτ2 eτ3) "if expression cannot be typed"
  | CEComma ce1 ce2 =>
     '(e1,τ1) ← to_expr Δl ce1 ≫= uncurry to_R;
     '(e2,τ2) ← to_expr Δl ce2 ≫= uncurry to_R;
     mret (cast{voidT} e1,, e2, inr τ2)
  | CEAnd ce1 ce2 =>
     '(e1,τ1) ← to_expr Δl ce1 ≫= uncurry to_R;
     τb1 ← error_of_option (maybe TBase τ1)
       "first argument of && of non-base type";
     guard (τb1 ≠ TVoid) with "first argument of && of void type";
     '(e2,τ2) ← to_expr Δl ce2 ≫= uncurry to_R;
     τb2 ← error_of_option (maybe TBase τ2)
       "second argument of && of non-base type";
     guard (τb2 ≠ TVoid) with "second argument of && of void type";
     mret (if{e1} if{e2} # intV{sintT} 1 else # intV{sintT} 0
       else #(intV{sintT} 0), inr sintT)
  | CEOr ce1 ce2 =>
     '(e1,τ1) ← to_expr Δl ce1 ≫= uncurry to_R;
     τb1 ← error_of_option (maybe TBase τ1)
       "first argument of || of non-base type";
     guard (τb1 ≠ TVoid) with "first argument of || of void type";
     '(e2,τ2) ← to_expr Δl ce2 ≫= uncurry to_R;
     τb2 ← error_of_option (maybe TBase τ2)
       "second argument of || of non-base type";
     guard (τb2 ≠ TVoid) with "second argument of || of void type";
     mret (if{e1} # intV{sintT} 0
       else (if{e2} # intV{sintT} 1 else #(intV{sintT} 0)), inr sintT)
  | CECast cσ ci =>
     σ ← to_type to_Type Δl cσ;
     guard (maybe2 TArray σ = None) with "array compound literal not supported";
     guard (maybe CSingleInit ci = None ∨ maybe2 TCompound σ = None) with
       "cast to struct/union not allowed";
     e ← to_init_expr Δl σ ci;
     mret (e, inr σ)
  | CEField ce x =>
     '(e,τlr) ← to_expr Δl ce;
     match τlr with
     | inl τp =>
        '(c,t) ← error_of_option (maybe TType τp ≫= maybe2 TCompound)
          "field operator applied to argument of non-compound type";
        '(i,σ) ← lookup_compound t x;
        mret (e %> to_field_ref_seg c i t, inl (TType σ))
     | inr τ =>
        '(c,t) ← error_of_option (maybe2 TCompound τ)
          "field operator applied to argument of non-compound type";
        '(i,σ) ← lookup_compound t x;
        guard (maybe2 TArray σ = None) with
          "indexing array field of r-value struct/union not supported";
        mret (e #> to_field_ref_seg c i t, inr σ)
     end
  end
with to_init_expr `{Env K} (Δl : local_env K)
    (σ : type K) (ci : cinit) : M (expr K) :=
  match ci with
  | CSingleInit ce =>
     match maybe CEConstString ce with
     | Some zs =>
        '(v,n) ← error_of_option (to_string_const zs)
          "char of string initializer out of range";
        if decide (σ = type_of v) then mret (# v) else
        if decide (σ = charT.*) then
          o ← insert_object perm_readonly v;
          mret (& ((% Ptr (addr_top o (charT.[n]))) %> RArray 0 charT n))
        else fail "string initializer of wrong type or size"
     | None =>
        '(e,τ) ← to_expr Δl ce ≫= uncurry (to_R_NULL σ);
        Γ ← gets to_env;
        guard (cast_typed τ σ) with "cast or initializer cannot be typed";
        mret (cast{σ} e)
     end
  | CCompoundInit inits =>
     Γ ← gets to_env;
     to_compound_init (to_expr Δl) (to_init_expr Δl) σ (# val_0 Γ σ) [] inits
  end
with to_type `{Env K} (k : to_type_kind)
    (Δl : local_env K) (cτ : ctype) : M (to_type_type k) :=
  match cτ with
  | CTVoid =>
     match k return M (to_type_type k) with to_Type => mret voidT | to_Ptr => mret TAny end
  | CTDef x =>
     τp ← lookup_typedef Δl x;
     match k return M (to_type_type k) with
     | to_Ptr => mret τp
     | to_Type =>
        match τp with
        | TType τ =>
           Γ ← gets to_env;
           guard (type_complete Γ τ) with "complete typedef expected";
           mret τ
        | TAny => mret voidT
        | _ => fail "complete typedef expected"
        end
     end
  | CTEnum x =>
     let t : tag := x in
     Γn ← gets to_compounds;
     τi ← error_of_option (Γn !! t ≫= maybe Enum)
       ("enum `" +:+ x +:+ "` not found");
     to_type_ret (intT τi)
  | CTInt cτi => to_type_ret (intT (to_inttype cτi))
  | CTPtr cτ => τp ← to_type to_Ptr Δl cτ; to_type_ret (τp.*)
  | CTArray cτ ce =>
     τ ← to_type to_Type Δl cτ;
     guard (τ ≠ voidT) with "array with elements of void type";
     '(e,_) ← to_expr Δl ce;
     guard (is_pure e) with "array with non-constant size expression";
     Γ ← gets to_env; m ← gets to_mem;
     v ← error_of_option (⟦ e ⟧ Γ [] m ≫= maybe inr)
       "array with undefined size expression";
     '(_,x) ← error_of_option (maybe VBase v ≫= maybe2 VInt)
       "array with non-integer size expression";
     let n := Z.to_nat x in
     guard (n ≠ 0) with "array with negative or zero size expression";
     to_type_ret (τ.[n])
  | CTCompound c x =>
     let t : tag := x in
     match k with
     | to_Ptr => mret (compoundT{c} t)%PT
     | to_Type =>
        Γ ← gets to_env;
        guard (is_Some (Γ !! t)) with "complete compound type expected";
        mret (compoundT{c} t)
     end
  | CTFun cτs cτ =>
     match k with
     | to_Type => fail "complete type expected"
     | to_Ptr =>
        '(xτs,τ) ← to_fun_type (to_type to_Ptr Δl) cτs cτ;
        mret (xτs.*2 ~> τ)
     end
  | CTTypeOf ce =>
     '(_,τlr) ← to_expr Δl ce;
     match τlr with
     | inl (TType τ) =>
        Γ ← gets to_env;
        guard (type_complete Γ τ) with "complete typeof expected";
        to_type_ret τ
     | inr τ => to_type_ret τ
     | _ => fail "typeof of function"
     end
  end.

Section frontend_more.
Context `{Env K}.

Definition to_init_val (Δl : local_env K)
     (τ : type K) (ci : cinit) : M (val K) :=
   e ← to_init_expr Δl τ ci;
   Γ ← gets to_env; m ← gets to_mem;
   guard (is_pure e) with "initializer with non-constant expression";
   error_of_option (⟦ e ⟧ Γ [] m ≫= maybe inr)
     "initializer with undefined expression".
Definition alloc_global (Δl : local_env K) (x : string) (sto : cstorage)
    (cτ : ctype) (mci : option cinit) :
    M (index * type K + list (type K) * type K) :=
  τp ← to_type to_Ptr Δl cτ;
  Δg ← gets to_globals;
  match Δg !! x with
  | Some (Global sto' o τ init) =>
     guard (τp = TType τ) with
       ("global `" +:+ x +:+ "` previously declared with different type");
     guard (sto = ExternStorage ∨ sto = sto'
         ∨ sto = AutoStorage ∧ sto' = ExternStorage) with
       ("global `" +:+ x +:+ "` previously declared with different linkage");
     match mci with
     | Some ci =>
        guard (sto ≠ ExternStorage) with
          ("global `" +:+ x +:+ "` initialized and declared `extern`");
        guard (init = false) with
          ("global `" +:+ x +:+ "` already initialized");
        _ ← insert_global_decl x (Global sto o τ true); (* update storage *)
        v ← to_init_val Δl τ ci;
        _ ← update_object o perm_full v;
        mret (inl (o,τ))
     | None => mret (inl (o,τ))
     end
  | Some (Fun sto' τs σ ms) =>
     guard (τp = τs ~> σ) with
       ("function previously `" +:+ x +:+ "` declared with different type");
     guard (sto = ExternStorage ∨ sto = sto'
         ∨ sto = AutoStorage ∧ sto' = ExternStorage) with
       ("function `" +:+ x +:+ "` previously declared with different linkage");
     guard (mci = None) with ("function `" +:+ x +:+ "` with initializer");
     _ ← insert_fun x sto τs σ ms; (* update storage *)
     mret (inr (τs,σ))
  | Some (GlobalTypeDef _) =>
     fail ("global `" +:+ x +:+ "` previously declared as typedef")
  | Some (EnumVal _ _) =>
     fail ("global `" +:+ x +:+ "` previously declared as enum tag")
  | None =>
     match τp with
     | τs ~> σ =>
        Γ ← gets to_env;
        guard (mci = None) with ("function `" +:+ x +:+ "` with initializer");
        _ ← insert_fun x sto τs σ None;
        mret (inr (τs,σ))
     | TType τ =>
        Γ ← gets to_env;
        guard (type_complete Γ τ) with
          ("global `" +:+ x +:+ "` with incomplete type");
        match mci with
        | Some ci =>
           o ← insert_object perm_full (val_new Γ τ);
           _ ← insert_global_decl x (Global sto o τ true);
           v ← to_init_val Δl τ ci;
           _ ← update_object o perm_full v;
           mret (inl (o,τ))
        | None =>
           o ← insert_object perm_full (val_0 Γ τ);
           _ ← insert_global_decl x (Global sto o τ false);
           mret (inl (o,τ))
        end
     | TAny => fail ("global `" +:+ x +:+ "` of void type")
     end
  end.
Definition alloc_static (Δl : local_env K) (x : string) (cτ : ctype)
    (mci : option cinit) : M (index * type K) :=
  τ ← to_type to_Type Δl cτ;
  guard (τ ≠ voidT) with ("static `" +:+ x +:+ "` of void type");
  Γ ← gets to_env;
  match mci with
  | Some ci =>
     o ← insert_object perm_full (val_new Γ τ);
     v ← to_init_val (Some (x, Extern (inl (o,τ))) :: Δl) τ ci;
     _ ← update_object o perm_full v;
     mret (o, τ)
  | None => (.,τ) <$> insert_object perm_full (val_0 Γ τ)
  end.
Definition to_storage (stos : list cstorage) : option cstorage :=
  match stos with [] => Some AutoStorage | [sto] => Some sto | _ => None end.
Notation break_continue := (option nat * option nat)%type.
Definition to_stmt (τret : type K) :
    break_continue → local_env K → cstmt → M (stmt K * rettype K) :=
  fix go bc Δl cs {struct cs} :=
  match cs with
  | CSDo ce =>
     '(e,_) ← to_expr Δl ce ≫= uncurry to_R;
     mret (!(cast{voidT} e), (false, None))
  | CSSkip => mret (skip, (false, None))
  | CSGoto l => mret (goto l, (true, None))
  | CSBreak =>
    n ← error_of_option (bc.1) "unbound break";
    mret (throw n, (true, None))
  | CSContinue =>
     n ← error_of_option (bc.2) "unbound break";
     mret (throw n, (true, None))
  | CSReturn (Some ce) =>
     guard (τret ≠ voidT) with
       "return with expression in function returning void";
     '(e,τ) ← to_expr Δl ce ≫= uncurry (to_R_NULL τret);
     Γ ← gets to_env;
     guard (cast_typed τ τret) with "return expression has incorrect type";
     mret (ret (cast{τret} e), (true, Some τret))
  | CSReturn None =>
     guard (τret = voidT) with "return with no expression in non-void function";
     mret (ret (#voidV), (true, Some voidT))
  | CSCase ce cs =>
     '(e,_) ← to_expr Δl ce;
     guard (is_pure e) with "case with non-constant expression";
     Γ ← gets to_env; m ← gets to_mem;
     v ← error_of_option (⟦ e ⟧ Γ [] m ≫= maybe inr)
       "case with undefined expression";
     '(_,x) ← error_of_option (maybe VBase v ≫= maybe2 VInt)
       "case with non-integer expression";
     '(s,cmσ) ← go bc Δl cs;
     mret ((scase (Some x) ;; s)%S, cmσ)   
  | CSDefault cs => '(s,cmσ) ← go bc Δl cs; mret ((scase None ;; s)%S, cmσ)
  | CSScope cs => go bc (None :: Δl) cs
  | CSLocal stos x cτ mce cs =>
     guard (local_fresh x Δl) with
       ("block scope variable `" +:+ x +:+ "` previously declared");
     match to_storage stos with
     | Some StaticStorage =>
        '(o,τ) ← alloc_static Δl x cτ mce;
        go bc (Some (x, Extern (inl (o,τ))) :: Δl) cs
     | Some ExternStorage =>
        guard (mce = None) with ("block scope variable `" +:+ x +:+
          "` has both `extern` and an initializer");
        decl ← alloc_global Δl x ExternStorage cτ None;
        go bc (Some (x, Extern decl) :: Δl) cs
     | Some AutoStorage =>
        τ ← to_type to_Type Δl cτ;
        guard (τ ≠ voidT) with
          ("block scope variable `" +:+ x +:+ "` of void type");
        Γ ← gets to_env;
        match mce with
        | Some ce =>
           e ← to_init_expr (Some (x,Local τ) :: Δl) τ ce;
           '(s,cmσ) ← go bc (Some (x,Local τ) :: Δl) cs;
           mret (local{τ} (var 0 ::= e ;; s), cmσ)
        | None =>
           '(s,cmσ) ← go bc (Some (x,Local τ) :: Δl) cs;
           mret (local{τ} s, cmσ)
        end
     | _ => fail ("block scope variable `" +:+ x +:+
                  "` has multiple storage specifiers")
     end
  | CSTypeDef x cτ cs =>
     guard (local_fresh x Δl) with
       ("typedef `" +:+ x +:+ "` previously declared");
     τp ← to_type to_Ptr Δl cτ;
     go bc (Some (x,TypeDef τp) :: Δl) cs
  | CSComp cs1 cs2 =>
     '(s1,cmσ1) ← go bc Δl cs1;
     '(s2,cmσ2) ← go bc Δl cs2;
     mσ ← error_of_option (rettype_union_alt (cmσ1.2) (cmσ2.2))
       "composition of statements with non-matching return types";
     mret ((s1 ;; s2)%S, (cmσ2.1, mσ))
  | CSLabel l cs => '(s,cmσ) ← go bc Δl cs; mret (l :; s, cmσ)
  | CSWhile ce cs =>
     '(e,τ) ← to_expr Δl ce ≫= uncurry to_R;
     τb ← error_of_option (maybe TBase τ)
       "conditional argument of while statement of non-base type";
     guard (τb ≠ TVoid) with
       "conditional argument of while statement of void type";
     '(s,cmσ) ← go (Some 1, Some 0) Δl cs;
     mret (catch (loop (if{e} skip else throw 0 ;; catch s)), (false, cmσ.2))
  | CSFor ce1 ce2 ce3 cs =>
     '(e1,τ1) ← to_expr Δl ce1 ≫= uncurry to_R;
     '(e2,τ2) ← to_expr Δl ce2 ≫= uncurry to_R;
     '(e3,τ3) ← to_expr Δl ce3 ≫= uncurry to_R;
     '(s,cmσ) ← go (Some 1, Some 0) Δl cs;
     τb ← error_of_option (maybe TBase τ2)
       "conditional argument of for statement of non-base type";
     guard (τb ≠ TVoid) with
       "conditional argument of for statement of void type";
     mret ((!(cast{voidT} e1) ;;
       catch (loop (
         if{e2} skip else throw 0 ;; catch s ;; !(cast{voidT} e3)
       )))%S, (false, cmσ.2))
  | CSDoWhile cs ce =>
     '(s,cmσ) ← go (Some 1, Some 0) Δl cs;
     '(e,τ) ← to_expr Δl ce ≫= uncurry to_R;
     τb ← error_of_option (maybe TBase τ)
       "conditional argument of do-while statement of non-base type";
     guard (τb ≠ TVoid) with
       "conditional argument of do-while statement of void type";
     mret (catch (loop (catch s ;; if{e} skip else throw 0)), (false, cmσ.2))
  | CSIf ce cs1 cs2 =>
     '(e,τ) ← to_expr Δl ce ≫= uncurry to_R;
     '(s1,cmσ1) ← go bc Δl cs1;
     '(s2,cmσ2) ← go bc Δl cs2;
     τb ← error_of_option (maybe TBase τ)
       "conditional argument of if statement of non-base type";
     guard (τb ≠ TVoid) with
       "conditional argument of if statement of void type";
     mσ ← error_of_option (rettype_union_alt (cmσ1.2) (cmσ2.2))
       "if statement with non-matching return types";
     mret (if{e} s1 else s2, (cmσ1.1 && cmσ2.1, mσ))%S
  | CSSwitch ce cs =>
     '(e,τ) ← to_expr Δl ce ≫= uncurry to_R;
     τi ← error_of_option (maybe (TBase ∘ TInt) τ)
       "conditional argument of switch statement of non-integer type";
     '(s,cmσ) ← go (Some 0, S <$> bc.2) Δl cs;
     mret (catch (switch{e} s), (false, cmσ.2))
  end.
Definition stmt_fix_return (Γ : env K) (f : string) (σ : type K) (s : stmt K)
    (cmτ : rettype K) : stmt K * rettype K :=
  match cmτ with
  | (false, _) =>
     if decide (σ = voidT) then (s,cmτ)
     else if decide (f = "main") then ((s;; ret (# val_0 Γ σ))%S, (true, Some σ))
     else ((s;; ret (abort σ))%S, (true, Some σ))
  | _ => (s,cmτ)
  end.
Definition to_fun_stmt (f : string) (mys : list (option string))
     (τs : list (type K)) (σ : type K) (cs : cstmt) : M (stmt K) :=
  ys ← error_of_option (mapM id mys)
    ("function `" +:+ f +:+ "` has unnamed arguments");
  '(s,cmσ) ← to_stmt σ (None,None) (zip_with (λ y τ, Some (y, Local τ)) ys τs) cs;
  Γ ← gets to_env;
  let (s,cmσ) := stmt_fix_return Γ f σ s cmσ in
  guard (gotos s ⊆ labels s) with
    ("function `" +:+ f +:+ "` has unbound gotos");
  mret s.
Definition alloc_fun (f : string)
    (sto : cstorage) (cσ : ctype) (cs : cstmt)  : M () :=
  '(cτs,cτ) ← error_of_option (maybe2 CTFun cσ)
     ("function `" +:+ f +:+ "` whose type is not a function type");
  '(xτs,τ) ← to_fun_type (to_type to_Ptr []) cτs cτ;
  Γ ← gets to_env;
  guard (Forall (type_complete Γ) (xτs.*2)) with
    ("function `" +:+ f +:+ "` with incomplete argument type");
  guard (type_complete Γ τ) with
    ("function `" +:+ f +:+ "` with incomplete return type");
  Δg ← gets to_globals;
  match Δg !! f with
  | Some (Fun sto' τs' τ' ms) =>
     guard (τs' = xτs.*2) with
       ("argument types of function `" +:+ f
         +:+ "` do not match previously declared prototype");
     guard (τ' = τ) with
       ("return type of function `" +:+ f
         +:+ "` does not match previously declared prototype");
     guard (sto = ExternStorage ∨ sto = sto'
         ∨ sto = AutoStorage ∧ sto' = ExternStorage) with
       ("function `" +:+ f +:+ "` previously declared with different linkage");
     guard (ms = None) with ("function `" +:+ f +:+ "` previously completed");
     s ← to_fun_stmt f (xτs.*1) (xτs.*2) τ cs;
     let sto := if decide (sto = ExternStorage) then sto' else sto in
     insert_fun f sto τs' τ' (Some s)
  | Some (Global _ _ _ _) =>
     fail ("function `" +:+ f +:+ "` previously declared as global")
  | Some (GlobalTypeDef _) =>
     fail ("function `" +:+ f +:+ "` previously declared as typedef")
  | Some (EnumVal _ _) =>
     fail ("function `" +:+ f +:+ "` previously declared as enum tag")
  | None =>
     _ ← insert_fun f sto (xτs.*2) τ None;
     s ← to_fun_stmt f (xτs.*1) (xτs.*2) τ cs;
     insert_fun f sto (xτs.*2) τ (Some s)
  end.
Fixpoint alloc_enum (xces : list (string * option cexpr))
    (τi : int_type K) (z : Z) : M () :=
  match xces return M () with
  | [] => mret ()
  | (x,None) :: xces =>
     Δg ← gets to_globals;
     guard (Δg !! x = None) with
       ("enum field `" +:+ x +:+ "` previously declared");
     guard (int_typed z τi) with
       ("enum field `" +:+ x +:+ "` has value out of range");
     _ ← insert_global_decl x (EnumVal τi z);
     alloc_enum xces τi (z + 1)%Z
  | (x,Some ce) :: xces =>
     '(e,_) ← to_expr [] ce;
     Δg ← gets to_globals;
     guard (Δg !! x = None) with
       ("enum field `" +:+ x +:+ "` previously declared");
     guard (is_pure e) with
       ("enum field `" +:+ x +:+ "` has non-constant value");
     Γ ← gets to_env; m ← gets to_mem;
     v ← error_of_option (⟦ e ⟧ Γ [] m ≫= maybe inr)
       ("enum field `" +:+ x +:+ "` has undefined value");
     '(_,z') ← error_of_option (maybe VBase v ≫= maybe2 VInt)
       ("enum field `" +:+ x +:+ "` has non-integer value");
     guard (int_typed z' τi) with "enum field with value out of range";
     _ ← insert_global_decl x (EnumVal τi z');
     alloc_enum xces τi (z' + 1)%Z
  end.
Definition to_compound_fields (t : tag) :
    list (string * ctype) → M (list (string * type K)) :=
  fix go cτs :=
  match cτs with
  | [] => mret []
  | (x,cτ) :: cτs =>
     τ ← to_type to_Type [] cτ;
     guard (τ ≠ voidT) with
      ("compound type `" +:+ t +:+ "` with field `" +:+ x +:+ "` of void type");
     ((x,τ) ::.) <$> go cτs
  end.
Fixpoint alloc_decls (Θ : list (string * decl)) : M () :=
  match Θ with
  | [] => mret ()
  | (x,CompoundDecl c cτs) :: Θ =>
     let t : tag := x in
     xτs ← to_compound_fields t cτs;
     Γ ← gets to_env;
     guard (Γ !! t = None) with
       ("compound type `" +:+ x +:+ "` previously declared");
     guard (NoDup (xτs.*1)) with
       ("compound type `" +:+ x +:+ "` has field names that are not unique");
     guard (xτs ≠ []) with
       ("compound type `" +:+ x +:+ "` declared without any fields");
     _ ← insert_compound c t xτs;
     alloc_decls Θ
  | (x,EnumDecl cτi yces) :: Θ =>
     let t : tag := x in
     let τi := to_inttype cτi in
     Γn ← gets to_compounds;
     guard (Γn !! t = None) with
       ("enum type `" +:+ x +:+ "` previously declared");
     _ ← insert_enum t τi;
     _ ← alloc_enum yces τi 0;
     alloc_decls Θ
  | (x,TypeDefDecl cτ) :: Θ =>
     τp ← to_type to_Ptr [] cτ;
     Δg ← gets to_globals;
     guard (Δg !! x = None) with
       ("typedef `" +:+ x +:+ "` previously declared");
     _ ← insert_global_decl x (GlobalTypeDef τp);
     alloc_decls Θ
  | (x,GlobDecl stos cτ me) :: Θ =>
     guard (stos ≠ [AutoStorage]) with
       ("global `" +:+ x +:+ "` has `auto` storage");
     sto ← error_of_option (to_storage stos)
       ("global `" +:+ x +:+ "` has multiple storage specifiers");
     _ ← alloc_global [] x sto cτ me;
     alloc_decls Θ
  | (f,FunDecl stos cσ cs) :: Θ =>
     guard (stos ≠ [AutoStorage]) with
       ("function `" +:+ f +:+ "` has `auto` storage");
     sto ← error_of_option (to_storage stos)
       ("function `" +:+ f +:+ "` has multiple storage specifiers");
     _ ← alloc_fun f sto cσ cs;
     alloc_decls Θ
  end.
Definition alloc_program (Θ : list (string * decl)) : M () :=
  _ ← alloc_decls Θ;
  S ← gets id;
  let incomp_fs : stringset := incomplete_fun_decls S in
  guard (incomp_fs = ∅) with "function `" +:+
    default "" (head (elements incomp_fs)) +:+ "` not completed";
  let incomp_xs : stringset := extern_global_decls S in
  guard (incomp_xs = ∅) with "global `" +:+
    default "" (head (elements incomp_xs)) +:+ "` with `extern` not linked";
  mret ().
End frontend_more.
