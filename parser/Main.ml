(* Copyright (c) 2012-2014, Freek Wiedijk. *)
(* This file is distributed under the terms of the BSD license. *)
#load "nums.cma";;
#load "Cerrors.cmo";;
#load "Cabs.cmo";;
#load "Cabshelper.cmo";;
#load "Parse_aux.cmo";;
#load "Parser.cmo";;
#load "Lexer.cmo";;
#load "Extracted.cmo";;
open Num
open Format
open Extracted

let col = ref 0
let trace_width = ref 72
let trace_printfs = ref true
let choose_randomly = ref true
let break_on_undef = ref false
let printf_returns_int = ref true

let cabs_of_file name =
  Cerrors.reset();
  let ic = open_in name in
  let lb = Lexer.init name ic in
  let p = Parser.file Lexer.initial lb in
  Lexer.finish();
  close_in ic;
  if Cerrors.check_errors() then failwith "Parser";
  p

let rec nat_of_int n =
  if n = 0 then O else S (nat_of_int (n - 1))

let rec positive_of_int n =
  if n = 1 then XH else
  let n' = positive_of_int (n/2) in
  if n mod 2 = 1 then XI n' else XO n'

let n_of_int n =
  if n = 0 then N0 else Npos (positive_of_int n)

let z_of_int i =
  if i = 0 then Z0 else if i > 0 then Zpos (positive_of_int i) else
  Zneg (positive_of_int (-i))

let rec int_of_nat n =
  match n with O -> 0 | S n' -> int_of_nat n' + 1

let rec int_of_positive n =
  match n with XI n' -> 2*(int_of_positive n') + 1 |
    XO n' -> 2*(int_of_positive n') | XH -> 1

let int_of_n n =
  match n with N0 -> 0 | Npos n' -> int_of_positive n'

let int_of_z i =
  match i with Z0 -> 0 | Zpos n' -> int_of_positive n'
    | Zneg n' -> -(int_of_positive n')

let rec nat_of_num n =
  if n = Int 0 then O else S (nat_of_num (n -/ Int 1))

let rec positive_of_num n =
  if n = Int 1 then XH else
  let n' = positive_of_num (quo_num n (Int 2)) in
  if mod_num n (Int 2) = Int 1 then XI n' else XO n'

let n_of_num n =
  if n = Int 0 then N0 else Npos (positive_of_num n)

let z_of_num i =
  if i = Int 0 then Z0 else if i >/ Int 0 then Zpos (positive_of_num i) else
  Zneg (positive_of_num (minus_num i))

let rec num_of_nat n =
  match n with O -> Int 0 | S n' -> num_of_nat n' +/ Int 1

let rec num_of_positive n =
  match n with XI n' -> Int 2*/(num_of_positive n') +/ Int 1 |
    XO n' -> Int 2*/(num_of_positive n') | XH -> Int 1

let num_of_n n =
  match n with N0 -> Int 0 | Npos n' -> num_of_positive n'

let num_of_z i =
  match i with Z0 -> Int 0 | Zpos n' -> num_of_positive n'
    | Zneg n' -> minus_num (num_of_positive n')

let pp_print_nat fmt x =
  pp_open_box fmt 2;
 (match num_of_nat x with
  | Int y ->
     (pp_print_string fmt "(nat_of_int";
      pp_print_space fmt ();
      pp_print_int fmt y;
      pp_print_string fmt ")")
  | y ->
     (pp_print_string fmt "(nat_of_num";
      pp_print_space fmt ();
      pp_print_string fmt "(num_of_string";
      pp_print_space fmt ();
      pp_print_string fmt "\"";
      pp_print_string fmt (string_of_num y);
      pp_print_string fmt "\"))"));
  pp_close_box fmt ()

let pp_print_n fmt x =
  pp_open_box fmt 2;
 (match num_of_n x with
  | Int y ->
     (pp_print_string fmt "(n_of_int";
      pp_print_space fmt ();
      pp_print_int fmt y;
      pp_print_string fmt ")")
  | y ->
     (pp_print_string fmt "(n_of_num";
      pp_print_space fmt ();
      pp_print_string fmt "(num_of_string";
      pp_print_space fmt ();
      pp_print_string fmt "\"";
      pp_print_string fmt (string_of_num y);
      pp_print_string fmt "\"))"));
  pp_close_box fmt ()

let pp_print_z fmt x =
  pp_open_box fmt 2;
 (match num_of_z x with
  | Int y ->
     (pp_print_string fmt "(z_of_int";
      pp_print_space fmt ();
      pp_print_int fmt y;
      pp_print_string fmt ")")
  | y ->
     (pp_print_string fmt "(z_of_num";
      pp_print_space fmt ();
      pp_print_string fmt "(num_of_string";
      pp_print_space fmt ();
      pp_print_string fmt "\"";
      pp_print_string fmt (string_of_num y);
      pp_print_string fmt "\"))"));
  pp_close_box fmt ()

let print_nat = pp_print_nat std_formatter;;
#install_printer print_nat;;
let print_n = pp_print_n std_formatter;;
#install_printer print_n;;
let print_z = pp_print_z std_formatter;;
#install_printer print_z;;

let time f x =
  let start_time = Sys.time() in
  try let result = f x in
      let finish_time = Sys.time() in
      print_string ("CPU time (user): "^
        (string_of_float(finish_time -. start_time))^"\n");
      result
  with e ->
      let finish_time = Sys.time() in
      print_string("Failed after (user) CPU time of "^
        (string_of_float(finish_time -. start_time))^": \n");
      raise e

let index x l =
  let rec index' n l =
    if l = [] then raise Not_found else
    if x = List.hd l then n else index' (n + 1) (List.tl l) in
  index' 0 l

let uniq l =
  let rec uniq' l k =
    match l with
    | [] -> k
    | x::l' -> uniq' l' (if List.mem x k then k else x::k) in
  List.rev (uniq' l [])

let string_of_chars l =
  let s = String.make (List.length l) ' ' in
  let rec init n l =
    match l with
    | [] -> ()
    | x::l' -> String.set s n x; init (n + 1) l' in
  init 0 l; s

let chars_of_string s =
  let l = String.length s in
  let rec chars n =
    if n < l then String.get s n::chars (n + 1) else [] in
  chars 0

exception Unknown_expression of Cabs.expression
exception Unknown_statement of Cabs.statement
exception Unknown_spec_elem of Cabs.spec_elem
exception Unknown_definition of Cabs.definition
exception Incompatible_compound of n * decl * decl

let the_ids = ref ([]:string list)
let the_compound_decls = ref ([]:(n * decl) list)
let the_printfs = ref ([]:(n * decl) list)
let the_formats = ref ([]:(n * string) list)

let nindex s =
  n_of_int (try index s !the_ids with
  Not_found ->
    let ids = !the_ids in
    the_ids := ids@[s];
    List.length ids)

let int_signed = {csign = Signed; crank = CIntRank }
let uchar = {csign = Unsigned; crank = CCharRank }

let econst n = CEConst (int_signed,z_of_num n)
let econst0 = econst (Int 0)
let econst1 = econst (Int 1)

let unop_of_unary_operator x =
  match x with
  | Cabs.MINUS -> NegOp
  | Cabs.BNOT -> ComplOp
  | Cabs.NOT -> NotOp
  | _ -> failwith "unop_of_unary_operator"

let binop_of_binary_operator x =
  match x with
  | Cabs.ADD -> ArithOp PlusOp
  | Cabs.SUB -> ArithOp MinusOp
  | Cabs.MUL -> ArithOp MultOp
  | Cabs.DIV -> ArithOp DivOp
  | Cabs.MOD -> ArithOp ModOp
  | Cabs.BAND -> BitOp AndOp
  | Cabs.BOR -> BitOp OrOp
  | Cabs.XOR -> BitOp XorOp
  | Cabs.SHL -> ShiftOp ShiftLOp
  | Cabs.SHR -> ShiftOp ShiftROp
  | Cabs.EQ -> CompOp EqOp
  | Cabs.LT -> CompOp LtOp
  | Cabs.LE -> CompOp LeOp
  | _ -> failwith "binop_of_binary_operator"

let rec mult_list l =
  match l with
  | [] -> econst1
  | [x] -> x
  | x::l' -> CEBinOp (ArithOp MultOp,mult_list l',x)

let rec split_sizeof' x =
  match x with
  | CESizeOf (t) -> (Some t,[])
  | CEBinOp (ArithOp MultOp,x1,x2) ->
      let (t,l2) = split_sizeof' x2 in
     (match t with
      | None ->
          let (t',l1) = split_sizeof' x1 in
          (t',l1@l2)
      | _ -> (t,x1::l2))
  | _ -> (None,[x])

let split_sizeof x =
  let (t,l) = split_sizeof' x in
  let y = mult_list (List.rev l) in
  match t with
  | None -> (CTInt uchar,y)
  | Some t' -> (t',y)

let length_of_format s =
  let n = String.length s in
  let rec length m =
    if m >= n then 0 else
    let c = String.get s m in if c <> '%' then 1 + length (m + 1) else
    if m + 1 < n && String.get s (m + 1) = 'd' then length (m + 2) else
    failwith "length_of_format" in 
  length 0

let printf_body i =
  let len = nindex "len-%d" in
  let rec body n a =
    match a with
    | [] -> CSReturn (Some (CEVar i))
    | x::a' -> CSComp (CSDo (CEAssign (PreOp (ArithOp PlusOp), CEVar i,
        CECall (len,[CEVar (n_of_int n)]))),body (n + 1) a') in
  body 1

let args_of_format s =
  let rec args_of_format' n m =
    try if String.get s n = '%' && String.get s (n + 1) = 'd' then
        (n_of_int m,CTInt int_signed)::args_of_format' (n + 2) (m + 1)
      else args_of_format' (n + 1) m
    with Invalid_argument _ -> [] in
  args_of_format' 0 1

let rec add_compound k0 n l =
   let k = CompoundDecl (k0,
     List.flatten (List.map (fun (t,l') -> List.map (fun f ->
       match f with
       | ((s',t',[],_),None) -> (nindex s',ctype_of_specifier_decl_type t t')
       | _ -> failwith "add_compound") l') l)) in
   try let k' = List.assoc n !the_compound_decls in
     if k' <> k then raise (Incompatible_compound (n,k',k))
   with Not_found -> the_compound_decls := !the_compound_decls@[(n,k)]

and ctype_of_spec_elem x ty =
  let int_type_of ty =
    match ty with
    | CTInt ty' -> ty'
    | _ -> failwith "ctype_of_spec_elem 1" in
  match x with
  | Cabs.SpecType Cabs.Tvoid -> CTVoid
  | Cabs.SpecType Cabs.Tsigned ->
      CTInt {csign = Signed; crank = (int_type_of ty).crank}
  | Cabs.SpecType Cabs.Tunsigned ->
      CTInt {csign = Unsigned; crank = (int_type_of ty).crank}
  | Cabs.SpecType Cabs.Tchar ->
      CTInt {csign = (int_type_of ty).csign; crank = CCharRank }
  | Cabs.SpecType Cabs.Tshort ->
      CTInt {csign = (int_type_of ty).csign; crank = CShortRank}
  | Cabs.SpecType Cabs.Tint -> ty
  | Cabs.SpecType Cabs.Tlong ->
      CTInt {csign = (int_type_of ty).csign; crank = CLongRank (nat_of_int 0)}
  | Cabs.SpecType (Cabs.Tstruct (s,None,[])) ->
      CTCompound (Struct_kind,nindex s)
  | Cabs.SpecType (Cabs.Tunion (s,None,[])) ->
      CTCompound (Union_kind,nindex s)
  | Cabs.SpecType (Cabs.Tenum (s,None,[])) ->
      CTEnum (nindex s)
  | Cabs.SpecType (Cabs.Tstruct (s,Some l,[])) ->
      let n = nindex s in
      add_compound Struct_kind n l;
      CTCompound (Struct_kind,n)
  | Cabs.SpecType (Cabs.Tunion (s,Some l,[])) ->
      let n = nindex s in
      add_compound Union_kind n l;
      CTCompound (Union_kind,n)
  | Cabs.SpecType (Cabs.Tenum (s,Some l,[])) ->
      let n = nindex s in
      let k = EnumDecl (int_signed,List.map (fun (s,x,_) ->
         (nindex s,
          match x with
          | Cabs.NOTHING -> None
          | _ -> Some (cexpr_of_expression x))) l) in
     (try let k' = List.assoc n !the_compound_decls in
        if k' <> k then raise (Incompatible_compound (n,k',k))
      with Not_found -> the_compound_decls := !the_compound_decls@[(n,k)]);
      CTEnum n
  | Cabs.SpecType (Cabs.Tnamed s) -> CTDef (nindex s)
  | _ -> raise (Unknown_spec_elem x)

and ctype_of_specifier x =
  List.fold_right ctype_of_spec_elem x (CTInt int_signed)

and ctype_of_decl_type t x =
  match x with
  | Cabs.JUSTBASE -> t
  | Cabs.PROTO (y,_,false) -> ctype_of_decl_type t y
  | Cabs.ARRAY (y,[],n) ->
      ctype_of_decl_type (CTArray (t,cexpr_of_expression n)) y
  | Cabs.PTR ([],y) ->
      ctype_of_decl_type (CTPtr t) y
  | Cabs.PARENTYPE ([],y,[]) -> ctype_of_decl_type t y
  | _ -> failwith "ctype_of_decl_type"

and ctype_of_specifier_decl_type x y =
  ctype_of_decl_type (ctype_of_specifier x) y

and cexpr_of_expression x =
  match x with
  | Cabs.CONSTANT (Cabs.CONST_INT s) -> econst (num_of_string s)
  | Cabs.VARIABLE "NULL" -> CECast (CTPtr CTVoid,econst0)
  | Cabs.VARIABLE "CHAR_BITS" -> CEBits uchar
  | Cabs.VARIABLE "SCHAR_MIN" -> CEMin { csign = Signed; crank = CCharRank }
  | Cabs.VARIABLE "SCHAR_MAX" -> CEMax { csign = Signed; crank = CCharRank }
  | Cabs.VARIABLE "UCHAR_MAX" -> CEMax { csign = Unsigned; crank = CCharRank }
  | Cabs.VARIABLE "SHRT_MIN" -> CEMin { csign = Signed; crank = CShortRank }
  | Cabs.VARIABLE "SHRT_MAX" -> CEMax { csign = Signed; crank = CShortRank }
  | Cabs.VARIABLE "USHRT_MAX" -> CEMax { csign = Unsigned; crank = CShortRank }
  | Cabs.VARIABLE "INT_MIN" -> CEMin { csign = Signed; crank = CIntRank }
  | Cabs.VARIABLE "INT_MAX" -> CEMax { csign = Signed; crank = CIntRank }
  | Cabs.VARIABLE "UINT_MAX" -> CEMax { csign = Unsigned; crank = CIntRank }
  | Cabs.VARIABLE "LONG_MIN" ->
     CEMin { csign = Signed; crank = CLongRank (nat_of_int 0) }
  | Cabs.VARIABLE "LONG_MAX" ->
     CEMax { csign = Signed; crank = CLongRank (nat_of_int 0) }
  | Cabs.VARIABLE "ULONG_MAX" ->
     CEMax { csign = Unsigned; crank = CLongRank (nat_of_int 0) }
  | Cabs.VARIABLE s -> CEVar (nindex s)
  | Cabs.UNARY (Cabs.MEMOF,y) ->
      CEDeref (cexpr_of_expression y)
  | Cabs.UNARY (Cabs.ADDROF,y) ->
      CEAddrOf (cexpr_of_expression y)
  | Cabs.UNARY (Cabs.PLUS,y) ->
      CEBinOp (ArithOp PlusOp,econst0,cexpr_of_expression y)
  | Cabs.UNARY (Cabs.PREINCR,y) ->
      CEAssign (PreOp (ArithOp PlusOp),cexpr_of_expression y,econst1)
  | Cabs.UNARY (Cabs.PREDECR,y) ->
      CEAssign (PreOp (ArithOp MinusOp),cexpr_of_expression y,econst1)
  | Cabs.UNARY (Cabs.POSINCR,y) ->
      CEAssign (PostOp (ArithOp PlusOp),cexpr_of_expression y,econst1)
  | Cabs.UNARY (Cabs.POSDECR,y) ->
      CEAssign (PostOp (ArithOp MinusOp),cexpr_of_expression y,econst1)
  | Cabs.UNARY (op,y) ->
      CEUnOp (unop_of_unary_operator op,cexpr_of_expression y)
  | Cabs.BINARY (Cabs.AND,y1,y2) ->
      CEAnd (cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.OR,y1,y2) ->
      CEOr (cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.ASSIGN,y1,y2) ->
      CEAssign (Assign,
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.ADD_ASSIGN,y1,y2) ->
      CEAssign (PreOp (ArithOp PlusOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.SUB_ASSIGN,y1,y2) ->
      CEAssign (PreOp (ArithOp MinusOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.MUL_ASSIGN,y1,y2) ->
      CEAssign (PreOp (ArithOp MultOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.DIV_ASSIGN,y1,y2) ->
      CEAssign (PreOp (ArithOp DivOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.MOD_ASSIGN,y1,y2) ->
      CEAssign (PreOp (ArithOp ModOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.BAND_ASSIGN,y1,y2) ->
      CEAssign (PreOp (BitOp AndOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.BOR_ASSIGN,y1,y2) ->
      CEAssign (PreOp (BitOp OrOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.XOR_ASSIGN,y1,y2) ->
      CEAssign (PreOp (BitOp XorOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.SHL_ASSIGN,y1,y2) ->
      CEAssign (PreOp (ShiftOp ShiftLOp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.SHR_ASSIGN,y1,y2) ->
      CEAssign (PreOp (ShiftOp ShiftROp),
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.BINARY (Cabs.NE,y1,y2) ->
      CEUnOp (NotOp,CEBinOp (CompOp EqOp,
        cexpr_of_expression y1,cexpr_of_expression y2))
  | Cabs.BINARY (Cabs.GT,y1,y2) ->
      CEBinOp (CompOp LtOp,
        cexpr_of_expression y2,cexpr_of_expression y1)
  | Cabs.BINARY (Cabs.GE,y1,y2) ->
      CEBinOp (CompOp LeOp,
        cexpr_of_expression y2,cexpr_of_expression y1)
  | Cabs.BINARY (op,y1,y2) ->
      CEBinOp (binop_of_binary_operator op,
        cexpr_of_expression y1,cexpr_of_expression y2)
  | Cabs.PAREN y -> cexpr_of_expression y
  | Cabs.QUESTION (y1,y2,y3) ->
      CEIf (cexpr_of_expression y1,
        cexpr_of_expression y2,cexpr_of_expression y3)
  | Cabs.CAST ((t1,t2),Cabs.SINGLE_INIT y) ->
      CECast(ctype_of_specifier_decl_type t1 t2,
        cexpr_of_expression y)
  | Cabs.CALL (Cabs.VARIABLE "malloc",[y]) ->
      let (t,y') = split_sizeof (cexpr_of_expression y) in
      CEAlloc (t,y')
  | Cabs.CALL (Cabs.VARIABLE "free",[y]) ->
      CEFree (cexpr_of_expression y)
  | Cabs.CALL (Cabs.VARIABLE "printf",
        Cabs.CONSTANT (Cabs.CONST_STRING s)::l) ->
      let f = nindex ("printf-"^s) in
      let a = args_of_format s in
      the_printfs := !the_printfs@
        [(f,if !printf_returns_int then
          let i = n_of_int 0 in
          FunDecl (a,CTInt int_signed,
            Some (CSBlock (false,i,CTInt int_signed,
              Some (CEConst (int_signed,z_of_int (length_of_format s))),
            printf_body i a))) else
          FunDecl (a,CTVoid,Some (CSSkip)))];
      the_formats := !the_formats@[(f,s)];
      CECall (f,List.map cexpr_of_expression l)
  | Cabs.CALL (Cabs.VARIABLE s,l) ->
      CECall (nindex s,List.map cexpr_of_expression l)
  | Cabs.COMMA (h::t) ->
      List.fold_left (fun y1 y2 -> CEComma (y1,cexpr_of_expression y2))
        (cexpr_of_expression h) t
  | Cabs.EXPR_SIZEOF y ->
      CESizeOf (CTTypeOf (cexpr_of_expression y))
  | Cabs.TYPE_SIZEOF (y1,y2) ->
      CESizeOf (ctype_of_specifier_decl_type y1 y2)
  | Cabs.INDEX (y1,y2) ->
      CEDeref (CEBinOp (ArithOp PlusOp,
        cexpr_of_expression y1,cexpr_of_expression y2))
  | Cabs.MEMBEROF (y,f) -> CEField (cexpr_of_expression y,nindex f)
  | Cabs.MEMBEROFPTR (y,f) ->
      CEDeref (CEField (cexpr_of_expression y,nindex f))
  | Cabs.NOTHING -> econst1
  | _ -> raise (Unknown_expression x)

let decl_of_init_expression x =
  match x with
  | Cabs.NO_INIT -> None
  | Cabs.SINGLE_INIT y -> Some (cexpr_of_expression y)
  | _ -> failwith "expr_of_init_expression"

let cscomp x y =
  if y = CSSkip then x else CSComp (x,y)

let rec cstmt_of_statements l =
  let rec fold_defs h t l b =
    match l with
    | [] -> cstmt_of_statements b
    | ((s,t',[],_),z)::l' ->
        CSBlock (h,nindex s,
          ctype_of_specifier_decl_type t t',
          decl_of_init_expression z,
          fold_defs h t l' b)
    | _ -> failwith "cstmt_of_statements 1" in
  match l with
  | [] -> CSSkip
  | Cabs.LABEL (s,y,_)::l' ->
      cscomp (CSLabel (nindex s,cstmt_of_statements [y]))
        (cstmt_of_statements l')
  | Cabs.BLOCK ({Cabs.bstmts = y},_)::l' ->
      cscomp (cstmt_of_statements y) (cstmt_of_statements l')
  | Cabs.DEFINITION (Cabs.DECDEF ((t,l),_))::l' ->
      let h,t = match t with
        | Cabs.SpecStorage Cabs.STATIC::t -> true,t
        | _ -> false,t in
      fold_defs h t l l'
  | Cabs.COMPUTATION (y,_)::l' ->
      cscomp (CSDo (cexpr_of_expression y))
        (cstmt_of_statements l')
  | Cabs.IF (e,y1,y2,_)::l' ->
      cscomp (CSIf (cexpr_of_expression e,
          cstmt_of_statements [y1],cstmt_of_statements [y2]))
        (cstmt_of_statements l')
  | Cabs.WHILE (e,y,_)::l' ->
      cscomp (CSWhile (cexpr_of_expression e,cstmt_of_statements [y]))
        (cstmt_of_statements l')
  | Cabs.FOR (Cabs.FC_EXP e1,e2,e3,y,_)::l' ->
      cscomp (CSFor (cexpr_of_expression e1,
          cexpr_of_expression e2,cexpr_of_expression e3,
          cstmt_of_statements [y]))
        (cstmt_of_statements l')
  | Cabs.FOR (Cabs.FC_DECL (Cabs.DECDEF ((t,l),_)),e2,e3,y,z)::l' ->
      fold_defs false t l (Cabs.FOR (Cabs.FC_EXP Cabs.NOTHING,e2,e3,y,z)::l')
  | Cabs.DOWHILE (e,y,_)::l' ->
      cscomp (CSDoWhile (cstmt_of_statements [y],
          cexpr_of_expression e))
        (cstmt_of_statements l')
  | Cabs.GOTO (s,_)::l' ->
      cscomp (CSGoto (nindex s))
        (cstmt_of_statements l')
  | Cabs.RETURN (Cabs.NOTHING,_)::l' ->
      cscomp (CSReturn None)
        (cstmt_of_statements l')
  | Cabs.RETURN (y,_)::l' ->
      cscomp (CSReturn (Some (cexpr_of_expression y)))
        (cstmt_of_statements l')
  | Cabs.NOP _::l' -> cstmt_of_statements l'
  | _ -> raise (Unknown_statement (List.hd l))

let rec args_of_decl_type x =
  match x with
  | Cabs.PROTO (Cabs.JUSTBASE,a,false) -> a
  | Cabs.ARRAY (y,[],_) -> args_of_decl_type y
  | Cabs.PTR ([],y) -> args_of_decl_type y
  | Cabs.PARENTYPE ([],y,[]) -> args_of_decl_type y
  | _ -> failwith "args_of_decl_type"

let args_of a =
  match a with
  | [([Cabs.SpecType Cabs.Tvoid],("",Cabs.JUSTBASE,[],_))] -> []
  | _ ->
      List.map (fun y ->
        match y with
        | (t,(s,t',[],_)) ->
            (nindex s,ctype_of_specifier_decl_type t t')
        | _ -> failwith "args_of") a

let decls_of_definition x =
  match x with
  | Cabs.DECDEF ((t,l),_) ->
      List.map (fun z ->
        match z with
        | ((s,t',[],_),z) ->
             (nindex s,
               GlobDecl (ctype_of_specifier_decl_type t t',
                 decl_of_init_expression z))
        | _ -> failwith "decls_of_definition 1") l
  | Cabs.FUNDEF ((t,(s,t',[],_)),
        {Cabs.bstmts = l},_,_) ->
      [(nindex s,
        FunDecl (args_of (args_of_decl_type t'),
          ctype_of_specifier_decl_type t t',
          Some (cstmt_of_statements l)))]
  | Cabs.ONLYTYPEDEF (t,_) ->
      let _ = ctype_of_specifier t in []
  | Cabs.TYPEDEF ((Cabs.SpecTypedef::t,l),_) ->
      List.map (fun z ->
        match z with
        | (s,t',[],_) ->
             (nindex s,
               TypeDefDecl (ctype_of_specifier_decl_type t t'))
        | _ -> failwith "decls_of_definition 1") l
  | _ -> raise (Unknown_definition x)

let printf_prelude () =
  try let len = nindex "len-%d" in
    let i = n_of_int 0 and n = n_of_int 1 in [(len,
    FunDecl ([(i, CTInt int_signed)],CTInt int_signed,Some
     (CSBlock (false,n,CTInt int_signed,Some econst0,
      CSComp (CSIf (CEBinOp (CompOp EqOp,CEVar i,econst0),
        CSReturn (Some econst1),CSSkip),
      CSComp (CSIf (CEBinOp (CompOp LtOp,CEVar i,econst0),
        CSComp (CSDo (CEAssign (PostOp (ArithOp PlusOp),CEVar n,econst1)),
        CSDo (CEAssign (PreOp (ArithOp MultOp),CEVar i,econst (Int (-1))))),
        CSSkip),
      CSComp (CSWhile (CEBinOp (CompOp LtOp,econst0,CEVar i),
        CSComp (CSDo (CEAssign (PostOp (ArithOp PlusOp),CEVar n,econst1)),
        CSDo (CEAssign (PreOp (ArithOp DivOp),CEVar i,econst (Int 10))))),
      CSReturn (Some (CEVar n)))))))))]
  with Not_found -> []

let decls_of_cabs x =
  the_ids := [];
  the_formats := [];
  the_compound_decls := [];
  the_printfs := [];
  let decls = List.flatten (List.map decls_of_definition x) in
  (the_printfs := printf_prelude ()@ !the_printfs);
  (!the_ids,(nindex "main",!the_compound_decls@ !the_printfs@decls))

let decls_of_file x =
  decls_of_cabs (cabs_of_file x)

exception CH2O_error of string
exception CH2O_undef of irank undef_state
exception CH2O_exited of num

let chars_of_format s l =
  let rec chars_of_format' n l =
    try let c = String.get s n in
      if c = '%' && String.get s (n + 1) = 'd' then
        chars_of_string (string_of_num (List.hd l))@
        chars_of_format' (n + 2) (List.tl l)
      else c::chars_of_format' (n + 1) l
    with Invalid_argument _ -> [] in
  chars_of_format' 0 l

let event_of_state x =
  match x.sFoc with
  | Call (f,l) ->
     (try let fmt = List.assoc f !the_formats in
        chars_of_format fmt
          (List.map (fun y ->
             match y with
             | VBase (VInt (_,n)) -> num_of_z n
             | _ -> failwith "event_of_state") l)
      with Not_found -> [])
  | _ -> []

let graph_of_decls (ids,(m,x)) =
  match interpreter_all true (nat_of_int 8)
    (=) event_of_state (fun x -> z_of_int (Hashtbl.hash x)) x m [] with
  | Inl y -> raise (CH2O_error (string_of_chars y))
  | Inr y -> (ids,y)

let graph_of_cabs x =
  graph_of_decls (decls_of_cabs x)

let graph_of_file x =
  graph_of_decls (decls_of_file x)

let choose =
  ref (fun x -> if !choose_randomly
    then nat_of_int (Random.int (int_of_nat x))
    else nat_of_int 0)

let stream_of_decls (ids,(m,x)) =
  match interpreter_rand true (nat_of_int 8) event_of_state !choose x m [] with
  | Inl y -> raise (CH2O_error (string_of_chars y))
  | Inr y -> (ids,y)

let stream_of_cabs x =
  stream_of_decls (decls_of_cabs x)

let stream_of_file x =
  stream_of_decls (decls_of_file x)

let rec print_states ids l =
  match l with
  | [] -> print_string "\n"; col := 0
  | {events_all = e; sem_state = s}::l' ->
      (match s.sFoc with
       | Return (f,VBase (VInt (_,y))) ->
           let e' = String.escaped (string_of_chars e) in
           print_string "\"";
           print_string e';
           print_string "\" ";
           print_string (string_of_num (num_of_z y))
       | Undef y ->
           if !break_on_undef then raise (CH2O_undef y) else
           print_string "undef"
       | _ -> failwith "print_states");
      (if l' <> [] then print_string "\n"); print_states ids l'

let rec string_of_events l =
  match l with
  | [] -> ""
  | s::l' -> "\""^s^"\""^(if l' <> [] then " "^string_of_events l' else "")

let symbols = [
       0,"";
       1,".";
       2,",";
       4,"-";
       8,"+";
      16,":";
      32,";";
      64,"!";
     128,"|";
     256,"?";
     512,"*";
    1024,"%";
    4096,"$";
   16384,"@";
   99999,"#";
  ]

let rec find_symbol n l =
  match l with
  | [] -> failwith "find_symbol"
  | [(_,c)] -> c
  | (m,c)::l' -> if n <= m then c else find_symbol n l'

let trace_graph (ids,x) =
  let h = ref x in
  try
    while true do
      let Scons ((s1,s2),x') = Lazy.force !h in
      (if s1 = [] && s2 = [] then raise Not_found);
      (if s2 <> [] then
        (if !col > 0 then print_string "\n"; print_states ids s2; col := 0));
      (if s1 <> [] then
        let c = find_symbol (List.length s1) symbols in
        (if !col >= !trace_width then (print_string "\n"; col := 0));
        print_string c; col := !col + 1;
        let e = uniq (List.filter ((<>) "") (List.map (fun x ->
          String.escaped (string_of_chars x.events_new)) s1)) in
        if !trace_printfs && e <> [] then
          (let s = "<"^string_of_events e^">" in
           let n = String.length s in
           (if !col + n > !trace_width then (print_string "\n"; col := 0));
           print_string s; col := !col + n));
      print_flush ();
      flush stdout;
      h := x'
    done
  with Not_found -> ()

let trace_cabs x =
  trace_graph (graph_of_cabs x)

let trace_file x =
  trace_graph (graph_of_file x)

let run_stream (ids,x) =
  Random.self_init ();
  let h = ref x in
  try
    while true do
      let Scons (s,x') = Lazy.force !h in
     (match s with
      | Inl {events_new = e} -> print_string (string_of_chars e)
      | Inr {sem_state = s} ->
         (match s.sFoc with
          | Return (f,VBase (VInt (_,y))) -> raise (CH2O_exited (num_of_z y))
          | Undef y -> raise (CH2O_undef y)
          | _ -> failwith "run_stream"));
      print_flush ();
      flush stdout;
      h := x'
    done; 0
  with CH2O_exited y -> int_of_num y

let run_cabs x =
  run_stream (stream_of_cabs x)

let run_file x =
  run_stream (stream_of_file x)

let main () =
  try if Array.length Sys.argv < 2 then raise Not_found else
    if Sys.argv.(1) = "-t" then
      if Array.length Sys.argv <> 3 then raise Not_found else
      (trace_printfs := false; trace_file Sys.argv.(2); 0)
    else if Sys.argv.(1) = "-T" then
      if Array.length Sys.argv <> 3 then raise Not_found else
      (trace_printfs := true; trace_file Sys.argv.(2); 0)
    else if Sys.argv.(1) = "-r" then
      if Array.length Sys.argv <> 3 then raise Not_found else
      (choose_randomly := true; run_file Sys.argv.(2))
    else
      if Array.length Sys.argv <> 2 then raise Not_found else
      (choose_randomly := false; run_file Sys.argv.(1))
  with Not_found -> output_string stderr
    ("Usage: "^Filename.basename(Sys.argv.(0))^" [-r | -t | -T] filename\n");
    64

let interactive () =
  try
    let s = Sys.argv.(0) in
    let n = String.length s in
    n >= 5 && String.sub s (n - 5) 5 = "ocaml"
  with _ -> true;;

if not (interactive ()) then exit (main())

