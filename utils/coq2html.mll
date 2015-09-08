(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          with modifications by Robbert Krebbers                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

{
open Printf

module StringSet = Set.Make(String)

let mkset l = List.fold_right StringSet.add l StringSet.empty

(** Cross-referencing *)

let current_module = ref ""

type xref =
  | Def of string * string    (* path, type *)
  | Ref of string * string * string (* unit, path, type *)

let xref_table : (int, xref) Hashtbl.t = Hashtbl.create 273

let extern_refs : (string * string) list ref =
  ref ["Coq", "http://coq.inria.fr/library"]

let path sp id =
  match sp, id with
  | "<>", "<>" -> ""
  | "<>", _    -> id
  | _   , "<>" -> sp
  | _   , _    -> sp ^ "." ^ id

let add_reference pos dp sp id ty =
  if not (Hashtbl.mem xref_table pos)
  then Hashtbl.add xref_table pos (Ref(dp, path sp id, ty))

let add_definition pos sp id ty =
  if not (Hashtbl.mem xref_table pos)
  then Hashtbl.add xref_table pos (Def(path sp id, ty))

type link = Link of string | Anchor of string | Nolink

let re_sane_path = Str.regexp "[A-Za-z0-9_.]+$"
let sane_tys = mkset [
  "def"; "ind"; "class"; "lib"; "proj"; "rec"; "constr"; "prf"; "inst"; "thm";
  "sec"; "syndef"; "coe"; "meth" ]

let make_url m =
  let rec go es =
    match es with
    | [] -> m ^ ".html"
    | (m',url) :: es when String.length m' < String.length m
       && String.sub m 0 (String.length m') = m' -> sprintf "%s/%s.html" url m
    | _ :: es -> go es
  in go !extern_refs
  
let crossref pos =
  try match Hashtbl.find xref_table pos with
  | Def(p, ty) ->
      if not (StringSet.mem ty sane_tys) then Nolink else
      Anchor p
  | Ref(m', p, ty) ->
      if not (StringSet.mem ty sane_tys) then Nolink else
      let url = make_url m' in
      if p = "" then
        Link url
      else if Str.string_match re_sane_path p 0 then
        Link(url ^ "#" ^ p)
      else
        Nolink
  with Not_found ->
    Nolink

(** Keywords, etc *)

let coq_keywords = mkset [
  "forall"; "match"; "as"; "in"; "return"; "with"; "end"; "let";
  "dest"; "fun"; "if"; "then"; "else"; "Prop"; "Set"; "Type"; ":=";
  "where"; "struct"; "wf"; "measure";
  "AddPath"; "Axiom"; "Abort"; "Boxed"; "Chapter"; "Check";
  "Coercion"; "CoFixpoint"; "CoInductive"; "Corollary"; "Defined";
  "Definition"; "End"; "Eval"; "Example"; "Export"; "Fact"; "Fix";
  "Fixpoint"; "Global"; "Grammar"; "Goal"; "Hint"; "Hypothesis";
  "Hypotheses"; "Resolve"; "Unfold"; "Immediate"; "Extern";
  "Implicit"; "Import"; "Inductive"; "Infix"; "Lemma"; "Let"; "Load";
  "Local"; "Ltac"; "Module"; "Module Type"; "Declare Module";
  "Include"; "Mutual"; "Parameter"; "Parameters"; "Print"; "Proof";
  "Qed"; "Record"; "Recursive"; "Remark"; "Require";
  "Save"; "Scheme"; "Induction"; "for"; "Sort"; "Section"; "Show";
  "Structure"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; "Set";
  "Types"; "Undo"; "Unset"; "Variable"; "Variables"; "Context";
  "Notation"; "Reserved"; "Tactic"; "Delimit"; "Bind"; "Open";
  "Scope"; "Boxed"; "Unboxed"; "Inline"; "Implicit Arguments"; "Add";
  "Strict"; "Typeclasses"; "Instance"; "Global Instance"; "Class";
  "Instantiation"; "subgoal"; "Program"; "Example"; "Obligation";
  "Obligations"; "Solve"; "using"; "Next"; "Instance"; "Equations";
  "Equations_nocomp"; "Arguments"; "Existing"; "Printing"; "Constructor"
]

let coq_tactics = mkset [
  "intro"; "intros"; "apply"; "rewrite"; "refine"; "case"; "clear";
  "injection"; "elimtype"; "progress"; "setoid_rewrite"; "destruct";
  "destruction"; "destruct_call"; "dependent"; "elim";
  "extensionality"; "f_equal"; "generalize"; "generalize_eqs";
  "generalize_eqs_vars"; "induction"; "rename"; "move"; "omega";
  "set"; "assert"; "do"; "repeat"; "cut"; "assumption"; "exact";
  "split"; "subst"; "try"; "discriminate"; "simpl"; "unfold"; "red";
  "compute"; "at"; "in"; "by"; "reflexivity"; "symmetry";
  "transitivity"; "replace"; "setoid_replace"; "inversion";
  "inversion_clear"; "pattern"; "intuition"; "congruence"; "fail";
  "fresh"; "trivial"; "exact"; "tauto"; "firstorder"; "ring";
  "clapply"; "program_simpl"; "program_simplify"; "eapply"; "auto";
  "eauto"; "easy"; "now"; "exists"; "eexists"; "specialize"
]

(** HTML generation *)

let oc = ref stdout

let character = function
  | '<' -> output_string !oc "&lt;"
  | '>' -> output_string !oc "&gt;"
  | '&' -> output_string !oc "&amp;"
  |  c  -> output_char !oc c

let section_level = function
  | "*" -> 2
  | "**" -> 3
  | _ -> 4

let start_section sect =
  fprintf !oc "<h%d>" (section_level sect)
let end_section sect =
  fprintf !oc "</h%d>\n" (section_level sect)

let start_doc_right () =
  fprintf !oc "<span class=\"docright\">(* "
let end_doc_right () =
  fprintf !oc " *)</span>"

let start_doc_inline () =
  fprintf !oc "<span class=\"docinline\">(* "
let end_doc_inline () =
  fprintf !oc " *)</span>"

let enum_depth = ref 0

let rec set_enum_depth d =
  if !enum_depth < d then begin
    fprintf !oc "<ul>\n";
    fprintf !oc "<li>\n";
    incr enum_depth;
  end
  else if !enum_depth > d then begin
    fprintf !oc "</li>\n";
    fprintf !oc "</ul>\n";
    decr enum_depth;
  end
  else if !enum_depth > 0 then begin
    fprintf !oc "</li>\n";
    fprintf !oc "<li>\n"
  end

let start_doc () =
  fprintf !oc "<div class=\"doc\">"
let end_doc () =
  set_enum_depth 0;
  fprintf !oc "</div>\n"

let ident pos id =
  match crossref pos with
  | Nolink ->
      if StringSet.mem id coq_keywords then
        fprintf !oc "<span class=\"kwd\">%s</span>" id
      else if StringSet.mem id coq_tactics then
        fprintf !oc "<span class=\"tactic\">%s</span>" id
      else
        fprintf !oc "<span class=\"id\">%s</span>" id
  | Link p ->
      fprintf !oc "<span class=\"id\"><a href=\"%s\">%s</a></span>" p id
  | Anchor p ->
      fprintf !oc "<span class=\"id\"><a name=\"%s\">%s</a></span>" p id

let space s =
  for i = 1 to String.length s do fprintf !oc "&nbsp;" done

let newline () =
  fprintf !oc "<br/>\n"

let dashes = function
  | "-" -> set_enum_depth 1
  | "--" -> set_enum_depth 2
  | "---" -> set_enum_depth 3
  | "----" -> set_enum_depth 4
  | _ -> fprintf !oc "<hr/>\n"

let start_verbatim () =
  fprintf !oc "<pre>\n"

let end_verbatim () =
  fprintf !oc "</pre>\n"

let start_bracket () =
  fprintf !oc "<span class=\"bracket\">"

let end_bracket () =
  fprintf !oc "</span>"

let proof_counter = ref 0

let start_proof s kwd =
  incr proof_counter;
  fprintf !oc "<span class=\"proof\">";
  space s;
  fprintf !oc "<span class=\"toggleproof\">%s</span>\n" kwd;
  fprintf !oc "<span class=\"proofscript\" id=\"proof%d\">\n" !proof_counter

let end_proof kwd =
  fprintf !oc "%s</span></span>\n" kwd

let start_html_page () =
  fprintf !oc "\
<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\">

<head>
<meta http-equiv=\"Content-Type\" content=\"text/html; charset=utf-8\" />
<title>Module %s</title>
<meta name=\"description\" content=\"Documentation of Coq module %s\" />
<link href=\"style.css\" rel=\"stylesheet\" type=\"text/css\" />
<script type=\"text/javascript\" src=\"scripts.js\"> </script>
</head>

<body>
<h1>Module %s</h1>
<div class=\"coq\">
" !current_module !current_module !current_module

let end_html_page () =
  fprintf !oc "\
</div>
<div class=\"footer\">Generated by coq2html</div>
</body>
</html>
"

}

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let path = ident ("." ident)*
let start_proof = "Proof." | ("Proof" space+ "with") | ("Next" space+ "Obligation.")
let end_proof = "Qed." | "Defined." | "Save." | "Admitted." | "Abort."

let xref = path | "<>"
let integer = ['0'-'9']+

rule coq_bol = parse
  | space* as s (start_proof as sp)
      { start_proof s sp;
        coq lexbuf }
  | space* "(** " ("*"+ as sect)
      { start_section sect;
        doc lexbuf;
        end_section sect;
        coq_bol_skip_newline lexbuf }
  | space* "(** "
      { start_doc();
        doc lexbuf;
        end_doc();
        coq_bol_skip_newline lexbuf }
  | space* "(* "
      { comment lexbuf;
        coq_bol_skip_newline lexbuf }
  | eof
      { () }
  | space* as s
      { space s;
        coq lexbuf }

and coq_bol_skip_newline = parse
  | space* "\n"*
      { coq_bol lexbuf }
  | ""
      { coq lexbuf }

and coq = parse
  | end_proof as ep
      { end_proof ep;
        coq_skip_newline lexbuf }
  | "(**r "
      { start_doc_right();
        doc lexbuf;
        end_doc_right();
        coq lexbuf }
  | "(**i "
      { start_doc_inline();
        doc_inline lexbuf;
        end_doc_inline();
        coq lexbuf }
  | "(*"
      { comment lexbuf;
        coq lexbuf }
  | path as id
      { ident (Lexing.lexeme_start lexbuf) id; coq lexbuf }
  | "\n"
      { newline(); coq_bol lexbuf }
  | eof
      { () }
  | _ as c
      { character c; coq lexbuf }

and coq_skip_newline = parse
  | space*
      { coq_bol lexbuf }
  | ""
      { coq lexbuf }

and bracket = parse
  | ']'
      { () }
  | '['
      { character '['; bracket lexbuf; character ']'; bracket lexbuf }
  | path as id
      { ident (Lexing.lexeme_start lexbuf) id; bracket lexbuf }
  | eof
      { () }
  | _ as c
      { character c; bracket lexbuf }

and comment = parse
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | eof
      { () }
  | _
      { comment lexbuf }

and doc_bol = parse
  | "<<" space* "\n"
      { start_verbatim();
        verbatim lexbuf;
        end_verbatim();
        doc_bol lexbuf }
  | "-"+ as d
      { dashes d; doc lexbuf }
  | "\n"
      { set_enum_depth 0; doc_bol lexbuf }
  | ""
      { doc lexbuf }

and doc = parse
  | "*)"
      { () }
  | "\n"
      { character '\n'; doc_bol lexbuf }
  | "["
      { start_bracket(); bracket lexbuf; end_bracket(); doc lexbuf }
  | "$" [^ '\n' '$']* "$"
      { doc lexbuf }
  | "#" ([^ '\n' '#']* as html) "#"
      { output_string !oc html; doc lexbuf }
  | eof
      { () }
  | _ as c
      { character c; doc lexbuf }

and doc_inline = parse
  | "*)"
      { () }
  | "\n" (space* as s)
      { newline(); space s; doc_inline lexbuf }
  | "["
      { start_bracket(); bracket lexbuf; end_bracket(); doc_inline lexbuf }
  | eof
      { () }
  | _ as c
      { character c; doc_inline lexbuf }

and verbatim = parse
  | "\n>>" space* "\n"
      { () }
  | eof
      { () }
  | _ as c
      { character c; verbatim lexbuf }

and globfile = parse
  | eof
      { () }
  | "F" (path as m) space* "\n"
      { current_module := m; globfile lexbuf }
  | "R" (integer as pos) ":" integer
    space+ (xref as dp)
    space+ (xref as sp)
    space+ (xref as id)
    space+ (ident as ty)
    space* "\n"
      { add_reference (int_of_string pos) dp sp id ty;
        globfile lexbuf }
  | (ident as ty)
    space+ (integer as pos) ":" integer
    space+ (xref as sp)
    space+ (xref as id)
    space* "\n"
      { add_definition (int_of_string pos) sp id ty;
        globfile lexbuf }
  | [^ '\n']* "\n"
      { globfile lexbuf }

{

let output_name = ref "-"

let process_glob f =
  let glob = Filename.chop_suffix f ".v" ^ ".glob" in
  let ic = open_in glob in
  globfile (Lexing.from_channel ic);
  close_in ic
  
let process_file f =
  if not (Filename.check_suffix f ".v") then begin
    eprintf "Don't know what to do with file %s\n" f;
    exit 2
  end;
  process_glob f;
  let ic = open_in f in
  oc := if !output_name = "-" then stdout else open_out !output_name;
  start_html_page ();
  coq_bol (Lexing.from_channel ic);
  end_html_page();
  if !output_name <> "-" then (close_out !oc; oc := stdout);
  close_in ic

let _ =
  let temp_coqdir = ref "" in
  Arg.parse [
    "-R", Arg.Tuple
      [Arg.String (fun s -> temp_coqdir := s);
       Arg.String (fun s -> extern_refs := (!temp_coqdir, s) :: !extern_refs)],
      " <coqdir> <url> Set base url for coqdir";
    "-o", Arg.String (fun s -> output_name := s),
      " <output> Set output file (default stdout)"
  ] process_file
  "Usage: coq2html [options] file.v\nOptions are:"
}
