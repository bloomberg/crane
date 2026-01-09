(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Production of C++ syntax. *)

open Pp
open CErrors
open Util
open Names
open ModPath
open Table
open Miniml
open Mlutil
open Modutil
open Common
open Minicpp
open Translation


(*s Some utility functions. *)

let pp_tvar id = str (Id.to_string id)

let pp_parameters l =
  (pp_boxed_tuple pp_tvar l ++ space_if (not (List.is_empty l)))

let pp_string_parameters l =
  (pp_boxed_tuple str l ++ space_if (not (List.is_empty l)))

(*s C++ renaming issues. *)

let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
  [ "and"; "as"; "assert"; "begin"; "bool"; "class"; "constraint"; "do";
    "done"; "downto"; "else"; "end"; "exception"; "external"; "false";
    "for"; "fun"; "function"; "functor"; "if"; "in"; "include";
    "inherit"; "initializer"; "lazy"; "let"; "match"; "method";
    "module"; "mutable"; "new"; "nonrec"; "object"; "of"; "open"; "or";
    "parser"; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true";
    "try"; "type"; "val"; "virtual"; "when"; "while"; "with"; "mod";
    "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr" ; "_" ; "__" ]
  Id.Set.empty

(* Note: do not shorten [str "foo" ++ fnl ()] into [str "foo\n"],
   the '\n' character interacts badly with the Format boxing mechanism *)

let pp_open mp = str ("open "^ string_of_modfile mp) ++ fnl ()

let pp_comment s = str "(* " ++ hov 0 s ++ str " *)"

let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl2 ()

let then_nl pp = if Pp.ismt pp then mt () else pp ++ fnl ()

let preamble _ comment used_modules usf =
  pp_header_comment comment ++
  then_nl (prlist pp_open used_modules) (* ++
  then_nl (pp_tdummy usf ++ pp_mldummy usf) *)

let sig_preamble _ comment used_modules usf =
  pp_header_comment comment (* ++
  then_nl (pp_tdummy usf) *)

(*s The pretty-printer for C++ syntax*)

(* Context tracking for code generation *)
let in_struct_context = ref false

(* Beware of the side-effects of [pp_global] and [pp_modname].
   They are used to update table of content for modules. Many [let]
   below should not be altered since they force evaluation order.
*)

let str_global_with_key k key r =
  if is_inline_custom r then find_custom r else Common.pp_global_with_key k key r

let str_global k r = str_global_with_key k (repr_of_r r) r

let pp_global_with_key k key r = str (str_global_with_key k key r)

let pp_global k r = str (str_global k r)
(*
let pp_lowercase r = str (String.uncapitalize_ascii (str_global Type r))

let pp_uppercase r = str (String.capitalize_ascii (str_global Type r))
*)
let pp_global_name k r = str (Common.pp_global k r)

let pp_modname mp = str (Common.pp_module mp)

(* grammar from OCaml 4.06 manual, "Prefix and infix symbols" *)

let infix_symbols =
  ['=' ; '<' ; '>' ; '@' ; '^' ; ';' ; '&' ; '+' ; '-' ; '*' ; '/' ; '$' ; '%' ]
let operator_chars =
  [ '!' ; '$' ; '%' ; '&' ; '*' ; '+' ; '-' ; '.' ; '/' ; ':' ; '<' ; '=' ; '>' ; '?' ; '@' ; '^' ; '|' ; '~' ]

(* infix ops in OCaml, but disallowed by preceding grammar *)

let builtin_infixes =
  [ "::" ; "," ]

let substring_all_opchars s start stop =
  let rec check_char i =
    if i >= stop then true
    else
      List.mem s.[i] operator_chars && check_char (i+1)
  in
  check_char start

let is_infix r =
  is_inline_custom r &&
  (let s = find_custom r in
   let len = String.length s in
   len >= 3 &&
   (* parenthesized *)
   (s.[0] == '(' && s.[len-1] == ')' &&
      let inparens = String.trim (String.sub s 1 (len - 2)) in
      let inparens_len = String.length inparens in
      (* either, begins with infix symbol, any remainder is all operator chars *)
      (List.mem inparens.[0] infix_symbols && substring_all_opchars inparens 1 inparens_len) ||
      (* or, starts with #, at least one more char, all are operator chars *)
      (inparens.[0] == '#' && inparens_len >= 2 && substring_all_opchars inparens 1 inparens_len) ||
      (* or, is an OCaml built-in infix *)
      (List.mem inparens builtin_infixes)))

let get_infix r =
  let s = find_custom r in
  String.sub s 1 (String.length s - 2)

let get_ind = let open GlobRef in function
  | IndRef _ as r -> r
  | ConstructRef (ind,_) -> IndRef ind
  | _ -> assert false

let kn_of_ind = let open GlobRef in function
  | IndRef (kn,_) -> MutInd.user kn
  | _ -> assert false

let pp_one_field r i = function
  | Some r' -> pp_global_with_key Term (kn_of_ind (get_ind r)) r'
  | None -> pp_global Type (get_ind r) ++ str "__" ++ int i

let pp_field r fields i = pp_one_field r i (List.nth fields i)

let pp_fields r fields = List.map_i (pp_one_field r) 0 fields


(* pretty printing c++ syntax *)
let try_cpp c o =
  try c
  with TODO -> o

let pp_tymod = function
  | TMconst -> str "const "
  | TMstatic -> str "static "
  | TMextern -> str "extern "

let std_angle label s =
  if Table.std_lib () = "BDE"
    then str "bsl::" ++ str label ++ str "<" ++ s ++ str ">"
    else str "std::" ++ str label ++ str "<" ++ s ++ str ">"

let cpp_angle label s = str label ++ str "<" ++ s ++ str ">"


type custom_case =
| CCscrut
| CCty
| CCbody of int
| CCty_arg of int
| CCbr_var of int * int
| CCbr_var_ty of int * int
(* | CCbr_rty of int *)
| CCstring of string
| CCarg of int

let is_digit c = c >= '0' && c <= '9'

(* Parses an integer starting at [i], returns (value, next_index) *)
let parse_number s i n =
  let rec aux j =
    if j < n && is_digit s.[j] then aux (j + 1) else j
  in
  let j = aux i in
  if j = i then None
  else
    let num_str = String.sub s i (j - i) in
    Some (int_of_string num_str, j)

(*
  The following functions parse custom placeholders in extraction syntax strings:
  - parse_custom_fixed: parses fixed placeholders like %scrut or %ty
  - parse_custom_single_arg: parses placeholders like %a0, %t12 (single argument)
  - parse_custom_double_arg: parses placeholders like %b0a1, %b10a20 (two arguments)
*)

(* Parses fixed custom placeholders like %scrut or %ty *)
let parse_custom_fixed esc cc s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start chunks_rev =
    if i >= n then
      let last_chunk = String.sub s start (n - start) in
      List.rev (CCstring last_chunk :: chunks_rev)
    else
      match s.[i], i + esc_len + 1 < n with
      | '%', true ->
        if esc = String.sub s (i+1) esc_len then
          let chunk = String.sub s start (i - start) in
          aux (i + esc_len + 1) (i + esc_len + 1) (cc :: CCstring chunk :: chunks_rev)
        else
          aux (i + 1) start chunks_rev
      | _ ->
        aux (i + 1) start chunks_rev
  in
  aux 0 0 []

(* Parses single-argument custom placeholders like %a0, %t12 *)
let parse_numbered_args esc f s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start acc =
    if i >= n then
      List.rev (if start < n then CCstring (String.sub s start (n - start)) :: acc else acc)
    else if s.[i] = '%' && i + esc_len < n &&
            String.sub s (i + 1) esc_len = esc then
      match parse_number s (i + 1 + esc_len) n with
      | Some (idx, j) ->
        let chunk = String.sub s start (i - start) in
        aux j j (f idx :: CCstring chunk :: acc)
      | None ->
        aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

(* Parses double-argument custom placeholders like %b0a1, %b10a20 *)
let parse_custom_numbered_binders esc1 esc2 f s =
  let n = String.length s in
  let len1 = String.length esc1 in
  let len2 = String.length esc2 in
  let rec aux i start acc =
    if i >= n then
      List.rev (if start < n then CCstring (String.sub s start (n - start)) :: acc else acc)
    else if s.[i] = '%' &&
            i + len1 < n &&
            String.sub s (i + 1) len1 = esc1 then
      match parse_number s (i + 1 + len1) n with
      | Some (idx1, j) when j + len2 <= n && String.sub s j len2 = esc2 ->
        begin
          match parse_number s (j + len2) n with
          | Some (idx2, k) ->
            let chunk = String.sub s start (i - start) in
            aux k k (f idx1 idx2 :: CCstring chunk :: acc)
          | None ->
            aux (i + 1) start acc
        end
      | _ ->
        aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

let print_cpp_type_var vl i = (try pp_tvar (List.nth vl (pred i))
                              with Failure _ -> (str "T" ++ int i)) (* TODO: CHANGE *)

(* cleanup without parens bool *)
let rec pp_cpp_type par vl t =
  let rec pp_rec par = function
    | Tvar (i, None) -> print_cpp_type_var vl i
    | Tvar (_, Some id) -> Id.print id
    | Tglob (r,tys, args) when is_inline_custom r ->
    let s = find_custom r in
    let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
    let cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_numbered_args "t" (fun i -> CCty_arg i) s)
                      | _ -> prev @ [curr]) [] cmds in
    pp_custom (Pp.string_of_ppcmds (GlobRef.print r) ^ " := " ^ s) (empty_env ()) None None tys [] args vl cmds
    | Tglob (r,[],_) -> pp_global Type r
    | Tglob (r,l,_) ->
          pp_global Type r ++ str "<" ++ pp_list (pp_rec false) l ++ str ">"
    | Tfun (d,c) -> std_angle "function" (pp_rec false c ++ pp_par true (pp_list (pp_rec false) d))
    | Tstruct (id, args) ->
      let templates =
        (match args with
        | [] -> mt ()
        | args -> str "<" ++ pp_list (pp_rec false) args ++ str ">") in
      pp_global Type id ++ templates
    | Tref t -> pp_rec false t ++ str "&"
    | Tmod (m, t) -> pp_tymod m ++ pp_rec false t
    | Tnamespace (r,t) ->
        (* Capitalize inductive references *)
        let name = match r with
          | GlobRef.IndRef _ -> str (String.capitalize_ascii (str_global Type r))
          | _ -> pp_global Type r
        in
        str "typename " ++ name ++ str "::" ++ pp_rec false t
    | Tvariant tys -> std_angle "variant" (pp_list (pp_rec false) tys)
    | Tshared_ptr t ->
        if Table.std_lib () = "BDE"
          then cpp_angle "bsl::shared_ptr" (pp_rec false t)
          else cpp_angle "std::shared_ptr" (pp_rec false t)
    | Tstring ->
        if Table.std_lib () = "BDE"
          then str "bsl::string"
          else str "std::string"
    | Tvoid -> str "void"
    | Ttodo -> str "auto"
    | Tunknown -> str "UNKNOWN" (* TODO: BAD *)
  in
  h (pp_rec par t)

and pp_cpp_expr env args t =
  let apply st = pp_apply_cpp st args in
  match t with
  | CPPvar' id -> (try apply (Id.print (get_db_name id env)) (* very confused by evar now *)
               with Failure _ -> str "BadCPPVar")
  | CPPvar id -> Id.print id
  | CPPglob (x, tys) when is_inline_custom x ->
    let custom = find_custom x in
    let cmds = parse_numbered_args "t" (fun i -> CCty_arg i) custom in
    pp_custom (Pp.string_of_ppcmds (GlobRef.print x) ^ " := " ^ custom) env None None tys [] [] [] cmds
  | CPPglob (x, tys) ->
    (match tys with
    | [] -> apply (pp_global Term x)
    | _ ->
      let ty_args = pp_list (pp_cpp_type false []) tys in
      apply (pp_global Term x) ++ str "<" ++ ty_args ++ str ">")
  | CPPnamespace (r, t) ->
      (* Capitalize inductive references *)
      let name = match r with
        | GlobRef.IndRef _ -> str (String.capitalize_ascii (str_global Type r))
        | _ -> pp_global Type r
      in
      h (name ++ str "::" ++ pp_cpp_expr env args t)
  | CPPfun_call (CPPglob (n,tys), ts) when is_inline_custom n ->
    let s = find_custom n in
    let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
    let cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_numbered_args "t" (fun i -> CCty_arg i) s)
                      | _ -> prev @ [curr]) [] cmds in
    pp_custom (Pp.string_of_ppcmds (GlobRef.print n) ^ " := " ^ s) env None None tys [] (List.rev ts) [] cmds
  | CPPfun_call (f, ts) ->
    let args_s = pp_list (pp_cpp_expr env args) (List.rev ts) in
    pp_cpp_expr env args f ++ str "(" ++ args_s ++ str ")"
  | CPPderef e ->
      str "*" ++ (pp_cpp_expr env args e)
  | CPPmove e ->
      if Table.std_lib () = "BDE"
        then str "bsl::move(" ++ (pp_cpp_expr env args e) ++ str ")"
        else str "std::move(" ++ (pp_cpp_expr env args e) ++ str ")"
  | CPPforward (ty, e) ->
      if Table.std_lib () = "BDE"
        then str "bsl::forward<" ++ pp_cpp_type false [] ty ++ str ">(" ++ (pp_cpp_expr env args e) ++ str ")"
        else str "std::forward<" ++ pp_cpp_type false [] ty ++ str ">(" ++ (pp_cpp_expr env args e) ++ str ")"
  | CPPlambda (params, ret_ty, body) ->
      let (params_s, capture) =
        (match params with
        | [] -> str "void", str "[&]("
        | _ -> pp_list (fun (ty, id_opt) ->
            let id_s = match id_opt with None -> str "" | Some id -> Id.print id in
            (pp_cpp_type false [] ty) ++ spc () ++ id_s) (List.rev params), str "[&](")
      in
      let body_s = pp_list_stmt (pp_cpp_stmt env args) body in
      (* h (capture ++ params_s ++ str ")") ++ str " {" ++ fnl () ++ body_s ++ fnl () ++ str "}" *)
      begin match ret_ty with
      | Some ty ->
        h  (capture ++ params_s ++ str ") -> " ++ (pp_cpp_type false [] ty)) ++ str " {" ++ fnl () ++ body_s ++ fnl () ++ str "}"
      | None ->
        h (capture ++ params_s ++ str ")") ++ str " {" ++ fnl () ++ body_s ++ fnl () ++ str "}"
      end
  | CPPvisit ->
      if Table.std_lib () = "BDE"
        then str "bsl::visit"
        else str "std::visit"
  | CPPmk_shared t ->
      if Table.std_lib () = "BDE"
        then cpp_angle "bsl::make_shared" (pp_cpp_type false [] t)
        else cpp_angle "std::make_shared" (pp_cpp_type false [] t)
  | CPPoverloaded ls ->
      let ls_s = pp_list_newline (pp_cpp_expr env args) ls in
      let o = if Table.std_lib () = "BDE" then str "bdlf::Overloaded" else str "Overloaded" in
      o ++ str " {" ++ fnl () ++ ls_s ++ fnl () ++ str "}"
  | CPPmatch (scrut, ls) -> mt () (*
      let scrut_s = pp_cpp_expr env args scrut in
      let ls_s = pp_list_newline (pp_cpp_expr env args) ls in
      let o = if Table.std_lib () = "BDE" then str "bsl::visit(bdlf::Overloaded" else str "std::visit(Overloaded" in
      o ++ str " {" ++ fnl () ++ ls_s ++ fnl () ++ str "}, " ++ scrut_s ++ str ")" *)
  | CPPstructmk (id, tys, es) ->
      let es_s = pp_list (pp_cpp_expr env args) es in
      let templates =
        (match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">") in
      pp_global Type id ++  templates ++ str "::make(" ++ es_s ++ str ")"
  | CPPstruct (id, tys, es) ->
      let es_s = pp_list (pp_cpp_expr env args) es in
      let templates =
        (match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">") in
      pp_global Type id ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPget (e, id) ->
      (pp_cpp_expr env args e) ++ str "." ++ (Id.print id)
  | CPPget' (e, id) ->
      (pp_cpp_expr env args e) ++ str "->" ++ pp_global Type id
  | CPPstring s -> str ("\"" ^  (Pstring.to_string s) ^ "\"")
  | CPPparray (elems, _) -> str "{" ++ pp_list (pp_cpp_expr env args) (Array.to_list elems) ++ str "}"
  | CPPuint x -> str (Uint63.to_string x)
  | CPPrequires (ty_vars, exprs) ->
      let ty_vars_s = match ty_vars with [] -> mt () | _ ->
        str "(" ++ pp_list (fun (ty, id) -> (pp_cpp_type false [] ty) ++ spc () ++ Id.print id) ty_vars ++ str ") " in
      let exprs_s = pp_list (fun (e1, e2) ->
        str "{" ++ pp_cpp_expr env args e1 ++ str "} -> " ++ pp_cpp_expr env args e2 ++ str ";") exprs in
      str "requires " ++ ty_vars_s ++ str "{ " ++ exprs_s ++ str " }"

and pp_cpp_stmt env args = function
| SreturnVoid -> str "return;"
| Sreturn e ->
    str "return " ++ pp_cpp_expr env args e ++ str ";"
| Sdecl (id, ty) -> (pp_cpp_type false [] ty) ++ str " " ++ Id.print id ++ str ";"
| Sasgn (id, Some ty, e) ->
    (pp_cpp_type false [] ty) ++ str " " ++ Id.print id ++ str " = " ++ (pp_cpp_expr env args e) ++ str ";"
| Sasgn (id, None, e) ->
    Id.print id ++ str " = " ++ (pp_cpp_expr env args e) ++ str ";"
| Sexpr e ->
    pp_cpp_expr env args e ++ str ";"
| Scustom_case (typ,t,tyargs,cases,cmatch) ->
  let cmds = parse_custom_fixed "scrut" CCscrut cmatch in
  let cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_custom_fixed "ty" CCty s)
                      | _ -> prev @ [curr]) [] cmds in
  let helper e f cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_numbered_args e f s)
                      | _ -> prev @ [curr]) [] cmds in
  let cmds = helper "t" (fun i -> CCty_arg i) cmds in
  let cmds = helper "br" (fun i -> CCbody i) cmds in
  let helper2 e1 e2 f cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_custom_numbered_binders e1 e2 f s)
                      | _ -> prev @ [curr]) [] cmds in
  let cmds = helper2 "b" "a" (fun i j -> CCbr_var (i, j)) cmds in
  let cmds = helper2 "b" "t" (fun i j -> CCbr_var_ty (i, j)) cmds in
  pp_custom ("custom match for " ^ (Pp.string_of_ppcmds (pp_cpp_type false [] typ)) ^ " := " ^ cmatch) env (Some typ) (Some t) tyargs cases [] [] cmds

and pp_custom custom env typ t tyargs cases args vl cmds =
  let pp cmd = match cmd with
    | CCstring s -> str s
    | CCscrut ->(match t with
        | Some t -> pp_cpp_expr env [] t
        | None -> assert false)
    | CCty ->(match typ with
        | Some typ -> pp_cpp_type false vl typ
        | None -> assert false)
    | CCbody i -> (try
      let (_,_,ss) = List.nth cases i in
       pp_list_stmt (pp_cpp_stmt env []) ss
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound case body in"; print_endline custom; assert false)
    | CCty_arg i ->(try pp_cpp_type false vl (List.nth tyargs i)
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound type argument in"; print_endline custom; assert false)
    | CCbr_var (i, j) -> (try
      let (ids,_,_) = List.nth cases i in
      let (id,_) = List.nth ids j in
      Id.print id
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound case branch variable in"; print_endline custom; assert false)
    | CCbr_var_ty (i, j) -> (try
      let (ids,_,_) = List.nth cases i in
      let (_,ty) = List.nth ids j in
      pp_cpp_type false vl ty
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound case branch type argument in"; print_endline custom; assert false)
    | CCarg i -> (try pp_cpp_expr env [] (List.nth args i)
      with Failure _ -> print_endline "Error: custom inlined syntax referencing an unbound term argument in"; print_endline custom; assert false) in
  List.fold_left (fun prev c -> prev ++ pp c) (mt ()) cmds

let pp_cpp_field env = function
| Fvar (id, ty) ->
    h ((pp_cpp_type false [] ty) ++ str " " ++ Id.print id ++ str ";")
| Fvar' (id, ty) ->
    h ((pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str ";")
| Ffundef (id, ret_ty, params, body) ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) params
    in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
      h ((pp_cpp_type false [] ret_ty) ++ str " " ++ Id.print id ++ pp_par true params_s ++ str "{") ++ fnl () ++ body_s ++ str "}"
| Ffundecl (id, ret_ty, params) ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) (List.rev params)
    in h ((pp_cpp_type false [] ret_ty) ++ str " " ++ Id.print id ++ pp_par true params_s) ++ str ";"

let pp_template_type = function
  | TTtypename -> str "typename"
  | TTfun (dom, cod) -> str "MapsTo<" ++ pp_cpp_type false [] cod  ++ str ", " ++ pp_list (pp_cpp_type false []) dom ++ str ">"
  | TTconcept (concept) -> pp_global Type concept

let rec  pp_cpp_decl env =
  let pp_cpp_fields_with_pub ls =
    pp_list_stmt (fun (fld, is_pub) -> pp_cpp_field env fld
    (*  TODO: Currently every field is public, so not needed
      let f_s = pp_cpp_field env fld in
      if is_pub then str "public:" ++ fnl () ++ f_s
      else           str "private:" ++ fnl () ++ f_s
    *)
    ) ls
  in
function
| Dtemplate (temps, cstr, decl) ->
    let args = pp_list (fun (tt, id) -> pp_template_type tt ++ spc () ++ Id.print id) temps in
    h (str "template <" ++ args ++ str ">")
    ++ (match cstr with
        | None -> fnl ()
        | Some c -> pp_cpp_expr env [] c ++ fnl ())
    ++ pp_cpp_decl env decl
| Dnspace (None, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl env) decls in
    h (str "namespace " ++ str "{") ++ fnl () ++ ds ++ fnl () ++ str "};"
| Dnspace (Some id, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl env) decls in
    (* Generate as struct to allow nesting inside other structs/modules *)
    (* Capitalize the struct name to avoid conflicts with inner type alias of same name *)
    let struct_name = match id with
      | GlobRef.IndRef (kn, i) ->
          let base = str_global Type id in
          str (String.capitalize_ascii base)
      | _ -> pp_global Type id
    in
    h (str "struct " ++ struct_name ++ str " {") ++ fnl () ++ ds ++ fnl () ++ str "};"
| Dfundef (ids, ret_ty, params, body) ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) (List.rev params)
    in
    let name = prlist_with_sep (fun () -> str "::") (fun (n, tys) ->
      (match tys with
      | [] -> pp_global Type n
      | _ -> pp_global Type n ++ str "<" ++ (pp_list (pp_cpp_type false []) tys) ++ str ">")) ids
      in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
    (* Add static for struct member functions (qualified names with >1 component or templates) *)
    let is_struct_member = List.length ids > 1 || (match ids with | [(_, tys)] when tys <> [] -> true | _ -> false) in
    let static_kw = if is_struct_member then str "static " else mt () in
      h (static_kw ++ (pp_cpp_type false [] ret_ty) ++ str " " ++ name ++ pp_par true params_s) ++ str "{" ++ body_s ++ str "}"
| Dfundecl (ids, ret_ty, params) ->
    let params_s =
      pp_list (fun (id, ty) ->
        match id with
        | Some id -> (pp_cpp_type false [] ty) ++ str " " ++ Id.print id
        | None -> pp_cpp_type false [] ty) (List.rev params) in
    let name = prlist_with_sep (fun () -> str "::") (fun (n, tys) ->
      (match tys with
      | [] -> pp_global Type n
      | _ -> pp_global Type n ++ str "<" ++ (pp_list (pp_cpp_type false []) tys) ++ str ">")) ids
      in
    (* Add static for struct member functions *)
    (* Check if qualified name (out-of-line definition) OR inside a struct context *)
    let is_qualified = List.length ids > 1 || (match ids with | [(_, tys)] when tys <> [] -> true | _ -> false) in
    let is_struct_member = is_qualified || !in_struct_context in
    let static_kw = if is_struct_member then str "static " else mt () in
    h (static_kw ++ (pp_cpp_type false [] ret_ty) ++ str " " ++ name ++ pp_par true params_s) ++ str ";"
| Dstruct (id, fields) ->
    let f_s = pp_cpp_fields_with_pub fields in
    str "struct " ++ pp_global Type id ++ str "{" ++ fnl () ++ f_s ++ str "};"
| Dstruct_decl id ->
    str "struct " ++ pp_global Type id ++ str ";"
| Dusing (id, ty) ->
    str "using " ++ pp_global Type id ++ str " = " ++ pp_cpp_type false [] ty ++ str ";"
| Dasgn (id, ty, e) ->
    (* Add static for struct members *)
    (* For static const members with initializers, add inline (C++17) *)
    let static_kw = if !in_struct_context then str "static inline " else mt () in
    h (static_kw ++ (pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str " = " ++ (pp_cpp_expr env [] e) ++ str ";")
| Ddecl (id, ty) ->
    h ((pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str ";")
| Dconcept (id, cstr) ->
    h (str "concept " ++ pp_global Type id ++ str " = " ++ pp_cpp_expr env [] cstr ++ str ";")
| Dstatic_assert (e, so) ->
    match so with
    | None -> h (str "static_assert(" ++ pp_cpp_expr env [] e ++ str ");")
    | Some s -> h (str "static_assert(" ++ pp_cpp_expr env [] e ++ str ", \"" ++ str s ++ str "\");")

(*s Pretty-printing of types. [par] is a boolean indicating whether parentheses
    are needed or not. *)

let pp_type par vl t =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) [] [] t in
  pp_cpp_type par vl cty

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

let cut2 () = brk (0,-100000) ++ brk (0,0)

let pp_cpp_ind kn ind =
  let names =
  Array.mapi (fun i p -> GlobRef.IndRef (kn,i))
    ind.ind_packets
  in
  let cnames =
    Array.mapi
      (fun i p ->
         Array.mapi (fun j _ -> GlobRef.ConstructRef ((kn,i),j+1))
           p.ip_types)
      ind.ind_packets in
  match ind.ind_kind with
  | Record fields -> mt ()
  | _ ->
  let rec pp i =
    if i >= Array.length ind.ind_packets then mt ()
    else
      let ip = (kn,i) in
      let p = ind.ind_packets.(i) in
      if is_custom (GlobRef.IndRef ip) then pp (i+1)
      else
        pp_cpp_decl (empty_env ()) (gen_ind_cpp p.ip_vars names.(i) cnames.(i) p.ip_types)
  in
  pp 0

let pp_tydef ids name def =
  let templates = match ids with
  | [] -> mt ()
  | _ -> str "template <" ++
          List.fold_left (fun s v -> s ++ v) (mt ())
            (List.mapi (fun i v -> if i = 0 then str "typename " ++ Id.print v else str ", typename " ++ Id.print v) ids)
          ++ str "> " in
  hov 2 (templates ++ str "using " ++ name ++ def ++ str ";")

let pp_decl = function
    | Dtype (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_any_inline_custom r -> mt ()
    | Dind (kn,i) -> mt ()  (* Inductives are fully defined in headers *)
    | Dtype (r, l, t) -> mt ()
    | Dterm (r, a, Tglob (ty, args,e)) when is_monad ty ->
          let defs = List.filter (fun (_,_,l) -> l == []) (gen_dfuns (Array.of_list [r], Array.of_list [a], Array.of_list [Miniml.Tglob (ty, args,e)])) in
          pp_list_stmt (fun(ds, env, _) -> pp_cpp_decl env ds) defs
    | Dterm (r, a, t) ->
        let (ds, env, tvars) = gen_decl_for_pp r a t in
        (*let _ = print_endline (Pp.string_of_ppcmds (pp_type false [] t)) in*)
        begin match ds, tvars with
        | Some ds , [] -> pp_cpp_decl env ds
        | _ , _ -> mt ()
        end
    | Dfix (rv,defs,typs) ->
          let filter = Array.to_list (Array.map (fun x -> not (is_inline_custom x)) rv) in
          let rv = Array.filter_with filter rv in
          let defs = Array.filter_with filter defs in
          let typs = Array.filter_with filter typs in
          let defs = List.filter (fun (_,_,l) -> l == []) (gen_dfuns (rv, defs, typs)) in
          pp_list_stmt (fun(ds, env, _) -> pp_cpp_decl env ds) defs

let pp_cpp_ind_header kn ind =
  let names =
  Array.mapi (fun i p -> GlobRef.IndRef (kn,i))
    ind.ind_packets
  in
  let cnames =
    Array.mapi
      (fun i p ->
         Array.mapi (fun j _ -> GlobRef.ConstructRef ((kn,i),j+1))
           p.ip_types)
      ind.ind_packets in
  match ind.ind_kind with
  | Record fields -> pp_cpp_decl (empty_env ()) (gen_record_cpp names.(0) fields ind.ind_packets.(0))
  | _ ->
    let rec pp i =
      if i >= Array.length ind.ind_packets then mt ()
      else
        let ip = (kn,i) in
        let p = ind.ind_packets.(i) in
        if is_custom (GlobRef.IndRef ip) then pp (i+1)
        else
          pp_cpp_decl (empty_env ()) (gen_ind_header p.ip_vars names.(i) cnames.(i) p.ip_types)
    in
    pp 0

let pp_hdecl = function
    | Dtype (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_any_inline_custom r -> mt ()
    | Dind (kn,i) -> pp_cpp_ind_header kn i
    | Dtype (r, l, t) -> (* TODO: Do for real sometime! *)
        let name = pp_global Type r in
        let l = rename_tvars keywords l in
        let ids, def =
          try
            let ids,s = find_type_custom r in
            pp_string_parameters ids, str " =" ++ spc () ++ str s
          with Not_found ->
            pp_parameters l,
            if t == Taxiom then str " (* AXIOM TO BE REALIZED *)"
            else str " =" ++ spc () ++ pp_type false l t
        in
        pp_tydef l name def
    | Dterm (r, a, Tglob (ty, args,e)) when is_monad ty ->
          let defs = (gen_dfuns_header (Array.of_list [r], Array.of_list [a], Array.of_list [Miniml.Tglob (ty, args,e)])) in
          pp_list_stmt (fun(ds, env) -> pp_cpp_decl env ds) defs
    | Dterm (r, a, t) -> (* ADD CUSTOM for non-inlined *)
      let (ds, env, tvars) = gen_decl_for_pp r a t in
            begin match ds, tvars with
            | Some ds , [] -> let (ds, env) = gen_spec r a t in
                              pp_cpp_decl env ds
            | Some ds , _::_ -> pp_cpp_decl env ds
            | None , _ -> let (ds, env) = gen_spec r a t in
                              pp_cpp_decl env ds
            end
    | Dfix (rv,defs,typs) ->
          let filter = Array.to_list (Array.map (fun x -> not (is_inline_custom x)) rv) in
          let rv = Array.filter_with filter rv in
          let defs = Array.filter_with filter defs in
          let typs = Array.filter_with filter typs in
          (* pp_list_stmt (fun(ds, env, _) ->  pp_cpp_decl env ds) (gen_dfuns (rv, defs, typs)) *)
          pp_list_stmt (fun(ds, env) ->  pp_cpp_decl env ds) (gen_dfuns_header (rv, defs, typs))


let pp_spec = function
  | Sval (r,_,_) when is_inline_custom r -> mt ()
  | Stype (r,_,_) when is_inline_custom r -> mt ()
  | Sind (kn,i) -> pp_cpp_ind_header kn i
  | Sval (r,b,t) ->
        let (ds, env) = gen_spec r b t in
        (*let _ = print_endline (Pp.string_of_ppcmds (pp_type false [] t)) in*)
        pp_cpp_decl env ds
  | Stype (r,vl,ot) -> (* TODO: maybe do for real? but is is necessary? *)
      let name = pp_global_name Type r in
      let l = rename_tvars keywords vl in
      let ids, def =
        try
          let ids, s = find_type_custom r in
          pp_string_parameters ids, str " =" ++ spc () ++ str s
        with Not_found ->
          let ids = pp_parameters l in
          match ot with
            | None -> ids, mt ()
            | Some Taxiom -> ids, str " (* AXIOM TO BE REALIZED *)"
            | Some t -> ids, str " =" ++ spc () ++ pp_type false l t
      in
        pp_tydef l name def


let rec pp_specif = function
  | (_,Spec (Sval _ as s)) -> pp_spec s
  | (l,Spec s) ->
     (match Common.get_duplicate (top_visible_mp ()) l with
      | None -> pp_spec s
      | Some ren -> pp_spec s (*
         hov 1 (str ("module "^ren^" : sig") ++ fnl () ++ pp_spec s) ++
         fnl () ++ str "end" ++ fnl () ++
         str ("include module type of struct include "^ren^" end") *))
  | (l,Smodule mt) ->
      let def = pp_module_type [] mt in
      def ++
      (match Common.get_duplicate (top_visible_mp ()) l with
       | None -> Pp.mt ()
       | Some ren ->
         fnl ())
  | (l,Smodtype mt) ->
      let def = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module type " ++ name ++ str " =" ++ fnl () ++ def) ++
      (match Common.get_duplicate (top_visible_mp ()) l with
       | None -> Pp.mt ()
       | Some ren -> fnl () ++ str ("module type "^ren^" = ") ++ name)

(* Helper to convert a spec to a concept requirement *)
and pp_spec_as_requirement = function
  | Sval (r,_,_) when is_inline_custom r -> mt ()
  | Stype (r,_,_) when is_inline_custom r -> mt ()
  | Sind (kn,i) -> mt () (* TODO: handle inductive requirements *)
  | Sval (r,b,t) ->
      (* Generate requires clause for a function/value *)
      let name = pp_global_name Term r in
      (* Check if it's a function by looking at the type *)
      let rec get_function_parts = function
        | Tarr (arg, rest) ->
            let (args, ret) = get_function_parts rest in
            (arg :: args, ret)
        | ret_ty -> ([], ret_ty)
      in
      let (args, ret_ty) = get_function_parts t in
      if args = [] then
        (* For non-function values, require typename *)
        str "typename M::" ++ name ++ str ";" ++ fnl ()
      else
        (* For functions, generate requires expression with parameters and return type *)
        let cpp_args = List.map (convert_ml_type_to_cpp_type (empty_env ()) [] []) args in
        let cpp_ret = convert_ml_type_to_cpp_type (empty_env ()) [] [] ret_ty in
        (* Helper to qualify type names with M:: *)
        (* Only qualify simple type references, not standard library types *)
        let rec qualify_type = function
          | Tglob (r, [], _) when not (is_custom r) ->
              (* Simple type reference - qualify with M:: *)
              str "typename M::" ++ pp_global Type r
          | Tglob (r, args, _) when not (is_custom r) ->
              (* Parametric type - don't qualify the constructor, but qualify type arguments *)
              pp_global Type r ++ str "<" ++ prlist_with_sep (fun () -> str ", ") qualify_type args ++ str ">"
          | Tglob (r, args, _) when is_custom r ->
              (* Custom type - for std types like option, manually construct with qualified args *)
              let custom_str = find_custom r in
              (* Check for common patterns *)
              if String.contains custom_str '%' then
                (* Has type parameters - substitute with qualified versions *)
                (* For now, handle std::optional specially *)
                (match args with
                | [arg] when custom_str = "std::optional<%t0>" ->
                    str "std::optional<" ++ qualify_type arg ++ str ">"
                | _ ->
                    (* Fallback - just use the regular printer *)
                    (* This won't qualify inner types, but it's better than nothing *)
                    pp_cpp_type false [] (Tglob (r, args, [])))
              else
                str custom_str
          | Tshared_ptr ty ->
              (* std::shared_ptr - don't qualify, but qualify inner type *)
              str "std::shared_ptr<" ++ qualify_type ty ++ str ">"
          | Tvariant tys ->
              (* std::variant - don't qualify, but qualify type arguments *)
              str "std::variant<" ++ prlist_with_sep (fun () -> str ", ") qualify_type tys ++ str ">"
          | Tnamespace (r, ty) ->
              (* Qualified type - already qualified, just print it *)
              pp_cpp_type false [] (Tnamespace (r, ty))
          | ty -> pp_cpp_type false [] ty
        in
        (* Generate: { M::name(std::declval<arg1>(), ...) } -> std::same_as<ret_ty>; *)
        let declvals = List.map (fun arg_ty ->
          str "std::declval<" ++ qualify_type arg_ty ++ str ">()"
        ) cpp_args in
        let call_expr = str "M::" ++ name ++ str "(" ++ prlist_with_sep (fun () -> str ", ") identity declvals ++ str ")" in
        str "{ " ++ call_expr ++ str " } -> std::same_as<" ++ qualify_type cpp_ret ++ str ">;" ++ fnl ()
  | Stype (r,vl,ot) ->
      (* Generate requires clause for a type *)
      let name = pp_global_name Type r in
      str "typename M::" ++ name ++ str ";" ++ fnl ()

and pp_module_type params = function
  | MTident kn ->
      (* Reference to a concept name *)
      pp_modname kn
  | MTfunsig (mbid, mt, mt') ->
      (* Functor type signature - for now, just return the body type *)
      (* This is used in the context of functor definitions *)
      pp_module_type (MPbound mbid :: params) mt'
  | MTsig (mp, sign) ->
      (* Generate concept body with requirements *)
      push_visible mp params;
      let pp_req (_label, specif) = match specif with
        | Spec s -> pp_spec_as_requirement s
        | Smodule _ -> mt () (* TODO: nested modules *)
        | Smodtype _ -> mt () (* TODO: nested module types *)
      in
      let reqs = List.map pp_req sign in
      let reqs = List.filter (fun p -> not (Pp.ismt p)) reqs in
      pop_visible ();
      if List.is_empty reqs then mt ()
      else prlist identity reqs
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      (* TODO: handle with type constraints properly *)
      pp_module_type [] mt
  | MTwith(mt,ML_With_module(idl,mp)) ->
      (* TODO: handle with module constraints properly *)
      pp_module_type [] mt

let rec pp_structure_elem ~is_header f = function
  | (l,SEdecl d) ->
     (match Common.get_duplicate (top_visible_mp ()) l with
      | None -> f d
      | Some ren ->
         v 1 (str ("namespace " ^ ren ^ " {") ++ fnl () ++ f d) ++
         fnl () ++ str "};")
  | (l,SEmodule m) ->
      (* Generate module as a struct or template struct *)
      let mp = MPdot (top_visible_mp (), l) in
      let name = pp_modname mp in
      if Pp.ismt (pp_module_expr ~is_header f [] m.ml_mod_expr) then mt ()
      else
        (match m.ml_mod_expr with
         | MEfunctor _ ->
             (* Functor: extract template declaration and body *)
             (* Only generate in header file - templates need definitions in headers *)
             if not is_header then mt () else
             let get_template_and_body = function
               | MEfunctor (mbid, mt, me) ->
                   let rec collect_params mbid mt me = match me with
                     | MEfunctor (mbid', mt', me') ->
                         let (params_rest, body) = collect_params mbid' mt' me' in
                         ((mbid, mt) :: params_rest, body)
                     | _ -> ([(mbid, mt)], me)
                   in
                   collect_params mbid mt me
               | _ -> ([], m.ml_mod_expr)
             in
             let (template_params, body) = get_template_and_body m.ml_mod_expr in
             let pp_template_param (mbid, mt) =
               let concept_name = pp_module_type [] mt in
               let param_name = pp_modname (MPbound mbid) in
               concept_name ++ str " " ++ param_name
             in
             let template_decl =
               str "template<" ++
               prlist_with_sep (fun () -> str ", ") pp_template_param template_params ++
               str ">"
             in
             (* Set context: we're inside a struct *)
             let old_context = !in_struct_context in
             in_struct_context := true;
             let struct_body = pp_module_expr ~is_header f (List.map (fun (mbid, _) -> MPbound mbid) template_params) body in
             in_struct_context := old_context;  (* Restore context *)
             template_decl ++ fnl () ++
             str "struct " ++ name ++ str " {" ++ fnl () ++
             struct_body ++
             str "};"
         | MEapply _ ->
             (* Module application: generate using declaration *)
             (* Only in header - it's a type alias *)
             if not is_header then mt () else
             let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
             let using_decl = str "using " ++ name ++ str " = " ++ body ++ str ";" in
             (* Add static_assert for functor applications with known return types *)
             let static_assert = match m.ml_mod_type with
             | MTident kn ->
                 (* Functor returns a module of this type *)
                 let concept_name = pp_modname kn in
                 fnl () ++ str "static_assert(" ++ concept_name ++ str "<" ++ name ++ str ">);"
             | _ -> mt ()
             in
             using_decl ++ static_assert
         | MEstruct _ | MEident _ ->
             (* Regular module: generate struct *)
             (* For now, only generate in header - TODO: split decl/def for non-inline functions *)
             if not is_header then mt () else
             let old_context = !in_struct_context in
             in_struct_context := true;
             let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
             in_struct_context := old_context;
             let struct_def = str "struct " ++ name ++ str " {" ++ fnl () ++
               body ++
               str "};" in
             (* For modules with type annotations, add static_assert *)
             (* Check if module has a type by looking at ml_mod_type *)
             let static_assert = match m.ml_mod_type with
             | MTsig _ -> mt ()  (* No simple type annotation *)
             | MTident kn ->
                 (* Module implements a module type - add static_assert *)
                 let concept_name = pp_modname kn in
                 fnl () ++ str "static_assert(" ++ concept_name ++ str "<" ++ name ++ str ">);"
             | _ -> mt ()
             in
             struct_def ++ static_assert
        )
  | (l,SEmodtype m) ->
      (* Module types become concepts - only in header *)
      if not is_header then mt () else
      let def = pp_module_type [] m in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      (* Generate a C++ concept with template parameter *)
      str "template<typename M>" ++ fnl () ++
      hov 1 (str "concept " ++ name ++ str " = requires {" ++ fnl () ++ def ++ str "};") ++
      (match Common.get_duplicate (top_visible_mp ()) l with
       | None -> mt ()
       | Some ren -> fnl () ++ str ("template<typename M> concept "^ren^" = ") ++ name ++ str "<M>;")

and pp_module_expr ~is_header f params = function
  | MEident mp ->
      (* Reference to a module name *)
      pp_modname mp
  | MEapply (me, me') ->
      (* Functor application: collect all arguments and generate single template instantiation *)
      let rec collect_args acc = function
        | MEapply (f, arg) -> collect_args (arg :: acc) f
        | base -> (base, acc)
      in
      let (base, args) = collect_args [me'] me in
      let base_pp = pp_module_expr ~is_header f [] base in
      let args_pp = prlist_with_sep (fun () -> str ", ") (pp_module_expr ~is_header f []) args in
      base_pp ++ str "<" ++ args_pp ++ str ">"
  | MEfunctor (mbid, mt, me) ->
      (* Functor body: just generate the body, template params are handled in pp_structure_elem *)
      pp_module_expr ~is_header f (MPbound mbid :: params) me
  | MEstruct (mp, sel) ->
      (* Module structure: generate struct members *)
      push_visible mp params;
      let try_pp_structure_elem l x =
        let px = pp_structure_elem ~is_header f x in
        if Pp.ismt px then l else px::l
      in
      (* We cannot use fold_right here due to side effects in pp_structure_elem *)
      let l = List.fold_left try_pp_structure_elem [] sel in
      let l = List.rev l in
      pop_visible ();
      if List.is_empty l then mt ()
      else
        v 1 (prlist_with_sep cut2 identity l) ++ fnl ()

let rec prlist_sep_nonempty sep f = function
  | [] -> mt ()
  | [h] -> f h
  | h::t ->
     let e = f h in
     let r = prlist_sep_nonempty sep f t in
     if Pp.ismt e then r
     else e ++ sep () ++ r

let do_struct f s =
  let ppl (mp,sel) =
    push_visible mp [];
    let p = prlist_sep_nonempty cut2 f sel in
    (* for monolithic extraction, we try to simulate the unavailability
       of [MPfile] in names by artificially nesting these [MPfile] *)
    (if modular () then pop_visible ()); p
  in
  let p = prlist_sep_nonempty cut2 ppl s in
  (if not (modular ()) then repeat (List.length s) pop_visible ());
  v 0 p ++ fnl ()

let pp_struct s = do_struct (pp_structure_elem ~is_header:false pp_decl) s
let pp_hstruct s = do_struct (pp_structure_elem ~is_header:true pp_hdecl) s

let pp_signature s = do_struct pp_specif s

let cpp_descr = {
  keywords = keywords;
  file_suffix = ".cpp";
  file_naming = file_of_modfile;
  preamble = preamble;
  pp_struct = pp_struct;
  pp_hstruct = pp_hstruct;
  sig_suffix = Some ".h";
  sig_preamble = sig_preamble;
  pp_sig = pp_signature;
  pp_decl = pp_decl;
}
