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
(* Track when we're in a non-local context (static inline variable initialization).
   Lambdas in non-local contexts cannot have capture-default [&]. *)
let in_nonlocal_context = ref false
(* Track current struct name for qualifying out-of-struct definitions *)
let current_struct_name : Pp.t option ref = ref None
(* Track whether we're inside a template struct (functor) *)
let in_template_struct = ref false
(* Track eponymous type info for method generation.
   When a module M contains an inductive type m (lowercase of M),
   functions taking shared_ptr<m> as first arg become methods on m. *)
let eponymous_type_ref : GlobRef.t option ref = ref None
(* Collected method candidates: (function_ref, body, type, this_position) for current eponymous type.
   this_position is the index (0-based) of the first argument that matches the eponymous type. *)
let method_candidates : (GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int) list ref = ref []

(* Eponymous record: when a module M contains a record with the same name (e.g., module CHT with record CHT),
   we merge the record fields into the module struct to avoid C++ name conflicts.
   Stores: (record_ref, field_refs, ind_packet) *)
let eponymous_record : (GlobRef.t * GlobRef.t option list * Miniml.ml_ind_packet) option ref = ref None

(* Global registry of methods across all modules.
   Maps function GlobRef to (eponymous_type_ref, this_position).
   This allows cross-module method call transformation. *)
let global_method_registry : (GlobRef.t, GlobRef.t * int) Hashtbl.t = Hashtbl.create 100

let register_method (func_ref : GlobRef.t) (epon_ref : GlobRef.t) (this_pos : int) =
  Hashtbl.replace global_method_registry func_ref (epon_ref, this_pos)

let is_registered_method (func_ref : GlobRef.t) : (GlobRef.t * int) option =
  Hashtbl.find_opt global_method_registry func_ref

(* Global registry of eponymous records.
   When a module M contains a record with the same name (e.g., module CHT with record CHT),
   the record fields are merged directly into the module struct. This avoids C++ name
   conflicts where both the module and record would have the same name.

   This registry is global (not per-module) because type references from OTHER modules
   need to know how to render the type name. Without this registry, a reference to CHT
   from another module would incorrectly generate "CHT::cHT" instead of just "CHT".

   See also: pp_inductive_type_name which uses this registry for type name rendering. *)
let global_eponymous_record_registry : (GlobRef.t, unit) Hashtbl.t = Hashtbl.create 100

let register_eponymous_record (record_ref : GlobRef.t) =
  Hashtbl.replace global_eponymous_record_registry record_ref ()

let is_eponymous_record_global (r : GlobRef.t) : bool =
  Hashtbl.mem global_eponymous_record_registry r

(* Track current structure's declarations for finding methods from sibling modules.
   When processing a module like List inside tree.v, we need to also scan
   sibling declarations (like app) that are from the same Rocq module. *)
let current_structure_decls : (Label.t * Miniml.ml_structure_elem) list ref = ref []

(* Reset ALL global state - must be called between extractions to avoid pollution.
   This prevents state from one extraction affecting another when running multiple
   extractions in the same process (e.g., during 'dune build'). *)
let reset_cpp_state () =
  in_struct_context := false;
  in_nonlocal_context := false;
  current_struct_name := None;
  in_template_struct := false;
  eponymous_type_ref := None;
  eponymous_record := None;
  method_candidates := [];
  current_structure_decls := [];
  Hashtbl.clear global_method_registry;
  Hashtbl.clear global_eponymous_record_registry

(* Check if a function is a projection for the eponymous record.
   Such projections are redundant when the record fields are merged into the module struct. *)
let is_eponymous_record_projection r =
  match !eponymous_record with
  | None -> false
  | Some (epon_ref, _, _) ->
      if Table.is_projection r then
        let (ip, _arity) = Table.projection_info r in
        (* Check if this projection's inductive matches the eponymous record *)
        Environ.QGlobRef.equal Environ.empty_env (GlobRef.IndRef ip) epon_ref
      else
        false

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

(* ============================================================================
   Helper functions to reduce code duplication
   ============================================================================ *)

(* Check if a type name is already qualified (contains ::) *)
let is_qualified_name name_str = String.contains name_str ':'

(* Check if a GlobRef is a record type (not a regular inductive).
   Records don't get wrapped in namespace structs, so they keep their original case. *)
let is_record_inductive r =
  match r with
  | GlobRef.IndRef _ -> Table.get_record_fields r <> []
  | _ -> false

(* Check if a GlobRef refers to a local inductive (defined in current module scope).
   Local inductives don't need namespace qualification (e.g., List::list vs just list). *)
let is_local_inductive r =
  List.exists (Environ.QGlobRef.equal Environ.empty_env r) (get_local_inductives ())

(* Get the appropriate name for an inductive reference.
   - Local inductives: lowercase name directly (e.g., "list")
   - Non-local inductives: capitalized namespace prefix (e.g., "List::list")
   Returns (name_pp, needs_namespace) where:
   - name_pp is the printed name for namespace prefix
   - needs_namespace indicates if namespace qualification is needed *)
let inductive_name_info r =
  match r with
  | GlobRef.IndRef _ when is_eponymous_record_global r ->
      (* Eponymous record: merged into module struct, no nested namespace.
         Check this FIRST because local inductives can also be eponymous. *)
      (str (String.capitalize_ascii (str_global Type r)), false)
  | GlobRef.IndRef _ when is_local_inductive r ->
      (* Local inductive: use lowercase name directly, no namespace *)
      (pp_global Type r, false)
  | GlobRef.IndRef _ ->
      (* Non-local inductive: capitalize for namespace struct name *)
      (str (String.capitalize_ascii (str_global Type r)), true)
  | _ ->
      (* Non-inductive: use as-is, no namespace *)
      (pp_global Type r, false)

(* Format an inductive type name for type references.
   For inductives wrapped in namespace structs (Dnspace), the pattern is:
   - Wrapper struct: capitalized (e.g., "List", "Ordering")
   - Inner type: lowercase (e.g., "list", "ordering")
   So "Ordering::Ordering" becomes "Ordering::ordering".
   Non-inductives and local inductives are unchanged.
   EXCEPTION 1: Eponymous records (module M with record M) are merged into the
   module struct, so we use just the capitalized name (e.g., "CHT" not "CHT::cHT").
   EXCEPTION 2: Regular records (not eponymous) keep their original case because
   they don't get wrapped in namespace structs. *)
let pp_inductive_type_name r =
  let result = match r with
  | GlobRef.IndRef _ when is_eponymous_record_global r ->
      (* Eponymous record: use capitalized name directly (merged into module struct)
         Check this FIRST because local inductives can also be eponymous *)
      str (String.capitalize_ascii (str_global Type r))
  | GlobRef.IndRef _ when is_record_inductive r ->
      (* Regular records: keep original case (no namespace wrapper) *)
      pp_global Type r
  | GlobRef.IndRef _ when is_local_inductive r ->
      (* Local inductive: use lowercase name directly *)
      str (String.uncapitalize_ascii (str_global Type r))
  | GlobRef.IndRef _ ->
      let base = str_global Type r in
      if is_qualified_name base then
        (* Already qualified (e.g., C::t from module parameter): use as-is *)
        str base
      else
        (* Non-local, unqualified inductive: Wrapper::lowercase_inner
           The wrapper is capitalized, inner is lowercase *)
        let wrapper = String.capitalize_ascii base in
        let inner = String.uncapitalize_ascii base in
        str (wrapper ^ "::" ^ inner)
  | _ ->
      (* Non-inductive: use as-is *)
      pp_global Type r
  in
  result

(* Add typename prefix for dependent types in template contexts.
   C++ requires 'typename' keyword when accessing nested types in templates. *)
let typename_prefix_for name_str =
  if !in_template_struct && is_qualified_name name_str then
    str "typename "
  else
    mt ()

(* Add struct qualification prefix if needed.
   When generating out-of-struct member function definitions, we need to qualify
   types that belong to the current struct. *)
let struct_qualifier_for r name_str =
  match !current_struct_name with
  | Some struct_name when not (is_qualified_name name_str) ->
      let full_path = Pp.string_of_ppcmds (GlobRef.print r) in
      let struct_name_str = Pp.string_of_ppcmds struct_name in
      (* Only qualify if the type belongs to the current struct *)
      if Common.contains_substring full_path struct_name_str then
        struct_name ++ str "::"
      else
        mt ()
  | _ -> mt ()

(* Check if a global function needs :: prefix to avoid name collision.
   When generating out-of-struct definitions, we add :: to call external functions
   rather than recursing into the struct's own member. *)
let needs_global_qualifier x =
  match !current_struct_name with
  | Some struct_name ->
      let name_str = str_global Term x in
      if is_qualified_name name_str then false  (* Already qualified *)
      else
        let full_path = Pp.string_of_ppcmds (GlobRef.print x) in
        let struct_name_str = Pp.string_of_ppcmds struct_name in
        (* Function is external if its path doesn't contain struct name *)
        not (Common.contains_substring full_path struct_name_str)
  | None -> false

(* Look up method info for a function reference.
   Checks both local method_candidates and global method_registry.
   Returns Some this_pos if the function is a method, None otherwise. *)
let lookup_method_this_pos n =
  (* First check local method_candidates *)
  let local_result = List.find_map (fun (r', _, _, pos) ->
    if Environ.QGlobRef.equal Environ.empty_env n r' then Some pos else None
  ) !method_candidates in
  match local_result with
  | Some pos -> Some pos
  | None ->
    (* Fall back to global registry for cross-module methods *)
    match is_registered_method n with
    | Some (_, pos) -> Some pos
    | None -> None

(* Helper module for tracking variable names *)
module IdSet = Set.Make(Names.Id)

(* Check if a lambda actually needs to capture variables from enclosing scope.
   A lambda needs [&] capture if its body references variables that are:
   - Not lambda parameters
   - Not locally declared within the lambda body
   - 'this' pointer (always needs capture in a lambda)
   Returns true if capture is needed, false if [] can be used.

   Also checks recursively: if a nested lambda captures from the outer lambda's scope,
   that counts as the outer lambda needing capture. *)
let rec lambda_needs_capture (params : (Minicpp.cpp_type * Names.Id.t option) list)
                              (body : Minicpp.cpp_stmt list) : bool =
  let open Minicpp in

  (* Collect parameter names *)
  let param_names = List.fold_left (fun acc (_, id_opt) ->
    match id_opt with Some id -> IdSet.add id acc | None -> acc
  ) IdSet.empty params in

  (* Track if 'this' is used - it always requires capture *)
  let uses_this = ref false in

  (* Collect all variable references and local declarations from expressions and statements *)
  let rec collect_from_expr (refs, decls) e =
    match e with
    | CPPvar id -> (IdSet.add id refs, decls)
    | CPPvar' _ -> (refs, decls)  (* de Bruijn - ignore *)
    | CPPthis -> uses_this := true; (refs, decls)  (* 'this' requires capture *)
    | CPPfun_call (f, args) ->
        let acc = collect_from_expr (refs, decls) f in
        List.fold_left collect_from_expr acc args
    | CPPnamespace (_, e') -> collect_from_expr (refs, decls) e'
    | CPPderef e' -> collect_from_expr (refs, decls) e'
    | CPPmove e' -> collect_from_expr (refs, decls) e'
    | CPPforward (_, e') -> collect_from_expr (refs, decls) e'
    | CPPlambda (inner_params, _, inner_body) ->
        (* For nested lambdas, don't count their parameters or local vars as our refs.
           But DO check if the nested lambda itself captures from OUR scope. *)
        let inner_param_names = List.fold_left (fun acc (_, id_opt) ->
          match id_opt with Some id -> IdSet.add id acc | None -> acc
        ) IdSet.empty inner_params in
        let (inner_refs, inner_decls) = List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) inner_body in
        (* Variables referenced in inner lambda that aren't its own params/locals
           might be captured from our scope *)
        let inner_free = IdSet.diff inner_refs (IdSet.union inner_param_names inner_decls) in
        (IdSet.union refs inner_free, decls)
    | CPPoverloaded exprs -> List.fold_left collect_from_expr (refs, decls) exprs
    | CPPmatch (scrut, cases) ->
        let acc = collect_from_expr (refs, decls) scrut in
        List.fold_left (fun a (p, b) -> collect_from_expr (collect_from_expr a p) b) acc cases
    | CPPstructmk (_, _, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPstruct (_, _, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPstruct_id (_, _, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPget (e', _) -> collect_from_expr (refs, decls) e'
    | CPPget' (e', _) -> collect_from_expr (refs, decls) e'
    | CPPparray (arr, e') ->
        let acc = Array.fold_left (fun a e -> collect_from_expr a e) (refs, decls) arr in
        collect_from_expr acc e'
    | CPPnew (_, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPshared_ptr_ctor (_, e') -> collect_from_expr (refs, decls) e'
    | CPPmember (e', _) -> collect_from_expr (refs, decls) e'
    | CPParrow (e', _) -> collect_from_expr (refs, decls) e'
    | CPPmethod_call (obj, _, args) ->
        let acc = collect_from_expr (refs, decls) obj in
        List.fold_left collect_from_expr acc args
    | CPPqualified (e', _) -> collect_from_expr (refs, decls) e'
    | CPPrequires (_, constraints) ->
        List.fold_left (fun a (e', _) -> collect_from_expr a e') (refs, decls) constraints
    | CPPglob _ | CPPvisit | CPPmk_shared _ | CPPstring _ | CPPuint _ | CPPconvertible_to _ ->
        (refs, decls)

  and collect_from_stmt (refs, decls) stmt =
    match stmt with
    | SreturnVoid -> (refs, decls)
    | Sreturn e -> collect_from_expr (refs, decls) e
    | Sdecl (id, _) -> (refs, IdSet.add id decls)
    | Sasgn (id, _, e) ->
        let (refs', decls') = collect_from_expr (refs, decls) e in
        (refs', IdSet.add id decls')
    | Sexpr e -> collect_from_expr (refs, decls) e
    | Scustom_case (_, scrut, _, branches, _) ->
        let acc = collect_from_expr (refs, decls) scrut in
        List.fold_left (fun (r, d) (branch_vars, _, stmts) ->
          let branch_decls = List.fold_left (fun acc (id, _) -> IdSet.add id acc) d branch_vars in
          List.fold_left collect_from_stmt (r, branch_decls) stmts
        ) acc branches
  in

  let (all_refs, local_decls) = List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) body in
  let bound_vars = IdSet.union param_names local_decls in
  let free_vars = IdSet.diff all_refs bound_vars in
  (* Lambda needs capture if it has free variables OR uses 'this' *)
  not (IdSet.is_empty free_vars) || !uses_this

(* Check if a cpp_expr contains any lambdas that need capture (have free variables).
   Used to determine if IIFE wrapping is needed for static inline initializers.
   Closed lambdas (with []) don't need IIFE wrapping. *)
and expr_contains_capturing_lambda (e : Minicpp.cpp_expr) : bool =
  let open Minicpp in
  match e with
  | CPPlambda (params, _, body) ->
      (* Check if this lambda needs capture, OR if any nested lambdas need capture *)
      lambda_needs_capture params body ||
      List.exists stmt_contains_capturing_lambda body
  | CPPfun_call (f, args) -> expr_contains_capturing_lambda f || List.exists expr_contains_capturing_lambda args
  | CPPnamespace (_, e') -> expr_contains_capturing_lambda e'
  | CPPderef e' -> expr_contains_capturing_lambda e'
  | CPPmove e' -> expr_contains_capturing_lambda e'
  | CPPforward (_, e') -> expr_contains_capturing_lambda e'
  | CPPoverloaded exprs -> List.exists expr_contains_capturing_lambda exprs
  | CPPmatch (scrut, cases) ->
      expr_contains_capturing_lambda scrut || List.exists (fun (p, b) -> expr_contains_capturing_lambda p || expr_contains_capturing_lambda b) cases
  | CPPstructmk (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPstruct (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPstruct_id (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPget (e', _) -> expr_contains_capturing_lambda e'
  | CPPget' (e', _) -> expr_contains_capturing_lambda e'
  | CPPparray (args, e') -> Array.exists expr_contains_capturing_lambda args || expr_contains_capturing_lambda e'
  | CPPnew (_, args) -> List.exists expr_contains_capturing_lambda args
  | CPPshared_ptr_ctor (_, e') -> expr_contains_capturing_lambda e'
  | CPPmember (e', _) -> expr_contains_capturing_lambda e'
  | CPParrow (e', _) -> expr_contains_capturing_lambda e'
  | CPPmethod_call (obj, _, args) -> expr_contains_capturing_lambda obj || List.exists expr_contains_capturing_lambda args
  | CPPqualified (e', _) -> expr_contains_capturing_lambda e'
  | CPPrequires (_, constraints) -> List.exists (fun (e', _) -> expr_contains_capturing_lambda e') constraints
  | CPPvar _ | CPPvar' _ | CPPglob _ | CPPvisit | CPPmk_shared _ | CPPstring _ | CPPuint _ | CPPthis | CPPconvertible_to _ -> false

and stmt_contains_capturing_lambda (s : Minicpp.cpp_stmt) : bool =
  let open Minicpp in
  match s with
  | SreturnVoid -> false
  | Sreturn e -> expr_contains_capturing_lambda e
  | Sdecl _ -> false
  | Sasgn (_, _, e) -> expr_contains_capturing_lambda e
  | Sexpr e -> expr_contains_capturing_lambda e
  | Scustom_case (_, scrut, _, branches, _) ->
      expr_contains_capturing_lambda scrut ||
      List.exists (fun (_, _, stmts) -> List.exists stmt_contains_capturing_lambda stmts) branches

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
    (* NEW: Tid for local type references (e.g., nested structs inside modules).
       These don't need GlobRef qualification, just simple Id references.
       Can be parameterized like generic types: Leaf<int> *)
    | Tid (id, []) -> Id.print id
    | Tid (id, args) -> Id.print id ++ str "<" ++ pp_list (pp_rec false) args ++ str ">"
    | Tglob (r,tys, args) when is_inline_custom r ->
    let s = find_custom r in
    let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
    let cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_numbered_args "t" (fun i -> CCty_arg i) s)
                      | _ -> prev @ [curr]) [] cmds in
    pp_custom (Pp.string_of_ppcmds (GlobRef.print r) ^ " := " ^ s) (empty_env ()) None None tys [] args vl cmds
    | Tglob (r,[],_) ->
      (* Use pp_inductive_type_name for inductives to get Wrapper::lowercase pattern *)
      let type_name = pp_inductive_type_name r in
      let name_str = Pp.string_of_ppcmds type_name in
      typename_prefix_for name_str ++ struct_qualifier_for r name_str ++ type_name
    | Tglob (r,l,_) ->
      let type_name = pp_inductive_type_name r in
      let name_str = Pp.string_of_ppcmds type_name in
      typename_prefix_for name_str ++ struct_qualifier_for r name_str ++
      type_name ++ str "<" ++ pp_list (pp_rec false) l ++ str ">"
    | Tfun (d,c) -> std_angle "function" (pp_rec false c ++ pp_par true (pp_list (pp_rec false) d))
    | Tstruct (id, args) ->
      let id_str = Pp.string_of_ppcmds (pp_global Type id) in
      let templates =
        (match args with
        | [] -> mt ()
        | args -> str "<" ++ pp_list (pp_rec false) args ++ str ">") in
      typename_prefix_for id_str ++ pp_global Type id ++ templates
    | Tref t -> pp_rec false t ++ str "&"
    | Tmod (m, t) -> pp_tymod m ++ pp_rec false t
    | Tnamespace (r,t) ->
        (* DESIGN: Namespace-qualified types for inductive types.
           Rocq's inductives live in wrapper structs (e.g., type 'list' in struct 'List').
           Local inductives don't need namespace wrapping; non-local ones get the prefix.
           EXCEPTION: Eponymous records are merged into the module struct, so we use just
           the capitalized name without namespace qualification (CHT, not CHT::cHT). *)
        let (name, _needs_ns) = inductive_name_info r in
        (* Check if inner type is Tglob with the same reference *)
        (match (r, t) with
         | GlobRef.IndRef _, Tglob (r', args, _) when Environ.QGlobRef.equal Environ.empty_env r r' ->
           let templates = match args with
             | [] -> mt ()
             | args -> str "<" ++ pp_list (pp_rec false) args ++ str ">"
           in
           (* Skip prefix if type name already contains module path (::) *)
           let type_name_str = str_global Type r' in
           (* Check eponymous record FIRST because they can also be local *)
           if is_eponymous_record_global r' then
             (* Eponymous record: use capitalized name directly, no namespace nesting *)
             str (String.capitalize_ascii type_name_str) ++ templates
           else if is_qualified_name type_name_str then
             (* Already qualified (e.g., C::t from module parameter): add typename if in template *)
             typename_prefix_for type_name_str ++ str type_name_str ++ templates
           else
             (* Use lowercase inner name: List::list, Ordering::ordering *)
             let inner_name = String.uncapitalize_ascii type_name_str in
             name ++ str "::" ++ str inner_name ++ templates
         | _ ->
           (* Fallback: generic namespace-qualified type *)
           str "typename " ++ name ++ str "::" ++ pp_rec false t)
    | Tqualified (base_ty, nested_id) ->
        (* DESIGN: Template-dependent type access like 'typename M::Key::t'
           C++ templates require 'typename' to access nested types from dependent base types. *)
        let base_str = match base_ty with
          | Tglob (r, _, _) ->
            let (ns_name, needs_ns) = inductive_name_info r in
            if needs_ns then
              ns_name ++ str "::" ++ pp_rec false base_ty
            else
              pp_rec false base_ty
          | _ -> pp_rec false base_ty
        in
        str "typename " ++ base_str ++ str "::" ++ Id.print nested_id
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
    | Tany -> str "std::any"
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
    (* Determine the base name for a global reference *)
    let base_name = match x with
      | GlobRef.IndRef _ ->
        let (ns_name, needs_ns) = inductive_name_info x in
        let type_name_str = str_global Type x in
        (* Check eponymous record FIRST because they can also be local *)
        if is_eponymous_record_global x then
          (* Eponymous record: use capitalized name (merged into module struct) *)
          str (String.capitalize_ascii type_name_str)
        else if is_qualified_name type_name_str then
          (* Already qualified (e.g., C::t from module parameter): use as-is
             Do NOT lowercase - the qualifier (like module param C) should keep case *)
          str type_name_str
        else if needs_ns then
          (* Non-local, unqualified inductive: add capitalized namespace prefix, lowercase inner *)
          let inner_name = str (String.uncapitalize_ascii type_name_str) in
          ns_name ++ str "::" ++ inner_name
        else
          (* Local inductive: use lowercase name directly *)
          str (String.uncapitalize_ascii type_name_str)
      | GlobRef.VarRef _ ->
        (* Local variable reference - no prefix *)
        pp_global Term x
      | _ ->
        (* Function calls: add :: prefix for external functions to avoid name collision *)
        if needs_global_qualifier x then
          str "::" ++ pp_global Term x
        else
          pp_global Term x
    in
    (match tys with
    | [] -> apply base_name
    | _ ->
      let ty_args = pp_list (pp_cpp_type false []) tys in
      apply base_name ++ str "<" ++ ty_args ++ str ">")
  | CPPnamespace (r, t) ->
      (* Use inductive_name_info to get proper namespace name *)
      let (name, _) = inductive_name_info r in
      h (name ++ str "::" ++ pp_cpp_expr env args t)
  | CPPfun_call (CPPglob (n,tys), ts) when is_inline_custom n ->
    let s = find_custom n in
    let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
    let cmds = List.fold_left
    (fun prev curr -> match curr with
                      | CCstring s -> prev @ (parse_numbered_args "t" (fun i -> CCty_arg i) s)
                      | _ -> prev @ [curr]) [] cmds in
    pp_custom (Pp.string_of_ppcmds (GlobRef.print n) ^ " := " ^ s) env None None tys [] (List.rev ts) [] cmds
  | CPPfun_call (CPPglob (n, _tys), ts) when lookup_method_this_pos n <> None ->
    (* Transform function call to method call: f(a0, a1, ...) -> a[this_pos]->f(other_args)
       Handles both local method_candidates and cross-module registered methods. *)
    let method_name = Id.of_string (Common.pp_global_name Term n) in
    let this_pos = match lookup_method_this_pos n with Some p -> p | None -> 0 in
    let args_normal = List.rev ts in  (* Convert to normal order *)
    let (this_arg_opt, other_args) = Common.extract_at_pos this_pos args_normal in
    (match this_arg_opt with
     | Some this_arg ->
       let obj_s = pp_cpp_expr env args this_arg in
       let args_s = pp_list (pp_cpp_expr env args) other_args in
       obj_s ++ str "->" ++ Id.print method_name ++ str "(" ++ args_s ++ str ")"
     | None ->
       (* Fallback - shouldn't happen for registered methods *)
       pp_cpp_expr env args (CPPglob (n, _tys)) ++ str "()")
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
      (* Use [] for closed lambdas (no captured variables), [&] otherwise *)
      let needs_capture = lambda_needs_capture params body in
      let capture_str = if needs_capture then str "[&](" else str "[](" in
      let (params_s, capture) =
        (match params with
        | [] -> str "void", capture_str
        | _ -> pp_list (fun (ty, id_opt) ->
            let id_s = match id_opt with None -> str "" | Some id -> Id.print id in
            (pp_cpp_type false [] ty) ++ spc () ++ id_s) (List.rev params), capture_str)
      in
      let body_s = pp_list_stmt (pp_cpp_stmt env args) body in
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
      (* Match Dstruct naming: records keep original case, inductives are lowercased. *)
      let struct_name = match id with
        | GlobRef.IndRef _ when is_record_inductive id ->
            (* Records keep original case - no namespace wrapper *)
            pp_global Type id
        | GlobRef.IndRef _ ->
            let base = str_global Type id in
            str (String.uncapitalize_ascii base)
        | _ -> pp_global Type id
      in
      struct_name ++  templates ++ str "::make(" ++ es_s ++ str ")"
  | CPPstruct (id, tys, es) ->
      let es_s = pp_list (pp_cpp_expr env args) es in
      let templates =
        (match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">") in
      (* Match Dstruct naming: records keep original case, inductives are lowercased. *)
      let struct_name = match id with
        | GlobRef.IndRef _ when is_record_inductive id ->
            (* Records keep original case - no namespace wrapper *)
            pp_global Type id
        | GlobRef.IndRef _ ->
            let base = str_global Type id in
            str (String.uncapitalize_ascii base)
        | _ -> pp_global Type id
      in
      struct_name ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPstruct_id (id, tys, es) ->
      let es_s = pp_list (pp_cpp_expr env args) es in
      let templates =
        (match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">") in
      Id.print id ++ templates ++ str "{" ++ es_s ++ str "}"
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
      (* Use newlines without commas for requires clauses *)
      let exprs_s = prlist_with_sep fnl (fun (e1, e2) ->
        str "  { " ++ pp_cpp_expr env args e1 ++ str " } -> " ++ pp_cpp_expr env args e2 ++ str ";") exprs in
      str "requires " ++ ty_vars_s ++ str "{" ++ fnl () ++ exprs_s ++ fnl () ++ str "}"
  | CPPnew (ty, exprs) ->
      str "new " ++ pp_cpp_type false [] ty ++ str "(" ++ pp_list (pp_cpp_expr env args) exprs ++ str ")"
  | CPPshared_ptr_ctor (ty, expr) ->
      let std_shared_ptr = if Table.std_lib () = "BDE" then "bsl::shared_ptr" else "std::shared_ptr" in
      str std_shared_ptr ++ str "<" ++ pp_cpp_type false [] ty ++ str ">(" ++ pp_cpp_expr env args expr ++ str ")"
  | CPPthis -> str "this"
  | CPPmember (e, id) ->
      pp_cpp_expr env args e ++ str "." ++ Id.print id
  | CPParrow (e, id) ->
      pp_cpp_expr env args e ++ str "->" ++ Id.print id
  | CPPmethod_call (obj, method_name, call_args) ->
      pp_cpp_expr env args obj ++ str "->" ++ Id.print method_name ++
      str "(" ++ pp_list (pp_cpp_expr env args) call_args ++ str ")"
  | CPPqualified (e, id) ->
      pp_cpp_expr env args e ++ str "::" ++ Id.print id
  | CPPconvertible_to ty ->
      str "std::convertible_to<" ++ pp_cpp_type false [] ty ++ str ">"

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

let pp_template_type = function
  | TTtypename -> str "typename"
  | TTfun (dom, cod) -> str "MapsTo<" ++ pp_cpp_type false [] cod  ++ str ", " ++ pp_list (pp_cpp_type false []) dom ++ str ">"
  | TTconcept (concept) -> pp_global Type concept

(* pp_cpp_field takes optional struct_name for printing constructors *)
let rec pp_cpp_field ?(struct_name : Pp.t option) env = function
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
| Fmethod (id, template_params, ret_ty, params, body, is_const, is_static) ->
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) params
    in
    let const_s = if is_const then str " const" else mt () in
    let static_s = if is_static then str "static " else mt () in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
    let template_s = match template_params with
      | [] -> mt ()
      | _ ->
        let args = pp_list (fun (tt, id) -> pp_template_type tt ++ spc () ++ Id.print id) template_params in
        str "template <" ++ args ++ str ">" ++ fnl ()
    in
    template_s ++
      h (static_s ++ (pp_cpp_type false [] ret_ty) ++ str " " ++ Id.print id ++ pp_par true params_s ++ const_s ++ str " {") ++ fnl () ++ body_s ++ str "}"
| Fconstructor (params, init_list, is_explicit) ->
    let sname = match struct_name with Some s -> s | None -> str "UNKNOWN_STRUCT" in
    let params_s =
      pp_list (fun (id, ty) ->
          (pp_cpp_type false [] ty) ++ str " " ++ Id.print id) params
    in
    let init_s = match init_list with
      | [] -> mt ()
      | _ -> str " : " ++ pp_list (fun (member, expr) ->
              Id.print member ++ str "(" ++ pp_cpp_expr env [] expr ++ str ")") init_list
    in
    let explicit_s = if is_explicit then str "explicit " else mt () in
    h (explicit_s ++ sname ++ pp_par true params_s ++ init_s ++ str " {}")
| Fnested_struct (id, fields) ->
    let fields_s = pp_cpp_fields_with_vis ~struct_name:(Id.print id) env fields in
    h (str "struct " ++ Id.print id ++ str " {") ++ fnl () ++ fields_s ++ fnl () ++ str "};"
| Fnested_using (id, ty) ->
    h (str "using " ++ Id.print id ++ str " = " ++ pp_cpp_type false [] ty ++ str ";")
| Fdeleted_ctor ->
    let sname = match struct_name with Some s -> s | None -> str "UNKNOWN_STRUCT" in
    h (sname ++ str "() = delete;")

(* Helper to print fields with visibility sections *)
and pp_cpp_fields_with_vis ?(struct_name : Pp.t option) env fields =
  (* Group consecutive fields by visibility *)
  let rec group_by_vis current_vis acc result = function
    | [] ->
        if acc = [] then List.rev result
        else List.rev ((current_vis, List.rev acc) :: result)
    | (fld, vis) :: rest ->
        if vis = current_vis then
          group_by_vis current_vis (fld :: acc) result rest
        else
          let result' = if acc = [] then result
                       else (current_vis, List.rev acc) :: result in
          group_by_vis vis [fld] result' rest
  in
  let groups = group_by_vis VPublic [] [] fields in
  (* Check if we need visibility labels (only if mixed or all private) *)
  let needs_labels = match groups with
    | [] -> false
    | [(VPublic, _)] -> false  (* All public - struct default is public *)
    | _ -> true  (* Mixed or all private *)
  in
  let pp_group (vis, flds) =
    if needs_labels then
      let vis_str = match vis with VPublic -> "public:" | VPrivate -> "private:" in
      str vis_str ++ fnl () ++
      pp_list_stmt (pp_cpp_field ?struct_name env) flds
    else
      pp_list_stmt (pp_cpp_field ?struct_name env) flds
  in
  prlist_with_sep fnl pp_group groups

let rec pp_cpp_decl env =
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
    (* CRITICAL DESIGN: Transform namespaces into structs
       This is the key innovation enabling module support in C++.

       Why:
       1. C++ doesn't allow namespaces inside structs, but we need inductives to be nested
       2. Using structs instead of namespaces gives us scoped type definitions
       3. This aligns with the goal of generating modules as template structs

       Context tracking: Set in_struct_context so nested declarations know they're inside
       a struct and can apply appropriate transformations (static keywords, nested inductives). *)
    let old_context = !in_struct_context in
    in_struct_context := true;
    let ds = pp_list_stmt (pp_cpp_decl env) decls in
    in_struct_context := old_context;

    (* Generate as struct to allow nesting inside other structs/modules *)
    (* Capitalize the struct name. The inner inductive struct is lowercase,
       so capitalization creates different names: struct List { struct list { ... }; };
       For already capitalized names like 'Ordering', inner becomes 'ordering'. *)
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
    let base_name = prlist_with_sep (fun () -> str "::") (fun (n, tys) ->
      (match tys with
      | [] -> pp_global Type n
      | _ -> pp_global Type n ++ str "<" ++ (pp_list (pp_cpp_type false []) tys) ++ str ">")) ids
      in
    (* If generating out-of-struct definitions, prepend struct name *)
    let name = match !current_struct_name with
      | Some struct_name when not !in_struct_context -> struct_name ++ str "::" ++ base_name
      | _ -> base_name
      in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
    (* DESIGN: Static member functions for struct context
       When a function is inside a struct (module), it needs to be static because:
       1. Structs don't have implicit 'this' for free functions
       2. Qualified names (Module::func) indicate out-of-line member definitions
       3. Template functions at module scope are static helpers

       Heuristics for detecting struct membership:
       - Multiple IDs: qualified name like MakeMap<K,V>::find indicates member
       - Non-empty tys: template function likely a member helper
       - in_struct_context: explicitly tracking struct nesting
       - current_struct_name set: generating out-of-struct definitions (no static) *)
    let is_qualified = List.length ids > 1 || (match ids with | [(_, tys)] when tys <> [] -> true | _ -> false) in
    let is_struct_member = is_qualified || !in_struct_context in
    let is_out_of_struct_def = match !current_struct_name with | Some _ -> not !in_struct_context | None -> false in
    let static_kw = if is_struct_member && not is_out_of_struct_def then str "static " else mt () in
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
    (* For regular inductives, use lowercase struct name to avoid conflict with
       the wrapper namespace struct (which is capitalized).
       Pattern: struct List { struct list { ... }; };
       EXCEPTION 1: Records don't get wrapped in namespace structs, so they
       keep their original case to avoid name collision with values.
       EXCEPTION 2: Eponymous records are merged into the module struct,
       so they use the capitalized name directly.
       Check eponymous FIRST, then records, then default to lowercase. *)
    let struct_name = match id with
      | GlobRef.IndRef _ when is_eponymous_record_global id ->
          let base = str_global Type id in
          str (String.capitalize_ascii base)
      | GlobRef.IndRef _ when is_record_inductive id ->
          (* Records keep original case - no namespace wrapper *)
          pp_global Type id
      | GlobRef.IndRef _ ->
          let base = str_global Type id in
          str (String.uncapitalize_ascii base)
      | _ -> pp_global Type id
    in
    let f_s = pp_cpp_fields_with_vis ~struct_name env fields in
    str "struct " ++ struct_name ++ str " {" ++ fnl () ++ f_s ++ fnl () ++ str "};"
| Dstruct_decl id ->
    str "struct " ++ pp_global Type id ++ str ";"
| Dusing (id, ty) ->
    str "using " ++ pp_global Type id ++ str " = " ++ pp_cpp_type false [] ty ++ str ";"
| Dasgn (id, ty, e) ->
    (* DESIGN: Static inline member variables for module constants
       In C++17, static data members can be defined inside the class with 'inline'.

       Why:
       - 'static': This is a class/struct member variable, not an instance variable
       - 'inline': Allows definition in header file without violating ODR (One Definition Rule)
       - Enables constant propagation by the compiler since definitions are available

       Without 'inline', multiple .cpp files including this header would cause linker errors
       due to duplicate symbol definitions.

       Note: When in_struct_context and the expression contains lambdas, we wrap the
       initializer in an IIFE (Immediately Invoked Function Expression) to allow
       nested lambdas to use [&] capture. This is necessary because:
       - C++ forbids capture-default in "non-local" lambdas
       - ALL lambdas directly in a static inline initializer are "non-local"
       - But by wrapping in []() { return expr; }(), inner lambdas are now "local" *)
    let static_kw = if !in_struct_context then str "static inline " else mt () in
    let expr_pp = pp_cpp_expr env [] e in
    (* Wrap in IIFE only when in struct context AND the expression contains lambdas.
       This is needed because C++ forbids capture-default [&] in non-local lambdas.
       If there are no lambdas, no wrapping is needed. *)
    let needs_iife = !in_struct_context && expr_contains_capturing_lambda e in
    let wrapped_expr = if needs_iife then
      str "[]() {" ++ fnl () ++ str "return " ++ expr_pp ++ str ";" ++ fnl () ++ str "}()"
    else
      expr_pp
    in
    h (static_kw ++ (pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str " = " ++ wrapped_expr ++ str ";")
| Ddecl (id, ty) ->
    h ((pp_cpp_type false [] ty) ++ str " " ++ pp_global Type id ++ str ";")
| Dconcept (id, cstr) ->
    (* For hoisted concepts, use only the simple base name without module qualification *)
    let simple_name = Common.pp_global_name Type id in
    (* Extract just the last component after :: if present *)
    let last_component = match String.rindex_opt simple_name ':' with
      | Some idx when idx > 0 && idx < String.length simple_name - 1 && simple_name.[idx-1] = ':' ->
          String.sub simple_name (idx + 1) (String.length simple_name - idx - 1)
      | _ -> simple_name
    in
    h (str "concept " ++ str last_component ++ str " = " ++ pp_cpp_expr env [] cstr ++ str ";")
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
  | Record fields | TypeClass fields -> mt ()
  | _ ->
  let rec pp i =
    if i >= Array.length ind.ind_packets then mt ()
    else
      let ip = (kn,i) in
      let p = ind.ind_packets.(i) in
      if is_custom (GlobRef.IndRef ip) then pp (i+1)
      else
        (* Compute parameter-only type vars (same as in pp_cpp_ind_header) *)
        let param_sign = List.firstn ind.ind_nparams p.ip_sign in
        let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
        let param_vars = List.firstn num_param_vars p.ip_vars in
        pp_cpp_decl (empty_env ()) (gen_ind_cpp param_vars names.(i) cnames.(i) p.ip_types) ++ pp (i+1)
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
    | Dterm (r,_,_) when is_eponymous_record_projection r ->
          (* Skip - this is a projection for an eponymous record merged into module struct *)
          mt ()
    | Dind (kn,i) -> mt ()  (* Inductives are fully defined in headers *)
    | Dtype (r, l, t) -> mt ()
    | Dterm (r, a, Tglob (ty, args,e)) when is_monad ty ->
          let defs = List.filter (fun (_,_,l) -> l == []) (gen_dfuns (Array.of_list [r], Array.of_list [a], Array.of_list [Miniml.Tglob (ty, args,e)])) in
          pp_list_stmt (fun(ds, env, _) -> pp_cpp_decl env ds) defs
    | Dterm (r, _, _) when List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r') !method_candidates ->
          (* Skip - this function is generated as a method on the eponymous type *)
          mt ()
    | Dterm (r, _, _) when is_registered_method r <> None ->
          (* Skip - this function is registered as a method in another module *)
          mt ()
    | Dterm (r, a, t) when Translation.is_typeclass_instance a t ->
          (* Type class instances: fully defined in header, skip in implementation *)
          mt ()
    | Dterm (r, a, t) ->
        let (ds, env, tvars) = gen_decl_for_pp r a t in
        (*let _ = print_endline (Pp.string_of_ppcmds (pp_type false [] t)) in*)
        begin match ds, tvars with
        | Some ds , [] -> pp_cpp_decl env ds
        | _ , _ -> mt ()
        end
    | Dfix (rv,defs,typs) ->
          (* Filter out inline custom, method candidates, globally registered methods, and eponymous record projections *)
          let is_method_candidate x = List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env x r') !method_candidates in
          let is_global_method x = is_registered_method x <> None in
          let filter = Array.to_list (Array.map (fun x -> not (is_inline_custom x) && not (is_method_candidate x) && not (is_global_method x) && not (is_eponymous_record_projection x)) rv) in
          let rv = Array.filter_with filter rv in
          let defs = Array.filter_with filter defs in
          let typs = Array.filter_with filter typs in
          if Array.length rv = 0 then mt ()
          else
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
  | TypeClass fields ->
      (* Type classes become C++ concepts *)
      (* Skip if inside struct context - concepts are hoisted to namespace scope *)
      if !in_struct_context then mt ()
      else pp_cpp_decl (empty_env ()) (gen_typeclass_cpp names.(0) fields ind.ind_packets.(0))
  | Record fields ->
      (* Check if this is an eponymous record being merged into module struct *)
      let ind_ref = names.(0) in
      (match !eponymous_record with
      | Some (epon_ref, _, _) when Environ.QGlobRef.equal Environ.empty_env ind_ref epon_ref ->
          mt ()  (* Skip - merged into module struct *)
      | _ ->
          pp_cpp_decl (empty_env ()) (gen_record_cpp names.(0) fields ind.ind_packets.(0)))
  | _ ->
    (* DESIGN: Mutual inductive support with forward declarations
       Rocq supports mutually recursive inductive types. In C++, this requires:
       1. Forward declarations so each struct can reference the others
       2. Full definitions immediately after

       Example (tree and node are mutually inductive):
         struct Tree;  // forward decl
         struct Node;  // forward decl
         struct Tree { ... Node usage ... };
         struct Node { ... Tree usage ... }; *)
    let is_mutual = Array.length ind.ind_packets > 1 in
    let forward_decls =
      if is_mutual then
        let rec fwd i =
          if i >= Array.length ind.ind_packets then mt ()
          else
            let ip = (kn,i) in
            if is_custom (GlobRef.IndRef ip) then fwd (i+1)
            else
              let name = pp_global Type names.(i) in
              str "struct " ++ name ++ str ";" ++ fnl () ++ fwd (i+1)
        in
        fwd 0
      else mt ()
    in
    (* Helper to find method candidates from current_structure_decls for a given inductive.
       IMPORTANT: Skip functions whose signatures reference type aliases (Dtype) from the
       same module. This prevents issues like `heap_delete_max : tree -> priqueue` becoming
       a method on `tree`, where `priqueue` is a type alias not visible from inside `tree`. *)
    let find_methods_for_inductive ind_ref =
      let ind_modpath = modpath_of_r ind_ref in
      (* First, collect all type aliases (Dtype) defined in the same module.
         These are types like `priqueue := list tree` that become `using` declarations.
         Methods on nested inductives can't reference these (visibility issue). *)
      let module_type_aliases = ref [] in
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl (Dtype (r, _, _)) when ModPath.equal (modpath_of_r r) ind_modpath ->
            module_type_aliases := r :: !module_type_aliases
        | _ -> ()
      ) !current_structure_decls;
      (* Check if a type references any module-level type alias *)
      let rec refs_module_alias = function
        | Miniml.Tglob (r, args, _) ->
            List.exists (Environ.QGlobRef.equal Environ.empty_env r) !module_type_aliases ||
            List.exists refs_module_alias args
        | Miniml.Tarr (t1, t2) -> refs_module_alias t1 || refs_module_alias t2
        | Miniml.Tmeta {contents = Some t} -> refs_module_alias t
        | _ -> false
      in
      (* Find the position of the first argument matching the inductive type *)
      let rec find_ind_arg_pos pos = function
        | Miniml.Tarr (Miniml.Tglob (arg_ref, _, _), rest) when Environ.QGlobRef.equal Environ.empty_env arg_ref ind_ref ->
          Some pos
        | Miniml.Tarr (_, rest) -> find_ind_arg_pos (pos + 1) rest
        | _ -> None
      in
      (* Check if function comes from the same Rocq module as the inductive *)
      let same_module r = ModPath.equal (modpath_of_r r) ind_modpath in
      let methods = ref [] in
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl (Dterm (r, body, ty)) ->
          (* Skip if function signature references a module-level type alias *)
          if same_module r && not (refs_module_alias ty) then
            (match find_ind_arg_pos 0 ty with
            | Some pos ->
              (* Note: We allow functions with extra type variables beyond the inductive's.
                 These extra type vars become template parameters on the method. *)
              methods := (r, body, ty, pos) :: !methods;
              register_method r ind_ref pos
            | None -> ())
        | SEdecl (Dfix (rv, defs, typs)) ->
          Array.iteri (fun i r ->
            let ty = typs.(i) in
            (* Skip if function signature references a module-level type alias *)
            if same_module r && not (refs_module_alias ty) then begin
              let body = defs.(i) in
              match find_ind_arg_pos 0 ty with
              | Some pos ->
                (* Note: We allow functions with extra type variables beyond the inductive's.
                   These extra type vars become template parameters on the method. *)
                methods := (r, body, ty, pos) :: !methods;
                register_method r ind_ref pos
              | None -> ()
            end
          ) rv
        | _ -> ()
      ) !current_structure_decls;
      !methods
    in
    let rec pp i =
      if i >= Array.length ind.ind_packets then mt ()
      else
        let ip = (kn,i) in
        let p = ind.ind_packets.(i) in
        if is_custom (GlobRef.IndRef ip) then pp (i+1)
        else
          (* Get method candidates: first check if set via SEmodule processing,
             otherwise find from sibling declarations in current_structure_decls.
             IMPORTANT: Only use find_methods_for_inductive for top-level inductives.
             For inductives nested inside modules, only the eponymous type gets methods.
             This prevents issues like tree inside Priqueue getting methods that return
             priqueue (a sibling type alias not visible from inside tree). *)
          let ind_ref = GlobRef.IndRef ip in
          (* Check if ind_ref appears inside any SEmodule in current_structure_decls.
             This detects when an inductive is declared inside a submodule. *)
          let is_inside_submodule_decl =
            let rec find_in_module_expr = function
              | MEstruct (_, sel') ->
                  List.exists (fun (_l', se') ->
                    match se' with
                    | SEdecl (Dind (kn', ind')) ->
                        let rec check_packets i' =
                          if i' >= Array.length ind'.ind_packets then false
                          else
                            let r = GlobRef.IndRef (kn', i') in
                            Environ.QGlobRef.equal Environ.empty_env r ind_ref || check_packets (i' + 1)
                        in
                        check_packets 0
                    | _ -> false
                  ) sel'
              | MEfunctor (_, _, me) -> find_in_module_expr me
              | MEapply (me, _) -> find_in_module_expr me
              | MEident _ -> false
            in
            List.exists (fun (_l, se) ->
              match se with
              | SEmodule m -> find_in_module_expr m.ml_mod_expr
              | _ -> false
            ) !current_structure_decls
          in
          let methods = match !eponymous_type_ref with
            | Some epon_ref when Environ.QGlobRef.equal Environ.empty_env ind_ref epon_ref ->
                !method_candidates
            | _ when not !in_struct_context && not is_inside_submodule_decl ->
                (* For top-level inductives only, find methods from sibling declarations *)
                find_methods_for_inductive ind_ref
            | _ ->
                (* Inside a module, non-eponymous inductives don't get methods *)
                []
          in
          (* Compute parameter-only type vars.
             Parameters (before the colon) become template params.
             Indices (after the colon) are erased.
             ind.ind_nparams gives the number of Rocq parameters.
             p.ip_sign covers all args (params + indices).
             Count Keep entries in the first nparams positions to get param type var count. *)
          let param_sign = List.firstn ind.ind_nparams p.ip_sign in
          let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
          let param_vars = List.firstn num_param_vars p.ip_vars in
          let decl = gen_ind_header_v2 param_vars names.(i) cnames.(i) p.ip_types (List.rev methods) in
          (* DESIGN: Contextual wrapping for inductive definitions
             - If inside a struct/module: generate the inductive directly (no namespace wrapper)
             - If at module scope: wrap in a namespace struct (which becomes a struct via Dnspace)

             This allows inductives to nest naturally inside modules while maintaining
             proper scoping at the module level. *)
          let wrapped_decl =
            if !in_struct_context then decl
            else Dnspace (Some names.(i), [decl])
          in
          pp_cpp_decl (empty_env ()) wrapped_decl ++ pp (i+1)
    in
    forward_decls ++ pp 0

let pp_hdecl = function
    | Dtype (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_any_inline_custom r -> mt ()
    | Dterm (r,_,_) when is_eponymous_record_projection r ->
          (* Skip - this is a projection for an eponymous record merged into module struct *)
          mt ()
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
    | Dterm (r, _, _) when List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env r r') !method_candidates ->
          (* Skip - this function will be generated as a method on the eponymous type *)
          mt ()
    | Dterm (r, _, _) when is_registered_method r <> None ->
          (* Skip - this function is registered as a method in another module *)
          mt ()
    | Dterm (r, a, t) when Translation.is_typeclass_instance a t ->
          (* Type class instances: generate struct with static methods and static_assert *)
          let (ds_opt, class_ref_opt, type_args) = Translation.gen_instance_struct r a t in
          let struct_pp = match ds_opt with
            | Some ds -> pp_cpp_decl (empty_env ()) ds
            | None -> mt ()
          in
          (* Generate static_assert to verify the instance satisfies the concept *)
          let static_assert_pp = match class_ref_opt with
            | Some class_ref ->
                let instance_name = pp_global Type r in
                let class_name = pp_global Type class_ref in
                let type_args_pp = match type_args with
                  | [] -> mt ()
                  | args ->
                      str ", " ++ prlist_with_sep (fun () -> str ", ")
                        (fun ty -> pp_cpp_type false [] (convert_ml_type_to_cpp_type (empty_env ()) [] [] ty)) args
                in
                fnl () ++ str "static_assert(" ++ class_name ++ str "<" ++ instance_name ++ type_args_pp ++ str ">);"
            | None -> mt ()
          in
          struct_pp ++ static_assert_pp
    | Dterm (r, a, t) -> (* ADD CUSTOM for non-inlined *)
      let (ds, env, tvars) = gen_decl_for_pp r a t in
            begin match ds, tvars with
            | Some ds , [] ->
                (* For template structs, use full definitions instead of specs *)
                if !in_template_struct then
                  let (ds, env, _) = gen_decl r a t in pp_cpp_decl env ds
                else
                  let (ds, env) = gen_spec r a t in pp_cpp_decl env ds
            | Some ds , _::_ -> pp_cpp_decl env ds
            | None , _ ->
                if !in_template_struct then
                  let (ds, env, _) = gen_decl r a t in pp_cpp_decl env ds
                else
                  let (ds, env) = gen_spec r a t in pp_cpp_decl env ds
            end
    | Dfix (rv,defs,typs) ->
          (* Filter out inline custom, method candidates, and globally registered methods *)
          let is_method_candidate x = List.exists (fun (r', _, _, _) -> Environ.QGlobRef.equal Environ.empty_env x r') !method_candidates in
          let is_global_method x = is_registered_method x <> None in
          let filter = Array.to_list (Array.map (fun x -> not (is_inline_custom x) && not (is_method_candidate x) && not (is_global_method x) && not (is_eponymous_record_projection x)) rv) in
          let rv = Array.filter_with filter rv in
          let defs = Array.filter_with filter defs in
          let typs = Array.filter_with filter typs in
          if Array.length rv = 0 then mt ()
          else
          (* For template structs, generate full definitions inline, not just declarations *)
          if !in_template_struct then
            pp_list_stmt (fun(ds, env, _) ->  pp_cpp_decl env ds) (gen_dfuns (rv, defs, typs))
          else
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

(* DESIGN: Convert Rocq specifications to C++ concept requirements

   Rocq module types specify what operations/types are available on a module.
   In C++, this becomes a concept with 'requires' clauses checking:
   - Function signatures exist
   - Type aliases are defined

   Examples:
   - Sval (foo : int → int) becomes: requires { foo(std::declval<int>()) } -> std::same_as<int>;
   - Stype (Key) becomes: requires { typename M::Key; };

   This enables compile-time checking that modules satisfy their type signatures. *)
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
        (* For non-function values, generate a requires expression to check the value exists *)
        let cpp_ret = convert_ml_type_to_cpp_type (empty_env ()) [] [] ret_ty in
        (* Helper to qualify type names with M:: *)
        let rec qualify_type = function
          | Tglob (r, [], _) when not (is_custom r) ->
              str "typename M::" ++ pp_global Type r
          | Tglob (r, args, _) when not (is_custom r) ->
              pp_global Type r ++ str "<" ++ prlist_with_sep (fun () -> str ", ") qualify_type args ++ str ">"
          | Tglob (r, args, _) when is_custom r ->
              let custom_str = find_custom r in
              if String.contains custom_str '%' then
                (match args with
                | [arg] when custom_str = "std::optional<%t0>" ->
                    str "std::optional<" ++ qualify_type arg ++ str ">"
                | _ -> pp_cpp_type false [] (Tglob (r, args, [])))
              else
                str custom_str
          | Tshared_ptr ty ->
              str "std::shared_ptr<" ++ qualify_type ty ++ str ">"
          | Tvariant tys ->
              str "std::variant<" ++ prlist_with_sep (fun () -> str ", ") qualify_type tys ++ str ">"
          | Tnamespace (r, ty) ->
              pp_cpp_type false [] (Tnamespace (r, ty))
          | ty -> pp_cpp_type false [] ty
        in
        let (same_as, remove_cvref) =
          if Table.std_lib () = "BDE"
          then ("same_as", "bsl::remove_cvref_t")
          else ("std::same_as", "std::remove_cvref_t")
        in
        str "requires " ++ str same_as ++ str "<" ++ str remove_cvref ++ str "<decltype(M::" ++ name ++ str ")>, " ++ qualify_type cpp_ret ++ str ">;" ++ fnl ()
      else
        (* For functions, generate requires expression with parameters and return type *)
        let cpp_args = List.map (convert_ml_type_to_cpp_type (empty_env ()) [] []) args in
        let cpp_ret = convert_ml_type_to_cpp_type (empty_env ()) [] [] ret_ty in
        (* Helper to qualify type names with M:: *)
        let rec qualify_type = function
          | Tglob (r, [], _) when not (is_custom r) ->
              str "typename M::" ++ pp_global Type r
          | Tglob (r, args, _) when not (is_custom r) ->
              pp_global Type r ++ str "<" ++ prlist_with_sep (fun () -> str ", ") qualify_type args ++ str ">"
          | Tglob (r, args, _) when is_custom r ->
              let custom_str = find_custom r in
              if String.contains custom_str '%' then
                (match args with
                | [arg] when custom_str = "std::optional<%t0>" ->
                    str "std::optional<" ++ qualify_type arg ++ str ">"
                | _ -> pp_cpp_type false [] (Tglob (r, args, [])))
              else
                str custom_str
          | Tshared_ptr ty ->
              str "std::shared_ptr<" ++ qualify_type ty ++ str ">"
          | Tvariant tys ->
              str "std::variant<" ++ prlist_with_sep (fun () -> str ", ") qualify_type tys ++ str ">"
          | Tnamespace (r, ty) ->
              pp_cpp_type false [] (Tnamespace (r, ty))
          | ty -> pp_cpp_type false [] ty
        in
        (* Generate: { M::name(std::declval<arg1>(), ...) } -> std::same_as<ret_ty>; *)
        let (same_as, declval) =
          if Table.std_lib () = "BDE"
          then ("same_as", "bsl::declval")
          else ("std::same_as", "std::declval")
        in
        let declvals = List.map (fun arg_ty ->
          str declval ++ str "<" ++ qualify_type arg_ty ++ str ">()"
        ) cpp_args in
        let call_expr = str "M::" ++ name ++ str "(" ++ prlist_with_sep (fun () -> str ", ") identity declvals ++ str ")" in
        str "{ " ++ call_expr ++ str " } -> " ++ str same_as ++ str "<" ++ qualify_type cpp_ret ++ str ">;" ++ fnl ()
  | Stype (r,vl,ot) ->
      (* Generate requires clause for a type *)
      let name = pp_global_name Type r in
      str "typename M::" ++ name ++ str ";" ++ fnl ()

and pp_module_type params = function
  | MTident kn ->
      (* Reference to a concept name *)
      pp_modname kn
  | MTfunsig (mbid, mt, mt') ->
      (* DESIGN: Functor type signatures
         For a functor taking parameter Param of type MT returning MT',
         we just generate MT' since the template parameters are handled
         separately in pp_structure_elem.

         Example: module MakeMap(Key: OrderedType)(Value: BaseType) : SigName
         becomes: template<OrderedType Key, BaseType Value> struct MakeMap { ... };
         (parameter concepts are in template params, body type is pp_module_type) *)
      pp_module_type (MPbound mbid :: params) mt'
  | MTsig (mp, sign) ->
      (* DESIGN: Module type signatures become concept definitions
         Each Sval/Stype specification becomes a requires clause that checks
         the module parameter satisfies the expected interface.

         The signature { type Key; val find : Key -> Value } becomes:
         template<typename M> concept SigName = requires {
           typename M::Key;
           M::find(std::declval<M::Key>()) -> std::same_as<...>;
         }; *)
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
      (* DESIGN: Module generation - three cases
         1. Regular modules → struct ModuleName { members };
         2. Functors → template<Concept P1, Concept P2> struct Functor { members };
         3. Module applications → using Result = Functor<Arg1, Arg2>;

         This enables:
         - Type parameters via template arguments
         - Compile-time checking via concepts
         - Proper scoping and visibility of module members *)
      let mp = MPdot (top_visible_mp (), l) in
      let name = pp_modname mp in
      (* NOTE: Previously we had an emptiness check here that called pp_module_expr
         BEFORE setting up context. This caused side effects (method registration)
         to happen with wrong context. We now handle emptiness within each case. *)
      (match m.ml_mod_expr with
         | MEfunctor _ ->
             (* DESIGN: Functor template generation
                For a functor taking multiple parameters:
                  module MakeMap(K: OrderedType)(V: BaseType) = ...
                Generate:
                  template<OrderedType K, BaseType V>
                  struct MakeMap { ... };

                Only generate in header - C++ templates require definitions in headers.
                Template instantiation happens automatically at compile time. *)
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
             (* Set context: we're inside a template struct *)
             let old_context = !in_struct_context in
             let old_template = !in_template_struct in
             in_struct_context := true;
             in_template_struct := true;  (* Mark that we're in a template *)
             let struct_body = pp_module_expr ~is_header f (List.map (fun (mbid, _) -> MPbound mbid) template_params) body in
             in_struct_context := old_context;
             in_template_struct := old_template;  (* Restore template context *)
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
             let rec get_concept_name = function
               | MTident kn -> Some (pp_modname kn)
               | MTwith(mt, _) -> get_concept_name mt
               | MTfunsig (_, mt, mt') -> get_concept_name mt'
               | MTsig _ -> None
             in
             let static_assert = match get_concept_name m.ml_mod_type with
             | Some concept_name ->
                 fnl () ++ str "static_assert(" ++ concept_name ++ str "<" ++ name ++ str ">);"
             | None -> mt ()
             in
             using_decl ++ static_assert
         | MEstruct (_, sel) ->
             (* Regular module: generate struct in header, member definitions in implementation *)
             let old_context = !in_struct_context in
             let old_struct_name = !current_struct_name in
             let old_eponymous = !eponymous_type_ref in
             let old_methods = !method_candidates in
             (* Save parent's eponymous_record BEFORE detecting for this module *)
             let old_eponymous_record = !eponymous_record in

             (* Clear eponymous state for this module - will be set if this module has one *)
             eponymous_type_ref := None;
             eponymous_record := None;

             (* Find eponymous inductive: an inductive with lowercase of module name *)
             let module_name_str = Pp.string_of_ppcmds name in
             let lowercase_module = String.lowercase_ascii module_name_str in
             List.iter (fun (_l, se) ->
               match se with
               | SEdecl (Dind (kn, ind)) ->
                 Array.iteri (fun i p ->
                   let ind_ref = GlobRef.IndRef (kn, i) in
                   let ind_name = Common.pp_global_name Type ind_ref in
                   if String.lowercase_ascii ind_name = lowercase_module then begin
                     match ind.ind_kind with
                     | TypeClass _ ->
                         (* Type classes become concepts, no eponymous handling *)
                         ()
                     | Record fields ->
                         (* Eponymous RECORD: merge into module struct to avoid name conflict *)
                         eponymous_record := Some (ind_ref, fields, p);
                         register_eponymous_record ind_ref
                     | _ ->
                         (* Eponymous INDUCTIVE: existing method generation behavior *)
                         eponymous_type_ref := Some ind_ref
                   end
                 ) ind.ind_packets
               | _ -> ()
             ) sel;

             method_candidates := [];

             (* Collect method candidates: functions that take eponymous type as any argument.
                Find the first argument that matches and record its position.
                Exclude functions with additional type variables beyond those in the eponymous type.
                IMPORTANT: Only include functions from the SAME Rocq module as the eponymous type.
                This ensures that stdlib's app (from Corelib.Init.Datatypes) becomes a method on list
                (also from Corelib.Init.Datatypes), but rev (from Stdlib.Lists.List) does not.

                We scan BOTH the current module's sel AND the parent structure's decls
                (current_structure_decls) to find methods. This handles the case where
                list and app are from the same Rocq module but extracted as siblings. *)
             (* Collect method candidates for BOTH eponymous inductives AND eponymous records.
                For inductives, methods are generated on the nested inductive struct.
                For records, methods are generated directly on the module struct (which has record fields merged). *)
             let epon_ref_opt = match !eponymous_type_ref, !eponymous_record with
               | Some r, _ -> Some r
               | _, Some (r, _, _) -> Some r
               | None, None -> None
             in
             (match epon_ref_opt with
             | Some epon_ref ->
               (* Get the module path of the eponymous type/record *)
               let epon_modpath = modpath_of_r epon_ref in
               (* Find the position of the first argument matching the eponymous type/record *)
               let rec find_epon_arg_pos pos = function
                 | Miniml.Tarr (Miniml.Tglob (arg_ref, _, _), rest) when Environ.QGlobRef.equal Environ.empty_env arg_ref epon_ref ->
                   Some pos
                 | Miniml.Tarr (_, rest) -> find_epon_arg_pos (pos + 1) rest
                 | _ -> None
               in
               (* Check if function comes from the same Rocq module as eponymous type/record *)
               let same_module r = ModPath.equal (modpath_of_r r) epon_modpath in
               (* Helper to process a single declaration *)
               let process_decl (_l, se) =
                 match se with
                 | SEdecl (Dterm (r, body, ty)) ->
                   (* Only consider functions from the same Rocq module as the eponymous type/record *)
                   if same_module r then
                     (match find_epon_arg_pos 0 ty with
                     | Some pos ->
                       (* Note: We allow functions with extra type variables beyond the eponymous type's.
                          These extra type vars become template parameters on the method. *)
                       method_candidates := (r, body, ty, pos) :: !method_candidates;
                       register_method r epon_ref pos  (* Register globally for cross-module calls *)
                     | None -> ())
                 | SEdecl (Dfix (rv, defs, typs)) ->
                   (* Handle fixpoints similarly - only from same module *)
                   Array.iteri (fun i r ->
                     if same_module r then begin
                       let ty = typs.(i) in
                       let body = defs.(i) in
                       match find_epon_arg_pos 0 ty with
                       | Some pos ->
                         (* Note: We allow functions with extra type variables beyond the eponymous type's.
                            These extra type vars become template parameters on the method. *)
                         method_candidates := (r, body, ty, pos) :: !method_candidates;
                         register_method r epon_ref pos  (* Register globally for cross-module calls *)
                       | None -> ()
                     end
                   ) rv
                 | _ -> ()
               in
               (* Scan current module's declarations *)
               List.iter process_decl sel;
               (* Also scan parent structure's declarations for sibling functions
                  from the same Rocq module (e.g., app next to List module) *)
               List.iter process_decl !current_structure_decls
             | None -> ());

             (* Save THIS module's detected eponymous_record for struct generation *)
             let this_eponymous_record = !eponymous_record in

             (* DESIGN: Type class concept hoisting
                Type classes inside modules must be hoisted to namespace scope because C++ concepts
                can only be declared at namespace or global scope, not inside structs.

                Before generating the module struct:
                1. Collect all type class inductives from the module
                2. Generate their concepts at the current scope (before the struct)
                3. Skip them when generating the struct body *)
             let typeclass_concepts = if is_header then
               List.concat_map (fun (_l, se) ->
                 match se with
                 | SEdecl (Dind (kn, ind)) ->
                     List.concat (List.init (Array.length ind.ind_packets) (fun i ->
                       match ind.ind_kind with
                       | TypeClass fields ->
                           let ind_ref = GlobRef.IndRef (kn, i) in
                           let packet = ind.ind_packets.(i) in
                           [pp_cpp_decl (empty_env ()) (Translation.gen_typeclass_cpp ind_ref fields packet)]
                       | _ -> []
                     ))
                 | _ -> []
               ) sel
             else [] in
             let typeclasses_pp = prlist_with_sep fnl (fun x -> x) typeclass_concepts in
             let typeclasses_pp = if typeclass_concepts = [] then mt () else typeclasses_pp ++ fnl () ++ fnl () in

             (* Only set struct context for header; implementation needs out-of-struct definitions *)
             if is_header then
               in_struct_context := true
             else
               (* Track struct name for qualification - combine with parent for nested modules *)
               current_struct_name := (match old_struct_name with
                 | Some parent -> Some (parent ++ str "::" ++ name)
                 | None -> Some name);
             let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
             (* Save method_candidates before restoring old state - need them for generating record methods *)
             let this_method_candidates = !method_candidates in
             in_struct_context := old_context;
             current_struct_name := old_struct_name;
             eponymous_type_ref := old_eponymous;
             eponymous_record := old_eponymous_record;  (* Restore PARENT's value *)
             method_candidates := old_methods;
             if is_header then
               (* Header: full struct definition *)
               (* For eponymous records: add template params, record fields, and methods *)
               let (template_decl, record_fields_pp, record_methods_pp) = match this_eponymous_record with
                 | Some (epon_ref, fields, packet) ->
                     (* Generate template parameters from record's type vars *)
                     let ty_vars = packet.ip_vars in
                     let template_str = if ty_vars = [] then mt () else
                       str "template<" ++
                       prlist_with_sep (fun () -> str ", ")
                         (fun v -> str "typename " ++ Id.print v) ty_vars ++
                       str ">" ++ fnl ()
                     in
                     (* Generate record fields *)
                     let field_list = List.combine fields packet.ip_types.(0) in
                     let pp_field (field_ref, field_ty) =
                       let field_name = match field_ref with
                         | Some r -> str (Common.pp_global_name Term r)
                         | None -> str "_field"
                       in
                       let cpp_ty = pp_cpp_type false ty_vars (convert_ml_type_to_cpp_type (empty_env ()) [] ty_vars field_ty) in
                       cpp_ty ++ spc () ++ field_name ++ str ";"
                     in
                     let fields_pp = prlist_with_sep fnl pp_field field_list ++ fnl () in
                     (* Generate methods from method candidates, filtering out record projections
                       since they have the same names as fields and are redundant *)
                     let non_projection_candidates = List.filter (fun (r, _, _, _) ->
                       not (Table.is_projection r)
                     ) (List.rev this_method_candidates) in
                     let method_fields = Translation.gen_record_methods epon_ref ty_vars non_projection_candidates in
                     let methods_pp = if method_fields = [] then mt () else
                       prlist_with_sep fnl (fun (fld, _vis) -> pp_cpp_field (empty_env ()) fld) method_fields ++ fnl ()
                     in
                     (template_str, fields_pp, methods_pp)
                 | None -> (mt (), mt (), mt ())
               in
               let struct_def = template_decl ++
                 str "struct " ++ name ++ str " {" ++ fnl () ++
                 record_fields_pp ++
                 record_methods_pp ++
                 body ++
                 str "};" in
               (* For modules with type annotations, add static_assert *)
               let rec get_concept_name = function
                 | MTident kn -> Some (pp_modname kn)
                 | MTwith(mt, _) -> get_concept_name mt  (* Extract base from 'with' clauses *)
                 | MTfunsig (_, mt, mt') -> get_concept_name mt'  (* Extract return type from functor sig *)
                 | MTsig _ -> None  (* Anonymous signature, no concept *)
               in
               let static_assert = match get_concept_name m.ml_mod_type with
               | Some concept_name ->
                   fnl () ++ str "static_assert(" ++ concept_name ++ str "<" ++ name ++ str ">);"
               | None -> mt ()
               in
               typeclasses_pp ++ struct_def ++ static_assert
             else
               (* Implementation: just the member definitions (body is already processed) *)
               body
         | MEident _ ->
             (* Module alias: generate as is *)
             let old_context = !in_struct_context in
             let old_struct_name = !current_struct_name in
             if is_header then
               in_struct_context := true
             else
               (* Track struct name for qualification - combine with parent for nested modules *)
               current_struct_name := (match old_struct_name with
                 | Some parent -> Some (parent ++ str "::" ++ name)
                 | None -> Some name);
             let body = pp_module_expr ~is_header f [] m.ml_mod_expr in
             in_struct_context := old_context;
             current_struct_name := old_struct_name;
             if is_header then
               str "struct " ++ name ++ str " {" ++ fnl () ++ body ++ str "};"
             else
               body
        )
  | (l,SEmodtype m) ->
      (* Module types become concepts - only in header *)
      if not is_header then mt () else
      let def = pp_module_type [] m in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      (* Generate a C++ concept with template parameter *)
      (* TODO: Don't love the hard-coded 'M' for the typename *)
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
      (* Track current structure's declarations for sibling access *)
      let old_structure_decls = !current_structure_decls in
      current_structure_decls := sel;
      (* Register all inductives defined in this module before processing declarations.
         This ensures that references to sibling inductives don't get namespace-qualified. *)
      let old_local_inductives = get_local_inductives () in
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) ->
          (* Add all inductives in this mutual block *)
          Array.iteri (fun i _p -> add_local_inductive (GlobRef.IndRef (kn, i))) ind.ind_packets
        | _ -> ()
      ) sel;
      let try_pp_structure_elem l x =
        let px = pp_structure_elem ~is_header f x in
        if Pp.ismt px then l else px::l
      in
      (* We cannot use fold_right here due to side effects in pp_structure_elem *)
      let l = List.fold_left try_pp_structure_elem [] sel in
      let l = List.rev l in
      (* Restore previous local_inductives state for proper nesting *)
      clear_local_inductives ();
      List.iter add_local_inductive old_local_inductives;
      current_structure_decls := old_structure_decls;
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

let do_struct_with_decl_tracking f s =
  let ppl (mp,sel) =
    push_visible mp [];
    (* Track structure declarations for sibling access during inductive generation *)
    let old_decls = !current_structure_decls in
    current_structure_decls := sel;
    let p = prlist_sep_nonempty cut2 f sel in
    current_structure_decls := old_decls;
    (* for monolithic extraction, we try to simulate the unavailability
       of [MPfile] in names by artificially nesting these [MPfile] *)
    (if modular () then pop_visible ()); p
  in
  let p = prlist_sep_nonempty cut2 ppl s in
  (if not (modular ()) then repeat (List.length s) pop_visible ());
  v 0 p ++ fnl ()

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

let pp_struct s = do_struct_with_decl_tracking (pp_structure_elem ~is_header:false pp_decl) s
let pp_hstruct s = do_struct_with_decl_tracking (pp_structure_elem ~is_header:true pp_hdecl) s

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
