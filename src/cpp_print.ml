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

(** Pretty-printing of C++ types, expressions, statements, fields, and
    declarations.

    This module contains the core pretty-printing functions that convert MiniCpp
    AST nodes into Pp.t values representing C++ source code. It also includes
    lambda capture analysis, custom syntax parsing, and the Meyers singleton
    helper. *)

open Pp
open Names
open Table
open Miniml
open Mlutil
open Modutil
open Common
open Minicpp
open Translation
open Cpp_state
open Cpp_names

(** Registry of GlobRefs that are axiom types (extracted as std::any). Functions
    whose return type involves an axiom type should not be marked
    __attribute__((pure)) because they may transitively call axiom stubs that
    throw std::logic_error. *)
let axiom_type_refs : (GlobRef.t, unit) Hashtbl.t = Hashtbl.create 16

let register_axiom_type (r : GlobRef.t) = Hashtbl.replace axiom_type_refs r ()

let is_axiom_type_ref (r : GlobRef.t) = Hashtbl.mem axiom_type_refs r

(** Check if a lambda actually needs to capture variables from enclosing scope.
    A lambda needs [&] capture if its body references variables that are:
    - Not lambda parameters
    - Not locally declared within the lambda body
    - 'this' pointer (always needs capture in a lambda) Returns true if capture
      is needed, false if [] can be used.

    Also checks recursively: if a nested lambda captures from the outer lambda's
    scope, that counts as the outer lambda needing capture. *)
(** Check if an identifier is referenced in a list of statements.
    Used to decide whether a parameter or variable needs [[maybe_unused]]. *)
let stmts_reference_id target_id body =
  let open Minicpp in
  let found = ref false in
  let rec check_expr = function
    | CPPvar id when Id.equal id target_id -> found := true
    | CPPvar _ | CPPglob _ | CPPvisit | CPPmk_shared _ | CPPmk_unique _
    | CPPstring _ | CPPuint _ | CPPfloat _ | CPPconvertible_to _
    | CPPabort _ | CPPenum_val _ | CPPraw _ | CPPbool _ | CPPint _
    | CPPbrace_init | CPPthis | CPPunop _ -> ()
    | CPPfun_call (f, args) -> check_expr f; List.iter check_expr args
    | CPPnamespace (_, e) | CPPderef e | CPPmove e | CPPforward (_, e)
    | CPPget (e, _) | CPPget' (e, _) | CPPmember (e, _) | CPParrow (e, _)
    | CPPqualified (e, _) | CPPshared_ptr_ctor (_, e)
    | CPPunique_ptr_ctor (_, e) | CPPany_cast (_, e) -> check_expr e
    | CPPshared_from_this _ -> ()
    | CPPlambda (_, _, stmts, _) -> List.iter check_stmt stmts
    | CPPoverloaded es | CPPstructmk (_, _, es) | CPPstruct (_, _, es)
    | CPPstruct_id (_, _, es) | CPPnew (_, es) ->
      List.iter check_expr es
    | CPPparray (arr, e) -> Array.iter check_expr arr; check_expr e
    | CPPmethod_call (obj, _, args) ->
      check_expr obj; List.iter check_expr args
    | CPPrequires (_, constraints, _) ->
      List.iter (fun (e, _) -> check_expr e) constraints
    | CPPbinop (_, l, r) -> check_expr l; check_expr r
  and check_stmt = function
    | Sreturn (Some e) | Sexpr e -> check_expr e
    | Sreturn None | Sdecl _ | Sthrow _ | Sassert _ | Sraw _
    | Sstruct_def _ | Susing _ | Sdecl_init _ | Scontinue | Sbreak -> ()
    | Sasgn (_, _, e) -> check_expr e
    | Sif (c, t, f) ->
      check_expr c; List.iter check_stmt t; List.iter check_stmt f
    | Sswitch (e, _, branches, def) ->
      check_expr e;
      List.iter (fun (_, stmts) -> List.iter check_stmt stmts) branches;
      Option.iter (List.iter check_stmt) def
    | Scustom_case (_, e, _, branches, template) ->
      (* Only count scrutinee as a reference when the template actually uses it.
         E.g., unit match template "{ %br0 }" ignores the scrutinee, while nat
         template "if (%scrut <= 0) { ... }" uses it. *)
      if Common.contains_substring template "%scrut" then check_expr e;
      List.iter (fun (_, _, stmts) -> List.iter check_stmt stmts) branches
    | Sassign_field (o, _, e) -> check_expr o; check_expr e
    | Swhile (c, stmts) -> check_expr c; List.iter check_stmt stmts
    | Sblock stmts -> List.iter check_stmt stmts
    | Sblock_custom (_, _, _, _, args, _) -> List.iter check_expr args
    | Smatch (branches, default) ->
      List.iter (fun br ->
        check_expr br.smb_scrutinee;
        List.iter check_expr br.smb_extra_conds;
        ( match br.smb_reuse with
        | Some (cond, _, stmts) -> check_expr cond; List.iter check_stmt stmts
        | None -> () );
        List.iter check_stmt br.smb_body) branches;
      Option.iter (List.iter check_stmt) default
  in
  List.iter check_stmt body;
  !found

let[@warning "-39"] rec lambda_needs_capture
    (params : (Minicpp.cpp_type * Names.Id.t option) list)
    (body : Minicpp.cpp_stmt list) : bool * bool =
  let open Minicpp in
  (* Collect parameter names *)
  let param_names =
    List.fold_left
      (fun acc (_, id_opt) ->
        match id_opt with
        | Some id -> IdSet.add id acc
        | None -> acc )
      IdSet.empty
      params
  in
  (* Track if 'this' is used - it always requires capture *)
  let uses_this = ref false in
  (* Collect all variable references and local declarations from expressions and
     statements *)
  let rec collect_from_expr (refs, decls) e =
    match e with
    | CPPvar id -> (IdSet.add id refs, decls)
    | CPPthis ->
      uses_this := true;
      (refs, decls)
    | CPPshared_from_this _ ->
      uses_this := true;
      (refs, decls)
    | CPPfun_call (f, args) ->
      let acc = collect_from_expr (refs, decls) f in
      List.fold_left collect_from_expr acc args
    | CPPnamespace (_, e') -> collect_from_expr (refs, decls) e'
    | CPPderef e' -> collect_from_expr (refs, decls) e'
    | CPPmove e' -> collect_from_expr (refs, decls) e'
    | CPPforward (_, e') -> collect_from_expr (refs, decls) e'
    | CPPlambda (inner_params, _, inner_body, _) ->
      let inner_param_names =
        List.fold_left
          (fun acc (_, id_opt) ->
            match id_opt with
            | Some id -> IdSet.add id acc
            | None -> acc )
          IdSet.empty
          inner_params
      in
      let inner_refs, inner_decls =
        List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) inner_body
      in
      let inner_free =
        IdSet.diff inner_refs (IdSet.union inner_param_names inner_decls)
      in
      (IdSet.union refs inner_free, decls)
    | CPPoverloaded exprs ->
      List.fold_left collect_from_expr (refs, decls) exprs
    | CPPstructmk (_, _, args) ->
      List.fold_left collect_from_expr (refs, decls) args
    | CPPstruct (_, _, args) ->
      List.fold_left collect_from_expr (refs, decls) args
    | CPPstruct_id (_, _, args) ->
      List.fold_left collect_from_expr (refs, decls) args
    | CPPget (e', _) -> collect_from_expr (refs, decls) e'
    | CPPget' (e', _) -> collect_from_expr (refs, decls) e'
    | CPPparray (arr, e') ->
      let acc =
        Array.fold_left (fun a e -> collect_from_expr a e) (refs, decls) arr
      in
      collect_from_expr acc e'
    | CPPnew (_, args) -> List.fold_left collect_from_expr (refs, decls) args
    | CPPshared_ptr_ctor (_, e') -> collect_from_expr (refs, decls) e'
    | CPPunique_ptr_ctor (_, e') -> collect_from_expr (refs, decls) e'
    | CPPmember (e', _) -> collect_from_expr (refs, decls) e'
    | CPParrow (e', _) -> collect_from_expr (refs, decls) e'
    | CPPmethod_call (obj, _, args) ->
      let acc = collect_from_expr (refs, decls) obj in
      List.fold_left collect_from_expr acc args
    | CPPqualified (e', _) -> collect_from_expr (refs, decls) e'
    | CPPrequires (_, constraints, _) ->
      List.fold_left
        (fun acc (e', _) -> collect_from_expr acc e')
        (refs, decls)
        constraints
    | CPPbinop (_, lhs, rhs) ->
      collect_from_expr (collect_from_expr (refs, decls) lhs) rhs
    | CPPglob _
     |CPPvisit
     |CPPmk_shared _
     |CPPmk_unique _
     |CPPstring _
     |CPPuint _
     |CPPfloat _
     |CPPconvertible_to _
     |CPPabort _
     |CPPenum_val _
     |CPPraw _
     |CPPbool _
     |CPPint _
     |CPPbrace_init
     |CPPunop _ -> (refs, decls)
    | CPPany_cast (_, e) -> collect_from_expr (refs, decls) e
  and collect_from_stmt (refs, decls) stmt =
    match stmt with
    | Sreturn None -> (refs, decls)
    | Sreturn (Some e) -> collect_from_expr (refs, decls) e
    | Sexpr e -> collect_from_expr (refs, decls) e
    | Sdecl (id, _) -> (refs, IdSet.add id decls)
    | Sasgn (id, ty, e) ->
      let refs', decls' = collect_from_expr (refs, decls) e in
      ( match ty with
      | Some _ ->
        (* Declaration: ty id = e; — id is a new local *)
        (refs', IdSet.add id decls')
      | None ->
        (* Assignment: id = e; — id is a reference to an outer variable *)
        (IdSet.add id refs', decls') )
    | Sif (cond, then_stmts, else_stmts) ->
      List.fold_left
        collect_from_stmt
        (List.fold_left
           collect_from_stmt
           (collect_from_expr (refs, decls) cond)
           then_stmts )
        else_stmts
    | Sswitch (scrut, _, branches, default) ->
      let acc =
        List.fold_left
          (fun acc (_, stmts) -> List.fold_left collect_from_stmt acc stmts)
          (collect_from_expr (refs, decls) scrut)
          branches
      in
      ( match default with
      | Some stmts -> List.fold_left collect_from_stmt acc stmts
      | None -> acc )
    | Scustom_case (_, scrut, _, branches, _) ->
      List.fold_left
        (fun (r, d) (branch_vars, _, stmts) ->
          let branch_decls =
            List.fold_left (fun acc (id, _) -> IdSet.add id acc) d branch_vars
          in
          List.fold_left collect_from_stmt (r, branch_decls) stmts )
        (collect_from_expr (refs, decls) scrut)
        branches
    | Sassign_field (obj, _, e) ->
      collect_from_expr (collect_from_expr (refs, decls) obj) e
    | Swhile (cond, body) ->
      List.fold_left
        collect_from_stmt
        (collect_from_expr (refs, decls) cond)
        body
    | Sblock stmts -> List.fold_left collect_from_stmt (refs, decls) stmts
    | Sblock_custom (_, _, id, _, args, _) ->
      let acc = List.fold_left (fun a e -> collect_from_expr a e) (refs, decls) args in
      let refs', decls' = acc in
      (refs', IdSet.add id decls')
    | Smatch (branches, default) ->
      let acc =
        List.fold_left
          (fun acc br ->
            let acc = collect_from_expr acc br.smb_scrutinee in
            let acc = List.fold_left collect_from_expr acc br.smb_extra_conds in
            let acc =
              match br.smb_reuse with
              | Some (cond, _, stmts) ->
                let acc = collect_from_expr acc cond in
                List.fold_left collect_from_stmt acc stmts
              | None -> acc
            in
            let refs', decls' = acc in
            let branch_decls =
              (* Add structured-binding field names as declared. *)
              let d =
                List.fold_left
                  (fun d (bname, _, _) -> IdSet.add bname d)
                  decls' br.smb_field_bindings
              in
              match br.smb_var with
              | Some id -> IdSet.add id d
              | None -> d
            in
            List.fold_left collect_from_stmt (refs', branch_decls) br.smb_body)
          (refs, decls) branches
      in
      ( match default with
      | Some stmts -> List.fold_left collect_from_stmt acc stmts
      | None -> acc )
    | Sthrow _ | Sassert _ | Sraw _ | Sstruct_def _ | Susing _ | Sdecl_init _
    | Scontinue | Sbreak -> (refs, decls)
  in
  let all_refs, local_decls =
    List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) body
  in
  let bound_vars = IdSet.union param_names local_decls in
  let free_vars = IdSet.diff all_refs bound_vars in
  ((not (IdSet.is_empty free_vars)) || !uses_this, !uses_this)

(** Check if a cpp_expr contains any lambdas that need capture (have free
    variables). Used to determine if IIFE wrapping is needed for static inline
    initializers. Closed lambdas (with []) don't need IIFE wrapping. *)
and expr_contains_capturing_lambda (e : Minicpp.cpp_expr) : bool =
  let open Minicpp in
  match e with
  | CPPlambda (params, _, body, _) ->
    fst (lambda_needs_capture params body)
    || List.exists stmt_contains_capturing_lambda body
  | CPPfun_call (f, args) ->
    expr_contains_capturing_lambda f
    || List.exists expr_contains_capturing_lambda args
  | CPPnamespace (_, e') -> expr_contains_capturing_lambda e'
  | CPPderef e' -> expr_contains_capturing_lambda e'
  | CPPmove e' -> expr_contains_capturing_lambda e'
  | CPPforward (_, e') -> expr_contains_capturing_lambda e'
  | CPPoverloaded exprs -> List.exists expr_contains_capturing_lambda exprs
  | CPPstructmk (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPstruct (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPstruct_id (_, _, args) -> List.exists expr_contains_capturing_lambda args
  | CPPget (e', _) -> expr_contains_capturing_lambda e'
  | CPPget' (e', _) -> expr_contains_capturing_lambda e'
  | CPPparray (args, e') ->
    Array.exists expr_contains_capturing_lambda args
    || expr_contains_capturing_lambda e'
  | CPPnew (_, args) -> List.exists expr_contains_capturing_lambda args
  | CPPshared_ptr_ctor (_, e') -> expr_contains_capturing_lambda e'
  | CPPunique_ptr_ctor (_, e') -> expr_contains_capturing_lambda e'
  | CPPmember (e', _) -> expr_contains_capturing_lambda e'
  | CPParrow (e', _) -> expr_contains_capturing_lambda e'
  | CPPmethod_call (obj, _, args) ->
    expr_contains_capturing_lambda obj
    || List.exists expr_contains_capturing_lambda args
  | CPPqualified (e', _) -> expr_contains_capturing_lambda e'
  | CPPrequires (_, constraints, _) ->
    List.exists (fun (e', _) -> expr_contains_capturing_lambda e') constraints
  | CPPbinop (_, lhs, rhs) ->
    expr_contains_capturing_lambda lhs || expr_contains_capturing_lambda rhs
  | CPPvar _
   |CPPglob _
   |CPPvisit
   |CPPmk_shared _
   |CPPmk_unique _
   |CPPstring _
   |CPPuint _
   |CPPfloat _
   |CPPthis
   |CPPshared_from_this _
   |CPPconvertible_to _
   |CPPabort _
   |CPPenum_val _
   |CPPraw _
   |CPPbool _
   |CPPint _
   |CPPbrace_init
   |CPPunop _ -> false
  | CPPany_cast (_, e') -> expr_contains_capturing_lambda e'

and stmt_contains_capturing_lambda (s : Minicpp.cpp_stmt) : bool =
  let open Minicpp in
  let any = List.exists stmt_contains_capturing_lambda in
  let expr = expr_contains_capturing_lambda in
  match s with
  | Sreturn (Some e) | Sexpr e | Sasgn (_, _, e) -> expr e
  | Sreturn None -> false
  | Sassign_field (obj, _, e) -> expr obj || expr e
  | Sif (cond, then_s, else_s) -> expr cond || any then_s || any else_s
  | Sswitch (scrut, _, branches, default) ->
    expr scrut || List.exists (fun (_, stmts) -> any stmts) branches
    || (match default with Some stmts -> any stmts | None -> false)
  | Scustom_case (_, scrut, _, branches, _) ->
    expr scrut || List.exists (fun (_, _, stmts) -> any stmts) branches
  | Swhile (cond, body) -> expr cond || any body
  | Sblock stmts -> any stmts
  | Sblock_custom (_, _, _, _, args, _) -> List.exists expr args
  | Smatch (branches, default) ->
    List.exists (fun br ->
      expr br.smb_scrutinee
      || List.exists expr br.smb_extra_conds
      || ( match br.smb_reuse with
         | Some (cond, _, stmts) -> expr cond || any stmts
         | None -> false )
      || any br.smb_body) branches
    || (match default with Some stmts -> any stmts | None -> false)
  | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ | Sstruct_def _ | Susing _
  | Sdecl_init _ | Scontinue | Sbreak -> false

(** {2 Pretty-printing C++ syntax.} *)

(** Try evaluating a C++ code-generation thunk; on [TODO] exception, return
    fallback [o]. *)
let try_cpp c o = try c with TODO -> o

(** Print a C++ type modifier keyword (const, static, extern). *)
let pp_tymod = function
  | TMconst -> str "const "
  | TMstatic -> str "static "
  | TMextern -> str "extern "

(** Print a qualified standard-library angle-bracket type: [std::label<s>]. *)
let std_angle label s =
  str (sn ()).ns ++ str "::" ++ str label ++ str "<" ++ s ++ str ">"

(** Print an unqualified angle-bracket type: [label<s>]. *)
let cpp_angle label s = str label ++ str "<" ++ s ++ str ">"

(** Split a rendered C++ string on semicolons while respecting string
    literals (double-quoted) and character literals (single-quoted).
    Escaped quotes inside literals are handled. *)
let split_on_semicolons (s : string) : string list =
  let len = String.length s in
  let buf = Buffer.create 64 in
  let acc = ref [] in
  let i = ref 0 in
  while !i < len do
    let c = s.[!i] in
    if c = ';' then begin
      acc := Buffer.contents buf :: !acc;
      Buffer.clear buf;
      incr i
    end
    else if c = '"' || c = '\'' then begin
      (* Inside a string or char literal — consume until matching close *)
      let quote = c in
      Buffer.add_char buf c;
      incr i;
      while !i < len && s.[!i] <> quote do
        if s.[!i] = '\\' && !i + 1 < len then begin
          Buffer.add_char buf s.[!i];
          Buffer.add_char buf s.[!i + 1];
          i := !i + 2
        end else begin
          Buffer.add_char buf s.[!i];
          incr i
        end
      done;
      if !i < len then begin
        Buffer.add_char buf s.[!i]; (* closing quote *)
        incr i
      end
    end
    else begin
      Buffer.add_char buf c;
      incr i
    end
  done;
  let last = Buffer.contents buf in
  List.rev (if String.trim last = "" then !acc else last :: !acc)

(** Custom extraction syntax placeholder types for template string substitution.
*)
type custom_case =
  | CCscrut
  | CCty
  | CCbody of int
  | CCty_arg of int
  | CCbr_var of int * int
  | CCbr_var_ty of int * int
  | CCstring of string
  | CCarg of int

(** Test whether a character is an ASCII digit. *)
let is_digit c = c >= '0' && c <= '9'

(** Parses an integer starting at [i], returns (value, next_index) *)
let parse_number s i n =
  let rec aux j = if j < n && is_digit s.[j] then aux (j + 1) else j in
  let j = aux i in
  if j = i then
    None
  else
    let num_str = String.sub s i (j - i) in
    Some (int_of_string num_str, j)

(* The following functions parse custom placeholders in extraction syntax
   strings: - parse_custom_fixed: parses fixed placeholders like %scrut or %ty -
   parse_numbered_args: parses placeholders like %a0, %t12 (single argument) -
   parse_custom_numbered_binders: parses placeholders like %b0a1, %b10a20 (two
   arguments) *)

(** Parses fixed custom placeholders like [%scrut] or [%ty] in a custom
    extraction syntax string. Returns a list of {!custom_case} chunks. *)
let parse_custom_fixed esc cc s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start chunks_rev =
    if i >= n then
      let last_chunk = String.sub s start (n - start) in
      List.rev (CCstring last_chunk :: chunks_rev)
    else
      match
        (s.[i], i + esc_len + 1 <= n)
      with
      | '%', true ->
        if esc = String.sub s (i + 1) esc_len then
          let chunk = String.sub s start (i - start) in
          aux
            (i + esc_len + 1)
            (i + esc_len + 1)
            (cc :: CCstring chunk :: chunks_rev)
        else
          aux (i + 1) start chunks_rev
      | _ -> aux (i + 1) start chunks_rev
  in
  aux 0 0 []

(** Parses single-argument custom placeholders like %a0, %t12 *)
let parse_numbered_args esc f s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start acc =
    if i >= n then
      List.rev
        ( if start < n then
            CCstring (String.sub s start (n - start)) :: acc
          else
            acc )
    else if s.[i] = '%' && i + esc_len < n && String.sub s (i + 1) esc_len = esc
    then
      match
        parse_number s (i + 1 + esc_len) n
      with
      | Some (idx, j) ->
        let chunk = String.sub s start (i - start) in
        aux j j (f idx :: CCstring chunk :: acc)
      | None -> aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

(** Parses double-argument custom placeholders like %b0a1, %b10a20 *)
let parse_custom_numbered_binders esc1 esc2 f s =
  let n = String.length s in
  let len1 = String.length esc1 in
  let len2 = String.length esc2 in
  let rec aux i start acc =
    if i >= n then
      List.rev
        ( if start < n then
            CCstring (String.sub s start (n - start)) :: acc
          else
            acc )
    else if s.[i] = '%' && i + len1 < n && String.sub s (i + 1) len1 = esc1 then
      match
        parse_number s (i + 1 + len1) n
      with
      | Some (idx1, j) when j + len2 <= n && String.sub s j len2 = esc2 ->
        ( match parse_number s (j + len2) n with
        | Some (idx2, k) ->
          let chunk = String.sub s start (i - start) in
          aux k k (f idx1 idx2 :: CCstring chunk :: acc)
        | None -> aux (i + 1) start acc )
      | _ -> aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

(** Expand placeholders in a command list using a parser function.
    For each [CCstring] chunk, apply [parser] to produce new chunks.
    Non-string chunks are passed through unchanged. *)
let expand_custom_chunks parser cmds =
  List.fold_left
    (fun prev curr ->
      match curr with
      | CCstring s -> prev @ parser s
      | _ -> prev @ [curr] )
    []
    cmds

let expand_numbered_args esc f = expand_custom_chunks (parse_numbered_args esc f)
let expand_custom_binders esc1 esc2 f = expand_custom_chunks (parse_custom_numbered_binders esc1 esc2 f)
let expand_custom_fixed esc cc = expand_custom_chunks (parse_custom_fixed esc cc)

(** Flatten a command list that is known to contain only [CCstring] chunks
    back into a single string. *)
let flatten_custom_strings cmds =
  String.concat ""
    (List.map (function CCstring s -> s | _ -> assert false) cmds)

(** Get the number of template type parameters for an inductive reference,
    defaulting to 2 when unavailable. *)
let num_ind_params = function
  | GlobRef.IndRef (kn, _) ->
    (match Table.get_ind_num_param_vars_opt kn with
     | Some n -> n | None -> 2)
  | _ -> 2

(** Generate N placeholder type arguments (comma-separated ["int"]s). *)
let gen_placeholder_args n =
  String.concat ", " (List.init n (fun _ -> "int"))

(** Insert ["template "] before the last [::]-separated component of a
    qualified name.  E.g. ["C::foo"] becomes ["C::template foo"].
    Returns [name_pp] unchanged if the string contains no [:]. *)
let insert_template_keyword name_pp name_str =
  if String.contains name_str ':' then
    let last_colon_pos = String.rindex name_str ':' in
    let before = String.sub name_str 0 (last_colon_pos + 1) in
    let after =
      String.sub name_str (last_colon_pos + 1)
        (String.length name_str - last_colon_pos - 1)
    in
    str before ++ str "template " ++ str after
  else
    name_pp

(** Print a type variable by de Bruijn index, looking up in [vl]. Falls back to
    [T<n>] if index is out of range. *)
let print_cpp_type_var vl i =
  try pp_tvar (List.nth vl (pred i)) with Failure _ -> str "T" ++ int i

(** Set of parameter IDs whose C++ type is [Tany] (std::any) in the
    current method being printed.  Set before printing a method body,
    cleared after. *)
let current_any_typed_params : Id.Set.t ref = ref Id.Set.empty

(** Pretty-print a MiniCpp type as C++ source. [par] controls whether
    parentheses are added around the result. [vl] is the list of type variable
    names for de Bruijn lookup. *)
let rec pp_cpp_type par vl t =
  let rec pp_rec par = function
    | Tvar (i, None) -> print_cpp_type_var vl i
    | Tvar (1000, Some id) ->
      (* PROMOTED TYPE VARIABLES: Record fields that were promoted from value-level
         to type-level during concept generation (e.g., [m_carrier] from [Monoid],
         [Obj]/[Hom] from [PreCategory]).

         These Type-valued fields cannot exist as struct members in C++, so they
         become type requirements in concepts and "using" declarations in structs.

         The special index 1000 distinguishes promoted vars from:
         - Regular type params: Tvar(0/1/2, Some name) from generic functions
         - Local loopification types: Tvar(0, Some "_Frame") from loop transforms

         Context-dependent rendering:
         - Inside struct (header): "Obj" → resolves via [using Obj = std::any;]
         - Outside struct (.cpp file): "Obj" → "StructName::Obj" (qualified access)

         Example:
           In struct:  using Obj = std::any;
           In .cpp:    DepRecord::Obj my_var = ...;  *)
      ( match render_ctx.rc_struct_name with
      | Some struct_name when not render_ctx.rc_in_struct ->
        struct_name ++ str "::" ++ Id.print id
      | _ -> Id.print id )
    | Tvar (_, Some id) -> Id.print id
    (* Tid for local type references (e.g., nested structs inside modules).
       These don't need GlobRef qualification, just simple Id references. Can be
       parameterized like generic types: Leaf<int>. When generating
       out-of-struct definitions, prepend struct name. *)
    | Tid (id, []) ->
      ( match render_ctx.rc_struct_name with
      | Some struct_name when not render_ctx.rc_in_struct ->
        struct_name ++ str "::" ++ Id.print id
      | _ -> Id.print id )
    | Tid (id, args) ->
      ( match render_ctx.rc_struct_name with
      | Some struct_name when not render_ctx.rc_in_struct ->
        struct_name
        ++ str "::"
        ++ Id.print id
        ++ str "<"
        ++ pp_list (pp_rec false) args
        ++ str ">"
      | _ -> Id.print id ++ str "<" ++ pp_list (pp_rec false) args ++ str ">" )
    | Tid_external (id, []) -> Id.print id
    | Tid_external (id, args) ->
      Id.print id ++ str "<" ++ pp_list (pp_rec false) args ++ str ">"
    | Tglob (r, tys, args) ->
      (* Erased type/prop/implicit markers (from Tdummy in the ML AST) should
         never reach the C++ output. When they do survive — e.g. as a template
         argument of SigT<nat, dummy_prop> — render them as std::any. *)
      ( match r with
      | GlobRef.VarRef id
        when let name = Id.to_string id in
             name = "dummy_type"
             || name = "dummy_prop"
             || name = "dummy_implicit" ->
        require_header "any";
        str "std::any"
      | _ ->
      match find_custom_opt r with
      | Some s when to_inline r ->
        let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
        let cmds = expand_numbered_args "t" (fun i -> CCty_arg i) cmds in
        pp_custom
          (Pp.string_of_ppcmds (GlobRef.print r) ^ " := " ^ s)
          (empty_env ())
          None
          None
          tys
          []
          args
          []
          vl
          cmds
      | _ ->
        (* Non-custom cases *)
        let type_name = pp_inductive_type_name_cached r in
        let name_str = Pp.string_of_ppcmds type_name in
        ( match tys with
        | [] ->
          typename_prefix_for name_str
          ++ struct_qualifier_for r name_str
          ++ type_name
        | l ->
          (* When type_name contains :: (qualified name like "C::t"), we need to
             insert "template " before the last component for dependent
             templates. E.g., "C::t" + <unsigned int> -> "C::template t<unsigned
             int>" *)
          let type_name_with_template =
            insert_template_keyword type_name name_str
          in
          typename_prefix_for name_str
          ++ struct_qualifier_for r name_str
          ++ type_name_with_template
          ++ str "<"
          ++ pp_list (pp_rec false) l
          ++ str ">" ) )
    | Tfun (d, c) ->
      require_header "functional";
      std_angle
        "function"
        (pp_rec false c ++ pp_par true (pp_list (pp_rec false) d))
    | Tref t -> pp_rec false t ++ str "&"
    | Tptr t -> pp_rec false t ++ str "*"
    | Tmod (m, t) -> pp_tymod m ++ pp_rec false t
    | Tnamespace (r, t) ->
      (* DESIGN: Namespace-qualified types for inductive types. Rocq's
         inductives live in wrapper structs (e.g., type 'list' in struct
         'List'). Local inductives don't need namespace wrapping; non-local ones
         get the prefix. EXCEPTION: Eponymous records are merged into the module
         struct, so we use just the capitalized name without namespace
         qualification (CHT, not CHT::cHT). *)
      let name, _needs_ns = inductive_name_info_cached r in
      ( match (r, t) with
      | GlobRef.IndRef _, Tglob (r', args, _)
        when Environ.QGlobRef.equal Environ.empty_env r r' ->
        let templates =
          match args with
          | [] -> mt ()
          | args -> str "<" ++ pp_list (pp_rec false) args ++ str ">"
        in
        (* Skip prefix if type name already contains module path (::) *)
        let type_name_str = str_global Type r' in
        (* Check eponymous record FIRST because they can also be local *)
        if is_eponymous_record_cached r' then
          (* Eponymous record: use capitalized name directly, no namespace
             nesting. *)
          str (Common.pp_type_name_capitalized r') ++ templates
        else if is_enum_cached r' then
          (* Enum types at global scope need no struct qualification. Enums
             inside structs (e.g., Comparison::cmp) need it. *)
          let qualifier =
            match render_ctx.rc_struct_name with
            | Some struct_name when not render_ctx.rc_in_struct ->
              if is_global_scope_enum_cached r' then
                mt ()
              else
                let full_path = Pp.string_of_ppcmds (GlobRef.print r') in
                let struct_name_str = Pp.string_of_ppcmds struct_name in
                let struct_name_dotted =
                  Str.global_replace
                    (Str.regexp_string "::")
                    "."
                    struct_name_str
                in
                if Common.contains_substring full_path struct_name_dotted then
                  struct_name ++ str "::"
                else
                  mt ()
            | _ -> mt ()
          in
          qualifier
          ++ str (capitalize_enum_qualified type_name_str r')
          ++ templates
        else if is_qualified_name type_name_str then
          (* Already qualified (e.g., C::t from module parameter): add typename
             if in template *)
          typename_prefix_for type_name_str ++ str type_name_str ++ templates
        else if is_merged_inductive_cached r' then
          (* Merged: use capitalized name directly *)
          name ++ templates
        else (* Unmerged: use Wrapper::inner<args> *)
          name ++ str "::" ++ str type_name_str ++ templates
      | _ ->
        (* Fallback: generic namespace-qualified type *)
        str "typename " ++ name ++ str "::" ++ pp_rec false t )
    | Tqualified (base_ty, nested_id) ->
      (* DESIGN: Template-dependent type access like 'typename M::Key::t'.
         C++ templates require 'typename' to access nested types from
         dependent base types.  Nested Tqualified chains (e.g.,
         [Tqualified(Tqualified(Tvar I, base_category), Obj)]) are flattened
         so only a single leading [typename] is emitted — writing
         [typename typename I::base_category::Obj] is invalid C++. *)
      let rec pp_qualified_chain ty =
        match ty with
        | Tqualified (inner_ty, id) ->
          pp_qualified_chain inner_ty ++ str "::" ++ Id.print id
        | Tglob (r, _, _) ->
          let type_name_str = str_global Type r in
          if is_qualified_name type_name_str then
            pp_rec false ty
          else
            let ns_name, needs_ns = inductive_name_info_cached r in
            if needs_ns && not (is_merged_inductive_cached r) then
              ns_name ++ str "::" ++ pp_rec false ty
            else
              pp_rec false ty
        | _ -> pp_rec false ty
      in
      str "typename " ++ pp_qualified_chain base_ty ++ str "::" ++ Id.print nested_id
    | Tvariant tys ->
      require_header "variant";
      std_angle "variant" (pp_list (pp_rec false) tys)
    | Tshared_ptr t ->
      require_header "memory";
      cpp_angle (sn ()).shared_ptr (pp_rec false t)
    | Tunique_ptr t ->
      require_header "memory";
      cpp_angle (sn ()).unique_ptr (pp_rec false t)
    | Tvoid -> str "void"
    | Ttodo -> str "auto"
    | Tunknown -> str "UNKNOWN"
    | Tany ->
      require_header "any";
      str "std::any"
    | Tauto -> str "auto"
    | Tdecltype e ->
      (* Print decltype(expr) where expr has been rewritten by
         rewrite_field_access_for_decltype to use std::declval. *)
      str "decltype(" ++ pp_cpp_expr ([], Id.Set.empty) [] e ++ str ")"
  in
  h (pp_rec par t)

(** Pretty-print a MiniCpp expression as C++ source. [env] is the de Bruijn
    variable name environment. [args] is the list of accumulated arguments (for
    partial application). *)
and pp_cpp_expr env args t =
  let apply st = pp_apply_cpp st args in
  (* Generate an IIFE wrapper for a block template (%result) in expression
     position.  [ref_name] is for debug labels, [custom] is the raw template
     string, [tys] are type args, [val_args] are value args (already reversed
     for pp_custom). *)
  let gen_block_iife ref_name custom tys val_args =
    let ret_ty =
      try
        let ml_ty = Table.find_type ref_name in
        Translation.convert_ml_type_to_cpp_type
          env Refset'.empty [] (Translation.ml_codomain ml_ty)
      with _ -> Tauto
    in
    let result_str = "_r" in
    let substituted =
      flatten_custom_strings
        (parse_custom_fixed "result" (CCstring result_str) custom)
    in
    let cmds = parse_numbered_args "a" (fun i -> CCarg i) substituted in
    let cmds = expand_numbered_args "t" (fun i -> CCty_arg i) cmds in
    let body_pp =
      pp_custom
        (Pp.string_of_ppcmds (GlobRef.print ref_name) ^ " := " ^ custom)
        env None None tys [] val_args [] [] cmds
    in
    let body_str = Pp.string_of_ppcmds body_pp in
    let stmts =
      List.filter (fun s -> String.trim s <> "")
        (split_on_semicolons body_str)
    in
    let stmt_lines =
      String.concat "\n"
        (List.map (fun s -> "  " ^ String.trim s ^ ";") stmts)
    in
    str "[]() -> " ++ pp_cpp_type false [] ret_ty ++ str " {"
    ++ fnl ()
    ++ str ("  " ^ Pp.string_of_ppcmds (pp_cpp_type false [] ret_ty)
            ^ " " ^ result_str ^ ";")
    ++ fnl ()
    ++ str stmt_lines
    ++ fnl ()
    ++ str ("  return " ^ result_str ^ ";")
    ++ fnl ()
    ++ str "}()"
  in
  match t with
  | CPPvar id -> Id.print id
  | CPPglob (x, tys, Some ci) when ci.ci_inline <> None ->
    let custom = Option.get ci.ci_inline in
    if Common.contains_substring custom "%result" then
      gen_block_iife x custom tys []
    else
    let cmds = parse_numbered_args "t" (fun i -> CCty_arg i) custom in
    pp_custom
      (Pp.string_of_ppcmds (GlobRef.print x) ^ " := " ^ custom)
      env
      None
      None
      tys
      []
      []
      []
      []
      cmds
  | CPPglob (x, _tys, _)
    when lookup_method_this_pos x <> None
         &&
         match is_registered_method x with
         | Some (epon_ref, _) ->
           (* Only use this-> for methods belonging to the current struct. Check
              if the method's eponymous type name matches current_struct_name.
              This prevents e.g. SigT::projT1 from being rendered as
              this->projT1() when generating code inside a different struct like
              Levenshtein. *)
           ( match render_ctx.rc_struct_name with
           | Some sn ->
             let epon_name = Common.pp_global_name Type epon_ref in
             let sn_str = Pp.string_of_ppcmds sn in
             String.equal (String.capitalize_ascii epon_name) sn_str
           | None -> true )
         | None -> true ->
    (* A bare reference to a method on the same struct (eta-reduced from \self.
       method self). Generate this->method() - a call to the method via this,
       not a function pointer. *)
    let method_name = Id.of_string (Common.pp_global_name Term x) in
    str "this->" ++ Id.print method_name ++ str "()"
  | CPPglob (x, _tys, _)
    when lookup_method_this_pos x <> None
         &&
         match is_registered_method x with
         | Some (epon_ref, _) ->
           (* Bare reference to a method on a DIFFERENT struct (used as a
              function value). Since C++ non-static member functions can't be
              passed as function pointers, wrap in a lambda that calls the
              method on its argument. *)
           ( match render_ctx.rc_struct_name with
           | Some sn ->
             let epon_name = Common.pp_global_name Type epon_ref in
             let sn_str = Pp.string_of_ppcmds sn in
             not (String.equal (String.capitalize_ascii epon_name) sn_str)
           | None -> false )
         | None -> false ->
    let method_name = Id.of_string (Common.pp_global_name Term x) in
    str "[](const auto &_x) { return _x->"
    ++ Id.print method_name
    ++ str "(); }"
  | CPPglob (x, tys, _) ->
    (* Determine the base name for a global reference *)
    let base_name =
      match x with
      | GlobRef.IndRef _ ->
        let ns_name, needs_ns = inductive_name_info_cached x in
        let type_name_str = str_global Type x in
        (* Check eponymous record FIRST because they can also be local *)
        if is_eponymous_record_cached x then
          (* Eponymous record: use capitalized name (merged into module
             struct). *)
          str (Common.pp_type_name_capitalized x)
        else if Hashtbl.mem promoted_inductives x then
          (* Promoted inductive: use capitalized name directly *)
          str (String.capitalize_ascii type_name_str)
        else if is_qualified_name type_name_str then
          (* Already qualified (e.g., C::t from module parameter): use as-is *)
          str type_name_str
        else if needs_ns then
          if is_merged_inductive_cached x then
            (* Merged non-local inductive: use capitalized name directly *)
            ns_name
          else (* Unmerged non-local inductive: Wrapper::inner *)
            ns_name ++ str "::" ++ str type_name_str
        else (* Local inductive: use original name directly *)
          str type_name_str
      | GlobRef.VarRef _ ->
        (* Local variable reference — no prefix *)
        pp_global Term x
      | _ ->
      (* Check if this function is inside an eponymous template struct. If so,
         type args go on the struct name, not the function name. *)
      match (get_containing_eponymous_struct x, tys) with
      | Some record_ref, _ :: _ ->
        (* Function inside eponymous template struct with type args: Generate
           StructName<int, ...>::template funcName<Args> for static methods. We
           use placeholder types for the struct and actual args for the
           method. *)
        let struct_name = Common.pp_global_name Type record_ref in
        let func_name = Common.pp_global_name Term x in
        let placeholder_args = gen_placeholder_args (num_ind_params record_ref) in
        let ty_args = pp_list (pp_cpp_type false []) tys in
        str (String.capitalize_ascii struct_name)
        ++ str "<"
        ++ str placeholder_args
        ++ str ">::template "
        ++ str func_name
        ++ str "<"
        ++ ty_args
        ++ str ">"
      | Some record_ref, [] ->
        let struct_name = Common.pp_global_name Type record_ref in
        let func_name = Common.pp_global_name Term x in
        let placeholder_args = gen_placeholder_args (num_ind_params record_ref) in
        str (String.capitalize_ascii struct_name)
        ++ str "<"
        ++ str placeholder_args
        ++ str ">::"
        ++ str func_name
      | None, _ ->
        (* Normal case: function not in eponymous struct *)
        let name = str_global Term x in
        let qualified_name = wrapper_qualify_name_cached x name in
        if qualified_name <> name then
          str qualified_name
        else if needs_global_qualifier x then
          str "::" ++ pp_global Term x
        else
          pp_global Term x
    in
    let is_accessor =
      let x_mp = modpath_of_r x in
      let x_lbl = label_of_r x in
      List.exists
        (fun (reg_mp, reg_lbl) ->
          Label.equal x_lbl reg_lbl
          && ( ModPath.equal x_mp reg_mp
             ||
             match Hashtbl.find_opt functor_app_sources x_mp with
             | Some source_mp -> ModPath.equal source_mp reg_mp
             | None -> false ) )
        !template_static_accessors
    in
    let full_name =
      match (tys, get_containing_eponymous_struct x) with
      | [], _ -> base_name
      | _, Some _ -> base_name
      | _ ->
        let ty_args = pp_list (pp_cpp_type false []) tys in
        (* Check if base_name contains :: (qualified name). If so, we need to
           insert "template " before the last component. E.g., "C::empty" +
           <unsigned int> -> "C::template empty<unsigned int>" *)
        let base_name_str = string_of_ppcmds base_name in
        insert_template_keyword base_name base_name_str
        ++ str "<" ++ ty_args ++ str ">"
    in
    let full_name = if is_accessor then full_name ++ str "()" else full_name in
    apply full_name
  | CPPnamespace (r, t) ->
    let name, _ = inductive_name_info_cached r in
    h (name ++ str "::" ++ pp_cpp_expr env args t)
  | CPPfun_call (CPPglob (n, tys, Some ci), ts) when ci.ci_inline <> None ->
    let s = Option.get ci.ci_inline in
    if Common.contains_substring s "%result" then
      gen_block_iife n s tys (List.rev ts)
    else
    let has_placeholder = String.contains s '%' in
    if not has_placeholder then
      let ty_args_s =
        match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
      in
      let args_s = pp_list (pp_cpp_expr env args) (List.rev ts) in
      str s ++ ty_args_s ++ str "(" ++ args_s ++ str ")"
    else
      let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
      let cmds = expand_numbered_args "t" (fun i -> CCty_arg i) cmds in
      let arg_types =
        try
          let ml_ty = Table.find_type n in
          let rec extract_arg_types = function
            | Miniml.Tarr (t1, t2) ->
              if Mlutil.isTdummy t1 then
                extract_arg_types t2
              else
                t1 :: extract_arg_types t2
            | _ -> []
          in
          let ml_arg_types = extract_arg_types ml_ty in
          List.map
            (Translation.convert_ml_type_to_cpp_type env Refset'.empty [])
            ml_arg_types
        with _ -> []
      in
      pp_custom
        (Pp.string_of_ppcmds (GlobRef.print n) ^ " := " ^ s)
        env
        None
        None
        tys
        []
        (List.rev ts)
        arg_types
        []
        cmds
  | CPPfun_call (CPPglob (n, tys, _), ts) when lookup_method_this_pos n <> None
    ->
    let method_name = Id.of_string (Common.pp_global_name Term n) in
    let this_pos =
      match lookup_method_this_pos n with
      | Some p -> p
      | None -> 0
    in
    let args_normal = List.rev ts in
    let this_arg_opt, other_args = Common.extract_at_pos this_pos args_normal in
    ( match this_arg_opt with
    | Some this_arg ->
      let obj_s = pp_cpp_expr env args this_arg in
      let args_s = pp_list (pp_cpp_expr env args) other_args in
      let ind_tvar_positions = lookup_method_ind_tvar_positions n in
      let filtered_tys =
        match tys with
        | [] -> []
        | _ ->
          List.filteri (fun i _ty -> not (List.mem i ind_tvar_positions)) tys
      in
      let template_kw, ty_args_s =
        match filtered_tys with
        | [] -> (mt (), mt ())
        | _ ->
          ( str "template ",
            str "<" ++ pp_list (pp_cpp_type false []) filtered_tys ++ str ">" )
      in
      obj_s
      ++ str "->"
      ++ template_kw
      ++ Id.print method_name
      ++ ty_args_s
      ++ str "("
      ++ args_s
      ++ str ")"
    | None -> pp_cpp_expr env args (CPPglob (n, tys, None)) ++ str "()" )
  | CPPfun_call (f, ts) ->
    let args_s = pp_list (pp_cpp_expr env args) (List.rev ts) in
    pp_cpp_expr env args f ++ str "(" ++ args_s ++ str ")"
  | CPPderef e -> str "*" ++ pp_cpp_expr env args e
  | CPPmove e ->
    require_header "utility";
    str (sn ()).move ++ str "(" ++ pp_cpp_expr env args e ++ str ")"
  | CPPforward (ty, e) ->
    str (sn ()).forward
    ++ str "<"
    ++ pp_cpp_type false [] ty
    ++ str ">("
    ++ pp_cpp_expr env args e
    ++ str ")"
  | CPPlambda (params, ret_ty, body, capture_by_value) ->
    let needs_capture, uses_this = lambda_needs_capture params body in
    let capture_str =
      if not needs_capture then
        str "[]("
      else if capture_by_value then
        if uses_this then str "[=, this](" else str "[=]("
      else
        str "[&]("
    in
    (* [=] lambdas need 'mutable' so captured variables aren't const-qualified.
       Without it, forwarding-reference parameters (F0&&) captured by value
       become const inside the lambda, preventing them from binding to F0&& in
       recursive calls. *)
    let mutable_str =
      if capture_by_value && needs_capture && not uses_this then
        str " mutable"
      else
        mt ()
    in
    let body_s = pp_list_stmt (pp_cpp_stmt env args) body in
    let params_s, capture =
      match params with
      | [] -> (mt (), capture_str)
      | _ ->
        ( pp_list
            (fun (ty, id_opt) ->
              match id_opt with
              | None -> pp_cpp_type false [] ty
              | Some id when not (stmts_reference_id id body) ->
                (* Unused parameter: omit the name entirely — the idiomatic
                   C++ way to signal an intentionally unused parameter. *)
                pp_cpp_type false [] ty
              | Some id ->
                pp_cpp_type false [] ty ++ spc () ++ Id.print id )
            (List.rev params),
          capture_str )
    in
    ( match ret_ty with
    | Some ty ->
      h
        ( capture
        ++ params_s
        ++ str ")"
        ++ mutable_str
        ++ str " -> "
        ++ pp_cpp_type false [] ty )
      ++ str " {"
      ++ fnl ()
      ++ body_s
      ++ fnl ()
      ++ str "}"
    | None ->
      h (capture ++ params_s ++ str ")" ++ mutable_str)
      ++ str " {"
      ++ fnl ()
      ++ body_s
      ++ fnl ()
      ++ str "}" )
  | CPPvisit ->
    require_header "variant";
    str (sn ()).visit
  | CPPmk_shared t ->
    require_header "memory";
    cpp_angle (sn ()).make_shared (pp_cpp_type false [] t)
  | CPPmk_unique t ->
    require_header "memory";
    cpp_angle (sn ()).make_unique (pp_cpp_type false [] t)
  | CPPoverloaded ls ->
    let ls_s = pp_list_newline (pp_cpp_expr env args) ls in
    str (sn ()).overloaded ++ str " {" ++ fnl () ++ ls_s ++ fnl () ++ str "}"
  | CPPstructmk (id, tys, es) ->
    let es_s = pp_list (pp_cpp_expr env args) es in
    let templates =
      match tys with
      | [] -> mt ()
      | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
    in
    let struct_name =
      match id with
      | GlobRef.IndRef _ when is_eponymous_record_cached id ->
        str (Common.pp_type_name_capitalized id)
      | _ -> pp_global Type id
    in
    struct_name ++ templates ++ str "::make(" ++ es_s ++ str ")"
  | CPPstruct (id, tys, es) ->
    let es_s = pp_list (pp_cpp_expr env args) es in
    let templates =
      match tys with
      | [] -> mt ()
      | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
    in
    let struct_name =
      match id with
      | GlobRef.IndRef _ when is_eponymous_record_cached id ->
        str (Common.pp_type_name_capitalized id)
      | _ -> pp_global Type id
    in
    struct_name ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPstruct_id (id, tys, es) ->
    let es_s = pp_list (pp_cpp_expr env args) es in
    let templates =
      match tys with
      | [] -> mt ()
      | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
    in
    Id.print id ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPget (e, id) -> pp_cpp_expr env args e ++ str "." ++ Id.print id
  | CPPget' (e, id) -> pp_cpp_expr env args e ++ str "->" ++ pp_global Type id
  | CPPstring s -> str ("\"" ^ Pstring.to_string s ^ "\"")
  | CPPparray (elems, _) ->
    str "{" ++ pp_list (pp_cpp_expr env args) (Array.to_list elems) ++ str "}"
  | CPPuint x ->
    let s = Uint63.to_string x in
    ( match
        try Some (Nametab.locate (Libnames.qualid_of_string "int"))
        with Not_found -> None
      with
    | Some gr when is_inline_custom gr ->
      ( match find_custom_opt gr with
      | Some cpp_type -> str (cpp_type ^ "(" ^ s ^ ")")
      | None -> str s )
    | _ -> str s )
  | CPPfloat f -> str (Printf.sprintf "%h" (Float64.to_float f))
  | CPPrequires (ty_vars, exprs, type_reqs) ->
    let ty_vars_s =
      match ty_vars with
      | [] -> mt ()
      | _ ->
        str "("
        ++ pp_list
             (fun (ty, id) -> pp_cpp_type false [] ty ++ spc () ++ Id.print id)
             ty_vars
        ++ str ") "
    in
    let type_reqs_s =
      prlist_with_sep
        fnl
        (fun ty -> str "  " ++ pp_cpp_type false [] ty ++ str ";")
        type_reqs
    in
    let exprs_s =
      prlist_with_sep
        fnl
        (fun (e1, e2) ->
          str "  { "
          ++ pp_cpp_expr env args e1
          ++ str " } -> "
          ++ pp_cpp_expr env args e2
          ++ str ";" )
        exprs
    in
    str "requires "
    ++ ty_vars_s
    ++ str "{"
    ++ fnl ()
    ++ type_reqs_s
    ++ ( if type_reqs <> [] && exprs <> [] then
           fnl ()
         else
           mt () )
    ++ exprs_s
    ++ fnl ()
    ++ str "}"
  | CPPnew (ty, exprs) ->
    str "new "
    ++ pp_cpp_type false [] ty
    ++ str "("
    ++ pp_list (pp_cpp_expr env args) exprs
    ++ str ")"
  | CPPshared_ptr_ctor (ty, expr) ->
    str (sn ()).shared_ptr
    ++ str "<"
    ++ pp_cpp_type false [] ty
    ++ str ">("
    ++ pp_cpp_expr env args expr
    ++ str ")"
  | CPPunique_ptr_ctor (ty, expr) ->
    str (sn ()).unique_ptr
    ++ str "<"
    ++ pp_cpp_type false [] ty
    ++ str ">("
    ++ pp_cpp_expr env args expr
    ++ str ")"
  | CPPthis -> str "this"
  | CPPshared_from_this ty ->
    str "std::const_pointer_cast<"
    ++ pp_cpp_type false [] ty
    ++ str ">(this->shared_from_this())"
  | CPPmember (e, id) ->
    (* Rewrite std::move(x).field → std::move(x.field): access the field
       first, then move its value.  This is semantically equivalent and:
       - Fixes Infer Use-After-Delete (moving a pointer then accessing it is flagged)
       - Enables the Unnecessary-Copy-Intermediate fix (field value is moved, not copied)
       For method calls we strip the move instead since methods need a live object. *)
    ( match e with
    | CPPmove inner ->
      str (sn ()).move ++ str "(" ++ pp_cpp_expr env args inner ++ str "." ++ Id.print id ++ str ")"
    | _ ->
      pp_cpp_expr env args e ++ str "." ++ Id.print id )
  | CPParrow (e, id) ->
    ( match e with
    | CPPmove inner ->
      (* std::move(ptr)->field → std::move(ptr->field) *)
      str (sn ()).move ++ str "(" ++ pp_cpp_expr env args inner ++ str "->" ++ Id.print id ++ str ")"
    | _ ->
      pp_cpp_expr env args e ++ str "->" ++ Id.print id )
  | CPPmethod_call (obj, method_name, call_args) ->
    let obj = match obj with CPPmove inner -> inner | _ -> obj in
    pp_cpp_expr env args obj
    ++ str "->"
    ++ Id.print method_name
    ++ str "("
    ++ pp_list (pp_cpp_expr env args) call_args
    ++ str ")"
  | CPPqualified (e, id) -> pp_cpp_expr env args e ++ str "::" ++ Id.print id
  | CPPconvertible_to ty ->
    require_header "concepts";
    str "std::convertible_to<" ++ pp_cpp_type false [] ty ++ str ">"
  | CPPabort msg ->
    str "([]() -> std::any { throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str msg
    ++ str "\"); return std::any{}; })()"
  | CPPenum_val (ind, ctor) ->
    (* Generate EnumType::Constructor for enum class values. Use str_global for
       proper module qualification, with collision-aware capitalization. *)
    let full_name = capitalize_enum_qualified (str_global Type ind) ind in
    str full_name ++ str "::" ++ Id.print ctor
  (* Low-level constructs for reuse optimization *)
  | CPPraw code -> str code
  | CPPbinop (op, lhs, rhs) ->
    (* Parenthesize && subexpressions inside || to avoid
       -Wlogical-op-parentheses warnings. *)
    let paren_child child =
      match child with
      | CPPbinop ("&&", _, _) when op = "||" ->
        str "(" ++ pp_cpp_expr env args child ++ str ")"
      | CPPbinop ("||", _, _) when op = "&&" ->
        str "(" ++ pp_cpp_expr env args child ++ str ")"
      | _ -> pp_cpp_expr env args child
    in
    paren_child lhs
    ++ str " "
    ++ str op
    ++ str " "
    ++ paren_child rhs
  | CPPbool b -> str (if b then "true" else "false")
  | CPPint n -> str (string_of_int n)
  | CPPbrace_init -> str "{}"
  | CPPunop (op, e) -> str op ++ pp_cpp_expr env args e
  | CPPany_cast (ty, e) ->
    require_header "any";
    str (sn ()).any_cast
    ++ str "<"
    ++ pp_cpp_type false [] ty
    ++ str ">("
    ++ pp_cpp_expr env args e
    ++ str ")"

(** Pretty-print a MiniCpp statement as C++ source. *)
and pp_cpp_stmt env args = function
  | Sreturn None -> str "return;"
  | Sreturn (Some (CPPabort msg)) ->
    str "throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str msg
    ++ str "\");"
  | Sreturn (Some e) ->
    (* Strip std::move from return statements — C++ applies implicit move
       on local variables in return statements.  Explicit std::move prevents
       NRVO (Named Return Value Optimization) and triggers
       -Wpessimizing-move / -Wredundant-move warnings. *)
    let e = match e with CPPmove inner -> inner | _ -> e in
    str "return " ++ pp_cpp_expr env args e ++ str ";"
  | Sdecl (id, ty) ->
    pp_cpp_type false [] ty ++ str " " ++ Id.print id ++ str ";"
  | Sasgn (id, Some ty, e) ->
    pp_cpp_type false [] ty
    ++ str " "
    ++ Id.print id
    ++ str " = "
    ++ pp_cpp_expr env args e
    ++ str ";"
  | Sasgn (id, None, e) ->
    Id.print id ++ str " = " ++ pp_cpp_expr env args e ++ str ";"
  | Sexpr e -> pp_cpp_expr env args e ++ str ";"
  | Sthrow msg ->
    require_header "stdexcept";
    str "throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str msg
    ++ str "\");"
  | Sswitch (scrut, ind, branches, default) ->
    (* Generate switch statement for enum class matching. Use pp_global_name to
       get the unqualified base name, capitalize to match enum class
       definition. *)
    let type_name = pp_inductive_type_name_cached ind in
    let pp_branch (ctor, stmts) =
      str "case "
      ++ type_name
      ++ str "::"
      ++ Id.print ctor
      ++ str ": {"
      ++ fnl ()
      ++ pp_list_stmt (pp_cpp_stmt env args) stmts
      ++ fnl ()
      ++ str "}"
    in
    require_header "utility";
    str "switch ("
    ++ pp_cpp_expr env args scrut
    ++ str ") {"
    ++ fnl ()
    ++ prlist_with_sep fnl pp_branch branches
    ++ fnl ()
    ++ ( match default with
       | Some stmts ->
         str "default: {"
         ++ fnl ()
         ++ pp_list_stmt (pp_cpp_stmt env args) stmts
         ++ fnl ()
         ++ str "}"
       | None ->
         str "default:"
         ++ fnl ()
         ++ str "  std::unreachable();" )
    ++ fnl ()
    ++ str "}"
  | Sassert (expr_str, comment_opt) ->
    require_header "cassert";
    ( match comment_opt with
    | Some c ->
      str "// Precondition: "
      ++ str c
      ++ fnl ()
      ++ str "assert("
      ++ str expr_str
      ++ str ");"
    | None -> str "assert(" ++ str expr_str ++ str ");" )
  (* Reuse optimization constructs *)
  | Sif (cond, then_stmts, else_stmts) ->
    str "if ("
    ++ pp_cpp_expr env args cond
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) then_stmts
    ++ fnl ()
    ++ str "} else {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) else_stmts
    ++ fnl ()
    ++ str "}"
  | Sraw code ->
    if Common.contains_substring code "std::vector" then
      require_header "vector";
    str code
  | Sstruct_def (name, fields) ->
    str "struct "
    ++ Id.print name
    ++ str " { "
    ++ prlist_with_sep mt
         (fun (fid, ty) ->
           pp_cpp_type false [] ty ++ str " " ++ Id.print fid ++ str "; ")
         fields
    ++ str "};"
  | Susing (name, ty) ->
    str "using " ++ Id.print name ++ str " = " ++ pp_cpp_type false [] ty ++ str ";"
  | Sdecl_init (id, ty) ->
    pp_cpp_type false [] ty ++ str " " ++ Id.print id ++ str "{};"
  | Swhile (cond, body) ->
    str "while ("
    ++ pp_cpp_expr env args cond
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) body
    ++ fnl ()
    ++ str "}"
  | Sblock stmts ->
    str "{"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) stmts
    ++ fnl ()
    ++ str "}"
  | Scontinue -> str "continue;"
  | Sbreak -> str "break;"
  | Sassign_field (obj, field, e) ->
    pp_cpp_expr env args obj
    ++ str "."
    ++ Id.print field
    ++ str " = "
    ++ pp_cpp_expr env args e
    ++ str ";"
  | Sblock_custom (_ref, tmpl, result_var, result_ty, args, tyargs) ->
    (* Block template: emit a declaration + template-substituted statements.
       %result → result_var, %aN → value args, %tN → type args *)
    let result_str = Pp.string_of_ppcmds (Id.print result_var) in
    (* Substitute %result first *)
    let flat =
      flatten_custom_strings
        (parse_custom_fixed "result" (CCstring result_str) tmpl)
    in
    let cmds = parse_numbered_args "a" (fun i -> CCarg i) flat in
    let cmds = expand_numbered_args "t" (fun i -> CCty_arg i) cmds in
    (* Render: type declaration + template body as statements *)
    let decl_pp =
      pp_cpp_type false [] result_ty
      ++ str " "
      ++ Id.print result_var
      ++ str ";"
    in
    let body_pp =
      pp_custom
        ("block custom " ^ Pp.string_of_ppcmds (GlobRef.print _ref))
        env None None tyargs [] args [] [] cmds
    in
    (* Split rendered body by ';' and emit each as a statement line *)
    let body_str = Pp.string_of_ppcmds body_pp in
    let stmts =
      List.filter
        (fun s -> String.trim s <> "")
        (split_on_semicolons body_str)
    in
    let stmt_pps =
      List.map (fun s -> str (String.trim s) ++ str ";") stmts
    in
    prlist_with_sep fnl (fun x -> x) (decl_pp :: stmt_pps)
  | Scustom_case (typ, t, tyargs, cases, cmatch) ->
    (* When the template uses %scrut more than once and the scrutinee is a
       non-trivial expression (e.g., a function call), cache it in a temporary
       to avoid double evaluation. This fixes Infer OPTIONAL_EMPTY_ACCESS
       false positives where the same optional-returning call appears in both
       the has_value() check and the dereference. *)
    let scrut_uses =
      let plen = 6 in
      let n = String.length cmatch in
      let rec count i acc =
        if i + plen > n then acc
        else if String.sub cmatch i plen = "%scrut" then count (i + plen) (acc + 1)
        else count (i + 1) acc
      in
      count 0 0
    in
    let t, cache_decl_opt =
      if scrut_uses > 1 then
        match t with
        | CPPvar _ | CPPget _ | CPPget' _ | CPParrow _ | CPPmember _
        | CPPqualified _ | CPPderef _ | CPPenum_val _ | CPPglob _ -> (t, None)
        | _ ->
          let cache_id = Id.of_string "_cs" in
          let cache_var = CPPvar cache_id in
          let decl = Sasgn (cache_id, Some Ttodo, t) in
          (cache_var, Some decl)
      else (t, None)
    in
    let cmds = parse_custom_fixed "scrut" CCscrut cmatch in
    let cmds = expand_custom_fixed "ty" CCty cmds in
    let cmds = expand_numbered_args "t" (fun i -> CCty_arg i) cmds in
    let cmds = expand_numbered_args "br" (fun i -> CCbody i) cmds in
    let cmds = expand_custom_binders "b" "a" (fun i j -> CCbr_var (i, j)) cmds in
    let cmds = expand_custom_binders "b" "t" (fun i j -> CCbr_var_ty (i, j)) cmds in
    let case_pp =
      pp_custom
        ( "custom match for "
        ^ Pp.string_of_ppcmds (pp_cpp_type false [] typ)
        ^ " := "
        ^ cmatch )
        env
        (Some typ)
        (Some t)
        tyargs
        cases
        []
        []
        []
        cmds
    in
    ( match cache_decl_opt with
    | None -> case_pp
    | Some decl ->
      pp_cpp_stmt env [] decl ++ fnl () ++ case_pp )
  | Smatch (branches, default) ->
    require_header "variant";
    (* Print an if/else-if chain using [std::holds_alternative] for
       discrimination, then structured bindings via [std::get]:

         if (std::holds_alternative<Ctor>(_sv->v())) {
           const auto& [d_f0, d_f1] = std::get<Ctor>(_sv->v());
           body
         }

       Structured bindings ([smb_field_bindings] non-empty) decompose the
       constructor struct into individual field variables.  The binding
       names come from the Rocq constructor field names (with numeric
       suffixes for nested matches to avoid shadowing).

       Frame-dispatch branches ([smb_field_bindings] empty, [smb_var = Some _f])
       use a single aggregate binding:
         [const auto& _f = std::get<FrameType>(_fsv);]

       Branches without a binding ([smb_var = None]) emit no binding.

       The scrutinee is evaluated once and stored in [auto&&] to prevent
       re-evaluation and to keep temporaries alive across branches.

       The last explicit branch before [None] default (= exhaustive match
       without wildcard) uses plain [else] — the discriminant check is
       redundant since Rocq guarantees exhaustiveness.

       Single-constructor exhaustive matches (one branch, no wildcard)
       emit just the binding + body inline — no if/else needed. *)
    let n_branches = List.length branches in
    let pp_scrut = pp_cpp_expr env args in
    (* Derive a unique scrutinee variable name from the first branch's binding
       variable, so that two Smatch nodes in the same scope never redeclare the
       same scrutinee name — no block-scoping is needed. *)
    let sv_name =
      match List.find_opt (fun br -> br.smb_var <> None) branches with
      | Some { smb_var = Some id; _ } ->
        let s = Id.to_string id in
        let strip_prefix p =
          let n = String.length p in
          if String.length s >= n && String.sub s 0 n = p
          then Some (String.sub s n (String.length s - n))
          else None
        in
        ( match strip_prefix "_m" with
        | Some suffix -> "_sv" ^ suffix
        | None ->
          match strip_prefix "_f" with
          | Some suffix -> "_fsv" ^ suffix
          | None -> "_sv" )
      | _ -> "_sv"
    in
    (* Helper: [std::holds_alternative<Ctor>(scrut)]. *)
    let pp_holds scrut_var_pp br =
      str (sn ()).holds_alternative ++ str "<"
      ++ pp_cpp_type false [] br.smb_ctor_type ++ str ">("
      ++ scrut_var_pp ++ str ")"
    in
    (* Helper: binding statement inside the if-block.
       - Structured bindings: [const auto& [f1, f2] = std::get<T>(scrut);]
       - Frame dispatch (no field bindings): [const auto& _f = std::get<T>(scrut);]
       - No binding: empty. *)
    let pp_block_binding scrut_var_pp br =
      match br.smb_field_bindings with
      | _ :: _ ->
        str "const auto& ["
        ++ prlist_with_sep (fun () -> str ", ")
             (fun (bname, _ty, _used) -> Id.print bname)
             br.smb_field_bindings
        ++ str "] = " ++ str (sn ()).get ++ str "<"
        ++ pp_cpp_type false [] br.smb_ctor_type ++ str ">("
        ++ scrut_var_pp ++ str ");"
      | [] ->
        ( match br.smb_var with
        | Some var_id ->
          str "const auto& " ++ Id.print var_id
          ++ str " = " ++ str (sn ()).get ++ str "<"
          ++ pp_cpp_type false [] br.smb_ctor_type ++ str ">("
          ++ scrut_var_pp ++ str ");"
        | None -> mt () )
    in
    (* Extract the scrutinee object expression from [CPPmethod_call(obj, "v", [])].
       Bind it with [auto&&] to extend any temporary's lifetime, then
       reconstruct the variant accessor as [_svN->v()].
       Falls back to the raw scrutinee expression when the pattern doesn't match. *)
    let first_scrut = (List.hd branches).smb_scrutinee in
    let scrut_obj_opt =
      match first_scrut with
      | CPPmethod_call (obj, v_id, []) when Id.to_string v_id = "v" ->
        Some obj
      | _ -> None
    in
    let scrut_binding_pp, scrut_var_pp, scrut_obj_pp =
      match scrut_obj_opt with
      | Some (CPPvar id) ->
        let name = Id.to_string id in
        (mt (), str (name ^ "->v()"), str name)
      | Some CPPthis ->
        (mt (), str "this->v()", str "(*this)")
      | Some obj_expr ->
        let obj_pp = pp_scrut obj_expr in
        ( str ("auto&& " ^ sv_name ^ " = ") ++ obj_pp ++ str ";" ++ fnl (),
          str (sv_name ^ "->v()"), str sv_name )
      | None ->
        ( match first_scrut with
        | CPPvar id ->
          let name = Id.to_string id in
          (mt (), str name, str name)
        | _ ->
          let raw_pp = pp_scrut first_scrut in
          ( str ("const auto& " ^ sv_name ^ " = ") ++ raw_pp ++ str ";" ++ fnl (),
            str sv_name, str sv_name ) )
    in
    if n_branches = 1 && default = None then
      (* Single-constructor exhaustive match: emit binding + body inline.
         No if/else needed. *)
      let br = List.hd branches in
      let body_pp = pp_list_stmt (pp_cpp_stmt env args) br.smb_body in
      let binding = pp_block_binding scrut_var_pp br in
      if binding = mt () then body_pp
      else scrut_binding_pp ++ binding ++ fnl () ++ body_pp
    else
    let pp_branch i br =
      let keyword = if i = 0 then "if" else "} else if" in
      let is_last_no_wild =
        i = n_branches - 1 && default = None && n_branches > 1
      in
      let normal_body_pp = pp_list_stmt (pp_cpp_stmt env args) br.smb_body in
      let binding = pp_block_binding scrut_var_pp br in
      (* When the branch has a reuse fast-path, nest the use_count check
         inside the holds_alternative block:
           if (holds_alternative<Ctor>(scrut)) {
             if (use_count_cond) { reuse_body }
             else { bindings; normal_body }
           } *)
      let body_pp =
        match br.smb_reuse with
        | Some (cond, rf_var, reuse_body) ->
          let rf_binding = match rf_var with
            | Some id ->
              str "auto& " ++ Id.print id ++ str " = "
              ++ str (sn ()).get ++ str "<"
              ++ pp_cpp_type false [] br.smb_ctor_type ++ str ">("
              ++ scrut_obj_pp ++ str "->v_mut());" ++ fnl ()
            | None -> mt ()
          in
          let reuse_pp = pp_list_stmt (pp_cpp_stmt env args) reuse_body in
          str "if (" ++ pp_cpp_expr env args cond ++ str ") {"
          ++ fnl () ++ rf_binding ++ reuse_pp
          ++ str "} else {" ++ fnl ()
          ++ ( if binding = mt () then mt ()
               else binding ++ fnl () )
          ++ normal_body_pp
          ++ str "}" ++ fnl ()
        | None ->
          ( if binding = mt () then mt ()
            else binding ++ fnl () )
          ++ normal_body_pp
      in
      if is_last_no_wild then
        str "} else {" ++ fnl () ++ body_pp
      else
        let holds_pp = pp_holds scrut_var_pp br in
        let cond_pp =
          match br.smb_extra_conds with
          | [] -> holds_pp
          | conds ->
            let conds_pp =
              prlist_with_sep
                (fun () -> str " && ")
                (pp_cpp_expr env args)
                conds
            in
            holds_pp ++ str " && " ++ conds_pp
        in
        str keyword ++ str " (" ++ cond_pp ++ str ") {"
        ++ fnl () ++ body_pp
    in
    let branches_pp =
      scrut_binding_pp
      ++ prlist_with_sep fnl (fun (i, br) -> pp_branch i br)
           (List.mapi (fun i br -> (i, br)) branches)
    in
    let default_pp =
      match default with
      | Some stmts ->
        fnl () ++ str "} else {"
        ++ fnl () ++ pp_list_stmt (pp_cpp_stmt env args) stmts
      | None when branches = [] ->
        str "std::unreachable();"
      | None ->
        mt ()
    in
    branches_pp ++ default_pp ++ fnl () ++ str "}"

(** Check if a return type is eligible for __attribute__((pure)). Types that
    involve allocation (shared_ptr, unique_ptr), side effects (void), or are
    unknown at definition time (type variables, any, todo) are excluded. Axiom
    type refs are also excluded since functions operating on axiom types may
    transitively call axiom stubs that throw std::logic_error. *)
and is_pure_return_type = function
  | Tshared_ptr _ | Tunique_ptr _ -> false
  | Tvoid | Tvar _ | Tany | Tauto | Ttodo | Tunknown -> false
  | Tglob (r, _, _) when is_axiom_type_ref r -> false
  | Tmod (_, t) | Tref t | Tptr t -> is_pure_return_type t
  | _ -> true

(** Check if a C++ type is a literal type eligible for [constexpr] context.

    Strictly stronger than {!is_pure_return_type}: in addition to the same
    exclusions (allocation, side-effects, unknowns), also rejects:
    - [Tfun]: [std::function] uses type-erased internal storage
    - [Tdecltype]: the expression may reference non-constexpr entities
    - Composite types where any component is non-literal

    The check is recursive for container types ([Tvariant], [Tglob], [Tid],
    [Tnamespace], [Tqualified]) — a [std::variant<A, B>] is constexpr only
    if both [A] and [B] are. *)
and is_constexpr_type = function
  | Tshared_ptr _ | Tunique_ptr _ -> false
  | Tvoid | Tvar _ | Tany | Tauto | Ttodo | Tunknown -> false
  | Tfun _ -> false  (* std::function uses type erasure *)
  | Tdecltype _ -> false
  | Tglob (r, _, _) when is_axiom_type_ref r -> false
  | Tmod (_, t) | Tref t | Tptr t -> is_constexpr_type t
  | Tvariant tys -> List.for_all is_constexpr_type tys
  | Tglob (_, tys, _) -> List.for_all is_constexpr_type tys
  | Tid (_, tys) | Tid_external (_, tys) -> List.for_all is_constexpr_type tys
  | Tnamespace (_, t) -> is_constexpr_type t
  | Tqualified (t, _) -> is_constexpr_type t

(** Check if a function is constexpr-eligible: all param types AND return
    type must be constexpr-eligible literal types. *)
and is_constexpr_eligible ret_ty params =
  is_constexpr_type ret_ty
  && List.for_all (fun (_, ty) -> is_constexpr_type ty) params

(** Check if a function body consists solely of throwing an abort/axiom error.
    Such functions must not be marked [pure] or [constexpr] because the compiler
    may optimise away the throw. *)
and body_is_throw = function
  | [Sreturn (Some (CPPabort _))] -> true
  | _ -> false

(** Compute the C++ function qualifier prefix as a three-way decision:
    - [constexpr] when the function is constexpr-eligible and [can_constexpr]
      is [true] (i.e. the definition is visible in the header);
    - [__attribute__((pure))] when the return type is allocation-free; or
    - nothing, for functions that allocate, throw, or take non-literal types.

    @param can_constexpr  whether this call site may use [constexpr]
    @param throws         whether the body unconditionally throws
    @param ret_ty         the C++ return type
    @param params         [(name, type)] pairs for all formal parameters *)
and fun_qualifier ~can_constexpr ~throws ~no_pure ret_ty params =
  if can_constexpr && not throws && not no_pure && is_constexpr_eligible ret_ty params then
    str "constexpr "
  else if is_pure_return_type ret_ty && not throws && not no_pure then
    str "__attribute__((pure)) "
  else
    mt ()

(** Check if a C++ type is concrete (can be used in any_cast). Type variables
    and unknown types are not concrete - we can't cast to them. *)
and is_concrete_cpp_type = function
  | Tvar _ -> false
  | Tunknown | Ttodo | Tany | Tauto -> false
  | Tmod (_, inner) -> is_concrete_cpp_type inner
  | _ -> true

and expr_is_any_returning_method = function
  | CPPmethod_call (CPPglob (n, _, _), _, _) -> method_returns_any n
  | CPPfun_call (CPPglob (n, _, _), _) when lookup_method_this_pos n <> None ->
    method_returns_any n
  | CPPfun_call (CPPget' (_, n), _) -> method_returns_any n
  | _ -> false

(** Check if an expression is a variable (possibly wrapped in [CPPmove])
    whose type is [std::any] — tracked via {!current_any_typed_params}. *)
and expr_is_any_typed_param = function
  | CPPvar id -> Id.Set.mem id !current_any_typed_params
  | CPPmove e -> expr_is_any_typed_param e
  | _ -> false

and wrap_any_cast_if_needed expr expr_printed expected_ty vl =
  if (expr_is_any_returning_method expr || expr_is_any_typed_param expr)
     && is_concrete_cpp_type expected_ty
  then
    str (sn ()).any_cast
    ++ str "<"
    ++ pp_cpp_type false vl expected_ty
    ++ str ">("
    ++ expr_printed
    ++ str ")"
  else
    expr_printed

(** Render a custom extraction syntax template by substituting placeholder
    tokens ([CCscrut], [CCty], [CCarg], etc.) with pretty-printed C++ fragments.
*)
and pp_custom custom env typ t tyargs cases args arg_types vl cmds =
  let pp ?(followed_by_dot=false) cmd =
    match cmd with
    | CCstring s -> str s
    | CCscrut ->
      ( match t with
      | Some t_expr ->
        let t_printed = pp_cpp_expr env [] t_expr in
        let t_printed =
          match t_expr with
          | CPPstring _ -> t_printed ++ str (sn ()).str_suffix
          | _ -> t_printed
        in
        ( match typ with
        | Some expected_ty ->
          wrap_any_cast_if_needed t_expr t_printed expected_ty vl
        | None -> t_printed )
      | None ->
        CErrors.anomaly
          (Pp.str "Custom syntax: scrutinee token with no bound expression") )
    | CCty ->
      ( match typ with
      | Some typ -> pp_cpp_type false vl typ
      | None ->
        CErrors.anomaly (Pp.str "Custom syntax: type token with no bound type")
      )
    | CCbody i ->
      ( try
          let _, _, ss = List.nth cases i in
          pp_list_stmt (pp_cpp_stmt env []) ss
        with Failure _ ->
          CErrors.anomaly
            Pp.(str "Custom syntax: unbound case body in: " ++ str custom) )
    | CCty_arg i ->
      ( try pp_cpp_type false vl (List.nth tyargs i)
        with Failure _ ->
          CErrors.anomaly
            Pp.(str "Custom syntax: unbound type argument in: " ++ str custom)
      )
    | CCbr_var (i, j) ->
      ( try
          let ids, _, _ = List.nth cases i in
          let id, _ = List.nth ids j in
          Id.print id
        with Failure _ ->
          CErrors.anomaly
            Pp.(
              str "Custom syntax: unbound case branch variable in: "
              ++ str custom ) )
    | CCbr_var_ty (i, j) ->
      ( try
          let ids, _, _ = List.nth cases i in
          let _, ty = List.nth ids j in
          pp_cpp_type false vl ty
        with Failure _ ->
          CErrors.anomaly
            Pp.(
              str "Custom syntax: unbound case branch type argument in: "
              ++ str custom ) )
    | CCarg i ->
    try
      let arg_expr = List.nth args i in
      let arg = pp_cpp_expr env [] arg_expr in
      let arg =
        match arg_expr with
        | CPPstring _ -> arg ++ str (sn ()).str_suffix
        | _ -> arg
      in
      (* Parenthesize compound expressions that would bind incorrectly
         when followed by member access (.c_str() etc.) in templates. *)
      let arg =
        if followed_by_dot then
          match arg_expr with
          | CPPbinop _ -> str "(" ++ arg ++ str ")"
          | CPPfun_call (CPPglob (_, _, Some ci), _) when ci.ci_inline <> None ->
            str "(" ++ arg ++ str ")"
          | _ -> arg
        else arg
      in
      match List.nth_opt arg_types i with
      | Some expected_ty -> wrap_any_cast_if_needed arg_expr arg expected_ty vl
      | None -> arg
    with Failure _ ->
      CErrors.anomaly
        Pp.(str "Custom syntax: unbound term argument in: " ++ str custom)
  in
  let next_starts_with_dot = function
    | CCstring s :: _ ->
      let s = String.trim s in
      String.length s > 0 && s.[0] = '.'
    | _ -> false
  in
  let rec fold_cmds acc = function
    | [] -> acc
    | cmd :: rest ->
      let followed_by_dot = next_starts_with_dot rest in
      fold_cmds (acc ++ pp ~followed_by_dot cmd) rest
  in
  fold_cmds (mt ()) cmds

(** Print a template parameter type keyword (typename, concept constraint,
    MapsTo). *)
let pp_template_type = function
  | TTtypename -> str "typename"
  | TTtypename_default _ -> str "typename"
  | TTfun (dom, cod) ->
    str "MapsTo<"
    ++ pp_cpp_type false [] cod
    ++ str ", "
    ++ pp_list (pp_cpp_type false []) dom
    ++ str ">"
  | TTconcept concept -> pp_global Type concept

(** Print a complete template parameter including name and optional default *)
let pp_template_param (tt, id) =
  match tt with
  | TTtypename_default default_ty ->
    str "typename"
    ++ spc ()
    ++ Id.print id
    ++ str " = "
    ++ pp_cpp_type false [] default_ty
  | _ -> pp_template_type tt ++ spc () ++ Id.print id

(** Render a doc comment as [///]-prefixed lines followed by a newline, or
    [mt ()] if no comment is registered for [name].  This is the single lookup
    point used by field, constructor-struct, and enum-value printers.

    @param indent  optional prefix prepended to every line (e.g. ["  "] for
    indented contexts such as enum values).  Defaults to [""]. *)
let pp_doc_comment_for_name ?(indent = "") name =
  match Doc_comments.find name with
  | None -> mt ()
  | Some text ->
    let lines = Doc_comments.format_as_cpp_lines text in
    prlist_with_sep fnl (fun l -> str (indent ^ l)) lines ++ fnl ()

(** pp_cpp_field takes optional struct_name for printing constructors *)
let rec pp_cpp_field ?(struct_name : Pp.t option) env = function
  | Fvar (id, ty) ->
    (* Strip d_ prefix for doc comment lookup (C++ fields are d_fst, Rocq
       names are fst) *)
    let id_str = Id.to_string id in
    let rocq_name =
      if String.length id_str > 2 && String.sub id_str 0 2 = "d_" then
        String.sub id_str 2 (String.length id_str - 2)
      else id_str
    in
    pp_doc_comment_for_name rocq_name
    ++ h (pp_cpp_type false [] ty ++ str " " ++ Id.print id ++ str ";")
  | Fvar' (id, ty) ->
    pp_doc_comment_for_name (Common.pp_global_name Type id)
    ++ h (pp_cpp_type false [] ty ++ str " " ++ pp_global Type id ++ str ";")
  | Ffundef (id, ret_ty, params, body) ->
    let params_s =
      pp_list
        (fun (id, ty) -> pp_cpp_type false [] ty ++ str " " ++ Id.print id)
        params
    in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
    let qualifier =
      fun_qualifier ~can_constexpr:true ~throws:(body_is_throw body) ~no_pure:false
        ret_ty params
    in
    h
      ( qualifier
      ++ pp_cpp_type false [] ret_ty
      ++ str " "
      ++ Id.print id
      ++ pp_par true params_s
      ++ str "{" )
    ++ fnl ()
    ++ body_s
    ++ str "}"
  | Ffundecl (id, ret_ty, params) ->
    let params_s =
      pp_list
        (fun (id, ty) -> pp_cpp_type false [] ty ++ str " " ++ Id.print id)
        (List.rev params)
    in
    let qualifier =
      fun_qualifier ~can_constexpr:true ~throws:false ~no_pure:false ret_ty params
    in
    h
      ( qualifier
      ++ pp_cpp_type false [] ret_ty
      ++ str " "
      ++ Id.print id
      ++ pp_par true params_s )
    ++ str ";"
  | Fmethod
      {
        mf_name;
        mf_tparams;
        mf_ret_type;
        mf_params;
        mf_body;
        mf_is_const;
        mf_is_static;
        mf_no_pure;
      } ->
    let const_s = if mf_is_const then str " const" else mt () in
    let static_s = if mf_is_static then str "static " else mt () in
    let saved_any_params = !current_any_typed_params in
    current_any_typed_params :=
      List.fold_left
        (fun acc (id, ty) ->
          match ty with Tany -> Id.Set.add id acc | _ -> acc)
        Id.Set.empty mf_params;
    let body_s = pp_list_stmt (pp_cpp_stmt env []) mf_body in
    let params_s =
      pp_list
        (fun (id, ty) ->
          if not (stmts_reference_id id mf_body) then
            pp_cpp_type false [] ty
          else
            pp_cpp_type false [] ty ++ str " " ++ Id.print id)
        mf_params
    in
    current_any_typed_params := saved_any_params;
    let template_s =
      match mf_tparams with
      | [] -> mt ()
      | _ ->
        let args = pp_list pp_template_param mf_tparams in
        str "template <" ++ args ++ str ">" ++ fnl ()
    in
    let doc_comment = pp_doc_comment_for_name (Id.to_string mf_name) in
    let qualifier =
      fun_qualifier ~can_constexpr:mf_is_static ~throws:false ~no_pure:mf_no_pure
        mf_ret_type mf_params
    in
    doc_comment
    ++ template_s
    ++ h
         ( qualifier
         ++ static_s
         ++ pp_cpp_type false [] mf_ret_type
         ++ str " "
         ++ Id.print mf_name
         ++ pp_par true params_s
         ++ const_s
         ++ str " {" )
    ++ fnl ()
    ++ body_s
    ++ str "}"
  | Fconstructor (params, init_list, is_explicit) ->
    let sname =
      match struct_name with
      | Some s -> s
      | None -> str "UNKNOWN_STRUCT"
    in
    let params_s =
      pp_list
        (fun (id, ty) -> pp_cpp_type false [] ty ++ str " " ++ Id.print id)
        params
    in
    let init_s =
      match init_list with
      | [] -> mt ()
      | _ ->
        str " : "
        ++ pp_list
             (fun (member, expr) ->
               Id.print member ++ str "(" ++ pp_cpp_expr env [] expr ++ str ")" )
             init_list
    in
    let explicit_s = if is_explicit then str "explicit " else mt () in
    h (explicit_s ++ sname ++ pp_par true params_s ++ init_s ++ str " {}")
  | Fnested_struct (id, fields) ->
    let fields_s =
      pp_cpp_fields_with_vis ~struct_name:(Id.print id) env fields
    in
    (* Constructor structs are PascalCase (e.g. Mycons) while Rocq names are
       lowercase (mycons).  Try both for the doc comment lookup. *)
    let id_str = Id.to_string id in
    let doc_s =
      let d = pp_doc_comment_for_name id_str in
      if Pp.ismt d then pp_doc_comment_for_name (String.uncapitalize_ascii id_str)
      else d
    in
    doc_s
    ++ h (str "struct " ++ Id.print id ++ str " {")
    ++ fnl ()
    ++ fields_s
    ++ fnl ()
    ++ str "};"
  | Fnested_using (id, ty) ->
    h
      ( str "using "
      ++ Id.print id
      ++ str " = "
      ++ pp_cpp_type false [] ty
      ++ str ";" )
  | Fdeleted_ctor ->
    let sname =
      match struct_name with
      | Some s -> s
      | None -> str "UNKNOWN_STRUCT"
    in
    h (sname ++ str "() = delete;")

(** Helper to print fields with visibility and section tag grouping *)
and pp_cpp_fields_with_vis ?(struct_name : Pp.t option) env fields =
  (* Group consecutive fields by (visibility, section_tag) *)
  let rec group_fields current_vis current_tag acc result = function
    | [] ->
      if acc = [] then
        List.rev result
      else
        List.rev ((current_vis, current_tag, List.rev acc) :: result)
    | (fld, vis, tag) :: rest ->
      if vis = current_vis && tag = current_tag then
        group_fields current_vis current_tag (fld :: acc) result rest
      else
        let result' =
          if acc = [] then
            result
          else
            (current_vis, current_tag, List.rev acc) :: result
        in
        group_fields vis tag [fld] result' rest
  in
  let groups = group_fields VPublic SNoTag [] [] fields in
  (* Check if we need visibility labels (only if mixed or all private) *)
  let needs_labels =
    match groups with
    | [] -> false
    | _ ->
      let all_public = List.for_all (fun (vis, _, _) -> vis = VPublic) groups in
      not all_public
  in
  let section_tag_str = function
    | STypes -> Some "// TYPES"
    | SData -> Some "// DATA"
    | SCreators -> Some "// CREATORS"
    | SManipulators -> Some "// MANIPULATORS"
    | SAccessors -> Some "// ACCESSORS"
    | SNoTag -> None
  in
  (* When printing groups, only emit visibility label when it changes *)
  let rec pp_groups prev_vis = function
    | [] -> mt ()
    | [(vis, tag, flds)] ->
      let vis_pp =
        if needs_labels && vis <> prev_vis then
          let vis_str =
            match vis with
            | VPublic -> "public:"
            | VPrivate -> "private:"
          in
          str vis_str ++ fnl ()
        else
          mt ()
      in
      let tag_pp =
        match section_tag_str tag with
        | Some s -> str ("  " ^ s) ++ fnl ()
        | None -> mt ()
      in
      vis_pp ++ tag_pp ++ pp_list_stmt (pp_cpp_field ?struct_name env) flds
    | (vis, tag, flds) :: rest ->
      let vis_pp =
        if needs_labels && vis <> prev_vis then
          let vis_str =
            match vis with
            | VPublic -> "public:"
            | VPrivate -> "private:"
          in
          str vis_str ++ fnl ()
        else
          mt ()
      in
      let tag_pp =
        match section_tag_str tag with
        | Some s -> str ("  " ^ s) ++ fnl ()
        | None -> mt ()
      in
      vis_pp
      ++ tag_pp
      ++ pp_list_stmt (pp_cpp_field ?struct_name env) flds
      ++ fnl ()
      ++ pp_groups vis rest
  in
  pp_groups VPublic groups

(** Generate a Meyers' singleton accessor for a static data member. Wraps the
    initializer in a function with a local [static const] variable, guaranteeing
    initialization on first use. This avoids the static initialization order
    fiasco for template static inline members whose initialization order
    relative to other inline variables is unspecified.

    Registers the accessor in {!template_static_accessors} so that call sites
    append [()] after the template arguments (see {!pp_cpp_expr}). *)
let pp_meyers_singleton env id ty expr_pp =
  (let mp = modpath_of_r id in
   let lbl = label_of_r id in
   template_static_accessors := (mp, lbl) :: !template_static_accessors );
  let bare_ty =
    match ty with
    | Tmod (TMconst, inner) -> inner
    | _ -> ty
  in
  h
    ( str "static const "
    ++ pp_cpp_type false [] bare_ty
    ++ str "& "
    ++ pp_global Type id
    ++ str "() {" )
  ++ fnl ()
  ++ str "  static const "
  ++ pp_cpp_type false [] bare_ty
  ++ str " v = "
  ++ expr_pp
  ++ str ";"
  ++ fnl ()
  ++ str "  return v;"
  ++ fnl ()
  ++ str "}"

(** Extract the primary GlobRef from a declaration, if any. *)
let rec decl_globref = function
  | Dtemplate (_, _, inner) -> decl_globref inner
  | Dfundef ((r, _) :: _, _, _, _, _) -> Some r
  | Dstruct ds -> Some ds.ds_ref
  | Dnspace (Some r, _) -> Some r
  | _ -> None

(** Apply loopify transformation to a declaration before rendering. *)
let maybe_loopify decl =
  let should =
    match decl_globref decl with
    | Some r -> Table.should_loopify r
    | None -> Table.loopify ()
  in
  if should then
    let pp_type t = Pp.string_of_ppcmds (pp_cpp_type false [] t) in
    let pp_expr e = Pp.string_of_ppcmds (pp_cpp_expr ([], Id.Set.empty) [] e) in
    Loopify.transform_decl ~pp_type ~pp_expr decl
  else
    decl

(** Pretty-print a MiniCpp declaration as C++ source. Handles templates,
    namespaces/structs, functions, assignments, enums, etc. *)
let rec pp_cpp_decl env decl = pp_cpp_decl_raw env (maybe_loopify decl)

and pp_cpp_decl_raw env = function
  | Dtemplate (temps, cstr, Dasgn (id, ty, e)) when render_ctx.rc_in_struct ->
    let args = pp_list pp_template_param temps in
    let expr_pp = wrap_any_cast_if_needed e (pp_cpp_expr env [] e) ty [] in
    h (str "template <" ++ args ++ str ">")
    ++ ( match cstr with
    | None -> fnl ()
    | Some c -> pp_cpp_expr env [] c ++ fnl () )
    ++ pp_meyers_singleton env id ty expr_pp
  | Dtemplate (temps, cstr, decl) ->
    let args = pp_list pp_template_param temps in
    h (str "template <" ++ args ++ str ">")
    ++ ( match cstr with
    | None -> fnl ()
    | Some c -> pp_cpp_expr env [] c ++ fnl () )
    ++ pp_cpp_decl_raw env decl
  | Dnspace (None, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl_raw env) decls in
    h (str "namespace " ++ str "{") ++ fnl () ++ ds ++ fnl () ++ str "};"
  | Dnspace (Some id, decls) ->
    let struct_name_str =
      match id with
      | GlobRef.IndRef _ -> String.capitalize_ascii (str_global Type id)
      | _ -> string_of_ppcmds (pp_global Type id)
    in
    let has_pending = Hashtbl.mem pending_wrapper_decls struct_name_str in
    ( match (decls, has_pending) with
    | ( [
          Dstruct
            {
              ds_fields = fields;
              ds_tparams = [];
              ds_needs_shared_from_this = sft;
              _;
            };
        ],
        false ) ->
      (* MERGE non-template: struct Nat { ... } *)
      let struct_name = str struct_name_str in
      let f_s =
        with_render_ctx
          ~setup:(fun () -> render_ctx.rc_in_struct <- true)
          (fun () -> pp_cpp_fields_with_vis ~struct_name env fields)
      in
      let inherit_clause =
        if sft then
          str " : public std::enable_shared_from_this<"
          ++ struct_name
          ++ str ">"
        else
          mt ()
      in
      str "struct "
      ++ struct_name
      ++ inherit_clause
      ++ str " {"
      ++ fnl ()
      ++ f_s
      ++ fnl ()
      ++ str "};"
    | ( [
          Dstruct
            {
              ds_fields = fields;
              ds_tparams = temps;
              ds_constraint = cstr;
              ds_needs_shared_from_this = sft;
              _;
            };
        ],
        false ) ->
      (* MERGE template: template<typename A> struct List { ... } *)
      let struct_name = str struct_name_str in
      let f_s =
        with_render_ctx
          ~setup:(fun () ->
            render_ctx.rc_in_struct <- true;
            render_ctx.rc_in_template <- true )
          (fun () -> pp_cpp_fields_with_vis ~struct_name env fields)
      in
      let args = pp_list pp_template_param temps in
      let inherit_clause =
        if sft then
          let type_args = pp_list (fun (_, id) -> Id.print id) temps in
          str " : public std::enable_shared_from_this<"
          ++ struct_name
          ++ str "<"
          ++ type_args
          ++ str ">>"
        else
          mt ()
      in
      h (str "template <" ++ args ++ str ">")
      ++ ( match cstr with
      | None -> fnl ()
      | Some c -> pp_cpp_expr env [] c ++ fnl () )
      ++ str "struct "
      ++ struct_name
      ++ inherit_clause
      ++ str " {"
      ++ fnl ()
      ++ f_s
      ++ fnl ()
      ++ str "};"
    | _ ->
      (* No merge: keep wrapper struct (has pending decls or multiple
         children) *)
      let ds =
        with_render_ctx
          ~setup:(fun () -> render_ctx.rc_in_struct <- true)
          (fun () -> pp_list_stmt (pp_cpp_decl_raw env) decls)
      in
      let pending_fwd =
        match Hashtbl.find_opt pending_wrapper_decls struct_name_str with
        | Some specs ->
          Hashtbl.remove pending_wrapper_decls struct_name_str;
          fnl () ++ specs
        | None -> mt ()
      in
      h (str "struct " ++ str struct_name_str ++ str " {")
      ++ fnl ()
      ++ ds
      ++ pending_fwd
      ++ fnl ()
      ++ str "};" )
  | Dfundef (ids, ret_ty, params, body, no_pure) ->
    let params_s =
      pp_list
        (fun (id, ty) ->
          if not (stmts_reference_id id body) then
            pp_cpp_type false [] ty
          else
            pp_cpp_type false [] ty ++ str " " ++ Id.print id)
        (List.rev params)
    in
    let base_name =
      prlist_with_sep
        (fun () -> str "::")
        (fun (n, tys) ->
          match tys with
          | [] -> pp_global Type n
          | _ ->
            pp_global Type n
            ++ str "<"
            ++ pp_list (pp_cpp_type false []) tys
            ++ str ">" )
        ids
    in
    let is_lifted =
      match ids with
      | (GlobRef.VarRef _, _) :: _ -> true
      | _ -> false
    in
    let name =
      match render_ctx.rc_struct_name with
      | Some struct_name when (not render_ctx.rc_in_struct) && not is_lifted ->
        struct_name ++ str "::" ++ base_name
      | _ -> base_name
    in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
    let is_qualified =
      List.length ids > 1
      ||
      match ids with
      | [(_, tys)] when tys <> [] -> true
      | _ -> false
    in
    (* Check if qualified name (out-of-line definition) OR inside a struct
       context *)
    let is_struct_member = is_qualified || render_ctx.rc_in_struct in
    let is_out_of_struct_def =
      match render_ctx.rc_struct_name with
      | Some _ -> not render_ctx.rc_in_struct
      | None -> false
    in
    (* Add static for struct member functions *)
    let static_kw =
      if is_struct_member && not is_out_of_struct_def then
        str "static "
      else
        mt ()
    in
    (* Dfundef is the top-level definition form — it's either in a .cpp file
       (out-of-line) or inline in a template struct (in-struct + in-template).
       constexpr requires the definition visible in the header, so only use
       it for inline template struct definitions. *)
    let qualifier =
      fun_qualifier
        ~can_constexpr:(render_ctx.rc_in_struct && not is_out_of_struct_def)
        ~throws:(body_is_throw body)
        ~no_pure
        ret_ty params
    in
    h
      ( qualifier
      ++ static_kw
      ++ pp_cpp_type false [] ret_ty
      ++ str " "
      ++ name
      ++ pp_par true params_s )
    ++ str "{"
    ++ body_s
    ++ str "}"
  | Dfundecl (ids, ret_ty, params, no_pure) ->
    let params_s =
      pp_list
        (fun (id, ty) ->
          match id with
          | Some id -> pp_cpp_type false [] ty ++ str " " ++ Id.print id
          | None -> pp_cpp_type false [] ty )
        (List.rev params)
    in
    let name =
      prlist_with_sep
        (fun () -> str "::")
        (fun (n, tys) ->
          match tys with
          | [] -> pp_global Type n
          | _ ->
            pp_global Type n
            ++ str "<"
            ++ pp_list (pp_cpp_type false []) tys
            ++ str ">" )
        ids
    in
    let is_qualified =
      List.length ids > 1
      ||
      match ids with
      | [(_, tys)] when tys <> [] -> true
      | _ -> false
    in
    let is_struct_member = is_qualified || render_ctx.rc_in_struct in
    let static_kw = if is_struct_member then str "static " else mt () in
    (* Dfundecl is always a forward declaration for an out-of-line .cpp
       definition, so constexpr is never applicable here (it requires the
       full definition to be visible in the header).  We don't use
       {!fun_qualifier} because [can_constexpr] is unconditionally false
       and the param list has a different shape ([Id.t option] vs [Id.t]). *)
    let qualifier =
      if is_pure_return_type ret_ty && not no_pure then
        str "__attribute__((pure)) "
      else
        mt ()
    in
    h
      ( qualifier
      ++ static_kw
      ++ pp_cpp_type false [] ret_ty
      ++ str " "
      ++ name
      ++ pp_par true params_s )
    ++ str ";"
  | Dstruct
      {
        ds_ref = id;
        ds_fields = fields;
        ds_tparams = tparams;
        ds_constraint = cstr;
        ds_needs_shared_from_this = sft;
      } ->
    let struct_name =
      match id with
      | GlobRef.IndRef _ when is_eponymous_record_cached id ->
        str (Common.pp_type_name_capitalized id)
      | GlobRef.IndRef _ when is_record_cached id -> pp_global Type id
      | GlobRef.IndRef _ -> pp_global Type id
      | _ -> pp_global Type id
    in
    let f_s =
      match tparams with
      | [] -> pp_cpp_fields_with_vis ~struct_name env fields
      | _ ->
        with_render_ctx
          ~setup:(fun () -> render_ctx.rc_in_template <- true)
          (fun () -> pp_cpp_fields_with_vis ~struct_name env fields)
    in
    let tmpl =
      match tparams with
      | [] -> mt ()
      | _ ->
        let args = pp_list pp_template_param tparams in
        h (str "template <" ++ args ++ str ">")
        ++
        ( match cstr with
        | None -> fnl ()
        | Some c -> pp_cpp_expr env [] c ++ fnl () )
    in
    let inherit_clause =
      if sft then
        match
          tparams
        with
        | [] ->
          str " : public std::enable_shared_from_this<"
          ++ struct_name
          ++ str ">"
        | _ ->
          let type_args = pp_list (fun (_, tid) -> Id.print tid) tparams in
          str " : public std::enable_shared_from_this<"
          ++ struct_name
          ++ str "<"
          ++ type_args
          ++ str ">>"
      else
        mt ()
    in
    tmpl
    ++ str "struct "
    ++ struct_name
    ++ inherit_clause
    ++ str " {"
    ++ fnl ()
    ++ f_s
    ++ fnl ()
    ++ str "};"
  | Dstruct_decl id -> str "struct " ++ pp_global Type id ++ str ";"
  | Dusing (id, ty) ->
    str "using "
    ++ pp_global Type id
    ++ str " = "
    ++ pp_cpp_type false [] ty
    ++ str ";"
  | Dasgn (id, ty, e) ->
    (* Special handling for CPPabort: generate lambda with correct return
       type *)
    let expr_pp =
      match e with
      | CPPabort msg ->
        str "([]() -> "
        ++ pp_cpp_type false [] ty
        ++ str " { throw "
        ++ str (sn ()).logic_error
        ++ str "(\""
        ++ str msg
        ++ str "\"); })()"
      | _ -> wrap_any_cast_if_needed e (pp_cpp_expr env [] e) ty []
    in
    if render_ctx.rc_in_template then
      (* Inside template: use Meyers singleton to avoid static init order
         fiasco *)
      pp_meyers_singleton env id ty expr_pp
    else
      let static_kw =
        if render_ctx.rc_in_struct then
          str "static inline "
        else
          mt ()
      in
      let needs_iife =
        render_ctx.rc_in_struct && expr_contains_capturing_lambda e
      in
      let wrapped_expr =
        if needs_iife then
          str "[]() {"
          ++ fnl ()
          ++ str "return "
          ++ expr_pp
          ++ str ";"
          ++ fnl ()
          ++ str "}()"
        else
          expr_pp
      in
      h
        ( static_kw
        ++ pp_cpp_type false [] ty
        ++ str " "
        ++ pp_global Type id
        ++ str " = "
        ++ wrapped_expr
        ++ str ";" )
  | Ddecl (id, ty) ->
    h (pp_cpp_type false [] ty ++ str " " ++ pp_global Type id ++ str ";")
  | Dconcept (id, cstr) ->
    (* For hoisted concepts, use only the simple base name without module
       qualification *)
    let simple_name = Common.pp_global_name Type id in
    (* Extract just the last component after :: if present *)
    let last_component =
      match String.rindex_opt simple_name ':' with
      | Some idx
        when idx > 0
             && idx < String.length simple_name - 1
             && simple_name.[idx - 1] = ':' ->
        String.sub simple_name (idx + 1) (String.length simple_name - idx - 1)
      | _ -> simple_name
    in
    h
      ( str "concept "
      ++ str last_component
      ++ str " = "
      ++ pp_cpp_expr env [] cstr
      ++ str ";" )
  | Dstatic_assert (e, so) ->
    ( match so with
    | None -> h (str "static_assert(" ++ pp_cpp_expr env [] e ++ str ");")
    | Some s ->
      h
        ( str "static_assert("
        ++ pp_cpp_expr env [] e
        ++ str ", \""
        ++ str s
        ++ str "\");" ) )
  | Denum {de_ref = name; de_ctors = ctors; de_ctor_rocq_names = rocq_names; _}
    ->
    let struct_name =
      match name with
      | GlobRef.IndRef _ -> pp_inductive_type_name_cached name
      | _ -> pp_global Type name
    in
    (* Emit each enum value, preceded by its doc comment if one exists.
       [rocq_names] and [ctors] are parallel lists from the same constructor
       array, so [List.map2] is safe. *)
    let ctors_s =
      prlist_with_sep
        (fun () -> str "," ++ fnl ())
        (fun (id, rname) ->
          pp_doc_comment_for_name ~indent:"  " rname
          ++ str "  " ++ Id.print id )
        (List.combine ctors rocq_names)
    in
    str "enum class "
    ++ struct_name
    ++ str " {"
    ++ fnl ()
    ++ ctors_s
    ++ fnl ()
    ++ str "};"

(** {2 Pretty-printing of types. [par] is a boolean indicating whether
    parentheses are needed or not.} *)

let pp_type par vl t =
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] t in
  pp_cpp_type par vl cty

(** {2 Pretty-printing of expressions. [par] indicates whether parentheses are
    needed or not. [env] is the list of names for the de Bruijn variables.
    [args] is the list of collected arguments (already pretty-printed).} *)

(** Insert a double line-break in the Pp output (used to visually separate
    declaration groups in the generated C++ source). *)
let cut2 () = brk (0, -100000) ++ brk (0, 0)
