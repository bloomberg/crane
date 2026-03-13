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

(** Check if a lambda actually needs to capture variables from enclosing scope.
    A lambda needs [&] capture if its body references variables that are:
    - Not lambda parameters
    - Not locally declared within the lambda body
    - 'this' pointer (always needs capture in a lambda) Returns true if capture
      is needed, false if [] can be used.

    Also checks recursively: if a nested lambda captures from the outer lambda's
    scope, that counts as the outer lambda needing capture. *)
let rec lambda_needs_capture
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
     |CPPraw _ -> (refs, decls)
  and collect_from_stmt (refs, decls) stmt =
    match stmt with
    | Sreturn None -> (refs, decls)
    | Sreturn (Some e) -> collect_from_expr (refs, decls) e
    | Sexpr e -> collect_from_expr (refs, decls) e
    | Sdecl (id, _) -> (refs, IdSet.add id decls)
    | Sasgn (id, _, e) ->
      let refs', decls' = collect_from_expr (refs, decls) e in
      (refs', IdSet.add id decls')
    | Sif (cond, then_stmts, else_stmts) ->
      List.fold_left
        collect_from_stmt
        (List.fold_left
           collect_from_stmt
           (collect_from_expr (refs, decls) cond)
           then_stmts )
        else_stmts
    | Sswitch (scrut, _, branches) ->
      List.fold_left
        (fun acc (_, stmts) -> List.fold_left collect_from_stmt acc stmts)
        (collect_from_expr (refs, decls) scrut)
        branches
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
    | Sthrow _ | Sassert _ | Sraw _ -> (refs, decls)
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
   |CPPraw _ -> false

and stmt_contains_capturing_lambda (s : Minicpp.cpp_stmt) : bool =
  let open Minicpp in
  let any = List.exists stmt_contains_capturing_lambda in
  let expr = expr_contains_capturing_lambda in
  match s with
  | Sreturn (Some e) | Sexpr e | Sasgn (_, _, e) -> expr e
  | Sreturn None -> false
  | Sassign_field (obj, _, e) -> expr obj || expr e
  | Sif (cond, then_s, else_s) -> expr cond || any then_s || any else_s
  | Sswitch (scrut, _, branches) ->
    expr scrut || List.exists (fun (_, stmts) -> any stmts) branches
  | Scustom_case (_, scrut, _, branches, _) ->
    expr scrut || List.exists (fun (_, _, stmts) -> any stmts) branches
  | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ -> false

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
        (s.[i], i + esc_len + 1 < n)
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

(** Print a type variable by de Bruijn index, looking up in [vl]. Falls back to
    [T<n>] if index is out of range. *)
let print_cpp_type_var vl i =
  try pp_tvar (List.nth vl (pred i)) with Failure _ -> str "T" ++ int i

(** Pretty-print a MiniCpp type as C++ source. [par] controls whether
    parentheses are added around the result. [vl] is the list of type variable
    names for de Bruijn lookup. *)
let rec pp_cpp_type par vl t =
  let rec pp_rec par = function
    | Tvar (i, None) -> print_cpp_type_var vl i
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
    | Tglob (r, tys, args) ->
      (* Erased type/prop/implicit markers (from Tdummy in the ML AST) should
         never reach the C++ output. When they do survive — e.g. as a template
         argument of SigT<nat, dummy_prop> — render them as std::any. *)
      ( match r with
      | GlobRef.VarRef id
        when let name = Id.to_string id in
             name = "dummy_type"
             || name = "dummy_prop"
             || name = "dummy_implicit" -> str "std::any"
      | _ ->
      match find_custom_opt r with
      | Some s when to_inline r ->
        let cmds = parse_numbered_args "a" (fun i -> CCarg i) s in
        let cmds =
          List.fold_left
            (fun prev curr ->
              match curr with
              | CCstring s ->
                prev @ parse_numbered_args "t" (fun i -> CCty_arg i) s
              | _ -> prev @ [curr] )
            []
            cmds
        in
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
            if String.contains name_str ':' then
              let last_colon_pos = String.rindex name_str ':' in
              let before = String.sub name_str 0 (last_colon_pos + 1) in
              let after =
                String.sub
                  name_str
                  (last_colon_pos + 1)
                  (String.length name_str - last_colon_pos - 1)
              in
              str before ++ str "template " ++ str after
            else
              type_name
          in
          typename_prefix_for name_str
          ++ struct_qualifier_for r name_str
          ++ type_name_with_template
          ++ str "<"
          ++ pp_list (pp_rec false) l
          ++ str ">" ) )
    | Tfun (d, c) ->
      std_angle
        "function"
        (pp_rec false c ++ pp_par true (pp_list (pp_rec false) d))
    | Tref t -> pp_rec false t ++ str "&"
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
      (* DESIGN: Template-dependent type access like 'typename M::Key::t'. C++
         templates require 'typename' to access nested types from dependent base
         types. *)
      let base_str =
        match base_ty with
        | Tglob (r, _, _) ->
          let type_name_str = str_global Type r in
          if is_qualified_name type_name_str then
            pp_rec false base_ty
          else
            let ns_name, needs_ns = inductive_name_info_cached r in
            if needs_ns && not (is_merged_inductive_cached r) then
              ns_name ++ str "::" ++ pp_rec false base_ty
            else
              pp_rec false base_ty
        | _ -> pp_rec false base_ty
      in
      str "typename " ++ base_str ++ str "::" ++ Id.print nested_id
    | Tvariant tys -> std_angle "variant" (pp_list (pp_rec false) tys)
    | Tshared_ptr t -> cpp_angle (sn ()).shared_ptr (pp_rec false t)
    | Tunique_ptr t -> cpp_angle (sn ()).unique_ptr (pp_rec false t)
    | Tvoid -> str "void"
    | Ttodo -> str "auto"
    | Tunknown -> str "UNKNOWN"
    | Tany -> str "std::any"
  in
  h (pp_rec par t)

(** Pretty-print a MiniCpp expression as C++ source. [env] is the de Bruijn
    variable name environment. [args] is the list of accumulated arguments (for
    partial application). *)
and pp_cpp_expr env args t =
  let apply st = pp_apply_cpp st args in
  match t with
  | CPPvar id -> Id.print id
  | CPPglob (x, tys, Some ci) when ci.ci_inline <> None ->
    let custom = Option.get ci.ci_inline in
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
        let num_struct_params =
          match record_ref with
          | GlobRef.IndRef (kn, _) ->
            ( match Table.get_ind_num_param_vars_opt kn with
            | Some n -> n
            | None -> 2 )
          | _ -> 2
        in
        let placeholder_args =
          String.concat ", " (List.init num_struct_params (fun _ -> "int"))
        in
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
        (* Constant/function inside eponymous template struct with NO type args:
           This happens for non-parameterized constants like e_SUCCESS. Generate
           StructName<int, int>::constName as a workaround. *)
        let struct_name = Common.pp_global_name Type record_ref in
        let func_name = Common.pp_global_name Term x in
        let num_params =
          match record_ref with
          | GlobRef.IndRef (kn, _) ->
            ( match Table.get_ind_num_param_vars_opt kn with
            | Some n -> n
            | None -> 2 )
          | _ -> 2
        in
        let placeholder_args =
          String.concat ", " (List.init num_params (fun _ -> "int"))
        in
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
        if String.contains base_name_str ':' then
          (* Find last occurrence of :: and insert "template " after it *)
          let last_colon_pos = String.rindex base_name_str ':' in
          let before = String.sub base_name_str 0 (last_colon_pos + 1) in
          let after =
            String.sub
              base_name_str
              (last_colon_pos + 1)
              (String.length base_name_str - last_colon_pos - 1)
          in
          str before
          ++ str "template "
          ++ str after
          ++ str "<"
          ++ ty_args
          ++ str ">"
        else
          base_name ++ str "<" ++ ty_args ++ str ">"
    in
    let full_name = if is_accessor then full_name ++ str "()" else full_name in
    apply full_name
  | CPPnamespace (r, t) ->
    let name, _ = inductive_name_info_cached r in
    h (name ++ str "::" ++ pp_cpp_expr env args t)
  | CPPfun_call (CPPglob (n, tys, Some ci), ts) when ci.ci_inline <> None ->
    let s = Option.get ci.ci_inline in
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
      let cmds =
        List.fold_left
          (fun prev curr ->
            match curr with
            | CCstring s ->
              prev @ parse_numbered_args "t" (fun i -> CCty_arg i) s
            | _ -> prev @ [curr] )
          []
          cmds
      in
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
    let params_s, capture =
      match params with
      | [] -> (str "void", capture_str)
      | _ ->
        ( pp_list
            (fun (ty, id_opt) ->
              let id_s =
                match id_opt with
                | None -> str ""
                | Some id -> Id.print id
              in
              pp_cpp_type false [] ty ++ spc () ++ id_s )
            (List.rev params),
          capture_str )
    in
    let body_s = pp_list_stmt (pp_cpp_stmt env args) body in
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
  | CPPvisit -> str (sn ()).visit
  | CPPmk_shared t -> cpp_angle (sn ()).make_shared (pp_cpp_type false [] t)
  | CPPmk_unique t -> cpp_angle (sn ()).make_unique (pp_cpp_type false [] t)
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
  | CPPmember (e, id) -> pp_cpp_expr env args e ++ str "." ++ Id.print id
  | CPParrow (e, id) -> pp_cpp_expr env args e ++ str "->" ++ Id.print id
  | CPPmethod_call (obj, method_name, call_args) ->
    pp_cpp_expr env args obj
    ++ str "->"
    ++ Id.print method_name
    ++ str "("
    ++ pp_list (pp_cpp_expr env args) call_args
    ++ str ")"
  | CPPqualified (e, id) -> pp_cpp_expr env args e ++ str "::" ++ Id.print id
  | CPPconvertible_to ty ->
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
    pp_cpp_expr env args lhs
    ++ str " "
    ++ str op
    ++ str " "
    ++ pp_cpp_expr env args rhs

(** Pretty-print a MiniCpp statement as C++ source. *)
and pp_cpp_stmt env args = function
  | Sreturn None -> str "return;"
  | Sreturn (Some (CPPabort msg)) ->
    str "throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str msg
    ++ str "\");"
  | Sreturn (Some e) -> str "return " ++ pp_cpp_expr env args e ++ str ";"
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
    str "throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str msg
    ++ str "\");"
  | Sswitch (scrut, ind, branches) ->
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
    str "switch ("
    ++ pp_cpp_expr env args scrut
    ++ str ") {"
    ++ fnl ()
    ++ prlist_with_sep fnl pp_branch branches
    ++ fnl ()
    ++ str "}"
  | Sassert (expr_str, comment_opt) ->
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
  | Sraw code -> str code
  | Sassign_field (obj, field, e) ->
    pp_cpp_expr env args obj
    ++ str "."
    ++ Id.print field
    ++ str " = "
    ++ pp_cpp_expr env args e
    ++ str ";"
  | Scustom_case (typ, t, tyargs, cases, cmatch) ->
    let cmds = parse_custom_fixed "scrut" CCscrut cmatch in
    let cmds =
      List.fold_left
        (fun prev curr ->
          match curr with
          | CCstring s -> prev @ parse_custom_fixed "ty" CCty s
          | _ -> prev @ [curr] )
        []
        cmds
    in
    let helper e f cmds =
      List.fold_left
        (fun prev curr ->
          match curr with
          | CCstring s -> prev @ parse_numbered_args e f s
          | _ -> prev @ [curr] )
        []
        cmds
    in
    let cmds = helper "t" (fun i -> CCty_arg i) cmds in
    let cmds = helper "br" (fun i -> CCbody i) cmds in
    let helper2 e1 e2 f cmds =
      List.fold_left
        (fun prev curr ->
          match curr with
          | CCstring s -> prev @ parse_custom_numbered_binders e1 e2 f s
          | _ -> prev @ [curr] )
        []
        cmds
    in
    let cmds = helper2 "b" "a" (fun i j -> CCbr_var (i, j)) cmds in
    let cmds = helper2 "b" "t" (fun i j -> CCbr_var_ty (i, j)) cmds in
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

(** Check if a return type is eligible for __attribute__((pure)). Types that
    involve allocation (shared_ptr, unique_ptr), side effects (void), or are
    unknown at definition time (type variables, any, todo) are excluded. *)
and is_pure_return_type = function
  | Tshared_ptr _ | Tunique_ptr _ -> false
  | Tvoid | Tvar _ | Tany | Ttodo | Tunknown -> false
  | Tmod (_, t) | Tref t -> is_pure_return_type t
  | _ -> true

(** Check if a C++ type is concrete (can be used in any_cast). Type variables
    and unknown types are not concrete - we can't cast to them. *)
and is_concrete_cpp_type = function
  | Tvar _ -> false
  | Tunknown | Ttodo | Tany -> false
  | Tmod (_, inner) -> is_concrete_cpp_type inner
  | _ -> true

and expr_is_any_returning_method = function
  | CPPmethod_call (CPPglob (n, _, _), _, _) -> method_returns_any n
  | CPPfun_call (CPPglob (n, _, _), _) when lookup_method_this_pos n <> None ->
    method_returns_any n
  | _ -> false

and wrap_any_cast_if_needed expr expr_printed expected_ty vl =
  if expr_is_any_returning_method expr && is_concrete_cpp_type expected_ty then
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
  let pp cmd =
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
      match List.nth_opt arg_types i with
      | Some expected_ty -> wrap_any_cast_if_needed arg_expr arg expected_ty vl
      | None -> arg
    with Failure _ ->
      CErrors.anomaly
        Pp.(str "Custom syntax: unbound term argument in: " ++ str custom)
  in
  List.fold_left (fun prev c -> prev ++ pp c) (mt ()) cmds

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

(** pp_cpp_field takes optional struct_name for printing constructors *)
let rec pp_cpp_field ?(struct_name : Pp.t option) env = function
  | Fvar (id, ty) ->
    h (pp_cpp_type false [] ty ++ str " " ++ Id.print id ++ str ";")
  | Fvar' (id, ty) ->
    h (pp_cpp_type false [] ty ++ str " " ++ pp_global Type id ++ str ";")
  | Ffundef (id, ret_ty, params, body) ->
    let params_s =
      pp_list
        (fun (id, ty) -> pp_cpp_type false [] ty ++ str " " ++ Id.print id)
        params
    in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
    let pure_attr =
      if is_pure_return_type ret_ty then
        str "__attribute__((pure)) "
      else
        mt ()
    in
    h
      ( pure_attr
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
    let pure_attr =
      if is_pure_return_type ret_ty then
        str "__attribute__((pure)) "
      else
        mt ()
    in
    h
      ( pure_attr
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
      } ->
    let params_s =
      pp_list
        (fun (id, ty) -> pp_cpp_type false [] ty ++ str " " ++ Id.print id)
        mf_params
    in
    let const_s = if mf_is_const then str " const" else mt () in
    let static_s = if mf_is_static then str "static " else mt () in
    let body_s = pp_list_stmt (pp_cpp_stmt env []) mf_body in
    let template_s =
      match mf_tparams with
      | [] -> mt ()
      | _ ->
        let args = pp_list pp_template_param mf_tparams in
        str "template <" ++ args ++ str ">" ++ fnl ()
    in
    let doc_comment =
      match Doc_comments.find (Id.to_string mf_name) with
      | None -> mt ()
      | Some text ->
        let lines = Doc_comments.format_as_cpp_lines text in
        prlist_with_sep fnl (fun l -> str l) lines ++ fnl ()
    in
    let pure_attr =
      if is_pure_return_type mf_ret_type then
        str "__attribute__((pure)) "
      else
        mt ()
    in
    doc_comment
    ++ template_s
    ++ h
         ( pure_attr
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
    h (str "struct " ++ Id.print id ++ str " {")
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

(** Pretty-print a MiniCpp declaration as C++ source. Handles templates,
    namespaces/structs, functions, assignments, enums, etc. *)
let rec pp_cpp_decl env = function
  | Dtemplate (temps, cstr, Dasgn (id, ty, e)) when render_ctx.rc_in_struct ->
    let args = pp_list pp_template_param temps in
    let expr_pp = pp_cpp_expr env [] e in
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
    ++ pp_cpp_decl env decl
  | Dnspace (None, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl env) decls in
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
          (fun () -> pp_list_stmt (pp_cpp_decl env) decls)
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
  | Dfundef (ids, ret_ty, params, body) ->
    let params_s =
      pp_list
        (fun (id, ty) -> pp_cpp_type false [] ty ++ str " " ++ Id.print id)
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
    let pure_attr =
      if is_pure_return_type ret_ty then
        str "__attribute__((pure)) "
      else
        mt ()
    in
    h
      ( pure_attr
      ++ static_kw
      ++ pp_cpp_type false [] ret_ty
      ++ str " "
      ++ name
      ++ pp_par true params_s )
    ++ str "{"
    ++ body_s
    ++ str "}"
  | Dfundecl (ids, ret_ty, params) ->
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
    let pure_attr =
      if is_pure_return_type ret_ty then
        str "__attribute__((pure)) "
      else
        mt ()
    in
    h
      ( pure_attr
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
      | _ -> pp_cpp_expr env [] e
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
  | Denum {de_ref = name; de_ctors = ctors; _} ->
    let struct_name =
      match name with
      | GlobRef.IndRef _ -> pp_inductive_type_name_cached name
      | _ -> pp_global Type name
    in
    let ctors_s =
      prlist_with_sep
        (fun () -> str "," ++ fnl () ++ str "  ")
        (fun id -> Id.print id)
        ctors
    in
    str "enum class "
    ++ struct_name
    ++ str " {"
    ++ fnl ()
    ++ str "  "
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
