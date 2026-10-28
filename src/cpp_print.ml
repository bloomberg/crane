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
open Common
open Minicpp
open Cpp_state
open Cpp_names
open Foreign_template

(** Escape a byte string for emission inside a double-quoted C++ string literal.

    A primitive Rocq [String] can contain any byte, including quotes,
    backslashes, newlines, and comment delimiters. Emitting those verbatim would
    terminate the literal early or otherwise corrupt (or inject into) the
    generated C++ source (CWE-116/CWE-94). We therefore escape the C++-
    significant characters and render every other non-printable byte as a
    three-digit octal escape ([\\ooo]) — octal is bounded to three digits, so
    unlike [\\x…] it cannot swallow a following hex digit. Note this differs from
    OCaml's [String.escaped], whose [\\ddd] escapes are decimal and would be
    misread by C++ as octal. *)
let escape_cpp_string (s : string) : string =
  let buf = Buffer.create (String.length s + 2) in
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string buf "\\\""
      | '\\' -> Buffer.add_string buf "\\\\"
      | '\n' -> Buffer.add_string buf "\\n"
      | '\r' -> Buffer.add_string buf "\\r"
      | '\t' -> Buffer.add_string buf "\\t"
      | c when Char.code c >= 0x20 && Char.code c < 0x7f -> Buffer.add_char buf c
      | c -> Buffer.add_string buf (Printf.sprintf "\\%03o" (Char.code c)) )
    s;
  Buffer.contents buf

(** Check if a lambda needs to capture variables from enclosing scope.
    A lambda needs [&] capture if its body references variables that are
    not lambda parameters and not locally declared within the body.
    [this] pointer references always require capture.

    Returns [(needs_capture, uses_this)].  Also recurses into nested lambdas:
    if a nested lambda captures from the outer lambda's scope, that counts
    as the outer lambda needing capture.

    @param params  the lambda's formal parameters as [(type, optional_name)] pairs
    @param body    the lambda's statement body
    @return [(needs_capture, uses_this)] where [needs_capture] is [true] when
            the lambda has free variables (so it must use [[&]] or [[=]]) and
            [uses_this] is [true] when the body references the enclosing [this] *)
let lambda_needs_capture
    (params : (Minicpp.cpp_type * Names.Id.t option) list)
    (body : Minicpp.cpp_stmt list) : bool * bool =
  let param_names =
    List.fold_left
      (fun acc (_, id_opt) ->
        match id_opt with Some id -> IdSet.add id acc | None -> acc)
      IdSet.empty params
  in
  let uses_this = ref false in
  let rec collect_from_expr (refs, decls) e =
    match e with
    | CPPvar id -> (IdSet.add id refs, decls)
    | CPPderef e -> collect_from_expr (refs, decls) e
    | CPPthis | CPPshared_from_this _ ->
      uses_this := true;
      (refs, decls)
    | CPPlambda {cl_params = inner_params; cl_body = inner_body; _} ->
      let inner_param_names =
        List.fold_left
          (fun acc (_, id_opt) ->
            match id_opt with Some id -> IdSet.add id acc | None -> acc)
          IdSet.empty (to_reversed inner_params)
      in
      let inner_refs, inner_decls =
        List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) inner_body
      in
      let inner_free =
        IdSet.diff inner_refs (IdSet.union inner_param_names inner_decls)
      in
      (IdSet.union refs inner_free, decls)
    | _ ->
      let acc = ref (refs, decls) in
      iter_expr_children
        ~on_expr:(fun e' -> acc := collect_from_expr !acc e')
        ~on_stmts:(fun stmts ->
          acc := List.fold_left collect_from_stmt !acc stmts)
        e;
      !acc
  and collect_from_stmt (refs, decls) stmt =
    match stmt with
    | Sraw raw_s -> collect_from_expr (refs, decls) (CPPraw raw_s)
    | Sdecl (id, _, _) -> (refs, IdSet.add id decls)
    | Sasgn (id, ty, e) ->
      let refs', decls' = collect_from_expr (refs, decls) e in
      ( match ty with
      | Declare _ | Declare_static _ -> (refs', IdSet.add id decls')
      | Existing -> (IdSet.add id refs', decls') )
    | Sassign_expr (lhs, e) ->
      (* The lhs is scanned for captures (referenced, not declared); the RHS
         is also scanned. *)
      let refs', decls' = collect_from_expr (refs, decls) lhs in
      collect_from_expr (refs', decls') e
    | Scustom_case (_, scrut, _, branches, _) ->
      List.fold_left
        (fun (r, d) (branch_vars, _, stmts) ->
          let branch_decls =
            List.fold_left (fun acc p -> IdSet.add p.cp_name acc) d branch_vars
          in
          List.fold_left collect_from_stmt (r, branch_decls) stmts)
        (collect_from_expr (refs, decls) scrut)
        branches
    | Sblock_custom (_, _, id, _, args, _, _) ->
      let refs', decls' =
        List.fold_left collect_from_expr (refs, decls) args
      in
      (refs', IdSet.add id decls')
    | Smatch (scrut, branches, default) ->
      let refs, decls = collect_from_expr (refs, decls) scrut.sc_expr in
      let acc =
        List.fold_left
          (fun acc br ->
            let acc =
              List.fold_left collect_from_expr acc br.smb_extra_conds
            in
            let refs', decls' = acc in
            let branch_decls =
              let d =
                List.fold_left
                  (fun d fb -> IdSet.add fb.fb_name d)
                  decls' br.smb_field_bindings
              in
              match br.smb_var with Some id -> IdSet.add id d | None -> d
            in
            List.fold_left
              collect_from_stmt (refs', branch_decls) br.smb_body)
          (refs, decls) branches
      in
      ( match default with
      | Some stmts -> List.fold_left collect_from_stmt acc stmts
      | None -> acc )
    | _ ->
      let acc = ref (refs, decls) in
      iter_stmt_children
        ~on_expr:(fun e -> acc := collect_from_expr !acc e)
        ~on_stmts:(fun stmts ->
          acc := List.fold_left collect_from_stmt !acc stmts)
        stmt;
      !acc
  in
  let all_refs, local_decls =
    List.fold_left collect_from_stmt (IdSet.empty, IdSet.empty) body
  in
  let bound_vars = IdSet.union param_names local_decls in
  let free_vars = IdSet.diff all_refs bound_vars in
  ((not (IdSet.is_empty free_vars)) || !uses_this, !uses_this)

(** Whether [e] is a lambda that captures nothing, or one such invoked at
    once with no argument: a value that names no variable of its scope, so
    the same wherever it is evaluated.  The printer writes [[]] for it, and
    the C++ compiler holds it to that. *)
let closed_lambda (e : Minicpp.cpp_expr) : bool =
  let captureless = function
    | CPPlambda {cl_params; cl_body; _} -> not (fst (lambda_needs_capture (to_reversed cl_params) cl_body))
    | _ -> false
  in
  match e with
  | CPPlambda _ -> captureless e
  | CPPfun_call (_, f, args) -> call_args args = [] && captureless f
  | _ -> false

(** Check if a cpp_expr contains any lambdas that need capture (have free
    variables). Used to determine if IIFE wrapping is needed for static inline
    initializers. Closed lambdas (with []) don't need IIFE wrapping. *)
let rec expr_contains_capturing_lambda (e : Minicpp.cpp_expr) : bool =
  match e with
  | CPPlambda {cl_params = params; cl_body = body; _} ->
    fst (lambda_needs_capture (to_reversed params) body)
    || List.exists stmt_contains_capturing_lambda body
  | _ ->
    let exception Found in
    ( try
        iter_expr_children
          ~on_expr:(fun e' ->
            if expr_contains_capturing_lambda e' then raise Found)
          ~on_stmts:(fun stmts ->
            if List.exists stmt_contains_capturing_lambda stmts then
              raise Found)
          e;
        false
      with Found -> true )

(** Statement counterpart of {!expr_contains_capturing_lambda}. *)
and stmt_contains_capturing_lambda (s : Minicpp.cpp_stmt) : bool =
  let exception Found in
  ( try
      iter_stmt_children
        ~on_expr:(fun e ->
          if expr_contains_capturing_lambda e then raise Found)
        ~on_stmts:(fun stmts ->
          if List.exists stmt_contains_capturing_lambda stmts then
            raise Found)
        s;
      false
    with Found -> true )

(** {2 Pretty-printing C++ syntax.} *)

(** The C++ source spelling of a binary operator. *)
let spell_binop = function
  | Beq -> "=="
  | Bneq -> "!="
  | Band -> "&&"
  | Bor -> "||"
  | Bassign -> "="

(** The C++ source spelling of a unary prefix operator. *)
let spell_unop = function Unot -> "!" | Uaddr -> "&"

(** The C++ source spelling of a [double] literal.

    [%h] renders the finite values as hexadecimal floating-point literals, which
    are exact, but renders the infinities and the NaNs as the bare words
    [infinity] and [nan] — not C++ literals at all, and in a declaration named
    after the constant they parse as a self-initialisation.  Those three cases
    are spelled with the compiler builtins instead, which need no include. *)
let spell_double (x : float) : string =
  if Float.is_nan x then "__builtin_nan(\"\")"
  else if x = Float.infinity then "__builtin_inf()"
  else if x = Float.neg_infinity then "-__builtin_inf()"
  else Printf.sprintf "%h" x

(** What is being written needs the header declaring the tagged union an
    inductive's alternatives are stored in, and its accessors. *)
let writes_variant () = writes (sn ()).variant_header



(** A name of Crane's runtime or of the standard library the configuration
    selects, written in full as {!Crane_rt} and {!Cpp_state.sn} spell it:
    every qualifier such a name has is a namespace. *)
let library_name s =
  match List.rev (Str.split (Str.regexp_string "::") s) with
  | base :: rev_namespaces ->
    Cpp_name.name (List.rev_map (fun ns -> Cpp_name.Namespace ns) rev_namespaces) base
  | [] -> Cpp_name.unqualified s

(** {!library_name} as a document. *)
let pp_library_name s = Cpp_name.pp (library_name s)

(** Print a library template applied: [label<s>].

    @param label  the template's name (e.g. [crane::fn] or [std::variant])
    @param s      the pre-rendered type argument list *)
let cpp_angle label s = pp_library_name label ++ str "<" ++ s ++ str ">"

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

(* Does a C++ type structurally mention an inductive that recurses through a
   boxed-element container?  If so it must be boxed as such a container's
   element, everywhere, for type-consistency. *)
let rec cpp_type_mentions_boxed_recursive t =
  match t with
  | Tglob (r, args, _) ->
    Table.is_boxed_recursive_ind r
    || List.exists cpp_type_mentions_boxed_recursive args
  | Tnamespace (_, t) -> cpp_type_mentions_boxed_recursive t
  | _ -> false

(* Suppresses [%elem] boxing while rendering a [crane_container_cast] target
   type.  That cast reconstructs a concrete container type from an erased
   [std::any] representation to match a CALLEE's declared parameter type; when
   the callee is a template function generic over the element (e.g.
   [nodupKeys<T1>]), its declaration never boxes (a bare [Tvar] never
   recurses), so the cast target must stay unboxed too, even though this
   call site's substituted element type (e.g. [Json_value]) would otherwise
   be judged boxed-recursive. *)
let suppress_elem_boxing = ref false

(** Render a custom type template, filling hole [i] with [hole i] and copying
    the text between holes verbatim.  [hole] returns [None] for an index the
    caller cannot fill, which is written back out as a placeholder of the same
    index -- nothing here knows better than the template did. *)
let render_type_template ~hole template =
  prlist
    (function
      | CCstring lit -> str lit
      | (CCty_arg i | CCelem i) as tok -> (
        match hole i with
        | Some pp -> pp
        | None ->
          str (Printf.sprintf "%%%s%d" (match tok with CCelem _ -> "elem" | _ -> "t") i) )
      | _ ->
        CErrors.anomaly
          (Pp.str "render_type_template: a type template has only type holes"))
    (type_template template)

(** Substitute the element hole of a wrapper template (e.g. ["immer::box<%t0>"])
    with an already-rendered element string. *)
let subst_wrapper_t0 wrapper elem_str =
  Pp.string_of_ppcmds
    (render_type_template
       ~hole:(fun i -> if i = 0 then Some (str elem_str) else None)
       wrapper)

(** Generate N placeholder type arguments (comma-separated ["int"]s). *)
let gen_placeholder_args n =
  String.concat ", " (List.init n (fun _ -> "int"))

(** Print a type variable by de Bruijn index, looking up in [vl]. Falls back to
    [T<n>] if index is out of range.

    Out of range covers both ends: a scope shorter than the type -- a
    declaration read before its own quantifiers are in hand -- leaves the
    variable unnamed, and so does index [0], which is what an unnamed variable
    carries.  Neither is an error here; the fallback spelling is.

    @param vl  list of type variable names (de Bruijn, 1-indexed from the right)
    @param i   1-based de Bruijn index into [vl] *)
let print_cpp_type_var vl i =
  match if i >= 1 then List.nth_opt vl (pred i) else None with
  | Some name -> pp_tvar name
  | None -> str "T" ++ int i


(** The type names the header introduces at file scope, planned with its
    layout ({!file_scope_types}); none in the implementation, which defines
    no type of its own.

    A definition written outside its struct ([Owner::f]) qualifies the plain
    names in its signature with [Owner::], which is right for a member and
    wrong for anything else.  An erased type-class field is a case of
    "anything else": the class is at file scope, so its erased face is a
    file-scope [using iptr = std::any;], and some unrelated struct's hoisted
    body must resolve [iptr] to that alias rather than claim it as a member it
    never declared.

    The set is only consulted to {i withhold} the qualifier, and a file-scope
    name that a struct also declares as a member still resolves to the
    member, because the body of an out-of-line definition is inside its
    class's scope. *)
let file_scope_type_names : CString.Set.t ref = State.cell State.Unit CString.Set.empty

let is_file_scope_type id =
  CString.Set.mem (Id.to_string id) !file_scope_type_names

(** Under [CRANE_CHECK_IR], the type names the file being written introduced
    at file scope, as written. *)
let file_scope_types_written : CString.Set.t ref = ref CString.Set.empty

let note_file_scope_name ctx name =
  if Probe.checking () && not ctx.rc_in_struct then
    file_scope_types_written := CString.Set.add (Pp.string_of_ppcmds name) !file_scope_types_written

(** The type name a declaration introduces, for the shapes whose spelling is
    settled here.  A struct records itself where it is printed. *)
let rec decl_type_name ctx = function
  | Dtemplate (_, _, inner) -> decl_type_name ctx inner
  | Dusing u -> Some (pp_global ctx Type u.du_name)
  | Dnspace (Some r, _) ->
    Some (str (String.capitalize_ascii (str_global ctx Type r)))
  | _ -> None

let note_file_scope_type ctx d = Option.iter (note_file_scope_name ctx) (decl_type_name ctx d)

(** The types [d] declares under a name no struct qualifies, each with how
    it is declared and the template parameters it is declared over, which an
    alias of it written elsewhere repeats: an alias, an enum, and a struct
    planned at namespace scope. *)
let rec declared_types ?(outer = []) = function
  | Dtemplate (tparams, _, inner) -> declared_types ~outer:(outer @ tparams) inner
  | Dusing u -> [(u.du_name, Cpp_ast.Alias_definition, outer @ u.du_tparams)]
  | Denum {de_ref; _} -> [(de_ref, Cpp_ast.Enum_definition, outer)]
  | Dstruct {ds_ref; ds_tparams; _} when Module_plan.is_namespace_scope_ref ds_ref ->
    [(ds_ref, Cpp_ast.Struct_definition, outer @ ds_tparams)]
  | Dnspace (Some r, ds) when Module_plan.is_namespace_scope_ref r -> List.concat_map (declared_types ~outer) ds
  | _ -> []

let stand_ins t =
  List.concat_map
    (function
      | Cpp_ast.Declared (Declaration {settled; _} | Absorbed {settled; _}) ->
        List.map
          (fun (target, definition, tparams) ->
            Cpp_ast.(global_alias (Alias_of_type {target = global_ref target; definition; tparams})) )
          (declared_types (settled :> cpp_decl))
      | Declared
          ( Fields _ | Modtype_concept _ | Global_alias _ | Assertion _ | Module_alias _ | Functor_alias _ | Derived_functor _
          | Forward_declaration _ ) ->
        []
      | Struct_of mp -> [Cpp_ast.(global_alias (Alias_of_module (module_ref mp)))] )
    (Cpp_ast.declared t)

(** The C++ token an {!Minicpp.obj_access} prints as. *)
let pp_obj_access = function Adot -> "." | Aarrow -> "->"

let ref_has_no_cpp_name = Ml_type_util.ref_has_no_cpp_name

(** The C++ identifiers appearing in [text], as whole tokens.  Used to tell
    whether a rendered type body really names a template parameter, which a
    structural walk over the type cannot: a custom mapping's replacement text
    may leave an argument unwritten. *)
let identifier_tokens text =
  let is_id c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
    || c = '_'
  in
  let out = ref [] and buf = Buffer.create 16 in
  let flush () =
    if Buffer.length buf > 0 then (
      out := Buffer.contents buf :: !out;
      Buffer.clear buf )
  in
  String.iter (fun c -> if is_id c then Buffer.add_char buf c else flush ()) text;
  flush ();
  !out

(** The type variable an alias template abstracts over, and the sentinel used
    to find out whether one is needed at all: rendering the constructor
    applied to it says whether the application is just a head plus this
    argument. *)
let ctor_alias_tvar = Minicpp.ctor_alias_tvar

(** A template synthesised to stand where a type constructor is written as a
    template template argument but has no template name of its own.

    A custom mapping is a {e spelling}, not a template name: [itree] maps to
    [std::shared_ptr<ITree<%t1>>], whose head is [std::shared_ptr] -- a
    template that, applied to the element, gives something else entirely.  A
    template template argument position needs a name that applies correctly,
    so one is introduced: an alias template, [template <typename _A> using
    ITree_tc = std::shared_ptr<ITree<_A>>;].

    A namespace-scope alias cannot name a function template's own parameter,
    so the carrier of [`{TFunctor (fun T => two T (FnBody T))}] -- whose body
    is [two<_CraneTcArg, T1<_CraneTcArg>>] -- has nowhere to be declared as a
    plain alias.  What can be declared there is a holder parameterised over
    exactly those names, with the alias as a member:

      template <template <typename> class _F0> struct C_h {
        template <typename _CraneTcArg> using c = two<_CraneTcArg, _F0<_CraneTcArg>>;
      };

    and the use site writes [C_h<T1>::template c], which is the dependent
    alias the [Tqualified] branch of the type printer already knows how to
    spell.  Its body has the captured names replaced by the holder's own, so
    two declarations that differ only in what they call their parameters
    share one holder. *)
type ctor_alias = {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : bool;
  ca_home : Names.ModPath.t option;
      (** The module struct it is declared in ({!ctor_alias_home}), or
          [None] for namespace scope. *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared, with the
          sentinel where the template's own parameter goes. *)
}

(** The module struct the template abbreviating [body], written in [file],
    has to be declared inside, if any: that of the module whose element is
    being written ({!Cpp_state.render_ctx}), where [body] names a global
    declared anywhere in the struct at namespace scope that encloses it --
    of that module, of one enclosing it, or of one nested in either.  Such
    a global is incomplete, or written bare, in front of that struct, and
    so means nothing at namespace scope; inside the module being written,
    every one declared ahead of the use is in scope.  In the implementation
    file, which writes no module struct, it is the struct whose members are
    defined out of line around it.  Where no module's element is being
    written, there is none. *)
let ctor_alias_home ctx body =
  match ctx.rc_module with
  | None -> None
  | Some cur ->
    let modpath_of = function
      | GlobRef.ConstRef c -> Some (Names.Constant.modpath c)
      | GlobRef.IndRef (kn, _) | GlobRef.ConstructRef ((kn, _), _) -> Some (Names.MutInd.modpath kn)
      | GlobRef.VarRef _ -> None
    in
    (* The struct at namespace scope [cur] is written in: what it declares,
       at any depth, is incomplete in front of it. *)
    let rec outermost mp =
      match mp with ModPath.MPdot (parent, _) when not (Table.is_modfile parent) -> outermost parent | _ -> mp
    in
    let struct_ = outermost cur in
    let rec inside mp =
      ModPath.equal mp struct_ || match mp with ModPath.MPdot (parent, _) -> inside parent | _ -> false
    in
    let names_struct =
      exists_cpp_type
        (function
          | Tglob (r, _, _) -> ( match modpath_of r with Some mp -> inside mp | None -> false )
          | _ -> false )
        body
    in
    if names_struct && not (Table.is_modfile cur) then Some cur else None

(** Where a template with home [home] is declared, and so the visibility
    its body is written in: the body of its home module, as planned, or
    outside every module body. *)
let ctor_alias_visibility = function
  | Some home -> (
    match Scope_plan.visibility home with
    | Some v -> v
    | None ->
      CErrors.anomaly
        Pp.(str "Crane: the module " ++ str (ModPath.to_string home) ++ str " has no planned visibility.") )
  | None ->
    Common.toplevel_visibility
      (List.rev (List.filter Table.is_modfile (Common.visible_mps (Common.current_visibility ()))))

(** The context a template with home [home] is written in, in the file
    being written: at
    namespace scope; in the header, inside its home's struct, a class
    template where the home's struct is one; in the implementation, beside
    the definitions of its home's members, which are written out of line and
    qualify what they name by the struct they are members of. *)
let ctor_alias_render_ctx ctx home =
  let start = file_start ctx.rc_file in
  match (home, ctx.rc_file) with
  | None, _ -> start
  | Some home, Common.Intf ->
    {start with rc_in_struct = true; rc_in_template = Scope_plan.templated home; rc_module = Some home}
  | Some home, Common.Impl -> {start with rc_scope = Scope_plan.of_module home; rc_module = Some home}

(** What a file writes that places the templates it writes: a declaration,
    or the fields of the eponymous record merged into a module's struct,
    which no declaration holds. *)
type written = Written_declaration of cpp_decl | Written_fields of GlobRef.t

(** What a file writes, in the module it is written in. *)
module Written = Hashtbl.Make (struct
  type t = ModPath.t * written

  (* [compare] rather than [=]: a NaN literal is equal to itself. *)
  let equal (mp, w) (mp', w') =
    ModPath.equal mp mp'
    &&
    match (w, w') with
    | Written_declaration d, Written_declaration d' -> compare d d' = 0
    | Written_fields r, Written_fields r' -> GlobRef.UserOrd.equal r r'
    | (Written_declaration _ | Written_fields _), _ -> false

  let hash (mp, w) =
    Hashtbl.hash
      ( ModPath.hash mp,
        match w with
        | Written_declaration d -> Hashtbl.hash_param 40 160 d
        | Written_fields r -> GlobRef.UserOrd.hash r )
end)

(** What planning reads off something a file writes: what it is, as the
    render reads it back, and the synthesised templates it writes, in the
    order written. *)
type ctor_aliases_read = {
  read_written : Written.key;
  read_aliases : ctor_alias list;
}

(** The synthesised templates each file writes, planned before either is
    rendered ({!Cpp.plan_ctor_aliases}): each file's, in the order it first
    writes them, and those each declaration it writes writes. *)
type ctor_alias_plan = {
  intf : ctor_alias list;
  impl : ctor_alias list;
  intf_writes : ctor_alias list Written.t;
  impl_writes : ctor_alias list Written.t;
}

(** [None] until the unit's templates are planned: a declaration rendered
    before then, for its text, or on its own
    ({!Extract_env.print_one_decl}), places none. *)
let ctor_alias_plan : ctor_alias_plan option ref = State.cell State.Unit None

(** Set while the templates some declaration or type writes are collected
    ({!ctor_aliases_found}). *)
let collecting_ctor_aliases = ref false

(** The templates spelled in the file being written, under [CRANE_CHECK_IR],
    or in what is being collected. *)
let ctor_aliases_spelled : ctor_alias list ref = ref []

let note_ctor_alias_spelled a =
  if (!collecting_ctor_aliases || Probe.checking ()) && not (List.mem a !ctor_aliases_spelled) then
    ctor_aliases_spelled := !ctor_aliases_spelled @ [a]

let start_ctor_alias_census () = ctor_aliases_spelled := []

(** Plan the templates each file writes, [written file] those of [file] in
    the order written: the header's, then the implementation's. *)
let plan_ctor_aliases written =
  let dedup l = List.fold_left (fun acc a -> if List.mem a acc then acc else acc @ [a]) [] l in
  let planned file =
    let reads = written file in
    let writes = Written.create 64 in
    List.iter
      (fun r ->
        if not (Written.mem writes r.read_written) then Written.add writes r.read_written r.read_aliases )
      reads;
    (dedup (List.concat_map (fun r -> r.read_aliases) reads), writes)
  in
  let intf, intf_writes = planned Common.Intf in
  let impl, impl_writes = planned Common.Impl in
  ctor_alias_plan := Some {intf; impl; intf_writes; impl_writes}

(** The name of [alias]: a function of its body alone, not a counter.  The
    two files declare the aliases they write independently, so the same body
    has to be the same name in both, and every use names what it meant;
    repeating a [using] with the same definition is legal, which is what
    lets both declare it.  A holder's body names the holders written inside
    it by their names, which are functions of their own bodies, so no order
    of spelling enters any name.  The body is written where the template is
    declared, with the holder's own parameters for what it captures, so the
    digest is over text that is already canonical. *)
let ctor_alias_name a =
  let kind = if a.ca_holder then "_tch_" else "_tc_" in
  a.ca_base ^ kind ^ String.sub (Digest.to_hex (Digest.string a.ca_body)) 0 16

(** The declaration of [alias].  A holder's parameters are the captured
    names its body writes: one written applied to the alias's own argument
    is a type constructor ([CraneFk]), one written bare a type ([CranePk]),
    a plain family the declaration deapplied. *)
let ctor_alias_declaration a =
  let name = ctor_alias_name a in
  if not a.ca_holder then
    str "template <typename " ++ str ctor_alias_tvar ++ str "> using " ++ str name ++ str " = "
    ++ str a.ca_body ++ str ";"
  else
    let names = identifier_tokens a.ca_body in
    let rec params i =
      let f = Id.to_string (Generated_name.indexed "F" i)
      and p = Id.to_string (Generated_name.indexed "P" i) in
      if List.mem f names then (str "template <typename> class " ++ str f) :: params (i + 1)
      else if List.mem p names then (str "typename " ++ str p) :: params (i + 1)
      else []
    in
    str "template <"
    ++ prlist_with_sep (fun () -> str ", ") (fun p -> p) (params 0)
    ++ str "> struct " ++ str name ++ str " { template <typename " ++ str ctor_alias_tvar
    ++ str "> using c = " ++ str a.ca_body ++ str "; };"

(** The templates the file [file] declares, each once, in the order planned:
    the aliases it writes, and, in the header, every holder the unit writes.

    A holder is a struct, and a struct may be defined once.  An alias may be
    declared in whichever file writes the use, because repeating a [using]
    with the same definition is legal; repeating a [struct] is not, so the
    header, the one file everything sees, declares every holder. *)
let ctor_aliases_declared_in ~file =
  let declared =
    match (!ctor_alias_plan, file) with
    | None, _ -> []
    | Some plan, Common.Intf -> plan.intf @ List.filter (fun a -> a.ca_holder) plan.impl
    | Some plan, Common.Impl -> List.filter (fun a -> not a.ca_holder) plan.impl
  in
  List.fold_left
    (fun acc a ->
      if List.exists (fun a' -> String.equal (ctor_alias_name a') (ctor_alias_name a)) acc then acc else acc @ [a] )
    [] declared


(** Under [CRANE_CHECK_IR], the templates the file [file] spelled must be
    the ones planned for it. *)
let check_ctor_alias_plan ~file =
  if Probe.checking () then begin
    let planned =
      match (!ctor_alias_plan, file) with
      | None, _ -> []
      | Some plan, Common.Intf -> plan.intf
      | Some plan, Common.Impl -> plan.impl
    in
    let spelled = !ctor_aliases_spelled in
    ctor_aliases_spelled := [];
    let describe a =
      Printf.sprintf "%s %s%s" (if a.ca_holder then "holder" else "alias") a.ca_body
        (match a.ca_home with Some mp -> " in " ^ ModPath.to_string mp | None -> "")
    in
    let missing l l' = List.filter (fun a -> not (List.mem a l')) l in
    match (missing spelled planned, missing planned spelled) with
    | [], [] -> ()
    | unplanned, unspelled ->
      Probe.violation "constructor aliases"
        Pp.(
          str "the " ++ str (Common.file_name file) ++ str " spells "
          ++ prlist_with_sep pr_comma (fun a -> str (describe a)) unplanned
          ++ str " unplanned, and does not spell "
          ++ prlist_with_sep pr_comma (fun a -> str (describe a)) unspelled
          ++ str " planned" )
  end

(** The constructor a type constructor position writes: an applied type
    there is the eta-expansion of the constructor, whose head is what the
    position wants. *)
let tyctor_constructor = function Tapply (head, _) -> head | t -> t

(** [str_of] up to its first template argument list. *)
let cut_at_argument_list str_of =
  match String.index_opt str_of '<' with
  | Some i -> String.sub str_of 0 i
  | None -> str_of

(* Whether [probe], a type constructor applied to the sentinel, is written as
   a template name applied to the sentinel alone, read off its structure and
   not off its rendering; [None] where the structure does not say.  A custom
   mapping is that name where its text is a head with no argument list of its
   own, then the sentinel's hole, then the list's close; any other global is
   its name applied to its arguments. *)
let rec applied_to_sentinel_alone = function
  | Tid (_, args) | Tid_external (_, args) -> Some (args = [Thole])
  | Tnamespace (_, t) -> applied_to_sentinel_alone t
  | Tglob (r, args, []) -> (
    match find_custom_opt r with
    | None -> Some (args = [Thole])
    | Some template -> (
      match type_template template with
      | [CCstring head; CCty_arg i; CCstring ">"] when List.nth_opt args i = Some Thole ->
        Some (String.index_opt head '<' = Some (String.length head - 1))
      | tokens -> if List.exists (function CCelem _ -> true | _ -> false) tokens then None else Some false ) )
  | _ -> None

(** The C++ name of the field a projection reads.

    It is the projection's own label, escaped the same way the field was when
    the record's struct was written -- a record with a field named [this] has
    one named [this_], and a projection of it has to say so too. *)
let projection_field_name (r : GlobRef.t) : string =
  Common.modular_rename Term (Label.to_id (label_of_r r))


(** Whether a definition whose eligibility the seam decided
    ({!Cpp_erasure.decide_constexpr}) may be [constexpr]. *)
let may_be_constexpr = function
  | Eligible -> true
  | Ineligible -> false
  | Undecided ->
    CErrors.anomaly (str "a definition reached the printer with its constexpr eligibility undecided")

(** Whether a rendered document writes a qualifier anywhere in it, its
    template arguments included. *)
let writes_qualifier doc =
  List.exists
    (function
      | Cpp_name.Scope _ -> true
      | Cpp_name.Foreign_text text | Cpp_name.Untagged text -> String.contains text ':')
    (Cpp_name.written doc)

(** What a type is as the qualifier of a member type named through it: a
    template parameter, which defers the lookup, when it is one or is a chain
    of member types through one; a struct otherwise. *)
let rec member_kind = function
  | Tvar _ | Tinstance _ -> fun s -> Cpp_name.Parameter s
  | Tqualified (t, _) -> member_kind t
  | _ -> fun s -> Cpp_name.Class s

(** The qualifiers a member of the struct being defined out of line is
    written with when it is named outside that struct's body ([Tid] and
    [Tpromoted]), or [None] where it is written bare. *)
let member_scopes (ctx : render_ctx) id =
  match ctx.rc_scope with
  | Some sc when (not ctx.rc_in_struct) && not (is_file_scope_type id) ->
    Some (List.map (fun s -> Cpp_name.Class s) sc.Scope_plan.qualifier)
  | _ -> None

(** A type's name as the type printer writes it: the qualifiers written in
    front of it, the name itself, whether a dependent qualifier in it asks
    for [typename], and whether it is followed by template arguments that
    need the [template] disambiguator. *)
type written_head = {
  outer : Cpp_name.scope list;
  head : Cpp_name.t;
  typename : bool;
  template_keyword : bool;
}

let unqualified_head head = {outer = []; head; typename = false; template_keyword = false}

let needs_typename (ctx : render_ctx) n = ctx.rc_in_template && Cpp_name.is_qualified n

(** The head of the type [Tglob (r, tys, _)] that no custom mapping inlines,
    [applied] when [tys] is not empty. *)
let glob_head ctx r ~applied =
  let bare = inductive_type_name ctx r in
  let enclosing = struct_scopes_for ctx r bare @ global_scopes_for r bare in
  (* The wrapper qualifier is the last resort: the two qualifiers above say
     where the name lives whenever they say anything, and stacking this one
     on top of them spells the same struct twice. *)
  let name = if enclosing = [] then wrapper_qualified_type_name ctx r bare else bare in
  {outer = enclosing; head = name; typename = needs_typename ctx name; template_keyword = applied}

(** The head of the inductive type [Tnamespace (r, Tglob (r, args, _))],
    [applied] when [args] is not empty.

    DESIGN: Namespace-qualified types for inductive types. Rocq's
    inductives live in wrapper structs (e.g., type 'list' in struct 'List').
    Local inductives don't need namespace wrapping; non-local ones get the
    prefix. EXCEPTION: Eponymous records are merged into the module struct,
    so we use just the capitalized name without namespace qualification
    (CHT, not CHT::cHT). *)
let inductive_head ctx r ~applied =
  let name, needs_ns = inductive_name ctx r in
  let class_ s = Cpp_name.Class s in
  let type_name = global_name ctx Type r in
  (* Check eponymous record FIRST because they can also be local *)
  if is_eponymous_record_cached r then
    let cap_name = Common.pp_type_name_capitalized r in
    if Common.get_force_cross_file_qualification () && not (local_at ctx r)
    then unqualified_head (Cpp_name.name [class_ cap_name] cap_name)
    else unqualified_head (Cpp_name.unqualified cap_name)
  else if is_enum_cached r then
    (* Enum types at global scope need no struct qualification. Enums inside
       structs (e.g., Comparison::cmp) need it. *)
    let qualifier = if is_global_scope_enum_cached r then [] else struct_scopes_for ctx r type_name in
    {(unqualified_head (enum_name type_name r)) with outer = qualifier}
  else if Cpp_name.is_qualified type_name then
    let cap =
      if Common.get_force_cross_file_qualification () then capitalize_base type_name else type_name
    in
    let cap =
      if is_merged_inductive r then dedup_tail ~allow_bare:(Table.modular () && not needs_ns) cap
      else cap
    in
    (* The qualified name is relative to the enclosing module struct, so
       out-of-line definitions -- whose return type precedes the qualified
       function name, and so sits outside that struct's scope -- need the
       struct prefix in front of it. *)
    { outer = struct_scopes_for ctx r cap;
      head = cap;
      typename = needs_typename ctx cap;
      template_keyword = applied && ctx.rc_in_template }
  else if is_merged_inductive r && not (local_at ctx r) then
    (* A local inductive is a sibling member of the enclosing module struct,
       so it is in scope under its own name; the merged-wrapper spelling
       ([Opt] for [opt]) names nothing there. *)
    let cap = capitalize_initial type_name in
    if needs_ns && Table.modular () then unqualified_head (Cpp_name.inside cap class_ cap)
    else
      (* A file whose declarations were folded into a struct keeps its
         inductives there too, so the struct is their scope -- the same
         qualifier a call into that file already gets. *)
      let qualified = if Cpp_state.is_nested_struct_ref r then wrapper_qualify r cap else cap in
      if not (Cpp_name.equal qualified cap) then unqualified_head qualified
      else {(unqualified_head cap) with outer = global_scopes_for r cap}
  else if needs_ns then unqualified_head (Cpp_name.inside name class_ type_name)
  else {(unqualified_head type_name) with outer = global_scopes_for r type_name}

(** [h] written, the [typename] it asks for only if [lead]. *)
let pp_written_head ~lead h =
  (if lead && h.typename then str "typename " else mt ())
  ++ Cpp_name.pp_scopes h.outer
  ++ Cpp_name.pp ~template_keyword:h.template_keyword h.head

(** Whether text no name was written through -- an external name, a custom
    mapping's replacement -- qualifies a name into something other than one
    of the included libraries' namespaces: the identifier in front of each
    [::] is the qualifier. *)
let text_names_into_a_struct text =
  let libraries = ["std"; "crane"; (sn ()).ns] in
  let n = String.length text in
  let is_ident c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'
  in
  let rec scan i =
    if i + 1 >= n then false
    else if text.[i] = ':' && text.[i + 1] = ':' then
      let stop = ref i in
      while !stop > 0 && is_ident text.[!stop - 1] do decr stop done;
      let qualifier = String.sub text !stop (i - !stop) in
      if List.mem qualifier libraries then scan (i + 2) else true
    else scan (i + 1)
  in
  scan 0

(** Whether one thing a rendering writes ({!Cpp_name.written}) is a qualifier
    naming into a struct or a template parameter rather than a namespace. *)
let writes_into_a_struct = function
  | Cpp_name.Scope (Cpp_name.Namespace _ | Cpp_name.Global) -> false
  | Cpp_name.Scope (Cpp_name.Class _ | Cpp_name.Parameter _) -> true
  | Cpp_name.Foreign_text text | Cpp_name.Untagged text -> text_names_into_a_struct text

let scopes_name_into_a_struct = List.exists (fun s -> writes_into_a_struct (Cpp_name.Scope s))

(** Whether the head [h] is written through a struct or a template
    parameter. *)
let head_names_into_a_struct h =
  scopes_name_into_a_struct (h.outer @ Cpp_name.scopes h.head)
  || match h.head with Cpp_name.Foreign text -> text_names_into_a_struct text | Cpp_name.Name _ -> false

(** The spelling of an external type's name: the configured library's vector
    for the standard one. *)
let external_type_name id_s =
  if String.equal id_s "std::vector" && (sn ()).ns <> "std" then "bsl::vector" else id_s

(** Under [CRANE_CHECK_IR], that the position a printer is given is the one
    installed where it is: printers not given it yet read it there. *)
let check_position ctx =
  if Probe.checking () && not (ctx == !render_ctx || ctx = !render_ctx) then
    Probe.violation "threaded positions" (str "a printer is given another position than the one it is at")

(** Whether the type [t] writes a qualifier into a struct or a template
    parameter, asked of the type rather than of its rendering: each name is
    the one {!pp_cpp_type} writes, from the same heads, at the position
    [ctx].  [None] where only the rendering can tell -- an
    expression's type, and a type constructor named as a template argument,
    which may be written through a synthesised alias ({!ctor_alias_at}). *)
let type_names_into_a_struct ctx t =
  let rec names_into t =
  let any ts =
    List.fold_left
      (fun acc t -> match acc with Some true | None -> acc | Some false -> names_into t)
      (Some false) ts
  in
  let ( ||? ) b rest = if b then Some true else rest in
  match t with
  | Tvar _ | Tinstance _ | Tvoid | Thole | Tdecltype_auto | Terased _ | Tany | Topaque -> Some false
  | Tunresolved -> None
  | Tpromoted id -> Some (scopes_name_into_a_struct (Option.default [] (member_scopes ctx id)))
  | Tid (id, args) -> scopes_name_into_a_struct (Option.default [] (member_scopes ctx id)) ||? any args
  | Tid_external (id_s, args) -> text_names_into_a_struct (external_type_name id_s) ||? any args
  | Tglob (r, tys, _) -> (
    match find_custom_opt r with
    | Some s when to_inline r -> text_names_into_a_struct s ||? any tys
    | _ ->
      head_names_into_a_struct (glob_head ctx r ~applied:(tys <> [])) ||? any tys )
  | Tnamespace ((GlobRef.IndRef _ as r), Tglob (r', args, _)) when globref_equal r r' ->
    head_names_into_a_struct (inductive_head ctx r' ~applied:(args <> [])) ||? any args
  | Tnamespace _ | Tqualified _ | Tapply (Tqualified _, _) -> Some true
  | Tapply (head, args) -> any (head :: args)
  | Tfun (dom, cod) -> any (cod :: dom)
  | Tnondeduced t | Tref (_, t) | Tptr t | Tconst t | Tshared_ptr t -> names_into t
  | Trebind (h, x) -> any [h; x]
  | Tvariant (_, tys) -> any tys
  | Texpr_type _ | Ttyctor _ | Tdecay _ | Tauto -> None
  in
  names_into t

(** Whether [d], written as a member of a struct body, is a static function
    declaration ending at its semicolon: no body, no initialiser, no
    template head. *)
let is_static_member_declaration (d : cpp_decl) =
  match d with Dfun {df_shape = Ddecl _; _} -> true | _ -> false

(** Whether the function declaration [d] writes a qualifier into a struct or
    a template parameter ({!type_names_into_a_struct}): in its name, result
    and parameters, and in its template head -- a concept constraining a
    parameter, a type a parameter defaults to or a callable one is invoked
    with.  [None] for anything else, a declaration under a [requires]
    clause, or where only its rendering can tell. *)
let rec declaration_names_into_a_struct ctx (d : cpp_decl) =
  let any_type ts =
    List.fold_left
      (fun acc t -> match acc with Some false -> type_names_into_a_struct ctx t | _ -> acc)
      (Some false) ts
  in
  let names_through n = head_names_into_a_struct (unqualified_head n) in
  match d with
  | Dfun {df_path = {dp_outer; dp_inner}; df_ret; df_shape = Ddecl params; _} ->
    let path = dp_outer :: dp_inner in
    if List.exists (fun (n, _) -> names_through (global_name ctx Type n)) path then Some true
    else any_type ((df_ret :: List.map snd params) @ List.concat_map snd path)
  | Dtemplate (tparams, None, inner) ->
    let concept_names_through c = (not (class_concept_held_back ctx c)) && names_through (concept_name ctx c) in
    let param_types (tt, _) =
      match tt with
      | TTtypename | TTtemplate _ -> []
      | TTtypename_default t -> [t]
      | TTfun (dom, cod) -> cod :: dom
      | TTinvocable (invs, cod) -> cod :: List.concat_map (fun inv -> List.map snd inv.inv_args) invs
      | TTconcept (_, args) -> args
    in
    if List.exists (function TTconcept (c, _), _ -> concept_names_through c | _ -> false) tparams
    then Some true
    else (
      match any_type (List.concat_map param_types tparams) with
      | Some false -> declaration_names_into_a_struct ctx inner
      | answer -> answer )
  | _ -> None

(** Pretty-print a MiniCpp type as C++ source text.

    @param par  whether to parenthesize (for precedence in function types)
    @param vl   type variable names for de Bruijn index lookup

    A {!Minicpp.Tpromoted} reaching the printer is one no resolution map
    claimed, so it is rendered as a member of the enclosing struct: the bare
    name inside a struct body, [StructName::id] outside one. *)
let rec pp_cpp_type ?(lead = true) ctx par vl t =
  check_position ctx;
  let rec pp_rec ?(lead = true) par t =
    (* The [typename] a dependent qualifier needs, unless the caller is placing
       this type somewhere the keyword would be wrong: as the base of a longer
       qualified chain, which spells the single leading one itself, or in front
       of a value.  Only this outermost type is affected -- every recursive
       call below takes the default -- so the keywords inside template
       arguments stay where they belong. *)
    let leading_typename = if lead then str "typename " else mt () in
    match t with
    | Tvar (Tv_index (i, None)) -> print_cpp_type_var vl i
    | Tinstance (id, _) -> Id.print id
    | Tpromoted id ->
      (* A [Type]-valued type-class field ([m_carrier] of [Monoid], [Obj] of
         [PreCategory]) cannot be a struct member in C++, so it becomes a type
         requirement in the concept and a [using] declaration in the instance
         struct.  Here it is a reference to that declaration:

           in struct:  using Obj = std::any;
           in .cpp:    DepRecord::Obj my_var = ...;

         The qualifier is only correct for a struct that declares the member.
         An erased field also gets a file-scope [using] of the same name, and a
         hoisted body whose owner is some other struct must resolve to that
         one, not to a member that does not exist. *)
      ( match member_scopes ctx id with
      | Some scopes -> Cpp_name.pp_scopes scopes ++ Id.print id
      | None -> Id.print id )
    | Tvar (Tv_index (_, Some id) | Tv_named id) -> Id.print id
    (* Tid for local type references (e.g., nested structs inside modules).
       These don't need GlobRef qualification, just simple Id references. Can be
       parameterized like generic types: Leaf<int>. When generating
       out-of-struct definitions, prepend struct name. *)
    | Tid (id, args) ->
      let scopes = Option.default [] (member_scopes ctx id) in
      Cpp_name.pp_scopes scopes ++ Id.print id
      ++ (match args with [] -> mt () | _ -> str "<" ++ pp_list (pp_rec false) args ++ str ">")
    | Tnondeduced t ->
      cpp_angle "std::type_identity_t" (pp_rec false t)
    | Trebind (h, x) ->
      writes_obj ();
      cpp_angle Crane_rt.rebind (pp_list (pp_rec false) [ h; x ])
    | Thole -> str ctor_alias_tvar
    | Tref (Forwarding, t) -> pp_rec false t ++ str "&&"
    | Texpr_type e -> str "decltype(" ++ pp_cpp_expr ctx ([], Id.Set.empty) [] e ++ str ")"
    | Tdecltype_auto -> str "decltype(auto)"
    | Tid_external (id_s, args) ->
      let id_s =
        if String.equal id_s "std::vector" then begin
          writes_standard "vector";
          external_type_name id_s
        end else if String.equal id_s Crane_rt.constant_tc then begin
          writes_obj ();
          id_s
        end else id_s
      in
      ( match args with
        | [] -> str id_s
        | _ -> str id_s ++ str "<" ++ pp_list (pp_rec false) args ++ str ">" )
    (* Erasure markers should never reach the C++ output.  When one does
       survive -- a template argument of [SigT<nat, dummy_prop>] -- it is
       rendered as the erased type. *)
    | Terased _ ->
      writes_obj ();
      pp_library_name Crane_rt.obj
    | Tglob (r, tys, args) ->
      ( match find_custom_opt r with
      | Some s when to_inline r ->
        let cmds =
          term_template (custom_template_with_args s (List.length tys))
        in
        pp_custom
          ~container:r ctx (Pp.string_of_ppcmds (GlobRef.print r) ^ " := " ^ s)
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
        pp_written_head ~lead (glob_head ctx r ~applied:(tys <> []))
        ++ (match tys with [] -> mt () | l -> str "<" ++ pp_list (pp_rec false) l ++ str ">") )
    | Tfun (d, c) ->
      writes (Table.Runtime Crane_rt.fn_header);
      cpp_angle
        Crane_rt.fn
        (pp_rec false c ++ pp_par true (pp_list (pp_rec false) d))
    | Tref (Lvalue, t) -> pp_rec false t ++ str "&"
    | Tptr t -> pp_rec false t ++ str "*"
    | Tconst t -> str "const " ++ pp_rec false t
    | Tnamespace (r, t) ->
      ( match (r, t) with
      | GlobRef.IndRef _, Tglob (r', args, _)
        when globref_equal r r' ->
        pp_written_head ~lead (inductive_head ctx r' ~applied:(args <> []))
        ++ (match args with [] -> mt () | args -> str "<" ++ pp_list (pp_rec false) args ++ str ">")
      | _ ->
        (* Fallback: generic namespace-qualified type *)
        leading_typename
        ++ Cpp_name.pp_qualifier (fun s -> Cpp_name.Class s) (fst (inductive_name ctx r))
        ++ pp_rec false t )
    | (Tqualified _ | Tapply (Tqualified _, _)) as qualified_ty ->
      (* An associated type may itself be an alias template — the carrier of a
         higher-kinded class parameter, [typename I::template C<A>].  It is
         spelled like a plain associated type but for the [template]
         disambiguator and the argument list, so both share this arm. *)
      let base_ty, nested_id, targs =
        match qualified_ty with
        | Tqualified (b, n) -> (b, n, [])
        | Tapply (Tqualified (b, n), a) -> (b, n, a)
        | _ -> assert false
      in
      (* DESIGN: Template-dependent type access like 'typename M::Key::t'.
         C++ templates require 'typename' to access nested types from
         dependent base types.  Nested Tqualified chains (e.g.,
         [Tqualified(Tqualified(Tvar I, base_category), Obj)]) are flattened
         so only a single leading [typename] is emitted — writing
         [typename typename I::base_category::Obj] is invalid C++.

         The chain renderer writes the head of a [Tnamespace] or [Tglob]
         without its [typename] — the outer [Tqualified] provides the single
         leading [typename].  Template arguments inside the base type (e.g.,
         [pair<typename X::t, T1>]) are rendered normally, preserving inner
         [typename] keywords where needed. *)
      (* Render the base of the chain with the ordinary type printer -- it
         already knows how to qualify an inductive with its wrapper struct and
         where the [template] disambiguator goes -- then drop the [typename]
         it may prepend, since the enclosing [Tqualified] emits the single
         leading one. *)
      let pp_chain_base ty = pp_rec ~lead:false false ty in
      let rec pp_qualified_chain ty =
        match ty with
        | Tqualified (inner_ty, id) ->
          pp_qualified_chain inner_ty ++ str "::" ++ Id.print id
        | ty -> pp_chain_base ty
      in
      leading_typename
      ++ Cpp_name.pp_type_qualifier (member_kind base_ty) (pp_qualified_chain base_ty)
      ++ ( if targs = [] then Id.print nested_id
           else
             str "template " ++ Id.print nested_id
             ++ str "<" ++ pp_list (pp_rec false) targs ++ str ">" )
    | Tapply (head, args) ->
      (* A non-dependent alias template: the head names it outright.

         Unless the head has no name.  A constructor [Crane Extract Skip]
         removed renders as nothing, and nothing followed by [<args>] is not a
         template-id with an elided name, it is a syntax error -- and one that
         then gets wrapped by whatever reads the result, which is how
         [crane_event_as<<typename I::PROV>>] happened.  A removed constructor
         is the identity on what it was applied to, so its arguments are the
         whole of what there is to write. *)
      ( match head with
      | Tglob (r, _, _) when ref_has_no_cpp_name r ->
        pp_list (pp_rec false) args
      | _ ->
        (* Non-dependent is what the head usually is, but not always: a
           carrier whose body names a template parameter of the enclosing
           declaration has no namespace-scope alias to be, so it is
           synthesised as a member of a holder, spelled [H<T1>::template c].
           That is a dependent qualified name, and applying it yields a type,
           which needs the [typename] the {!Tqualified} arm above would have
           given it.  Whether a holder was needed is decided by which names
           the body actually {e writes}, which is not a property of the type's
           shape, so the head says how it was written ({!tyctor_head}). *)
        let head_pp, dependent_member =
          match head with
          | Ttyctor t -> tyctor_head t
          | _ -> (pp_rec false head, false)
        in
        (if dependent_member then leading_typename else mt ())
        ++ head_pp ++ str "<" ++ pp_list (pp_rec false) args ++ str ">" )
    | Tvariant (Inline_variant, tys) ->
      writes_variant ();
      cpp_angle (sn ()).variant (pp_list (pp_rec false) tys)
    | Tvariant (Shared_variant, tys) ->
      writes (Table.Runtime Crane_rt.shared_variant_header);
      cpp_angle Crane_rt.shared_variant (pp_list (pp_rec false) tys)
    | Tshared_ptr t -> (
      let pointer () =
        writes_standard "memory";
        cpp_angle (sn ()).shared_ptr (pp_rec false t)
      in
      match Pointer_slot.of_pointee t with
      | Pointer_slot.Shared ->
        writes (Table.Runtime Crane_rt.shared_variant_header);
        cpp_angle Crane_rt.shared_box (pp_rec false t)
      | Pointer_slot.At_instantiation ->
        writes (Table.Runtime Crane_rt.shared_variant_header);
        cpp_angle Crane_rt.shared_or (pp_rec false t ++ str ", " ++ pointer ())
      | Pointer_slot.Pointer -> pointer () )
    | Tvoid -> str "void"
    | Tunresolved ->
      (* There is no C++ spelling for "no type was determined"; emitting a
         placeholder would hand the user a file that does not compile, with
         nothing to say where it came from. *)
      CErrors.anomaly (Pp.str "pp_cpp_type: Tunresolved reached the printer")
    | Tany | Topaque ->
      (* [Topaque] is a type we could not pin down; [std::any] is the only
         spelling that accepts whatever it turns out to be. *)
      writes_obj ();
      pp_library_name Crane_rt.obj
    | Ttyctor t -> fst (tyctor_head t)
    | Tauto -> str "auto"
    | Tdecay t ->
      writes_standard "type_traits";
      cpp_angle "std::decay_t" (pp_rec false t)
  (* A type constructor written as a template template argument, and
     whether it is written as a member of a dependent qualifier -- a
     higher-kinded carrier's [_tcI0::template M], or a holder's
     [H<T1>::template c] -- which, applied, needs [typename]. *)
  and tyctor_head t =
    (* A template template argument is the bare template name.  Ask the type
       for its head rather than rendering it applied and cutting the result
       back: an applied type is a head plus arguments, and for a custom
       mapping the head is the template's own leading text.  An applied type
       here is the eta-expansion of the constructor: its head is what the
       position wants. *)
    let t = tyctor_constructor t in
    match ctor_alias_at ctx vl t with
    | Some (alias, args) ->
      note_ctor_alias_spelled alias;
      let name = ctor_alias_name alias in
      if alias.ca_holder then (str (name ^ "<" ^ String.concat ", " args ^ ">::template c"), true)
      else (str name, false)
    | None -> (
      match t with
      | Tqualified (base, id) ->
        (* A dependent alias template -- the carrier of a higher-kinded class
           parameter.  Here it names a template rather than a type, so the
           leading [typename] a qualified type would take is wrong; what the
           member needs is [template], which tells the parser the dependent
           name is a template before any argument list is in sight
           ([temp.names]/5).  Without it the name parses as a non-template
           member and the position rejects it. *)
        (pp_rec ~lead:false false base ++ str "::template " ++ Id.print id, true)
      | Tglob (r, _ :: _, _) ->
        ( ( match find_custom_opt r with
          | Some template when String.contains template '%' -> (
            match type_template template with
            | CCstring lit :: _ -> str (cut_at_argument_list lit)
            | _ -> str (cut_at_argument_list template) )
          | Some template -> str (cut_at_argument_list template)
          | None -> pp_rec false (Tglob (r, [], [])) ),
          false )
      | _ -> (str (cut_at_argument_list (Pp.string_of_ppcmds (pp_rec false t))), false) )
  in
  (pp_rec ~lead par t)

(** The template synthesised for the type constructor [t], written as a
    template template argument, if it has no template name of its own, with
    the arguments a holder is applied to where it is written.

    A constructor applied to the sentinel is both the test and the alias body:
    where the rendering comes out as a head plus that one argument, the head
    is a template name and naming it is enough; where it does not, there is
    no head to name and an alias template is introduced.  [itree] is
    [std::shared_ptr<ITree<%t1>>] and a composite Rocq carrier is
    [std::pair<_CraneTcArg, Box<_CraneTcArg>>]; neither can be cut back, and
    the same reading of the same rendering covers both.

    A carrier built by the front end already has the sentinel standing where
    its argument goes -- it is the abstraction, not an application of one.  A
    custom mapping arrives applied to its real arguments, so the sentinel is
    put in the carrier's place first. *)
and ctor_alias_at ctx vl t =
  let custom () =
    match t with
    | Tglob (r, (_ :: _ as args), _) when find_custom_opt r <> None ->
      let fixed = List.filteri (fun i _ -> i < List.length args - 1) args in
      ctor_alias_of_probe ctx vl ~base:(Common.pp_global_name Type r) (Tglob (r, fixed @ [Thole], []))
    | _ -> None
  in
  if exists_cpp_type (fun s -> s = Thole) t then
    match ctor_alias_of_probe ctx vl ~base:"crane_carrier" t with
    | Some _ as alias -> alias
    | None -> custom ()
  else custom ()

(** The template synthesised for [probe], a type constructor applied to the
    sentinel, if its rendering is not a head applied to the sentinel.

    The body is rendered where the template is declared ({!ctor_alias_visibility}),
    because that is where a [using] is read; every name it writes
    has to mean there what it means at the use. *)
and ctor_alias_of_probe ctx vl ~base probe =
  (* Every node of a type, in the order written, a type constructor's
     included: a carrier nested in the body as a template template argument
     is written through its own template, whose arguments name what it
     names. *)
  let visit t f = ignore (exists_cpp_type (fun t -> f t; false) t) in
  (* The template parameters of the enclosing declaration that the body
     names, each as the body writes it.  An alias whose body mentions one
     cannot live at namespace scope, so those are what the holder abstracts
     over. *)
  let captured probe =
    let seen = ref [] in
    visit probe (function
      | Tvar (Tv_index (i, _) as v) when not (List.mem_assoc i !seen) -> seen := !seen @ [(i, v)]
      | _ -> () );
    !seen
  in
  let written_var v = Pp.string_of_ppcmds (pp_cpp_type ctx false vl (Tvar v)) in
  (* A captured parameter is named {e applied} to the alias's own
     argument -- that is what makes the body an abstraction rather than a
     type, and it is what lets the holder declare every parameter it
     takes as a type constructor.  A variable the body names bare is not
     a carrier parameter; it is a type the body mentions, and mentioning
     it at the use site writes a name from the declaration's quantifier.
     An instance method's body is emitted without that quantifier, so
     [crane_carrier_tch<T1>] there names a scope the function is not in.
     What the body has instead is the erasure it was emitted under, and
     [std::any] is how the rest of it already spells that. *)
  let applied_vars =
    let seen = ref [] in
    visit probe (function Tapply (Tvar (Tv_index (i, _)), _) -> seen := i :: !seen | _ -> ());
    !seen
  in
  (* A variable the body names bare is kept where it is a declared
     parameter -- named, as a plain family the declaration deapplied is
     -- and becomes a [typename] parameter of the holder. *)
  let bare_vars =
    let seen = ref [] in
    visit probe (function
      | Tvar (Tv_index (i, Some _)) when not (List.mem i applied_vars) -> seen := i :: !seen
      | _ -> () );
    !seen
  in
  let probe =
    map_cpp_type
      (function
        | Tvar (Tv_index (i, _))
          when not (List.mem i applied_vars || List.mem i bare_vars) ->
          Tany
        | t -> t )
      probe
  in
  let home = ctor_alias_home ctx probe in
  let render t =
    let declared = ctor_alias_render_ctx ctx home in
    with_render_ctx
      (fun _ -> declared)
      (fun () ->
        Common.with_visibility (ctor_alias_visibility home) (fun () -> Pp.string_of_ppcmds (pp_cpp_type declared false vl t)) )
  in
  let rendered = lazy (render probe) in
  let head_alone () =
    let rendered = Lazy.force rendered in
    String.equal rendered (cut_at_argument_list rendered ^ "<" ^ ctor_alias_tvar ^ ">")
  in
  let alone =
    match applied_to_sentinel_alone probe with
    | Some alone ->
      if Probe.checking () && alone <> head_alone () then
        Probe.violation "constructor alias shape"
          Pp.(str "the type constructor written " ++ str (Lazy.force rendered) ++ str " is read off its structure as "
              ++ str (if alone then "" else "not ") ++ str "a template name applied to its argument alone");
      alone
    | None ->
      Probe.hit "CTORALIAS_UNDECIDED" (fun () -> Lazy.force rendered);
      head_alone ()
  in
  if alone then None
  else
    let rendered = Lazy.force rendered in
    (* Only a name the body actually {e writes} has to be abstracted
       over.  A custom mapping's replacement text need not use every
       argument -- [itree]'s spells only its last -- so a parameter that
       the probe carries structurally but the rendering drops would
       otherwise mint a holder with an unused parameter, and the alias
       would be declared as a partial specialisation of nothing. *)
    let names = identifier_tokens rendered in
    let captured probe = List.filter (fun (_, v) -> List.mem (written_var v) names) (captured probe) in
    (* A class instance the body reads a type out of -- [typename
       _tcI0::ptr] -- is the enclosing declaration's parameter as much
       as a variable is, and is captured the same way. *)
    let instances =
      let seen = ref [] in
      visit probe (function
        | Tinstance (id, _) when not (List.exists (Id.equal id) !seen) -> seen := !seen @ [id]
        | _ -> () );
      !seen
    in
    match (captured probe, instances) with
    | [], [] -> Some ({ca_base = base; ca_holder = false; ca_home = home; ca_body = rendered}, [])
    | vars, instances ->
      (* Rendered a second time with the captured names replaced by the
         holder's own, so that two declarations differing only in what
         they call their parameters share one holder.  A renamed variable
         is still a variable: a holder nested in the body captures it under
         its new name, and is applied to that. *)
      let var_names =
        List.mapi (fun k (i, _) -> (i, Generated_name.indexed (if List.mem i bare_vars then "P" else "F") k)) vars
      and instance_names = List.mapi (fun j id -> (id, Generated_name.indexed "P" (List.length vars + j))) instances in
      let renamed =
        rewrite_cpp_type
          (function
            | Tvar (Tv_index (i, _)) -> Option.map (fun name -> Tvar (Tv_index (i, Some name))) (List.assoc_opt i var_names)
            | Tinstance (id, c) -> (
              match List.find_opt (fun (id', _) -> Id.equal id id') instance_names with
              | Some (_, name) -> Some (Tinstance (name, c))
              | None -> None )
            | _ -> None )
          probe
      in
      Some
        ( {ca_base = base; ca_holder = true; ca_home = home; ca_body = render renamed},
          List.map (fun (_, v) -> written_var v) vars @ List.map Id.to_string instances )

(** Render [ty] as the qualifier of a {e value} -- [T::member] -- rather than of
    a nested type.

    A type and a value spell the same global differently.  The type spelling
    carries a leading [typename] for a dependent qualifier (see
    {!Cpp_names.typename_prefix_for}), which is ill-formed in front of a static
    member function -- [typename C::t::pair(x)] claims [pair] names a type --
    and it qualifies a global by its namespace where the value spelling elides
    the prefix that is already in scope.  A named global therefore goes through
    the expression printer; anything else only needs the keyword removed. *)
and pp_value_qualifier ctx env ty =
  match ty with
  | Tglob (r, tys, []) ->
    (* No [~yields]: a type qualifier is never a block in value position. *)
    pp_cpp_expr ctx env [] (CPPglob (r, tys, Some (Table.custom_info r)))
  | _ ->
  pp_cpp_type ~lead:false ctx false [] ty

(** Pretty-print a MiniCpp expression as C++ source.  The central expression
    printer of the module; dispatches on every {!Minicpp.cpp_expr} form and
    recurses into {!pp_cpp_stmt} for block/statement-valued expressions.

    @param env   name environment: the de Bruijn name list plus the set of
                 identifiers currently in scope
    @param args  arguments accumulated by callers (already pretty-printed) to be
                 applied once the head expression is reached, via [pp_apply_cpp]
    @param t     the expression to render *)
(* A member named after [.] or [->], with the template arguments it writes. *)
and pp_member_name ctx method_name = function
  | [] -> Id.print method_name
  | tys ->
    str "template " ++ Id.print method_name ++ str "<"
    ++ pp_list (pp_cpp_type ctx false []) tys
    ++ str ">"

and pp_cpp_expr ctx env args t =
  check_position ctx;
  let apply st = pp_apply_cpp st args in
  (* Generate an IIFE wrapper for a block template (%result) in expression
     position.  [ref_name] is for debug labels, [custom] is the raw template
     string, [tys] are type args, [val_args] are value args (already reversed
     for pp_custom). *)
  let gen_block_iife ?yields ref_name custom tys val_args =
    (* What the block evaluates to, as translation recorded it -- on the call
       node for a call, and on the global's own [ci_yields] for a bare
       reference to a block-valued constant, which has no call node.  The
       printer does not re-derive it: it would be reading the uninstantiated
       scheme out of the front-end table, and answering [List<T1>] where
       [List<uint64_t>] was meant. *)
    let ret_ty = match yields with Some ty -> ty | None -> Tauto in
    let result_str = "_r" in
    let substituted = with_result result_str custom in
    let cmds = term_template substituted in
    let body_pp =
      pp_custom
        ~container:ref_name ctx (Pp.string_of_ppcmds (GlobRef.print ref_name) ^ " := " ^ custom)
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
    str "[]() -> " ++ pp_cpp_type ctx false [] ret_ty ++ str " {"
    ++ fnl ()
    ++ str ("  " ^ Pp.string_of_ppcmds (pp_cpp_type ctx false [] ret_ty)
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
  | CPPglob (x, tys, Some {ci_inline = Some tmpl; ci_yields; _}) ->
    let custom = tmpl.it_text in
    if tmpl.it_form = Block_iife then
      gen_block_iife ?yields:ci_yields x custom tys []
    else
    let cmds = type_template custom in
    pp_custom
      ~container:x ctx (Pp.string_of_ppcmds (GlobRef.print x) ^ " := " ^ custom)
      env
      None
      None
      tys
      []
      []
      []
      []
      cmds
  | CPPmethod_value {mv_method; mv_access; mv_receiver; mv_params; mv_type_args} ->
    let names =
      match mv_params with
      | [_] -> ["_x"]
      | ps -> List.mapi (fun i _ -> "_x" ^ string_of_int i) ps
    in
    let param name = function
      | Some ty ->
        Pp.string_of_ppcmds (str "const " ++ pp_cpp_type ctx false [] ty ++ str (" &" ^ name))
      | None -> "const auto &" ^ name
    in
    let params = String.concat ", " (List.map2 param names mv_params) in
    let call_args = String.concat ", " (List.filteri (fun i _ -> i <> mv_receiver) names) in
    str ("[](" ^ params ^ ") { return " ^ List.nth names mv_receiver)
    ++ str (pp_obj_access mv_access)
    ++ pp_member_name ctx (Common.id_of_global Term mv_method) mv_type_args
    ++ str ("(" ^ call_args ^ "); }")
  | CPPprojection_value r ->
    str "[](const auto &_x) { return _x." ++ str (projection_field_name r) ++ str "; }"
  | CPPglob (x, tys, _) ->
    let class_ s = Cpp_name.Class s in
    (* The base name of a global reference: a name, or -- for a function in an
       eponymous template struct, which writes its own template arguments --
       already written. *)
    let base =
      match x with
      | GlobRef.IndRef _ -> `Named (inductive_value ctx x)
      | GlobRef.VarRef v -> `Named (Cpp_name.unqualified (Id.to_string v))
      | _ ->
      (* Check if this function is inside an eponymous template struct. If so,
         type args go on the struct name, not the function name.  A record of
         no parameters merges into a struct that is no template, whose
         functions are spelled as any module's are. *)
      let template_record = function
        | Some {Module_plan.record; type_params} when type_params > 0 -> Some (record, type_params)
        | Some _ | None -> None
      in
      match (template_record (Module_plan.eponymous_record_containing x), tys) with
      | Some (record_ref, type_params), _ :: _ ->
        (* Function inside eponymous template struct with type args: Generate
           StructName<int, ...>::template funcName<Args> for static methods. We
           use placeholder types for the struct and actual args for the
           method. *)
        let struct_name = Common.pp_global_name Type record_ref in
        let func_name = Common.pp_global_name Term x in
        let placeholder_args = gen_placeholder_args type_params in
        let ty_args = pp_list (pp_cpp_type ctx false []) tys in
        `Written
          ( Cpp_name.pp_type_qualifier class_
              (str (String.capitalize_ascii struct_name) ++ str "<" ++ str placeholder_args ++ str ">")
          ++ str "template "
          ++ str func_name
          ++ str "<"
          ++ ty_args
          ++ str ">" )
      | Some (record_ref, type_params), [] ->
        let struct_name = Common.pp_global_name Type record_ref in
        let func_name = Common.pp_global_name Term x in
        let placeholder_args = gen_placeholder_args type_params in
        `Written
          ( Cpp_name.pp_type_qualifier class_
              (str (String.capitalize_ascii struct_name) ++ str "<" ++ str placeholder_args ++ str ">")
          ++ str func_name )
      | None, _ ->
        (* Normal case: function not in eponymous struct *)
        let name = global_name ctx Term x in
        let qualified = wrapper_qualify x name in
        if not (Cpp_name.equal qualified name) then `Named qualified
        else if needs_global_qualifier ctx x then `Named (Cpp_name.within Cpp_name.Global name)
        else `Named name
    in
    let base_name = match base with `Named n -> Cpp_name.pp n | `Written d -> d in
    let is_accessor =
      let x_mp = modpath_of_r x in
      let x_lbl = label_of_r x in
      let rec resolve_mp mp =
        match Module_plan.functor_app_source mp with
        | Some source -> resolve_mp source  (* iterate to fixpoint *)
        | None ->
          match mp with
          | Names.ModPath.MPdot (parent, lbl) ->
            let resolved_parent = resolve_mp parent in
            if ModPath.equal resolved_parent parent then mp
            else Names.ModPath.MPdot (resolved_parent, lbl)
          | _ -> mp
      in
      let resolved_x_mp = resolve_mp x_mp in
      let planned =
        List.exists
          (fun (reg_mp, reg_lbl) ->
            Label.equal x_lbl reg_lbl
            && ( ModPath.equal x_mp reg_mp
               || ModPath.equal resolved_x_mp reg_mp ) )
          !template_static_accessors
      in
      (* A constant reached through a module alias is the target's own, which
         its canonical name says.  One reached through a functor parameter
         has whatever shape the argument gives it, and the use below accepts
         both: any accessor of the same name makes it one. *)
      planned
      || (match x with GlobRef.ConstRef c -> Hashtbl.mem template_static_accessor_kns (Constant.canonical c) | _ -> false)
      || under_mp_bound x_mp
         && List.exists (fun (_, reg_lbl) -> Label.equal x_lbl reg_lbl) !template_static_accessors
    in
    let full_name =
      match (base, tys, Module_plan.eponymous_record_containing x) with
      | `Written _, _, _ | _, [], _ | _, _, Some _ -> base_name
      | `Named n, _, None ->
        (* A template named through a qualifier takes the [template]
           disambiguator: [C::template empty<T>]. *)
        Cpp_name.pp ~template_keyword:true n
        ++ str "<" ++ pp_list (pp_cpp_type ctx false []) tys ++ str ">"
    in
    let full_name =
      if not is_accessor then full_name
      else if under_mp_bound (modpath_of_r x) then
        (* Reached through a bound module parameter, whose member shape is not
           known here: the argument module may define this value as a static
           data member or -- when it is itself inside a template, as a Meyers
           singleton -- as a nullary accessor.  The generated concept accepts
           both spellings (see [pp_spec_as_requirement] in [cpp.ml]), so the
           use site must accept both too. *)
        let n = string_of_ppcmds full_name in
        str ("[]{ if constexpr (requires { " ^ n ^ "(); }) return " ^ n
             ^ "(); else return " ^ n ^ "; }()")
      else full_name ++ str "()"
    in
    apply full_name
  | CPPnamespace (r, t) ->
    let name, _ = inductive_name ctx r in
    Cpp_name.pp_qualifier (fun s -> Cpp_name.Class s) name ++ pp_cpp_expr ctx env args t
  | CPPfun_call (res, CPPglob (n, tys, Some {ci_inline = Some tmpl; _}), ts) ->
    let s = tmpl.it_text in
    if tmpl.it_form = Block_iife then
      gen_block_iife
        ?yields:(match res.cs_yields with Ryields ty -> Some ty | Ropaque -> None)
        n s tys (call_args ts)
    else
    if tmpl.it_form = Bare_callee then
      let ty_args_s =
        match tys with
        | [] -> mt ()
        | _ -> str "<" ++ pp_list (pp_cpp_type ctx false []) tys ++ str ">"
      in
      let args_s = pp_list (pp_cpp_expr ctx env args) (call_args ts) in
      str s ++ ty_args_s ++ str "(" ++ args_s ++ str ")"
    else
      (* [%ret] is the type the call yields, as translation recorded it: a
         mapping can name a generated type -- the enum an ordering
         becomes -- without knowing what the generator called it. *)
      let s =
        if Common.contains_substring s "%ret" then
          match res.cs_yields with
          | Ryields ty ->
            Str.global_replace (Str.regexp_string "%ret")
              (Pp.string_of_ppcmds (pp_cpp_type ctx false [] ty)) s
          | Ropaque ->
            CErrors.user_err
              Pp.(str "Crane: the mapping " ++ GlobRef.print n
                  ++ str " names %ret, but the type its call yields is not known here.")
        else s
      in
      let cmds = term_template s in
      let arg_types =
        match res.cs_params with Ptypes ts -> ts | Punknown -> []
      in
      (* A mapping names the arguments it needs, and an argument past the last
         one it names is one it chose not to read.  An argument past the
         constant's own parameters -- [case_ f g] applied to an event -- is
         not this call's at all: translation applies the result to it. *)
      let all_args = call_args ts in
      let named =
        List.fold_left
          (fun acc -> function CCarg i -> max acc (i + 1) | _ -> acc)
          0 cmds
      in
      pp_custom
        ~container:n ctx (Pp.string_of_ppcmds (GlobRef.print n) ^ " := " ^ s)
        env
        None
        None
        tys
        []
        (CList.firstn (min named (List.length all_args)) all_args)
        arg_types
        []
        cmds
  | CPPmethod_call {mc_method; mc_access; mc_receiver; mc_type_args; mc_args} ->
    pp_cpp_expr ctx env args mc_receiver
    ++ str (pp_obj_access mc_access)
    ++ pp_member_name ctx (Common.id_of_global Term mc_method) mc_type_args
    ++ str "("
    ++ pp_list (pp_cpp_expr ctx env args) mc_args
    ++ str ")"
  | CPPfun_call (_, CPPrt Crane_rt.Share_child, {rev = [arg]}) -> (
    (* A field read out of a matched value goes to the new node as the cell
       it is in; anything else is the value itself. *)
    match arg with
    | CPPderef p -> str (Crane_rt.name Crane_rt.Share_child) ++ str "(" ++ pp_cpp_expr ctx env args p ++ str ")"
    | _ -> pp_cpp_expr ctx env args arg )
  | CPPfun_call (_, CPPderef e, ts) ->
    (* Call through a dereferenced pointer: deref + invoke pattern.
       Arises from the shared_ptr fixpoint pattern where recursive calls
       dereference the function pointer before invoking. *)
    let args_s = pp_list (pp_cpp_expr ctx env args) (call_args ts) in
    str "(*" ++ pp_cpp_expr ctx env args e ++ str ")(" ++ args_s ++ str ")"
  | CPPprojection {pj_projection; pj_record; pj_args} ->
    pp_cpp_expr ctx env args pj_record ++ str "." ++ str (projection_field_name pj_projection)
    ++ (if pj_args = [] then mt () else str "(" ++ pp_list (pp_cpp_expr ctx env args) pj_args ++ str ")")
  | CPPfun_call (_, f, ts) ->
    let args_s = pp_list (pp_cpp_expr ctx env args) (call_args ts) in
    let prefix = match f with
      | CPPglob (GlobRef.IndRef _, _, _)
        when ctx.rc_in_template && writes_qualifier (pp_cpp_expr ctx env args f) ->
        str "typename "
      | _ -> mt ()
    in
    prefix ++ pp_cpp_expr ctx env args f ++ str "(" ++ args_s ++ str ")"
  (* A box is the converting constructor [std::any(e)], so it prints as one. *)
  | CPPbox (ty, e) -> pp_cpp_expr ctx env args (CPPconverting_ctor (ty, [ e ]))
  | CPPconverting_ctor (ty, ts) ->
    pp_cpp_type ctx false [] ty ++ str "(" ++ pp_list (pp_cpp_expr ctx env args) ts ++ str ")"
  | CPPderef e ->
    let needs_parens = match e with
      | CPPvar _ | CPPthis | CPPfun_call _ | CPPaccess _
      | CPPaccess_call _ | CPPmethod_call _ | CPPprojection _ -> false
      | _ -> true
    in
    if needs_parens then str "*(" ++ pp_cpp_expr ctx env args e ++ str ")"
    else str "*" ++ pp_cpp_expr ctx env args e
  | CPPmove e ->
    writes_standard "utility";
    str (sn ()).move ++ str "(" ++ pp_cpp_expr ctx env args e ++ str ")"
  | CPPforward (ty, e) ->
    str (sn ()).forward
    ++ str "<"
    ++ pp_cpp_type ctx false [] ty
    ++ str ">("
    ++ pp_cpp_expr ctx env args e
    ++ str ")"
  | CPPlambda
    { cl_params = params;
      cl_tparams = tparams;
      cl_ret = ret_ty;
      cl_body = body;
      cl_capture = capture;
      cl_moved = moved } ->
    let params = to_reversed params in
    let needs_capture, uses_this = lambda_needs_capture params body in
    (* A polymorphic function object: the erased positions of a rank-2
       argument are the lambda's own template parameters, so the body says
       [X] where it would otherwise have to guess. *)
    let tparams_str =
      match tparams with
      | [] -> mt ()
      | ids ->
        str "<"
        ++ pp_list (fun id -> str "typename " ++ Id.print id) ids
        ++ str ">"
    in
    (* Never [mutable]: a closure's captures are [const] in its body, which
       is what lets every copy of a [crane::fn] share one closure. *)
    let capture =
      ( if not needs_capture then str "[]"
        else match capture with
          | Closure ->
            (* A variable whose last use is this capture moves into it. *)
            let moves =
              List.map
                (fun x -> str ", " ++ Id.print x ++ str " = std::move(" ++ Id.print x ++ str ")")
                moved
            in
            str "[=" ++ (if uses_this then str ", this" else mt ()) ++ seq moves ++ str "]"
          | Immediate -> str "[&]" )
      ++ tparams_str ++ str "("
    in
    let body_s = pp_list_stmt (pp_cpp_stmt ctx env args) body in
    let read = Minicpp.reads_as_printed body in
    let params_s =
      pp_list
        (fun (ty, id_opt) ->
          match id_opt with
          | Some id when read id -> pp_cpp_type ctx false [] ty ++ spc () ++ Id.print id
          | _ -> pp_cpp_type ctx false [] ty )
        (List.rev params)
    in
    ( match ret_ty with
    | Some ty ->
      h
        ( capture
        ++ params_s
        ++ str ")"
        ++ str " -> "
        ++ pp_cpp_type ctx false [] ty )
      ++ str " {"
      ++ fnl ()
      ++ body_s
      ++ fnl ()
      ++ str "}"
    | None ->
      (capture ++ params_s ++ str ")")
      ++ str " {"
      ++ fnl ()
      ++ body_s
      ++ fnl ()
      ++ str "}" )
  | CPPalloc ((Alloc_heap | Alloc_arena_scoped), t) when Pointer_slot.of_pointee t = Pointer_slot.Shared ->
    (* A shared value goes into its slot as it is: no cell to allocate. *)
    writes (Table.Runtime Crane_rt.shared_variant_header);
    cpp_angle Crane_rt.shared_box (pp_cpp_type ctx false [] t) ++ str "::make"
  | CPPalloc (Alloc_heap, t) ->
    writes_standard "memory";
    cpp_angle (sn ()).make_shared (pp_cpp_type ctx false [] t)
  | CPPalloc (Alloc_reusing, t) ->
    (* Perceus reuse factory; only emitted under NonAtomicRc (crane::rc). *)
    cpp_angle Crane_rt.make_rc_reusing (pp_cpp_type ctx false [] t)
  | CPPalloc (Alloc_arena_scoped, t) ->
    (* Runtime scoped-arena factory: the arena-aware form of make_shared/make_rc
       for the current pointer flavor.  Falls back to a plain heap allocation at
       runtime whenever no arena scope is open at the call site. *)
    let inner = pp_cpp_type ctx false [] t in
    if Table.non_atomic_rc () then begin
      (* crane::rc<T>::make(...) -- rc.h transitively includes arena.h. *)
      writes_standard "memory";
      cpp_angle Crane_rt.rc inner ++ str "::make"
    end
    else if Table.std_lib () = "BDE" then
      (* No runtime arena under BDE (arena.h is std-only): plain factory. *)
      cpp_angle (sn ()).make_shared inner
    else begin
      writes Table.arena_header;
      cpp_angle Crane_rt.arena_make_shared inner
    end
  | CPPstructmk (id, tys, es) | CPPstruct (id, tys, es) as e ->
    let suffix = match e with CPPstructmk _ -> "::make(" | _ -> "{" in
    let closing = match e with CPPstructmk _ -> str ")" | _ -> str "}" in
    let es_s = pp_list (pp_cpp_expr ctx env args) es in
    let templates =
      match tys with
      | [] -> mt ()
      | _ -> str "<" ++ pp_list (pp_cpp_type ctx false []) tys ++ str ">"
    in
    let struct_name =
      match id with
      | GlobRef.IndRef _ when is_eponymous_record_cached id ->
        Cpp_name.unqualified (Common.pp_type_name_capitalized id)
      | _ -> global_name ctx Type id
    in
    typename_prefix_for ctx struct_name
    ++ Cpp_name.pp struct_name ++ templates ++ str suffix ++ es_s ++ closing
  | CPPstruct_id (id, tys, es) ->
    let es_s = pp_list (pp_cpp_expr ctx env args) es in
    let templates =
      match tys with
      | [] -> mt ()
      | _ -> str "<" ++ pp_list (pp_cpp_type ctx false []) tys ++ str ">"
    in
    Id.print id ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPget (e, id) ->
    ( match e with
    | CPPderef CPPthis -> str "this->" ++ Id.print id
    | CPPderef _ | CPPraw _ ->
      str "(" ++ pp_cpp_expr ctx env args e ++ str ")." ++ Id.print id
    | _ -> pp_cpp_expr ctx env args e ++ str "." ++ Id.print id )
  | CPPget' (e, id, _) ->
    let field_name = str (Common.pp_global_name Type id) in
    ( match e with
    | CPPderef CPPthis -> str "this->" ++ field_name
    | CPPderef _ | CPPraw _ ->
      str "(" ++ pp_cpp_expr ctx env args e ++ str ")." ++ field_name
    | _ -> pp_cpp_expr ctx env args e ++ str "." ++ field_name )
  | CPPstring s -> str ("\"" ^ escape_cpp_string (Pstring.to_string s) ^ "\"")
  | CPPparray (elems, _) ->
    str "{" ++ pp_list (pp_cpp_expr ctx env args) (Array.to_list elems) ++ str "}"
  | CPPuint x ->
    let s = Uint63.to_string x in
    ( match
        try Some (Nametab.locate (Libnames.qualid_of_string "int"))
        with Not_found -> None
      with
    | Some gr when is_inline_custom gr ->
      ( match find_custom_opt gr with
      | Some "int64_t" -> str ("INT64_C(" ^ s ^ ")")
      | Some cpp_type -> str (cpp_type ^ "(" ^ s ^ ")")
      | None -> str s )
    | _ -> str s )
  | CPPfloat f -> str (spell_double (Float64.to_float f))
  | CPPconcept_app (concept, subject, tys) ->
    (* A concept is hoisted out of every enclosing struct, so it is named
       unqualified here however deeply the subject is nested. *)
    pp_concept_name_of_ref ctx concept
    ++ str "<"
    ++ pp_global ctx Type subject
    ++ prlist (fun ty -> str ", " ++ pp_cpp_type ctx false [] ty) tys
    ++ str ">"
  | CPPrequires (ty_vars, exprs, type_reqs) ->
    let ty_vars_s =
      match ty_vars with
      | [] -> mt ()
      | _ ->
        str "("
        ++ pp_list
             (fun (ty, id) -> pp_cpp_type ctx false [] ty ++ spc () ++ Id.print id)
             ty_vars
        ++ str ") "
    in
    let type_reqs_s =
      prlist_with_sep
        fnl
        (fun ty -> str "  " ++ pp_cpp_type ctx false [] ty ++ str ";")
        type_reqs
    in
    let exprs_s =
      prlist_with_sep
        fnl
        (fun (e1, e2) ->
          str "  { "
          ++ pp_cpp_expr ctx env args e1
          ++ str " } -> "
          ++ pp_cpp_expr ctx env args e2
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
    ++ pp_cpp_type ctx false [] ty
    ++ str "("
    ++ pp_list (pp_cpp_expr ctx env args) exprs
    ++ str ")"
  | CPPshared_ptr_ctor (ty, expr) ->
    str (sn ()).shared_ptr
    ++ str "<"
    ++ pp_cpp_type ctx false [] ty
    ++ str ">("
    ++ pp_cpp_expr ctx env args expr
    ++ str ")"
  | CPPthis -> str "this"
  | CPPshared_from_this ty ->
    (* [crane::rc] returns a mutable [rc<T>] from [rc_from_this()], so no
       const_pointer_cast is needed; [std::shared_ptr] needs the cast to strip
       the const that [shared_from_this()] adds in const methods. *)
    if String.equal (sn ()).shared_ptr Crane_rt.rc then
      str "this->rc_from_this()"
    else
      str "std::const_pointer_cast<"
      ++ pp_cpp_type ctx false [] ty
      ++ str ">(this->shared_from_this())"
  | CPPaccess (acc, e, id) ->
    ( match (acc, e) with
    | Adot, CPPderef inner ->
      (* Dot access on a dereferenced pointer is arrow access on the pointer. *)
      pp_object ctx env args inner ++ str "->" ++ Id.print id
    | _ -> pp_object ctx env args e ++ str (pp_obj_access acc) ++ Id.print id )
  | CPPaccess_call (acc, obj, method_name, call_args) ->
    pp_object ctx env args obj ++ str (pp_obj_access acc) ++ Id.print method_name
    ++ str "(" ++ pp_list (pp_cpp_expr ctx env args) call_args ++ str ")"
  | CPPscope (e, id, []) ->
    pp_cpp_expr ctx env args e ++ str "::" ++ Id.print id
  | CPPscope (e, id, tys) ->
    pp_cpp_expr ctx env args e ++ str "::template " ++ Id.print id ++ str "<"
    ++ pp_list (pp_cpp_type ctx false []) tys ++ str ">"
  | CPPqualified_t (ty, id) ->
    pp_value_qualifier ctx env ty ++ str "::" ++ Id.print id
  | CPPconvertible_to ty ->
    writes_standard "concepts";
    str "std::convertible_to<" ++ pp_cpp_type ctx false [] ty ++ str ">"
  | CPPabort (msg, ty) ->
    writes_standard "stdexcept";
    str "([]() -> "
    ++ pp_cpp_type ctx false [] ty
    ++ str " { throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str (escape_cpp_string msg)
    ++ str "\"); })()"
  | CPPenum_val (ind, ctor) ->
    (* Generate EnumType::Constructor for enum class values. Use str_global for
       proper module qualification, with collision-aware capitalization. *)
    let full_name = enum_name (global_name ctx Type ind) ind in
    Cpp_name.pp_scopes (global_scopes_for ind full_name)
    ++ Cpp_name.pp_qualifier (fun s -> Cpp_name.Class s) full_name
    ++ Id.print ctor
  | CPPnullptr -> str "nullptr"
  | CPPin_place ->
    writes_standard "utility";
    str ((sn ()).ns ^ "::in_place")
  | CPPin_place_index i ->
    writes_standard "utility";
    str ((sn ()).ns ^ "::in_place_index<" ^ string_of_int i ^ ">")
  | CPPbraced es ->
    str "{" ++ pp_list (pp_cpp_expr ctx env args) es ++ str "}"
  | CPPstd_get (ty, None) ->
    writes_variant ();
    str ((sn ()).get ^ "<") ++ pp_cpp_type ctx false [] ty ++ str ">"
  | CPPstd_get (ty, Some e) ->
    writes_variant ();
    str ((sn ()).get ^ "<") ++ pp_cpp_type ctx false [] ty ++ str ">("
    ++ pp_cpp_expr ctx env args e
    ++ str ")"
  | CPPstd_holds_alternative ty ->
    writes_variant ();
    str ((sn ()).holds_alternative ^ "<") ++ pp_cpp_type ctx false [] ty ++ str ">"
  | CPPdeclval ty ->
    writes_standard "utility";
    str "std::declval<" ++ pp_cpp_type ctx false [] ty ++ str ">()"
  | CPPtype_name ty -> pp_cpp_type ctx false [] ty
  (* Low-level constructs for reuse optimization *)
  | CPPrt h ->
    (match h with
     | Crane_rt.Raw | Crane_rt.Deep_box -> writes Table.erase_fn_header
     | Crane_rt.Unbox_field -> writes (Table.Runtime Crane_rt.field_header)
     | Crane_rt.Apply2 -> writes (Table.Runtime Crane_rt.fn_header)
     | Crane_rt.Constant _ | Crane_rt.Immortal ->
       writes (Table.Runtime Crane_rt.shared_block_header)
     | Crane_rt.Make_rc_reusing_unchecked | Crane_rt.Reuse_step
     | Crane_rt.Share_child -> ());
    str (Crane_rt.name h)
  | CPPnumeral (_, n) -> str n.nl_text
  | CPPraw code -> str code
  | CPPbinop (op, lhs, rhs) ->
    (* Parenthesize && subexpressions inside || to avoid
       -Wlogical-op-parentheses warnings. *)
    let paren_child child =
      match child with
      | CPPbinop (Band, _, _) when op = Bor ->
        str "(" ++ pp_cpp_expr ctx env args child ++ str ")"
      | CPPbinop (Bor, _, _) when op = Band ->
        str "(" ++ pp_cpp_expr ctx env args child ++ str ")"
      | _ -> pp_cpp_expr ctx env args child
    in
    paren_child lhs
    ++ str " "
    ++ str (spell_binop op)
    ++ str " "
    ++ paren_child rhs
  | CPPcond (cond, then_expr, else_expr) ->
    (* Wrap the whole ternary in parentheses, so a conditional used as a
       subexpression cannot bind incorrectly against a surrounding operator. *)
    str "("
    ++ pp_cpp_expr ctx env args cond
    ++ str " ? "
    ++ pp_cpp_expr ctx env args then_expr
    ++ str " : "
    ++ pp_cpp_expr ctx env args else_expr
    ++ str ")"
  | CPPbool b -> str (if b then "true" else "false")
  | CPPint n -> str (string_of_int n)
  | CPPunop (op, e) ->
    (* Parenthesize the operand only when it is a lower-precedence compound
       expression (a binary operator or ternary), so that e.g. [!(a == b)] is
       not emitted as the mis-parsed [!a == b]. Leaf operands like [&x] / [!flag]
       stay unparenthesized. *)
    let operand =
      match e with
      | CPPbinop _ | CPPcond _ -> str "(" ++ pp_cpp_expr ctx env args e ++ str ")"
      | _ -> pp_cpp_expr ctx env args e
    in
    str (spell_unop op) ++ operand
  | CPPunbox (Unbox_to ty, e) ->
    writes_obj ();
    str Crane_rt.obj_cast ++ str "<" ++ pp_cpp_type ctx false [] ty ++ str ">("
    ++ pp_cpp_expr ctx env args e ++ str ")"
  | CPPunbox (Unbox_or_keep ty, e) ->
    writes_standard "type_traits";
    let ty_pp = pp_cpp_type ctx false [] ty and e_pp = pp_cpp_expr ctx env args e in
    str "[&]() -> " ++ ty_pp
    ++ str " { if constexpr (std::is_same_v<" ++ ty_pp
    ++ str (", " ^ Crane_rt.obj ^ ">) return ") ++ e_pp
    ++ str "; else return " ++ str Crane_rt.obj_cast
    ++ str "<" ++ ty_pp ++ str ">(" ++ e_pp ++ str "); }()"
  | CPPunbox (Unbox_list (list_ty, flat_ty), e) ->
    pp_cpp_type ctx false [] list_ty
    ++ str "(" ++ str Crane_rt.obj_cast ++ str "<"
    ++ pp_cpp_type ctx false [] flat_ty
    ++ str ">(" ++ pp_cpp_expr ctx env args e ++ str "))"
  | CPPany_cast (ty, e) | CPPany_cast_tolerant (ty, e) ->
    writes_obj ();
    (* A binder holding a known type in a box is read bare inside a cast
       that already names its type; {!Cpp_erasure.lower_boxed_reads} leaves
       it so. *)
    let inner = pp_cpp_expr ctx env args e in
    (* Which caster, and whether the cast is needed at all, was decided by
       {!Cpp_erasure.resolve_casts}. *)
    let caster =
      match t with
      | CPPany_cast_tolerant _ ->
        writes Table.erase_fn_header;
        Crane_rt.any_cast
      | _ -> Crane_rt.obj_cast
    in
    str caster ++ str "<" ++ pp_cpp_type ctx false [] ty ++ str ">(" ++ inner
    ++ str ")"
  | CPPerase_fn
      (shape, (CPPglob (GlobRef.ConstRef _, [], (None | Some {ci_inline = None; _})) as g)) ->
    (* A global never changes, so neither does its adapter: made once.  A
       method is never a global here: it is named through a lambda
       ({!Minicpp.method_value}), never as itself. *)
    writes Table.erase_fn_header;
    str Crane_rt.erase_global ++ str "<" ++ pp_cpp_expr ctx env args g
    ++ ( match shape with
       | Boxed_whole -> mt ()
       | At_signature ty -> str ", " ++ pp_cpp_type ctx false [] ty )
    ++ str ">()"
  | CPPsuspend (ty, thunk) ->
    pp_cpp_expr ctx env args
      (CPPfun_call
         ( Minicpp.call_sig ~yields:ty ~nargs:1 (),
           CPPqualified_t (ty, Id.of_string "lazy_"),
           of_reversed [thunk] ))
  | CPPerase_fn (shape, e) ->
    writes Table.erase_fn_header;
    str Crane_rt.erase_fn
    ++ ( match shape with
       | Boxed_whole -> mt ()
       | At_signature ty -> str "<" ++ pp_cpp_type ctx false [] ty ++ str ">" )
    ++ str "("
    ++ pp_cpp_expr ctx env args e
    ++ str ")"
  | CPPerased_call (f, a) ->
    (* The one signature a callable is erased into storage at, so the one it
       can be recovered at; each application yields a [std::any] in turn. *)
    writes_obj ();
    writes_standard "functional";
    str Crane_rt.obj_cast
    ++ str "<"
    ++ pp_cpp_type ctx false [] (Tfun ([Tany], Tany))
    ++ str ">("
    ++ pp_cpp_expr ctx env args f
    ++ str ")("
    ++ pp_cpp_expr ctx env args a
    ++ str ")"
  | CPPtolerant_call (f, call_args) ->
    writes Table.erase_fn_header;
    str Crane_rt.call_erased
    ++ str "("
    ++ prlist_with_sep pr_comma (pp_cpp_expr ctx env args) (f :: call_args)
    ++ str ")"
  | CPPfn_value e ->
    writes (Table.Runtime Crane_rt.fn_header);
    str Crane_rt.fn ++ str "(" ++ pp_cpp_expr ctx env args e ++ str ")"
  | CPPconvert (ty, e) ->
    writes Table.erase_fn_header;
    str Crane_rt.convert
    ++ str "<"
    ++ pp_cpp_type ctx false [] ty
    ++ str ">("
    ++ pp_cpp_expr ctx env args e
    ++ str ")"
  | CPPcontainer_cast (ty, e, suppress_boxing) ->
    writes Table.erase_fn_header;
    let ty_pp =
      setting suppress_elem_boxing (suppress_boxing || !suppress_elem_boxing) (fun () -> pp_cpp_type ctx false [] ty)
    in
    str Crane_rt.container_cast ++ str "<"
    ++ ty_pp
    ++ str ">("
    ++ pp_cpp_expr ctx env args e
    ++ str ")"
  | CPPstd_get_if (ty, e) ->
    writes_variant ();
    str ((sn ()).get_if ^ "<") ++ pp_cpp_type ctx false [] ty ++ str ">("
    ++ pp_cpp_expr ctx env args e ++ str ")"

(** [pp_object ctx env args e] prints [e] in the position a [.], [->] or member
    call is about to be applied to.

    Postfix operators bind tighter than the prefix ones, so an [e] that prints
    with a leading [*] has to be parenthesised for the access to apply to [e]
    as a whole rather than to its operand. *)
and pp_object ctx env args e =
  match e with
  | CPPderef _ -> str "(" ++ pp_cpp_expr ctx env args e ++ str ")"
  | CPPraw s when String.length s > 0 && s.[0] = '*' ->
    str "(" ++ pp_cpp_expr ctx env args e ++ str ")"
  | _ -> pp_cpp_expr ctx env args e

(** Pretty-print a MiniCpp statement as C++ source.

    @param env   name environment (see {!pp_cpp_expr})
    @param args  accumulated argument list forwarded to sub-expression printers *)
and pp_cpp_stmt ctx env args stmt =
  check_position ctx;
  match stmt with
  | Sreturn None -> str "return;"
  | Sreturn (Some (CPPabort (msg, _))) ->
    writes_standard "stdexcept";
    str "throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str (escape_cpp_string msg)
    ++ str "\");"
  | Sreturn (Some e) ->
    str "return " ++ pp_cpp_expr ctx env args e ++ str ";"
  | Sdecl (id, ty, _) ->
    pp_cpp_type ctx false [] ty ++ str " " ++ Id.print id ++ str ";"
  | Sasgn (id, Declare (ty, _), e) ->
    pp_cpp_type ctx false [] ty
    ++ str " "
    ++ Id.print id
    ++ str " = "
    ++ pp_cpp_expr ctx env args e
    ++ str ";"
  | Sasgn (id, Existing, e) ->
    Id.print id ++ str " = " ++ pp_cpp_expr ctx env args e ++ str ";"
  | Sasgn (id, Declare_static ty, e) ->
    str "static " ++ pp_cpp_type ctx false [] ty ++ str " " ++ Id.print id ++ str " = "
    ++ pp_cpp_expr ctx env args e ++ str ";"
  | Sexpr e -> pp_cpp_expr ctx env args e ++ str ";"
  | Sthrow msg ->
    writes_standard "stdexcept";
    str "throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str (escape_cpp_string msg)
    ++ str "\");"
  | Sswitch (scrut, ind, branches, default) ->
    (* Generate switch statement for enum class matching. Use pp_global_name to
       get the unqualified base name, capitalize to match enum class
       definition. *)
    let type_name =
      let n = inductive_type_name ctx ind in
      Cpp_name.pp_scopes (global_scopes_for ind n) ++ Cpp_name.pp n
    in
    let ends_with_return stmts =
      match List.rev stmts with
      | Sreturn _ :: _ -> true
      | _ -> false
    in
    let pp_branch (ctor, stmts) =
      str "case "
      ++ type_name
      ++ str "::"
      ++ Id.print ctor
      ++ str ": {"
      ++ fnl ()
      ++ pp_list_stmt (pp_cpp_stmt ctx env args) stmts
      ++ ( if ends_with_return stmts then mt ()
         else fnl () ++ str "break;" )
      ++ fnl ()
      ++ str "}"
    in
    writes_standard "utility";
    str "switch ("
    ++ pp_cpp_expr ctx env args scrut
    ++ str ") {"
    ++ fnl ()
    ++ prlist_with_sep fnl pp_branch branches
    ++ fnl ()
    ++ ( match default with
       | Some stmts ->
         str "default: {"
         ++ fnl ()
         ++ pp_list_stmt (pp_cpp_stmt ctx env args) stmts
         ++ fnl ()
         ++ str "}"
       | None ->
         str "default:"
         ++ fnl ()
         ++ str "  std::unreachable();" )
    ++ fnl ()
    ++ str "}"
  | Sassert precond ->
    (* The Rocq term is pretty-printed and may span several lines; a bare [//]
       would only comment out the first one and leave the rest to be parsed as
       C++.  Prefix every line. *)
    let statement = match precond with Pchecked s | Pstated s -> s in
    let lines = String.split_on_char '\n' statement in
    let lines = List.map (fun l -> String.trim l) lines in
    let lines = List.filter (fun l -> l <> "") lines in
    prlist_with_sep fnl
      (fun l -> str "// " ++ str l)
      ( match lines with
      | [] -> ["Precondition:"]
      | first :: rest -> ("Precondition: " ^ first) :: rest )
    ++
    ( match precond with
    | Pchecked expr_str ->
      writes_standard "cassert";
      fnl () ++ str "assert(" ++ str expr_str ++ str ");"
    | Pstated _ -> mt () )
  (* Reuse optimization constructs *)
  | Sif_constexpr (Tt_convertible (t1, t2), then_stmts, else_stmts) ->
    writes Table.erase_fn_header;
    str "if constexpr (" ++ str Crane_rt.convertible ++ str "<"
    ++ pp_cpp_type ctx false [] t1
    ++ str ", "
    ++ pp_cpp_type ctx false [] t2
    ++ str ">) {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt ctx env args) then_stmts
    ++ fnl ()
    ++ str "} else {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt ctx env args) else_stmts
    ++ fnl ()
    ++ str "}"
  | Sif (cond, then_stmts, else_stmts) ->
    str "if ("
    ++ pp_cpp_expr ctx env args cond
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt ctx env args) then_stmts
    ++ fnl ()
    ++ ( match else_stmts with
       | [] -> str "}"
       | _ ->
         str "} else {"
         ++ fnl ()
         ++ pp_list_stmt (pp_cpp_stmt ctx env args) else_stmts
         ++ fnl ()
         ++ str "}" )
  | Sif_decl (id, ty, init, then_stmts, else_stmts) ->
    str "if ("
    ++ pp_cpp_type ctx false [] ty ++ str " " ++ Id.print id
    ++ str " = " ++ pp_cpp_expr ctx env args init
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt ctx env args) then_stmts
    ++ fnl ()
    ++ (match else_stmts with
        | [] -> str "}"
        | _ ->
          str "} else {"
          ++ fnl ()
          ++ pp_list_stmt (pp_cpp_stmt ctx env args) else_stmts
          ++ fnl ()
          ++ str "}")
  | Sraw code ->
    if Common.contains_substring code "std::vector" then
      writes_standard "vector";
    str code
  | Scomment text ->
    str ("/// " ^ text)
  | Sstruct_def (name, fields) ->
    str "struct "
    ++ Id.print name
    ++ str " { "
    ++ prlist_with_sep mt
         (fun (fid, ty) ->
           pp_cpp_type ctx false [] ty ++ str " " ++ Id.print fid ++ str "; ")
         fields
    ++ str "};"
  | Susing (name, ty) ->
    str "using " ++ Id.print name ++ str " = " ++ pp_cpp_type ctx false [] ty ++ str ";"
  | Sdecl_init (id, ty) ->
    pp_cpp_type ctx false [] ty ++ str " " ++ Id.print id ++ str "{};"
  | Sbind (ids, e) ->
    str "const auto& [" ++ prlist_with_sep (fun () -> str ", ") Id.print ids
    ++ str "] = " ++ pp_cpp_expr ctx env args e ++ str ";"
  | Sfor_range (id, e, body) ->
    str "for (auto& " ++ Id.print id ++ str " : "
    ++ pp_cpp_expr ctx env args e
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt ctx env args) body
    ++ fnl ()
    ++ str "}"
  | Swhile (cond, body) ->
    str "while ("
    ++ pp_cpp_expr ctx env args cond
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt ctx env args) body
    ++ fnl ()
    ++ str "}"
  | Sblock stmts ->
    str "{"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt ctx env args) stmts
    ++ fnl ()
    ++ str "}"
  | Scontinue -> str "continue;"
  | Sbreak -> str "break;"
  | Sassign_expr (lhs, e) ->
    pp_cpp_expr ctx env args lhs
    ++ str " = "
    ++ pp_cpp_expr ctx env args e
    ++ str ";"
  | Sblock_custom (_ref, tmpl, result_var, result_ty, args, tyargs, _) ->
    (* Block template: emit a declaration + template-substituted statements.
       %result → result_var, %aN → value args, %tN → type args *)
    let result_str = Pp.string_of_ppcmds (Id.print result_var) in
    (* Substitute %result first *)
    let flat = with_result result_str tmpl in
    let cmds = term_template flat in
    (* Render: type declaration + template body as statements *)
    let decl_pp =
      pp_cpp_type ctx false [] result_ty
      ++ str " "
      ++ Id.print result_var
      ++ str ";"
    in
    let body_pp =
      pp_custom
        ~container:_ref ctx ("block custom " ^ Pp.string_of_ppcmds (GlobRef.print _ref))
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
    (* Scrutinee caching (auto _cs = expr;) is handled during translation
       in gen_custom_cpp_case, which prepends an Sasgn before this node
       when the template uses %scrut more than once with a non-trivial
       scrutinee.  The printer just expands the template. *)
    let text = custom_match_text cmatch in
    let cmds = match_template text in
    pp_custom ctx ( "custom match for "
      ^ Pp.string_of_ppcmds (pp_cpp_type ctx false [] typ)
      ^ " := "
      ^ text )
      env
      (Some typ)
      (Some t)
      tyargs
      cases
      []
      []
      []
      cmds
  | Smatch (scrut, branches, default) ->
    writes_variant ();
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
    let pp_scrut = pp_cpp_expr ctx env args in
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
      ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
      ++ scrut_var_pp ++ str ")"
    in
    (* Helper: binding statement inside the if-block.
       - Structured bindings: [const auto& [f1, f2] = std::get<T>(scrut);]
       - Frame dispatch (no field bindings): [const auto& _f = std::get<T>(scrut);]
       - No binding: empty. *)
    let pp_block_binding scrut_var_pp br =
      match br.smb_field_bindings with
      | _ :: _ ->
        let binding_qual =
          if scrut.sc_owned then "auto& [" else "const auto& ["
        in
        if scrut.sc_flat then
          str binding_qual
          ++ prlist_with_sep (fun () -> str ", ")
               (fun fb -> Id.print fb.fb_name)
               br.smb_field_bindings
          ++ str "] = " ++ scrut_var_pp ++ str ";"
        else
          str binding_qual
          ++ prlist_with_sep (fun () -> str ", ")
               (fun fb -> Id.print fb.fb_name)
               br.smb_field_bindings
          ++ str "] = " ++ str (sn ()).get ++ str "<"
          ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
          ++ scrut_var_pp ++ str ");"
      | [] ->
        ( match br.smb_var with
        | Some var_id ->
          if scrut.sc_owned then
            str "auto " ++ Id.print var_id
            ++ str " = std::move(" ++ str (sn ()).get ++ str "<"
            ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
            ++ scrut_var_pp ++ str "));"
          else
            str "const auto& " ++ Id.print var_id
            ++ str " = " ++ str (sn ()).get ++ str "<"
            ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
            ++ scrut_var_pp ++ str ");"
        | None -> mt () )
    in
    (* Extract the scrutinee object expression from the variant accessor.
       Handles both [CPPaccess_call (Aarrow, obj, "v", [])] (pointer:
       [obj->v()])
       and [CPPfun_call(CPPaccess (Adot, obj, "v"), [])] (value: [obj.v()]).
       Bind temporaries with [auto&&] to extend lifetime, then reconstruct
       the accessor. *)
    let first_scrut = scrut.sc_expr in
    let is_value_type = scrut.sc_access = Adot in
    let scrut_obj_opt =
      match first_scrut with
      | CPPaccess_call (Aarrow, obj, v_id, []) when Id.to_string v_id = "v" ->
        Some obj
      | CPPfun_call (_, CPPaccess (Adot, obj, v_id), {rev = []})
        when Id.to_string v_id = "v" ->
        Some obj
      | _ -> None
    in
    let is_receiver_obj = function
      | CPPthis | CPPderef CPPthis -> true
      | _ -> false
    in
    let is_owned =
      scrut.sc_owned
      &&
      match scrut_obj_opt with
      | Some obj -> not (is_receiver_obj obj)
      | None -> true
    in
    let v_access name =
      if is_value_type then
        name ^ (if is_owned then ".v_mut()" else ".v()")
      else
        name ^ (if is_owned then "->v_mut()" else "->v()")
    in
    let scrut_binding_pp, scrut_var_pp, _scrut_obj_pp =
      match scrut_obj_opt with
      | Some (CPPvar id) ->
        let name = Id.to_string id in
        (mt (), str (v_access name), str name)
      | Some CPPthis | Some (CPPderef CPPthis) ->
        (mt (), str (if is_owned then "this->v_mut()" else "this->v()"), str "(*this)")
      | Some obj_expr ->
        let obj_pp = pp_scrut obj_expr in
        ( str ("auto&& " ^ sv_name ^ " = ") ++ obj_pp ++ str ";" ++ fnl (),
          str (v_access sv_name), str sv_name )
      | None ->
        ( match first_scrut with
        | CPPvar id ->
          let name = Id.to_string id in
          (mt (), str name, str name)
        | CPPderef CPPthis ->
          (mt (), str "*this", str "(*this)")
        | _ ->
          let raw_pp = pp_scrut first_scrut in
          ( str ("const auto& " ^ sv_name ^ " = ") ++ raw_pp ++ str ";" ++ fnl (),
            str sv_name, str sv_name ) )
    in
    if n_branches = 1 && default = None then
      (* Single-constructor exhaustive match: emit binding + body inline.
         No if/else needed. *)
      let br = match branches with br :: _ -> br
        | [] -> CErrors.anomaly (Pp.str "pp_cpp_stmt ctx Smatch: empty branch list") in
      let binding = pp_block_binding scrut_var_pp br in
      let body_pp = pp_list_stmt (pp_cpp_stmt ctx env args) br.smb_body in
      if binding = mt () then body_pp
      else scrut_binding_pp ++ binding ++ fnl () ++ body_pp
    else
    let pp_branch i br =
      let keyword = if i = 0 then "if" else "} else if" in
      let is_last_no_wild =
        i = n_branches - 1 && default = None && n_branches > 1
      in
      let binding = pp_block_binding scrut_var_pp br in
      let normal_body_pp = pp_list_stmt (pp_cpp_stmt ctx env args) br.smb_body in
      let body_pp =
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
                (pp_cpp_expr ctx env args)
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
        ++ fnl () ++ pp_list_stmt (pp_cpp_stmt ctx env args) stmts
      | None when branches = [] ->
        str "std::unreachable();"
      | None ->
        mt ()
    in
    branches_pp ++ default_pp ++ fnl () ++ str "}"

(** Render a custom extraction syntax template by substituting placeholder
    tokens with pretty-printed C++ fragments.

    {b Placeholder tokens:}
    - [CCstring s] — literal string, emitted verbatim.
    - [CCscrut] — the scrutinee expression (for match-style custom extractions).
      Wrapped in [std::any_cast] when the scrutinee type doesn't match the
      expected type.
    - [CCty] — the full C++ type of the expression being extracted.
    - [CCty_arg i] — the [i]-th type argument of the applied type constructor
      (e.g. for [list<int>], [CCty_arg 0] = [int]).
    - [CCarg i] — the [i]-th function argument, pretty-printed as a C++
      expression.  Compound expressions are parenthesized when followed by [.]
      (member access) to prevent binding errors.
    - [CCbr_var (i, j)] — the [j]-th pattern variable name from the [i]-th
      match branch.
    - [CCbr_var_ty (i, j)] — the type of the [j]-th pattern variable in the
      [i]-th branch.
    - [CCbody i] — the full statement body of the [i]-th match branch.
    - [CCresult] — (handled upstream) the result expression in tail position.

    @param custom  the raw custom syntax string (for error messages)
    @param env     name environment for pretty-printing sub-expressions
    @param typ     optional expected C++ type (for [CCty] and any-cast wrapping)
    @param t       optional scrutinee expression (for [CCscrut])
    @param tyargs  type arguments for [CCty_arg]
    @param cases   match branches as [(ids, rty, stmts)] triples
    @param args    function argument expressions for [CCarg]
    @param arg_types  expected types for each arg (for any-cast wrapping)
    @param vl      type variable names in scope
    @param cmds    parsed placeholder token list to substitute *)
(* A string literal spliced into a mapping's C++ template, as the string object
   the template's operations expect ([std::string("(") + p(a)]).  Spelled as a
   construction rather than with the [s] literal suffix, which would need a
   [using namespace] in every header that splices one. *)
and string_object printed =
  writes_standard "string";
  str (sn ()).string ++ str "(" ++ printed ++ str ")"

and pp_custom ?container ctx custom env typ t tyargs cases args _arg_types vl cmds =
  (* Every read of a boxed value the template needs at a concrete type was
     made explicit by {!Cpp_erasure.lower_boxed_reads}; this prints. *)
  let pp ?(followed_by_dot=false) cmd =
    match cmd with
    | CCstring s -> str s
    | CCscrut ->
      ( match t with
      | Some t_expr ->
        let t_printed = pp_cpp_expr ctx env [] t_expr in
        ( match t_expr with
        | CPPstring _ -> string_object t_printed
        (* A custom match template splices [%scrut] in as text and appends
           to it, so a scrutinee carrying a prefix operator would bind
           looser than whatever follows.  A recursive occurrence nested
           under a mapped type (e.g. [option chain]) is stored behind a
           smart pointer, so the scrutinee prints as [*a1] and the option
           template's [%scrut.has_value()] came out as [*a1.has_value()] --
           the member access binding to [a1] rather than to the pointee,
           which does not compile.  Parenthesize so the operator keeps its
           intended operand.

           Only the pointer operators need this: they are the ones a
           template can follow with a member access.  The logical and
           arithmetic prefixes ([!], [-], [~]) already bind tighter than
           anything a template appends after [%scrut], so parenthesizing
           them would only add noise to the generated code. *)
        | _
          when (let s = Pp.string_of_ppcmds t_printed in
                String.length s > 0
                && (match s.[0] with
                    | '*' | '&' -> true
                    | _ -> false)) ->
          surround t_printed
        | _ -> t_printed )
      | None ->
        CErrors.anomaly
          (Pp.str "Custom syntax: scrutinee token with no bound expression") )
    | CCty ->
      ( match typ with
      | Some typ -> pp_cpp_type ctx false vl typ
      | None ->
        CErrors.anomaly (Pp.str "Custom syntax: type token with no bound type")
      )
    | CCbody i ->
      ( try
          let _, _, ss = List.nth cases i in
          pp_list_stmt (pp_cpp_stmt ctx env []) ss
        with Failure _ ->
          CErrors.anomaly
            Pp.(str "Custom syntax: unbound case body in: " ++ str custom) )
    | CCty_arg i ->
      ( match List.nth_opt tyargs i with
        | Some ty -> pp_cpp_type ctx false vl ty
        | None -> pp_cpp_type ctx false vl Tany
      )
    | CCelem i ->
      (* Like CCty_arg, but wrap the element in the container's [Boxed Element]
         wrapper when the element recurses through a boxed-element container. *)
      let elem_ty =
        match List.nth_opt tyargs i with Some ty -> ty | None -> Tany
      in
      let base = pp_cpp_type ctx false vl elem_ty in
      let container_ref =
        match container with
        | Some _ -> container
        | None ->
          ( match typ with
          | Some (Tglob (g, _, _)) -> Some g
          | Some (Tnamespace (_, Tglob (g, _, _))) -> Some g
          | _ -> None )
      in
      ( match container_ref with
      | Some g
        when (not !suppress_elem_boxing)
             && cpp_type_mentions_boxed_recursive elem_ty ->
        let ind =
          match g with
          | GlobRef.ConstructRef (ip, _) -> GlobRef.IndRef ip
          | _ -> g
        in
        ( match Table.find_boxed_wrapper_opt ind with
        | Some w -> str (subst_wrapper_t0 w (Pp.string_of_ppcmds base))
        | None -> base )
      | _ -> base )
    | CCbr_var (i, j) ->
      ( try
          let ids, _, _ = List.nth cases i in
          Id.print (List.nth ids j).cp_name
        with Failure _ ->
          CErrors.anomaly
            Pp.(
              str "Custom syntax: unbound case branch variable in: "
              ++ str custom ) )
    | CCbr_var_ty (i, j) ->
      ( try
          let ids, _, _ = List.nth cases i in
          (* Spellable: one that is not was materialised at the seam
             ({!Cpp_erasure.materialise}). *)
          pp_cpp_type ctx false vl (List.nth ids j).cp_type
        with Failure _ ->
          CErrors.anomaly
            Pp.(
              str "Custom syntax: unbound case branch type argument in: "
              ++ str custom ) )
    | CCarg i ->
    try
      let arg_expr = List.nth args i in
      let arg = pp_cpp_expr ctx env [] arg_expr in
      let arg =
        match arg_expr with
        | CPPstring _ -> string_object arg
        | _ -> arg
      in
      (* Parenthesize compound expressions that would bind incorrectly
         when followed by member access (.c_str() etc.) in templates. *)
      if followed_by_dot then
        match arg_expr with
        | CPPbinop _ -> str "(" ++ arg ++ str ")"
        | CPPfun_call (_, CPPglob (_, _, Some ci), _) when ci.ci_inline <> None ->
          str "(" ++ arg ++ str ")"
        (* A prefix pointer operator binds looser than the member access
           the template appends, so [%a0.first] applied to a scrutinee
           that prints as [*a0] came out as [*a0.first] -- the [.first]
           attaching to the pointer rather than the pointee.  This is the
           same hazard [CCscrut] guards against; see the comment there for
           why only [*] and [&] need it. *)
        | _
          when (let s = Pp.string_of_ppcmds arg in
                String.length s > 0
                && (match s.[0] with '*' | '&' -> true | _ -> false)) ->
          str "(" ++ arg ++ str ")"
        | _ -> arg
      else arg
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


(** Pretty-print an already-converted MiniCpp type with no parenthesization and
    no type-variable context; the common-case shorthand for {!pp_cpp_type}. *)
let pp_type ctx t = pp_cpp_type ctx false [] t

(* A callable parameter whose constraint was never settled from its body
   ({!Minicpp.settle_constraints}) is printed unconstrained -- a constraint
   guessed from its declared type could name the wrong operands.  Under
   [CRANE_CHECK_IR] none gets here: the seam checks that the constraints were
   settled ({!Cpp_pipeline.finish}). *)
(** Print a template parameter type keyword (typename or concept constraint). *)
let pp_template_type ctx = function
  | TTtypename -> str "typename"
  | TTtypename_default _ -> str "typename"
  | TTtemplate arity ->
    str "template <"
    ++ prlist_with_sep (fun () -> str ", ") (fun _ -> str "typename")
         (List.init arity Fun.id)
    ++ str "> class"
  | TTfun _ | TTinvocable _ -> str "typename"
  | TTconcept (concept, _) when class_concept_held_back ctx concept ->
    str "typename"
  | TTconcept (concept, []) -> pp_concept_name_of_ref ctx concept
  | TTconcept (_, _ :: _) ->
    (* Multi-parameter concept: the constraint cannot be written inline
       ([C _tcI0] would apply C to only one argument), so declare the
       parameter as a plain [typename] and attach [requires C<_tcI0, …>]
       via {!pp_requires_of_tparams}. *)
    str "typename"

(** Print a complete template parameter including name and optional default *)
let pp_template_param ctx (tt, id) =
  match tt with
  | TTtypename_default default_ty ->
    str "typename"
    ++ spc ()
    ++ Id.print id
    ++ str " = "
    ++ pp_type ctx default_ty
  | _ -> pp_template_type ctx tt ++ spc () ++ Id.print id

(** [template <...> ] prefix for a declaration, or nothing when the parameter
    list is empty. *)
let pp_template_header ctx = function
  | [] -> mt ()
  | tparams -> str "template <" ++ pp_list (pp_template_param ctx) tparams ++ str "> "

(** Print a template parameter for a re-declaration: same kind, but without the
    default argument, which C++ allows to appear only once per parameter. *)
let pp_template_param_redecl ctx (tt, id) = pp_template_type ctx tt ++ spc () ++ Id.print id

(** Build a [requires] clause from template parameters that have [TTfun]
    constraints.  Each [TTfun(dom, cod)] with parameter name [F] becomes
    [std::is_invocable_r_v<cod, F &, dom1 &, dom2 &, ...>].  Returns [None]
    when no [TTfun] parameters are present.  In BDE mode, uses
    [bsl::is_invocable_r_v] instead.

    @param tparams  list of [(template_type, id)] pairs from the surrounding
                    template parameter declaration
    @return [Some pp] where [pp] is the full [requires ...] clause, or [None]
            if no [TTfun] constraints are present *)
let pp_requires_of_tparams ctx tparams =
  let invocable_r =
    if String.equal (Table.std_lib ()) "BDE" then "bsl::is_invocable_r_v"
    else "std::is_invocable_r_v"
  in
  let clauses =
    List.filter_map
      (fun (tt, id) ->
        match tt with
        (* What a callable must accept was settled from the body before
           printing: see {!Minicpp.settle_constraints}. *)
        | TTinvocable (invs, cod) ->
          writes_standard "type_traits";
          let operand cat ty =
            match cat with
            | Mutable_lvalue -> ty ++ str " &"
            | Const_lvalue -> str "const " ++ ty ++ str " &"
            | Xvalue -> ty ++ str " &&"
            | Prvalue -> ty
          in
          let clause inv =
            str invocable_r ++ str "<"
            ++ pp_type ctx cod
            ++ str ", "
            ++ operand inv.inv_callable (Id.print id)
            ++ List.fold_left
                 (fun acc (cat, ty) -> acc ++ str ", " ++ operand cat (pp_type ctx ty))
                 (mt ()) inv.inv_args
            ++ str ">"
          in
          Some (prlist_with_sep (fun () -> str " && ") clause invs)
        | TTfun _ -> None
        | TTconcept (concept, _) when class_concept_held_back ctx concept -> None
        | TTconcept (concept, (_ :: _ as args)) ->
          (* Multi-parameter concept constraint: [C<_tcI0, T1, …>].  The
             constrained parameter [id] is the first concept argument, the
             kept type args follow.  Emitting this as a [requires] clause is
             what enforces the Rocq typeclass interface at the use site
             instead of an unconstrained [typename] (CWE-693 / CWE-345). *)
          Some
            ( pp_concept_name_of_ref ctx concept ++ str "<"
            ++ Id.print id
            ++ List.fold_left
                 (fun acc ty -> acc ++ str ", " ++ pp_type ctx ty)
                 (mt ()) args
            ++ str ">" )
        | _ -> None)
      tparams
  in
  match clauses with
  | [] -> None
  | [c] -> Some (str "  requires " ++ c)
  | _ ->
    Some
      ( str "  requires "
      ++ List.hd clauses
      ++ List.fold_left
           (fun acc c -> acc ++ fnl () ++ str "      && " ++ c)
           (mt ()) (List.tl clauses) )

(** A struct's template head: its parameters, and the constraint its
    concept-kinded parameters and its own [requires] clause make.  The
    definition and a constrained forward declaration print it here, so a
    re-declaration repeats the constraint token for token -- which is what
    makes the compiler see the two as one. *)
let struct_template_head ~pp_param ctx env tparams cstr =
  match tparams with
  | [] -> mt ()
  | _ ->
    let args = pp_list pp_param tparams in
    let req = pp_requires_of_tparams ctx tparams in
    let cstr_pp = match (req, cstr) with
      | None, None -> mt ()
      | Some r, None -> r ++ fnl ()
      | None, Some c -> pp_cpp_expr ctx env [] c ++ fnl ()
      | Some r, Some c -> r ++ str " && " ++ pp_cpp_expr ctx env [] c ++ fnl ()
    in
    (str "template <" ++ args ++ str ">")
    ++ cstr_pp

(** Render a doc comment as [///]-prefixed lines followed by a newline, or
    [mt ()] if no comment is registered for [name].  This is the single lookup
    point used by field, constructor-struct, and enum-value printers.

    @param indent  optional prefix prepended to every line (e.g. ["  "] for
    indented contexts such as enum values).  Defaults to [""]. *)
let pp_doc_comment_for_name = Doc_comments.pp

(** The synthesised templates spelled, in [file], at the type constructors
    [visit] calls its argument at, in the order spelled -- one written in
    another's body ahead of it -- each spelled as the printer spells it in
    that file, inside the struct of the inductive whose members are written
    around it, if any ({!Cpp_resolution.Inductive_struct}). *)
let ctor_aliases_found ~file visit =
  writing_file file @@ fun () ->
  setting collecting_ctor_aliases true @@ fun () ->
  setting ctor_aliases_spelled [] @@ fun () ->
  visit (fun ~vl ~owner t ->
      match t with
      | Ttyctor _ ->
        let spell () = ignore (pp_cpp_type !render_ctx false vl t) in
        ( match owner with Some r -> enter (Inductive_struct r) spell | None -> spell () )
      | _ -> () );
  !ctor_aliases_spelled

let ctor_aliases_written ~file (d : Cpp_erasure.settled) =
  { read_written = (module_written !render_ctx, Written_declaration (d :> cpp_decl));
    read_aliases = ctor_aliases_found ~file (fun f -> Cpp_demands.tyctors_of_decl f (d :> cpp_decl)) }

let ctor_aliases_of_fields ~file ~vl r types =
  { read_written = (module_written !render_ctx, Written_fields r);
    read_aliases = ctor_aliases_found ~file (fun f -> List.iter (Cpp_demands.tyctors_of_type f ~vl) types) }

(** The synthesised templates [w], written in the module [module_], writes
    in the file being written, as planned. *)
let planned_aliases ~module_ w =
  match !ctor_alias_plan with
  | None -> []
  | Some plan -> (
    let file = (!render_ctx).rc_file in
    let writes = match file with Common.Intf -> plan.intf_writes | Common.Impl -> plan.impl_writes in
    match Written.find_opt writes (module_, w) with
    | Some aliases -> aliases
    | None ->
      let what = match w with Written_declaration _ -> "a declaration" | Written_fields _ -> "the fields of a record" in
      CErrors.anomaly
        Pp.(str "Crane: " ++ str what ++ str " of the " ++ str (Common.file_name file) ++ str " in "
            ++ str (ModPath.to_string module_)
            ++ str " are written that were not read when their templates were planned.") )

(** The synthesised templates the finished declaration [d], written in the
    module [module_], writes in the file being written, as planned. *)
let planned_ctor_aliases ~module_ (d : Cpp_erasure.settled) = planned_aliases ~module_ (Written_declaration (d :> cpp_decl))

(** The synthesised templates the finished declaration [d] writes in the
    file being written, as an element of the module the render context
    names, as planned; under [CRANE_CHECK_IR], spelled again and
    compared. *)
let ctor_aliases_planned (d : Cpp_erasure.settled) =
  match !ctor_alias_plan with
  | None -> []
  | Some _ ->
    let ctx = !render_ctx in
    let aliases = planned_ctor_aliases ~module_:(module_written ctx) d in
    let file = ctx.rc_file in
    if Probe.checking () && (ctor_aliases_written ~file d).read_aliases <> aliases then
      Probe.violation "constructor aliases"
        Pp.(str "a declaration of the " ++ str (Common.file_name file)
            ++ str " writes other templates than were planned for it");
    aliases

(** Where a member is being written.

    A member's signature is spelled the same in all three places, so one
    printer serves them: what differs is the name it is written under, and
    whether the body follows. *)
type member_mode =
  | Mm_inline  (** In the struct, with its body. *)
  | Mm_declared  (** In the struct, without its body: ends at the [;]. *)
  | Mm_defined of Pp.t * (template_type * Id.t) list
      (** Out of line, under the given qualifier, for a struct with the given
          template parameters. *)

(** The [template <...>] line a struct's parameters call for, if any. *)
let pp_owner_template ctx = function
  | [] -> mt ()
  | tps -> (str "template <" ++ pp_list (pp_template_param ctx) tps ++ str ">") ++ fnl ()

(** Pretty-print a single MiniCpp struct field as C++ source.

    @param struct_name  the enclosing struct's pretty-printed name, forwarded
                        to constructor and destructor printers that need it
    @param env          name environment for sub-expression pretty-printing *)
let rec pp_cpp_field ?(struct_name : Pp.t option) ?(mode = Mm_inline) ctx env = function
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
    ++ (pp_type ctx ty ++ str " " ++ Id.print id ++ str ";")
  | Fvar' (id, ty) ->
    (* A field's name lives in its struct, not in the enclosing namespace, so
       it must not be registered as occupying one: a field named after a type
       the same module refers to would otherwise look like a clash and send
       that type through a duplicate wrapper.  Reads spell the field the same
       way (see [CPPget']). *)
    pp_doc_comment_for_name (Common.pp_global_name Type id)
    ++ (pp_type ctx ty ++ str " " ++ str (Common.pp_global_name Type id)
          ++ str ";")
  | Fmethod
      {
        mf_name;
        mf_tparams;
        mf_ret_type;
        mf_params;
        mf_body;
        mf_receiver;
        mf_is_inline;
        mf_constexpr;
        mf_is_noexcept;
        mf_is_conversion;
      } ->
    let const_s =
      match mf_receiver with
      | Static -> mt ()
      | Instance {is_const; ref_qual; _} -> (
        (if is_const then str " const" else mt ())
        ++
        match ref_qual with
        | Rq_any -> mt ()
        | Rq_lvalue -> str " &"
        | Rq_rvalue -> str " &&" )
    in
    let mf_is_static = mf_receiver = Static in
    let noexcept_s = if mf_is_noexcept then str " noexcept" else mt () in
    (* [static] belongs to the declaration alone, and an out-of-line
       definition in a header needs [inline] unless a template already
       exempts it from the one-definition rule. *)
    let static_s =
      match mode with
      | Mm_defined _ -> mt ()
      | Mm_inline | Mm_declared -> if mf_is_static then str "static " else mt ()
    in
    let inline_s =
      match mode with
      | Mm_inline -> if mf_is_inline then str "inline " else mt ()
      | Mm_declared -> mt ()
      | Mm_defined (_, owner_tps) ->
        if owner_tps = [] && mf_tparams = [] then str "inline " else mt ()
    in
    let body_s = pp_list_stmt (pp_cpp_stmt ctx env []) mf_body in
    let read = Minicpp.reads_as_printed mf_body in
    let params_s =
      pp_list
        (fun (id, ty) ->
          if
            (not (read id))
            && not (String.equal (Id.to_string mf_name) "operator=")
          then pp_type ctx ty
          else pp_type ctx ty ++ str " " ++ Id.print id)
        mf_params
    in
    let template_s =
      match mf_tparams with
      | [] -> mt ()
      | _ ->
        let args = pp_list (pp_template_param ctx) mf_tparams in
        let req = pp_requires_of_tparams ctx mf_tparams in
        str "template <" ++ args ++ str ">" ++ fnl ()
        ++ ( match req with
           | None -> mt ()
           | Some r -> r ++ fnl () )
    in
    let doc_comment = pp_doc_comment_for_name (Id.to_string mf_name) in
    let qualifier = if may_be_constexpr mf_constexpr then str "constexpr " else mt () in
    let owner_template_s, qual_s =
      match mode with
      | Mm_defined (qual, owner_tps) ->
        (pp_owner_template ctx owner_tps, qual ++ str "::")
      | Mm_inline | Mm_declared -> (mt (), mt ())
    in
    (* A conversion function has no return type of its own -- its name is the
       type it converts to -- and none of the qualifiers apply. *)
    let head =
      h
        ( inline_s
        ++ ( if mf_is_conversion then
               qual_s ++ str "operator " ++ pp_type ctx mf_ret_type
             else
               qualifier ++ static_s ++ pp_type ctx mf_ret_type ++ str " "
               ++ qual_s ++ Id.print mf_name )
        ++ pp_par true params_s
        ++ const_s
        ++ noexcept_s )
    in
    doc_comment
    ++ owner_template_s
    ++ template_s
    ++
    ( match mode with
    | Mm_declared -> head ++ str ";"
    | Mm_inline | Mm_defined _ -> head ++ str " {" ++ fnl () ++ body_s ++ str "}" )
  | Fconstructor
      { fc_tparams; fc_params; fc_inits; fc_body; fc_explicit; fc_noexcept } ->
    let sname =
      match struct_name with Some s -> s | None -> str "UNKNOWN_STRUCT"
    in
    let template_s =
      match fc_tparams with
      | [] -> mt ()
      | _ ->
        str "template <" ++ pp_list (pp_template_param ctx) fc_tparams ++ str ">"
        ++ fnl ()
    in
    let params_s =
      pp_list (fun (id, ty) -> pp_type ctx ty ++ str " " ++ Id.print id) fc_params
    in
    let init_s =
      match fc_inits with
      | [] -> mt ()
      | _ ->
        str " : "
        ++ pp_list
             (fun (member, expr) ->
               Id.print member ++ str "(" ++ pp_cpp_expr ctx env [] expr ++ str ")" )
             fc_inits
    in
    let explicit_s = if fc_explicit then str "explicit " else mt () in
    let noexcept_s = if fc_noexcept then str " noexcept" else mt () in
    let head =
      (explicit_s ++ sname ++ pp_par true params_s ++ noexcept_s ++ init_s)
    in
    template_s
    ++ ( match fc_body with
       | [] -> head ++ str " {}"
       | _ ->
         head ++ str " {" ++ fnl ()
         ++ pp_list_stmt (pp_cpp_stmt ctx env []) fc_body
         ++ str "}" )
  | Fdestructor body ->
    let sname =
      match struct_name with
      | Some s -> s
      | None -> str "UNKNOWN_STRUCT"
    in
    ( match mode with
    | Mm_declared -> (str "~" ++ sname ++ str "();")
    | Mm_inline ->
      (str "~" ++ sname ++ str "() {")
      ++ fnl ()
      ++ pp_list_stmt (pp_cpp_stmt ctx env []) body
      ++ fnl ()
      ++ str "}"
    | Mm_defined (qual, owner_tps) ->
      pp_owner_template ctx owner_tps
      ++ h
           ( (if owner_tps = [] then str "inline " else mt ())
           ++ qual ++ str "::~" ++ sname ++ str "() {" )
      ++ fnl ()
      ++ pp_list_stmt (pp_cpp_stmt ctx env []) body
      ++ fnl ()
      ++ str "}" )
  | Fnested_struct (id, fields) ->
    let fields_s =
      pp_cpp_fields_with_vis ctx ~struct_name:(Id.print id) env fields
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
    ++ (str "struct " ++ Id.print id ++ str " {")
    ++ fnl ()
    ++ fields_s
    ++ fnl ()
    ++ str "};"
  | Fdeferred_struct {dfs_name; dfs_selves; dfs_fields} ->
    let tmpl = Id.to_string dfs_name ^ "_" in
    h
      ( str "template <"
      ++ pp_list
           (fun (id, ty) ->
             str "typename " ++ Id.print id ++ str " = "
             ++ pp_cpp_type ctx false [] ty )
           dfs_selves
      ++ str "> struct " ++ str tmpl ++ str " {" )
    ++ fnl ()
    ++ prlist_with_sep fnl
         (fun (id, ty) -> (pp_cpp_type ctx false [] ty ++ spc () ++ Id.print id ++ str ";"))
         dfs_fields
    ++ fnl ()
    ++ str "};"
    ++ fnl ()
    ++ (str "using " ++ Id.print dfs_name ++ str " = " ++ str tmpl ++ str "<>;")
  | Fnested_using (tparams, id, ty) ->
    h
      ( ( if tparams = [] then mt ()
          else
            str "template <"
            ++ pp_list (pp_template_param ctx) tparams
            ++ str "> " )
      ++ str "using "
      ++ Id.print id
      ++ str " = "
      ++ pp_type ctx ty
      ++ str ";" )
  | Fmember_decl m ->
    pp_cpp_field ctx ?struct_name ~mode:Mm_declared env (field_of_member m)
  | Fdeleted_ctor ->
    let sname =
      match struct_name with
      | Some s -> s
      | None -> str "UNKNOWN_STRUCT"
    in
    (sname ++ str "() = delete;")
  | Fdefaulted_special_members ->
    let sname =
      match struct_name with
      | Some s -> s
      | None -> str "UNKNOWN_STRUCT"
    in
    (* A user-declared destructor suppresses the implicit move ctor/assign and
       deprecates the implicit copies; declaring the moves would then delete the
       implicit copies.  Re-default all four so the value keeps cheap move
       semantics (no refcount bump) while staying copyable.  No exception
       specification: a defaulted move is noexcept exactly when its members'
       moves are, and a payload of a generic type may throw -- spelling
       [noexcept] would turn that throw into [std::terminate]. *)
    (sname ++ str "(const " ++ sname ++ str "&) = default;")
    ++ fnl ()
    ++ (sname ++ str "& operator=(const " ++ sname ++ str "&) = default;")
    ++ fnl ()
    ++ (sname ++ str "(" ++ sname ++ str "&&) = default;")
    ++ fnl ()
    ++ (sname ++ str "& operator=(" ++ sname ++ str "&&) = default;")

(** Print the body of a struct: groups fields by [(visibility, section_tag)],
    emits [public:]/[private:] labels only when necessary, and inserts
    section-tag comments (e.g. [// TYPES], [// DATA]).

    @param struct_name  forwarded to {!pp_cpp_field} for constructor/destructor
    @param env          name environment for sub-expression pretty-printing
    @param fields       list of [(field, visibility, section_tag)] triples *)
and pp_cpp_fields_with_vis ?(struct_name : Pp.t option) ctx env fields =
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
      vis_pp ++ tag_pp ++ pp_list_stmt (pp_cpp_field ctx ?struct_name env) flds
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
      ++ pp_list_stmt (pp_cpp_field ctx ?struct_name env) flds
      ++ fnl ()
      ++ pp_groups vis rest
  in
  pp_groups VPublic groups

(** Generate a Meyers' singleton accessor for a static data member. Wraps the
    initializer in a function with a local [static const] variable, guaranteeing
    initialization on first use. This avoids the static initialization order
    fiasco for template static inline members whose initialization order
    relative to other inline variables is unspecified.

    The accessor was planned before rendering ({!Cpp.plan_accessors}), so that
    call sites append [()] after the template arguments (see {!pp_cpp_expr}).

    @param env      name environment (passed through for sub-expression use)
    @param id       global reference identifying the data member (used for the
                    function name and to register in [template_static_accessors])
    @param ty       C++ type of the data member; [const] modifier is stripped
                    before use inside the function body
    @param expr_pp  already pretty-printed initializer expression *)
let pp_meyers_singleton ctx env id ty expr_pp =
  if not (is_template_static_accessor (modpath_of_r id) (label_of_r id)) then
    Probe.violation "template static accessors"
      Pp.(str "the accessor " ++ GlobRef.print id ++ str " was printed without being planned");
  let bare_ty =
    match ty with
    | Tconst inner -> inner
    | _ -> ty
  in
  h
    ( str "static const "
    ++ pp_type ctx bare_ty
    ++ str "& "
    ++ pp_global ctx Type id
    ++ str "() {" )
  ++ fnl ()
  ++ str "  static const "
  ++ pp_type ctx bare_ty
  ++ str " v = "
  ++ expr_pp
  ++ str ";"
  ++ fnl ()
  ++ str "  return v;"
  ++ fnl ()
  ++ str "}"

(** The name the struct wrapping an inductive at namespace scope is written
    under.  An inductive's wrapper is named after the inductive, capitalised;
    anything else is spelled as itself. *)
let nspace_wrapper_name ctx id =
  Table.escape_reserved_struct_name
    ( match id with
    | GlobRef.IndRef _ -> String.capitalize_ascii (str_global ctx Type id)
    | _ -> string_of_ppcmds (pp_global ctx Type id) )

(** Whether the inductive [r] is written inside a wrapper that other
    declarations were queued against -- a file module of the same name, whose
    functions go in beside it -- and so is spelled [List::list] rather than
    [List].  A struct written inside another is named by member lookup, which
    no forward declaration answers.  Planned ({!in_unmerged_wrapper}), so the
    answer does not depend on whether the wrapper has been written yet. *)
let nested_in_wrapper = in_unmerged_wrapper

(** Whether a wrapper and the struct inside it are written as one struct
    rather than two.  A sole struct is merged into its wrapper and takes the
    wrapper's name; a wrapper holding anything else, or one that declarations
    were queued against, keeps both levels, and the struct inside keeps its own
    name underneath.

    Whether that struct is a template has nothing to do with it -- both merge
    branches below handle one -- so this asks only about the wrapper.

    Asked by {!pp_cpp_decl} of the declaration and by the out-of-line
    member definition of its owner, which must agree about how many names the
    qualifier has. *)
let nspace_merges (w : dm_wrapper) : bool =
  w.dw_sole_child && not (nested_in_wrapper w.dw_ref)

(** The name the struct of [id] is defined under. *)
let struct_definition_name ctx id = Cpp_name.pp (Cpp_names.struct_definition_name ctx id)

(** The name the scoped enum of [r] is defined under. *)
let enum_definition_name ctx r = Cpp_name.pp (Cpp_names.enum_definition_name ctx r)

(** The names of the wrapper structs [d] writes around something other than
    a sole struct merged into them, in the order it writes them: the structs
    another wrapper's declarations can be written into. *)
let rec unmerged_wrappers_written ctx (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> unmerged_wrappers_written ctx inner
  | Namespace (None, decls) -> List.concat_map (unmerged_wrappers_written ctx) decls
  | Namespace (Some id, members) ->
    let sole_child = match (members :> cpp_decl list) with [Dstruct _] -> true | _ -> false in
    if nspace_merges {dw_ref = id; dw_sole_child = sole_child} then []
    else List.concat_map (unmerged_wrappers_written ctx) members @ [nspace_wrapper_name ctx id]
  | Decl _ -> []

(** The assertions [d] holds back, in the order it writes them: those that
    a class's concept holds of an instance where the concept is declared
    after the struct being written, because its requirements name the
    struct's own types. *)
let rec held_back_assertions ctx (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> held_back_assertions ctx inner
  | Namespace (None, decls) -> List.concat_map (held_back_assertions ctx) decls
  | Namespace (Some id, members) ->
    let sole_child = match (members :> cpp_decl list) with [Dstruct _] -> true | _ -> false in
    if nspace_merges {dw_ref = id; dw_sole_child = sole_child} then []
    else List.concat_map (held_back_assertions ctx) members
  | Decl (Dstatic_assert (CPPconcept_app (class_ref, subject, tys), None)) when class_concept_held_back ctx class_ref ->
    [ { Cpp_ast.concept = Of_class (Cpp_ast.global_ref class_ref);
        subject = Instance {instance = Cpp_ast.global_ref subject; args = tys} } ]
  | Decl _ -> []

(** The structs and scoped enums [d] defines at namespace scope, written
    in the scope being written, in the order it defines them, each with the
    reference it is declared under, its definition's template head and its
    constraint. *)
let rec structs_defined (d : Cpp_erasure.settled) : Cpp_ast.defined list =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> structs_defined inner
  | Namespace (None, decls) -> List.concat_map structs_defined decls
  | Namespace (Some id, members) -> (
    match (members :> cpp_decl list) with
    | [Dstruct {ds_tparams; ds_constraint; _}] when nspace_merges {dw_ref = id; dw_sole_child = true} ->
      [Defined_struct {struct_ = id; name = As_inductive_wrapper; tparams = ds_tparams; constraint_ = ds_constraint}]
    | _ -> [] )
  | Decl (Dstruct {ds_ref; ds_tparams; ds_constraint; _}) ->
    [Defined_struct {struct_ = ds_ref; name = As_defined; tparams = ds_tparams; constraint_ = ds_constraint}]
  | Decl (Denum {de_ref; _}) -> [Defined_enum de_ref]
  | Decl _ -> []

let defined_ref : Cpp_ast.defined -> _ = function Defined_struct {struct_ = r; _} | Defined_enum r -> r

(** A forward declaration of a struct defined at namespace scope.

    A module struct can be emitted before an inductive a later module pulled
    up to global scope, so a member declaration may name a type whose
    definition comes further down the header ([static Prod<nat, nat>
    divmod(...)] ahead of [struct Prod]).  A declaration only needs the name
    to have been introduced, so the header's prologue declares them up front.
    Printed by the function that prints the definition's template head, so
    the two spellings of the parameter list cannot drift apart.

    A constrained template -- a [requires] clause on the struct, or a
    concept-kinded parameter -- names its concept, which need not be declared
    by that prologue, nor anywhere above the struct's first use; its
    declaration goes in front of the first chunk of the file that names the
    struct before defining it ({!Cpp.do_struct_with_decl_tracking}): a
    section-local instance's struct and the file module's struct can each
    name the other, [typename StateV<_tcI0>::state] in a member's signature
    against a call to that member in the instance's body.

    An opaque declaration of a scoped enum is one too: [enum class E;] is a
    complete type -- a scoped enum has a fixed underlying type -- so replaying
    it in the header prologue is enough for the members naming it ahead of
    its definition, which still follows in its own place. *)
type forward_declaration = {fwd_ref : GlobRef.t; fwd_tree : Cpp_ast.t; fwd_constrained : bool}

(* Whether [tparams] make the [requires] clause {!pp_requires_of_tparams}
   prints. *)
let makes_requires_clause ctx tparams =
  List.exists
    (fun (tt, _) ->
      match tt with
      | TTinvocable _ -> true
      | TTconcept (concept, _ :: _) -> not (class_concept_held_back ctx concept)
      | _ -> false )
    tparams

let constrained ctx : Cpp_ast.defined -> bool = function
  | Defined_struct {tparams; constraint_; _} ->
    Option.has_some constraint_ || makes_requires_clause ctx tparams
    || List.exists (function TTconcept _, _ -> true | _ -> false) tparams
  | Defined_enum _ -> false

(** The forward declarations of the structs and scoped enums [d], an element
    of the module [module_], defines at namespace scope, in the order it
    defines them: none inside a struct, where a member is not nameable before
    its enclosing struct anyway. *)
let forward_declarations ~module_ env (d : Cpp_erasure.settled) =
  let ctx = !render_ctx in
  if ctx.rc_in_struct then []
  else
    List.map
      (fun defined ->
        { fwd_ref = defined_ref defined;
          fwd_tree = Cpp_ast.elements ~source:module_ (Cpp_ast.forward_declaration env defined);
          fwd_constrained = constrained ctx defined } )
      (structs_defined d)

let pp_forward_declaration ctx env : Cpp_ast.defined -> _ = function
  | Defined_struct {struct_; name; tparams; constraint_} ->
    let name = match name with As_defined -> struct_definition_name ctx struct_ | As_inductive_wrapper -> str (nspace_wrapper_name ctx struct_) in
    struct_template_head ~pp_param:(pp_template_param_redecl ctx) ctx env tparams constraint_ ++ str "struct " ++ name ++ str ";"
  | Defined_enum r -> str "enum class " ++ enum_definition_name ctx r ++ str ";"

(** The type names [d], written at namespace scope, introduces there, as the
    printer writes them ({!note_file_scope_type}): its own, through a
    template head and an anonymous namespace, and a struct's -- but not
    those of what a wrapper struct holds, which are its members. *)
let file_scope_types (d : Cpp_erasure.settled) =
  let ctx = !render_ctx in
  let rec go (d : Cpp_erasure.settled) =
    (match decl_type_name ctx (d :> cpp_decl) with Some name -> [name] | None -> [])
    @
    match Cpp_erasure.view d with
    | Template (_, _, inner) -> go inner
    | Namespace (None, decls) -> List.concat_map go decls
    | Decl (Dstruct {ds_ref; _}) -> [struct_definition_name ctx ds_ref]
    | Namespace (Some _, _) | Decl _ -> []
  in
  List.map Pp.string_of_ppcmds (go d)

let start_file_scope_census () = file_scope_types_written := CString.Set.empty

(** Under [CRANE_CHECK_IR], the type names the file [file] introduced at
    file scope must be the ones planned for it. *)
let check_file_scope_types ~file =
  if Probe.checking () then begin
    let written = !file_scope_types_written and planned = !file_scope_type_names in
    file_scope_types_written := CString.Set.empty;
    if not (CString.Set.equal written planned) then
      Probe.violation "file-scope types"
        Pp.(
          str "the " ++ str (Common.file_name file) ++ str " introduced "
          ++ prlist_with_sep pr_comma str (CString.Set.elements (CString.Set.diff written planned))
          ++ str " unplanned, and not "
          ++ prlist_with_sep pr_comma str (CString.Set.elements (CString.Set.diff planned written)) )
  end

(** [pp_initialiser ctx env ty e] prints [e] as the initialiser of something
    declared with type [ty].

    A {!CPPabort} never returns, so the type it should be spelled with comes
    entirely from where it sits; here that is [ty].  Everywhere else the
    expression printer already knows enough. *)
let rec pp_initialiser ctx env ty e =
  match e with
  | CPPabort (msg, _) ->
    writes_standard "stdexcept";
    (* The lambda returns by value, so a top-level [const] on [ty] says
       nothing and [-Wignored-qualifiers] rejects it. *)
    let ret_ty = match ty with Tconst t -> t | t -> t in
    str "([]() -> "
    ++ pp_type ctx ret_ty
    ++ str " { throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str (escape_cpp_string msg)
    ++ str "\"); })()"
  | _ -> pp_cpp_expr ctx env [] e

(** Pretty-print a settled MiniCpp declaration as C++ source: every type here
    is spelled the way it will be written out, and the passes that settle a
    declaration ({!Cpp_pipeline.finish}) have already run.

    @param ctx  where it is written, as the scopes entered from where the
                declaration of the tree holding it is written say
    @param env  name environment for sub-expression and sub-type printers *)
and pp_cpp_decl ctx env (settled : Cpp_erasure.settled) =
  check_position ctx;
  note_file_scope_type ctx (settled :> cpp_decl);
  match Cpp_erasure.view settled with
  | Template (temps, cstr, inner) -> pp_template_decl ctx env temps cstr inner
  | Namespace (None, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl ctx env) decls in
    (str "namespace " ++ str "{") ++ fnl () ++ ds ++ fnl () ++ str "};"
  | Namespace (Some id, members) -> pp_wrapper_nspace ctx env id members
  | Decl d -> pp_leaf_decl ctx env d

(** A template head and the declaration it introduces. *)
and pp_template_decl ctx env temps cstr (inner : Cpp_erasure.settled) =
  match (inner :> cpp_decl) with
  | Dasgn {da_ref = id; da_type = ty; da_init = e; _} when ctx.rc_in_struct ->
    let expr_pp = pp_initialiser ctx env ty e in
    template_head ctx env temps cstr ++ pp_meyers_singleton ctx env id ty expr_pp
  | _ -> template_head ctx env temps cstr ++ pp_cpp_decl ctx env inner

(** A template head with its constraint.  A default may be given once per
    parameter.  Which printing gives it is decided in the declarations: a
    definition written after its declaration has had its defaults stripped
    ({!Function_entity.definition_after_declaration}). *)
and template_head ctx env temps cstr =
  let args = pp_list (pp_template_param ctx) temps in
  let req = pp_requires_of_tparams ctx temps in
  let cstr_pp = match (req, cstr) with
    | None, None -> mt ()
    | Some r, None -> r ++ fnl ()
    | None, Some c -> pp_cpp_expr ctx env [] c ++ fnl ()
    | Some r, Some c -> r ++ str " && " ++ pp_cpp_expr ctx env [] c ++ fnl ()
  in
  (str "template <" ++ args ++ str ">") ++ cstr_pp

(** A namespace-scope wrapper struct around [members], merged with its sole
    struct child where it can be. *)
and pp_wrapper_nspace ctx env id (members : Cpp_erasure.settled list) =
  let decls = (members :> cpp_decl list) in
  let struct_name_str = nspace_wrapper_name ctx id in
  (* The same question the out-of-line definition of a member asks, asked
     through the same function so the two cannot drift apart. *)
  let merges =
    nspace_merges
      { dw_ref = id;
        dw_sole_child = (match decls with [Dstruct _] -> true | _ -> false) }
  in
  ( match (decls, merges) with
  | ( [
        Dstruct
          {
            ds_ref;
            ds_fields = fields;
            ds_tparams = [];
            ds_needs_shared_from_this = sft;
            _;
          };
      ],
      true ) ->
    (* MERGE non-template: struct Nat { ... } *)
    let struct_name = str struct_name_str in
    let f_s = entering_from ctx [In_struct; Inductive_struct ds_ref] (fun ctx -> pp_cpp_fields_with_vis ~struct_name ctx env fields) in
    let inherit_clause =
      if sft then
        str " : public " ++ str (sn ()).enable_from_this ++ str "<"
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
            ds_ref;
            ds_fields = fields;
            ds_tparams = temps;
            ds_constraint = cstr;
            ds_needs_shared_from_this = sft;
            _;
          };
      ],
      true ) ->
    (* MERGE template: template<typename A> struct List { ... } *)
    let struct_name = str struct_name_str in
    let f_s =
      entering_from ctx [In_struct; In_template; Inductive_struct ds_ref] (fun ctx -> pp_cpp_fields_with_vis ~struct_name ctx env fields)
    in
    let args = pp_list (pp_template_param ctx) temps in
    let req = pp_requires_of_tparams ctx temps in
    let cstr_pp = match (req, cstr) with
      | None, None -> mt ()
      | Some r, None -> r ++ fnl ()
      | None, Some c -> pp_cpp_expr ctx env [] c ++ fnl ()
      | Some r, Some c -> r ++ str " && " ++ pp_cpp_expr ctx env [] c ++ fnl ()
    in
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
    (str "template <" ++ args ++ str ">")
    ++ cstr_pp
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
    let ds = enter_from ctx In_struct (fun ctx -> pp_list_stmt (pp_cpp_decl ctx env) members) in
    (str "struct " ++ str struct_name_str ++ str " {")
    ++ fnl ()
    ++ ds
    ++ fnl ()
    ++ str "};" )

(** A declaration with no declaration nested inside it. *)
and pp_leaf_decl ctx env (d : cpp_decl) =
  match d with
  (* Taken apart by {!Cpp_erasure.view}, which hands out their children
     settled. *)
  | Dtemplate _ | Dnspace _ -> assert false
  | Dfun {df_path; df_ret = ret_ty; df_constexpr; df_shape = shape} ->
    let ids = dfun_path_list df_path in
    (* A definition is either out-of-line in a .cpp file or inline in a
       template struct; a declaration is always the forward declaration of an
       out-of-line definition.  That is the whole difference between the two
       shapes here: a declaration never names the enclosing struct, never
       qualifies for [constexpr] (which needs the definition in the header),
       and ends at the semicolon. *)
    let is_def = match shape with Ddef _ -> true | Ddecl _ -> false in
    (* A definition outside every struct body is a member of the struct its
       declaration's scope names, as planned; so is every name written in it
       that the struct declares. *)
    enter_from ctx (Function {owner = fst df_path.dp_outer; defines = is_def}) @@ fun ctx ->
    let scope = ctx.rc_scope in
    let pp_fun_name n =
      match n with
      | GlobRef.VarRef v when is_def -> str (Id.to_string v)
      | _ -> pp_global ctx Type n
    in
    let base_name =
      prlist_with_sep
        (fun () -> str "::")
        (fun (n, tys) ->
          match tys with
          | [] -> pp_fun_name n
          | _ -> pp_fun_name n ++ str "<" ++ pp_list (pp_type ctx) tys ++ str ">" )
        ids
    in
    let is_lifted =
      match fst df_path.dp_outer with GlobRef.VarRef _ -> true | _ -> false
    in
    let name =
      match scope with
      | Some sc when not is_lifted -> str (Scope_plan.qualifier sc) ++ str "::" ++ base_name
      | _ -> base_name
    in
    (* Anything the name says beyond a bare identifier -- a [::] qualifier or
       an explicit template argument list -- means it is being written from
       outside the struct that declares it. *)
    let is_qualified =
      df_path.dp_inner <> [] || snd df_path.dp_outer <> []
    in
    let is_struct_member = is_qualified || ctx.rc_in_struct in
    let is_out_of_struct_def = Option.has_some scope in
    let static_kw =
      if is_struct_member && ((not is_def) || not is_out_of_struct_def) then
        str "static "
      else mt ()
    in
    let params_s, qualifier, tail =
      match shape with
      | Ddef (params, body) ->
        let body_s = pp_list_stmt (pp_cpp_stmt ctx env []) body in
        let read = Minicpp.reads_as_printed body in
        let params_s =
          pp_list
            (fun (id, ty) ->
              if not (read id) then pp_type ctx ty
              else pp_type ctx ty ++ str " " ++ Id.print id)
            (List.rev params)
        in
        let qualifier =
          if may_be_constexpr df_constexpr && ctx.rc_in_struct && not is_out_of_struct_def
          then str "constexpr "
          else mt ()
        in
        (params_s, qualifier, str "{" ++ body_s ++ str "}")
      | Ddecl params ->
        let params_s =
          pp_list
            (fun (id, ty) ->
              match id with
              | Some id -> pp_type ctx ty ++ str " " ++ Id.print id
              | None -> pp_type ctx ty )
            (List.rev params)
        in
        (params_s, mt (), str ";")
    in
    h
      ( qualifier
      ++ static_kw
      ++ pp_type ctx ret_ty
      ++ str " "
      ++ name
      ++ pp_par true params_s )
    ++ tail
  | Dstruct
      {
        ds_ref = id;
        ds_fields = fields;
        ds_tparams = tparams;
        ds_constraint = cstr;
        ds_needs_shared_from_this = sft;
      } ->
    let struct_name = struct_definition_name ctx id in
    note_file_scope_name ctx struct_name;
    if ctx.rc_in_struct then printed_nested_struct (Pp.string_of_ppcmds struct_name) (NSref id);
    let f_s =
      entering_from ctx
        (Cpp_resolution.Inductive_struct id :: (if tparams = [] then [] else [In_template]))
        (fun ctx -> pp_cpp_fields_with_vis ~struct_name ctx env fields)
    in
    let tmpl = struct_template_head ~pp_param:(pp_template_param ctx) ctx env tparams cstr in
    let inherit_clause =
      if sft then
        match
          tparams
        with
        | [] ->
          str " : public " ++ str (sn ()).enable_from_this ++ str "<"
          ++ struct_name
          ++ str ">"
        | _ ->
          let type_args = pp_list (fun (_, tid) -> Id.print tid) tparams in
          str " : public " ++ str (sn ()).enable_from_this ++ str "<"
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
  | Dasgn {da_ref = id; da_type = ty; da_init = e; da_constexpr} ->
    let expr_pp = pp_initialiser ctx env ty e in
    if ctx.rc_in_template || (ctx.rc_in_struct && Common.get_force_cross_file_qualification ()) then
      (* In template context or separate-extraction struct: use Meyers
         singleton so that module-type-parameter references via L::val()
         work for both template and non-template implementing modules. *)
      pp_meyers_singleton ctx env id ty expr_pp
    else
      (* A value written as a literal of a literal type is a constant
         expression: [constexpr] says so, and lets it stand in a
         [static_assert] or a template argument. *)
      let literal = may_be_constexpr da_constexpr in
      let ty = match ty with Tconst t when literal -> t | t -> t in
      let static_kw =
        match (ctx.rc_in_struct, literal) with
        | true, true -> str "static constexpr "
        | true, false -> str "static inline "
        | false, true -> str "inline constexpr "
        | false, false -> mt ()
      in
      let needs_iife = ctx.rc_in_struct && expr_contains_capturing_lambda e in
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
        ++ pp_type ctx ty
        ++ str " "
        ++ pp_global ctx Type id
        ++ str " = "
        ++ wrapped_expr
        ++ str ";" )
  | Dconcept (id, cstr) ->
    h
      ( str "concept "
      ++ pp_concept_name_of_ref ctx id
      ++ str " = "
      ++ pp_cpp_expr ctx env [] cstr
      ++ str ";" )
  | Dusing u ->
    (* The template parameter names are also the scope the right-hand side's
       type variables are read in: a parameterised alias names them once. *)
    let vl = List.map snd u.du_tparams in
    let def =
      match u.du_rhs with
      | None -> mt ()
      | Some ty -> str " =" ++ spc () ++ pp_cpp_type ctx false vl ty
    in
    let note =
      match u.du_note with None -> mt () | Some s -> str (" /* " ^ s ^ " */")
    in
    ( pp_template_header ctx u.du_tparams
      ++ str "using "
      ++ pp_global ctx Type u.du_name
      ++ def
      ++ note
      ++ str ";" )
  | Dstruct_fwd (tparams, r) ->
    (pp_template_header ctx tparams ++ str "struct " ++ pp_global ctx Type r ++ str ";")
  | Dmember_def {dm_owner; dm_enclosing; dm_tparams; dm_field} ->
    (* The struct is behind us, so its own name is no longer in scope: the
       member is written under the qualifier that names it from outside.

       An inductive wrapped in a namespace struct is spelled [Outer::inner],
       and its own name is not capitalised -- the capitalisation below is the
       namespace struct's name, which is only the whole answer when the
       inductive was promoted into it and has no struct of its own. *)
    (* Two names, because they answer different questions: [own_name] is what
       the struct calls itself, which is what a destructor repeats, and [sname]
       is how the outside reaches it. *)
    let own_name, sname =
      match dm_enclosing with
      | Some w when not (nspace_merges w) ->
        let own = str_global ctx Type dm_owner in
        (own, nspace_wrapper_name ctx w.dw_ref ^ "::" ^ own)
      | _ ->
        let own = String.capitalize_ascii (str_global ctx Type dm_owner) in
        (own, own)
    in
    let sname = str sname in
    let qual =
      match dm_tparams with
      | [] -> sname
      | tps ->
        sname ++ str "<" ++ pp_list (fun (_, id) -> Id.print id) tps ++ str ">"
    in
    entering_from ctx
      ((if dm_tparams = [] then [] else [Cpp_resolution.In_template]) @ [Inductive_struct dm_owner])
      (fun ctx ->
        pp_cpp_field ~struct_name:(str own_name) ctx ~mode:(Mm_defined (qual, dm_tparams)) env (field_of_member dm_field) )
  | Dfields ds ->
    let struct_name =
      str (String.capitalize_ascii (str_global ctx Type ds.ds_ref))
    in
    entering_from ctx
      ((Cpp_resolution.In_struct :: (if ds.ds_tparams = [] then [] else [In_template])) @ [Inductive_struct ds.ds_ref])
      (fun ctx -> pp_cpp_fields_with_vis ~struct_name ctx env ds.ds_fields)
  | Dstatic_assert (CPPconcept_app (class_ref, _, _), None) when class_concept_held_back ctx class_ref ->
    (* The concept is declared after the struct being rendered, because its
       requirements name the struct's own types.  The assertion goes with it
       ({!held_back_assertions}). *)
    mt ()
  | Dstatic_assert (e, so) ->
    ( match so with
    | None -> (str "static_assert(" ++ pp_cpp_expr ctx env [] e ++ str ");")
    | Some s ->
      h
        ( str "static_assert("
        ++ pp_cpp_expr ctx env [] e
        ++ str ", \""
        ++ str (escape_cpp_string s)
        ++ str "\");" ) )
  | Denum {de_ref = name; de_ctors = ctors; de_ctor_rocq_names = rocq_names; _}
    ->
    let struct_name = enum_definition_name ctx name in
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
    (* An [enum class] nested in a module struct shadows a global-scope type of
       the same name exactly as a nested struct does, so it is recorded the
       same way -- the standard library's [comparison] is emitted globally and
       a user type spelled [Comparison] inside the struct would otherwise
       capture every unqualified mention of it. *)
    if ctx.rc_in_struct then printed_nested_struct (Pp.string_of_ppcmds struct_name) (NSref name);
    str "enum class "
    ++ struct_name
    ++ str " {"
    ++ fnl ()
    ++ ctors_s
    ++ fnl ()
    ++ str "};"

(** The structs the file being written has constrained forward declarations
    of, planned with its layout, each by its reference and the name its
    declaration declares. *)
let constrained_structs : GlobRef.t list ref = State.cell State.Unit []

(** [d] printed in [env] where the printer is: a declaration written
    outside every tree. *)
let read_cpp_decl env d = pp_cpp_decl !render_ctx env d

(** The wrapper structs [d] writes that hold a wrapper module's
    declarations: those [homed] names, each with the module. *)
let absorbed_by ~homed ctx (d : Cpp_erasure.settled) =
  List.filter (fun name -> List.mem_assoc name homed) (unmerged_wrappers_written ctx d)

let absorbs ~homed ctx d = absorbed_by ~homed ctx d <> []

(** [d], which {!absorbs}, as written: each wrapper struct holding a wrapper
    module's declarations a {!Cpp_ast.Wrapper_struct}, the wrapper's own
    members its fields, each printed where the tree puts it
    ({!Cpp_ast.Absorbed}). *)
let rec absorbing_decl ~homed env (d : Cpp_erasure.settled) =
  let ctx = !render_ctx in
  note_file_scope_type ctx (d :> cpp_decl);
  let written d = if absorbs ~homed ctx d then absorbing_decl ~homed env d else Cpp_ast.absorbed env d in
  match Cpp_erasure.view d with
  | Template (temps, cstr, inner) -> Cpp_ast.seq [Cpp_ast.text (template_head ctx env temps cstr); written inner]
  | Namespace (None, decls) ->
    Cpp_ast.seq
      [Cpp_ast.text (str "namespace {" ++ fnl ()); Cpp_ast.concat fnl (List.map written decls); Cpp_ast.text (fnl () ++ str "};")]
  | Namespace (Some id, members) -> (
    let name = nspace_wrapper_name ctx id in
    let ds = enter In_struct (fun () -> Cpp_ast.concat fnl (List.map written members)) in
    match List.assoc_opt name homed with
    | Some module_ -> Cpp_ast.wrapper_struct ~name ~module_ ~fields:Cpp_ast.(seq [ds; text (fnl ())])
    | None -> Cpp_ast.(seq [text (str "struct " ++ str name ++ str " {" ++ fnl ()); ds; text (fnl () ++ str "};")]) )
  | Decl _ -> Cpp_ast.text (read_cpp_decl env d)

(** Whether [d] is an assertion the struct being written holds back
    ({!held_back_assertions}), which it writes nothing for. *)
let is_held_back_assertion ctx (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Decl (Dstatic_assert (CPPconcept_app (class_ref, _, _), None)) -> class_concept_held_back ctx class_ref
  | _ -> false

(* Of the structs the file has constrained forward declarations of
   ({!constrained_structs}), those named by [names ()] or [defined ()], and
   those defined. *)
let constrained_named ~names ~defined =
  match !constrained_structs with
  | [] -> ([], [])
  | constrained ->
    let of_refs refs = List.filter (fun r -> List.exists (GlobRef.UserOrd.equal r) refs) constrained in
    let defined = defined () in
    (of_refs (defined @ names ()), of_refs defined)

(** What placing the declarations a written declaration needs reads: the
    synthesised templates it writes, [templates], as planned
    ({!planned_ctor_aliases}); and, of the structs the file has constrained
    forward declarations of, those it names or defines, and those it
    defines.  The declarations of a wrapper module it writes into a struct
    of its own ({!Cpp_ast.Wrapper_struct}) are members of that struct, and
    need what they need themselves. *)
let needs_of ~templates (settled : Cpp_erasure.settled) =
  let names, defines =
    constrained_named
      ~names:(fun () -> Cpp_demands.globals_of_decl (settled :> cpp_decl))
      ~defined:(fun () -> List.map defined_ref (structs_defined settled))
  in
  {Cpp_ast.Needs.templates; names; defines}

let fields_needs ~module_ ~vl r types =
  let aliases = planned_aliases ~module_ (Written_fields r) in
  let file = (!render_ctx).rc_file in
  if Probe.checking () && Option.has_some !ctor_alias_plan && (ctor_aliases_of_fields ~file ~vl r types).read_aliases <> aliases
  then
    Probe.violation "constructor aliases"
      Pp.(str "the fields of a record in the " ++ str (Common.file_name file)
          ++ str " write other templates than were planned for them");
  let names, _ =
    constrained_named ~names:(fun () -> List.concat_map Cpp_demands.globals_of_type types) ~defined:(fun () -> [])
  in
  {Cpp_ast.Needs.templates = List.map ctor_alias_name aliases; names; defines = []}

let printed_needs settled = needs_of ~templates:(List.map ctor_alias_name (ctor_aliases_planned settled)) settled

(* The frames printing [d] enters names at: {!pp_cpp_decl}'s scopes, read
   without printing. *)
let declaration_frames (d : Cpp_erasure.settled) =
  let entered frame l = List.rev_append l frame in
  let template_body tps = if tps = [] then [] else [Cpp_resolution.In_template] in
  let rec decl frame (d : Cpp_erasure.settled) =
    match Cpp_erasure.view d with
    | Template (_, _, inner) -> frame :: decl frame inner
    | Namespace (None, decls) -> List.concat_map (decl frame) decls
    | Namespace (Some id, members) -> (
      match (members :> cpp_decl list) with
      | [Dstruct {ds_ref; ds_tparams; _}] when nspace_merges {dw_ref = id; dw_sole_child = true} ->
        [frame; entered frame ((Cpp_resolution.In_struct :: template_body ds_tparams) @ [Inductive_struct ds_ref])]
      | _ -> frame :: List.concat_map (decl (Cpp_resolution.In_struct :: frame)) members )
    | Decl (Dfun {df_path; df_shape; _}) ->
      let defines = match df_shape with Ddef _ -> true | Ddecl _ -> false in
      [Cpp_resolution.Function {owner = fst df_path.dp_outer; defines} :: frame]
    | Decl (Dstruct {ds_ref; ds_tparams; _}) ->
      [frame; entered frame (Cpp_resolution.Inductive_struct ds_ref :: template_body ds_tparams)]
    | Decl (Dmember_def {dm_owner; dm_tparams; _}) ->
      [frame; entered frame (template_body dm_tparams @ [Cpp_resolution.Inductive_struct dm_owner])]
    | Decl (Dfields {ds_ref; ds_tparams; _}) ->
      [frame; entered frame ((Cpp_resolution.In_struct :: template_body ds_tparams) @ [Inductive_struct ds_ref])]
    | Decl _ -> [frame]
  in
  decl [] d

(* The globals [d] declares, which it names where it declares them, and the
   classes its template parameters are constrained by: no expression or type
   of it names them. *)
let rec declared_globals (d : cpp_decl) =
  let concepts tps = List.filter_map (function TTconcept (r, _), _ -> Some r | _ -> None) tps in
  let rec field (f, _, _) =
    match f with
    | Fmethod {mf_tparams = tps; _} | Fconstructor {fc_tparams = tps; _} | Fnested_using (tps, _, _) -> concepts tps
    | Fnested_struct (_, fs) -> List.concat_map field fs
    | Fmember_decl m -> field (field_of_member m, VPublic, SNoTag)
    | _ -> []
  in
  match d with
  | Dtemplate (tps, _, inner) -> concepts tps @ declared_globals inner
  | Dnspace (id, ds) -> (match id with Some r -> [r] | None -> []) @ List.concat_map declared_globals ds
  | Dfun {df_path; _} -> List.map fst (dfun_path_list df_path)
  | Dstruct {ds_ref; ds_tparams; ds_fields; _} | Dfields {ds_ref; ds_tparams; ds_fields; _} ->
    (ds_ref :: concepts ds_tparams) @ List.concat_map field ds_fields
  | Dasgn {da_ref; _} -> [da_ref]
  | Dusing {du_name; du_tparams; _} -> du_name :: concepts du_tparams
  | Dstruct_fwd (tps, r) -> r :: concepts tps
  | Dmember_def {dm_owner; dm_enclosing; dm_tparams; dm_field} ->
    (dm_owner :: Option.cata (fun w -> [w.dw_ref]) [] dm_enclosing)
    @ concepts dm_tparams
    @ field (field_of_member dm_field, VPublic, SNoTag)
  | Denum {de_ref; _} -> [de_ref]
  | Dconcept (id, _) -> [id]
  | Dstatic_assert _ -> []

(* Of [globals], those whose name is decided -- printing decides none --
   asked for at each of [frames], each as the type and the expression
   printers may name it. *)
let global_names frames globals =
  let decided r = Option.has_some (Common.decided_global_name r) in
  let globals =
    List.sort_uniq GlobRef.UserOrd.compare
      (List.filter decided
         (List.concat_map (function GlobRef.ConstructRef (ind, _) as r -> [r; GlobRef.IndRef ind] | r -> [r]) globals) )
  in
  let keys =
    List.concat_map
      (fun r ->
        Cpp_resolution.[Unmapped (Type, r); Unmapped (Term, r); Class_concept r]
        @ match r with GlobRef.IndRef _ -> [Cpp_resolution.Inductive_value r] | _ -> [] )
      globals
  in
  List.concat_map (fun frame -> List.map (fun key -> (frame, key)) keys) frames

let template_param_globals tps =
  let types = ref [] in
  ignore (map_tparams (fun t -> types := t :: !types; t) tps);
  List.filter_map (function TTconcept (r, _), _ -> Some r | _ -> None) tps
  @ List.concat_map Cpp_demands.globals_of_type !types

let declaration_names (d : Cpp_erasure.settled) =
  let globals = ref [] in
  Minicpp.iter_globrefs (fun r -> globals := r :: !globals) (d :> cpp_decl);
  global_names (declaration_frames d) (!globals @ declared_globals (d :> cpp_decl))

let unprinted_names : Cpp_ast.declaration -> _ = function
  | Declaration {settled; _} | Absorbed {settled; _} -> declaration_names settled
  | Fields {fields; _} -> global_names [[]] (List.concat_map (fun (_, ty) -> Cpp_demands.globals_of_type ty) fields)
  | Assertion {subject = Instance {args; _}; _} -> global_names [[]] (List.concat_map Cpp_demands.globals_of_type args)
  | Global_alias (Alias_of_type {tparams; _}) -> global_names [[]] (template_param_globals tparams)
  | Forward_declaration {defined = Defined_struct {struct_; tparams; constraint_; _}; _} ->
    let constraint_globals c =
      let found = ref [] in
      Minicpp.iter_globrefs (fun r -> found := r :: !found) (Dstatic_assert (c, None));
      !found
    in
    global_names [[]] ((struct_ :: template_param_globals tparams) @ Option.cata constraint_globals [] constraint_)
  | Forward_declaration {defined = Defined_enum r; _} -> global_names [[]] [r]
  | Assertion {subject = Module _; _} | Global_alias (Alias_of_module _) | Modtype_concept _ | Module_alias _
  | Functor_alias _ | Derived_functor _ ->
    []

let naming names k = with_render_ctx (fun c -> {c with rc_names = Some names}) k

let printed_decl ctx env settled =
  let text = pp_cpp_decl ctx env settled in
  (text, printed_needs settled)

(** [settled], printed where it is made, with what placing the declarations
    it needs reads ({!needs_of}). *)
let write_decl env settled =
  let text, needs = printed_decl !render_ctx env settled in
  Cpp_ast.decl ~needs text

(** [settled], which {!absorbs}, written where it is made ({!absorbing_decl}),
    behind what placing the declarations it needs reads. *)
let write_absorbing ~homed env settled =
  let tree = absorbing_decl ~homed env settled in
  let needs = printed_needs settled in
  ( if Probe.checking () then
      let written = Cpp_ast.wrapper_structs tree and absorbing = absorbed_by ~homed !render_ctx settled in
      if List.sort String.compare written <> List.sort String.compare absorbing then
        Probe.violation "wrapper homes"
          Pp.(
            str "a declaration wrote the declarations of the wrappers "
            ++ prlist_with_sep pr_comma str written
            ++ str " into its structs, and needs what those of "
            ++ prlist_with_sep pr_comma str absorbing
            ++ str " need" ) );
  Cpp_ast.seq [Cpp_ast.decl ~needs (Pp.mt ()); tree]

let planned_needs ~module_ settled =
  needs_of ~templates:(List.map ctor_alias_name (planned_ctor_aliases ~module_ settled)) settled

let unprinted ~module_ env settled = Cpp_ast.unprinted ~needs:(planned_needs ~module_ settled) env settled

let unprinted_fields ~module_ ~vl r fields =
  Cpp_ast.fields ~needs:(fields_needs ~module_ ~vl r (List.map snd fields)) ~record:r ~vars:vl fields

let resolved key (resolution : Cpp_ast.resolution) =
  match resolution with Resolved n -> checked key ~live:(fun () -> live_name key) n | Unresolved -> unresolved key

let resolved_module (m : Cpp_ast.module_ref) = resolved (Module m.path) m.name
let resolved_class_concept (c : Cpp_ast.global_ref) = resolved (Class_concept c.global) c.name
let resolved_type_name (g : Cpp_ast.global_ref) = resolved (Global (Type, g.global)) g.name
let resolved_concept (c : Cpp_ast.concept_ref) = resolved (Modtype_concept c.module_type) c.name
let pp_declared_module (m : Cpp_ast.declared_module) = Cpp_name.pp (resolved (Module_declared m.declares) m.name)

let name_in names frame key = name_from names frame key ~live:(fun () -> live_name key)

(* A module named in a module expression, and its resolution. *)
let pp_module_name (m : Cpp_ast.module_ref) =
  let r = resolved_module m in
  (str (wrapper_qualify_modname m.path (resolved_string r)), r)

(* Inside a class template a qualified module is a dependent name: an
   argument is preceded by [typename], and a functor applied is named
   [A::template F]. *)
let pp_application ctx {Cpp_ast.functor_; args} =
  let in_template = ctx.rc_in_template in
  let head =
    match pp_module_name functor_ with
    | _, r when in_template && resolved_is_qualified r -> Cpp_name.pp ~template_keyword:true r
    | head, _ -> head
  in
  let arg m =
    match pp_module_name m with
    | a, r when in_template && resolved_is_qualified r -> str "typename " ++ a
    | a, _ -> a
  in
  head ++ str "<" ++ prlist_with_sep (fun () -> str ", ") arg args ++ str ">"

let pp_module_alias ctx name (target : Cpp_ast.module_expr) =
  let target =
    match target with
    | Module_named m ->
      let r = resolved_module m in
      let named = str (resolved_string r) in
      if ctx.rc_in_template && resolved_is_qualified r then str "typename " ++ named else named
    | Applied a -> pp_application ctx a
  in
  str "using " ++ pp_declared_module name ++ str " = " ++ target ++ str ";"

let pp_functor_alias name functor_ params =
  Cpp_ast.pp_template_head (List.map fst params)
  ++ str "using " ++ pp_declared_module name ++ str " = "
  ++ str (resolved_string (resolved_module functor_))
  ++ str "<" ++ prlist_with_sep (fun () -> str ", ") (fun (_, m) -> Cpp_name.pp (resolved_module m)) params ++ str ">;"

(* The base is written inside the functor's template; a base specifier
   names a type, so a dependent one takes no [typename]. *)
let pp_derived_functor ctx template name (base : Cpp_ast.module_expr) =
  let inside = {ctx with rc_in_struct = true; rc_in_template = true} in
  let base =
    with_render_ctx
      (fun _ -> inside)
      (fun () -> match base with Module_named m -> fst (pp_module_name m) | Applied a -> pp_application inside a)
  in
  Cpp_ast.pp_template_head template ++ str "struct " ++ pp_declared_module name ++ str " : " ++ base ++ str " {};"

let print_unprinted ~modtype_concept ~assertion (u : Cpp_ast.unprinted) =
  naming u.names @@ fun () ->
  (* Where the declaration is written, which is where the printer is. *)
  let ctx = !render_ctx in
  let text, needs =
    match u.declaration with
    | Modtype_concept {path; params; concept} -> (modtype_concept ~names:u.names ~params path concept, u.needs)
    | Assertion a -> (assertion a, u.needs)
    | Module_alias {name; target} -> (pp_module_alias ctx name target, u.needs)
    | Functor_alias {name; functor_; params} -> (pp_functor_alias name functor_ params, u.needs)
    | Derived_functor {template; name; base} -> (pp_derived_functor ctx template name base, u.needs)
    | Forward_declaration {env; defined} -> (pp_forward_declaration ctx env defined, u.needs)
    | Declaration {env; settled} -> printed_decl ctx env settled
    | Absorbed {env; settled} -> (pp_cpp_decl ctx env settled, u.needs)
    | Fields {record; vars; fields} ->
      ( prlist_with_sep fnl (fun (name, ty) -> pp_cpp_type ctx false vars ty ++ spc () ++ str name ++ str ";") fields
        ++ fnl (),
        if Probe.checking () then fields_needs ~module_:(module_written ctx) ~vl:vars record (List.map snd fields)
        else u.needs )
    | Global_alias a ->
      let tparams, name =
        match a with
        | Alias_of_type {target; definition; tparams} ->
          (tparams, Cpp_name.pp (resolved (Definition (definition, target.global)) target.name))
        | Alias_of_module m -> ([], Cpp_names.module_struct_name_of (resolved_module m))
      in
      let args =
        if tparams = [] then mt () else str "<" ++ prlist_with_sep (fun () -> str ", ") (fun (_, v) -> Id.print v) tparams ++ str ">"
      in
      (pp_template_header ctx tparams ++ str "using " ++ name ++ str " = ::" ++ name ++ args ++ str ";", u.needs)
  in
  if Probe.checking () && needs <> u.needs then
    Probe.violation "unprinted declarations"
      (Pp.str "a declaration printed where the tree puts it needs other declarations than planned where it was made");
  text

let cut2 = Cpp_ast.cut2

(* The type printer's entry for a type written outside every declaration of
   the tree: where the printer is. *)
let pp_cpp_type ?lead par vl t = pp_cpp_type ?lead !render_ctx par vl t
