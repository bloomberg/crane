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

(** Functions whose return type involves an axiom type must not be marked
    [__attribute__((pure))]: they may transitively call an axiom stub that
    throws [std::logic_error]. *)
let is_axiom_type_ref = Cpp_erasure.is_axiom_type_ref

(** [output_mentions body_s] is the test "does the printed body [body_s]
    contain this identifier, as a whole word".

    Whether a parameter may keep its name is a question about the {e output}:
    a name the body never mentions is a [-Wunused-parameter] error, and the
    AST is no proxy for what gets printed -- a custom-extraction template
    drops arguments when it prints a call, so a [CPPvar] node can stand for a
    name that never reaches the file.  The printer therefore asks the question
    of the text it has just produced, which is the text the C++ compiler will
    read.  Render the body first; the answer is only as good as the string it
    is given. *)
let output_mentions body_s =
  let s = Pp.string_of_ppcmds body_s in
  let len = String.length s in
  let is_word_char c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    || (c >= '0' && c <= '9') || c = '_'
  in
  fun id ->
    let name = Id.to_string id in
    let n = String.length name in
    let rec scan i =
      if i + n > len then false
      else if
        String.sub s i n = name
        && (i = 0 || not (is_word_char s.[i - 1]))
        && (i + n >= len || not (is_word_char s.[i + n]))
      then true
      else scan (i + 1)
    in
    n > 0 && scan 0

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
    | CPPraw s
      when String.length s > 3
           && String.sub s 0 2 = "(*"
           && s.[String.length s - 1] = ')' ->
      let name = String.sub s 2 (String.length s - 3) in
      (try (IdSet.add (Id.of_string name) refs, decls) with _ -> (refs, decls))
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
    | Sdecl (id, _) -> (refs, IdSet.add id decls)
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
            List.fold_left (fun acc (id, _) -> IdSet.add id acc) d branch_vars
          in
          List.fold_left collect_from_stmt (r, branch_decls) stmts)
        (collect_from_expr (refs, decls) scrut)
        branches
    | Sblock_custom (_, _, id, _, args, _) ->
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
                  (fun d (bname, _, _) -> IdSet.add bname d)
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


(** Whether a type is spelled [std::any] -- owned by {!Cpp_erasure}, which
    also records the aliases to it, so that the pass that decides how to cross
    an erasure boundary and the printer cannot disagree. *)
let is_any_type = Cpp_erasure.is_any_shaped

(** Type names introduced at file scope, recorded as they are emitted.

    A definition written outside its struct ([Owner::f]) qualifies the plain
    names in its signature with [Owner::], which is right for a member and
    wrong for anything else.  An erased type-class field is a case of
    "anything else": the class is at file scope, so its erased face is a
    file-scope [using iptr = std::any;], and some unrelated struct's hoisted
    body must resolve [iptr] to that alias rather than claim it as a member it
    never declared.

    The set is only consulted to {i withhold} the qualifier, so a name not yet
    seen keeps the old behaviour; and a file-scope name that a struct also
    declares as a member still resolves to the member, because the body of an
    out-of-line definition is inside its class's scope. *)
let file_scope_type_names : CString.Set.t ref = State.cell State.Unit CString.Set.empty

let is_file_scope_type id =
  CString.Set.mem (Id.to_string id) !file_scope_type_names

(** Record [name] as declared at file scope, if that is where we are.  Called
    with the name the printer is about to write, not one recomputed from the
    reference: a struct's spelling goes through several cases and a recomputed
    name would silently fail to match the one a use site writes. *)
let record_file_scope_name name =
  if not (!render_ctx).rc_in_struct then
    file_scope_type_names :=
      CString.Set.add (Pp.string_of_ppcmds name) !file_scope_type_names

(** The type name a declaration introduces, for the shapes whose spelling is
    settled here.  A struct records itself where it is printed. *)
let rec decl_type_name = function
  | Dtemplate (_, _, inner) -> decl_type_name inner
  | Dusing u -> Some (pp_global Type u.du_name)
  | Dnspace (Some r, _) ->
    Some (str (String.capitalize_ascii (str_global Type r)))
  | _ -> None

let record_file_scope_type d = Option.iter record_file_scope_name (decl_type_name d)

(** The using-declaration a unit needs for the promoted type variable [id]
    when its file-scope alias is another file's: under separate extraction
    that alias sits in its class's namespace, which a bare name in this one
    does not reach; the [using] gives the name the lookup it has in a
    single-file extraction, a struct's own member still first. *)
let promoted_alias_import id =
  if Common.get_force_cross_file_qualification () then
    match Table.promoted_type_var_field id with
    | Some g when Option.has_some (Common.file_qualifier Type g) -> Some ("using " ^ Common.pp_global Type g ^ ";")
    | _ -> None
  else None

(** The C++ token an {!Minicpp.obj_access} prints as. *)
let pp_obj_access = function Adot -> "." | Aarrow -> "->"

let ref_has_no_cpp_name = Ml_type_util.ref_has_no_cpp_name
let has_no_cpp_spelling = Ml_type_util.has_no_cpp_spelling

(** Report what {!has_no_cpp_spelling} saw.

    Two audiences.  A [Crane Extract Skip] on a constant that a custom
    template later needs {e by name} degrades silently: the binder becomes
    [std::any] and the only symptom is a type error a long way downstream, so
    that one is always warned about, naming the directive to remove.  A module
    left out by [Crane Extract Skip Module] was left out wholesale and on
    purpose, so it is not worth a word unless asked.

    [CRANE_DBG_UNSPELLABLE] adds the full shape.  The ordinal is the
    discriminator: firings are reported in emission order, which is the only
    handle on {e which} site fired when several share a custom template, and
    the alternative -- a printer-filled table of the declaration being emitted
    -- is the thing that must not be built. *)
let unspellable_firings = ref 0

let unspellable_warned : (string, unit) Hashtbl.t = Hashtbl.create 7

let report_unspellable where ty =
  let empty_custom = ref [] and skipped_mod = ref [] in
  ignore
    (Minicpp.exists_cpp_type
       (function
         | Tglob (r, _, _) when ref_has_no_cpp_name r ->
           let n = Pp.string_of_ppcmds (GlobRef.print r) in
           if Ml_type_util.ref_has_no_spelling r then
             empty_custom := n :: !empty_custom
           else skipped_mod := n :: !skipped_mod;
           false
         | _ -> false )
       ty );
  incr unspellable_firings;
  List.iter
    (fun n ->
      if not (Hashtbl.mem unspellable_warned n) then begin
        Hashtbl.add unspellable_warned n ();
        Feedback.msg_warning
          (Pp.str
             (Printf.sprintf
                "crane: a custom template needs %s by name, but [Crane \
                 Extract Skip] removed it, so the binder is typed std::any \
                 and the type is lost here.  If %s is still reachable, drop \
                 the directive that skips it."
                n n ) )
      end )
    (List.rev !empty_custom);
  if Sys.getenv_opt "CRANE_DBG_UNSPELLABLE" <> None then begin
    let shape = function
      | Tglob _ -> "Tglob"
      | Tapply _ -> "Tapply"
      | Tqualified _ -> "Tqualified"
      | Tvar _ -> "Tvar"
      | Tinstance _ -> "Tinstance"
      | Tpromoted _ -> "Tpromoted"
      | Tid _ -> "Tid"
      | Tid_external _ -> "Tid_external"
      | Tnondeduced _ -> "Tnondeduced"
      | Trebind _ -> "Trebind"
      | Thole -> "Thole"
      | Tref (Forwarding, _) -> "Tfwd_ref"
      | Texpr_type _ -> "Texpr_type"
      | Tdecltype_auto -> "Tdecltype_auto"
      | Ttyctor _ -> "Ttyctor"
      | Tany -> "Tany"
      | _ -> "other"
    in
    let tagged tag l = List.map (fun n -> n ^ " [" ^ tag ^ "]") l in
    Feedback.msg_warning
      (Pp.str
         (Printf.sprintf
            "crane: firing %d: %s yields std::any; outermost %s; nameless \
             globs: %s"
            !unspellable_firings where (shape ty)
            (String.concat ", "
               ( tagged "empty custom" (List.rev !empty_custom)
               @ tagged "skipped module" (List.rev !skipped_mod) ) ) ) )
  end

(** Alias templates standing in for custom-mapped type constructors that
    cannot be named by cutting their application back to a head.

    A custom mapping is a {e spelling}, not a template name: [itree] maps to
    [std::shared_ptr<ITree<%t1>>], whose head is [std::shared_ptr] -- a
    template that, applied to the element, gives something else entirely.  A
    template template argument position needs a name that applies correctly,
    so one is introduced: [template <typename _A> using ITree_tc =
    std::shared_ptr<ITree<_A>>;], declared in front of the first text that
    spells it ({!take_ctor_alias_decls}).  Keyed by the alias body, so a constructor
    reached twice is declared once. *)
let ctor_alias_decls : (string * string) list ref = ref []

(** Alias templates whose body mentions template parameters of the declaration
    that needs them.

    A namespace-scope alias cannot name a function template's own parameter, so
    the carrier of [`{TFunctor (fun T => two T (FnBody T))}] -- whose body is
    [two<_CraneTcArg, T1<_CraneTcArg>>] -- has nowhere to be declared as a
    plain alias.  What can be declared there is a holder parameterised over
    exactly those names, with the alias as a member:

      template <template <typename> class _F0> struct C_h {
        template <typename _CraneTcArg> using c = two<_CraneTcArg, _F0<_CraneTcArg>>;
      };

    and the use site writes [C_h<T1>::template c], which is the dependent alias
    the [Tqualified] branch below already knows how to spell.  Keyed by the
    body with the captured names replaced, so two declarations that differ only
    in what they call their parameters share one holder. *)
let ctor_holder_decls : (string * string) list ref = ref []

(** The alias and holder names already declared in the file being written.

    {!take_ctor_alias_decls} is called once per top-level element rather than
    once per file, so that an alias lands after the definitions its body names
    ({!Cpp.do_struct_with_decl_tracking}).  Draining empties the registry, and
    a later element reaching the same constructor mints the same name again --
    the same name, because it is a digest of the body.  Repeating the
    declaration would be legal and is what this avoids: the earlier one is
    still in scope, so the repeat says nothing.

    Per file, because the two files declare independently: a use in the
    implementation file is reached after the header has been handed over. *)
let ctor_alias_emitted : (string, unit) Hashtbl.t = Hashtbl.create 16

let reset_ctor_alias_emitted () = Hashtbl.reset ctor_alias_emitted

(** Whether [text] spells [name] as a whole identifier.  An alias's name ends
    in a digest of its body, but a holder's is numbered ([crane_carrier_tch],
    [crane_carrier_tch1]), so one can be a prefix of another. *)
let mentions_name text name =
  let n = String.length name and m = String.length text in
  let is_id c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
    || c = '_'
  in
  let at i =
    String.sub text i n = name
    && (i = 0 || not (is_id text.[i - 1]))
    && (i + n = m || not (is_id text.[i + n]))
  in
  let rec go i = i + n <= m && (at i || go (i + 1)) in
  n > 0 && go 0

(** The synthesised names minted but not yet declared. *)
let pending_ctor_alias_names () =
  List.map snd !ctor_alias_decls @ List.map snd !ctor_holder_decls

(** The module struct a synthesised name has to be declared inside
    ({!ctor_alias_home}). *)
let ctor_alias_homes : (string, Names.ModPath.t) Hashtbl.t = Hashtbl.create 17

(** A template synthesised to stand where a type constructor is written as a
    template template argument but has no template name of its own: an alias
    template, or a holder -- a struct parameterised over the enclosing
    declaration's parameters the body names, with the alias as its member
    [c]. *)
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

(** The module struct the template abbreviating [body] has to be declared
    inside, if any: the one being written, where [body] names a global of
    it.  Such a global is written bare only because that struct is the
    innermost visible scope, and so means nothing at namespace scope. *)
let ctor_alias_home body =
  let cur = Common.top_visible_mp () in
  let modpath_of = function
    | GlobRef.ConstRef c -> Some (Names.Constant.modpath c)
    | GlobRef.IndRef (kn, _) | GlobRef.ConstructRef ((kn, _), _) ->
      Some (Names.MutInd.modpath kn)
    | GlobRef.VarRef _ -> None
  in
  let in_cur =
    exists_cpp_type
      (function
        | Tglob (r, _, _) -> (
          match modpath_of r with
          | Some mp -> Names.ModPath.equal mp cur
          | None -> false )
        | _ -> false )
      body
  in
  if in_cur && not (Table.is_modfile cur) then Some cur else None

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

(** The pending synthesised names whose home is [mp]. *)
let pending_ctor_aliases_homed_in mp =
  List.filter
    (fun name ->
      match Hashtbl.find_opt ctor_alias_homes name with
      | Some home -> Names.ModPath.equal home mp
      | None -> false )
    (pending_ctor_alias_names ())

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

let ctor_holder_name_for ~base body =
  match List.assoc_opt body !ctor_holder_decls with
  | Some name -> name
  | None ->
    let taken name =
      List.exists (fun (_, n) -> String.equal n name) !ctor_holder_decls
    in
    let rec fresh i =
      let name = base ^ "_tch" ^ (if i = 0 then "" else string_of_int i) in
      if taken name then fresh (i + 1) else name
    in
    let name = fresh 0 in
    ctor_holder_decls := (body, name) :: !ctor_holder_decls;
    name

(** The type variable an alias template abstracts over, and the sentinel used
    to find out whether one is needed at all: rendering the constructor
    applied to it says whether the application is just a head plus this
    argument. *)
let ctor_alias_tvar = Minicpp.ctor_alias_tvar

(** The name of the alias template for [body], as a function of [body] alone.

    Not a counter.  {!ctor_alias_decls} is drained once per file, so a counter
    allocated against it restarts in the implementation file and binds the
    names the header already bound to different bodies -- and the use sites,
    written from whichever file reached them, then name entries their own
    table never declared.  Repeating a [using] with the same definition is
    legal, which is what makes the per-file draining sound; repeating the
    {e name} with a different definition is the error it was read as being.

    A digest is what makes the two agree without either file knowing what the
    other minted: the same body is the same name in both, so both may declare
    it and every use site names what it meant.  The body is a rendered C++
    type, so the digest is over text that is already canonical. *)
let ctor_alias_name_for ~base body =
  match List.assoc_opt body !ctor_alias_decls with
  | Some name -> name
  | None ->
    let name =
      base ^ "_tc_" ^ String.sub (Digest.to_hex (Digest.string body)) 0 16
    in
    ctor_alias_decls := (body, name) :: !ctor_alias_decls;
    name

(** The name of [alias], declared in the registries. *)
let register_ctor_alias alias =
  let name =
    if alias.ca_holder then ctor_holder_name_for ~base:alias.ca_base alias.ca_body
    else ctor_alias_name_for ~base:alias.ca_base alias.ca_body
  in
  Option.iter (Hashtbl.replace ctor_alias_homes name) alias.ca_home;
  name

(** [str_of] up to its first template argument list. *)
let cut_at_argument_list str_of =
  match String.index_opt str_of '<' with
  | Some i -> String.sub str_of 0 i
  | None -> str_of

(** The C++ name of the field a projection reads.

    It is the projection's own label, escaped the same way the field was when
    the record's struct was written -- a record with a field named [this] has
    one named [this_], and a projection of it has to say so too. *)
let projection_field_name (r : GlobRef.t) : string =
  Common.modular_rename Term (Label.to_id (label_of_r r))


(** Check if a C++ expression tree contains a string literal ([CPPstring]).
    Used to guard ternary simplification: ternary with string-literal branches
    loses the implicit [const char* → std::string] conversion that an IIFE
    with explicit return type provides. *)
let rec expr_contains_string e =
  match e with
  | CPPstring _ -> true
  | _ ->
    let found = ref false in
    iter_expr_children
      ~on_expr:(fun e -> if expr_contains_string e then found := true)
      ~on_stmts:(fun _ -> ())
      e;
    !found

(** Check if a C++ type is a literal type eligible for [constexpr] context.

    Excludes allocation ([shared_ptr]), side effects ([void]), types unknown
    at definition time, axiom types (whose stubs throw), and also:
    - [Tfun]: [std::function] uses type-erased internal storage
    - [decltype]: the expression may reference non-constexpr entities
    - Composite types where any component is non-literal

    The check is recursive for container types ([Tvariant], [Tglob], [Tid],
    [Tnamespace], [Tqualified]) — a [std::variant<A, B>] is constexpr only
    if both [A] and [B] are. *)
let rec is_constexpr_type ty =
  if is_any_type ty then false else
  match ty with
  | Tshared_ptr _ -> false
  | Tvoid | Tvar _ | Tinstance _ | Tpromoted _ | Tany | Topaque | Tauto
  | Tunresolved -> false
  | Tfun _ -> false  (* std::function uses type erasure *)
  | Tdecay _ -> false
  | Tglob (r, _, _) when is_axiom_type_ref r -> false
  (* A type mapped to a C++ scalar is that scalar. *)
  | Tglob (r, [], _) when Table.is_custom_scalar_ref r -> true
  | Tglob (GlobRef.IndRef _ as r, tys, _) ->
    (* Crane-generated non-enum inductives have user-provided constructors
       (T() {}, explicit T(Ctor _v) : d_v_(_v) {}) that are not constexpr,
       so the types are not literal.  Only enum inductives (generated as
       [enum class]) are literal types. *)
    Table.is_enum_inductive r && List.for_all is_constexpr_type tys
  | Tconst t | Tref (Lvalue, t) | Tptr t -> is_constexpr_type t
  | Tvariant (_, tys) -> List.for_all is_constexpr_type tys
  | Tglob (GlobRef.ConstRef _, [], _) -> false  (* defined constant with no type args — opaque alias *)
  | Tglob (_, tys, _) -> List.for_all is_constexpr_type tys
  | Tid (_, []) -> false  (* unresolved type alias — conservatively non-literal *)
  | Tid (_, tys) | Tid_external (_, tys) -> List.for_all is_constexpr_type tys
  | Tnondeduced t -> is_constexpr_type t
  | Trebind (h, x) -> is_constexpr_type h && is_constexpr_type x
  | Thole | Terased _ -> true
  | Tref (Forwarding, t) -> is_constexpr_type t
  | Texpr_type _ | Tdecltype_auto -> false
  | Tnamespace (_, t) -> is_constexpr_type t
  | Tqualified (t, _) -> is_constexpr_type t
  (* An applied associated type is whatever the instance makes it; nothing
     here can establish it is a literal type. *)
  | Ttyctor _ | Tapply _ -> false

(** Check if a function is constexpr-eligible: all param types AND return
    type must be constexpr-eligible literal types.

    @param ret_ty  the C++ return type to test
    @param params  list of [(name, type)] pairs for all formal parameters *)
let is_constexpr_eligible ret_ty params =
  is_constexpr_type ret_ty
  && List.for_all (fun (_, ty) -> is_constexpr_type ty) params

(** Check if a function body consists solely of throwing an abort/axiom error.
    Such functions must not be marked [pure] or [constexpr] because the compiler
    may optimise away the throw. *)
let body_is_throw = function
  | [Sreturn (Some (CPPabort _))] -> true
  | _ -> false

(** Compute the C++ function qualifier prefix as a three-way decision:
    - [constexpr] when the function is constexpr-eligible and [can_constexpr]
      is [true] (i.e. the definition is visible in the header);
    - nothing otherwise.

    @param can_constexpr  whether this call site may use [constexpr]
    @param throws         whether the body unconditionally throws
    @param no_pure        when [true], suppress [constexpr] even if the
                          function would otherwise qualify (used for functions
                          that operate on [std::any] or axiom types)
    @param ret_ty         the C++ return type
    @param params         [(name, type)] pairs for all formal parameters *)
let fun_qualifier ~can_constexpr ~throws ~no_pure ret_ty params =
  if can_constexpr && not throws && not no_pure && is_constexpr_eligible ret_ty params then
    str "constexpr "
  else
    mt ()

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
let member_scopes id =
  match (!render_ctx).rc_scope with
  | Some sc when (not (!render_ctx).rc_in_struct) && not (is_file_scope_type id) ->
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

let needs_typename n = (!render_ctx).rc_in_template && Cpp_name.is_qualified n

(** The head of the type [Tglob (r, tys, _)] that no custom mapping inlines,
    [applied] when [tys] is not empty. *)
let glob_head r ~applied =
  let bare = inductive_type_name r in
  let enclosing = struct_scopes_for r bare @ global_scopes_for r bare in
  (* The wrapper qualifier is the last resort: the two qualifiers above say
     where the name lives whenever they say anything, and stacking this one
     on top of them spells the same struct twice. *)
  let name = if enclosing = [] then wrapper_qualified_type_name r bare else bare in
  {outer = enclosing; head = name; typename = needs_typename name; template_keyword = applied}

(** The head of the inductive type [Tnamespace (r, Tglob (r, args, _))],
    [applied] when [args] is not empty.

    DESIGN: Namespace-qualified types for inductive types. Rocq's
    inductives live in wrapper structs (e.g., type 'list' in struct 'List').
    Local inductives don't need namespace wrapping; non-local ones get the
    prefix. EXCEPTION: Eponymous records are merged into the module struct,
    so we use just the capitalized name without namespace qualification
    (CHT, not CHT::cHT). *)
let inductive_head r ~applied =
  let name, needs_ns = inductive_name r in
  let class_ s = Cpp_name.Class s in
  let type_name = global_name Type r in
  (* Check eponymous record FIRST because they can also be local *)
  if is_eponymous_record_cached r then
    let cap_name = Common.pp_type_name_capitalized r in
    if Common.get_force_cross_file_qualification () && not (is_local_inductive r)
    then unqualified_head (Cpp_name.name [class_ cap_name] cap_name)
    else unqualified_head (Cpp_name.unqualified cap_name)
  else if is_enum_cached r then
    (* Enum types at global scope need no struct qualification. Enums inside
       structs (e.g., Comparison::cmp) need it. *)
    let qualifier = if is_global_scope_enum_cached r then [] else struct_scopes_for r type_name in
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
    { outer = struct_scopes_for r cap;
      head = cap;
      typename = needs_typename cap;
      template_keyword = applied && (!render_ctx).rc_in_template }
  else if is_merged_inductive r && not (is_local_inductive r) then
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

(** Whether the type [t] writes a qualifier into a struct or a template
    parameter, asked of the type rather than of its rendering: each name is
    the one {!pp_cpp_type} writes, from the same heads, in the render context
    the caller has set.  [None] where only the rendering can tell -- an
    expression's type, and a type constructor named as a template argument,
    whose alias is minted as it is written. *)
let rec type_names_into_a_struct t =
  let any ts =
    List.fold_left
      (fun acc t -> match acc with Some true | None -> acc | Some false -> type_names_into_a_struct t)
      (Some false) ts
  in
  let ( ||? ) b rest = if b then Some true else rest in
  match t with
  | Tvar _ | Tinstance _ | Tvoid | Thole | Tdecltype_auto | Terased _ | Tany | Topaque -> Some false
  | Tunresolved -> None
  | Tpromoted id -> Some (scopes_name_into_a_struct (Option.default [] (member_scopes id)))
  | Tid (id, args) -> scopes_name_into_a_struct (Option.default [] (member_scopes id)) ||? any args
  | Tid_external (id_s, args) -> text_names_into_a_struct (external_type_name id_s) ||? any args
  | Tglob (r, tys, _) -> (
    match find_custom_opt r with
    | Some s when to_inline r -> text_names_into_a_struct s ||? any tys
    | _ ->
      head_names_into_a_struct (glob_head r ~applied:(tys <> [])) ||? any tys )
  | Tnamespace ((GlobRef.IndRef _ as r), Tglob (r', args, _)) when globref_equal r r' ->
    head_names_into_a_struct (inductive_head r' ~applied:(args <> [])) ||? any args
  | Tnamespace _ | Tqualified _ | Tapply (Tqualified _, _) -> Some true
  | Tapply (head, args) -> any (head :: args)
  | Tfun (dom, cod) -> any (cod :: dom)
  | Tnondeduced t | Tref (_, t) | Tptr t | Tconst t | Tshared_ptr t -> type_names_into_a_struct t
  | Trebind (h, x) -> any [h; x]
  | Tvariant (_, tys) -> any tys
  | Texpr_type _ | Ttyctor _ | Tdecay _ | Tauto -> None

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
let rec declaration_names_into_a_struct (d : cpp_decl) =
  let any_type ts =
    List.fold_left
      (fun acc t -> match acc with Some false -> type_names_into_a_struct t | _ -> acc)
      (Some false) ts
  in
  let names_through n = head_names_into_a_struct (unqualified_head n) in
  match d with
  | Dfun {df_path = {dp_outer; dp_inner}; df_ret; df_shape = Ddecl params; _} ->
    let path = dp_outer :: dp_inner in
    if List.exists (fun (n, _) -> names_through (global_name Type n)) path then Some true
    else any_type ((df_ret :: List.map snd params) @ List.concat_map snd path)
  | Dtemplate (tparams, None, inner) ->
    let concept_names_through c = (not (class_concept_held_back c)) && names_through (concept_name c) in
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
      | Some false -> declaration_names_into_a_struct inner
      | answer -> answer )
  | _ -> None

(** Pretty-print a MiniCpp type as C++ source text.

    @param par  whether to parenthesize (for precedence in function types)
    @param vl   type variable names for de Bruijn index lookup

    A {!Minicpp.Tpromoted} reaching the printer is one no resolution map
    claimed, so it is rendered as a member of the enclosing struct: the bare
    name inside a struct body, [StructName::id] outside one. *)
let rec pp_cpp_type ?(lead = true) par vl t =
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
      ( match member_scopes id with
      | Some scopes -> Cpp_name.pp_scopes scopes ++ Id.print id
      | None -> Id.print id )
    | Tvar (Tv_index (_, Some id) | Tv_named id) -> Id.print id
    (* Tid for local type references (e.g., nested structs inside modules).
       These don't need GlobRef qualification, just simple Id references. Can be
       parameterized like generic types: Leaf<int>. When generating
       out-of-struct definitions, prepend struct name. *)
    | Tid (id, args) ->
      let scopes = Option.default [] (member_scopes id) in
      Cpp_name.pp_scopes scopes ++ Id.print id
      ++ (match args with [] -> mt () | _ -> str "<" ++ pp_list (pp_rec false) args ++ str ">")
    | Tnondeduced t ->
      cpp_angle "std::type_identity_t" (pp_rec false t)
    | Trebind (h, x) ->
      writes_obj ();
      cpp_angle Crane_rt.rebind (pp_list (pp_rec false) [ h; x ])
    | Thole -> str ctor_alias_tvar
    | Tref (Forwarding, t) -> pp_rec false t ++ str "&&"
    | Texpr_type e -> str "decltype(" ++ pp_cpp_expr ([], Id.Set.empty) [] e ++ str ")"
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
          ~container:r
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
        pp_written_head ~lead (glob_head r ~applied:(tys <> []))
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
        pp_written_head ~lead (inductive_head r' ~applied:(args <> []))
        ++ (match args with [] -> mt () | args -> str "<" ++ pp_list (pp_rec false) args ++ str ">")
      | _ ->
        (* Fallback: generic namespace-qualified type *)
        leading_typename
        ++ Cpp_name.pp_qualifier (fun s -> Cpp_name.Class s) (fst (inductive_name r))
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
           declaration has no namespace-scope alias to be, so it is minted as
           a member of a holder and comes back spelled [H<T1>::template c].
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
    let t = match t with Tapply (head, _) -> head | t -> t in
    match ctor_alias_at vl t with
    | Some (alias, args) ->
      let name = register_ctor_alias alias in
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
and ctor_alias_at vl t =
  let custom () =
    match t with
    | Tglob (r, (_ :: _ as args), _) when find_custom_opt r <> None ->
      let fixed = List.filteri (fun i _ -> i < List.length args - 1) args in
      ctor_alias_of_probe vl ~base:(Common.pp_global_name Type r) (Tglob (r, fixed @ [Thole], []))
    | _ -> None
  in
  if exists_cpp_type (fun s -> s = Thole) t then
    match ctor_alias_of_probe vl ~base:"crane_carrier" t with
    | Some _ as alias -> alias
    | None -> custom ()
  else custom ()

(** The template synthesised for [probe], a type constructor applied to the
    sentinel, if its rendering is not a head applied to the sentinel.

    The body is rendered where the template is declared ({!ctor_alias_visibility}),
    because that is where a [using] is read; every name it writes
    has to mean there what it means at the use. *)
and ctor_alias_of_probe vl ~base probe =
  (* The template parameters of the enclosing declaration that the body
     names.  An alias whose body mentions one cannot live at namespace
     scope, so those are what the holder abstracts over. *)
  let captured probe =
    let seen = ref [] in
    let rec go t =
      match t with
      | Tvar (Tv_index (i, _)) ->
        if not (List.mem i !seen) then seen := !seen @ [i]
      | Tglob (_, ts, _) | Tid (_, ts) | Tid_external (_, ts)
      | Tvariant (_, ts) ->
        List.iter go ts
      | Tfun (dom, cod) -> List.iter go dom; go cod
      | Tconst t | Tshared_ptr t | Tref (_, t) | Tptr t | Tnamespace (_, t)
      | Tqualified (t, _) | Tdecay t | Ttyctor t | Tnondeduced t ->
        go t
      | Trebind (h, x) -> go h; go x
      | Tapply (t, ts) -> go t; List.iter go ts
      | _ -> ()
    in
    go probe; !seen
  in
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
    let rec go t =
      match t with
      | Tapply (Tvar (Tv_index (i, _)), ts) ->
        seen := i :: !seen;
        List.iter go ts
      | Tglob (_, ts, _) | Tid (_, ts) | Tid_external (_, ts)
      | Tvariant (_, ts) ->
        List.iter go ts
      | Tfun (dom, cod) -> List.iter go dom; go cod
      | Tconst t | Tshared_ptr t | Tref (_, t) | Tptr t | Tnamespace (_, t)
      | Tqualified (t, _) | Tdecay t | Ttyctor t | Tnondeduced t ->
        go t
      | Trebind (h, x) -> go h; go x
      | Tapply (t, ts) -> go t; List.iter go ts
      | _ -> ()
    in
    go probe; !seen
  in
  (* A variable the body names bare is kept where it is a declared
     parameter -- named, as a plain family the declaration deapplied is
     -- and becomes a [typename] parameter of the holder. *)
  let bare_vars =
    let seen = ref [] in
    ignore
      (map_cpp_type
         (function
           | Tvar (Tv_index (i, Some _)) as t when not (List.mem i applied_vars) ->
             seen := i :: !seen;
             t
           | t -> t )
         probe );
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
  let home = ctor_alias_home probe in
  let render t =
    Common.with_visibility (ctor_alias_visibility home) (fun () -> Pp.string_of_ppcmds (pp_cpp_type false vl t))
  in
  let rendered = render probe in
  if
    String.equal rendered
      (cut_at_argument_list rendered ^ "<" ^ ctor_alias_tvar ^ ">")
  then None
  else
    (* Only a name the body actually {e writes} has to be abstracted
       over.  A custom mapping's replacement text need not use every
       argument -- [itree]'s spells only its last -- so a parameter that
       the probe carries structurally but the rendering drops would
       otherwise mint a holder with an unused parameter, and the alias
       would be declared as a partial specialisation of nothing. *)
    let names = identifier_tokens rendered in
    let captured probe =
      List.filter
        (fun i ->
          List.mem
            (Pp.string_of_ppcmds (print_cpp_type_var vl i))
            names )
        (captured probe)
    in
    (* A class instance the body reads a type out of -- [typename
       _tcI0::ptr] -- is the enclosing declaration's parameter as much
       as a variable is, and is captured the same way. *)
    let instances =
      let seen = ref [] in
      ignore
        (map_cpp_type
           (function
             | Tinstance (id, _) as t ->
               if not (List.exists (Id.equal id) !seen) then
                 seen := !seen @ [id];
               t
             | t -> t )
           probe );
      !seen
    in
    match (captured probe, instances) with
    | [], [] -> Some ({ca_base = base; ca_holder = false; ca_home = home; ca_body = rendered}, [])
    | vars, instances ->
      (* Rendered a second time with the captured names replaced by the
         holder's own, so that two declarations differing only in what
         they call their parameters share one holder. *)
      let renamed =
        List.fold_left
          (fun acc (k, i) ->
            map_cpp_type
              (function
                | Tvar (Tv_index (j, _)) when j = i ->
                  Tid_external
                    ( Id.to_string
                        (Generated_name.indexed
                           (if List.mem i bare_vars then "P" else "F")
                           k),
                      [] )
                | t -> t )
              acc )
          probe
          (List.mapi (fun k i -> (k, i)) vars)
      in
      let renamed =
        List.fold_left
          (fun acc (k, id) ->
            map_cpp_type
              (function
                | Tinstance (id', c) when Id.equal id id' ->
                  Tinstance (Generated_name.indexed "P" k, c)
                | t -> t )
              acc )
          renamed
          (List.mapi (fun j id -> (List.length vars + j, id)) instances)
      in
      Some
        ( {ca_base = base; ca_holder = true; ca_home = home; ca_body = render renamed},
          List.map (fun i -> Pp.string_of_ppcmds (print_cpp_type_var vl i)) vars
          @ List.map Id.to_string instances )

(** Render [ty] as the qualifier of a {e value} -- [T::member] -- rather than of
    a nested type.

    A type and a value spell the same global differently.  The type spelling
    carries a leading [typename] for a dependent qualifier (see
    {!Cpp_names.typename_prefix_for}), which is ill-formed in front of a static
    member function -- [typename C::t::pair(x)] claims [pair] names a type --
    and it qualifies a global by its namespace where the value spelling elides
    the prefix that is already in scope.  A named global therefore goes through
    the expression printer; anything else only needs the keyword removed. *)
and pp_value_qualifier env ty =
  match ty with
  | Tglob (r, tys, []) ->
    (* No [~yields]: a type qualifier is never a block in value position. *)
    pp_cpp_expr env [] (CPPglob (r, tys, Some (Table.custom_info r)))
  | _ ->
  pp_cpp_type ~lead:false false [] ty

(** Pretty-print a MiniCpp expression as C++ source.  The central expression
    printer of the module; dispatches on every {!Minicpp.cpp_expr} form and
    recurses into {!pp_cpp_stmt} for block/statement-valued expressions.

    @param env   name environment: the de Bruijn name list plus the set of
                 identifiers currently in scope
    @param args  arguments accumulated by callers (already pretty-printed) to be
                 applied once the head expression is reached, via [pp_apply_cpp]
    @param t     the expression to render *)
(* A member named after [.] or [->], with the template arguments it writes. *)
and pp_member_name method_name = function
  | [] -> Id.print method_name
  | tys ->
    str "template " ++ Id.print method_name ++ str "<"
    ++ pp_list (pp_cpp_type false []) tys
    ++ str ">"

and pp_cpp_expr env args t =
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
        ~container:ref_name
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
  | CPPglob (x, tys, Some {ci_inline = Some tmpl; ci_yields; _}) ->
    let custom = tmpl.it_text in
    if tmpl.it_form = Block_iife then
      gen_block_iife ?yields:ci_yields x custom tys []
    else
    let cmds = type_template custom in
    pp_custom
      ~container:x
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
  | CPPmethod_value {mv_method; mv_access; mv_receiver; mv_params; mv_type_args} ->
    let names =
      match mv_params with
      | [_] -> ["_x"]
      | ps -> List.mapi (fun i _ -> "_x" ^ string_of_int i) ps
    in
    let param name = function
      | Some ty ->
        Pp.string_of_ppcmds (str "const " ++ pp_cpp_type false [] ty ++ str (" &" ^ name))
      | None -> "const auto &" ^ name
    in
    let params = String.concat ", " (List.map2 param names mv_params) in
    let call_args = String.concat ", " (List.filteri (fun i _ -> i <> mv_receiver) names) in
    str ("[](" ^ params ^ ") { return " ^ List.nth names mv_receiver)
    ++ str (pp_obj_access mv_access)
    ++ pp_member_name (Common.id_of_global Term mv_method) mv_type_args
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
      | GlobRef.IndRef _ ->
        let ns_name, needs_ns = inductive_name x in
        let type_name = global_name Type x in
        let force = Common.get_force_cross_file_qualification () in
        `Named
          ( (* Check eponymous record FIRST because they can also be local *)
            if is_eponymous_record_cached x then
              Cpp_name.unqualified (Common.pp_type_name_capitalized x)
            else if Ref.User.Tbl.mem promoted_inductives x then
              dedup_tail (if force then capitalize_base type_name else capitalize_initial type_name)
            else if Cpp_name.is_qualified type_name then
              let cap = if force then capitalize_base type_name else type_name in
              if is_merged_inductive x then
                let allow_bare =
                  let ref_base = base_mp (modpath_of_r x) in
                  List.exists (ModPath.equal ref_base) (visible_mps (current_visibility ()))
                in
                dedup_tail ~allow_bare cap
              else cap
            else if needs_ns then
              if is_merged_inductive x then
                (* Merged non-local inductive: use capitalized name directly *)
                List.fold_right Cpp_name.within (global_scopes_for x ns_name) ns_name
              else (* Unmerged non-local inductive: Wrapper::inner *)
                Cpp_name.inside ns_name class_ type_name
            else if force then capitalize_initial type_name
            else (* Local inductive: use original name directly *)
              type_name )
      | GlobRef.VarRef v -> `Named (Cpp_name.unqualified (Id.to_string v))
      | _ ->
      (* Check if this function is inside an eponymous template struct. If so,
         type args go on the struct name, not the function name. *)
      match (Module_plan.eponymous_record_containing x, tys) with
      | Some record_ref, _ :: _ ->
        (* Function inside eponymous template struct with type args: Generate
           StructName<int, ...>::template funcName<Args> for static methods. We
           use placeholder types for the struct and actual args for the
           method. *)
        let struct_name = Common.pp_global_name Type record_ref in
        let func_name = Common.pp_global_name Term x in
        let placeholder_args = gen_placeholder_args (num_ind_params record_ref) in
        let ty_args = pp_list (pp_cpp_type false []) tys in
        `Written
          ( Cpp_name.pp_type_qualifier class_
              (str (String.capitalize_ascii struct_name) ++ str "<" ++ str placeholder_args ++ str ">")
          ++ str "template "
          ++ str func_name
          ++ str "<"
          ++ ty_args
          ++ str ">" )
      | Some record_ref, [] ->
        let struct_name = Common.pp_global_name Type record_ref in
        let func_name = Common.pp_global_name Term x in
        let placeholder_args = gen_placeholder_args (num_ind_params record_ref) in
        `Written
          ( Cpp_name.pp_type_qualifier class_
              (str (String.capitalize_ascii struct_name) ++ str "<" ++ str placeholder_args ++ str ">")
          ++ str func_name )
      | None, _ ->
        (* Normal case: function not in eponymous struct *)
        let name = global_name Term x in
        let qualified = wrapper_qualify x name in
        if not (Cpp_name.equal qualified name) then `Named qualified
        else if needs_global_qualifier x then `Named (Cpp_name.within Cpp_name.Global name)
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
      let found_in_list =
        List.exists
          (fun (reg_mp, reg_lbl) ->
            Label.equal x_lbl reg_lbl
            && ( ModPath.equal x_mp reg_mp
               || ModPath.equal resolved_x_mp reg_mp ) )
          !template_static_accessors
      in
      if found_in_list then true
      else
          let in_lbl_list = List.exists (fun (_, reg_lbl) -> Label.equal x_lbl reg_lbl)
            !template_static_accessors in
          in_lbl_list
          && ( under_mp_bound x_mp
             || (not (under_mp_bound resolved_x_mp)
                 && (under_mp_bound x_mp || under_mp_bound resolved_x_mp
                     || not (ModPath.equal x_mp resolved_x_mp))) )
    in
    let full_name =
      match (base, tys, Module_plan.eponymous_record_containing x) with
      | `Written _, _, _ | _, [], _ | _, _, Some _ -> base_name
      | `Named n, _, None ->
        (* A template named through a qualifier takes the [template]
           disambiguator: [C::template empty<T>]. *)
        Cpp_name.pp ~template_keyword:true n
        ++ str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
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
    let name, _ = inductive_name r in
    Cpp_name.pp_qualifier (fun s -> Cpp_name.Class s) name ++ pp_cpp_expr env args t
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
        | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
      in
      let args_s = pp_list (pp_cpp_expr env args) (call_args ts) in
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
              (Pp.string_of_ppcmds (pp_cpp_type false [] ty)) s
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
        ~container:n
        (Pp.string_of_ppcmds (GlobRef.print n) ^ " := " ^ s)
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
    pp_cpp_expr env args mc_receiver
    ++ str (pp_obj_access mc_access)
    ++ pp_member_name (Common.id_of_global Term mc_method) mc_type_args
    ++ str "("
    ++ pp_list (pp_cpp_expr env args) mc_args
    ++ str ")"
  | CPPfun_call (_, CPPrt Crane_rt.Share_child, {rev = [arg]}) -> (
    (* A field read out of a matched value goes to the new node as the cell
       it is in; anything else is the value itself. *)
    match arg with
    | CPPderef p -> str (Crane_rt.name Crane_rt.Share_child) ++ str "(" ++ pp_cpp_expr env args p ++ str ")"
    | _ -> pp_cpp_expr env args arg )
  | CPPfun_call (_, CPPderef e, ts) ->
    (* Call through a dereferenced pointer: deref + invoke pattern.
       Arises from the shared_ptr fixpoint pattern where recursive calls
       dereference the function pointer before invoking. *)
    let args_s = pp_list (pp_cpp_expr env args) (call_args ts) in
    str "(*" ++ pp_cpp_expr env args e ++ str ")(" ++ args_s ++ str ")"
  | CPPfun_call
      (_,  CPPlambda
        { cl_params = {rev = []};
          cl_body = [Smatch (scrut, branches, wildcard)];
          cl_capture = Immediate;
          _ },
        {rev = []} )
    when (* Detect simple IIFE-wrapped matches that can be printed as ternary.
            Eligible: exactly 2 return-only branches (no wildcard), or 1 branch
            + a return-only wildcard; no structured bindings, no extra conditions. *)
      ( match branches, wildcard with
      | [br1; br2], None ->
        br1.smb_field_bindings = [] && br2.smb_field_bindings = []
        && br1.smb_extra_conds = [] && br2.smb_extra_conds = []
        && ( match br1.smb_body, br2.smb_body with
             | [Sreturn (Some _)], [Sreturn (Some _)] -> true
             | _ -> false )
      | [br1], Some [Sreturn (Some _)] ->
        br1.smb_field_bindings = []
        && br1.smb_extra_conds = []
        && ( match br1.smb_body with
             | [Sreturn (Some _)] -> true
             | _ -> false )
      | _ -> false ) ->
    writes_variant ();
    let pp = pp_cpp_expr env args in
    let cond_pp, then_e, else_e =
      match branches, wildcard with
      | [br1; br2], None ->
        let cond =
          str (sn ()).holds_alternative ++ str "<"
          ++ pp_cpp_type false [] br1.smb_ctor_type ++ str ">("
          ++ pp scrut.sc_expr ++ str ")"
        in
        let e1 = match br1.smb_body with [Sreturn (Some e)] -> e
          | _ -> CErrors.anomaly (Pp.str "ternary: expected single Sreturn in branch") in
        let e2 = match br2.smb_body with [Sreturn (Some e)] -> e
          | _ -> CErrors.anomaly (Pp.str "ternary: expected single Sreturn in branch") in
        (cond, e1, e2)
      | [br1], Some [Sreturn (Some e2)] ->
        let cond =
          str (sn ()).holds_alternative ++ str "<"
          ++ pp_cpp_type false [] br1.smb_ctor_type ++ str ">("
          ++ pp scrut.sc_expr ++ str ")"
        in
        let e1 = match br1.smb_body with [Sreturn (Some e)] -> e
          | _ -> CErrors.anomaly (Pp.str "ternary: expected single Sreturn in branch") in
        (cond, e1, e2)
      | _ -> CErrors.anomaly (Pp.str "ternary: unexpected branch structure")
    in
    str "(" ++ cond_pp ++ str " ? " ++ pp then_e ++ str " : " ++ pp else_e ++ str ")"
  | CPPfun_call
      (_,  CPPlambda
        { cl_params = {rev = []};
          cl_body = [Sif (cond, [Sreturn (Some e1)], [Sreturn (Some e2)])];
          _ },
        {rev = []} )
    when not (expr_contains_string e1 || expr_contains_string e2) ->
    (* IIFE wrapping a simple if/else with single-expression returns in both
       branches → emit as ternary.  Skip when branches contain string literals
       to preserve implicit const char* → std::string conversion. *)
    let pp = pp_cpp_expr env args in
    str "(" ++ pp cond ++ str " ? " ++ pp e1 ++ str " : " ++ pp e2 ++ str ")"
  | CPPfun_call
      (_,  CPPlambda
        { cl_params = {rev = []};
          cl_body = [Scustom_case (_, scrut, _, branches, cmatch)];
          _ },
        {rev = []} )
    when (* Custom case with exactly 2 return-only branches and the standard
            bool-like if/else template → emit ternary.  Skip when branches
            contain string literals (const char* → std::string coercion). *)
      String.trim cmatch.cm_template = "if (%scrut) { %br0 } else { %br1 }"
      && List.length branches = 2
      && List.for_all
           (fun (_, _, stmts) ->
             match stmts with
             | [Sreturn (Some e)] -> not (expr_contains_string e)
             | _ -> false)
           branches ->
    let pp = pp_cpp_expr env args in
    let e1 = match branches with
      | (_, _, [Sreturn (Some e)]) :: _ -> e
      | _ -> CErrors.anomaly (Pp.str "ternary: unexpected custom_case branch structure")
    in
    let e2 = match branches with
      | _ :: (_, _, [Sreturn (Some e)]) :: _ -> e
      | _ -> CErrors.anomaly (Pp.str "ternary: unexpected custom_case branch structure")
    in
    str "(" ++ pp scrut ++ str " ? " ++ pp e1 ++ str " : " ++ pp e2 ++ str ")"
  | CPPprojection {pj_projection; pj_record; pj_args} ->
    pp_cpp_expr env args pj_record ++ str "." ++ str (projection_field_name pj_projection)
    ++ (if pj_args = [] then mt () else str "(" ++ pp_list (pp_cpp_expr env args) pj_args ++ str ")")
  | CPPfun_call (_, f, ts) ->
    let args_s = pp_list (pp_cpp_expr env args) (call_args ts) in
    let prefix = match f with
      | CPPglob (GlobRef.IndRef _, _, _)
        when (!render_ctx).rc_in_template && writes_qualifier (pp_cpp_expr env args f) ->
        str "typename "
      | _ -> mt ()
    in
    prefix ++ pp_cpp_expr env args f ++ str "(" ++ args_s ++ str ")"
  (* A box is the converting constructor [std::any(e)], so it prints as one. *)
  | CPPbox (ty, e) -> pp_cpp_expr env args (CPPconverting_ctor (ty, [ e ]))
  | CPPconverting_ctor (ty, ts) ->
    pp_cpp_type false [] ty ++ str "(" ++ pp_list (pp_cpp_expr env args) ts ++ str ")"
  | CPPderef e ->
    let needs_parens = match e with
      | CPPvar _ | CPPthis | CPPfun_call _ | CPPaccess _
      | CPPaccess_call _ | CPPmethod_call _ | CPPprojection _ -> false
      | _ -> true
    in
    if needs_parens then str "*(" ++ pp_cpp_expr env args e ++ str ")"
    else str "*" ++ pp_cpp_expr env args e
  | CPPmove e ->
    writes_standard "utility";
    str (sn ()).move ++ str "(" ++ pp_cpp_expr env args e ++ str ")"
  | CPPforward (ty, e) ->
    str (sn ()).forward
    ++ str "<"
    ++ pp_cpp_type false [] ty
    ++ str ">("
    ++ pp_cpp_expr env args e
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
    let capture_str =
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
    let body_s = pp_list_stmt (pp_cpp_stmt env args) body in
    let params_s, capture =
      match params with
      | [] -> (mt (), capture_str)
      | _ ->
        let mentioned = output_mentions body_s in
        ( pp_list
            (fun (ty, id_opt) ->
              match id_opt with
              | None -> pp_cpp_type false [] ty
              | Some id when not (mentioned id) -> pp_cpp_type false [] ty
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
        ++ str " -> "
        ++ pp_cpp_type false [] ty )
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
    cpp_angle Crane_rt.shared_box (pp_cpp_type false [] t) ++ str "::make"
  | CPPalloc (Alloc_heap, t) ->
    writes_standard "memory";
    cpp_angle (sn ()).make_shared (pp_cpp_type false [] t)
  | CPPalloc (Alloc_reusing, t) ->
    (* Perceus reuse factory; only emitted under NonAtomicRc (crane::rc). *)
    cpp_angle Crane_rt.make_rc_reusing (pp_cpp_type false [] t)
  | CPPalloc (Alloc_arena_scoped, t) ->
    (* Runtime scoped-arena factory: the arena-aware form of make_shared/make_rc
       for the current pointer flavor.  Falls back to a plain heap allocation at
       runtime whenever no arena scope is open at the call site. *)
    let inner = pp_cpp_type false [] t in
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
    let es_s = pp_list (pp_cpp_expr env args) es in
    let templates =
      match tys with
      | [] -> mt ()
      | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
    in
    let struct_name =
      match id with
      | GlobRef.IndRef _ when is_eponymous_record_cached id ->
        Cpp_name.unqualified (Common.pp_type_name_capitalized id)
      | _ -> global_name Type id
    in
    typename_prefix_for struct_name
    ++ Cpp_name.pp struct_name ++ templates ++ str suffix ++ es_s ++ closing
  | CPPstruct_id (id, tys, es) ->
    let es_s = pp_list (pp_cpp_expr env args) es in
    let templates =
      match tys with
      | [] -> mt ()
      | _ -> str "<" ++ pp_list (pp_cpp_type false []) tys ++ str ">"
    in
    Id.print id ++ templates ++ str "{" ++ es_s ++ str "}"
  | CPPget (e, id) ->
    ( match e with
    | CPPderef CPPthis -> str "this->" ++ Id.print id
    | CPPderef _ | CPPraw _ ->
      str "(" ++ pp_cpp_expr env args e ++ str ")." ++ Id.print id
    | _ -> pp_cpp_expr env args e ++ str "." ++ Id.print id )
  | CPPget' (e, id, _) ->
    let field_name = str (Common.pp_global_name Type id) in
    ( match e with
    | CPPderef CPPthis -> str "this->" ++ field_name
    | CPPderef _ | CPPraw _ ->
      str "(" ++ pp_cpp_expr env args e ++ str ")." ++ field_name
    | _ -> pp_cpp_expr env args e ++ str "." ++ field_name )
  | CPPstring s -> str ("\"" ^ escape_cpp_string (Pstring.to_string s) ^ "\"")
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
      | Some "int64_t" -> str ("INT64_C(" ^ s ^ ")")
      | Some cpp_type -> str (cpp_type ^ "(" ^ s ^ ")")
      | None -> str s )
    | _ -> str s )
  | CPPfloat f -> str (spell_double (Float64.to_float f))
  | CPPconcept_app (concept, subject, tys) ->
    (* A concept is hoisted out of every enclosing struct, so it is named
       unqualified here however deeply the subject is nested. *)
    pp_concept_name_of_ref concept
    ++ str "<"
    ++ pp_global Type subject
    ++ prlist (fun ty -> str ", " ++ pp_cpp_type false [] ty) tys
    ++ str ">"
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
  | CPPthis -> str "this"
  | CPPshared_from_this ty ->
    (* [crane::rc] returns a mutable [rc<T>] from [rc_from_this()], so no
       const_pointer_cast is needed; [std::shared_ptr] needs the cast to strip
       the const that [shared_from_this()] adds in const methods. *)
    if String.equal (sn ()).shared_ptr Crane_rt.rc then
      str "this->rc_from_this()"
    else
      str "std::const_pointer_cast<"
      ++ pp_cpp_type false [] ty
      ++ str ">(this->shared_from_this())"
  | CPPaccess (acc, e, id) ->
    (* Rewrite std::move(x).field → std::move(x.field): access the field
       first, then move its value.  This is semantically equivalent and:
       - Fixes Infer Use-After-Delete (moving a pointer then accessing it is flagged)
       - Enables the Unnecessary-Copy-Intermediate fix (field value is moved, not copied)
       For method calls we strip the move instead since methods need a live object. *)
    ( match (acc, e) with
    | Adot, CPPmove inner ->
      str (sn ()).move ++ str "(" ++ pp_cpp_expr env args inner ++ str "."
      ++ Id.print id ++ str ")"
    | Aarrow, CPPmove inner ->
      (* std::move(ptr)->field → std::move(ptr->field) *)
      str (sn ()).move ++ str "(" ++ pp_object env args inner ++ str "->"
      ++ Id.print id ++ str ")"
    | Adot, CPPderef inner ->
      (* Dot access on a dereferenced pointer is arrow access on the pointer. *)
      pp_object env args inner ++ str "->" ++ Id.print id
    | _ -> pp_object env args e ++ str (pp_obj_access acc) ++ Id.print id )
  | CPPaccess_call (acc, obj, method_name, call_args) ->
    let obj = match obj with CPPmove inner -> inner | _ -> obj in
    pp_object env args obj ++ str (pp_obj_access acc) ++ Id.print method_name
    ++ str "(" ++ pp_list (pp_cpp_expr env args) call_args ++ str ")"
  | CPPscope (e, id, []) ->
    pp_cpp_expr env args e ++ str "::" ++ Id.print id
  | CPPscope (e, id, tys) ->
    pp_cpp_expr env args e ++ str "::template " ++ Id.print id ++ str "<"
    ++ pp_list (pp_cpp_type false []) tys ++ str ">"
  | CPPqualified_t (ty, id) ->
    pp_value_qualifier env ty ++ str "::" ++ Id.print id
  | CPPconvertible_to ty ->
    writes_standard "concepts";
    str "std::convertible_to<" ++ pp_cpp_type false [] ty ++ str ">"
  | CPPabort (msg, ty) ->
    writes_standard "stdexcept";
    str "([]() -> "
    ++ pp_cpp_type false [] ty
    ++ str " { throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str (escape_cpp_string msg)
    ++ str "\"); })()"
  | CPPenum_val (ind, ctor) ->
    (* Generate EnumType::Constructor for enum class values. Use str_global for
       proper module qualification, with collision-aware capitalization. *)
    let full_name = enum_name (global_name Type ind) ind in
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
    str "{" ++ pp_list (pp_cpp_expr env args) es ++ str "}"
  | CPPstd_get (ty, None) ->
    writes_variant ();
    str ((sn ()).get ^ "<") ++ pp_cpp_type false [] ty ++ str ">"
  | CPPstd_get (ty, Some e) ->
    writes_variant ();
    str ((sn ()).get ^ "<") ++ pp_cpp_type false [] ty ++ str ">("
    ++ pp_cpp_expr env args e
    ++ str ")"
  | CPPstd_holds_alternative ty ->
    writes_variant ();
    str ((sn ()).holds_alternative ^ "<") ++ pp_cpp_type false [] ty ++ str ">"
  | CPPdeclval ty ->
    writes_standard "utility";
    str "std::declval<" ++ pp_cpp_type false [] ty ++ str ">()"
  | CPPtype_name ty -> pp_cpp_type false [] ty
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
  | CPPnumeral (r, n) -> (
    match Table.get_numeral_info r with
    | Some info -> str (Common.render_template [("%n", Z.to_string n)] info.Table.num_fmt)
    | None -> CErrors.anomaly Pp.(str "a numeral of a type with no numeral format") )
  | CPPraw code ->
    str
      (Str.global_replace
         (Str.regexp_string "*(this).")
         "(*(this))."
         code)
  | CPPbinop (op, lhs, rhs) ->
    (* Parenthesize && subexpressions inside || to avoid
       -Wlogical-op-parentheses warnings. *)
    let paren_child child =
      match child with
      | CPPbinop (Band, _, _) when op = Bor ->
        str "(" ++ pp_cpp_expr env args child ++ str ")"
      | CPPbinop (Bor, _, _) when op = Band ->
        str "(" ++ pp_cpp_expr env args child ++ str ")"
      | _ -> pp_cpp_expr env args child
    in
    paren_child lhs
    ++ str " "
    ++ str (spell_binop op)
    ++ str " "
    ++ paren_child rhs
  | CPPcond (cond, then_expr, else_expr) ->
    (* Wrap the whole ternary in parentheses like the other ternary sites, so a
       conditional used as a subexpression cannot bind incorrectly against a
       surrounding operator. *)
    str "("
    ++ pp_cpp_expr env args cond
    ++ str " ? "
    ++ pp_cpp_expr env args then_expr
    ++ str " : "
    ++ pp_cpp_expr env args else_expr
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
      | CPPbinop _ | CPPcond _ -> str "(" ++ pp_cpp_expr env args e ++ str ")"
      | _ -> pp_cpp_expr env args e
    in
    str (spell_unop op) ++ operand
  | CPPunbox (Unbox_to ty, e) ->
    writes_obj ();
    str Crane_rt.obj_cast ++ str "<" ++ pp_cpp_type false [] ty ++ str ">("
    ++ pp_cpp_expr env args e ++ str ")"
  | CPPunbox (Unbox_or_keep ty, e) ->
    writes_standard "type_traits";
    let ty_pp = pp_cpp_type false [] ty and e_pp = pp_cpp_expr env args e in
    str "[&]() -> " ++ ty_pp
    ++ str " { if constexpr (std::is_same_v<" ++ ty_pp
    ++ str (", " ^ Crane_rt.obj ^ ">) return ") ++ e_pp
    ++ str "; else return " ++ str Crane_rt.obj_cast
    ++ str "<" ++ ty_pp ++ str ">(" ++ e_pp ++ str "); }()"
  | CPPunbox (Unbox_list (list_ty, flat_ty), e) ->
    pp_cpp_type false [] list_ty
    ++ str "(" ++ str Crane_rt.obj_cast ++ str "<"
    ++ pp_cpp_type false [] flat_ty
    ++ str ">(" ++ pp_cpp_expr env args e ++ str "))"
  | CPPany_cast (ty, e) | CPPany_cast_tolerant (ty, e) ->
    writes_obj ();
    (* A binder holding a known type in a box is read bare inside a cast
       that already names its type; {!Cpp_erasure.lower_boxed_reads} leaves
       it so. *)
    let inner = pp_cpp_expr env args e in
    (* Which caster, and whether the cast is needed at all, was decided by
       {!Cpp_erasure.resolve_casts}. *)
    let caster =
      match t with
      | CPPany_cast_tolerant _ ->
        writes Table.erase_fn_header;
        Crane_rt.any_cast
      | _ -> Crane_rt.obj_cast
    in
    str caster ++ str "<" ++ pp_cpp_type false [] ty ++ str ">(" ++ inner
    ++ str ")"
  | CPPerase_fn
      (shape, (CPPglob (GlobRef.ConstRef _, [], (None | Some {ci_inline = None; _})) as g)) ->
    (* A global never changes, so neither does its adapter: made once.  A
       method is never a global here: it is named through a lambda
       ({!Minicpp.method_value}), never as itself. *)
    writes Table.erase_fn_header;
    str Crane_rt.erase_global ++ str "<" ++ pp_cpp_expr env args g
    ++ ( match shape with
       | Boxed_whole -> mt ()
       | At_signature ty -> str ", " ++ pp_cpp_type false [] ty )
    ++ str ">()"
  | CPPsuspend (ty, thunk) ->
    pp_cpp_expr env args
      (CPPfun_call
         ( Minicpp.call_sig ~yields:ty ~nargs:1 (),
           CPPqualified_t (ty, Id.of_string "lazy_"),
           of_reversed [thunk] ))
  | CPPerase_fn (shape, e) ->
    writes Table.erase_fn_header;
    str Crane_rt.erase_fn
    ++ ( match shape with
       | Boxed_whole -> mt ()
       | At_signature ty -> str "<" ++ pp_cpp_type false [] ty ++ str ">" )
    ++ str "("
    ++ pp_cpp_expr env args e
    ++ str ")"
  | CPPerased_call (f, a) ->
    (* The one signature a callable is erased into storage at, so the one it
       can be recovered at; each application yields a [std::any] in turn. *)
    writes_obj ();
    writes_standard "functional";
    str Crane_rt.obj_cast
    ++ str "<"
    ++ pp_cpp_type false [] (Tfun ([Tany], Tany))
    ++ str ">("
    ++ pp_cpp_expr env args f
    ++ str ")("
    ++ pp_cpp_expr env args a
    ++ str ")"
  | CPPtolerant_call (f, call_args) ->
    writes Table.erase_fn_header;
    str Crane_rt.call_erased
    ++ str "("
    ++ prlist_with_sep pr_comma (pp_cpp_expr env args) (f :: call_args)
    ++ str ")"
  | CPPfn_value e ->
    writes (Table.Runtime Crane_rt.fn_header);
    str Crane_rt.fn ++ str "(" ++ pp_cpp_expr env args e ++ str ")"
  | CPPconvert (ty, e) ->
    writes Table.erase_fn_header;
    str Crane_rt.convert
    ++ str "<"
    ++ pp_cpp_type false [] ty
    ++ str ">("
    ++ pp_cpp_expr env args e
    ++ str ")"
  | CPPcontainer_cast (ty, e, suppress_boxing) ->
    writes Table.erase_fn_header;
    let saved = !suppress_elem_boxing in
    if suppress_boxing then suppress_elem_boxing := true;
    let ty_pp = pp_cpp_type false [] ty in
    suppress_elem_boxing := saved;
    str Crane_rt.container_cast ++ str "<"
    ++ ty_pp
    ++ str ">("
    ++ pp_cpp_expr env args e
    ++ str ")"
  | CPPstd_get_if (ty, e) ->
    writes_variant ();
    str ((sn ()).get_if ^ "<") ++ pp_cpp_type false [] ty ++ str ">("
    ++ pp_cpp_expr env args e ++ str ")"

(** [pp_object env args e] prints [e] in the position a [.], [->] or member
    call is about to be applied to.

    Postfix operators bind tighter than the prefix ones, so an [e] that prints
    with a leading [*] has to be parenthesised for the access to apply to [e]
    as a whole rather than to its operand. *)
and pp_object env args e =
  match e with
  | CPPderef _ -> str "(" ++ pp_cpp_expr env args e ++ str ")"
  | CPPraw s when String.length s > 0 && s.[0] = '*' ->
    str "(" ++ pp_cpp_expr env args e ++ str ")"
  | _ -> pp_cpp_expr env args e

(** Pretty-print a MiniCpp statement as C++ source.

    @param env   name environment (see {!pp_cpp_expr})
    @param args  accumulated argument list forwarded to sub-expression printers *)
and pp_cpp_stmt env args = function
  | Sreturn None -> str "return;"
  | Sreturn (Some (CPPabort (msg, _))) ->
    writes_standard "stdexcept";
    str "throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str (escape_cpp_string msg)
    ++ str "\");"
  | Sreturn (Some e) ->
    (* Strip std::move from return statements when the inner expression is a
       plain variable — C++ applies implicit move on local variables in return
       statements.  Explicit std::move prevents NRVO and triggers
       -Wpessimizing-move / -Wredundant-move.
       Keep std::move for non-variable expressions like *_head (dereference of
       shared_ptr) where explicit move is required. *)
    let e = match e with
      | CPPmove (CPPvar _ as inner) -> inner
      | CPPmove ((CPPfun_call _ | CPPaccess_call _ | CPPmethod_call _ | CPPprojection _ | CPPstruct _
                 | CPPstructmk _ | CPPstruct_id _) as inner) -> inner
      | _ -> e
    in
    str "return " ++ pp_cpp_expr env args e ++ str ";"
  | Sdecl (id, ty) ->
    pp_cpp_type false [] ty ++ str " " ++ Id.print id ++ str ";"
  | Sasgn (id, Declare ty, e) ->
    pp_cpp_type false [] ty
    ++ str " "
    ++ Id.print id
    ++ str " = "
    ++ pp_cpp_expr env args e
    ++ str ";"
  | Sasgn (id, Existing, e) ->
    Id.print id ++ str " = " ++ pp_cpp_expr env args e ++ str ";"
  | Sasgn (id, Declare_static ty, e) ->
    str "static " ++ pp_cpp_type false [] ty ++ str " " ++ Id.print id ++ str " = "
    ++ pp_cpp_expr env args e ++ str ";"
  | Sexpr e -> pp_cpp_expr env args e ++ str ";"
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
      let n = inductive_type_name ind in
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
      ++ pp_list_stmt (pp_cpp_stmt env args) stmts
      ++ ( if ends_with_return stmts then mt ()
         else fnl () ++ str "break;" )
      ++ fnl ()
      ++ str "}"
    in
    writes_standard "utility";
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
    ++ pp_cpp_type false [] t1
    ++ str ", "
    ++ pp_cpp_type false [] t2
    ++ str ">) {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) then_stmts
    ++ fnl ()
    ++ str "} else {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) else_stmts
    ++ fnl ()
    ++ str "}"
  | Sif (cond, then_stmts, else_stmts) ->
    str "if ("
    ++ pp_cpp_expr env args cond
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) then_stmts
    ++ fnl ()
    ++ ( match else_stmts with
       | [] -> str "}"
       | _ ->
         str "} else {"
         ++ fnl ()
         ++ pp_list_stmt (pp_cpp_stmt env args) else_stmts
         ++ fnl ()
         ++ str "}" )
  | Sif_decl (id, ty, init, then_stmts, else_stmts) ->
    str "if ("
    ++ pp_cpp_type false [] ty ++ str " " ++ Id.print id
    ++ str " = " ++ pp_cpp_expr env args init
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) then_stmts
    ++ fnl ()
    ++ (match else_stmts with
        | [] -> str "}"
        | _ ->
          str "} else {"
          ++ fnl ()
          ++ pp_list_stmt (pp_cpp_stmt env args) else_stmts
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
           pp_cpp_type false [] ty ++ str " " ++ Id.print fid ++ str "; ")
         fields
    ++ str "};"
  | Susing (name, ty) ->
    str "using " ++ Id.print name ++ str " = " ++ pp_cpp_type false [] ty ++ str ";"
  | Sdecl_init (id, ty) ->
    pp_cpp_type false [] ty ++ str " " ++ Id.print id ++ str "{};"
  | Sbind (ids, e) ->
    str "const auto& [" ++ prlist_with_sep (fun () -> str ", ") Id.print ids
    ++ str "] = " ++ pp_cpp_expr env args e ++ str ";"
  | Sfor_range (id, e, body) ->
    str "for (auto& " ++ Id.print id ++ str " : "
    ++ pp_cpp_expr env args e
    ++ str ") {"
    ++ fnl ()
    ++ pp_list_stmt (pp_cpp_stmt env args) body
    ++ fnl ()
    ++ str "}"
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
  | Sassign_expr (lhs, e) ->
    pp_cpp_expr env args lhs
    ++ str " = "
    ++ pp_cpp_expr env args e
    ++ str ";"
  | Sblock_custom (_ref, tmpl, result_var, result_ty, args, tyargs) ->
    (* Block template: emit a declaration + template-substituted statements.
       %result → result_var, %aN → value args, %tN → type args *)
    let result_str = Pp.string_of_ppcmds (Id.print result_var) in
    (* Substitute %result first *)
    let flat = with_result result_str tmpl in
    let cmds = term_template flat in
    (* Render: type declaration + template body as statements *)
    let decl_pp =
      pp_cpp_type false [] result_ty
      ++ str " "
      ++ Id.print result_var
      ++ str ";"
    in
    let body_pp =
      pp_custom
        ~container:_ref
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
    (* Scrutinee caching (auto _cs = expr;) is handled during translation
       in gen_custom_cpp_case, which prepends an Sasgn before this node
       when the template uses %scrut more than once with a non-trivial
       scrutinee.  The printer just expands the template. *)
    let cmds = match_template cmatch.cm_template in
    pp_custom
      ( "custom match for "
      ^ Pp.string_of_ppcmds (pp_cpp_type false [] typ)
      ^ " := "
      ^ cmatch.cm_template )
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
        let binding_qual =
          if scrut.sc_owned then "auto& [" else "const auto& ["
        in
        if scrut.sc_flat then
          str binding_qual
          ++ prlist_with_sep (fun () -> str ", ")
               (fun (bname, _ty, _used) -> Id.print bname)
               br.smb_field_bindings
          ++ str "] = " ++ scrut_var_pp ++ str ";"
        else
          str binding_qual
          ++ prlist_with_sep (fun () -> str ", ")
               (fun (bname, _ty, _used) -> Id.print bname)
               br.smb_field_bindings
          ++ str "] = " ++ str (sn ()).get ++ str "<"
          ++ pp_cpp_type false [] br.smb_ctor_type ++ str ">("
          ++ scrut_var_pp ++ str ");"
      | [] ->
        ( match br.smb_var with
        | Some var_id ->
          if scrut.sc_owned then
            str "auto " ++ Id.print var_id
            ++ str " = std::move(" ++ str (sn ()).get ++ str "<"
            ++ pp_cpp_type false [] br.smb_ctor_type ++ str ">("
            ++ scrut_var_pp ++ str "));"
          else
            str "const auto& " ++ Id.print var_id
            ++ str " = " ++ str (sn ()).get ++ str "<"
            ++ pp_cpp_type false [] br.smb_ctor_type ++ str ">("
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
        | [] -> CErrors.anomaly (Pp.str "pp_cpp_stmt Smatch: empty branch list") in
      let binding = pp_block_binding scrut_var_pp br in
      let body_pp = pp_list_stmt (pp_cpp_stmt env args) br.smb_body in
      if binding = mt () then body_pp
      else scrut_binding_pp ++ binding ++ fnl () ++ body_pp
    else
    let pp_branch i br =
      let keyword = if i = 0 then "if" else "} else if" in
      let is_last_no_wild =
        i = n_branches - 1 && default = None && n_branches > 1
      in
      let binding = pp_block_binding scrut_var_pp br in
      let normal_body_pp = pp_list_stmt (pp_cpp_stmt env args) br.smb_body in
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

and pp_custom ?container custom env typ t tyargs cases args _arg_types vl cmds =
  (* Every read of a boxed value the template needs at a concrete type was
     made explicit by {!Cpp_erasure.lower_boxed_reads}; this prints. *)
  let pp ?(followed_by_dot=false) cmd =
    match cmd with
    | CCstring s -> str s
    | CCscrut ->
      ( match t with
      | Some t_expr ->
        let t_printed = pp_cpp_expr env [] t_expr in
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
      ( match List.nth_opt tyargs i with
        | Some ty -> pp_cpp_type false vl ty
        | None -> pp_cpp_type false vl Tany
      )
    | CCelem i ->
      (* Like CCty_arg, but wrap the element in the container's [Boxed Element]
         wrapper when the element recurses through a boxed-element container. *)
      let elem_ty =
        match List.nth_opt tyargs i with Some ty -> ty | None -> Tany
      in
      let base = pp_cpp_type false vl elem_ty in
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
          (* The generator's belief is only worth printing if this file can
             spell it.  A type from a module [Crane Extract Skip Module] left
             out has no declaration to name -- the binder would read
             [IO_axioms::ioE], an identifier nothing introduces -- so the
             honest answer is that the type is not known here, which is what
             [std::any] says.  A template reading this placeholder can then
             treat the two cases alike. *)
          if has_no_cpp_spelling ty then (
            report_unspellable
              (Printf.sprintf "branch %d var %d of %s" i j custom)
              ty;
            writes_obj ();
            str Crane_rt.obj )
          else pp_cpp_type false vl ty
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
let pp_type t = pp_cpp_type false [] t

(* A callable parameter whose constraint was never settled from its body
   ({!Minicpp.settle_constraints}) is printed unconstrained -- a constraint
   guessed from its declared type could name the wrong operands -- and is an
   error under [CRANE_CHECK_IR], since some path skipped the pipeline. *)
let unsettled_callable () =
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then
    CErrors.anomaly
      (Pp.str "Crane: a callable template parameter reached the printer unsettled.")

(** Print a template parameter type keyword (typename or concept constraint). *)
let pp_template_type = function
  | TTtypename -> str "typename"
  | TTtypename_default _ -> str "typename"
  | TTtemplate arity ->
    str "template <"
    ++ prlist_with_sep (fun () -> str ", ") (fun _ -> str "typename")
         (List.init arity Fun.id)
    ++ str "> class"
  | TTfun _ ->
    unsettled_callable ();
    str "typename"
  | TTinvocable _ -> str "typename"
  | TTconcept (concept, _) when class_concept_held_back concept ->
    str "typename"
  | TTconcept (concept, []) -> pp_concept_name_of_ref concept
  | TTconcept (_, _ :: _) ->
    (* Multi-parameter concept: the constraint cannot be written inline
       ([C _tcI0] would apply C to only one argument), so declare the
       parameter as a plain [typename] and attach [requires C<_tcI0, …>]
       via {!pp_requires_of_tparams}. *)
    str "typename"

(** Take and clear the alias templates ({!ctor_alias_decls}) minted since the
    last call, as declarations.

    A struct forward declaration belongs in the header, and the
    implementation file, which includes it, has no use for one.  An alias
    is minted by whichever file writes the use that needs it, and a use in the
    implementation file is reached while the header has already been handed
    over -- so it has to be declared where it was minted.

    Draining is sound only because {!ctor_alias_name_for} names an alias after
    its body rather than after its position in this list: a body minted in both
    files gets one name and two identical declarations, which is legal, while a
    counter would give the second file the first file's names for other
    bodies. *)
let take_ctor_alias_decls ?(select = fun _ -> true) ~is_header () =
  let unemitted l =
    List.filter
      (fun (_, name) ->
        if Hashtbl.mem ctor_alias_emitted name then false
        else (Hashtbl.add ctor_alias_emitted name (); true) )
      l
  in
  let taken, kept = List.partition (fun (_, name) -> select name) !ctor_alias_decls in
  ctor_alias_decls := taken;
  let held_taken, held_kept =
    (* A holder is named by the body of the alias that captured it, not by the
       text that uses the alias, so it comes along with whichever aliases go. *)
    let needed name =
      select name
      || List.exists (fun (body, _) -> mentions_name body name) taken
    in
    List.partition (fun (_, name) -> needed name) !ctor_holder_decls
  in
  if is_header then ctor_holder_decls := held_taken;
  let l =
    List.rev_map
      (fun (body, name) ->
        str "template <typename "
        ++ str ctor_alias_tvar
        ++ str "> using "
        ++ str name
        ++ str " = "
        ++ str body
        ++ str ";")
      (unemitted !ctor_alias_decls)
  in
  ctor_alias_decls := kept;
  (* A holder is a struct, and a struct may be defined once.  An alias above
     may be minted in whichever file writes the use, because repeating a
     [using] with the same definition is legal and a use in the implementation
     file is reached after the header has been handed over; repeating a
     [struct] is not, so the same reasoning gives [vellvm_bench.cpp:5]
     redefining [vellvm_bench.h:173].  The header is the one file everything
     sees, so every holder is declared there and the registry is not drained
     until it has been -- which also keeps a holder's name stable across the
     two passes, since the name is chosen fresh against this list. *)
  let holders =
    if not is_header then []
    else
    List.rev_map
      (fun (body, name) ->
        (* A captured parameter named applied to the alias's own argument is
           a type constructor ([CraneFk]); one named bare is a type
           ([CranePk]), a plain family the declaration deapplied. *)
        let names = identifier_tokens body in
        let rec params i =
          let f = Id.to_string (Generated_name.indexed "F" i)
          and p = Id.to_string (Generated_name.indexed "P" i) in
          if List.mem f names then
            (str "template <typename> class " ++ str f) :: params (i + 1)
          else if List.mem p names then
            (str "typename " ++ str p) :: params (i + 1)
          else []
        in
        str "template <"
        ++ prlist_with_sep (fun () -> str ", ") (fun p -> p) (params 0)
        ++ str "> struct "
        ++ str name
        ++ str " { template <typename "
        ++ str ctor_alias_tvar
        ++ str "> using c = "
        ++ str body
        ++ str "; };" )
      (unemitted !ctor_holder_decls)
  in
  if is_header then ctor_holder_decls := held_kept;
  holders @ l

(** Print a complete template parameter including name and optional default *)
let pp_template_param (tt, id) =
  match tt with
  | TTtypename_default default_ty ->
    str "typename"
    ++ spc ()
    ++ Id.print id
    ++ str " = "
    ++ pp_type default_ty
  | _ -> pp_template_type tt ++ spc () ++ Id.print id

(** [template <...> ] prefix for a declaration, or nothing when the parameter
    list is empty. *)
let pp_template_header = function
  | [] -> mt ()
  | tparams -> str "template <" ++ pp_list pp_template_param tparams ++ str "> "

(** Print a template parameter for a re-declaration: same kind, but without the
    default argument, which C++ allows to appear only once per parameter. *)
let pp_template_param_redecl (tt, id) = pp_template_type tt ++ spc () ++ Id.print id

(** Build a [requires] clause from template parameters that have [TTfun]
    constraints.  Each [TTfun(dom, cod)] with parameter name [F] becomes
    [std::is_invocable_r_v<cod, F &, dom1 &, dom2 &, ...>].  Returns [None]
    when no [TTfun] parameters are present.  In BDE mode, uses
    [bsl::is_invocable_r_v] instead.

    @param tparams  list of [(template_type, id)] pairs from the surrounding
                    template parameter declaration
    @return [Some pp] where [pp] is the full [requires ...] clause, or [None]
            if no [TTfun] constraints are present *)
let pp_requires_of_tparams tparams =
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
            ++ pp_type cod
            ++ str ", "
            ++ operand inv.inv_callable (Id.print id)
            ++ List.fold_left
                 (fun acc (cat, ty) -> acc ++ str ", " ++ operand cat (pp_type ty))
                 (mt ()) inv.inv_args
            ++ str ">"
          in
          Some (prlist_with_sep (fun () -> str " && ") clause invs)
        | TTfun _ ->
          unsettled_callable ();
          None
        | TTconcept (concept, _) when class_concept_held_back concept -> None
        | TTconcept (concept, (_ :: _ as args)) ->
          (* Multi-parameter concept constraint: [C<_tcI0, T1, …>].  The
             constrained parameter [id] is the first concept argument, the
             kept type args follow.  Emitting this as a [requires] clause is
             what enforces the Rocq typeclass interface at the use site
             instead of an unconstrained [typename] (CWE-693 / CWE-345). *)
          Some
            ( pp_concept_name_of_ref concept ++ str "<"
            ++ Id.print id
            ++ List.fold_left
                 (fun acc ty -> acc ++ str ", " ++ pp_type ty)
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
let struct_template_head ~pp_param env tparams cstr =
  match tparams with
  | [] -> mt ()
  | _ ->
    let args = pp_list pp_param tparams in
    let req = pp_requires_of_tparams tparams in
    let cstr_pp = match (req, cstr) with
      | None, None -> mt ()
      | Some r, None -> r ++ fnl ()
      | None, Some c -> pp_cpp_expr env [] c ++ fnl ()
      | Some r, Some c -> r ++ str " && " ++ pp_cpp_expr env [] c ++ fnl ()
    in
    (str "template <" ++ args ++ str ">")
    ++ cstr_pp

(** A forward declaration of a struct defined at namespace scope.

    A module struct can be emitted before an inductive a later module pulled
    up to global scope, so a member declaration may name a type whose
    definition comes further down the header ([static Prod<nat, nat>
    divmod(...)] ahead of [struct Prod]).  A declaration only needs the name
    to have been introduced, so the header's prologue declares them up front.
    Made here, by the function that prints the definition's template head,
    so the two spellings of the parameter list cannot drift apart.

    A constrained template -- a [requires] clause on the struct, or a
    concept-kinded parameter -- names its concept, which need not be declared
    by that prologue, nor anywhere above the struct's first use; its
    declaration goes in front of the first chunk of the file that names the
    struct before defining it ({!Cpp.do_struct_with_decl_tracking}): a
    section-local instance's struct and the file module's struct can each
    name the other, [typename StateV<_tcI0>::state] in a member's signature
    against a call to that member in the instance's body. *)
type forward_declaration = {
  fwd_struct : string;
  fwd_text : Pp.t;
  fwd_constrained : bool;
}

let forward_declaration ~env ~name ~tparams ~cstr =
  let concept_kinded (tt, _) =
    match tt with
    | TTconcept _ -> true
    | _ -> false
  in
  { fwd_struct = Pp.string_of_ppcmds name;
    fwd_text =
      struct_template_head ~pp_param:pp_template_param_redecl env tparams cstr
      ++ str "struct " ++ name ++ str ";";
    fwd_constrained =
      cstr <> None
      || pp_requires_of_tparams tparams <> None
      || List.exists concept_kinded tparams }

(** An opaque declaration of a scoped enum.  A module struct can be emitted
    before an enum a later module pulled up to global scope, so a member
    declaration may name the enum ahead of its definition.  [enum class E;]
    is a complete type -- a scoped enum has a fixed underlying type -- so
    replaying it in the header prologue is enough for those members, and the
    definition still follows in its own place. *)
let enum_forward_declaration name =
  {fwd_struct = Pp.string_of_ppcmds name; fwd_text = str "enum class " ++ name ++ str ";"; fwd_constrained = false}

(** Render a doc comment as [///]-prefixed lines followed by a newline, or
    [mt ()] if no comment is registered for [name].  This is the single lookup
    point used by field, constructor-struct, and enum-value printers.

    @param indent  optional prefix prepended to every line (e.g. ["  "] for
    indented contexts such as enum values).  Defaults to [""]. *)
let pp_doc_comment_for_name = Doc_comments.pp

(** Run [f] in the scope an inductive [r]'s struct opens.  The struct is a
    scope of its own between its module and its members: a constructor's
    struct declared in it hides a name the module declares, so a body that
    reaches the module's [Node] from inside [tree] has to qualify it.  The
    scope is a visibility layer whose path names nothing a reference could
    be declared in, holding the constructors' struct names. *)
let with_struct_scope r f =
  match r with
  | GlobRef.IndRef ((kn, i) as ind) ->
    let ctors =
      List.init (Option.default 0 (Table.get_ind_nb_ctors_opt kn i)) (fun j ->
          Ml_type_util.ctor_struct_id_of_ref (GlobRef.ConstructRef (ind, j + 1)))
    in
    let scope =
      Label.make
        (Printf.sprintf "%sstruct_%s_%d" Common.crane_local_prefix
           (Label.to_string (MutInd.label kn)) i)
    in
    let outer = current_visibility () in
    let mp = ModPath.MPdot (top_visible_mp (), scope) in
    with_visibility (inside ~members:(Id.Set.of_list ctors) mp [] outer) f
  | _ -> f ()

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
let pp_owner_template = function
  | [] -> mt ()
  | tps -> (str "template <" ++ pp_list pp_template_param tps ++ str ">") ++ fnl ()

(** Pretty-print a single MiniCpp struct field as C++ source.

    @param struct_name  the enclosing struct's pretty-printed name, forwarded
                        to constructor and destructor printers that need it
    @param env          name environment for sub-expression pretty-printing *)
let rec pp_cpp_field
    ?(struct_name : Pp.t option) ?(mode = Mm_inline) env = function
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
    ++ (pp_type ty ++ str " " ++ Id.print id ++ str ";")
  | Fvar' (id, ty) ->
    (* A field's name lives in its struct, not in the enclosing namespace, so
       it must not be registered as occupying one: a field named after a type
       the same module refers to would otherwise look like a clash and send
       that type through a duplicate wrapper.  Reads spell the field the same
       way (see [CPPget']). *)
    pp_doc_comment_for_name (Common.pp_global_name Type id)
    ++ (pp_type ty ++ str " " ++ str (Common.pp_global_name Type id)
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
        mf_no_pure;
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
    let body_s = pp_list_stmt (pp_cpp_stmt env []) mf_body in
    let mentioned = output_mentions body_s in
    let params_s =
      pp_list
        (fun (id, ty) ->
          if
            (not (mentioned id))
            && not (String.equal (Id.to_string mf_name) "operator=")
          then pp_type ty
          else pp_type ty ++ str " " ++ Id.print id)
        mf_params
    in
    let template_s =
      match mf_tparams with
      | [] -> mt ()
      | _ ->
        let args = pp_list pp_template_param mf_tparams in
        let req = pp_requires_of_tparams mf_tparams in
        str "template <" ++ args ++ str ">" ++ fnl ()
        ++ ( match req with
           | None -> mt ()
           | Some r -> r ++ fnl () )
    in
    let doc_comment = pp_doc_comment_for_name (Id.to_string mf_name) in
    let qualifier =
      fun_qualifier ~can_constexpr:mf_is_static ~throws:false ~no_pure:mf_no_pure
        mf_ret_type mf_params
    in
    let owner_template_s, qual_s =
      match mode with
      | Mm_defined (qual, owner_tps) ->
        (pp_owner_template owner_tps, qual ++ str "::")
      | Mm_inline | Mm_declared -> (mt (), mt ())
    in
    (* A conversion function has no return type of its own -- its name is the
       type it converts to -- and none of the qualifiers [fun_qualifier]
       computes from a return type apply. *)
    let head =
      h
        ( inline_s
        ++ ( if mf_is_conversion then
               qual_s ++ str "operator " ++ pp_type mf_ret_type
             else
               qualifier ++ static_s ++ pp_type mf_ret_type ++ str " "
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
        str "template <" ++ pp_list pp_template_param fc_tparams ++ str ">"
        ++ fnl ()
    in
    let params_s =
      pp_list (fun (id, ty) -> pp_type ty ++ str " " ++ Id.print id) fc_params
    in
    let init_s =
      match fc_inits with
      | [] -> mt ()
      | _ ->
        str " : "
        ++ pp_list
             (fun (member, expr) ->
               Id.print member ++ str "(" ++ pp_cpp_expr env [] expr ++ str ")" )
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
         ++ pp_list_stmt (pp_cpp_stmt env []) fc_body
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
      ++ pp_list_stmt (pp_cpp_stmt env []) body
      ++ fnl ()
      ++ str "}"
    | Mm_defined (qual, owner_tps) ->
      pp_owner_template owner_tps
      ++ h
           ( (if owner_tps = [] then str "inline " else mt ())
           ++ qual ++ str "::~" ++ sname ++ str "() {" )
      ++ fnl ()
      ++ pp_list_stmt (pp_cpp_stmt env []) body
      ++ fnl ()
      ++ str "}" )
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
             ++ pp_cpp_type false [] ty )
           dfs_selves
      ++ str "> struct " ++ str tmpl ++ str " {" )
    ++ fnl ()
    ++ prlist_with_sep fnl
         (fun (id, ty) -> (pp_cpp_type false [] ty ++ spc () ++ Id.print id ++ str ";"))
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
            ++ pp_list pp_template_param tparams
            ++ str "> " )
      ++ str "using "
      ++ Id.print id
      ++ str " = "
      ++ pp_type ty
      ++ str ";" )
  | Fmember_decl m ->
    pp_cpp_field ?struct_name ~mode:Mm_declared env (field_of_member m)
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

    The accessor was planned before rendering ({!Cpp.plan_accessors}), so that
    call sites append [()] after the template arguments (see {!pp_cpp_expr}).

    @param env      name environment (passed through for sub-expression use)
    @param id       global reference identifying the data member (used for the
                    function name and to register in [template_static_accessors])
    @param ty       C++ type of the data member; [const] modifier is stripped
                    before use inside the function body
    @param expr_pp  already pretty-printed initializer expression *)
let pp_meyers_singleton env id ty expr_pp =
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
    ++ pp_type bare_ty
    ++ str "& "
    ++ pp_global Type id
    ++ str "() {" )
  ++ fnl ()
  ++ str "  static const "
  ++ pp_type bare_ty
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
let nspace_wrapper_name id =
  Table.escape_reserved_struct_name
    ( match id with
    | GlobRef.IndRef _ -> String.capitalize_ascii (str_global Type id)
    | _ -> string_of_ppcmds (pp_global Type id) )

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
let struct_definition_name id =
  let local = is_local_inductive id in
  match struct_spelling ~local id with
  | As_declared -> pp_global Type id
  | Eponymous_record_name | Capitalized -> str (struct_declaration_name ~local id)

(** The name the scoped enum of [r] is defined under. *)
let enum_definition_name r =
  match r with
  | GlobRef.IndRef _ -> pp_inductive_type_name r
  | _ -> pp_global Type r

(** The names of the wrapper structs [d] writes around something other than
    a sole struct merged into them, in the order it writes them: the structs
    another wrapper's declarations can be written into. *)
let rec unmerged_wrappers_written (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> unmerged_wrappers_written inner
  | Namespace (None, decls) -> List.concat_map unmerged_wrappers_written decls
  | Namespace (Some id, members) ->
    let sole_child = match (members :> cpp_decl list) with [Dstruct _] -> true | _ -> false in
    if nspace_merges {dw_ref = id; dw_sole_child = sole_child} then []
    else List.concat_map unmerged_wrappers_written members @ [nspace_wrapper_name id]
  | Decl _ -> []

(** The declarations of the wrapper modules the element being written
    writes into a wrapper struct of the same name, by that name, as planned
    ({!Cpp.file_layout}). *)
let wrapper_members : (string * Pp.t) list ref = ref []

let writing_wrapper_members members f = setting wrapper_members members f

(** The wrapper structs that took a wrapper module's declarations, in the
    order they did, under [CRANE_CHECK_IR]. *)
let absorbed_wrappers : string list ref = ref []

let take_absorbed_wrappers () =
  let l = List.rev !absorbed_wrappers in
  absorbed_wrappers := [];
  l

(** The assertions [d] holds back, in the order it writes them: those that
    a class's concept holds of an instance where the concept is declared
    after the struct being written, because its requirements name the
    struct's own types.  Each is the concept held back, its name, and what
    it is asserted of, which the struct qualifies on the way out. *)
let rec held_back_assertions (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> held_back_assertions inner
  | Namespace (None, decls) -> List.concat_map held_back_assertions decls
  | Namespace (Some id, members) ->
    let sole_child = match (members :> cpp_decl list) with [Dstruct _] -> true | _ -> false in
    if nspace_merges {dw_ref = id; dw_sole_child = sole_child} then []
    else List.concat_map held_back_assertions members
  | Decl (Dstatic_assert (CPPconcept_app (class_ref, subject, tys), None)) when class_concept_held_back class_ref ->
    [ ( HCclass class_ref,
        pp_concept_name_of_ref class_ref,
        pp_global Type subject ++ prlist (fun ty -> str ", " ++ pp_cpp_type false [] ty) tys ) ]
  | Decl _ -> []

(** The forward declarations of the structs and scoped enums [d] defines at
    namespace scope, in the order it defines them: none inside a struct,
    where a member is not nameable before its enclosing struct anyway. *)
let rec forward_declarations env (d : Cpp_erasure.settled) =
  if (!render_ctx).rc_in_struct then []
  else
    match Cpp_erasure.view d with
    | Template (_, _, inner) -> forward_declarations env inner
    | Namespace (None, decls) -> List.concat_map (forward_declarations env) decls
    | Namespace (Some id, members) -> (
      match (members :> cpp_decl list) with
      | [Dstruct {ds_tparams; ds_constraint; _}] when nspace_merges {dw_ref = id; dw_sole_child = true} ->
        [ forward_declaration ~env ~name:(str (nspace_wrapper_name id)) ~tparams:ds_tparams
            ~cstr:ds_constraint ]
      | _ -> [] )
    | Decl (Dstruct {ds_ref; ds_tparams; ds_constraint; _}) ->
      [forward_declaration ~env ~name:(struct_definition_name ds_ref) ~tparams:ds_tparams ~cstr:ds_constraint]
    | Decl (Denum {de_ref; _}) -> [enum_forward_declaration (enum_definition_name de_ref)]
    | Decl _ -> []

(** [pp_initialiser env ty e] prints [e] as the initialiser of something
    declared with type [ty].

    A {!CPPabort} never returns, so the type it should be spelled with comes
    entirely from where it sits; here that is [ty].  Everywhere else the
    expression printer already knows enough. *)
let rec pp_initialiser env ty e =
  match e with
  | CPPabort (msg, _) ->
    writes_standard "stdexcept";
    (* The lambda returns by value, so a top-level [const] on [ty] says
       nothing and [-Wignored-qualifiers] rejects it. *)
    let ret_ty = match ty with Tconst t -> t | t -> t in
    str "([]() -> "
    ++ pp_type ret_ty
    ++ str " { throw "
    ++ str (sn ()).logic_error
    ++ str "(\""
    ++ str (escape_cpp_string msg)
    ++ str "\"); })()"
  | _ -> pp_cpp_expr env [] e

(** Pretty-print a settled MiniCpp declaration as C++ source: every type here
    is spelled the way it will be written out, and the passes that settle a
    declaration ({!Cpp_pipeline.finish}) have already run.

    @param env  name environment for sub-expression and sub-type printers *)
and pp_cpp_decl env (settled : Cpp_erasure.settled) =
  record_file_scope_type (settled :> cpp_decl);
  match Cpp_erasure.view settled with
  | Template (temps, cstr, inner) -> pp_template_decl env temps cstr inner
  | Namespace (None, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl env) decls in
    (str "namespace " ++ str "{") ++ fnl () ++ ds ++ fnl () ++ str "};"
  | Namespace (Some id, members) -> pp_wrapper_nspace env id members
  | Decl d -> pp_leaf_decl env d

(** A template head and the declaration it introduces. *)
and pp_template_decl env temps cstr (inner : Cpp_erasure.settled) =
  match (inner :> cpp_decl) with
  | Dasgn (id, ty, e) when (!render_ctx).rc_in_struct ->
    let args = pp_list pp_template_param temps in
    let expr_pp = pp_initialiser env ty e in
    let req = pp_requires_of_tparams temps in
    let cstr_pp = match (req, cstr) with
      | None, None -> mt ()
      | Some r, None -> r ++ fnl ()
      | None, Some c -> pp_cpp_expr env [] c ++ fnl ()
      | Some r, Some c -> r ++ str " && " ++ pp_cpp_expr env [] c ++ fnl ()
    in
    (str "template <" ++ args ++ str ">")
    ++ cstr_pp
    ++ pp_meyers_singleton env id ty expr_pp
  | decl ->
    (* A default may be given once per parameter.  Which printing gives it is
       decided in the declarations: a definition written after its
       declaration has had its defaults stripped
       ({!Function_entity.definition_after_declaration}). *)
    let args = pp_list pp_template_param temps in
    let req = pp_requires_of_tparams temps in
    let cstr_pp = match (req, cstr) with
      | None, None -> mt ()
      | Some r, None -> r ++ fnl ()
      | None, Some c -> pp_cpp_expr env [] c ++ fnl ()
      | Some r, Some c -> r ++ str " && " ++ pp_cpp_expr env [] c ++ fnl ()
    in
    (str "template <" ++ args ++ str ">")
    ++ cstr_pp
    ++ pp_cpp_decl env inner

(** A namespace-scope wrapper struct around [members], merged with its sole
    struct child where it can be. *)
and pp_wrapper_nspace env id (members : Cpp_erasure.settled list) =
  let decls = (members :> cpp_decl list) in
  let struct_name_str = nspace_wrapper_name id in
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
    let f_s =
      with_render_ctx
        (fun c -> { c with rc_in_struct = true })
        (fun () ->
          with_struct_scope ds_ref (fun () -> pp_cpp_fields_with_vis ~struct_name env fields) )
    in
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
      with_render_ctx
        (fun c -> { c with rc_in_struct = true; rc_in_template = true })
        (fun () ->
          with_struct_scope ds_ref (fun () -> pp_cpp_fields_with_vis ~struct_name env fields) )
    in
    let args = pp_list pp_template_param temps in
    let req = pp_requires_of_tparams temps in
    let cstr_pp = match (req, cstr) with
      | None, None -> mt ()
      | Some r, None -> r ++ fnl ()
      | None, Some c -> pp_cpp_expr env [] c ++ fnl ()
      | Some r, Some c -> r ++ str " && " ++ pp_cpp_expr env [] c ++ fnl ()
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
    let ds =
      with_render_ctx
        (fun c -> { c with rc_in_struct = true })
        (fun () -> pp_list_stmt (pp_cpp_decl env) members)
    in
    let pending_fwd =
      match List.assoc_opt struct_name_str !wrapper_members with
      | Some specs ->
        if Probe.checking () then absorbed_wrappers := struct_name_str :: !absorbed_wrappers;
        fnl () ++ specs
      | None -> mt ()
    in
    (str "struct " ++ str struct_name_str ++ str " {")
    ++ fnl ()
    ++ ds
    ++ pending_fwd
    ++ fnl ()
    ++ str "};" )

(** A declaration with no declaration nested inside it. *)
and pp_leaf_decl env (d : cpp_decl) =
  match d with
  (* Taken apart by {!Cpp_erasure.view}, which hands out their children
     settled. *)
  | Dtemplate _ | Dnspace _ -> assert false
  | Dfun {df_path; df_ret = ret_ty; df_no_pure = no_pure; df_shape = shape} ->
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
    let scope =
      if is_def && not (!render_ctx).rc_in_struct then
        Scope_plan.of_declaration (fst df_path.dp_outer)
      else None
    in
    with_render_ctx (fun c -> {c with rc_scope = scope}) @@ fun () ->
    let pp_fun_name n =
      match n with
      | GlobRef.VarRef v when is_def -> str (Id.to_string v)
      | _ -> pp_global Type n
    in
    let base_name =
      prlist_with_sep
        (fun () -> str "::")
        (fun (n, tys) ->
          match tys with
          | [] -> pp_fun_name n
          | _ -> pp_fun_name n ++ str "<" ++ pp_list pp_type tys ++ str ">" )
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
    let is_struct_member = is_qualified || (!render_ctx).rc_in_struct in
    let is_out_of_struct_def = Option.has_some scope in
    let static_kw =
      if is_struct_member && ((not is_def) || not is_out_of_struct_def) then
        str "static "
      else mt ()
    in
    let params_s, qualifier, tail =
      match shape with
      | Ddef (params, body) ->
        let body_s = pp_list_stmt (pp_cpp_stmt env []) body in
        let mentioned = output_mentions body_s in
        let params_s =
          pp_list
            (fun (id, ty) ->
              if not (mentioned id) then pp_type ty
              else pp_type ty ++ str " " ++ Id.print id)
            (List.rev params)
        in
        let qualifier =
          fun_qualifier
            ~can_constexpr:
              ((!render_ctx).rc_in_struct && not is_out_of_struct_def)
            ~throws:(body_is_throw body) ~no_pure ret_ty params
        in
        (params_s, qualifier, str "{" ++ body_s ++ str "}")
      | Ddecl params ->
        let params_s =
          pp_list
            (fun (id, ty) ->
              match id with
              | Some id -> pp_type ty ++ str " " ++ Id.print id
              | None -> pp_type ty )
            (List.rev params)
        in
        (params_s, mt (), str ";")
    in
    h
      ( qualifier
      ++ static_kw
      ++ pp_type ret_ty
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
    let struct_name = struct_definition_name id in
    record_file_scope_name struct_name;
    if (!render_ctx).rc_in_struct then printed_nested_struct (Pp.string_of_ppcmds struct_name) (NSref id);
    let f_s =
      with_struct_scope id (fun () ->
          match tparams with
          | [] -> pp_cpp_fields_with_vis ~struct_name env fields
          | _ ->
            with_render_ctx
              (fun c -> { c with rc_in_template = true })
              (fun () -> pp_cpp_fields_with_vis ~struct_name env fields) )
    in
    let tmpl = struct_template_head ~pp_param:pp_template_param env tparams cstr in
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
  | Dasgn (id, ty, e) ->
    let expr_pp = pp_initialiser env ty e in
    if (!render_ctx).rc_in_template
       || ((!render_ctx).rc_in_struct
           && Common.get_force_cross_file_qualification ()) then
      (* In template context or separate-extraction struct: use Meyers
         singleton so that module-type-parameter references via L::val()
         work for both template and non-template implementing modules. *)
      pp_meyers_singleton env id ty expr_pp
    else
      (* A value written as a literal of a literal type is a constant
         expression: [constexpr] says so, and lets it stand in a
         [static_assert] or a template argument.  A mapped constant
         constructor of such a type ([true]) is that type's literal. *)
      let literal =
        (match e with
         | CPPnumeral _ | CPPuint _ | CPPint _ | CPPbool _ | CPPenum_val _ -> true
         | CPPglob ((GlobRef.ConstructRef _ as r), [], _) -> Table.is_custom r
         | _ -> false)
        && is_constexpr_type ty
      in
      let ty = match ty with Tconst t when literal -> t | t -> t in
      let static_kw =
        match ((!render_ctx).rc_in_struct, literal) with
        | true, true -> str "static constexpr "
        | true, false -> str "static inline "
        | false, true -> str "inline constexpr "
        | false, false -> mt ()
      in
      let needs_iife =
        (!render_ctx).rc_in_struct && expr_contains_capturing_lambda e
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
        ++ pp_type ty
        ++ str " "
        ++ pp_global Type id
        ++ str " = "
        ++ wrapped_expr
        ++ str ";" )
  | Dconcept (id, cstr) ->
    h
      ( str "concept "
      ++ pp_concept_name_of_ref id
      ++ str " = "
      ++ pp_cpp_expr env [] cstr
      ++ str ";" )
  | Dusing u ->
    (* The template parameter names are also the scope the right-hand side's
       type variables are read in: a parameterised alias names them once. *)
    let vl = List.map snd u.du_tparams in
    let def =
      match u.du_rhs with
      | None -> mt ()
      | Some ty -> str " =" ++ spc () ++ pp_cpp_type false vl ty
    in
    let note =
      match u.du_note with None -> mt () | Some s -> str (" /* " ^ s ^ " */")
    in
    ( pp_template_header u.du_tparams
      ++ str "using "
      ++ pp_global Type u.du_name
      ++ def
      ++ note
      ++ str ";" )
  | Dstruct_fwd (tparams, r) ->
    (pp_template_header tparams ++ str "struct " ++ pp_global Type r ++ str ";")
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
        let own = str_global Type dm_owner in
        (own, nspace_wrapper_name w.dw_ref ^ "::" ^ own)
      | _ ->
        let own = String.capitalize_ascii (str_global Type dm_owner) in
        (own, own)
    in
    let sname = str sname in
    let qual =
      match dm_tparams with
      | [] -> sname
      | tps ->
        sname ++ str "<" ++ pp_list (fun (_, id) -> Id.print id) tps ++ str ">"
    in
    with_render_ctx
      (fun c -> {c with rc_in_template = c.rc_in_template || dm_tparams <> []})
      (fun () ->
        with_struct_scope dm_owner (fun () ->
            pp_cpp_field ~struct_name:(str own_name)
              ~mode:(Mm_defined (qual, dm_tparams))
              env (field_of_member dm_field) ) )
  | Dfields ds ->
    let struct_name =
      str (String.capitalize_ascii (str_global Type ds.ds_ref))
    in
    with_render_ctx
      (fun c ->
        { c with
          rc_in_struct = true;
          rc_in_template = c.rc_in_template || ds.ds_tparams <> [] } )
      (fun () ->
        with_struct_scope ds.ds_ref (fun () ->
            pp_cpp_fields_with_vis ~struct_name env ds.ds_fields ) )
  | Dstatic_assert (CPPconcept_app (class_ref, _, _), None) when class_concept_held_back class_ref ->
    (* The concept is declared after the struct being rendered, because its
       requirements name the struct's own types.  The assertion goes with it
       ({!held_back_assertions}). *)
    mt ()
  | Dstatic_assert (e, so) ->
    ( match so with
    | None -> (str "static_assert(" ++ pp_cpp_expr env [] e ++ str ");")
    | Some s ->
      h
        ( str "static_assert("
        ++ pp_cpp_expr env [] e
        ++ str ", \""
        ++ str (escape_cpp_string s)
        ++ str "\");" ) )
  | Denum {de_ref = name; de_ctors = ctors; de_ctor_rocq_names = rocq_names; _}
    ->
    let struct_name = enum_definition_name name in
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
    if (!render_ctx).rc_in_struct then printed_nested_struct (Pp.string_of_ppcmds struct_name) (NSref name);
    str "enum class "
    ++ struct_name
    ++ str " {"
    ++ fnl ()
    ++ ctors_s
    ++ fnl ()
    ++ str "};"

(** The break between two declaration groups.  It is a break hint, not a
    forced newline, so the vertical box the whole file is printed in
    ([Extract_env]) decides where it falls; clang-format keeps the blank lines
    it leaves. *)
let cut2 () = brk (0, -100000) ++ brk (0, 0)
