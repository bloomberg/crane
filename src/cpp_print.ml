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
    AST nodes into Pp.t values representing C++ source code, and the Meyers
    singleton helper. *)

open Pp
open Names
open Table
open Common
open Minicpp
open Cpp_state
open Cpp_names

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

(** {2 Pretty-printing C++ syntax.} *)

(** A lambda's capture as decided ({!Cpp_erasure.decide_captures}); a
    variable whose last use is the capture moves into it. *)
let pp_capture = function
  | Captures_nothing -> str "[]"
  | By_reference -> str "[&]"
  | By_copy {this; moved} ->
    if moved <> [] then writes_standard "utility";
    let moves = List.map (fun x -> str ", " ++ Id.print x ++ str " = std::move(" ++ Id.print x ++ str ")") moved in
    str "[=" ++ (if this then str ", this" else mt ()) ++ seq moves ++ str "]"

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

(* A piece of the type mapping [r]'s instantiated text, hole [i] written
   [arg i]: an element hole bare or inside the wrapper decided for it. *)
let pp_type_piece r arg = function
  | Fp_text s -> str s
  | Fp_type i | Fp_element (i, None) -> arg i
  | Fp_element (i, Some wrapper) ->
    let element = Pp.string_of_ppcmds (arg i) in
    str (String.concat "" (List.map (function Wp_text s -> s | Wp_element -> element) wrapper))
  | Fp_value _ | Fp_yields | Fp_result | Fp_statement_end ->
    CErrors.anomaly Pp.(str "the type mapping " ++ GlobRef.print r ++ str " names a value")

let pp_type_pieces r pieces arg =
  let arg i =
    match arg i with
    | Some pp -> pp
    | None -> CErrors.anomaly Pp.(str "a type argument the mapping " ++ GlobRef.print r ++ str " names was not supplied")
  in
  prlist (pp_type_piece r arg) pieces

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
  | Dusing u -> Some (str (declared_name ctx Type u.du_name))
  | Dnspace (Some w, _) -> Some (str (String.capitalize_ascii (declared_name ctx Type w.nw_ref)))
  | _ -> None

let note_file_scope_type ctx d = Option.iter (note_file_scope_name ctx) (decl_type_name ctx d)

(** The C++ token an {!Minicpp.obj_access} prints as. *)
let pp_obj_access = function Adot -> "." | Aarrow -> "->"

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
type ctor_alias = Cpp_state.ctor_alias = {
  ca_base : string;  (** What its name is made from. *)
  ca_holder : Cpp_state.holder_parameter list option;  (** A holder's parameters, where it is one. *)
  ca_declared : Cpp_ast.declared_in;  (** Where it is declared ({!Cpp_leaf_plan.ctor_alias_declared}). *)
  ca_body : string;
      (** The type it abbreviates, as written where it is declared, with the
          sentinel where the template's own parameter goes. *)
  ca_type : cpp_type;  (** That type. *)
  ca_vars : Id.t list;  (** The names of the variables it names by index. *)
  ca_uses : tyctor_use list;  (** How its body writes the type constructors in it. *)
}

(** Under [CRANE_CHECK_IR], the templates the file being written spells
    where nothing collects them: what {!check_ctor_alias_plan} compares with
    the plan. *)
let ctor_aliases_spelled : ctor_alias list ref = ref []

(** [a] spelled at [ctx]: collected where the position collects
    ({!Cpp_state.render_ctx.rc_aliases}), and otherwise, under
    [CRANE_CHECK_IR], noted as spelled in the file. *)
let note_ctor_alias_spelled ctx a =
  let add spelled = if not (List.mem a !spelled) then spelled := !spelled @ [a] in
  match ctx.rc_aliases with
  | Some found -> add found
  | None -> if Probe.checking () then add ctor_aliases_spelled

let start_ctor_alias_census () = ctor_aliases_spelled := []

(** The templates the file being written spelled where nothing collected
    them, since the census started; the census starts again. *)
let take_ctor_aliases_spelled () =
  let spelled = !ctor_aliases_spelled in
  ctor_aliases_spelled := [];
  spelled

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
  let kind = if Option.has_some a.ca_holder then "_tch_" else "_tc_" in
  a.ca_base ^ kind ^ String.sub (Digest.to_hex (Digest.string a.ca_body)) 0 16

(* The primitive integer type, found by what it is registered as: its short
   name may be a user's own [int] where the extraction runs. *)
let uint63_type () =
  let int63 = "num.int63.type" in
  if Rocqlib.has_ref int63 then Some (Rocqlib.lib_ref int63) else None

(** The constructor a type constructor position writes: an applied type
    there is the eta-expansion of the constructor, whose head is what the
    position wants. *)
let tyctor_constructor = function Tapply (head, _) -> head | t -> t

(** [str_of] up to its first template argument list. *)
let cut_at_argument_list str_of =
  match String.index_opt str_of '<' with
  | Some i -> String.sub str_of 0 i
  | None -> str_of

(* The text an instantiated mapping was instantiated from, each hole the
   placeholder it was written as. *)
let foreign_text fr =
  String.concat ""
    (List.map
       (function
         | Fp_text s -> s
         | Fp_type i -> Printf.sprintf "%%t%d" i
         | Fp_element (i, _) -> Printf.sprintf "%%elem%d" i
         | Fp_value i -> Printf.sprintf "%%a%d" i
         | Fp_yields -> "%ret"
         | Fp_result -> "%result"
         | Fp_statement_end -> ";")
       fr.fr_pieces)

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
    [Tpromoted]), or [None] where it is written bare.

    A definition written outside its struct ([Owner::f]) qualifies the plain
    names in its signature with [Owner::], which is right for a member and
    wrong for anything else.  An erased type-class field is a case of
    "anything else": the class is at file scope, so its erased face is a
    file-scope [using iptr = std::any;], and some unrelated struct's hoisted
    body must resolve [iptr] to that alias rather than claim it as a member it
    never declared.  The position says which names its file declares at file
    scope ({!Cpp_state.out_of_line}).

    Those names only {i withhold} the qualifier, and a file-scope name that
    a struct also declares as a member still resolves to the member, because
    the body of an out-of-line definition is inside its class's scope. *)
let member_scopes (ctx : render_ctx) id =
  match ctx.rc_scope with
  | Some {ol_scope; ol_file_scope_types} when (not ctx.rc_in_struct) && not (CString.Set.mem (Id.to_string id) ol_file_scope_types) ->
    Some (List.map (fun s -> Cpp_name.Class s) ol_scope.Scope_plan.qualifier)
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

(** [h] written with template arguments after it if [applied]. *)
let written_head ~applied (h : Cpp_resolution.head) =
  {outer = h.outer; head = h.head; typename = h.typename; template_keyword = applied && h.templated}

(** The head of the type [Tglob (r, tys, _)] that no custom mapping inlines,
    [applied] when [tys] is not empty. *)
let glob_head ctx r ~applied = written_head ~applied (Cpp_names.type_head ctx Glob_head r)

(** The head of the inductive type [Tnamespace (r, Tglob (r, args, _))],
    [applied] when [args] is not empty. *)
let inductive_head ctx r ~applied = written_head ~applied (Cpp_names.type_head ctx Inductive_head r)

(** [h] written, the [typename] it asks for only if [lead]. *)
let pp_written_head ~lead h =
  (if lead && h.typename then str "typename " else mt ())
  ++ Cpp_name.pp_scopes h.outer
  ++ Cpp_name.pp ~template_keyword:h.template_keyword h.head

(** The spelling of an external type's name: the configured library's vector
    for the standard one. *)
let external_type_name id_s =
  if String.equal id_s "std::vector" && (sn ()).ns <> "std" then "bsl::vector" else id_s

(** Pretty-print a MiniCpp type as C++ source text.

    @param par  whether to parenthesize (for precedence in function types)
    @param vl   type variable names for de Bruijn index lookup

    A {!Minicpp.Tpromoted} reaching the printer is one no resolution map
    claimed, so it is rendered as a member of the enclosing struct: the bare
    name inside a struct body, [StructName::id] outside one. *)
let rec pp_cpp_type ?(lead = true) ctx par vl t =
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
        end else if String.equal id_s Crane_rt.shared_box || String.equal id_s Crane_rt.shared_or then begin
          writes (Table.Runtime Crane_rt.shared_variant_header);
          id_s
        end else if String.equal id_s Crane_rt.rc then begin
          (* rc.h transitively includes arena.h. *)
          writes_standard "memory";
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
    | Tglob (r, tys, _) ->
      ( match Cpp_names.inline_custom_text ctx r with
      (* A mapped type is instantiated before it is printed
         ({!Cpp_erasure.instantiate_foreign}, {!Cpp_erasure.instantiate_type}
         for one written outside a declaration), and one mapped to nothing
         has no spelling to print: the [Tapply] arm writes such a head's
         arguments, and anywhere else it is refused at the seam. *)
      | Some "" ->
        CErrors.anomaly Pp.(str "a type mapped to nothing reached the printer: " ++ GlobRef.print r)
      | Some _ ->
        CErrors.anomaly Pp.(str "a mapped type reached the printer uninstantiated: " ++ GlobRef.print r)
      | None ->
        pp_written_head ~lead (glob_head ctx r ~applied:(tys <> []))
        ++ (match tys with [] -> mt () | l -> str "<" ++ pp_list (pp_rec false) l ++ str ">") )
    | Tforeign fr -> pp_foreign ctx (empty_env ()) vl fr
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
        ++ Cpp_name.pp_qualifier (fun s -> Cpp_name.Class s) (Cpp_names.inductive_scope ctx r)
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
      (* A non-dependent alias template: the head names it outright.  A head
         with no name -- a constructor [Crane Extract Skip] removed, written
         as nothing, and nothing followed by [<args>] is a syntax error
         ([crane_event_as<<typename I::PROV>>]) -- was replaced by its
         argument at the seam ({!Cpp_erasure.instantiate_foreign}). *)
      if Probe.checking () then begin
        match head with
        | Tglob (r, _, _) when Ml_type_util.ref_has_no_cpp_name r ->
          CErrors.anomaly (Pp.str "pp_cpp_type: a nameless constructor applied, not removed at the seam")
        | _ -> ()
      end;
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
      ++ head_pp ++ str "<" ++ pp_list (pp_rec false) args ++ str ">"
    | Tvariant (Inline_variant, tys) ->
      writes_variant ();
      cpp_angle (sn ()).variant (pp_list (pp_rec false) tys)
    | Tvariant (Shared_variant, tys) ->
      writes (Table.Runtime Crane_rt.shared_variant_header);
      cpp_angle Crane_rt.shared_variant (pp_list (pp_rec false) tys)
    (* The slot a pointer is held in was written down at the seam
       ({!Cpp_erasure.lower_pointer_slots}): what is left is a pointer -- to
       an inductive only a functor's instantiation knows the representation
       of, the pointer [shared_or_t] is given as its alternative. *)
    | Tshared_ptr t ->
      if Probe.checking () && Pointer_slot.of_pointee t = Pointer_slot.Shared then
        CErrors.anomaly (Pp.str "pp_cpp_type: a pointer's slot not chosen (Cpp_erasure.lower_pointer_slots)");
      writes_standard "memory";
      cpp_angle (sn ()).shared_ptr (pp_rec false t)
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
    match tyctor_written ctx vl t with
    | Some (alias, args) ->
      note_ctor_alias_spelled ctx alias;
      let name = ctor_alias_name alias in
      if Option.has_some alias.ca_holder then (str (name ^ "<" ^ String.concat ", " args ^ ">::template c"), true)
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
      | Tglob (r, _ :: _, _) -> (pp_rec false (Tglob (r, [], [])), false)
      | Tforeign ({fr_types = _ :: _; _} as fr) ->
        let lead = match fr.fr_pieces with Fp_text lit :: _ -> lit | _ -> foreign_text fr in
        (str (cut_at_argument_list lead), false)
      | _ -> (str (cut_at_argument_list (Pp.string_of_ppcmds (pp_rec false t))), false) )
  in
  (pp_rec ~lead par t)

(** How the type constructor [t] (the constructor of the template template
    argument written), naming the variables [vl] by index, is written at
    [ctx]: as the plan of the leaf being printed says, or as planning, which
    is spelling it, decides ({!Cpp_state.tyctor_plan}).  The printer decides
    none: a synthesised template's body is written where the template is
    declared, which only planning renders.  Under [CRANE_CHECK_IR] a
    constructor planning notes twice must be decided alike. *)
and tyctor_written ctx vl t =
  let same u = compare u.tu_constructor t = 0 && u.tu_vars = vl in
  let unplanned what =
    CErrors.anomaly
      Pp.(str "Crane: the type constructor " ++ pp_cpp_type {ctx with rc_tyctors = Planned []} false vl t
          ++ str what)
  in
  match ctx.rc_tyctors with
  | Unplanned -> unplanned " is written where nothing plans how."
  | Deciding {decide; noted} ->
    let alias = decide ctx vl t in
    ( match List.find_opt same !noted with
    | None -> noted := !noted @ [{tu_constructor = t; tu_vars = vl; tu_alias = alias}]
    | Some u ->
      if Probe.checking () && compare u.tu_alias alias <> 0 then
        Probe.violation "constructor alias uses"
          Pp.(str "a type constructor is decided twice, otherwise the second time, where one declaration writes it") );
    alias
  | Planned uses -> (
    match List.find_opt same uses with
    | Some u -> u.tu_alias
    | None -> unplanned " is written by a declaration whose plan does not say how." )

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
  let apply st = pp_apply_cpp st args in
  match t with
  | CPPvar id -> Id.print id
  | CPPforeign (Foreign_block capture, fr) ->
    let ret_ty = Pp.string_of_ppcmds (pp_cpp_type ctx false [] (Option.default Tauto fr.fr_yields)) in
    let result = "_r" in
    let stmts = pp_block_statements ctx env fr ~result in
    pp_capture capture ++ str ("() -> " ^ ret_ty ^ " {")
    ++ fnl ()
    ++ str ("  " ^ ret_ty ^ " " ^ result ^ ";")
    ++ fnl ()
    ++ str (String.concat "\n" (List.map (fun s -> "  " ^ s) stmts))
    ++ fnl ()
    ++ str ("  return " ^ result ^ ";")
    ++ fnl ()
    ++ str "}()"
  | CPPforeign ((Foreign_constant | Foreign_call), fr) -> pp_foreign ctx env [] fr
  | CPPforeign (Foreign_statements, fr) ->
    CErrors.anomaly Pp.(str "a block's statements written other than as the declaration they assign: " ++ GlobRef.print fr.fr_custom)
  | CPPglob (x, _, Some {ci_inline = Some _; _}) -> uninstantiated_mapping x
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
    ++ pp_member_name ctx (Id.of_string (short_name ctx Term mv_method)) mv_type_args
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
        let struct_name = short_name ctx Type record_ref in
        let func_name = short_name ctx Term x in
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
        let struct_name = short_name ctx Type record_ref in
        let func_name = short_name ctx Term x in
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
    Cpp_name.pp_qualifier (fun s -> Cpp_name.Class s) (Cpp_names.inductive_scope ctx r) ++ pp_cpp_expr ctx env args t
  (* A callee's text was instantiated as the call's callee, and a template's
     or a block's as the whole call ({!Cpp_erasure.instantiate_foreign}). *)
  | CPPfun_call (_, CPPglob (n, _, Some {ci_inline = Some _; _}), _) -> uninstantiated_mapping n
  | CPPmethod_call {mc_method; mc_access; mc_receiver; mc_type_args; mc_args} ->
    pp_cpp_expr ctx env args mc_receiver
    ++ str (pp_obj_access mc_access)
    ++ pp_member_name ctx (Id.of_string (short_name ctx Term mc_method)) mc_type_args
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
      _ } ->
    let params = to_reversed params in
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
      ( match capture with
      | Written w -> pp_capture w
      | Immediate | Closure -> CErrors.anomaly (Pp.str "a lambda whose capture is not written down reached the printer") )
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
  | CPPalloc (Alloc_heap, t) ->
    writes_standard "memory";
    cpp_angle (sn ()).make_shared (pp_cpp_type ctx false [] t)
  | CPPalloc (Alloc_reusing, t) ->
    (* Perceus reuse factory; only emitted under NonAtomicRc (crane::rc). *)
    cpp_angle Crane_rt.make_rc_reusing (pp_cpp_type ctx false [] t)
  | CPPalloc (Alloc_arena_scoped, t) ->
    (* Runtime scoped-arena factory: the arena-aware form of make_shared/make_rc
       for the current pointer flavor.  Falls back to a plain heap allocation at
       runtime whenever no arena scope is open at the call site.  A unit of
       non-atomic pointers has its pointer's factory instead, chosen at the
       seam ({!Cpp_erasure.lower_pointer_slots}). *)
    ( if Probe.checking () then
        if Table.non_atomic_rc () then
          CErrors.anomaly (Pp.str "pp_cpp_expr: an arena allocation of a non-atomic pointer reached the printer") );
    let inner = pp_cpp_type ctx false [] t in
    if Table.std_lib () = "BDE" then
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
      | GlobRef.IndRef _ when is_eponymous_record_cached id -> inductive_value ctx id
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
    let field_name = str (short_name ctx Type id) in
    ( match e with
    | CPPderef CPPthis -> str "this->" ++ field_name
    | CPPderef _ | CPPraw _ ->
      str "(" ++ pp_cpp_expr ctx env args e ++ str ")." ++ field_name
    | _ -> pp_cpp_expr ctx env args e ++ str "." ++ field_name )
  | CPPstring s -> str ("\"" ^ escape_cpp_string (Pstring.to_string s) ^ "\"")
  | CPPparray (elems, _) ->
    str "{" ++ pp_list (pp_cpp_expr ctx env args) (Array.to_list elems) ++ str "}"
  | CPPuint x ->
    (* Spelled through the mapping of the primitive type. *)
    let s = Uint63.to_string x in
    let mapped = Option.bind (uint63_type ()) (Cpp_names.inline_custom_text ctx) in
    ( match mapped with
    | Some "int64_t" -> str ("INT64_C(" ^ s ^ ")")
    | Some cpp_type -> str (cpp_type ^ "(" ^ s ^ ")")
    | None -> str s )
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
  (* A named global qualifying a member in value position was spelled as the
     value it names at the seam ({!Cpp_erasure.lower_qualifiers}): what is
     left is a type, written without [typename], since a member follows. *)
  | CPPqualified_t (Tglob (_, _, []), _) ->
    CErrors.anomaly (Pp.str "pp_cpp_expr: a type qualifier in value position not lowered (Cpp_erasure.lower_qualifiers)")
  | CPPqualified_t (ty, id) ->
    pp_cpp_type ~lead:false ctx false [] ty ++ str "::" ++ Id.print id
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
    let full_name = enum_name_at ctx (global_name ctx Type ind) ind in
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
  | CPPnumeral (r, n) ->
    Common.writes_custom r;
    str n.nl_text
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
  | CPPsuspend _ ->
    CErrors.anomaly (Pp.str "pp_cpp_expr: a suspension not lowered (Cpp_erasure.lower_qualifiers)")
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
  (* Whether the target boxes its elements was decided at the seam
     ({!Cpp_erasure.instantiate_foreign}). *)
  | CPPcontainer_cast (ty, e, _) ->
    writes Table.erase_fn_header;
    str Crane_rt.container_cast ++ str "<"
    ++ pp_cpp_type ctx false [] ty
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
  (* The block assigns the variable declared in front of it. *)
  | Sasgn (id, Declare (ty, _), CPPforeign (Foreign_statements, fr)) ->
    let decl = pp_cpp_type ctx false [] ty ++ str " " ++ Id.print id ++ str ";" in
    prlist_with_sep fnl (fun x -> x)
      (decl :: List.map str (pp_block_statements ctx env fr ~result:(Pp.string_of_ppcmds (Id.print id))))
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
      let n = (Cpp_names.type_head ctx Glob_head ind).head in
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
  | Sblock_custom (r, _, _, _, _, _, _) -> uninstantiated_mapping r
  | Scustom_case (typ, t, tyargs, cases, cmatch) ->
    (* Scrutinee caching (auto _cs = expr;) is handled during translation
       in gen_custom_cpp_case, which prepends an Sasgn before this node
       when the template uses %scrut more than once with a non-trivial
       scrutinee.  The printer writes the pieces. *)
    Common.writes_custom cmatch.cm_inductive;
    let pieces = match cmatch.cm_pieces with Some p -> p | None -> uninstantiated_mapping cmatch.cm_inductive in
    let unbound what = CErrors.anomaly Pp.(str ("Custom syntax: unbound " ^ what ^ " in the match of ") ++ GlobRef.print cmatch.cm_inductive) in
    let branch i = match List.nth_opt cases i with Some b -> b | None -> unbound "branch" in
    let binder i j = match List.nth_opt (let ps, _, _ = branch i in ps) j with Some p -> p | None -> unbound "binder" in
    let piece = function
      | Mp_text s -> str s
      | Mp_scrutinee {parenthesised} ->
        let printed = pp_cpp_expr ctx env [] t in
        ( match t with
        | CPPstring _ -> string_object printed
        (* A scrutinee carrying a prefix pointer operator binds looser than
           whatever the template appends: the option template's
           [%scrut.has_value()] applied to a recursive occurrence stored
           behind a smart pointer, written [*a1], came out as
           [*a1.has_value()].  Only the pointer operators need this: they are
           the ones a template can follow with a member access; the logical
           and arithmetic prefixes already bind tighter than anything a
           template appends. *)
        | _ ->
          check_leading_pointer_operator t printed;
          if parenthesised then surround printed else printed )
      | Mp_matched_type -> pp_cpp_type ctx false [] typ
      | Mp_type_arg i -> (
        (* Every type argument the text names was supplied at the seam
           ({!Cpp_erasure.supply_template_args}). *)
        match List.nth_opt tyargs i with Some ty -> pp_cpp_type ctx false [] ty | None -> unbound "type argument" )
      | Mp_branch i ->
        let _, _, ss = branch i in
        pp_list_stmt (pp_cpp_stmt ctx env []) ss
      | Mp_binder (i, j) -> Id.print (binder i j).cp_name
      (* Spellable: one that is not was materialised at the seam
         ({!Cpp_erasure.materialise}). *)
      | Mp_binder_type (i, j) -> pp_cpp_type ctx false [] (binder i j).cp_type
    in
    List.fold_left (fun acc p -> acc ++ piece p) (mt ()) pieces
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

       A computed scrutinee was declared, named, in front of the match at
       the seam ({!Cpp_erasure.name_scrutinees}): what is read here is a
       local or the receiver.

       The last explicit branch before [None] default (= exhaustive match
       without wildcard) uses plain [else] — the discriminant check is
       redundant since Rocq guarantees exhaustiveness.

       Single-constructor exhaustive matches (one branch, no wildcard)
       emit just the binding + body inline — no if/else needed. *)
    let n_branches = List.length branches in
    (* Helper: [std::holds_alternative<Ctor>(scrut)]. *)
    let pp_holds scrut_var_pp br =
      str (sn ()).holds_alternative ++ str "<"
      ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
      ++ Lazy.force scrut_var_pp ++ str ")"
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
          ++ str "] = " ++ Lazy.force scrut_var_pp ++ str ";"
        else
          str binding_qual
          ++ prlist_with_sep (fun () -> str ", ")
               (fun fb -> Id.print fb.fb_name)
               br.smb_field_bindings
          ++ str "] = " ++ str (sn ()).get ++ str "<"
          ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
          ++ Lazy.force scrut_var_pp ++ str ");"
      | [] ->
        ( match br.smb_var with
        | Some var_id ->
          if scrut.sc_owned then begin
            writes_standard "utility";
            str "auto " ++ Id.print var_id
            ++ str " = std::move(" ++ str (sn ()).get ++ str "<"
            ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
            ++ Lazy.force scrut_var_pp ++ str "));"
          end
          else
            str "const auto& " ++ Id.print var_id
            ++ str " = " ++ str (sn ()).get ++ str "<"
            ++ pp_cpp_type ctx false [] br.smb_ctor_type ++ str ">("
            ++ Lazy.force scrut_var_pp ++ str ");"
        | None -> mt () )
    in
    (* The scrutinee object under the variant accessor: pointer
       [CPPaccess_call (Aarrow, obj, "v", [])] ([obj->v()]) or value
       [CPPfun_call (CPPaccess (Adot, obj, "v"), [])] ([obj.v()]). *)
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
    let unnamed () =
      CErrors.anomaly (Pp.str "pp_cpp_stmt: a match reads a scrutinee no local holds (Cpp_erasure.name_scrutinees)")
    in
    (* Forced only where it is written: a match of one constructor that
       binds nothing writes no scrutinee, and none was named for it. *)
    let scrut_var_pp =
      lazy
      ( match scrut_obj_opt with
      | Some (CPPvar id) -> str (v_access (Id.to_string id))
      | Some CPPthis | Some (CPPderef CPPthis) -> str (if is_owned then "this->v_mut()" else "this->v()")
      | Some _ -> unnamed ()
      | None -> (
        match first_scrut with
        | CPPvar id -> str (Id.to_string id)
        | CPPderef CPPthis -> str "*this"
        | _ -> unnamed () ) )
    in
    if n_branches = 1 && default = None then
      (* Single-constructor exhaustive match: emit binding + body inline.
         No if/else needed. *)
      let br = match branches with br :: _ -> br
        | [] -> CErrors.anomaly (Pp.str "pp_cpp_stmt ctx Smatch: empty branch list") in
      let binding = pp_block_binding scrut_var_pp br in
      let body_pp = pp_list_stmt (pp_cpp_stmt ctx env args) br.smb_body in
      if binding = mt () then body_pp
      else binding ++ fnl () ++ body_pp
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
      prlist_with_sep fnl (fun (i, br) -> pp_branch i br)
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

(* A block's statements, each written on its own with the semicolon that
   ends it, its [%result] spelled [result]. *)
and pp_block_statements ctx env fr ~result =
  let rec split current = function
    | [] -> if current = [] then [] else [List.rev current]
    | Fp_statement_end :: rest -> List.rev current :: split [] rest
    | p :: rest -> split (p :: current) rest
  in
  List.map
    (fun pieces ->
      String.trim (Pp.string_of_ppcmds (pp_foreign ctx env [] ~result {fr with fr_pieces = pieces})) ^ ";")
    (split [] fr.fr_pieces)

(* A value argument spliced into a mapping's text: a string literal as the
   [std::string] it stands for. *)
and pp_spliced ctx env ~followed_by_dot arg_expr =
  let arg = pp_cpp_expr ctx env [] arg_expr in
  let arg =
    match arg_expr with
    | CPPstring _ -> string_object arg
    | _ -> arg
  in
  (* Parenthesize compound expressions that would bind incorrectly
     when followed by member access (.c_str() etc.) in templates. *)
  (* A compound expression, a mapping's call, or one written with a leading
     prefix pointer operator binds looser than the member access the text
     appends: [%a0.first] applied to a scrutinee written [*a0] came out as
     [*a0.first], the [.first] attaching to the pointer rather than the
     pointee.  See [CCscrut] for why only [*] and [&] need it. *)
  if followed_by_dot then begin
    check_leading_pointer_operator arg_expr arg;
    if Minicpp.spliced_in_parentheses arg_expr then str "(" ++ arg ++ str ")" else arg
  end
  else arg

(* Under [CRANE_CHECK_IR]: [e], written [printed], has a leading prefix
   pointer operator exactly where the tree says so
   ({!Minicpp.written_with_leading_pointer_operator}). *)
and check_leading_pointer_operator e printed =
  if Probe.checking () then
    let s = Pp.string_of_ppcmds printed in
    let rendered = String.length s > 0 && (s.[0] = '*' || s.[0] = '&') in
    if rendered <> Minicpp.written_with_leading_pointer_operator e then
      Probe.violation "leading pointer operator"
        Pp.(str "the expression written " ++ str s ++ str (if rendered then " begins" else " does not begin")
            ++ str " with a prefix pointer operator, which its tree says it "
            ++ str (if rendered then "does not" else "does"))

(* An instantiated mapping: its pieces in order, a type hole past the
   arguments the use supplies written erased; a block's [%result] spelled
   [result]. *)
and pp_foreign ?result ctx env vl fr =
  Common.writes_custom fr.fr_custom;
  let arg i = pp_cpp_type ctx false vl (Option.default Tany (List.nth_opt fr.fr_types i)) in
  let piece ~followed_by_dot = function
    | (Fp_text _ | Fp_type _ | Fp_element _) as p -> pp_type_piece fr.fr_custom arg p
    | Fp_yields -> (
      match fr.fr_yields with
      | Some ty -> str (Pp.string_of_ppcmds (pp_cpp_type ctx false [] ty))
      | None -> CErrors.anomaly Pp.(str "Custom syntax: %ret with no type the call yields in " ++ GlobRef.print fr.fr_custom) )
    | Fp_value i -> (
      match List.nth_opt fr.fr_values i with
      | Some e -> pp_spliced ctx env ~followed_by_dot e
      | None -> CErrors.anomaly Pp.(str "Custom syntax: unbound term argument in " ++ GlobRef.print fr.fr_custom) )
    | Fp_result -> (
      match result with
      | Some name -> str name
      | None -> CErrors.anomaly Pp.(str "Custom syntax: %result outside a block in " ++ GlobRef.print fr.fr_custom) )
    | Fp_statement_end ->
      CErrors.anomaly Pp.(str "Custom syntax: a block's statement written as a term in " ++ GlobRef.print fr.fr_custom)
  in
  let rec pieces acc = function
    | [] -> acc
    | p :: rest ->
      let followed_by_dot =
        match rest with
        | Fp_text s :: _ ->
          let s = String.trim s in
          String.length s > 0 && s.[0] = '.'
        | _ -> false
      in
      pieces (acc ++ piece ~followed_by_dot p) rest
  in
  pieces (mt ()) fr.fr_pieces

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
    pp_doc_comment_for_name (short_name ctx Type id)
    ++ (pp_type ctx ty ++ str " " ++ str (short_name ctx Type id)
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
    ++ str (declared_name ctx Type id)
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

(** The name the struct wrapping [id] at namespace scope is written under at
    the position [ctx] ({!Cpp_names.wrapper_name_from}). *)
let nspace_wrapper_name ctx id = wrapper_name_from (declared_name ctx) id

(** Whether the wrapper [w] of the declaration [members] and the struct
    inside it are written as one struct, as {!Cpp_ind} decided where it built
    the wrapper ({!Minicpp.nspace_wrapper}).  Under [CRANE_CHECK_IR] the
    decision is asked again of what is printed: a sole struct, and a wrapper
    no other declaration of its module was planned into. *)
let nspace_merges ctx (w : nspace_wrapper) (members : cpp_decl list) =
  ( if Probe.checking () then
      let asked =
        (match members with [Dstruct _] -> true | _ -> false)
        && not (in_unmerged_wrapper_named (short_name ctx Type w.nw_ref) w.nw_ref)
      in
      if asked <> w.nw_merges then
        Probe.violation "wrapper merges"
          Pp.(
            str "the wrapper of " ++ str (nspace_wrapper_name ctx w.nw_ref) ++ str " was built "
            ++ str (if w.nw_merges then "merged" else "unmerged")
            ++ str " and is printed around declarations it does not merge that way") );
  w.nw_merges

(** The name the struct of [id] is defined under. *)
let struct_definition_name ctx id = Cpp_name.pp (Cpp_names.definition_name ctx Struct_definition id)

(** The name the scoped enum of [r] is defined under. *)
let enum_definition_name ctx r = Cpp_name.pp (Cpp_names.definition_name ctx Enum_definition r)

let pp_forward_declaration ctx env : Cpp_ast.defined -> _ = function
  | Defined_struct {struct_; name; tparams; constraint_} ->
    let name = match name with As_defined -> struct_definition_name ctx struct_ | As_inductive_wrapper -> str (nspace_wrapper_name ctx struct_) in
    struct_template_head ~pp_param:(pp_template_param_redecl ctx) ctx env tparams constraint_ ++ str "struct " ++ name ++ str ";"
  | Defined_enum r -> str "enum class " ++ enum_definition_name ctx r ++ str ";"

let start_file_scope_census () = file_scope_types_written := CString.Set.empty

(** Under [CRANE_CHECK_IR], the type names the file [file] introduced at
    file scope must be the ones planned for it. *)
let check_file_scope_types ~file =
  if Probe.checking () then begin
    let written = !file_scope_types_written and planned = Cpp_state.file_scope_types_of file in
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
  note_file_scope_type ctx (settled :> cpp_decl);
  match Cpp_erasure.view settled with
  | Template (temps, cstr, inner) -> pp_template_decl ctx env temps cstr inner
  | Namespace (None, decls) ->
    let ds = pp_list_stmt (pp_cpp_decl ctx env) decls in
    (str "namespace " ++ str "{") ++ fnl () ++ ds ++ fnl () ++ str "};"
  | Namespace (Some w, members) -> pp_wrapper_nspace ctx env w members
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
and pp_wrapper_nspace ctx env w (members : Cpp_erasure.settled list) =
  let decls = (members :> cpp_decl list) in
  let struct_name_str = nspace_wrapper_name ctx w.nw_ref in
  (* The decision the out-of-line definition of a member reads too: the
     member carries its wrapper ({!Member_hoist}), so the two cannot drift
     apart. *)
  let merges = nspace_merges ctx w decls in
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
      | Some {ol_scope; _} when not is_lifted -> str (Scope_plan.qualifier ol_scope) ++ str "::" ++ base_name
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
      (* A [static inline] variable is initialised in a translation unit
         only if that unit names it: clang emits it nowhere else.  One that
         only a function body reads is then initialised only where that body
         is compiled -- the [.cpp] -- and another unit's initialiser calling
         the function runs first if its unit is linked first, reading the
         variable before it holds its value.  [[gnu::used]] has every unit
         including the header initialise it, before what follows it.  At
         namespace scope a [const] variable is one per unit, each initialised
         by its own unit, so the function reads its own unit's: [inline]
         makes it one variable. *)
      let static_kw =
        match (ctx.rc_in_struct, literal) with
        | true, true -> str "static constexpr "
        | true, false when Cpp_state.read_by_a_function id -> str "[[gnu::used]] static inline "
        | true, false -> str "static inline "
        | false, false when Cpp_state.read_by_a_function id -> str "[[gnu::used]] inline "
        | false, true -> str "inline constexpr "
        | false, false -> mt ()
      in
      (* An initialiser holding a lambda that captures is invoked in place
         already ({!Cpp_erasure.invoke_capturing_initialisers}). *)
      h
        ( static_kw
        ++ pp_type ctx ty
        ++ str " "
        ++ str (declared_name ctx Type id)
        ++ str " = "
        ++ expr_pp
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
      ++ str (declared_name ctx Type u.du_name)
      ++ def
      ++ note
      ++ str ";" )
  | Dstruct_fwd (tparams, r) ->
    (pp_template_header ctx tparams ++ str "struct " ++ str (declared_name ctx Type r) ++ str ";")
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
      | Some w when not w.nw_merges ->
        let own = declared_name ctx Type dm_owner in
        (own, nspace_wrapper_name ctx w.nw_ref ^ "::" ^ own)
      | _ ->
        let own = String.capitalize_ascii (declared_name ctx Type dm_owner) in
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
       ({!Cpp_leaf_plan.held_back_assertions}). *)
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

(** [d] printed in [env] where the printer is: a declaration written
    outside every tree. *)
let read_cpp_decl ctx env d = pp_cpp_decl ctx env d

(** The wrapper structs [d] writes around something other than a sole
    struct merged into them, in the order it writes them, each named by
    [name]: the structs another wrapper's declarations can be written
    into. *)
let rec unmerged_wrappers_named ~name (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> unmerged_wrappers_named ~name inner
  | Namespace (None, decls) -> List.concat_map (unmerged_wrappers_named ~name) decls
  | Namespace (Some w, members) ->
    if w.nw_merges then [] else List.concat_map (unmerged_wrappers_named ~name) members @ [name w.nw_ref]
  | Decl _ -> []

(* Whether [d], written at the position [ctx], writes a wrapper struct
   holding a wrapper module's declarations, one [homed] names. *)
let absorbs ctx ~homed d =
  List.exists
    (fun name -> List.mem_assoc name homed)
    (unmerged_wrappers_named ~name:(nspace_wrapper_name ctx) d)

(** [d], which {!absorbs}, as written: each wrapper struct holding a wrapper
    module's declarations a {!Cpp_ast.Wrapper_struct}, the wrapper's own
    members its fields, each printed where the tree puts it
    ({!Cpp_ast.Absorbed}). *)
let rec absorbing_at ctx ~homed ?tyctors env (d : Cpp_erasure.settled) =
  note_file_scope_type ctx (d :> cpp_decl);
  let written ctx d = if absorbs ctx ~homed d then absorbing_at ctx ~homed ?tyctors env d else Cpp_ast.absorbed ?tyctors env d in
  match Cpp_erasure.view d with
  | Template (temps, cstr, inner) -> Cpp_ast.seq [Cpp_ast.text (template_head ctx env temps cstr); written ctx inner]
  | Namespace (None, decls) ->
    Cpp_ast.seq
      [ Cpp_ast.text (str "namespace {" ++ fnl ());
        Cpp_ast.concat fnl (List.map (written ctx) decls);
        Cpp_ast.text (fnl () ++ str "};") ]
  | Namespace (Some w, members) -> (
    let name = nspace_wrapper_name ctx w.nw_ref in
    let ds = enter_from ctx In_struct (fun ctx -> Cpp_ast.concat fnl (List.map (written ctx) members)) in
    match List.assoc_opt name homed with
    | Some module_ -> Cpp_ast.wrapper_struct ~name ~module_ ~fields:Cpp_ast.(seq [ds; text (fnl ())])
    | None -> Cpp_ast.(seq [text (str "struct " ++ str name ++ str " {" ++ fnl ()); ds; text (fnl () ++ str "};")]) )
  | Decl _ -> Cpp_ast.text (pp_cpp_decl ctx env d)

let resolved ctx key (resolution : Cpp_ast.resolution) =
  match resolution with Resolved n -> checked ctx key n | Unresolved -> unresolved key

let resolved_module ctx (m : Cpp_ast.module_ref) = resolved ctx (Module m.path) m.name
let resolved_class_concept ctx (c : Cpp_ast.global_ref) = resolved ctx (Class_concept c.global) c.name
let resolved_type_name ctx (g : Cpp_ast.global_ref) = resolved ctx (Global (Type, g.global)) g.name
let resolved_concept ctx (c : Cpp_ast.concept_ref) = resolved ctx (Modtype_concept c.module_type) c.name
let pp_declared_module ctx (m : Cpp_ast.declared_module) = Cpp_name.pp (resolved ctx (Module_declared m.declares) m.name)

let name_in ctx names frame key = name_from ctx names frame key

(* A module named in a module expression, and its resolution. *)
let pp_module_name ctx (m : Cpp_ast.module_ref) =
  let r = resolved_module ctx m in
  (str (wrapper_qualify_modname m.path (resolved_string r)), r)

(* Inside a class template a qualified module is a dependent name: an
   argument is preceded by [typename], and a functor applied is named
   [A::template F]. *)
let pp_application ctx {Cpp_ast.functor_; args} =
  let in_template = ctx.rc_in_template in
  let head =
    match pp_module_name ctx functor_ with
    | _, r when in_template && resolved_is_qualified r -> Cpp_name.pp ~template_keyword:true r
    | head, _ -> head
  in
  let arg m =
    match pp_module_name ctx m with
    | a, r when in_template && resolved_is_qualified r -> str "typename " ++ a
    | a, _ -> a
  in
  head ++ str "<" ++ prlist_with_sep (fun () -> str ", ") arg args ++ str ">"

let pp_module_alias ctx name (target : Cpp_ast.module_expr) =
  let target =
    match target with
    | Module_named m ->
      let r = resolved_module ctx m in
      let named = str (resolved_string r) in
      if ctx.rc_in_template && resolved_is_qualified r then str "typename " ++ named else named
    | Applied a -> pp_application ctx a
  in
  str "using " ++ pp_declared_module ctx name ++ str " = " ++ target ++ str ";"

(* A template head, each name it writes checked where it is printed as the
   rest of the declaration's are ({!resolved}). *)
let pp_template_head ctx template =
  List.iter
    (function
      | Cpp_ast.Typename (Type_variable _) -> ()
      | Typename (Module_parameter m) -> ignore (resolved_module ctx m)
      | Constrained {concept; args; param} ->
        ignore (resolved_concept ctx concept);
        List.iter (fun m -> ignore (resolved_module ctx m)) (args @ [param]) )
    template;
  Cpp_ast.pp_template_head template

let pp_functor_alias ctx name functor_ params =
  pp_template_head ctx (List.map fst params)
  ++ str "using " ++ pp_declared_module ctx name ++ str " = "
  ++ str (resolved_string (resolved_module ctx functor_))
  ++ str "<" ++ prlist_with_sep (fun () -> str ", ") (fun (_, m) -> Cpp_name.pp (resolved_module ctx m)) params ++ str ">;"

(* The base is written inside the functor's template; a base specifier
   names a type, so a dependent one takes no [typename]. *)
let pp_derived_functor ctx template name (base : Cpp_ast.module_expr) =
  let inside = {ctx with rc_in_struct = true; rc_in_template = true} in
  let base = match base with Module_named m -> fst (pp_module_name inside m) | Applied a -> pp_application inside a in
  pp_template_head ctx template ++ str "struct " ++ pp_declared_module ctx name ++ str " : " ++ base ++ str " {};"

(* The declaration of a synthesised template, its body written where it is
   declared, which is where it is printed, a holder's parameters as planned
   ({!Cpp_state.holder_parameter}). *)
let pp_synthesised ctx (s : Cpp_ast.synthesised) =
  let body = Pp.string_of_ppcmds (pp_cpp_type ctx false s.vars s.body) in
  if Probe.checking () && not (String.equal body s.planned) then
    Probe.violation "constructor aliases"
      (str "the template " ++ str s.name ++ str " is declared with the body " ++ str body ++ str ", planned as "
     ++ str s.planned );
  match s.holder with
  | None -> str "template <typename " ++ str ctor_alias_tvar ++ str "> using " ++ str s.name ++ str " = " ++ str body ++ str ";"
  | Some params ->
    (if Probe.checking () then
       let names = identifier_tokens body in
       let rec read i =
         let f = Generated_name.indexed "F" i and p = Generated_name.indexed "P" i in
         if List.mem (Id.to_string f) names then Cpp_ast.Constructor_parameter f :: read (i + 1)
         else if List.mem (Id.to_string p) names then Cpp_ast.Type_parameter p :: read (i + 1)
         else []
       in
       if read 0 <> params then
         Probe.violation "holder parameters"
           (str "the holder " ++ str s.name ++ str " writes other parameters in its body than were planned for it"));
    let param : Cpp_ast.holder_parameter -> _ = function
      | Constructor_parameter f -> str "template <typename> class " ++ Id.print f
      | Type_parameter p -> str "typename " ++ Id.print p
    in
    str "template <"
    ++ prlist_with_sep (fun () -> str ", ") param params
    ++ str "> struct " ++ str s.name ++ str " { template <typename " ++ str ctor_alias_tvar ++ str "> using c = " ++ str body
    ++ str "; };"

let print_unprinted ctx ~modtype_concept ~assertion (u : Cpp_ast.unprinted) =
  let ctx =
    { ctx with
      rc_names = Names_resolved u.names;
      rc_tyctors = Planned (Option.default [] u.tyctors) }
  in
  match u.declaration with
  | Modtype_concept {path; params; concept} -> modtype_concept ctx ~names:u.names ~params path concept
  | Assertion a -> assertion ctx a
  | Module_alias {name; target} -> pp_module_alias ctx name target
  | Functor_alias {name; functor_; params} -> pp_functor_alias ctx name functor_ params
  | Derived_functor {template; name; base} -> pp_derived_functor ctx template name base
  | Forward_declaration {env; defined} -> pp_forward_declaration ctx env defined
  | Synthesised_template s -> pp_synthesised ctx s
  | Declaration {env; settled} | Absorbed {env; settled} -> pp_cpp_decl ctx env settled
  | Fields {vars; fields; _} ->
    prlist_with_sep fnl (fun (name, ty) -> pp_cpp_type ctx false vars ty ++ spc () ++ str name ++ str ";") fields ++ fnl ()
  | Global_alias a ->
    let tparams, name =
      match a with
      | Alias_of_type {target; definition; tparams} ->
        (tparams, Cpp_name.pp (resolved ctx (Definition (definition, target.global)) target.name))
      | Alias_of_module m -> ([], Cpp_names.module_struct_name_of (resolved_module ctx m))
    in
    let args =
      if tparams = [] then mt () else str "<" ++ prlist_with_sep (fun () -> str ", ") (fun (_, v) -> Id.print v) tparams ++ str ">"
    in
    pp_template_header ctx tparams ++ str "using " ++ name ++ str " = ::" ++ name ++ args ++ str ";"

let cut2 = Cpp_ast.cut2

let pp_cpp_type_at ctx par vl t = pp_cpp_type ctx par vl t

(* The type printer's entry for a type written outside every declaration of
   the tree: where the printer is. *)
let pp_cpp_type ?lead par vl t = pp_cpp_type ?lead (file_start Common.Intf) par vl t
