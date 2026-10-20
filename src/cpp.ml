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

(** Top-level C++ extraction orchestrator.

    This module handles module type → concept conversion, structure element
    processing, the wrapper module dual-pass, and the main pp_struct/pp_hstruct
    entry points. Lower-level rendering is delegated to:
    - {!Cpp_state} — mutable state and utilities
    - {!Cpp_names} — name resolution and qualification
    - {!Cpp_print} — type/expr/stmt/field/declaration pretty-printing
    - {!Cpp_concepts} — module-type concept printing
    - {!Cpp_ind} — inductive type rendering and decl-level dispatch *)

open Pp
open Util
open Names
open ModPath
open Table
open Miniml
open Common
open Minicpp
open Translation
open Gen_decls
open Cpp_state
open Cpp_names
open Cpp_print
open Cpp_concepts
open Cpp_ind

(** Whether the concept [d] of a type class declared in the module [mp]
    names one of the module's own members, and so cannot be declared ahead
    of the module's struct.  Asked of the concept generated, not of its
    text: a class it names is not a member, since its concept is declared
    outside every struct too. *)
let concept_names_member mp d =
  let names = ref false in
  Minicpp.iter_globrefs
    (fun r ->
      if MPset.mem mp (Table.prefixes_mp (modpath_of_r r)) && not (Table.is_typeclass r) then
        names := true )
    d;
  !names

(** Look up and format a doc comment for the given label. *)
let pp_doc_comment label = pp_doc_comment_for_name (Label.to_string label)

(** Try to extract a named concept from a module type.

    Strips [MTwith] constraints (which have no C++ concept equivalent) and
    [MTfunsig] parameter layers, looking for an [MTident] that references an
    already-defined concept.  Returns [None] for anonymous inline signatures
    ([MTsig]).

    This is important for functor parameters like
    [c' : C b' with Module a := A_instance].  Rocq's extraction expands
    [MEapply] (module type application) into an inline [MTsig], losing the
    reference to the named concept [C].  Without this helper,
    [pp_module_type] would inline the concept body into the template
    parameter list, producing garbled C++. *)
let rec concept_of_mt = function
  | MTident kn -> Some (kn, pp_concept_ref kn)
  | MTwith (mt, _) -> concept_of_mt mt
  | MTfunsig (_, _, mt') -> concept_of_mt mt'
  | MTsig _ -> None

(** The concept an enclosing struct holds back that makes it hold back
    [a]. *)
let held_concept_of (a : Cpp_ast.assertion) =
  match a.concept with Of_module_type mp -> HCmodtype mp | Of_class r -> HCclass r

(** The assertion that the module [mp] satisfies the concept of its module
    type [mty], and the assertions it holds back.  When that concept is one
    the enclosing struct holds back, so is the assertion: the concept is not
    declared yet. *)
let concept_assertion mp mty =
  match concept_of_mt mty with
  | None -> (Cpp_ast.empty, [])
  | Some (mt_mp, _) ->
    let a = {Cpp_ast.concept = Of_module_type mt_mp; subject = Module mp} in
    if concept_held_back (held_concept_of a) then (Cpp_ast.empty, [a]) else (Cpp_ast.assertion a, [])

(** Render a functor parameter as a C++ template parameter.

    Strategy:
    - If a named concept can be extracted from the module type via
      {!concept_of_mt}, emit [ConceptName param_name].
    - Otherwise emit [typename param_name] (unconstrained type parameter).
      {!concept_of_mt} declines only for [MTsig], and an anonymous
      signature's requirement lines are not a constraint expression: they
      belong inside a named concept, not in a template parameter list. *)
let template_param (mbid, mt) : Cpp_ast.template_param =
  let param = pp_modname (MPbound mbid) in
  match concept_of_mt mt with
  (* A concept the enclosing struct holds back is declared after it, so a
     functor inside it takes its parameter unconstrained, as a class concept
     held back does. *)
  | Some (mt_mp, _) when concept_held_back (HCmodtype mt_mp) -> Typename param
  | Some (mt_mp, cname) ->
    let args =
      match concept_extra_args mt_mp with
      | [] -> Pp.mt ()
      | ps -> str "<" ++ prlist_with_sep (fun () -> str ", ") pp_modname ps ++ str ">"
    in
    Constrained {concept = cname ++ args; param}
  | None -> Typename param

(** The functor application [me], its arguments in order.  Rocq applies a
    functor to paths only ({!Extract_env.extract_mexpr}), and only a path
    or an application is applied. *)
let application_of me =
  let rec flatten args = function
    | MEapply (g, MEident arg) -> flatten (arg :: args) g
    | MEident functor_ -> {Cpp_ast.functor_; args}
    | _ -> CErrors.anomaly (Pp.str "Crane: a functor application whose functor or argument is not a path.")
  in
  flatten [] me

(** [plain_struct name] is the head of the struct [name], which is no
    template and derives from nothing. *)
let plain_struct name = {Cpp_ast.template = []; name; base = None}

(** The name of the lifted helper a declaration defines, if it defines one.

    Asking {!Lifted.of_ref} rather than matching the shape of the name is what
    keeps an ordinary [Dfun] whose reference happens to be a [VarRef] -- a
    record field accessor, a [make] factory -- from being taken for a
    helper. *)
let rec lifted_decl_key = function
  | Dtemplate (_, _, inner) -> lifted_decl_key inner
  | Dfun {df_path = {dp_outer = r, []; dp_inner = []}; _} ->
    Option.map Lifted.name (Lifted.of_ref r)
  | _ -> None

(** Whether a rendering writes a qualifier into a struct or a template
    parameter, read from the kinds its names were tagged with as they were
    written ({!Cpp_name.written}). *)
let names_into_a_struct (doc : Pp.t) : bool = List.exists writes_into_a_struct (Cpp_name.written doc)

(** Whether [spec] may be emitted at the top of the file, above every
    definition in it.

    A declaration needs the types in its signature {e declared}, not complete,
    which is what lets one naming [Nat] precede [Nat]'s own definition.  Naming
    [List::list] is a different act: it is name lookup {e into} [List], and
    that needs [List] complete.  A forward declaration cannot supply it, so no
    position above the structs is legal for such a signature and the honest
    answer is to leave it where it is.

    The question is about what is written, and is asked of the declaration's
    types through the heads the type printer writes them with
    ({!Cpp_print.declaration_names_into_a_struct}), each qualifier with what it
    is.  The IR node alone cannot answer: [Nat] and [List::list] are both
    [Tnamespace], which means "an inductive's own scope", not "inside a module
    struct".  Nor can the tables behind the printer, taken one at a time --
    whether a qualifier is written is settled by a chain of them (is the
    module a wrapper, is the type nonetheless emitted at global scope, is it
    an eponymous record, an enum, a local inductive), and any single one of
    them is a second opinion; two such opinions have already been wrong here.
    The heads are not one: they are what the printer writes from.  Under
    [CRANE_CHECK_IR] the answer must agree with the qualifiers the rendered
    declaration writes, read back from their tags ({!names_into_a_struct}).

    A namespace needs nothing complete: naming into one asks only that the
    name be declared, which is all a declaration asks of an unqualified name
    too.  So a library's namespace ([std::], [crane::]), whose headers are
    included above everything, a file's under separate extraction, and the
    global one ([::Nat]) all pass.  A struct is refused, and so is a
    dependent [M::t], which needs no completeness but costs only a missed
    hoist to refuse.  Text no name was written through -- an external name,
    a custom mapping's replacement -- is read as text: the identifier in front
    of each [::] is the qualifier, and passes only as one of the included
    libraries' namespaces.

    This is the one place a declaration is not free.  A helper declared
    needlessly costs a line, but a helper declared needlessly {e and}
    qualifying into a struct would drag the whole block below that struct --
    past the uses it exists to precede -- so what it costs is the position, for
    every other helper in the block. *)
let spec_is_hoistable (spec : Cpp_erasure.settled) : bool =
  let hoistable = declaration_names_into_a_struct (spec :> cpp_decl) = Some false in
  if Probe.checking () && hoistable = names_into_a_struct (Cpp_print.read_cpp_decl (empty_env ()) spec) then
    Probe.violation "hoisted helpers"
      Pp.(str "a helper's declaration was judged by its type to "
          ++ str (if hoistable then "name nothing inside a struct, and its rendering does"
                  else "name into a struct, and its rendering does not"));
  hoistable

(* Whether the module [mp] is rendered outside every struct, as planned
   ({!Scope_plan.nested}). *)
let outside_every_struct mp = not (Scope_plan.nested mp)

(** A lifted helper [d], finalized: what to write in its place, and the
    declaration to hoist ahead of its callers where [d] defines a function,
    [may_hoist] allows it, and {!spec_is_hoistable} does.

    Both come from one finished definition, so the hoisted declaration states
    the head the definition does; the definition then leaves the template
    defaults to the declaration. *)
let lifted_views ?(may_hoist = true) (d : cpp_decl) =
  let e = Function_entity.of_finished (Cpp_ind.finished_alone d) in
  let spec = Function_entity.declaration e in
  if Function_entity.defines_function e && may_hoist && spec_is_hoistable spec
  then (Function_entity.definition_after_declaration e, Some spec)
  else (Function_entity.definition e, None)

(** Whether a module's members name only types a forward declaration can
    stand in for.

    The header opens with a forward declaration of every datatype struct, so a
    parameter or result spelled at one is nameable from anywhere in the file.
    Anything else a member's type can name -- a Rocq definition used as a type,
    which reaches C++ as a [using] alias at the point it was defined -- is not.

    Read off the members' ML types rather than the rendered text, because the
    text cannot tell [tbl] the alias from [a] the parameter. *)
let module_members_name_only_inductives sel =
  let rec ty_ok = function
    | Miniml.Tglob (r, args, _) ->
      (match r with GlobRef.IndRef _ -> true | _ -> false)
      && List.for_all ty_ok args
    | Miniml.Tarr (a, b) -> ty_ok a && ty_ok b
    | Miniml.Tmeta {contents = Some t} -> ty_ok t
    | _ -> true
  in
  List.for_all
    (fun (_, se) ->
      match se with
      | SEdecl ((Dterm _ | Dfix _) as d) ->
        List.for_all (fun fd -> ty_ok fd.fd_type) (Mlutil.term_defs d)
      (* Only a function declaration is being judged here.  Everything else a
         module holds -- an inductive, a type alias, a submodule -- is either
         rendered somewhere other than this struct or shows up in its text as a
         member that is not a [static] declaration, which the other half
         rejects; asking a question about it here only rejects modules whose
         struct never contained it. *)
      | _ -> true )
    sel

(** The modules whose structs the header declares ahead of the file rather
    than at the module's own place in the emitted order, by the module path
    of their body: planned before either file is rendered
    ({!plan_hoisted_structs}).

    Its own place is the safe answer and stays the default, because a member
    initialised inside the struct body runs there, and everything that body
    names must be complete by then.  The one shape that is certainly free of
    that is a struct of nothing but static function {e declarations} --
    [static Nat pick(Nat, Nat);], defined out of line: a declaration asks its
    parameter and result types to be declared, which the forward declarations
    above already do ({!module_members_name_only_inductives}), and asks
    nothing else of the file at all -- unless it qualifies a name into
    another struct, which is the question {!spec_is_hoistable} asks of a
    lifted helper and for the same reason: [Other::t] needs [Other] complete,
    so moving this in front of it would not help.  So the only thing such a
    struct's position decides is whether its callers can see it, and a
    function hoisted onto a datatype is a caller emitted with the datatype,
    which may come first. *)
let hoisted_structs : MPset.t ref = State.cell State.Unit MPset.empty

(** Whether the struct of the module whose body is [mp] is declared ahead of
    the file, as planned.  Under [CRANE_CHECK_IR] a struct planned to be
    must not write, in [t], what is written for it, a qualifier into another
    struct: the plan asked that of its members' types, and this is what is
    written, its declarations printed as the tree spells them. *)
let struct_hoists mp t =
  let planned = MPset.mem mp !hoisted_structs in
  if Probe.checking () && planned && names_into_a_struct (Cpp_ast.print_tree ~write:(Cpp_ind.write_unprinted ~file:Intf) t) then
    Probe.violation "hoisted structs"
      Pp.(
        str "the struct of the module " ++ str (ModPath.to_string mp)
        ++ str " was planned to be declared ahead of the file and qualifies a name into another struct" );
  planned

(** What the header writes away from where it is written, planned before
    either file is rendered ({!plan_file_layout}): each a section of groups
    of declarations, in writing order, each group with the module it was
    generated in, whose elements' scope it is spelled in
    ({!Cpp_ind.group}). *)
type file_layout = {
  erased_aliases : Cpp_ind.section;
      (** The erasure landing pads written at file scope -- [using X =
          std::any;] for a name with no C++ spelling behind it -- which go
          ahead of everything, the concepts included: an alias to [std::any]
          names nothing, and the text that lands on it does not follow it. *)
  lifted_specs : Cpp_ind.section;
      (** The declarations of the helpers an element written at namespace
          scope places, which go ahead of every section: an inductive's
          helpers are written directly after its struct closes, and so after
          the methods that call them. *)
  member_defs : Cpp_ind.section;
      (** The definitions of members a datatype's struct at namespace scope
          gave up because their bodies name a module's struct, which is
          written after every datatype and cannot be moved in front of one it
          holds by value: they go last. *)
  forward_decls : Pp.t list;
      (** The forward declaration of every struct and scoped enum the header
          defines at namespace scope but a constrained template, in the order
          it defines them, which open the file. *)
  constrained_decls : Cpp_print.forward_declaration list;
      (** The forward declarations of the constrained templates lifted out of
          a wrapper module's functions, in the order the header defines them:
          they go in front of the first chunk of the file that names the
          struct before defining it ({!Cpp_ast.schedule}).  One a
          top-level element defines is never needed: nothing ahead of the
          element names it, or the struct would not be a template the
          element defines. *)
  promoted_imports : string list;
      (** The using-declarations, at the top of the header, of the promoted
          type variables the unit's declarations write whose class field
          another file declares ({!Cpp_print.promoted_alias_import}), in
          alphabetical order: the implementation file includes the header,
          and so sees them too. *)
  wrapper_homes : (string * ml_decl) list;
      (** The wrapper modules whose declarations the header writes into a
          struct of the same name that a declaration writes around an
          inductive -- [Nat::nat], with the functions of the module [Nat] --
          by that name, with the declaration: the first the header writes,
          if it writes it before the module's own turn.  Any other wrapper
          module's declarations are written as a struct of their own, at the
          module's turn. *)
  file_scope_types : CString.Set.t;
      (** The type names the header introduces at namespace scope
          ({!Cpp_print.file_scope_types}), which a definition written out of
          line leaves unqualified. *)
}

let file_layout : file_layout ref =
  State.cell State.Unit
    { erased_aliases = [];
      lifted_specs = [];
      member_defs = [];
      forward_decls = [];
      constrained_decls = [];
      promoted_imports = [];
      wrapper_homes = [];
      file_scope_types = CString.Set.empty }


(** Report what a lifted helper met at the site that placed it, under
    [CRANE_DBG_LIFTED].

    A helper comes back from the generation that lifted it to the site that
    places that generation, and which of the site's conditions it failed is
    not recoverable from the output.

    The rendered declaration is printed with it, because that text is what
    {!spec_is_hoistable} answers for: a rejection is only interpretable next
    to the qualifier that caused it. *)
let dbg_lifted =
  let on = lazy (Sys.getenv_opt "CRANE_DBG_LIFTED" <> None) in
  fun ~site ?(extra = "") (d : cpp_decl) ->
    if Lazy.force on then
      let name =
        match lifted_decl_key d with
        | Some k -> Id.to_string k
        | None -> "<not-a-lifted-helper>"
      in
      let split =
        let e = Function_entity.of_finished (Cpp_ind.finished_alone d) in
        if Function_entity.defines_function e then
          let spec = Function_entity.declaration e in
          Printf.sprintf "splits=yes hoistable=%b spec=%S"
            (spec_is_hoistable spec)
            (Pp.string_of_ppcmds (read_cpp_decl (empty_env ()) spec))
        else "splits=no"
      in
      Feedback.msg_notice
        (Pp.str
           (Printf.sprintf "[crane:lifted] %-28s site=%-12s %s%s" name site
              split
              (if extra = "" then "" else " " ^ extra) ) )

(** The concept of the type class [r], generated in the module [module_],
    recorded as [r]'s generation. *)
let generated_concept ~module_ r fields =
  let d = Cpp_ind.concept ~module_ r fields in
  ignore (record_entity r [d] []);
  d

(** The concept [d] of a class, an element of the module [module_]
    wherever the file moves it -- ahead of or after the struct of the
    module declaring the class, or to the top of the file -- printed where
    the tree puts it. *)
let class_concept_element ~module_ d = Cpp_print.unprinted ~module_ (empty_env ()) (Cpp_ind.finished_alone d)

(** The functions of a module's method candidates [candidates] its
    eponymous record's struct is given as methods: those that are not
    projections, oldest first. *)
let record_method_candidates candidates =
  List.filter (fun (r, _, _, _) -> not (Table.is_projection r)) (List.rev candidates)

(** The methods [fields] of the eponymous record [r], with the helpers
    [lifted] out of them, each as the generation of the function it was made
    of, with the helpers lifted out of it. *)
let record_method_entities r fields lifted =
  List.filter_map
    (fun ((f, _, _) as field) ->
      match f with
      | Fmethod {mf_globref = Some m; _} ->
        let own d =
          match Option.bind (decl_globref d) Lifted.of_ref with
          | Some h -> Option.equal Names.GlobRef.UserOrd.equal (Lifted.origin h) (Some m)
          | None -> false
        in
        Some
          (Cpp_ind.entity m
             [ Dfields
                 { ds_ref = r;
                   ds_fields = [field];
                   ds_tparams = [];
                   ds_constraint = None;
                   ds_needs_shared_from_this = false } ]
             (List.filter own lifted) )
      | _ -> None )
    fields

(** The methods of the eponymous record [r] made of [candidates], each
    recorded as the generation of the function it was made of, and the
    helpers lifted out of their bodies, which are members beside them. *)
let generated_record_methods ~module_ r vars candidates =
  let fields, lifted = Cpp_ind.record_methods ~module_ r vars candidates in
  List.iter
    (fun e -> ignore (Generated_program.record e))
    (record_method_entities r fields lifted);
  (fields, lifted)

(** The classes [sel] declares, in order, each with its label and fields:
    every packet of a class inductive, and every singleton class, which is
    declared as its method's type and becomes a concept all the same. *)
let declared_classes sel =
  List.concat_map
    (fun (l, se) ->
      match se with
      | SEdecl (Dind (kn, ({ind_kind = TypeClass fields; _} as ind))) ->
        List.init (Array.length ind.ind_packets) (fun i -> (l, GlobRef.IndRef (kn, i), fields))
      | SEdecl (Dtype (r, _, _)) when Table.singleton_class_method r <> None ->
        [(l, r, Table.get_record_field_bindings r)]
      | _ -> [] )
    sel

(** Whether a name collision puts the module [mp] inside a wrapper struct,
    flattened or as a bystander. *)
let is_wrapped_child mp =
  match Module_plan.wrapper_role mp with
  | Some (Flattened | Bystander) -> true
  | Some Own | None -> false

(** [in_planned_visibility mp k] runs [k] in the visibility planned for the
    body of the module [mp] ({!plan_visibility}).  Under [CRANE_CHECK_IR],
    the body must be entered from the scope its plan nests it in. *)
let in_planned_visibility mp k =
  match Scope_plan.visibility mp with
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the module " ++ str (ModPath.to_string mp) ++ str " has no planned visibility.")
  | Some planned ->
    ( if Probe.checking () then
        let actual = current_visibility () in
        if not (equal_visibility (enclosing_visibility planned) actual) then
          Probe.violation "visibility chains"
            Pp.(
              str "the module " ++ str (ModPath.to_string mp) ++ str " is entered from "
              ++ pp_visibility actual ++ str ", planned in " ++ pp_visibility planned) );
    with_visibility planned k

(** Whether the module [mp], of elements [sel], has a child a name collision
    puts inside a wrapper struct, which then holds all of [mp]'s elements:
    the header writes them inside that struct. *)
let wraps_children mp sel =
  List.exists
    (fun (l, se) -> match se with SEmodule _ -> is_wrapped_child (MPdot (mp, l)) | _ -> false)
    sel

(** The inductives the body of the module [mp] of elements [sel] spells
    bare: those it declares, under separate extraction only those whose
    kernel name is [mp]'s own. *)
let inductives_declared_in mp sel =
  List.concat_map
    (fun (_, se) ->
      match se with
      | SEdecl (Dind (kn, ind)) when (not (modular ())) || ModPath.equal (MutInd.modpath kn) mp ->
        List.init (Array.length ind.ind_packets) (fun i -> GlobRef.IndRef (kn, i))
      | _ -> [] )
    sel

(** The inductives every module of the unit that is not a wrapper module
    spells bare: under separate extraction, all those the unit declares, at
    any depth; otherwise none.  A wrapper module is written without them,
    and a separately extracted unit, being one file module that is its own
    main module, has none. *)
let file_local_inductives (analysis : Structure_analysis.t) =
  let rec all sel =
    List.concat_map
      (fun (_, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) -> List.init (Array.length ind.ind_packets) (fun i -> GlobRef.IndRef (kn, i))
        | SEmodule {ml_mod_expr = MEstruct (_, sub); _} -> all sub
        | _ -> [] )
      sel
  in
  if modular () then List.concat_map (fun (mi : Structure_analysis.module_info) -> all mi.sels) analysis.sorted_modules
  else []

(** [with_local_inductives refs k] runs [k] with [refs] local as well. *)
let with_local_inductives refs k =
  let outer = get_local_inductives () in
  List.iter add_local_inductive refs;
  Fun.protect
    ~finally:(fun () ->
      clear_local_inductives ();
      List.iter add_local_inductive outer )
    k

(** Whether a finished declaration is an erasure landing pad: [using X =
    std::any;], which names nothing. *)
let is_erased_alias (_, d) =
  match (d : Cpp_erasure.settled :> cpp_decl) with
  | Dusing {du_rhs = Some rhs; _} -> Cpp_erasure.is_any_shaped rhs
  | _ -> false

(** What writing a structure element gives: its text, written where it is,
    and the concepts it declares that only namespace scope can hold, in the
    order written, which go to the top of the file.  A module's body gives
    its members as text, which the module encloses ({!Cpp_ast.body}). *)
type 'a rendering = {
  text : 'a;
  concepts : Cpp_ast.t list;
  asserts : Cpp_ast.assertion list;
      (** The assertions it held back, in the order written: a concept an
          enclosing struct holds back is declared after that struct, and
          the assertion goes with it. *)
}

type written = Cpp_ast.t rendering

let written text : written = {text; concepts = []; asserts = []}

(** [element_of mp w] is [w], an element of the body of the module [mp],
    spelled as its elements are ({!Cpp_ast.elements}) -- and so are the
    concepts it declares, which were written in that body too, wherever the
    file moves them. *)
let element_of mp (w : written) =
  {w with text = Cpp_ast.elements ~source:mp w.text; concepts = List.map (Cpp_ast.elements ~source:mp) w.concepts}

(** [unenclosed_element enclosure ?fields body] is a module element whose
    body is written with no struct of its own, as {!Cpp_ast.module_}
    writes it, and then, where it has members, the line break a struct
    would have closed them with. *)
let unenclosed_element enclosure ?fields body =
  let m = Cpp_ast.module_ enclosure ?fields body in
  if Cpp_ast.body_is_empty body then m else Cpp_ast.(seq [m; text (fnl ())])

(** [element_decl ~module_ env d] is the declaration [d], written as an
    element of the module [module_]: printed where the tree puts it
    ({!Cpp_ast.print}), but a wrapper struct holding a wrapper module's
    declarations, whose members are, and an assertion held back, which is
    nothing here: it is written after the struct holding it back
    ({!Cpp_print.held_back_assertions}). *)
let element_decl ~module_ env d =
  if Cpp_print.is_held_back_assertion d then Cpp_ast.empty
  else if Cpp_print.absorbs d then write_decl env d
  else Cpp_print.unprinted ~module_ env d

(** Pretty-print a structure element (label, elem) pair. Handles modules, module
    types, and declarations.

    @param is_header  When [true], emit header-mode output (struct definitions,
                      concept declarations, [using] aliases).  When [false],
                      emit implementation-mode output (out-of-line function
                      bodies, skipping header-only constructs).
    @param f          Callback used to pretty-print individual {!Miniml.ml_decl}
                      nodes; typically [impl_decls] or [header_decls].
    @param module_    The module whose body the element is an element of.
    @return The element written ({!written}): its text, empty if it
            produces no output in the current pass, and its concepts. *)
let rec pp_structure_elem ~is_header f ~module_ = function
  | l, SEdecl d ->
    (* {b Placement of lifted lambda helpers.}  A helper lifted out of a local
       [let g := fun ... in] that mentions the enclosing struct (its parameter
       types, or a sibling definition it calls) cannot be emitted before that
       struct, and emitting it after leaves the call site — which sits in a
       static data member initializer, {i not} a complete-class context —
       referring to an undeclared name.  Emit it as a static member template
       right before the declaration that produced it instead; helpers produced
       elsewhere keep their file-scope placement. *)
    let {Cpp_ind.rendered; helpers; _} = f ~module_ d in
    let element = element_decl ~module_ in
    (* An erasure landing pad -- [using X = std::any;] -- travels to the very
       top of the file, ahead of the concepts.

       It is correct there because it names nothing: the right-hand side is
       [std::any] and the parameters, if any, are its own.  It is {e needed}
       there because the text that lands on it does not follow it.  A concept
       body spells such a name bare, and concepts are hoisted to the top by the
       case below, so leaving the alias where it was written puts the use in
       front of the declaration.  Hoisting both and ordering them here is what
       makes that pair of placements independent of each other, and of any
       later pass that reorders the file.  It is planned there
       ({!file_layout}); here it is only left out. *)
    let body =
      if
        is_header
        && (not (!render_ctx).rc_in_struct)
        && rendered <> []
        && List.for_all is_erased_alias rendered
      then Cpp_ast.empty
      else Cpp_ast.concat fnl (List.map (fun (env, d) -> element env d) rendered)
    in
    (* A type class rendered at file scope is a concept, and a concept has no
       forward declaration to bridge a use that precedes it.  One such use is
       written unconditionally: a lifted helper's spec goes ahead of every
       section, because its callers are members of the struct it came out of,
       and its constraint names this concept.  So the concept travels to the
       top of the file, where the concepts of a nested module's type classes
       already go.

       Only at file scope: inside a struct the concept has already been
       hoisted or held back by {!pp_structure_elements}, which knows which of
       those two it is and this does not. *)
    let concepts, body =
      if
        is_header
        && (not (!render_ctx).rc_in_struct)
        && (not (!render_ctx).rc_concepts_hoisted)
        && (match d with
           | Miniml.Dind (_, ind) -> (
             match ind.ind_kind with Miniml.TypeClass _ -> true | _ -> false )
           | _ -> false)
        && not (Cpp_ast.is_empty body)
      then ([Cpp_ast.(seq [text (pp_doc_comment l); body])], Cpp_ast.empty)
      else ([], body)
    in
    (* The helpers are the ones planned for this element alone
       ({!Cpp_ind.header_claim}), each lifted once in the file. *)
    let member_lifted =
      if not is_header then Cpp_ast.empty
      else
        List.fold_left
          (fun acc d' ->
            (* Emitted after the struct this was lifted out of, so after the
               methods that call it.  The definition stays where it is and the
               declaration is planned at the top ({!file_layout}) -- the same
               repair as for a wrapper module's lifted helpers, on the path
               that produces them one at a time into a [Pp.t]. *)
            dbg_lifted ~site:"structure-elem"
              ~extra:
                (Printf.sprintf "rc_in_struct=%b" (!render_ctx).rc_in_struct)
              d';
            (* Only at namespace scope.  A struct is a complete-class
               context, so a method may call a member declared after it and a
               member has no forward reference to repair -- this pass has
               nothing to do there, whatever would be legal.

               Legality says the same thing the one time it is asked: a
               member's signature resolves against the struct, a nested [t] or
               a sibling type, and hoisting the declaration to file scope takes
               those names out of scope with it. *)
            let def, _ = lifted_views ~may_hoist:(not (!render_ctx).rc_in_struct) d' in
            let pp = element (empty_env ()) def in
            if Cpp_ast.is_empty pp then acc
            else if Cpp_ast.is_empty acc then pp
            else Cpp_ast.(seq [acc; text (cut2 ()); pp]) )
          Cpp_ast.empty
          helpers
    in
    let body =
      if Cpp_ast.is_empty member_lifted then body
      else if Cpp_ast.is_empty body then member_lifted
      else
        (* A helper lifted out of an inductive's own declaration comes from a
           definition that was turned into a method of that inductive, so it
           names the inductive in its parameter types and must follow it.  Its
           call sites are method bodies, which are complete-class contexts and
           so may name a member declared later. *)
        match d with
        | Miniml.Dind _ -> Cpp_ast.(seq [body; text (cut2 ()); member_lifted])
        | _ -> Cpp_ast.(seq [member_lifted; text (cut2 ()); body])
    in
    { text = (if Cpp_ast.is_empty body then Cpp_ast.empty else Cpp_ast.(seq [text (pp_doc_comment l); body]));
      concepts;
      asserts = List.concat_map (fun (_, d) -> Cpp_print.held_back_assertions d) rendered }
  | l, SEmodule m ->
    let mp = MPdot (module_, l) in
    let name =
      match m.ml_mod_expr with
      | MEident _ | MEapply _ ->
        (* Transparent aliases generate a [using X = Y;] alias in C++, named
           as references spell the module: a renamed one where another module
           shares the label ([OrdersEx.Positive_as_OT] beside
           [OrderedTypeEx.Positive_as_OT]). *)
        let s = Common.emitted_module_name mp in
        str (Table.escape_reserved_struct_name s)
      | _ -> Cpp_names.module_struct_name mp
    in
    (* A submodule becomes a nested struct, which shadows any global-scope type
       of the same name for unqualified lookups from inside the parent -- a
       [Module Nat] hides the runtime [Nat] exactly as an [Inductive Nat]
       would.  Record it so {!Cpp_names.global_scope_qualifier_for} spells the
       global one [::Nat]. *)
    if (!render_ctx).rc_in_struct then printed_nested_struct (Pp.string_of_ppcmds name) (NSmodule mp);
    let mod_pp =
      match m.ml_mod_expr with
      | MEfunctor _ ->
        if not is_header then
          written Cpp_ast.empty
        else
          let get_template_and_body = function
            | MEfunctor (mbid, mt, me) ->
              let rec collect_params mbid mt me =
                match me with
                | MEfunctor (mbid', mt', me') ->
                  let params_rest, body = collect_params mbid' mt' me' in
                  ((mbid, mt) :: params_rest, body)
                | _ -> ([(mbid, mt)], me)
              in
              collect_params mbid mt me
            | _ -> ([], m.ml_mod_expr)
          in
          let template_params, body = get_template_and_body m.ml_mod_expr in
          (* The module types the body declares cannot be concepts inside the
             class template the functor becomes: they go to file scope, over
             the functor's parameters too, under the functor's name. *)
          let concepts =
            match body with
            | MEstruct (body_mp, sel) ->
              let params = List.map (fun (mbid, _) -> MPbound mbid) template_params in
              List.filter_map
                (function
                  | l, SEmodtype mty ->
                    let path = MPdot (body_mp, l) in
                    let concept = Cpp_ind.modtype_concept ~module_ path ~params mty in
                    Some (Cpp_ast.modtype_concept ~path ~params concept)
                  | _ -> None )
                sel
            | _ -> []
          in
          let template = List.map template_param template_params in
          let {text = struct_def; concepts = body_concepts; asserts} =
            with_render_ctx
              (fun c -> { c with rc_in_struct = true; rc_in_template = true })
              (fun () ->
                match body with
                | MEstruct (body_mp, sel) ->
                  let b = pp_module_body ~is_header f body_mp sel in
                  { b with
                    text =
                      Cpp_ast.module_
                        (Struct {head = {template; name; base = None}; layout = Block})
                        b.text }
                (* A functor that is another module is a struct deriving
                   from it, as one applying another functor is. *)
                | MEapply _ -> written (Cpp_ast.derived_functor ~template ~name (Applied (application_of body)))
                | MEident mp -> written (Cpp_ast.derived_functor ~template ~name (Module_named mp))
                | MEfunctor _ -> CErrors.anomaly (Pp.str "Crane: a functor's parameters were not all collected.") )
          in
          { text = struct_def; concepts = concepts @ body_concepts; asserts }
      | MEapply _ ->
        if not is_header then
          written Cpp_ast.empty
        else
          let assertion, held = concept_assertion mp m.ml_mod_type in
          { text = Cpp_ast.seq [Cpp_ast.module_alias ~name (Applied (application_of m.ml_mod_expr)); assertion];
            concepts = [];
            asserts = held }
      | MEstruct (body_mp, sel) ->
        let old_context = (!render_ctx).rc_in_struct in
        with_module_frame @@ fun () ->
        let frame = Module_frame.planned mp in
        if
          Probe.checking ()
          && not
               (Module_frame.equal frame
                  (Module_frame.of_module mp ~name:(Pp.string_of_ppcmds name) sel
                     ~enclosing:!current_structure_decls ) )
        then
          Probe.violation "module frames"
            Pp.(str "the module " ++ str (ModPath.to_string mp)
                ++ str " is entered with another frame than planned");
        eponymous_type_ref := frame.eponymous_type;
        eponymous_record := frame.eponymous_record;
        method_candidates := frame.method_candidates;
        let this_eponymous_record = frame.eponymous_record in
        let has_concept_collision = frame.concept_collision in
        let class_concepts =
          if is_header then
            List.map
              (fun (l, r, fields) ->
                let d = generated_concept ~module_ r fields in
                let concept = class_concept_element ~module_ d in
                (HCclass r, Cpp_ast.(seq [text (pp_doc_comment l); concept]), concept_names_member mp d) )
              (declared_classes sel)
          else []
        in
        let modtype_concepts =
          if is_header then
            List.filter_map
              (fun (l, se) ->
                match se with
                | SEmodtype m ->
                  let path = MPdot (mp, l) in
                  let concept = Cpp_ind.modtype_concept ~module_ path ~params:[] m in
                  let concept_pp = Cpp_ast.modtype_concept ~path ~params:[] concept in
                  Some (HCmodtype path, concept_pp, Modtype_concept.names_member mp concept)
                | _ -> None )
              sel
          else
            []
        in
        (* The header declares the module's concepts where the walk ahead of
           the files planned them ({!Cpp_ind.concept_plan}); under
           [CRANE_CHECK_IR] the plan is checked against the concepts
           generated here. *)
        let plan = if is_header then Some (Cpp_ind.concept_plan mp) else None in
        if
          is_header && Probe.checking ()
          && not
               (Cpp_ind.equal_concept_plan (Option.get plan)
                  (Cpp_ind.plan_concepts ~nested:old_context
                     ~classes:(List.map (fun (c, _, names) -> (c, names)) class_concepts)
                     ~modtypes:(List.map (fun (c, _, names) -> (c, names)) modtype_concepts) ) )
        then
          Probe.violation "concept placements"
            Pp.(str "the module " ++ str (ModPath.to_string mp)
                ++ str " places its concepts otherwise than planned");
        let placed placement concepts =
          match plan with
          | None -> []
          | Some plan ->
            List.filter (fun (c, _, _) -> Cpp_ind.concept_placement plan c = placement) concepts
        in
        let docs = List.map (fun (_, c, _) -> c) in
        let own_concepts =
          docs (placed At_file_scope class_concepts) @ docs (placed At_file_scope modtype_concepts)
        in
        let typeclass_concepts = placed Ahead_of_struct class_concepts in
        let modtype_concepts_ahead = placed Ahead_of_struct modtype_concepts in
        let concepts_after =
          placed After_struct class_concepts @ placed After_struct modtype_concepts
        in
        let this_held_back = match plan with Some plan -> plan.held_back | None -> [] in
        let typeclasses_pp = Cpp_ast.concept_group Classes_ahead (docs typeclass_concepts) in
        let modtypes_pp = Cpp_ast.concept_group Module_types_ahead (docs modtype_concepts_ahead) in
        let modtypes_after_pp = Cpp_ast.concept_group After_struct (docs concepts_after) in
        (* Whether this module is outside every struct is a question about
           the module, not about the file: the implementation writes no
           struct around a nested module, but the header does, and promotes
           it only where none encloses it. *)
        if is_header && Probe.checking () && old_context = outside_every_struct mp then
          Probe.violation "promoted inductives"
            Pp.(
              str "the module " ++ str (ModPath.to_string mp)
              ++ str
                   ( if old_context then " is rendered inside a struct its plan says it is outside"
                     else " is rendered outside every struct where its plan says it is inside" ) );
        let is_promoted = frame.promoted <> None in
        let promoted_tparams = frame.promoted in
        (* Set the promotion state the body will be rendered under.  A
           promotion outlives this module -- every later mention of the
           inductive spells it the promoted way -- whereas the demotion a
           nested rendering needs lasts exactly as long as that rendering:
           the ones planned around its body ({!Cpp_ind.with_planned_demotions}). *)
        let with_promotion_scope body =
          if is_promoted then (
            eponymous_promote_ref := !eponymous_type_ref;
            Option.iter rendered_promotion !eponymous_type_ref );
          Cpp_ind.with_planned_demotions body_mp body
        in
        let promoted_template =
          is_promoted && match promoted_tparams with Some (_ :: _) -> true | _ -> false
        in
        (* Where the body of this module is rendered: inside the struct when
           the header spells it out, qualified by it in the implementation. *)
        (* The header writes the body in the scope planned for it
           ({!Cpp_ind.header_scope}): inside the struct unless a class concept
           takes the module's name, and with the concepts hoisted where this
           module or an enclosing one hoisted one.  Under [CRANE_CHECK_IR] the
           plan is checked against those two answers as this render reaches
           them. *)
        let enter_module c =
          if not is_header then c
          else
            match Cpp_ind.header_scope body_mp with
            | Some {in_struct; concepts_hoisted} ->
              if
                Probe.checking ()
                && ( in_struct <> (c.rc_in_struct || not has_concept_collision)
                   || concepts_hoisted <> (c.rc_concepts_hoisted || typeclass_concepts <> []) )
              then
                Probe.violation "header scopes"
                  Pp.(str "the module " ++ str (ModPath.to_string mp)
                      ++ str " is entered in another scope than planned");
              { c with
                rc_in_struct = in_struct;
                rc_concepts_hoisted = concepts_hoisted;
                (* A promoted module's template defines everything inline. *)
                rc_in_template =
                  c.rc_in_template || (promoted_template && not has_concept_collision) }
            | None ->
              CErrors.anomaly
                Pp.(str "Crane: the module " ++ str (ModPath.to_string mp)
                    ++ str " has no planned header scope.")
        in
        let body_written, this_method_candidates =
          with_promotion_scope @@ fun () ->
          with_render_ctx enter_module (fun () ->
            let body =
              setting held_back_concepts
                (Cpp_ind.planned_held_back ~file:(if is_header then Intf else Impl) body_mp)
                (fun () -> pp_module_body ~is_header f body_mp sel)
            in
            (body, !method_candidates) )
        in
        (* The assertions this struct's body held back: those naming a concept
           it declares are emitted after it, now that both are in scope; the
           rest travel further out.  Each names its subject from where it is
           written, which qualifies it by every struct it left. *)
        let mine, passed_out =
          List.partition (fun a -> is_held_back_in this_held_back (held_concept_of a)) body_written.asserts
        in
        let deferred_asserts_pp = Cpp_ast.seq (List.map Cpp_ast.assertion mine) in
        let body = body_written.text in
        (* Capture and clean up promotion state. *)
        let this_promoted = is_promoted in
        (* Whether the struct the eponymous inductive is promoted to derives
           from [enable_shared_from_this] is decided where the inductive was
           generated. *)
        let this_promote_sft =
          is_promoted
          && List.exists
               (function
                 | _, SEdecl (Dind (kn, _) as d) ->
                   (match !eponymous_type_ref with
                    | Some (GlobRef.IndRef (kn', _)) -> MutInd.CanOrd.equal kn kn'
                    | _ -> false)
                   && in_planned_visibility body_mp (fun () -> Cpp_ind.promoted_shared_from_this ~module_:body_mp d)
                 | _ -> false )
               sel
        in
        if is_promoted then eponymous_promote_ref := None;
        let text, own_held =
        if is_header then
          if this_promoted then
            (* Promoted module: the module struct IS the eponymous type. Wrap
               body in a template struct with the inductive's template params
               and emit deferred defs at file scope. *)
            let template =
              match promoted_tparams with
              | Some vars -> List.map (fun v -> Cpp_ast.Typename (Id.print (Common.tparam_name v))) vars
              | None -> []
            in
            let base =
              if this_promote_sft then
                let type_args =
                  match promoted_tparams with
                  | Some (_ :: _ as vars) ->
                    str "<"
                    ++ prlist_with_sep
                         (fun () -> str ", ")
                         (fun v -> Id.print (Common.tparam_name v))
                         vars
                    ++ str ">"
                  | _ -> mt ()
                in
                Some (str (sn ()).enable_from_this ++ str "<" ++ name ++ type_args ++ str ">")
              else
                None
            in
            let struct_def =
              Cpp_ast.module_
                (Struct {head = {template; name; base}; layout = Block})
                body
            in
            (Cpp_ast.seq [typeclasses_pp; modtypes_pp; struct_def; modtypes_after_pp; deferred_asserts_pp], [])
          else
            let template, record_fields_pp, record_methods_pp =
              match this_eponymous_record with
              | Some (epon_ref, fields, packet) ->
                let ty_vars = packet.ip_vars in
                let template = List.map (fun v -> Cpp_ast.Typename (Id.print v)) ty_vars in
                (* [fields] already pairs each projection with its type:
                   extraction selected the two together. *)
                let field_types = Cpp_ind.record_field_types ~module_ epon_ref ty_vars fields in
                let field_name i (field_ref, _) =
                  match field_ref with
                  | Some r -> Common.pp_global_name Term r
                  (* Index anonymous fields so multiple of them don't all
                     collapse to a single duplicate "_field" member (which
                     would not compile).  Matches gen_decls.ml. *)
                  | None -> "_field" ^ string_of_int i
                in
                let fields_pp =
                  Cpp_print.unprinted_fields ~module_ ~vl:ty_vars epon_ref
                    (List.combine (List.mapi field_name fields) field_types)
                in
                let method_fields, method_helpers =
                  generated_record_methods ~module_ epon_ref ty_vars
                    (record_method_candidates this_method_candidates)
                in
                (* A struct is a complete-class context, so a helper lifted out
                   of a method is a member that may follow the methods calling
                   it; it precedes them here. *)
                let helpers_pp =
                  Cpp_ast.seq
                    (List.map
                       (fun h ->
                         Cpp_ast.seq
                           [ Cpp_print.unprinted ~module_ (empty_env ()) (fst (lifted_views ~may_hoist:false h));
                             Cpp_ast.text (fnl ()) ] )
                       method_helpers )
                in
                let methods_pp =
                  if method_fields = [] then
                    Cpp_ast.empty
                  else
                    (* The record's methods are members of the module struct
                       it was merged into, and pass through every stage a
                       member does -- loopification, moves, the constraints
                       their bodies settle -- before they are printed. *)
                    let finished =
                      Cpp_ind.finished_record_methods epon_ref ty_vars method_fields
                    in
                    Cpp_ast.seq
                      [helpers_pp; Cpp_print.unprinted ~module_ (empty_env ()) finished; Cpp_ast.text (fnl ())]
                in
                (template, fields_pp, methods_pp)
              | None -> ([], Cpp_ast.empty, Cpp_ast.empty)
            in
            (* The record's fields and methods are members of the module's
               struct, but written as elements of the module it is an
               element of, in that body's visibility: they are planned
               there ({!plan_ctor_aliases}), and a type they name that the
               struct declares later means, in front of that declaration,
               what it means outside. *)
            let fields = Cpp_ast.elements ~source:module_ (Cpp_ast.seq [record_fields_pp; record_methods_pp]) in
            if has_concept_collision then
              (Cpp_ast.seq [typeclasses_pp; modtypes_pp; unenclosed_element In_enclosing_scope ~fields body], [])
            else if Cpp_ast.body_is_empty body && Cpp_ast.is_empty fields then
              (* Empty module: emit [struct Name {};] even though there are
                 no declarations.  The struct may be needed as a template
                 argument in functor instantiations, e.g.
                 [using M_ = M<Empty>;] where [Empty] was defined as an
                 empty Rocq module satisfying some module type.  Previously
                 this returned [mt ()] which suppressed the struct
                 entirely, causing undeclared-identifier errors. *)
              (Cpp_ast.module_ (Struct {head = {template; name; base = None}; layout = One_line}) body, [])
            else
              let struct_def =
                Cpp_ast.module_
                  (Struct {head = {template; name; base = None}; layout = Block})
                  ~fields body
              in
              let assertion, held = concept_assertion mp m.ml_mod_type in
              ( Cpp_ast.seq [typeclasses_pp; modtypes_pp; struct_def; modtypes_after_pp; deferred_asserts_pp; assertion],
                held )
        else if this_promoted && promoted_template then
          (* A promoted template's members are all defined inline in the
             header. *)
          (Cpp_ast.empty, [])
        else
          (unenclosed_element Out_of_line body, [])
        in
        {text; concepts = own_concepts @ body_written.concepts; asserts = passed_out @ own_held}
      | MEident target ->
        if not is_header then written Cpp_ast.empty
        else
          (* Rocq's extraction reduces [Module Facts (M : WS) := WFacts M.] to
             [MEident WFacts] with a functor's type: the alias is a template
             over the functor's parameters, [WFacts] being one too. *)
          let rec functor_params = function
            | MTfunsig (mbid, mt, rest) -> (template_param (mbid, mt), MPbound mbid) :: functor_params rest
            | _ -> []
          in
          match functor_params m.ml_mod_type with
          (* A file module is a namespace, which no alias in a struct can
             name. *)
          | [] when is_modfile target && (!render_ctx).rc_in_struct -> written Cpp_ast.empty
          | [] -> written (Cpp_ast.module_alias ~name (Module_named target))
          | params ->
            written (Cpp_ast.functor_alias ~name target params)
    in
    { mod_pp with
      text =
        (if Cpp_ast.is_empty mod_pp.text then Cpp_ast.empty else Cpp_ast.(seq [text (pp_doc_comment l); mod_pp.text]))
    }
  | l, SEmodtype m ->
    written
      ( if (not is_header) || (!render_ctx).rc_in_struct then Cpp_ast.empty
        else
          let path = MPdot (module_, l) in
          let concept = Cpp_ind.modtype_concept ~module_ path ~params:[] m in
          Cpp_ast.modtype_concept ~path ~params:[] concept )

(** The body of the module [mp] of elements [sel], each element a member of
    it, written in the visibility planned for it ({!in_planned_visibility}). *)
and pp_module_body ~is_header f mp sel =
  if is_header && Probe.checking () && (!render_ctx).rc_in_template <> Scope_plan.templated mp then
    Probe.violation "templated modules"
      Pp.(
        str "the module " ++ str (ModPath.to_string mp)
        ++ str
             ( if (!render_ctx).rc_in_template then " is written in a class template its plan says it is outside"
               else " is written outside every class template where its plan says it is inside" ) );
  if is_header && Probe.checking () then begin
    let c = !render_ctx in
    match Cpp_ind.header_scope mp with
    | Some {in_struct; concepts_hoisted} when in_struct = c.rc_in_struct && concepts_hoisted = c.rc_concepts_hoisted
      -> ()
    | Some _ ->
      Probe.violation "header scopes"
        Pp.(str "the module " ++ str (ModPath.to_string mp) ++ str " is written in another scope than its plan says")
    | None ->
      Probe.violation "header scopes" Pp.(str "the module " ++ str (ModPath.to_string mp) ++ str " has no planned scope")
  end;
  in_planned_visibility mp @@ fun () ->
  let old_structure_decls = !current_structure_decls in
  current_structure_decls := sel;
  Cpp_ind.with_planned_local_inductives mp @@ fun () ->
  (* A synthesised alias whose body names this module's own types, as its
     members spell them, is declared inside the struct, in front of the
     first member that writes it (see {!Cpp_print.ctor_alias_home}): at
     namespace scope those names mean nothing. *)
  let written =
    List.map (fun e -> element_of mp (writing_element_of mp (fun () -> pp_structure_elem ~is_header f ~module_:mp e))) sel
  in
  current_structure_decls := old_structure_decls;
  { text = Cpp_ast.module_body mp (List.map (fun w -> w.text) written);
    concepts = List.concat_map (fun w -> w.concepts) written;
    asserts = List.concat_map (fun w -> w.asserts) written }

(** [joined f l] writes each of [l] as [f] does, the non-empty ones joined
    ({!Cpp_ast.joined}). *)
let joined f l = Cpp_ast.joined (List.map f l)

(** The declarations and definitions generated functions contribute to the
    file being written, grouped as [gens] is: each one's declaration always,
    its definition only in the file that holds it.

    Every definition is split as it was finished ahead of the files
    ({!Cpp_ind.finalized}). *)
let file_views ~is_header (gens : Gen_decls.generated_fun list list) =
  let views ((g : Gen_decls.generated_fun), entity) =
    let with_env d = (d, g.gf_env) in
    match (g.gf_entity, entity) with
    | Defined (_, file), Some e ->
      ( [with_env (Function_entity.declaration e)],
        if (file = Gen_decls.Header) = is_header then
          [with_env (Function_entity.definition_after_declaration e)]
        else [] )
    | Declared d, _ -> ([with_env (Cpp_ind.finished_alone d)], [])
    | Defined _, None -> assert false
  in
  let rec regroup gens views =
    match gens with
    | [] -> []
    | gs :: gens ->
      let mine, rest = List.chop (List.length gs) views in
      (List.concat_map fst mine, List.concat_map snd mine) :: regroup gens rest
  in
  regroup gens (List.map views (Cpp_ind.finalized (List.concat gens)))

(** What a function element of a wrapper module is, for generating it. *)
type wrapper_element =
  | Wrapper_functions of GlobRef.t * (unit -> Gen_decls.generated_fun list)
      (** Functions, generated by the thunk once for both files
          ({!Cpp_ind.generated_once}), and recorded under the reference
          where their declaration names none. *)
  | Wrapper_instance of GlobRef.t * ml_ast * ml_type
      (** A type-class instance.  It is a struct, and it is named from
          wherever its class is used -- unqualified, because a concept's
          template argument is a type, not a member of whatever module
          happened to declare it.  So it is lifted out of the wrapper's
          struct to namespace scope, exactly as an instance declared at the
          extraction root is emitted.  Only the header writes it, so only the
          header generates it, as at the root ({!Cpp_ind.generate}). *)
  | Wrapper_nothing  (** Written elsewhere, or not at all. *)

(** [wrapper_element ~module_ se], an element of the wrapper module
    [module_], whose functions are generated as its.  An inline custom, a
    projection merged into or
    suppressed from a record, and a function registered as a method of some
    type -- which is generated with that type -- generate nothing here; nor
    does a monadic constant, which no render generates.  A method candidate
    is a registered method ({!Method_registry.planned_candidate}). *)
let wrapper_element ~module_ se =
  match se with
  | SEdecl (Dterm (r, _, _))
    when is_any_inline_custom r || is_eponymous_record_projection r
         || is_suppressed_projection r || is_registered_method r <> None ->
    Wrapper_nothing
  | SEdecl (Dterm (_, _, Tglob (ty, _, _))) when is_monad ty -> Wrapper_nothing
  | SEdecl (Dterm (r, a, t)) when is_typeclass_instance a t -> Wrapper_instance (r, a, t)
  | SEdecl (Dterm (r, a, t)) ->
    Wrapper_functions (r, fun () -> generated_once ~module_ se (fun () -> [gen_decl_for_pp_dual r a t]))
  | SEdecl (Dfix fds) -> (
    match filter_dfix fds with
    | [] -> Wrapper_nothing
    | {fd_ref; _} :: _ as fds ->
      Wrapper_functions (fd_ref, fun () -> generated_once ~module_ se (fun () -> gen_dfuns_dual fds)) )
  | _ -> Wrapper_nothing

(** Process a wrapper module in dual-pass mode (header vs implementation).

    PASS 1 (is_header=true): Emit forward declarations (specs) for functions.
    PASS 2 (is_header=false): Emit full definitions (defs) for functions.

    Each function is generated once, independent of the file; [is_header]
    only picks which of its views this file writes ({!file_views}).

    @param is_header   When [true] produce declaration specs; when [false]
                       produce out-of-line definitions, each qualified by the
                       scope its plan gives it ({!Scope_plan}).
    @param func_sels   The [(label, structure_elem)] pairs from the wrapper
                       that contain function declarations ([Dterm], [Dfix]).
    @param mp          The wrapper module.
    @return A quadruple [(specs, defs_pp, lifted_pp, lifted_specs_pp)] where
            [specs] is the header pass's body of the module's struct, each
            element's declarations a member of it, and nothing in the
            implementation, which writes no struct, [defs_pp] the
            implementation-pass definition block, [lifted_pp] any top-level
            declarations that were lifted out of local function bodies during
            translation, and [lifted_specs_pp] the forward declarations of the
            functions among those, which are due before the struct rather than
            after it. *)
let pp_wrapper_module_dual ~is_header mp func_sels =
  let process_sel (_l, se) =
    match wrapper_element ~module_:mp se with
    | Wrapper_nothing -> ([], [])
    | Wrapper_instance _ when not is_header -> ([], [])
    | Wrapper_instance (r, a, t) ->
      (* The helpers lifted out of its methods come first: the instance
         struct calls them. *)
      let ds, helpers = Cpp_ind.instance_entity ~module_:mp r a t in
      ([], helpers @ List.map snd ds)
    | Wrapper_functions (fallback, generate) ->
      let gs = generate () in
      record_funs ~fallback gs;
      let lifted = List.concat_map (fun g -> g.gf_lifted) gs in
      List.iter (dbg_lifted ~site:"wrapper-dterm") lifted;
      (gs, lifted)
  in
  let generated = List.map process_sel func_sels in
  let all_results = file_views ~is_header (List.map fst generated) in
  let all_lifted = List.concat_map snd generated in
  (* The declarations of its functions are members of its struct -- its
     own, or one an inductive of its name writes -- and everything else it
     writes is an element of it, all printed as the tree spells them. *)
  let render_sel_specs (specs, _) =
    Cpp_ast.concat fnl (List.map (fun (d, env) -> Cpp_print.unprinted ~module_:mp env d) specs)
  in
  let element = element_decl ~module_:mp in
  let render_sel_defs (_, defs) = Cpp_ast.concat fnl (List.map (fun (d, env) -> element env d) defs) in
  let specs = Cpp_ast.module_body mp (if is_header then List.map render_sel_specs all_results else []) in
  let defs_pp = joined render_sel_defs all_results in
  (* A lifted helper is emitted after the struct it was lifted out of, and its
     callers are inside that struct, so by the time the definition appears the
     name has already been used.  A wrapper struct's own members do not have
     this problem -- {!gen_dfuns_dual} declares them all before defining any --
     and this is the same repair for the one kind of function that path never
     reaches, because it is not a member.  Only functions: a lifted struct is
     already forward-declared where structs are, and a declaration of anything
     else is either illegal or a second definition.

     Both halves come out of one split so they state one template head, and the
     definition emitted here is the split's, not the one that went in.  Only
     the header writes either. *)
  let lifted_split =
    if is_header then List.map lifted_views all_lifted else []
  in
  let lifted_pp = joined (fun (def, _) -> element (empty_env ()) def) lifted_split in
  let lifted_specs_pp = joined (element (empty_env ())) (List.filter_map snd lifted_split) in
  let elements = Cpp_ast.elements ~source:mp in
  (specs, elements defs_pp, elements lifted_pp, elements lifted_specs_pp)

(** What analysing the structure concluded, for the passes that render it. *)
let structure_analysis : Structure_analysis.t option ref = ref None

(** The analysis of the structure being rendered.

    Absent means a pass was started without {!prepare_structure}, which is a
    bug in the caller rather than a structure with nothing to say. *)
let get_structure_analysis () =
  match !structure_analysis with
  | Some a -> a
  | None ->
    CErrors.anomaly (Pp.str "cpp: rendering a structure that was never analysed")

(** The module plan a structure analysis decides, with the functor concept
    scopes, which rendering reads from here, installed.

    Every field of {!Structure_analysis.t} but [sorted_modules] exists to be
    read while rendering, so they are all taken here: rendering only ever
    reads what they decide, and so cannot render a use before the decision it
    depends on has been made.  The record is destructured field by field under
    warning 9, which is what makes a field added to the analysis and not
    handled here a compile error rather than a decision nothing acts on. *)
let module_plan_of_analysis
    ({ sorted_modules;
       global_scope_enums;
       collision_wrappers;
       wrapper_bystanders;
       functor_app_sources;
       eponymous_records;
       functor_concept_scopes = scopes;
       concept_renames;
       modtype_concept_renames;
       lifted_instances;
       _ } :
      Structure_analysis.t ) : Module_plan.t =
  functor_concept_scopes := scopes;
  let wrapped =
    List.filter_map
      (fun (mi : Structure_analysis.module_info) ->
        Option.map (fun name -> (mi, name)) mi.wrapper_name )
      sorted_modules
  in
  { global_scope_enums;
      concept_names = concept_renames;
      modtype_concept_names = modtype_concept_renames;
      functor_app_sources;
      eponymous_records;
      namespace_scope_refs = lifted_instances;
      wrappers =
        List.map (fun (mp, name) -> (mp, name, Some Module_plan.Flattened)) collision_wrappers
        (* A bystander is nested inside the wrapper, not flattened into it. *)
        @ List.map (fun (mp, name) -> (mp, name, Some Module_plan.Bystander)) wrapper_bystanders
        @ List.map (fun ((mi : Structure_analysis.module_info), name) -> (mi.modpath, name, None)) wrapped;
      (* Not everything a wrapper module declares ends up inside the wrapper
         struct.  A type alias is emitted at global C++ scope as
         [using T = ...;], and a type class instance is lifted out to namespace
         scope by [process_sel] below, for the reason recorded there.  Either
         way {!Cpp_names.struct_qualifier_for} must not write [Wrapper::] in
         front of the name in the .cpp file.  Which module a declaration is
         emitted in is layout, so it is settled here rather than while
         emitting it. *)
      global_scope_types =
        List.concat_map
          (fun ((mi : Structure_analysis.module_info), _) ->
            List.filter_map
              (fun (_l, se) ->
                match se with
                | SEdecl (Dtype (r, _, _)) -> Some r
                | SEdecl (Dterm (r, a, t)) when is_typeclass_instance a t -> Some r
                | _ -> None )
              mi.sels )
          wrapped;
      (* Planned once the wrappers holding declarations are
         ({!plan_concept_prerequisites}). *)
      concept_prerequisites = [] }

(** Decide everything about the structure that does not depend on which file is
    being written, record what rendering reads of it here, and return its
    {!Module_plan} -- the layout -- for the target plan to hold.

    {!Structure_analysis} describes itself as running before rendering, and the
    tables it fills are read by both the header and the implementation; it was
    nonetheless invoked from inside the renderer, so the same conclusions were
    reached four times per unit and the last one silently won.  Reaching them
    once, here, is what lets the layout be planned before anything renders.

    It runs where a rendering pass starts, the unit's files visible: the
    analysis is a function of the structure, but the helpers it calls read
    the visibility, and this is a relocation, not a re-derivation. *)
let prepare_structure s =
  let initial_mps =
    List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s
  in
  let analysis =
    with_visibility (toplevel_visibility initial_mps) @@ fun () ->
    Common.detect_sibling_module_inductive_collisions s;
  method_registry :=
    Some
      ( match !global_method_registry with
      | Some reg -> reg
      | None ->
        Method_registry.create
          ~ret_is_erased:Translation.return_type_is_erased s );
  let analysis = Structure_analysis.analyze (get_method_registry ()) s in
  (* Whether an inductive is a flat struct, and whether a type is an axiom,
     are properties of their declarations; every reader, before or after the
     declaration is generated, gets one answer. *)
  Modutil.struct_iter
    (function
      | Dind (kn, ind) ->
        Array.iteri
          (fun i _ ->
            let r = GlobRef.IndRef (kn, i) in
            if Table.is_flat_inductive_packet kn ind i then
              Table.add_flat_inductive r )
          ind.ind_packets
      | Dtype (r, _, Taxiom) when (not (is_any_inline_custom r)) && Table.singleton_class_method r = None ->
        Cpp_erasure.register_axiom_type r;
        Table.add_erased_type_const r
      | _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    s;
    name_cache := Some (Name_resolution.create ~structure_analysis:analysis s);
    analysis
  in
  structure_analysis := Some analysis;
  module_plan_of_analysis analysis

(** The functions registered as methods of each packet of the inductive
    [kn] -- its projections apart, which its struct declares itself --, each
    with the packet's reference and the variables it is generated at: an
    eponymous record's own declaration's, which its methods are generated
    with, and otherwise those of the inductive's struct.  The candidates of a
    packet come in [order]. *)
let registered_methods ?(order = Fun.id) kn ind =
  let analysis = get_structure_analysis () in
  List.concat
    (List.mapi
       (fun i p ->
         let ind_ref = GlobRef.IndRef (kn, i) in
         if is_custom ind_ref || is_monad ind_ref then []
         else
           let vars =
             if List.exists (globref_equal ind_ref) analysis.eponymous_records then p.ip_vars
             else Common.ind_struct_tparams kn ind p
           in
           List.filter_map
             (fun ((r, _, _, _) as candidate) ->
               if Table.is_projection r then None else Some (ind_ref, vars, candidate) )
             (order (Method_registry.get_candidates (get_method_registry ()) ind_ref)) )
       (Array.to_list ind.ind_packets) )

(** [walk_as_rendered ?reversed ~decl s] calls [decl ~wrapper ~module_ se]
    at each declaration element [se] of [s], an element of the module
    [module_], in the order the renders reach them or,
    if [reversed], the reverse, with what generating a declaration reads of
    the render's walk set as the render sets it: the visibility, the
    inductives local to the enclosing modules, the declarations of the
    structure being walked, and each module's frame ({!Module_frame}).  The
    scope the header writes each module's body in is planned on the way
    ({!Cpp_ind.plan_header_scope}), from the module's frame and whether its
    class concepts, generated here ({!Cpp_ind.concept}), name its members.
    [wrapper] says [se] is
    one of a wrapper module's own elements, which a render generates as the
    wrapper's ({!pp_wrapper_module_dual}), before any inductive is made
    local; [after_wrapper ()] once a wrapper module's elements have all
    been walked, still inside it; [classes ~module_ cs] at the classes [cs]
    whose concepts the header writes outside the struct declaring them, as
    elements of [module_]: a module's, as {!declared_classes} gives them, just
    before [after_module], and a collision struct's own, once its elements
    have all been walked, still inside its file module, which they are
    elements of; [after_module ~module_ frame sel] once
    the body of a module of elements [sel], an element of [module_], has
    been walked, still in its frame [frame] but no longer inside it;
    [in_body ~wrapper mp sel] once the elements
    [sel] of a module [mp] written as a struct -- a wrapper module, or a
    module of the unit's -- have all been walked, still inside it;
    [modtype ~module_ path ~params mt] at each module type
    [mt] whose concept the header writes, where it writes it: a module's
    in its frame, a top-level one in place, a functor body's at the
    functor, each generated as an element of the module whose element the
    module type, module or functor is.  A
    functor's body is walked as the class
    template it becomes,
    its parameters visible in it.  Each module is walked in the visibility
    planned for it ({!in_planned_visibility}), as the render writes it. *)
let walk_as_rendered ?(reversed = false) ?(after_wrapper = ignore) ?(classes = fun ~module_:_ _ -> ())
    ?(after_module = fun ~module_:_ _ _ -> ()) ?(in_body = fun ~wrapper:_ _ _ -> ())
    ?(modtype = fun ~module_:_ _ ~params mt -> Modtype_concept.generate ~params mt)
    ~decl s =
  let order l = if reversed then List.rev l else l in
  let analysis = get_structure_analysis () in
  let header = ref {Cpp_ind.in_struct = false; concepts_hoisted = false} in
  let in_module mp sel k =
    Cpp_ind.plan_header_scope mp !header;
    in_planned_visibility mp @@ fun () -> setting current_structure_decls sel k
  in
  let in_header_scope scope k = setting header scope k in
  let modtypes ~module_ mp ~params sel =
    List.filter_map
      (function l, SEmodtype m -> Some (MPdot (mp, l), modtype ~module_ (MPdot (mp, l)) ~params m) | _ -> None)
      sel
  in
  (* A module's frame, as the render enters its body: the eponymous state
     and promotion the frame says, and the header's scope worked out as the
     header works it out ({!pp_structure_elem}), from whether the module's
     class concepts name its members. *)
  let in_module_frame ~module_ mp sel k =
    let name = Table.escape_reserved_struct_name (Common.pp_module mp) in
    let frame = Module_frame.of_module mp ~name sel ~enclosing:!current_structure_decls in
    Module_frame.plan mp frame;
    let outer = !header in
    let class_concepts =
      List.map
        (fun (_, r, fields) -> (HCclass r, concept_names_member mp (Cpp_ind.concept ~module_ r fields)))
        (declared_classes sel)
    in
    let hoisted_here = (not outer.in_struct) && List.exists (fun (_, names) -> not names) class_concepts in
    let scope =
      { Cpp_ind.in_struct = outer.in_struct || not frame.concept_collision;
        concepts_hoisted = outer.concepts_hoisted || hoisted_here }
    in
    with_module_frame @@ fun () ->
    eponymous_type_ref := frame.eponymous_type;
    eponymous_record := frame.eponymous_record;
    method_candidates := frame.method_candidates;
    let modtypes =
      List.map
        (fun (path, c) -> (HCmodtype path, Modtype_concept.names_member mp c))
        (modtypes ~module_ mp ~params:[] sel)
    in
    Cpp_ind.plan_module_concepts mp (Cpp_ind.plan_concepts ~nested:outer.in_struct ~classes:class_concepts ~modtypes);
    let with_promotion k =
      match frame.promoted with
      | Some _ -> setting eponymous_promote_ref frame.eponymous_type k
      | None -> Table.with_demoted_inductive frame.eponymous_type k
    in
    with_promotion (fun () -> in_header_scope scope k);
    classes ~module_ (declared_classes sel);
    after_module ~module_ frame sel
  in
  let rec elem ~wrapper ~module_ (l, se) =
    match se with
    | SEdecl _ -> decl ~wrapper ~module_ se
    | SEmodule {ml_mod_expr = MEfunctor _ as me; _} ->
      let rec split params = function
        | MEfunctor (mbid, _, me) -> split (params @ [MPbound mbid]) me
        | body -> (params, body)
      in
      let params, body = split [] me in
      (match body with MEstruct (body_mp, sel) -> ignore (modtypes ~module_ body_mp ~params sel) | _ -> ());
      with_render_ctx
        (fun c -> {c with rc_in_struct = true; rc_in_template = true})
        (fun () ->
          in_header_scope {!header with in_struct = true} (fun () -> module_expr body) )
    | SEmodule {ml_mod_expr = MEstruct (_, sel) as me; _} ->
      in_module_frame ~module_ (MPdot (module_, l)) sel (fun () -> module_expr me)
    | SEmodule {ml_mod_expr; _} -> module_expr ml_mod_expr
    | SEmodtype m -> ignore (modtype ~module_ (MPdot (module_, l)) ~params:[] m)
  and module_expr = function
    | MEstruct (mp, sel) ->
      in_module mp sel (fun () ->
          with_local_inductives (inductives_declared_in mp sel) (fun () ->
              List.iter (elem ~wrapper:false ~module_:mp) (order sel);
              in_body ~wrapper:false mp sel ) )
    | MEident _ | MEapply _ | MEfunctor _ -> ()
  in
  with_visibility (toplevel_visibility (List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s))
  @@ fun () ->
  List.iter
    (fun (mi : Structure_analysis.module_info) ->
      if mi.wrapper_name <> None then
        in_module mi.modpath mi.sels (fun () ->
            List.iter (elem ~wrapper:true ~module_:mi.modpath) (order mi.sels);
            after_wrapper ();
            in_body ~wrapper:true mi.modpath mi.sels ) )
    (order analysis.sorted_modules);
  with_local_inductives (file_local_inductives analysis) (fun () ->
      List.iter
        (fun (mi : Structure_analysis.module_info) ->
          if mi.wrapper_name = None then
            let collision = wraps_children mi.modpath mi.sels in
            in_header_scope {!header with in_struct = collision} (fun () ->
                in_module mi.modpath mi.sels (fun () ->
                    List.iter (elem ~wrapper:false ~module_:mi.modpath) (order mi.sels);
                    if collision then classes ~module_:mi.modpath (declared_classes mi.sels) ) ) )
        (order analysis.sorted_modules) )

(** The callable plan of each function the renders will generate, in the
    order of the unit's modules and declarations, or the reverse if
    [reversed]: planned before anything is rendered
    ({!Gen_decls.plan_function}), so that a call rendered ahead of its callee
    reads the head the callee is declared with.

    The modules are walked as a render walks them, for the two things a head
    is converted against: the visibility, and the inductives local to
    the enclosing modules.  Only what a render generates as a function is
    planned: a method, a projection, an inline custom and an alias's copy are
    not, and neither is a wrapper module's monadic constant, which no render
    generates at all.  Planning one of those would hand its call sites a head
    other than the one they assume; missing one is reported when it is
    generated ({!Callable_abi.check}).

    An instance's struct is planned beside, each of its methods by name
    ({!Cpp_ind.plan_instance_methods}).

    A method is planned where its inductive is declared, for each function
    registered as one ({!Gen_decls.plan_method}): at the variables of an
    eponymous record's own declaration, which its methods are generated
    with, and otherwise at those of the inductive's struct. *)
let plan_callables ?(reversed = false) s =
  let order l = if reversed then List.rev l else l in
  let plans = ref [] in
  let instance_plans = ref [] in
  let plan ~fixpoint r a t =
    if not (is_any_inline_custom r || Table.is_projection r || is_registered_method r <> None)
    then Option.iter (fun abi -> plans := abi :: !plans) (Gen_decls.plan_function ~fixpoint r a t)
  in
  let plan_methods kn ind =
    List.iter
      (fun (ind_ref, vars, candidate) ->
        plans := Gen_decls.plan_method ind_ref vars candidate :: !plans )
      (registered_methods ~order kn ind)
  in
  (* A monadic constant is generated as a recursive group of one. *)
  let plan_decl ~wrapper = function
    | Dterm (r, a, (Tglob (ty, _, _) as t)) when is_monad ty ->
      if not wrapper then plan ~fixpoint:true r a t
    | Dterm (r, a, t) when not (is_typeclass_instance a t) -> plan ~fixpoint:false r a t
    | Dterm (r, a, t) -> instance_plans := (r, Cpp_ind.plan_instance_methods r a t) :: !instance_plans
    | Dfix fds ->
      List.iter (fun fd -> plan ~fixpoint:true fd.fd_ref fd.fd_body fd.fd_type) (order fds)
    | Dind (kn, ind) -> plan_methods kn ind
    | Dtype _ -> ()
  in
  walk_as_rendered ~reversed
    ~decl:(fun ~wrapper ~module_:_ -> function SEdecl d -> plan_decl ~wrapper d | _ -> ())
    s;
  (List.rev !plans, List.rev !instance_plans)

(** The eponymous record of a module of frame [frame] that the header merges
    into the module's struct, with its fields and packet, if it has one: a
    record merged into a struct that is not a promoted inductive's. *)
let merged_eponymous_record (frame : Module_frame.t) =
  match frame.eponymous_record with
  | Some record when frame.promoted = None -> Some record
  | Some _ | None -> None

(** The record, variables and candidates of the methods the header gives
    the eponymous record of a module of frame [frame], if it gives any. *)
let eponymous_record_methods (frame : Module_frame.t) =
  Option.map
    (fun (r, _, packet) -> (r, packet.ip_vars, record_method_candidates frame.method_candidates))
    (merged_eponymous_record frame)

(** Convert the types of the fields the header writes for the eponymous
    record of a module of frame [frame], if it writes any. *)
let convert_eponymous_record_fields ~module_ frame =
  Option.iter
    (fun (r, fields, packet) -> ignore (Cpp_ind.record_field_types ~module_ r packet.ip_vars fields))
    (merged_eponymous_record frame)

(** Generate every declaration the renders write before either file is
    rendered (docs/Pipeline-Disentangling-Plan.md, Milestones 1, 8 and 9):
    each declaration as {!Cpp_ind.generate} generates it, each of a wrapper
    module's own as {!pp_wrapper_module_dual} does, in the module the render
    generates it in, an inductive, an alias and a concept in the scope the
    header writes their module in.  What is generated is recorded for both
    files ({!Cpp_ind.generating_ahead}); the renders take it from there. *)
let generating_ahead f =
  init_std_names ();
  Cpp_ind.generating_ahead f

(** What finishing [aheads] takes: what each generated, in the order
    generated, and then the helpers lifted out of them, once every function
    they may call is finished. *)
let finishing (aheads : Cpp_ind.ahead list) =
  List.concat_map (fun (a : Cpp_ind.ahead) -> a.finishing) aheads
  @ List.concat_map (fun (a : Cpp_ind.ahead) -> List.map Cpp_ind.finishing a.helpers) aheads

(** Record the unit's program ({!Generated_program.record_ahead}) and finish
    what was generated ahead, [aheads] in the order generated, all at once
    ({!Finished_program.finish}), installing the program: every function,
    and every helper Loopify transforms, registered with Loopify before any
    is finished, so that what it sees of the unit does not depend on which
    were finished before.  Then demand every header the files will need for
    what they write ({!Cpp_demands}): the finished program's, and those of
    the module-type concepts and eponymous record fields generated ahead of
    them. *)
let finish_ahead (aheads : Cpp_ind.ahead list) =
  List.iter (fun (a : Cpp_ind.ahead) -> List.iter Generated_program.record_ahead a.entities) aheads;
  let helpers = List.concat_map (fun (a : Cpp_ind.ahead) -> a.helpers) aheads in
  Generated_program.record_lifted_ahead helpers;
  List.iter (fun (a : Cpp_ind.ahead) -> List.iter Loopify.register_decl a.functions) aheads;
  List.iter (fun h -> if Cpp_pipeline.should_loopify h then Loopify.register_decl h) helpers;
  let program = Finished_program.finish (finishing aheads) in
  Finished_program.install program;
  List.iter Table.demand_header
    (Finished_program.demands program
    @ List.concat_map Cpp_demands.of_modtype_concept (Cpp_ind.generated_concepts ())
    @ List.concat_map Cpp_demands.of_type (Cpp_ind.generated_record_field_types ()))

let generate_decl_ahead ~module_ d = generating_ahead @@ fun () -> finish_ahead [Cpp_ind.generate_ahead ~module_ d]

(** The files the unit [s]'s names are written through, read off what was
    generated ahead of its files where the printer writes it
    ({!Cpp_demands.globals_of_decl}): the installed finished program's, and
    the types of the eponymous record fields generated with it. *)
let files_named_ahead s =
  let unit_files = List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s in
  Finished_program.installed_globals ()
  @ List.concat_map Cpp_demands.globals_of_type (Cpp_ind.generated_record_field_types ())
  |> List.filter_map (Common.file_named_by ~unit_files)
  |> List.sort_uniq ModPath.compare

let generate_ahead s =
  generating_ahead @@ fun () ->
  (* Everything is generated first, and finished after ({!finish_ahead}).  A
     wrapper's functions are finished as one group, as {!file_views} finishes
     them. *)
  let wrapper_functions = ref [] in
  let aheads = ref [] in
  let later (a : Cpp_ind.ahead) = aheads := a :: !aheads in
  let lifted helpers = later {Cpp_ind.entities = []; functions = []; finishing = []; helpers} in
  walk_as_rendered ~modtype:Cpp_ind.modtype_concept
    ~classes:(fun ~module_ ->
      List.iter (fun (_, r, fields) ->
          let d = Cpp_ind.concept ~module_ r fields in
          later
            { entities = [Cpp_ind.entity r [d] []];
              functions = [];
              finishing = [Cpp_ind.finishing d];
              helpers = [] } ) )
    ~after_module:(fun ~module_ frame _ ->
      convert_eponymous_record_fields ~module_ frame;
      Option.iter
        (fun (r, vars, candidates) ->
          let fields, hs = Cpp_ind.record_methods ~module_ r vars candidates in
          later
            { entities = record_method_entities r fields hs;
              functions = [];
              finishing =
                (if fields <> [] then [Cpp_ind.record_methods_finishing r vars fields] else []);
              helpers = hs } )
        (eponymous_record_methods frame) )
    ~after_wrapper:(fun () ->
      let elements = List.rev !wrapper_functions in
      later
        (Cpp_ind.functions_ahead
           ~entities:
             (List.concat_map
                (fun (fallback, gs) -> Cpp_ind.funs_entities ~fallback gs)
                elements )
           (List.concat_map snd elements) );
      wrapper_functions := [] )
    ~decl:(fun ~wrapper ~module_ se ->
      match se with
      | SEdecl (Dind (kn, ind) as d) ->
        List.iter
          (fun (ind_ref, vars, candidate) ->
            lifted (Gen_decls.generate_method_ahead ind_ref vars candidate) )
          (registered_methods kn ind);
        later (Cpp_ind.generate_ahead ~module_ d)
      | SEdecl (Dtype _ as d) -> later (Cpp_ind.generate_ahead ~module_ d)
      | _ when wrapper -> (
        match wrapper_element ~module_ se with
        | Wrapper_functions (fallback, generate) ->
          wrapper_functions := (fallback, generate ()) :: !wrapper_functions
        | Wrapper_instance (r, a, t) ->
          (* Lifted out of the wrapper whole, after its helpers. *)
          let ds, hs = Cpp_ind.instance_entity ~module_ r a t in
          later
            { entities = [Cpp_ind.entity r (List.map snd ds) hs];
              functions = [];
              finishing = [];
              helpers = hs @ List.map snd ds }
        | Wrapper_nothing -> () )
      | SEdecl d -> later (Cpp_ind.generate_ahead ~module_ d)
      | _ -> ())
    s;
  let aheads = List.rev !aheads in
  finish_ahead aheads;
  (* A body is a function of its declaration, not of the bodies generated or
     finished before it: under [CRANE_CHECK_IR] everything is finished and
     generated again in the reverse order and must come out the same (the
     plan's Milestone 4). *)
  if Probe.checking () then
    Cpp_ind.regenerating @@ fun () ->
    Finished_program.refinish (finishing (List.rev aheads));
    walk_as_rendered ~reversed:true ~modtype:Cpp_ind.modtype_concept
      ~after_module:(fun ~module_ frame _ ->
        convert_eponymous_record_fields ~module_ frame;
        Option.iter
          (fun (r, vars, candidates) -> ignore (Cpp_ind.record_methods ~module_ r vars candidates))
          (eponymous_record_methods frame) )
      ~decl:(fun ~wrapper ~module_ se ->
        match se with
        | SEdecl (Dind (kn, ind) as d) ->
          Cpp_ind.regenerate_ahead ~module_ d;
          List.iter
            (fun (ind_ref, vars, candidate) -> Gen_decls.check_method_ahead ind_ref vars candidate)
            (registered_methods ~order:List.rev kn ind)
        | SEdecl (Dtype _ as d) -> Cpp_ind.regenerate_ahead ~module_ d
        | _ when wrapper -> (
          match wrapper_element ~module_ se with
          | Wrapper_functions (_, generate) -> ignore (generate () : Gen_decls.generated_fun list)
          | Wrapper_instance (r, a, t) ->
            ignore (Cpp_ind.instance_entity ~module_ r a t : Cpp_ind.generated * cpp_decl list)
          | Wrapper_nothing -> () )
        | SEdecl d -> Cpp_ind.regenerate_ahead ~module_ d
        | _ -> ())
      s

(** The declarations the header writes in the struct of the module [mp] of
    elements [sel], read off what was generated ahead of the files
    ({!Cpp_ind.header_element_ahead}), or [None] where the struct holds
    something more: a nested module or module type, a concept, the fields of
    a merged record, a helper's definition.  A wrapper module's struct holds
    the declarations of its functions ({!pp_wrapper_module_dual}); any other
    module's holds what each of its elements is written as there. *)
let struct_members ~wrapper mp sel =
  let decls (rendered : Cpp_ind.rendered) = List.map (fun (_, d) -> (d : Cpp_erasure.settled :> cpp_decl)) rendered in
  with_render_ctx (fun c -> {c with rc_in_struct = true; rc_in_template = false; rc_scope = None})
  @@ fun () ->
  if wrapper then
    let generated =
      List.filter_map
        (fun (_, se) ->
          match wrapper_element ~module_:mp se with
          | Wrapper_functions (_, generate) -> Some (generate ())
          | Wrapper_instance _ | Wrapper_nothing -> None )
        sel
    in
    Some
      (List.concat_map
         (fun (specs, _) -> List.map (fun (d, _) -> (d : Cpp_erasure.settled :> cpp_decl)) specs)
         (file_views ~is_header:true generated) )
  else
    let frame = Module_frame.planned mp in
    if
      frame.promoted <> None || merged_eponymous_record frame <> None || frame.concept_collision
      || declared_classes sel <> []
    then None
    else
      List.fold_left
        (fun acc (_, se) ->
          match (acc, se) with
          | None, _ | _, (SEmodule _ | SEmodtype _) -> None
          | Some members, SEdecl d -> (
            match Cpp_ind.header_element_ahead ~module_:mp d with
            | {rendered; helpers = []; _} -> Some (members @ decls rendered)
            | {helpers = _ :: _; _} -> None ) )
        (Some []) sel

(** Plan where the header writes what it does not write in place
    ({!file_layout}), and which modules' structs it declares ahead of the
    file ({!hoisted_structs}).

    The sections are read off each element the header writes through
    {!pp_structure_elem} -- every one but a wrapper module's functions -- in
    the scope it writes it in: the module's visibility and planned header
    scope ({!Cpp_ind.header_scope}).  An element's member definitions go
    last; at namespace scope, an element written as nothing but erasure
    landing pads goes first, and so do the declarations of the helpers it
    places ({!lifted_views}).  The walk reaches the wrapper modules first,
    and the header writes the modules in their order, so the groups are put
    back in that order, by the file module each is written in.

    The structs hoisted are those of wrapper modules, and the modules a file's own
    elements are, written outside every struct and every class template a
    functor becomes -- the struct of a module written further in is placed
    with whatever contains it -- whose members' types name only inductives
    ({!module_members_name_only_inductives}), and whose struct holds nothing
    but static function declarations naming nothing inside another struct.
    Asked of what was generated ahead of the files, in the context the
    header writes each struct in ({!walk_as_rendered}), before either file is
    rendered. *)
let plan_file_layout s =
  let hoists ~wrapper mp sel =
    (wrapper
    || (match mp with MPdot (parent, _) -> is_modfile parent | MPfile _ | MPbound _ -> false)
       && outside_every_struct mp && not (Scope_plan.templated mp))
    && module_members_name_only_inductives sel
    && Option.cata
         (List.for_all (fun d ->
              is_static_member_declaration d && declaration_names_into_a_struct d = Some false ) )
         false
         (struct_members ~wrapper mp sel)
  in
  let analysis = get_structure_analysis () in
  let position mp =
    let rec file = function MPdot (mp, _) -> file mp | mp -> mp in
    let rec find i = function
      | [] -> List.length analysis.sorted_modules
      | (mi : Structure_analysis.module_info) :: rest ->
        if ModPath.equal mi.modpath (file mp) then i else find (i + 1) rest
    in
    find 0 analysis.sorted_modules
  in
  let erased = ref [] and specs = ref [] and member_defs = ref [] and forward = ref [] and homes = ref [] in
  let types = ref CString.Set.empty in
  let home mp d (rendered : Cpp_ind.rendered) =
    List.iter
      (fun (_, d') ->
        List.iter
          (fun name ->
            match Hashtbl.find_opt unmerged_wrappers name with
            | Some wrapped -> homes := (position mp, position wrapped, name, d) :: !homes
            | None -> () )
          (Cpp_print.unmerged_wrappers_written d') )
      rendered
  in
  let add band mp group = band := (position mp, group) :: !band in
  (* The header writes every wrapper module's functions before any module's
     types ({!do_struct_with_decl_tracking}), and so defines the structs
     lifted out of them first. *)
  let defines ~lifted mp env d =
    let pass = if lifted then 0 else 1 in
    forward := ((pass, position mp), List.map (fun f -> (lifted, f)) (Cpp_print.forward_declarations env d)) :: !forward;
    types := List.fold_right CString.Set.add (Cpp_print.file_scope_types d) !types
  in
  let wrapper_lifted ~module_ se =
    match wrapper_element ~module_ se with
    | Wrapper_nothing -> []
    | Wrapper_instance (r, a, t) ->
      let ds, helpers = Cpp_ind.instance_entity ~module_ r a t in
      helpers @ List.map snd ds
    | Wrapper_functions (_, generate) -> List.concat_map (fun (g : Gen_decls.generated_fun) -> g.gf_lifted) (generate ())
  in
  let wrapper_functions mp se =
    with_render_ctx at_file_scope @@ fun () ->
    List.iter (fun h -> defines ~lifted:true mp (empty_env ()) (fst (lifted_views h))) (wrapper_lifted ~module_:mp se)
  in
  let element mp d =
    Cpp_ind.in_header_element_scope mp @@ fun ~in_struct ->
      if
        Probe.checking ()
        && not (Option.cata (equal_visibility (current_visibility ())) false (Scope_plan.visibility mp))
      then
        Probe.violation "section scopes"
          Pp.(
            str "an element of the module " ++ str (ModPath.to_string mp)
            ++ str " is planned from a visibility other than the one planned for the module: "
            ++ pp_visibility (current_visibility ()) );
      let e = Cpp_ind.header_element_ahead ~module_:mp d in
      home mp d e.rendered;
      if e.member_defs <> [] then add member_defs mp {Cpp_ind.source = mp; declarations = e.member_defs};
      if not in_struct then begin
        if e.rendered <> [] && List.for_all is_erased_alias e.rendered then add erased mp {Cpp_ind.source = mp; declarations = e.rendered};
        List.iter (fun (env, d') -> defines ~lifted:false mp env d') e.rendered;
        List.iter
          (fun h ->
            let def, spec = lifted_views h in
            defines ~lifted:false mp (empty_env ()) def;
            Option.iter (fun spec -> add specs mp {Cpp_ind.source = mp; declarations = [(empty_env (), spec)]}) spec )
          e.helpers
      end
  in
  let in_writing_order band = List.map snd (List.stable_sort (fun (i, _) (j, _) -> Int.compare i j) (List.rev !band)) in
  Cpp_ind.peeking (fun () ->
      walk_as_rendered
        ~decl:(fun ~wrapper ~module_ se ->
          match se with
          | SEdecl (Dterm _ | Dfix _) when wrapper -> wrapper_functions module_ se
          | SEdecl d -> element module_ d
          | SEmodule _ | SEmodtype _ -> () )
        ~in_body:(fun ~wrapper mp sel ->
          if hoists ~wrapper mp sel then hoisted_structs := MPset.add mp !hoisted_structs )
        s );
  let promoted_imports =
    with_visibility (toplevel_visibility (List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s))
    @@ fun () ->
    List.sort_uniq String.compare
      (List.filter_map Cpp_print.promoted_alias_import
         ( Finished_program.installed_promoted ()
         @ List.concat_map Cpp_demands.promoted_of_type (Cpp_ind.generated_record_field_types ()) ))
  in
  let forward =
    List.concat_map snd
      (List.stable_sort
         (fun ((p, i), _) ((q, j), _) -> if p <> q then Int.compare p q else Int.compare i j)
         (List.rev !forward) )
  in
  file_layout :=
    { erased_aliases = in_writing_order erased;
      lifted_specs = in_writing_order specs;
      member_defs = in_writing_order member_defs;
      forward_decls = List.filter_map (fun (_, (f : Cpp_print.forward_declaration)) -> if f.fwd_constrained then None else Some f.fwd_text) forward;
      promoted_imports;
      constrained_decls =
        List.filter_map
          (fun (lifted, (f : Cpp_print.forward_declaration)) -> if lifted && f.fwd_constrained then Some f else None)
          forward;
      wrapper_homes =
        List.fold_left
          (fun acc (at, own, name, d) ->
            if at <= own && not (List.mem_assoc name acc) then acc @ [(name, d)] else acc )
          []
          (List.stable_sort (fun (i, _, _, _) (j, _, _, _) -> Int.compare i j) (List.rev !homes));
      file_scope_types = !types }

(** Plan the synthesised templates each file writes
    ({!Cpp_print.plan_ctor_aliases}), read off what was generated ahead of
    the files where the file writes it, in the scope it writes it in
    ({!walk_as_rendered}): each element's declarations, its helpers and the
    member definitions it gives up; a wrapper module's functions -- in the
    implementation only the definitions it holds, the declarations being
    members of the header's struct -- and, in
    the header, what is lifted out of them and its instances, which the
    header writes as it writes what is lifted ({!lifted_views}); and, in the
    header, a module's class concepts and the fields and methods of the
    record merged into its struct, which are written with the module, in the
    scope that encloses it. *)
let plan_ctor_aliases s =
  let written_in file =
    let found = ref [] in
    let written ds = List.iter (fun d -> found := Cpp_print.ctor_aliases_written ~file d :: !found) ds in
    let helpers hs =
      written
        (List.concat_map
           (fun h -> match lifted_views h with def, Some spec -> [def; spec] | def, None -> [def])
           hs )
    in
    let header = file = Common.Intf in
    (* What an element of the module [mp] writes is read in the scope the
       render writes it in, as an element of [mp]. *)
    let in_element_scope mp k =
      if header then Cpp_ind.in_header_element_scope mp (fun ~in_struct:_ -> writing_element_of mp k)
      else with_render_ctx at_file_scope (fun () -> writing_element_of mp k)
    in
    let element ~module_ d =
      in_element_scope module_ (fun () ->
          let e : Cpp_ind.element =
            if header then Cpp_ind.header_element_ahead ~module_ d else Cpp_ind.impl_element_ahead ~module_ d
          in
          written (List.map snd e.rendered);
          helpers e.helpers;
          written (List.map snd e.member_defs) )
    in
    let wrapper_element ~module_ se =
      with_render_ctx at_file_scope @@ fun () ->
      writing_element_of module_ @@ fun () ->
      match wrapper_element ~module_ se with
      | Wrapper_nothing -> ()
      | Wrapper_instance (r, a, t) ->
        if header then
          let ds, hs = Cpp_ind.instance_entity ~module_ r a t in
          helpers (hs @ List.map snd ds)
      | Wrapper_functions (_, generate) ->
        let gs = generate () in
        List.iter
          (fun (specs, defs) -> written (List.map fst (if header then specs @ defs else defs)))
          (file_views ~is_header:header [gs]);
        if header then helpers (List.concat_map (fun (g : Gen_decls.generated_fun) -> g.gf_lifted) gs)
    in
    let classes ~module_ cs =
      if header then
        in_element_scope module_ @@ fun () ->
        List.iter (fun (_, r, fields) -> written [Cpp_ind.finished_alone (Cpp_ind.concept ~module_ r fields)]) cs
    in
    let after_module ~module_ (frame : Module_frame.t) _ =
      if header then begin
        in_element_scope module_ @@ fun () ->
        Option.iter
          (fun (r, fields, (packet : ml_ind_packet)) ->
            let vl = packet.ip_vars in
            found :=
              Cpp_print.ctor_aliases_of_fields ~file ~vl r (Cpp_ind.record_field_types ~module_ r vl fields)
              :: !found )
          (merged_eponymous_record frame);
        Option.iter
          (fun (r, vars, candidates) ->
            let fields, hs = Cpp_ind.record_methods ~module_ r vars candidates in
            if fields <> [] then written [Cpp_ind.finished_record_methods r vars fields];
            written (List.map (fun h -> fst (lifted_views ~may_hoist:false h)) hs) )
          (eponymous_record_methods frame)
      end
    in
    Cpp_ind.peeking (fun () ->
        walk_as_rendered ~classes ~after_module
          ~decl:(fun ~wrapper ~module_ se ->
            match se with
            | SEdecl (Dterm _ | Dfix _) when wrapper -> wrapper_element ~module_ se
            | SEdecl d -> element ~module_ d
            | SEmodule _ | SEmodtype _ -> () )
          s );
    List.rev !found
  in
  Cpp_print.plan_ctor_aliases written_in

(* The declarations of [s], a functor's body's among them, in order. *)
let declarations s =
  let rec elems sel =
    List.concat_map
      (fun (_, se) ->
        match se with
        | SEdecl d -> [d]
        | SEmodule {ml_mod_expr; _} -> module_expr ml_mod_expr
        | SEmodtype _ -> [] )
      sel
  and module_expr = function
    | MEstruct (_, sel) -> elems sel
    | MEfunctor (_, _, body) -> module_expr body
    | MEident _ | MEapply _ -> []
  in
  List.concat_map (fun (_, sel) -> elems sel) s

let plan_names s =
  let name k r =
    if is_custom r || is_any_inline_custom r then [] else [(r, Common.pp_global_name k r)]
  in
  List.concat_map
    (function
      | Dind (kn, ind) ->
        List.concat
          (List.mapi
             (fun i p ->
               name Type (GlobRef.IndRef (kn, i))
               @ List.concat
                   (List.init (Array.length p.ip_types) (fun j ->
                        name Cons (GlobRef.ConstructRef ((kn, i), j + 1)) )) )
             (Array.to_list ind.ind_packets) )
        (* A record's fields, named as its struct spells them. *)
        @ ( match ind.ind_kind with
          | Record fields -> List.concat_map (fun (f, _) -> Option.cata (name Type) [] f) fields
          | Standard | Coinductive | TypeClass _ -> [] )
      | Dtype (r, _, _) -> name Type r
      | Dterm (r, _, _) -> name Term r
      | Dfix fds -> List.concat_map (fun fd -> name Term fd.fd_ref) fds )
    (declarations s)

let plan_referenced_names s =
  let seen = ref Ref.User.Set.empty and named = ref [] in
  let name k r =
    if not (Ref.User.Set.mem r !seen) then begin
      seen := Ref.User.Set.add r !seen;
      named := (r, Common.pp_global_name k r) :: !named
    end
  in
  (* The constructors of an inductive a type names, which the code taking a
     value of that type apart spells by their structs; only an inductive of
     the global environment has them to read, not a functor parameter's. *)
  let constructors ((kn, _) as ind) =
    match Table.base_mp (MutInd.modpath kn) with
    | MPbound _ -> ()
    | _ when not (Environ.mem_mind kn (Global.env ())) -> ()
    | _ ->
      let _, mip = Global.lookup_inductive ind in
      Array.iteri
        (fun j _ -> name Cons (GlobRef.ConstructRef (ind, j + 1)))
        mip.Declarations.mind_consnames
  in
  let rec ty : Miniml.ml_type -> unit = function
    | Miniml.Tglob (r, ts, vs) ->
      name Type r;
      (match r with GlobRef.IndRef ind -> constructors ind | _ -> ());
      List.iter ty ts;
      List.iter term vs
    | Tarr (a, b) ->
      ty a;
      ty b
    | Tapp (_, ts) -> List.iter ty ts
    | Tmeta {contents = Some t; _} -> ty t
    | Tvar _ | Tmeta _ | Thole _ | Topen _ | Tdummy _ | Miniml.Tunknown | Taxiom | Tstring -> ()
  and pattern = function
    | Pcons (r, ps) ->
      name Cons r;
      List.iter pattern ps
    | Pusual r -> name Cons r
    | Ptuple ps -> List.iter pattern ps
    | Prel _ | Pwild -> ()
  and term a =
    Mlutil.ast_iter term a;
    match a with
    | MLglob ({callee; _} as use) ->
      name Term callee;
      Global_use.iter_types ty use
    | MLcons (t, r, _) ->
      name Cons r;
      ty t
    | MLcase (t, _, brs) ->
      ty t;
      (* A match on a record reads its fields by name. *)
      List.iter (Option.iter (name Term)) (Table.record_fields_of_type t);
      Array.iter (fun (_, _, p, _) -> pattern p) brs
    | MLlam (_, t, _) | MLletin (_, t, _, _, _) -> ty t
    | MLfix (_, fs, _, _, _) -> Array.iter (fun (_, t) -> ty t) fs
    | MLmagic (Mcoerce (a, b), _) ->
      ty a;
      ty b
    | MLrel _ | MLapp _ | MLtuple _ | MLexn _ | MLdummy _ | MLaxiom _ | MLmagic _ | MLuint _
    | MLfloat _ | MLstring _ | MLparray _ ->
      ()
  in
  let inductive kn ind =
    ( match ind.ind_kind with
    | Record fields | TypeClass fields -> List.iter (fun (f, _) -> Option.iter (name Term) f) fields
    | Standard | Coinductive -> () );
    Array.iteri
      (fun i p ->
        name Type (GlobRef.IndRef (kn, i));
        ( match ind.ind_equiv with
        | Equiv kne -> name Type (GlobRef.IndRef (MutInd.make1 kne, i))
        | NoEquiv | RenEquiv _ -> () );
        Array.iteri
          (fun j args ->
            name Cons (GlobRef.ConstructRef ((kn, i), j + 1));
            List.iter ty args )
          p.ip_types )
      ind.ind_packets
  in
  let decl = function
    | Dind (kn, ind) -> inductive kn ind
    | Dtype (r, _, t) ->
      name Type r;
      ty t
    | Dterm (r, a, t) ->
      name Term r;
      term a;
      ty t
    | Dfix fds ->
      List.iter (fun fd -> name Term fd.fd_ref) fds;
      List.iter (fun fd -> term fd.fd_body) fds;
      List.iter (fun fd -> ty fd.fd_type) fds
  in
  let spec = function
    | Sind (kn, ind) -> inductive kn ind
    | Stype (r, _, t) ->
      name Type r;
      Option.iter ty t
    | Sval (r, _, t) ->
      name Term r;
      ty t
  in
  Modutil.struct_iter decl spec (fun mp -> ignore (Common.emitted_module_name mp)) s;
  (* Under separate extraction a promoted type variable another file declares
     is brought into scope by a [using] naming its field. *)
  if Common.get_force_cross_file_qualification () then
    List.iter
      (fun g ->
        let file = Table.base_mp (Table.modpath_of_r g) in
        if not (List.exists (fun (mp, _) -> ModPath.equal mp file) s) then name Type g )
      (Table.promoted_type_var_fields ());
  List.rev !named

(* The inductive the module [mp], of elements [sel], is promoted to where it
   is rendered outside every struct: its eponymous inductive, neither a record
   nor a class, where it declares no other inductive and no submodule --
   the last eponymous packet, as {!pp_structure_elem} reads them, with its
   block. *)
let promoted_inductive mp sel =
  let module_name =
    String.lowercase_ascii (Table.escape_reserved_struct_name (Common.emitted_module_name mp))
  in
  let inductives = List.filter_map (function _, SEdecl (Dind (kn, ind)) -> Some (kn, ind) | _ -> None) sel in
  if List.exists (function _, SEmodule _ -> true | _ -> false) sel then None
  else
    match inductives with
    | [(kn, ({ind_kind = Standard | Coinductive; _} as ind))] ->
      List.fold_left
        (fun found i ->
          let r = GlobRef.IndRef (kn, i) in
          if String.equal (String.lowercase_ascii (Common.pp_global_name Type r)) module_name then
            Some (r, ind)
          else found )
        None
        (List.init (Array.length ind.ind_packets) Fun.id)
    | _ -> None

(* Whether the module [mp], of elements [sel], promoted where it is rendered
   outside every struct, is a template: its inductive has parameters, and its
   other definitions are written in the template ({!pp_structure_elem}'s
   promotion). *)
let promoted_template mp sel =
  match promoted_inductive mp sel with
  | Some (GlobRef.IndRef (kn, i), ind) ->
    Table.ind_promoted_params kn @ fst (Table.ind_param_vars ind ind.ind_packets.(i)) <> []
  | Some _ | None -> false

(* A module outside every struct is promoted where {!promoted_inductive}
   says.  A promotion outlives the rendering that decided it. *)
let plan_promoted_inductives s =
  let rec elems parent sel =
    List.concat_map
      (fun (l, se) ->
        match se with
        | SEmodule {ml_mod_expr = MEstruct (_, sel'); _} ->
          let mp = MPdot (parent, l) in
          let own =
            if outside_every_struct mp then Option.cata (fun (r, _) -> [r]) [] (promoted_inductive mp sel')
            else []
          in
          own @ elems mp sel'
        | SEdecl _ | SEmodule _ | SEmodtype _ -> [] )
      sel
  in
  List.concat_map (fun (mp, sel) -> elems mp sel) s

let plan_accessors s =
  let accessor ~in_struct ~in_template r b ty =
    if is_any_inline_custom r || Table.is_projection r || is_registered_method r <> None
       || is_typeclass_instance b ty
    then false
    else
      match ty with
      | Tglob (m, _, _) when is_monad m -> false
      | _ -> (
        match convert_ml_type_to_cpp_type (empty_env ()) [] ty with
        | Tfun _ -> false
        | _ when thunk_reason r = Some Throws -> false
        | cty ->
          in_template
          || in_struct
             && (Ml_type_util.get_tvars cty <> [] || Common.get_force_cross_file_qualification ()) )
  in
  let rec elems ~in_struct ~in_template sel =
    List.concat_map
      (fun (_, se) ->
        match se with
        | SEdecl (Dterm (r, b, ty)) when accessor ~in_struct ~in_template r b ty -> [r]
        | SEmodule {ml_mod_expr = MEstruct (mp, sel); _} ->
          elems ~in_struct:true ~in_template:(Scope_plan.templated mp) sel
        | SEmodule {ml_mod_expr; _} -> module_expr ml_mod_expr
        | SEdecl _ | SEmodtype _ -> [] )
      sel
  and module_expr = function
    | MEstruct (_, sel) -> elems ~in_struct:true ~in_template:true sel
    | MEfunctor (_, _, body) -> module_expr body
    | MEident _ | MEapply _ -> []
  in
  (* A library file is written as a wrapper struct; the file being extracted
     is not. *)
  let wrapped =
    List.filter_map
      (fun (mi : Structure_analysis.module_info) ->
        if mi.wrapper_name <> None then Some mi.modpath else None )
      (get_structure_analysis ()).sorted_modules
  in
  List.concat_map
    (fun (mp, sel) ->
      elems ~in_struct:(List.exists (ModPath.equal mp) wrapped) ~in_template:false sel )
    s

(** The visibility each module's body is written in ({!Scope_plan.visibility}),
    keyed by the path the body is written under.  Every file of the unit is
    visible beneath all else; a top-level module's own scope is entered
    declaring nothing, and so is a child a name collision flattens into its
    parent's wrapper, whose elements are written in the wrapper beside its
    parent's.  Every other module's body, and a functor's, declares its
    elements' names, a functor's binding its parameters, outermost first. *)
let plan_visibility s =
  let base =
    toplevel_visibility (List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s)
  in
  let rec elems outer sel acc =
    List.fold_left
      (fun acc (_, se) ->
        match se with
        | SEmodule {ml_mod_expr; _} -> module_expr outer [] ml_mod_expr acc
        | SEdecl _ | SEmodtype _ -> acc )
      acc sel
  and module_expr outer params me acc =
    match me with
    | MEfunctor (mbid, _, me) -> module_expr outer (params @ [MPbound mbid]) me acc
    | MEstruct (mp, sel) -> body (inside ~members:(member_names_of_sel sel) mp params outer) mp sel acc
    | MEident _ | MEapply _ -> acc
  and body v mp sel acc = elems v sel ((mp, v) :: acc) in
  let wrapped =
    List.filter_map
      (fun (mi : Structure_analysis.module_info) ->
        if mi.wrapper_name <> None then Some mi.modpath else None )
      (get_structure_analysis ()).sorted_modules
  in
  let top acc (mp, sel) =
    let v = inside mp [] base in
    if List.exists (ModPath.equal mp) wrapped || not (wraps_children mp sel) then body v mp sel acc
    else
      List.fold_left
        (fun acc (l, se) ->
          match se with
          | SEmodule {ml_mod_expr = MEstruct (inner, sel'); _}
            when Module_plan.wrapper_role (MPdot (mp, l)) = Some Module_plan.Flattened ->
            body (inside inner [] v) inner sel' acc
          | se -> elems v [(l, se)] acc )
        ((mp, v) :: acc) sel
  in
  List.rev (List.fold_left top [] s)

(** [plan_bodies ~start ~enter s] is what the render carries into each
    module body of [s] it enters, keyed by the path the body is written
    under: [start ~wrapper] into a file module's -- a library's, if
    [wrapper] -- and into a child a name collision flattens into its
    parent's wrapper, whose elements are written beside its parent's;
    [enter state ~frame mp sel], from the [state] of the body declaring it,
    into the body [mp] of elements [sel] of a module declared with a struct
    for its body, which the render enters as a frame ({!pp_structure_elem}),
    [frame] being that module, at the path its label gives it, or of a
    functor, which it does not. *)
let plan_bodies ~start ~enter s =
  let rec elems state body_mp sel acc =
    List.fold_left
      (fun acc (l, se) ->
        match se with
        | SEmodule {ml_mod_expr = MEstruct (mp, sel'); _} ->
          body (enter state ~frame:(Some (MPdot (body_mp, l))) mp sel') mp sel' acc
        | SEmodule {ml_mod_expr; _} -> module_expr state ml_mod_expr acc
        | SEdecl _ | SEmodtype _ -> acc )
      acc sel
  and module_expr state me acc =
    match me with
    | MEfunctor (_, _, me) -> module_expr state me acc
    | MEstruct (mp, sel) -> body (enter state ~frame:None mp sel) mp sel acc
    | MEident _ | MEapply _ -> acc
  and body state mp sel acc = elems state mp sel ((mp, state) :: acc) in
  let wrapped =
    List.filter_map
      (fun (mi : Structure_analysis.module_info) -> if mi.wrapper_name <> None then Some mi.modpath else None)
      (get_structure_analysis ()).sorted_modules
  in
  let top acc (mp, sel) =
    let wrapper = List.exists (ModPath.equal mp) wrapped in
    let state = start ~wrapper in
    if wrapper || not (wraps_children mp sel) then body state mp sel acc
    else
      List.fold_left
        (fun acc (l, se) ->
          match se with
          | SEmodule {ml_mod_expr = MEstruct (inner, sel'); _}
            when Module_plan.wrapper_role (MPdot (mp, l)) = Some Module_plan.Flattened ->
            body state inner sel' acc
          | se -> elems state mp [(l, se)] acc )
        ((mp, state) :: acc) sel
  in
  List.rev (List.fold_left top [] s)

(** The inductives each module's body spells bare
    ({!Scope_plan.local_inductives}), as the render enters them: a file
    module that is not a library's starts from {!file_local_inductives},
    and every module body -- a struct's or a functor's -- adds those it
    declares ({!inductives_declared_in}). *)
let plan_local_inductives s =
  let analysis = get_structure_analysis () in
  plan_bodies s
    ~start:(fun ~wrapper -> if wrapper then [] else file_local_inductives analysis)
    ~enter:(fun local ~frame:_ mp sel -> inductives_declared_in mp sel @ local)

(** The module frames around each module's body ({!Scope_plan.frames}),
    innermost first, as the render enters them. *)
let plan_frames =
  plan_bodies ~start:(fun ~wrapper:_ -> []) ~enter:(fun frames ~frame _ _ -> Option.cata (fun m -> m :: frames) frames frame)

(** The scope of each module the unit emits as a struct
    ({!Scope_plan}): how a definition of one of its members, written out of
    line, names it; which modules are written inside a struct's body; and
    the visibility each module's body is written in ({!plan_visibility}).

    A wrapped file module is its wrapper struct.  A child a name collision
    flattens into its parent's wrapper is a member of the wrapper, which is
    its parent module's struct; a bystander keeps its own nesting under the
    wrapper's name; and the parent, unwrapped, is the wrapper.  Any other
    module emitted as a struct is nested in its parent's struct, if the parent
    is one -- the extraction root is not: its members are at namespace scope.
    A module holding a type class of its own name is a concept, not a struct,
    and its members are at namespace scope too. *)
let plan_scopes s =
  let own mp = Table.escape_reserved_struct_name (Common.emitted_module_name mp) in
  let child mp l = MPdot (mp, l) in
  let is_wrapped_child mp l =
    match Module_plan.wrapper_role (child mp l) with
    | Some (Module_plan.Flattened | Module_plan.Bystander) -> true
    | Some Module_plan.Own | None -> false
  in
  let modules sel =
    List.filter_map (fun (l, se) -> match se with SEmodule m -> Some (l, m) | _ -> None) sel
  in
  let collision_wrapper mp sel =
    if List.exists (fun (l, _) -> is_wrapped_child mp l) (modules sel) then
      Some
        ( List.find_map
            (fun (l, _) -> if is_wrapped_child mp l then Module_plan.wrapper_struct (child mp l) else None)
            (modules sel)
        |> Option.default
             (Table.escape_reserved_struct_name (String.capitalize_ascii (string_of_modfile mp))) )
    else None
  in
  (* The names compared are the ones planned, not the ones a reference
     spells: those depend on where the reference is written from. *)
  let concept_name r =
    match Module_plan.concept_name r with
    | Some name -> Some name
    | None -> Common.decided_global_name r
  in
  let concept_collision mp sel =
    List.exists
      (fun (_, se) ->
        match se with
        | SEdecl (Dind (kn, ({ind_kind = TypeClass _; _} as ind))) ->
          List.exists
            (fun i ->
              Option.equal String.equal
                (concept_name (GlobRef.IndRef (kn, i)))
                (Some (Common.emitted_module_name mp)) )
            (List.init (Array.length ind.ind_packets) Fun.id)
        | _ -> false )
      sel
  in
  let scope_of ~parent mp sel =
    let at module_ qualifier = Some {Scope_plan.module_; qualifier} in
    match Module_plan.wrapper mp with
    | Some (w, Module_plan.Own) -> at mp [w]
    | Some (w, Module_plan.Flattened) ->
      at (match mp with MPdot (p, _) -> p | _ -> mp) [w]
    | Some (w, Module_plan.Bystander) -> at mp [w; own mp]
    | None -> (
      match collision_wrapper mp sel with
      | Some w -> at mp [w]
      | None ->
        if Common.is_struct_module mp && not (concept_collision mp sel) then
          at mp (Option.cata (fun (p : Scope_plan.scope) -> p.qualifier) [] parent @ [own mp])
        else None )
  in
  (* Inside a functor's body no module gives a scope: the header writes the
     body as a class template, members defined inline, and the
     implementation writes none of it.  Every module there is nested and
     templated.  Outside it, a module is templated in a templated module, and
     where it is promoted to a template ({!promoted_template}), which it is
     only outside every struct.  Templated modules are keyed by the path
     their body is written under. *)
  let rec walk ~in_functor ~in_template ~parent mp sel (scopes, nested, templated) =
    let scope = if in_functor then None else scope_of ~parent mp sel in
    let scopes = match scope with Some sc -> (mp, sc) :: scopes | None -> scopes in
    List.fold_left
      (fun (scopes, nested, templated) (l, m) ->
        let mp' = child mp l in
        let is_nested = in_functor || Option.has_some scope in
        let nested = if is_nested then mp' :: nested else nested in
        let rec body = function
          | MEfunctor (_, _, me) -> body me
          | MEstruct (body_mp, sel) -> Some (body_mp, sel)
          | MEident _ | MEapply _ -> None
        in
        match (m.ml_mod_expr, body m.ml_mod_expr) with
        | MEstruct _, Some (body_mp, sel) ->
          let in_template = in_template || ((not is_nested) && promoted_template mp' sel) in
          let templated = if in_template then body_mp :: templated else templated in
          walk ~in_functor ~in_template ~parent:scope mp' sel (scopes, nested, templated)
        | MEfunctor _, Some (body_mp, sel) ->
          walk ~in_functor:true ~in_template:true ~parent:None mp' sel
            (scopes, nested, body_mp :: templated)
        | _ -> (scopes, nested, templated) )
      (scopes, nested, templated) (modules sel)
  in
  let scopes, nested, templated =
    List.fold_left
      (fun acc (mp, sel) -> walk ~in_functor:false ~in_template:false ~parent:None mp sel acc)
      ([], [], []) s
  in
  { Scope_plan.scopes = List.rev scopes;
    nested = List.rev nested;
    templated = List.rev templated;
    visibility = plan_visibility s;
    local_inductives = plan_local_inductives s;
    frames = plan_frames s }

let plan_nested_structs s =
  (* An instance is a struct where, past its parameters, its body builds the
     class's record -- as a singleton class's always does, its one method
     being the record -- rather than naming another instance, which is a
     [using] ({!Gen_decls.gen_instance_struct}). *)
  let instance_has_struct body ty =
    let rec past_parameters = function
      | MLlam (_, _, b) | MLmagic (_, b) -> past_parameters b
      | b -> b
    in
    match Ml_type_util.ml_return_type ty with
    | Tglob (cls, _, _) when Table.is_typeclass cls -> (
      match (Table.singleton_class_method cls, past_parameters body) with
      | Some _, _ | None, MLcons _ -> true
      | None, _ -> false )
    | _ -> false
  in
  (* An inductive declared outside every struct is still written inside one
     where its namespace wrapper holds declarations and so is not merged
     with it. *)
  (* A struct written inside another is its module's rendering, which demotes
     the module's inductive while it lasts: none is promoted there.  Whether
     its wrapper is merged is as a reference sees it at the declaration
     ({!Cpp_names.is_merged_inductive}), which spells the inductive the way
     the declaration does. *)
  let promoted _ = false in
  let merged r = not (in_unmerged_wrapper r) in
  let inductives ~in_struct ~local kn ind =
    List.concat
      (List.mapi
         (fun i _ ->
           let r = GlobRef.IndRef (kn, i) in
           if is_custom r || is_monad r || not (in_struct || in_unmerged_wrapper r) then []
           else
             match ind.ind_kind with
             | TypeClass _ -> []
             | Record _ when Module_plan.is_eponymous_record r -> []
             | _ when Table.is_enum_inductive r ->
               [(enum_declaration_name r, NSref r)]
             (* Moved out of the collision struct holding it to namespace
                scope, where it is generated ({!plan_concept_prerequisites}). *)
             | _ when Module_plan.is_namespace_scope_ref r -> []
             | _ -> [(struct_declaration_name ~merged ~promoted ~local r, NSref r)] )
         (Array.to_list ind.ind_packets) )
  in
  let rec elems ~in_struct ~local ?(role = fun _ -> None) parent sel =
    List.concat_map
      (fun (l, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) -> inductives ~in_struct ~local kn ind
        (* An instance is a struct where its module is one, unless it was
           lifted out to namespace scope. *)
        | SEdecl (Dterm (r, a, t))
          when in_struct && is_typeclass_instance a t && instance_has_struct a t
               && not (Module_plan.is_namespace_scope_ref r) ->
          [(Common.pp_global_name Type r, NSref r)]
        | SEdecl _ | SEmodtype _ -> []
        | SEmodule m -> (
          let mp = MPdot (parent, l) in
          match role l with
          (* Only its functions are written, straight into the wrapper. *)
          | Some Module_plan.Flattened -> []
          | Some (Module_plan.Own | Module_plan.Bystander) | None ->
            ( if in_struct then
                [(Table.escape_reserved_struct_name (Common.emitted_module_name mp), NSmodule mp)]
              else [] )
            @ module_expr mp m.ml_mod_expr ) )
      sel
  and module_expr mp = function
    | MEstruct (_, sel) -> elems ~in_struct:true ~local:true mp sel
    | MEfunctor (_, _, body) -> module_expr mp body
    | MEident _ | MEapply _ -> []
  in
  (* A file with no wrapper of its own whose child collides with a global
     type is written inside a collision wrapper struct, its own declarations
     among them, and they are not local there. *)
  let wrapper_files =
    List.filter_map
      (fun (mi : Structure_analysis.module_info) ->
        if mi.wrapper_name <> None then Some mi.modpath else None )
      (get_structure_analysis ()).sorted_modules
  in
  List.concat_map
    (fun (mp, sel) ->
      let role l =
        if List.exists (ModPath.equal mp) wrapper_files then None
        else Module_plan.wrapper_role (MPdot (mp, l))
      in
      let collision =
        List.exists
          (fun (l, se) ->
            match (se, role l) with
            | SEmodule _, Some (Module_plan.Flattened | Module_plan.Bystander) -> true
            | _ -> false )
          sel
      in
      elems ~in_struct:collision ~local:(not collision) ~role mp sel )
    s

let plan_instance_promoted_types s =
  List.concat_map
    (function
      | Dterm (r, a, t) when is_typeclass_instance a t -> (
        match Gen_decls.instance_promoted_types r a t with
        | [] -> []
        | bindings -> [(r, bindings)] )
      | Dind _ | Dtype _ | Dterm _ | Dfix _ -> [] )
    (declarations s)

let plan_unmerged_wrappers () : (string * ModPath.t) list =
  let is_member (_, se) =
    match se with
    | SEdecl (Dterm (r, _, _))
      when is_any_inline_custom r
           || is_eponymous_record_projection r
           || is_suppressed_projection r
           || is_registered_method r <> None ->
      false
    | SEdecl (Dterm (_, _, Tglob (ty, _, _))) when is_monad ty -> false
    | SEdecl (Dterm (_, a, t)) when is_typeclass_instance a t -> false
    | SEdecl (Dterm _) -> true
    | SEdecl (Dfix fds) -> filter_dfix fds <> []
    | _ -> false
  in
  List.filter_map
    (fun (mi : Structure_analysis.module_info) ->
      match mi.wrapper_name with
      | Some name when List.exists is_member mi.sels -> Some (name, mi.modpath)
      | Some _ | None -> None )
    (get_structure_analysis ()).sorted_modules

let plan_pointer_fields s =
  List.concat_map
    (function
      | Dind (kn, ({ind_kind = (Standard | Coinductive) as kind; _} as ind)) ->
        List.concat
          (List.mapi
             (fun i p ->
               let name = GlobRef.IndRef (kn, i) in
               if is_custom name || is_monad name || Table.is_flat_inductive name then []
               else
                 let vars = Common.ind_struct_tparams kn ind p in
                 List.concat
                   (List.init (Array.length p.ip_types) (fun j ->
                        let c = GlobRef.ConstructRef ((kn, i), j + 1) in
                        match
                          Gen_decls.constructor_pointer_fields ~name
                            ~is_coinductive:(kind = Coinductive) vars p.ip_types.(j)
                        with
                        | [] -> []
                        | fields -> [(name, Ml_type_util.ctor_struct_name_of_ref ~fallback_idx:j c, fields)] )) )
             (Array.to_list ind.ind_packets) )
      | Dind _ | Dtype _ | Dterm _ | Dfix _ -> [] )
    (declarations s)

let plan_module_names s =
  let rec elems parent sel =
    List.concat_map
      (fun (l, se) ->
        match se with
        | SEmodule {ml_mod_expr; _} ->
          let mp = MPdot (parent, l) in
          (mp, Common.emitted_module_name mp) :: module_expr mp ml_mod_expr
        | SEdecl _ | SEmodtype _ -> [] )
      sel
  and module_expr mp = function
    | MEstruct (_, sel) -> elems mp sel
    | MEfunctor (_, _, body) -> module_expr mp body
    | MEident _ | MEapply _ -> []
  in
  List.concat_map (fun (mp, sel) -> elems mp sel) s

let plan_field_names s =
  List.concat_map
    (function
      | Dind (kn, ({ind_kind = Standard | Coinductive; _} as ind)) ->
        List.concat
          (List.mapi
             (fun i p ->
               let ind_ref = GlobRef.IndRef (kn, i) in
               if is_custom ind_ref || is_monad ind_ref then []
               else
                 List.init (Array.length p.ip_types) (fun j ->
                     let c = GlobRef.ConstructRef ((kn, i), j + 1) in
                     let consarg_names =
                       if j < Array.length p.ip_consarg_names then p.ip_consarg_names.(j) else []
                     in
                     ( c,
                       Translation_support.compute_and_register_field_names ~owner:c
                         (Ml_type_util.ctor_struct_name_of_ref ~fallback_idx:j c)
                         (Translation_support.augment_with_args_renaming c consarg_names)
                         consarg_names
                         (List.length p.ip_types.(j)) ) ) )
             (Array.to_list ind.ind_packets) )
      | Dind _ | Dtype _ | Dterm _ | Dfix _ -> [] )
    (declarations s)

(** [pp_wrapper_struct name specs] is the struct a library module is rendered
    as: its body, [specs], inside a struct of that name. *)
let pp_wrapper_struct name specs =
  Cpp_ast.module_ (Struct {head = plain_struct (str name); layout = Block}) specs

(** What rendering one wrapper module produced, beyond the declarations that
    merge into its struct.

    [wr_specs] is the body of declarations of its functions, which go in its struct:
    one of its own at the module's turn, or one of the same name around an
    inductive, as planned ({!file_layout}).
    [wr_defs] are the out-of-line definitions, which follow the whole file.
    [wr_lifted] is a declaration lifted out of the module -- an instance struct,
    whose concept argument is a type no module owns -- and is due at the
    module's own place in the topological order, because a later module's
    constant may be initialised from it.

    [wr_lifted_specs] are the forward declarations of the functions among them,
    and go at the top of the file instead, because the callers of a lifted
    helper are inside the struct it was lifted out of and so precede it
    wherever its definition lands. *)
type wrapper_render = {
  wr_module : ModPath.t;
  wr_name : string;
  wr_specs : Cpp_ast.body;
  wr_defs : Cpp_ast.t;
  wr_lifted : Cpp_ast.t;
  wr_lifted_specs : Cpp_ast.t;
}

(** The top-level elements a hoisted concept cannot be read without.

    Hoisting a file-scope concept to the top of the file is answered, for
    almost everything it spells, by the forward declarations already in front
    of it: a [requires] body is unevaluated, so a plain mention wants the name
    declared and not defined.  Two kinds want more.  C++ admits no forward
    declaration for a [using], and a name spelled {e qualified} is a member
    lookup in a type that has to be complete.  Both are answered by moving the
    element itself, and the question this asks is which elements those are.

    It is asked of the whole file rather than at each element, because the
    element that has to move is almost always written {e after} the class that
    names it -- Rocq's own order guarantees only that it precedes the class,
    and the concept has left that position.  The answer is by label, which is
    what an element can check about itself while it renders.

    An inductive is spelled qualified when it is written inside a wrapper
    struct rather than merged with it -- [List::list], beside the functions of
    the file module [List] -- which is planned ({!Cpp_print.nested_in_wrapper}),
    so this is asked once the wrappers holding declarations are
    ({!plan_concept_prerequisites}).

    An inductive a collision struct holds -- a top-level element of a file
    written inside one -- has no declaration outside the struct for the
    concepts to read, and so moves too, leaving a member alias behind
    ({!Cpp_print.stand_ins}), as an alias does.  An enum is spelled bare
    already; any other is planned at namespace scope with the move
    ({!plan_concept_prerequisites}), so that every reference spells it
    bare too, its own body's, the concept's and its members' out of line.

    Transitive, and only through the elements themselves: an alias in the set
    spells types that then have to precede {e it}, and one of those may be
    another alias.  A struct in the set wants more than names: its payloads
    and the functions [wrapper_sels] merges into it are written out, so every
    inductive they mention has to be complete there, forward-declared or not.
    It does not descend into a module that is already in the set, because
    moving a struct moves everything in it. *)
let concept_prereqs ~wrapper_sels (s : ml_structure) : Names.Label.Set.t =
  let add_type_refs acc ty =
    let rec go acc = function
      | Miniml.Tglob (r, args, _) ->
        List.fold_left go (Ref.User.Set.add r acc) args
      | Miniml.Tarr (a, b) -> go (go acc a) b
      | Miniml.Tmeta {contents = Some t} -> go acc t
      | _ -> acc
    in
    go acc ty
  in
  let elements =
    List.concat_map
      (fun (mp, ms) -> List.map (fun (l, se) -> (mp, l, se)) ms)
      s
  in
  (* What the file-scope concepts spell: the field types of every type class
     declared here. *)
  let seed =
    List.fold_left
      (fun acc (_, _, se) ->
        match se with
        | Miniml.SEdecl (Miniml.Dind (_, ind)) -> (
          match ind.Miniml.ind_kind with
          | Miniml.TypeClass _ ->
            Array.fold_left
              (fun acc p ->
                Array.fold_left
                  (fun acc tys -> List.fold_left add_type_refs acc tys)
                  acc p.Miniml.ip_types )
              acc ind.Miniml.ind_packets
          | _ -> acc )
        | _ -> acc )
      Ref.User.Set.empty elements
  in
  let packet_refs kn ind =
    List.init (Array.length ind.Miniml.ind_packets) (fun i ->
        GlobRef.IndRef (kn, i) )
  in
  (* What a struct's body writes out: its payloads, and the signatures of the
     functions merged into it. *)
  let body_refs kn ind =
    let payloads =
      Array.fold_left
        (fun acc p ->
          Array.fold_left
            (fun acc tys -> List.fold_left add_type_refs acc tys)
            acc p.Miniml.ip_types )
        Ref.User.Set.empty ind.Miniml.ind_packets
    in
    List.fold_left
      (fun acc r ->
        List.fold_left
          (fun acc (_, se) ->
            match se with
            | Miniml.SEdecl d ->
              List.fold_left
                (fun acc fd -> add_type_refs acc fd.Miniml.fd_type)
                acc (Mlutil.term_defs d)
            | _ -> acc )
          acc
          (wrapper_sels (Cpp_print.nspace_wrapper_name r)) )
      payloads (packet_refs kn ind)
  in
  let held_in_collision_struct =
    let held = List.filter_map (fun (mp, ms) -> if is_modfile mp && wraps_children mp ms then Some mp else None) s in
    fun mp -> List.exists (ModPath.equal mp) held
  in
  let label_of (mp, l, se) (needed, complete) =
    match se with
    | Miniml.SEdecl (Miniml.Dtype (r, _, _)) ->
      if Ref.User.Set.mem r needed then Some l else None
    | Miniml.SEdecl (Miniml.Dind (kn, ind)) -> (
      match ind.Miniml.ind_kind with
      | Miniml.TypeClass _ -> None
      | _ ->
        if
          List.exists
            (fun r ->
              Ref.User.Set.mem r complete
              || Ref.User.Set.mem r needed
                 && (Cpp_print.nested_in_wrapper r || held_in_collision_struct mp) )
            (packet_refs kn ind)
        then Some l
        else None )
    | Miniml.SEmodule _ ->
      let inner = MPdot (mp, l) in
      let rec under m =
        ModPath.equal m inner
        || match m with MPdot (m', _) -> under m' | _ -> false
      in
      if
        Ref.User.Set.exists
          (fun r -> under (modpath_of_r r))
          needed
      then Some l
      else None
    | _ -> None
  in
  let rec fixpoint ((needed, complete) as refs) labels =
    let labels', (needed', complete') =
      List.fold_left
        (fun (labels, ((needed, complete) as refs)) ((_, l, se) as e) ->
          match label_of e refs with
          | None -> (labels, refs)
          | Some l' ->
            let labels = Names.Label.Set.add l' labels in
            let refs =
              match se with
              | Miniml.SEdecl (Miniml.Dtype (_, _, ty)) ->
                (add_type_refs needed ty, complete)
              | Miniml.SEdecl (Miniml.Dind (kn, ind)) ->
                let body = body_refs kn ind in
                (Ref.User.Set.union body needed, Ref.User.Set.union body complete)
              | _ -> refs
            in
            (labels, refs) )
        (labels, refs) elements
    in
    if
      Ref.User.Set.equal needed needed'
      && Ref.User.Set.equal complete complete'
      && Names.Label.Set.equal labels labels'
    then labels'
    else fixpoint (needed', complete') labels'
  in
  fixpoint (seed, Ref.User.Set.empty) Names.Label.Set.empty

(** Whether an element is a function, which a wrapper module writes into its
    struct. *)
let is_func_decl (_, se) = match se with SEdecl (Dterm _ | Dfix _) -> true | _ -> false

(** [plan] with the concept prerequisites of [s] ({!concept_prereqs}), asked
    in the visibility the files are written in, once the wrappers holding
    declarations are planned ({!plan_unmerged_wrappers}); and, at namespace
    scope, the inductives among them a collision struct holds, which move
    out of it. *)
let plan_concept_prerequisites (plan : Module_plan.t) s =
  let initial_mps = List.filter_map (fun (mp, _) -> if is_modfile mp then Some mp else None) s in
  let modules = (get_structure_analysis ()).sorted_modules in
  let wrapper_sels name =
    List.concat_map
      (fun (mi : Structure_analysis.module_info) ->
        if mi.wrapper_name = Some name then List.filter is_func_decl mi.sels else [] )
      modules
  in
  let labels = with_visibility (toplevel_visibility initial_mps) (fun () -> concept_prereqs ~wrapper_sels s) in
  let moved_out =
    List.concat_map
      (fun (mp, sel) ->
        if is_modfile mp && wraps_children mp sel then
          List.concat_map
            (fun (l, se) ->
              match se with
              | SEdecl (Dind (kn, ind)) when Names.Label.Set.mem l labels ->
                List.init (Array.length ind.ind_packets) (fun i -> GlobRef.IndRef (kn, i))
              | _ -> [] )
            sel
        else [] )
      s
  in
  { plan with
    concept_prerequisites = Names.Label.Set.elements labels;
    namespace_scope_refs = plan.namespace_scope_refs @ moved_out }

(** What placing top-level elements moves out of their places, each to a
    section of its own ahead of the body, in the order written: the structs
    of modules planned to be declared ahead of the file
    ({!hoisted_structs}), the elements the concepts cannot be read without
    ({!concept_prereqs}), and the concepts only namespace scope can hold. *)
type moved = {hoisted : Cpp_ast.t list; prereqs : Cpp_ast.t list; concepts : Cpp_ast.t list}

let nothing_moved = {hoisted = []; prereqs = []; concepts = []}

(** Everything [l] moves, in the order of [l]. *)
let moved_together l =
  { hoisted = List.concat_map (fun m -> m.hoisted) l;
    prereqs = List.concat_map (fun m -> m.prereqs) l;
    concepts = List.concat_map (fun m -> m.concepts) l }

(** What stays of each of [l], in order, and what they move. *)
let gathered l = (List.map fst l, moved_together (List.map snd l))

(** Main structure renderer with declaration tracking.

    PASS 1: Render every wrapper module's functions. PASS 2: Render types,
    writing a wrapper module's declarations into the struct planned for them.
    PASS 3: Emit deferred function definitions.

    This three-pass approach resolves forward reference issues while maintaining
    proper C++ declaration order.

    @param is_header  When [true] render the header pass (struct definitions,
                      concept declarations, inline specs); when [false] render
                      the implementation pass (out-of-line function bodies).
    @param f          Structure-element callback, typically
                      [pp_structure_elem ~is_header impl_decls] or the [header_decls]
                      variant; called for each [(label, ml_structure_elem)] pair
                      with the module it is an element of.
    @param s          The flat extraction structure: a list of
                      [(module_path, structure_elem list)] pairs produced by the
                      extraction pipeline.
    @return Pretty-printer document for the complete output file (header or
            implementation), including lifted declarations and deferred
            out-of-line function definitions. *)
let do_struct_with_decl_tracking ~is_header f s =
  writing_file (if is_header then Common.Intf else Common.Impl) @@ fun () ->
  (* A synthesised alias is emitted in front of the top-level element that
     writes it, rather than collected into the file's prologue.

     The prologue is only sound for a body naming top-level class templates:
     those can be forward-declared, so the prologue's forward declarations make
     the names readable there.  A body may name something that cannot be
     forward-declared at all -- a member template of another struct, or another
     alias template -- and then no prologue entry could have helped and the
     alias has to follow the {e definition}.

     The element to go in front of is the one that {e uses} the alias, which is
     not the one whose declaration produced the use: a use written into a
     deferred member definition belongs to some earlier element but is placed
     at the end of the file, and following its declaration puts the alias
     hundreds of lines ahead of everything the body names.  A use, by contrast, sits in
     code that manipulates values of the types the body names, and so comes
     after their definitions -- as a tendency and not as a guarantee: the use
     spells the alias, not the types inside it, so nothing here forces the
     margin to be positive.  On Vellvm it is about eleven thousand lines, and
     on this corpus the two placements coincide exactly, nothing in it being
     deferred.

     So the alias is emitted in front of the first chunk, in the order the
     file is written, that carries a declaration writing it -- which needs no
     knowledge of what the body names, only of which declaration writes it.
     Each top-level element is such a chunk, and so is each section of the
     assembled file; see {!Cpp_ast.schedule}.

     Only a top-level chunk.  A nested element is rendered inside a struct,
     where an alias template would acquire that struct's scope while its use
     sites spell it unqualified.

     A top-level element is placed here, in one of three places: the
     struct of a module planned to be declared ahead of the file goes to the
     top ({!hoisted_structs}); an element the concepts cannot be read without
     travels with them -- decided by label, because that is what the element
     knows about itself, against the plan ({!plan_concept_prerequisites}); and
     everything else stays where it is.  Placing an element gives what
     stays and what it moved ({!moved}), the concepts it declares, which go
     to the top of the file, among them. *)
  Cpp_print.file_scope_type_names := if is_header then !file_layout.file_scope_types else CString.Set.empty;
  Cpp_print.constrained_structs :=
    if is_header then
      List.map (fun (f : Cpp_print.forward_declaration) -> (f.fwd_ref, f.fwd_struct)) !file_layout.constrained_decls
    else [];
  let place ~wrapper_specs ~source ((l, se) as x) =
    let defined = if is_header then declarations [(source, [x])] else [] in
    let homed =
      List.filter_map (fun (name, d) -> if List.memq d defined then Some name else None) !file_layout.wrapper_homes
    in
    let {text = p; concepts = c; asserts = _} =
      element_of source
        (Cpp_print.writing_wrapper_members
           (List.map (fun name -> (name, wrapper_specs name)) homed)
           (fun () -> writing_element_of source (fun () -> f ~module_:source x)) )
    in
    if is_header && Probe.checking () then begin
      let absorbed = Cpp_print.take_absorbed_wrappers () in
      if absorbed <> homed then
        Probe.violation "wrapper homes"
          Pp.(
            str "an element wrote the declarations of the wrappers "
            ++ prlist_with_sep pr_comma str absorbed
            ++ str " into its structs, and was planned to write those of "
            ++ prlist_with_sep pr_comma str homed )
    end;
    let hoists =
      is_header
      && (not (!render_ctx).rc_in_struct)
      && (not (Cpp_ast.is_empty p))
      && match se with
         | SEmodule {ml_mod_expr = MEstruct (body_mp, _); _} -> struct_hoists body_mp p
         | _ -> false
    in
    (* A struct's member is not a chunk at namespace scope: the struct is. *)
    let p = if (!render_ctx).rc_in_struct then p else Cpp_ast.top_level p in
    if hoists then (Cpp_ast.empty, {nothing_moved with hoisted = [p]; concepts = c})
    else if is_header && Module_plan.is_concept_prerequisite l && is_modfile source && not (Cpp_ast.is_empty p) then (
      (* The prerequisites are asked for by label, of the files' top-level
         elements: a flattened child's element sharing the label is not one.
         A top-level element of a file a collision struct holds is a member
         of the struct, which cannot come first, its members naming the
         concepts: it moves out ahead of them all the same, the only order in
         which the concepts can be read, and leaves behind a member alias of
         each type it declares, through which the struct, and every
         reference qualified by it, still names it. *)
      let moved = {nothing_moved with prereqs = [p]; concepts = c} in
      if not (!render_ctx).rc_in_struct then (Cpp_ast.empty, moved)
      else
        let stand_ins = Cpp_print.stand_ins p in
        if Probe.checking () && stand_ins = [] then
          Probe.violation "concept prerequisites"
            Pp.(
              str "the element " ++ Names.Label.print l ++ str " of the module " ++ str (ModPath.to_string source)
              ++ str " is a member of a struct written ahead of the concepts, outside it, and nothing stands in for it" );
        (Cpp_ast.elements ~source (Cpp_ast.concat Pp.fnl stand_ins), moved) )
    else (p, {nothing_moved with concepts = c})
  in
  Cpp_print.start_ctor_alias_census ();
  Cpp_print.start_file_scope_census ();
  Cpp_ind.start_render ();
  init_std_names ();
  (* The file is written outside every module body, its files visible;
     [ppl] writes each module in the visibility planned for it, which has them
     beneath it.  What follows only assembles what was written there. *)
  let initial_mps =
    List.filter_map
      (fun (mp, _) -> if is_modfile mp then Some mp else None) s
  in
  let wrapper_parts, deferred_definitions, p, moved =
    with_visibility (toplevel_visibility initial_mps) @@ fun () ->
    let analysis = get_structure_analysis () in
    let wrapper_names =
      List.map
        (fun (mi : Structure_analysis.module_info) ->
          ((mi.modpath, mi.sels), mi.wrapper_name) )
        analysis.sorted_modules
    in
    (* Each wrapper module contributes up to three fragments: declarations that
       go in its struct, and definitions and lifted helpers that must follow
       it. *)
    let wrapper_parts =
      List.filter_map
        (fun ((mp, sel), wrapper_name) ->
          match wrapper_name with
          | None -> None
          | Some name ->
            in_planned_visibility mp @@ fun () ->
            let func_sels = List.filter is_func_decl sel in
            let old_decls = !current_structure_decls in
            current_structure_decls := sel;
            let p_specs, p_defs, p_lifted, p_lifted_specs =
              pp_wrapper_module_dual ~is_header mp func_sels
            in
            current_structure_decls := old_decls;
            if is_header && Cpp_ast.body_is_empty p_specs = Hashtbl.mem unmerged_wrappers name then
              Probe.violation "unmerged wrappers"
                Pp.(
                  str "the wrapper " ++ str name
                  ++ str
                       ( if Cpp_ast.body_is_empty p_specs then " was planned to hold declarations and holds none"
                         else " holds declarations it was not planned to" ) );
            Some
              {
                wr_module = mp;
                wr_name = name;
                wr_specs = p_specs;
                wr_defs = p_defs;
                wr_lifted = p_lifted;
                wr_lifted_specs = p_lifted_specs;
              } )
        wrapper_names
    in
    if is_header && Cpp_print.take_absorbed_wrappers () <> [] then
      Probe.violation "wrapper homes"
        (Pp.str "a wrapper's declarations were written into a struct lifted out of a wrapper module");
    let deferred_definitions = List.map (fun w -> w.wr_defs) wrapper_parts in
    let ppl ((mp, sel), wrapper_name) =
      in_planned_visibility mp @@ fun () ->
      Cpp_ind.with_planned_local_inductives mp @@ fun () ->
      let wrapper_specs name =
        match List.find_opt (fun w -> String.equal w.wr_name name) wrapper_parts with
        | Some w -> w.wr_specs
        | None -> Cpp_ast.module_body mp []
      in
      let place_in source = place ~wrapper_specs ~source in
      let f = place_in mp in
      let joined_placed sel =
        let stays, moved = gathered (List.map f sel) in
        (Cpp_ast.joined stays, moved)
      in
      let old_decls = !current_structure_decls in
      current_structure_decls := sel;
      let placed =
        match wrapper_name with
        | Some name ->
          let type_sels = List.filter (fun x -> not (is_func_decl x)) sel in
          let type_pp, type_moved = joined_placed type_sels in
          (* The wrapper struct belongs at its module's own place in the
             topological order, whether or not the module also declares types.
             A later module's constant is initialised inside its struct body, so
             a callee's struct has to be complete by then -- emitting the
             wrapper after everything else, as a leftover, is too late.  Unless
             a struct of its name written around an inductive was planned to
             hold its declarations, and has ({!file_layout}). *)
          let wrapper_pp, wrapper_moved =
            let specs = wrapper_specs name in
            if (not is_header) || Cpp_ast.body_is_empty specs || List.mem_assoc name !file_layout.wrapper_homes then
              (Cpp_ast.empty, nothing_moved)
            else
              let struct_pp = pp_wrapper_struct name specs in
              if struct_hoists mp struct_pp then (Cpp_ast.empty, {nothing_moved with hoisted = [struct_pp]})
              else (struct_pp, nothing_moved)
          in
          (* A declaration lifted out of this module -- an instance struct -- is
             due at the same point, and for the same reason: a later module's
             constant may be initialised from it. *)
          let lifted_pp =
            match List.find_opt (fun w -> ModPath.equal w.wr_module mp) wrapper_parts with
            | Some w -> w.wr_lifted
            | None -> Cpp_ast.empty
          in
          (* The wrapper struct and what was lifted out of it are elements of
             their own, assembled here rather than by [f]: an alias they spell
             goes in front of them, not in front of the whole section they end
             up in (see {!Cpp_ast.schedule}). *)
          let wrapper_pp = Cpp_ast.top_level wrapper_pp in
          let lifted_pp = Cpp_ast.top_level lifted_pp in
          (Cpp_ast.joined [type_pp; wrapper_pp; lifted_pp], moved_together [type_moved; wrapper_moved])
        | None ->
          (* Which children a name collision forces inside a wrapper struct is
             layout, decided by {!Structure_analysis} before any rendering began;
             here we only read the answer back. *)
          let is_colliding_child l _se =
            Module_plan.wrapper_role (MPdot (mp, l)) = Some Module_plan.Flattened
          in
          (* Whether a wrapper formed is not the same question as which children
             it flattens: a bystander is recorded only when one did, so a child
             in either table says the struct is there to be written. *)
          let is_wrapped_child l = is_wrapped_child (MPdot (mp, l)) in
          let has_child_collision = wraps_children mp sel in
          if has_child_collision then (
            (* The wrapper's name was chosen with the collision that forced it in
               view, by {!Structure_analysis}; each wrapped child records it. *)
            let parent_name =
              List.find_map
                (fun (l, se) ->
                  match se with
                  | SEmodule _ when is_wrapped_child l ->
                    Module_plan.wrapper_struct (MPdot (mp, l))
                  | _ -> None )
                sel
              |> Option.default
                   (Table.escape_reserved_struct_name
                      (String.capitalize_ascii (string_of_modfile mp)))
            in
            (* The struct holds the module's elements in order, each flattened
               child's where the child is, written with no struct of its own:
               the header only the child's functions, the implementation all
               of it.  Where the child is, because the initialiser of a
               constant is no complete-class context: a function of the child
               it calls has to be declared ahead of it, which Rocq's order
               already ensures. *)
            let flattened (l, se) = match se with SEmodule _ -> is_colliding_child l se | _ -> false in
            let child enclosure ~keep (_, se) =
              match se with
              | SEmodule {ml_mod_expr = MEstruct (inner_mp, inner_sel); _} ->
                in_planned_visibility inner_mp (fun () ->
                    Cpp_ind.with_planned_local_inductives inner_mp @@ fun () ->
                    let stays, moved = gathered (List.map (place_in inner_mp) (List.filter keep inner_sel)) in
                    (Cpp_ast.module_ enclosure (Cpp_ast.module_body inner_mp stays), moved) )
              | _ -> (Cpp_ast.empty, nothing_moved)
            in
            let body enclosure ~keep sel =
              let stays, moved = gathered (List.map (fun x -> if flattened x then child enclosure ~keep x else f x) sel) in
              (Cpp_ast.module_body mp stays, moved)
            in
            if is_header then (
              (* A module type is a concept, and so is a class, and C++ has no
                 member concepts, so one written among a wrapper's elements
                 cannot stay there -- and cannot simply move ahead of the
                 wrapper either, because a functor elsewhere may be constrained
                 by it and be emitted first.  It goes where the concepts of a
                 nested module's typeclasses already go, which is the top of
                 the file, written as an element of the module it is one of,
                 a class's generated as a module's are ({!walk_as_rendered}).
                 Being unwritable inside the struct used to be answered by
                 dropping it. *)
              let class_concept (l, r, fields) =
                with_render_ctx (fun c -> {c with rc_in_struct = true}) @@ fun () ->
                writing_element_of mp @@ fun () ->
                let d = generated_concept ~module_:mp r fields in
                let concept = class_concept_element ~module_:mp d in
                Cpp_ast.elements ~source:mp Cpp_ast.(seq [text (pp_doc_comment l); concept])
              in
              let concepts_moved =
                List.map
                  (fun ((_, se) as x) ->
                    let concepts, moved =
                      match se with
                      | SEmodtype _ ->
                        let concept, moved = f x in
                        ([concept], moved)
                      | _ -> (List.map class_concept (declared_classes [x]), nothing_moved)
                    in
                    {moved with concepts = moved.concepts @ List.filter (fun pp -> not (Cpp_ast.is_empty pp)) concepts} )
                  sel
              in
              let sel = List.filter (fun (_, se) -> match se with SEmodtype _ -> false | _ -> true) sel in
              let body, body_moved =
                with_render_ctx (fun c -> {c with rc_in_struct = true}) (fun () -> body In_enclosing_scope ~keep:is_func_decl sel)
              in
              let moved = moved_together (concepts_moved @ [body_moved]) in
              if Cpp_ast.body_is_empty body then (Cpp_ast.empty, moved)
              else
                ( Cpp_ast.top_level
                    (Cpp_ast.module_
                       (Struct {head = plain_struct (str parent_name); layout = Block})
                       body ),
                  moved ) )
            else
              let body, moved = body Out_of_line ~keep:(fun _ -> true) sel in
              (Cpp_ast.module_ Out_of_line body, moved) )
          else
            joined_placed sel
      in
      current_structure_decls := old_decls;
      placed
    in
    let placed = List.map ppl wrapper_names in
    let rendered = List.map2 (fun wn (p, _) -> (wn, p)) wrapper_names placed in
    let rev_rendered = List.rev rendered in
    let main_entry, pre_entries =
      match rev_rendered with
      | ((_, None), p) :: rest -> (Some p, List.rev rest)
      | _ -> (None, rendered)
    in
    let p_pre = joined snd pre_entries in
    let p =
      Cpp_ast.joined
        ( match main_entry with
        | Some main_p -> [p_pre; main_p]
        | None -> [p_pre] )
    in
    (wrapper_parts, deferred_definitions, p, moved_together (List.map snd placed))
  in
  let erased_aliases =
    let imports = if is_header then List.map (fun i -> Cpp_ast.text (str i)) !file_layout.promoted_imports else [] in
    let pads = if is_header then !file_layout.erased_aliases else [] in
    imports @ Cpp_ind.render_section pads
  in
  (* Aliases go in front of the text that writes them, and only what no text
     writes is left for the prologue; see {!Cpp_ast.schedule}. *)
  let forward_declarations = if is_header then !file_layout.forward_decls else [] in
  (* Declared ahead of everything that could call them, which is everything:
     a lifted helper's definition is placed after the struct it came out of,
     and its callers are that struct's members.  This goes after the concepts
     because a helper's constraint may name one, and after the struct forward
     declarations because its parameters may name a struct -- a declaration
     needs those declared, not complete.  Redeclaring a helper that did land
     before its uses is legal and costs a line; deciding which those are would
     cost the property that makes this correct. *)
  let lifted_specs =
    if is_header then
      List.map (fun w -> w.wr_lifted_specs) wrapper_parts @ Cpp_ind.render_section !file_layout.lifted_specs
    else []
  in
  (* Last of all: a datatype's method whose body names a module's struct, which
     is emitted after every datatype.  Nothing else in the header is later. *)
  let deferred_members = Cpp_ind.render_section (if is_header then !file_layout.member_defs else []) in
  (* Each section a chunk of its own, so that an alias no single element
     claimed -- one whose only use is in a section assembled out of several
     -- still lands in front of the first section that writes it rather than
     in the prologue.  The structs hoisted ahead of the file go alongside the
     lifted helpers and for the same reason, in front of them because a
     helper's own declaration may name one of them. *)
  let unit =
    { Cpp_ast.forward_declarations;
      erased_aliases;
      concept_prerequisites = moved.prereqs;
      concepts = moved.concepts;
      hoisted_structs = moved.hoisted;
      lifted_specs;
      body = p;
      deferred_definitions;
      deferred_members }
  in
  let templates =
    List.map
      (fun a ->
        { Cpp_ast.name = ctor_alias_name a;
          homed = Option.has_some a.ca_home;
          holder = a.ca_holder;
          declaration = ctor_alias_declaration a } )
      (ctor_aliases_declared_in ~file:(if is_header then Common.Intf else Common.Impl))
  in
  let forwards =
    if is_header then
      List.map
        (fun (f : Cpp_print.forward_declaration) -> {Cpp_ast.struct_ = f.fwd_struct; forward_declaration = f.fwd_text})
        !file_layout.constrained_decls
    else []
  in
  let written = if is_header then Common.Intf else Common.Impl in
  let file =
    Cpp_ast.print ~write:(Cpp_ind.write_unprinted ~file:written)
      (Cpp_ast.schedule ~templates ~forwards unit)
  in
  Cpp_print.check_ctor_alias_plan ~file:written;
  Cpp_print.check_file_scope_types ~file:written;
  file ++ fnl ()

(** Main entry point: render structure to C++ implementation file. *)
let pp_struct s =
  do_struct_with_decl_tracking
    ~is_header:false
    (pp_structure_elem ~is_header:false impl_decls)
    s

(** Main entry point: render structure to C++ header file. *)
let pp_hstruct s =
  do_struct_with_decl_tracking
    ~is_header:true
    (pp_structure_elem ~is_header:true header_decls)
    s

(** Language descriptor for C++ extraction. *)
let cpp_descr =
  {
    keywords;
    global_scope_keywords = c_library_globals;
    file_suffix = ".cpp";
    file_naming = file_of_modfile;
    preamble;
    pp_struct;
    pp_hstruct;
    sig_suffix = Some ".h";
    sig_preamble;
    pp_decl = (fun ~module_ d -> Cpp_ast.to_pp (pp_decls (impl_decls ~module_ d).rendered));
  }
