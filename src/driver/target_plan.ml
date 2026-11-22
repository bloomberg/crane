(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the backend decided about a unit before rendering it.  See
    [target_plan.mli]. *)

open Names

type kind_reason =
  | Functor_alignment
  | Used_as_value

type kind_decision = {
  block : MutInd.t;
  kind : Core.Inductive.Kind.t;
  reason : kind_reason;
}

type representation = {
  module_names : (ModPath.t * string) list;
  names : (GlobRef.t * string) list;
  referenced_names : (GlobRef.t * string) list;
  field_names : (GlobRef.t * Id.t list) list;
  pointer_fields : (GlobRef.t * string * Core_plan.Pointer_fields.planned list) list;
  unmerged_wrappers : (string * Names.ModPath.t) list;
  promoted_inductives : GlobRef.t list;
  accessors : GlobRef.t list;
  nested_structs : (string * Unit_plan.Cpp_state.nested_struct_owner) list;
  scopes : Core_plan.Scope_plan.t;
  instance_promoted_types : (GlobRef.t * (Id.t * Core.Type.t) list) list;
}

type t = {
  input : Core.Fingerprint.t option;
  config : Base.Table.unit_config;
  inductive_kinds : kind_decision list;
  template_kinds : (GlobRef.t * Cpp_ir.Tparam_kinds.t) list;
  modules : Core_plan.Module_plan.t;
  representation : representation;
  callables : Core_plan.Callable_abi.t list;
  instance_methods : (GlobRef.t * (Id.t * Core_plan.Callable_abi.t) list) list;
  assumed_callables : (GlobRef.t * Core_plan.Param_pos.orig Core_plan.Param_pos.pos list) list;
}

(** The last of [decisions] about [kn]. *)
let decided decisions kn =
  List.fold_left
    (fun acc d -> if MutInd.UserOrd.equal d.block kn then Some d.kind else acc)
    None decisions

let kind_of t kn = decided t.inductive_kinds kn

(** The kind [ind] has once [decisions] apply. *)
let kind_after decisions kn (ind : Core.Inductive.t) = Option.default ind.kind (decided decisions kn)

(** {!Base.Table.is_typeclass}, once [decisions] apply. *)
let is_typeclass_after decisions r =
  let of_block kn =
    match decided decisions kn with
    | Some (Core.Inductive.Kind.Type_class _) -> true
    | Some _ -> false
    | None -> Base.Table.is_typeclass r
  in
  match r with
  | GlobRef.IndRef (kn, _) | GlobRef.ConstructRef ((kn, _), _) -> of_block kn
  | GlobRef.ConstRef _ | GlobRef.VarRef _ -> Base.Table.is_typeclass r

(** Give a functor application's inductives the kind the functor's own body
    gave them.

    [Module FN := F N] does not alias [F]'s declarations: Rocq builds a second
    copy of every inductive in the body, with a kernel name of its own, and
    Crane classifies that copy independently.  The two answers can differ --
    instantiation registers a class declared inside a functor in Rocq's type
    class database while the body's own copy stays unregistered, so [F.Cl] is
    a {!Core.Inductive.Kind.Record} and [FN.Cl] a {!Core.Inductive.Kind.Type_class}.  One declaration with two kinds is
    a disagreement every later reader inherits: the struct is emitted from the
    body's copy, which is the one that exists in C++, while a call site
    reading the instantiated copy treats its instances as template arguments
    and spells [FN::template use<FN::inst>()].

    The body's copy governs, being the one emitted.  Only the classification
    is taken; the field references stay the instantiated copy's, as those are
    the ones its projections are spelled with. *)
let functor_alignment struc =
  (* Every module body's inductive kinds, keyed by the module's own path and
     the inductive's label -- the pair a functor application can name. *)
  let body_kinds : (string * Label.t, Core.Inductive.Kind.t) Hashtbl.t = Hashtbl.create 16 in
  let rec body_of (me : Core.Module.Expr.t) =
    match me with Core.Module.Expr.Functor {body = me; _} -> body_of me | me -> me
  in
  let rec collect_expr (me : Core.Module.Expr.t) =
    match me with
    | Core.Module.Expr.Structure {path = mp; items = sel} ->
      List.iter
        (fun (l, se) ->
          match se with
          | Core.Module.Structure_item.Declaration (Core.Decl.Inductive {definition = ind; _}) ->
            Hashtbl.replace body_kinds (ModPath.to_string mp, l) ind.kind
          | Core.Module.Structure_item.Module m -> collect_expr (body_of m.expr)
          | _ -> () )
        sel
    | Core.Module.Expr.Functor {body = me; _} -> collect_expr me
    | Core.Module.Expr.Path _ | Core.Module.Expr.Apply _ -> ()
  in
  (* The functor an application applies, however many arguments it takes. *)
  let rec applied_functor (me : Core.Module.Expr.t) =
    match me with
    | Core.Module.Expr.Apply {functor_ = me; _} -> applied_functor me
    | Core.Module.Expr.Path mp -> Some mp
    | Core.Module.Expr.Structure _ | Core.Module.Expr.Functor _ -> None
  in
  let decisions = ref [] in
  let align_sig mp_functor (mt : Core.Module.Type.t) =
    match mt with
    | Core.Module.Type.Signature {items = sigl; _} ->
      List.iter
        (fun (l, sp) ->
          match sp with
          | Core.Module.Signature_item.Declaration (Core.Signature.Declaration.Inductive {entity = kn;
                                                                                          definition = ind}) -> (
            let aligned =
              match
                ( Hashtbl.find_opt body_kinds (ModPath.to_string mp_functor, l),
                  kind_after !decisions kn ind )
              with
              | Some (Core.Inductive.Kind.Type_class _), Core.Inductive.Kind.Record fields ->
                Some (Core.Inductive.Kind.Type_class fields)
              | Some (Core.Inductive.Kind.Record _), Core.Inductive.Kind.Type_class fields ->
                Some (Core.Inductive.Kind.Record fields)
              | _ -> None
            in
            match aligned with
            | Some kind -> decisions := {block = kn; kind; reason = Functor_alignment} :: !decisions
            | None -> () )
          | Core.Module.Signature_item.Declaration _
          | Core.Module.Signature_item.Module _
          | Core.Module.Signature_item.Module_type _ -> () )
        sigl
    | Core.Module.Type.Path _ | Core.Module.Type.Functor _ | Core.Module.Type.Refined _ -> ()
  in
  let rec walk_expr (me : Core.Module.Expr.t) =
    match me with
    | Core.Module.Expr.Structure {items = sel; _} -> List.iter walk_elem sel
    | Core.Module.Expr.Functor {body = me; _} -> walk_expr me
    | Core.Module.Expr.Path _ | Core.Module.Expr.Apply _ -> ()
  and walk_elem (_l, se) =
    match se with
    | Core.Module.Structure_item.Module m ->
      Option.iter (fun mp -> align_sig mp m.type_) (applied_functor m.expr);
      walk_expr m.expr
    | Core.Module.Structure_item.Declaration _ | Core.Module.Structure_item.Module_type _ -> ()
  in
  List.iter
    (fun (_mp, sel) ->
      List.iter
        (fun (_l, se) -> match se with Core.Module.Structure_item.Module m -> collect_expr (body_of m.expr) | _ -> ())
        sel )
    struc;
  List.iter (fun (_mp, sel) -> List.iter walk_elem sel) struc;
  List.rev !decisions

(** Demote a record classified as a type class back to a plain struct when the
    structure uses it as a value, given the kinds [prior] decisions settled.

    A record with a [Type]-valued field models an algebraic structure -- a
    [Monoid] whose carrier and operations are resolved statically -- and is
    emitted as a C++ concept, which its instances satisfy as types.  But the
    same record can also be packed as an existential and handled as data ([list
    dyn]): a concept cannot be a list element, and the value carries its own
    type, so it has to be a struct with the promoted field erased.

    A type argument is the signal: an instance used statically appears as a
    definition's parameter, which becomes a template parameter, and never
    inside another type's arguments. *)
let value_use_demotion prior struc =
  let is_typeclass = is_typeclass_after prior in
  let demoted = ref Mindmap_env.empty in
  let demote kn = demoted := Mindmap_env.add kn () !demoted in
  let rec scan_arg t =
    match t with
    | Core.Type.Global_app {head = (GlobRef.IndRef (kn, _) as r); type_arguments = l; _} ->
      if is_typeclass r then demote kn;
      List.iter scan_arg l
    | Core.Type.Global_app {type_arguments = l; _} -> List.iter scan_arg l
    | Core.Type.Arrow {parameter = a; result = b} ->
      scan_arg a;
      scan_arg b
    | Core.Type.Meta {contents = Some t} -> scan_arg t
    | _ -> ()
  in
  let rec scan_type = function
    | Core.Type.Global_app {type_arguments = l; _} -> List.iter scan_arg l
    | Core.Type.Arrow {parameter = a; result = b} ->
      scan_type a;
      scan_type b
    | Core.Type.Meta {contents = Some t} -> scan_type t
    | _ -> ()
  in
  (* A constructor field is data outright, so a class named as the field's own
     type is used as data too -- not only one buried in its arguments.  A
     class's own field is not: a superclass field is what a concept refines,
     and demoting it would turn the refinement into a member. *)
  let scan_ind kn (ind : Core.Inductive.t) =
    let scan_field =
      match kind_after prior kn ind with Core.Inductive.Kind.Type_class _ -> scan_type | _ -> scan_arg
    in
    Array.iter
      (fun (p : Core.Inductive.Packet.t) -> Array.iter (List.iter scan_field) p.constructor_argument_types) ind.packets
  in
  (* A class value a definition computes from data is data: the struct an
     instance is otherwise emitted as is fixed at compile time, so it cannot
     stand for [mkDict base], whose fields depend on an argument.  Type and
     instance arguments do not count -- those an instance struct takes as
     template parameters. *)
  let scan_computed_class ty =
    let rec walk had_value = function
      | Core.Type.Arrow {parameter = a; result = b} ->
        let is_erased =
          match a with
          | Core.Type.Erased _ -> true
          | Core.Type.Global_app {head = r; _} -> is_typeclass r
          | _ -> false
        in
        walk (had_value || not is_erased) b
      | Core.Type.Meta {contents = Some t} -> walk had_value t
      | Core.Type.Global_app {head = (GlobRef.IndRef (kn, _) as r); _} when had_value ->
        if is_typeclass r then demote kn
      | _ -> ()
    in
    walk false ty
  in
  let scan_term_type u =
    scan_type u;
    scan_computed_class u
  in
  (* A body says the same thing with the types it annotates: [[natalg;
     natalg]] is a [list alg] whether or not any declaration's type says so. *)
  let scan_body body =
    ignore
      (Base.Core_util.ast_map_types
         (fun t ->
           scan_type t;
           t )
         body)
  in
  let scan_decl = function
    | Core.Decl.Inductive {entity = kn; definition = ind} -> scan_ind kn ind
    | Core.Decl.Type_alias {body = u; _} -> scan_type u
    | (Core.Decl.Value _ | Core.Decl.Recursive_group _) as d ->
      List.iter
        (fun (fd : Core.Recursion.Definition.t) ->
          scan_term_type fd.type_;
          scan_body fd.body )
        (Base.Core_util.term_defs d)
  in
  let scan_spec = function
    | Core.Signature.Declaration.Inductive {entity = kn; definition = ind} -> scan_ind kn ind
    | Core.Signature.Declaration.Type {body = ot; _} -> Option.iter scan_type ot
    | Core.Signature.Declaration.Value {type_ = u; _} -> scan_term_type u
  in
  Core_passes.Modutil.struct_iter scan_decl scan_spec (fun _ -> ()) struc;
  let decisions = ref [] in
  let decide kn ind =
    match kind_after prior kn ind with
    | Core.Inductive.Kind.Type_class fields when Mindmap_env.mem kn !demoted ->
      decisions := {block = kn; kind = Core.Inductive.Kind.Record fields; reason = Used_as_value} :: !decisions
    | _ -> ()
  in
  if not (Mindmap_env.is_empty !demoted) then
    Core_passes.Modutil.struct_iter
      (function Core.Decl.Inductive {entity = kn; definition = ind} -> decide kn ind | _ -> ())
      (function Core.Signature.Declaration.Inductive {entity = kn; definition = ind} -> decide kn ind | _ -> ())
      (fun _ -> ())
      struc;
  List.rev !decisions

let plan (facts : Program_facts.t) struc =
  let input =
    if Base.Pipeline_trace.enabled () || Sys.getenv_opt "CRANE_CHECK_IR" <> None then
      Some (Core.Fingerprint.structure struc)
    else None
  in
  let aligned = functor_alignment struc in
  { input;
    config = Base.Table.unit_config ~names:facts.used_customs;
    inductive_kinds = aligned @ value_use_demotion aligned struc;
    template_kinds = [];
    modules = Core_plan.Module_plan.empty;
    representation =
      {module_names = []; names = []; referenced_names = []; field_names = []; pointer_fields = [];
        unmerged_wrappers = [];
        promoted_inductives = [];
        accessors = [];
        nested_structs = [];
        scopes = Core_plan.Scope_plan.empty;
        instance_promoted_types = [] };
    callables = [];
    instance_methods = [];
    assumed_callables = [] }

let with_template_kinds t template_kinds = {t with template_kinds}

let with_layout t modules representation (callables, instance_methods) assumed_callables =
  {t with modules; representation; callables; instance_methods; assumed_callables}

let same_instance_methods a b =
  List.length a = List.length b
  && List.for_all
       (fun (r, ms) ->
         match List.find_opt (fun (r', _) -> GlobRef.UserOrd.equal r r') b with
         | Some (_, ms') ->
           List.equal (fun (n, abi) (n', abi') -> Id.equal n n' && Core_plan.Callable_abi.equal abi abi') ms ms'
         | None -> false )
       a

let same_callables a b =
  List.length a = List.length b
  && List.for_all
       (fun abi ->
         List.exists
           (fun abi' ->
             GlobRef.UserOrd.equal (Core_plan.Callable_abi.callee abi) (Core_plan.Callable_abi.callee abi')
             && Core_plan.Callable_abi.equal abi abi' )
           b )
       a

let kind_equal a b =
  let fields_equal = List.equal (fun (f : Core.Record.Field.t) (f' : Core.Record.Field.t) ->
        Option.equal GlobRef.UserOrd.equal f.projection f'.projection) in
  match (a, b) with
  | Core.Inductive.Kind.Coinductive, Core.Inductive.Kind.Coinductive
  | Core.Inductive.Kind.Inductive, Core.Inductive.Kind.Inductive -> true
  | Core.Inductive.Kind.Record f, Core.Inductive.Kind.Record f'
  | Core.Inductive.Kind.Type_class f, Core.Inductive.Kind.Type_class f' ->
    fields_equal f f'
  | (Core.Inductive.Kind.Coinductive | Core.Inductive.Kind.Inductive | Core.Inductive.Kind.Record _
  | Core.Inductive.Kind.Type_class _), _ -> false

(* The same global under the same name. *)
let same_name (r, s) (r', s') = GlobRef.UserOrd.equal r r' && String.equal s s'

let equal a b =
  Bool.equal a.config.concurrent b.config.concurrent
  && List.equal
    (fun d d' -> MutInd.UserOrd.equal d.block d'.block && d.reason = d'.reason && kind_equal d.kind d'.kind)
    a.inductive_kinds b.inductive_kinds
  && List.equal
       (fun (r, k) (r', k') -> GlobRef.UserOrd.equal r r' && Cpp_ir.Tparam_kinds.equal k k')
       a.template_kinds b.template_kinds
  && Core_plan.Module_plan.equal a.modules b.modules
  && List.equal
       (fun (mp, s) (mp', s') -> ModPath.equal mp mp' && String.equal s s')
       a.representation.module_names b.representation.module_names
  && List.equal same_name a.representation.names b.representation.names
  && List.equal same_name a.representation.referenced_names b.representation.referenced_names
  && List.equal
       (fun (r, ids) (r', ids') -> GlobRef.UserOrd.equal r r' && List.equal Id.equal ids ids')
       a.representation.field_names b.representation.field_names
  && List.equal
       (fun (r, c, fs) (r', c', fs') -> GlobRef.UserOrd.equal r r' && String.equal c c' && fs = fs')
       a.representation.pointer_fields b.representation.pointer_fields
  && List.equal
       (fun (n, mp) (n', mp') -> String.equal n n' && Names.ModPath.equal mp mp')
       a.representation.unmerged_wrappers b.representation.unmerged_wrappers
  && List.equal GlobRef.UserOrd.equal a.representation.promoted_inductives b.representation.promoted_inductives
  && List.equal GlobRef.UserOrd.equal a.representation.accessors b.representation.accessors
  && List.equal
       (fun (n, o) (n', o') -> String.equal n n' && Unit_plan.Cpp_state.nested_struct_owner_equal o o')
       a.representation.nested_structs b.representation.nested_structs
  && Core_plan.Scope_plan.equal_plans a.representation.scopes b.representation.scopes
  && List.equal
       (fun (r, bs) (r', bs') ->
         GlobRef.UserOrd.equal r r'
         && List.equal (fun (v, t) (v', t') -> Id.equal v v' && Base.Core_util.eq_core_type t t') bs bs' )
       a.representation.instance_promoted_types b.representation.instance_promoted_types
  && same_callables a.callables b.callables
  && same_instance_methods a.instance_methods b.instance_methods
  && List.equal
       (fun (r, ps) (r', ps') -> GlobRef.UserOrd.equal r r' && List.equal Core_plan.Param_pos.equal ps ps')
       a.assumed_callables b.assumed_callables

let record_kinds t struc =
  List.iter
    (fun {block; kind; _} ->
      Base.Table.add_inductive_kind block kind;
      let record kn (ind : Core.Inductive.t) = if MutInd.UserOrd.equal kn block then ind.kind <- kind in
      Core_passes.Modutil.struct_iter
        (function Core.Decl.Inductive {entity = kn; definition = ind} -> record kn ind | _ -> ())
        (function Core.Signature.Declaration.Inductive {entity = kn; definition = ind} -> record kn ind | _ -> ())
        (fun _ -> ())
        struc )
    t.inductive_kinds

let check_kinds_recorded t =
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then
  List.iter
    (fun {block; _} ->
      if not (Option.equal kind_equal (Base.Table.inductive_kind_of (GlobRef.IndRef (block, 0))) (kind_of t block)) then
        CErrors.anomaly Pp.(str "Crane: the recorded inductive kinds no longer agree with the plan.") )
    t.inductive_kinds
