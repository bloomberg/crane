(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml

type kind_reason =
  | Functor_alignment
  | Used_as_value

type kind_decision = {
  block : MutInd.t;
  kind : inductive_kind;
  reason : kind_reason;
}

type representation = {
  module_names : (ModPath.t * string) list;
  names : (GlobRef.t * string) list;
  referenced_names : (GlobRef.t * string) list;
  field_names : (GlobRef.t * Id.t list) list;
  pointer_fields : (GlobRef.t * string * (int * bool) list) list;
  unmerged_wrappers : string list;
  promoted_inductives : GlobRef.t list;
  accessors : GlobRef.t list;
  nested_structs : (string * Cpp_state.nested_struct_owner) list;
  scopes : Scope_plan.t;
  instance_promoted_types : (GlobRef.t * (Id.t * Miniml.ml_type) list) list;
}

type t = {
  input : Ml_fingerprint.t option;
  inductive_kinds : kind_decision list;
  template_kinds : (GlobRef.t * Tparam_kinds.t) list;
  modules : Module_plan.t;
  representation : representation;
  callables : Callable_abi.t list;
  instance_methods : (GlobRef.t * (Id.t * Callable_abi.t) list) list;
  assumed_callables : (GlobRef.t * Param_pos.orig Param_pos.pos list) list;
}

(** The last of [decisions] about [kn]. *)
let decided decisions kn =
  List.fold_left
    (fun acc d -> if MutInd.UserOrd.equal d.block kn then Some d.kind else acc)
    None decisions

let kind_of t kn = decided t.inductive_kinds kn

(** The kind [ind] has once [decisions] are installed. *)
let kind_after decisions kn ind = Option.default ind.ind_kind (decided decisions kn)

(** {!Table.is_typeclass}, once [decisions] are installed. *)
let is_typeclass_after decisions r =
  let of_block kn =
    match decided decisions kn with
    | Some (TypeClass _) -> true
    | Some _ -> false
    | None -> Table.is_typeclass r
  in
  match r with
  | GlobRef.IndRef (kn, _) | GlobRef.ConstructRef ((kn, _), _) -> of_block kn
  | GlobRef.ConstRef _ | GlobRef.VarRef _ -> Table.is_typeclass r

(** Give a functor application's inductives the kind the functor's own body
    gave them.

    [Module FN := F N] does not alias [F]'s declarations: Rocq builds a second
    copy of every inductive in the body, with a kernel name of its own, and
    Crane classifies that copy independently.  The two answers can differ --
    instantiation registers a class declared inside a functor in Rocq's type
    class database while the body's own copy stays unregistered, so [F.Cl] is
    a {!Record} and [FN.Cl] a {!TypeClass}.  One declaration with two kinds is
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
  let body_kinds : (string * Label.t, inductive_kind) Hashtbl.t = Hashtbl.create 16 in
  let rec body_of (me : ml_module_expr) =
    match me with MEfunctor (_, _, me) -> body_of me | me -> me
  in
  let rec collect_expr (me : ml_module_expr) =
    match me with
    | MEstruct (mp, sel) ->
      List.iter
        (fun (l, se) ->
          match se with
          | SEdecl (Dind (_, ind)) -> Hashtbl.replace body_kinds (ModPath.to_string mp, l) ind.ind_kind
          | SEmodule m -> collect_expr (body_of m.ml_mod_expr)
          | _ -> () )
        sel
    | MEfunctor (_, _, me) -> collect_expr me
    | MEident _ | MEapply _ -> ()
  in
  (* The functor an application applies, however many arguments it takes. *)
  let rec applied_functor (me : ml_module_expr) =
    match me with
    | MEapply (me, _) -> applied_functor me
    | MEident mp -> Some mp
    | MEstruct _ | MEfunctor _ -> None
  in
  let decisions = ref [] in
  let align_sig mp_functor (mt : ml_module_type) =
    match mt with
    | MTsig (_, sigl) ->
      List.iter
        (fun (l, sp) ->
          match sp with
          | Spec (Sind (kn, ind)) -> (
            let aligned =
              match
                ( Hashtbl.find_opt body_kinds (ModPath.to_string mp_functor, l),
                  kind_after !decisions kn ind )
              with
              | Some (TypeClass _), Record fields -> Some (TypeClass fields)
              | Some (Record _), TypeClass fields -> Some (Record fields)
              | _ -> None
            in
            match aligned with
            | Some kind -> decisions := {block = kn; kind; reason = Functor_alignment} :: !decisions
            | None -> () )
          | Spec _ | Smodule _ | Smodtype _ -> () )
        sigl
    | MTident _ | MTfunsig _ | MTwith _ -> ()
  in
  let rec walk_expr (me : ml_module_expr) =
    match me with
    | MEstruct (_, sel) -> List.iter walk_elem sel
    | MEfunctor (_, _, me) -> walk_expr me
    | MEident _ | MEapply _ -> ()
  and walk_elem (_l, se) =
    match se with
    | SEmodule m ->
      Option.iter (fun mp -> align_sig mp m.ml_mod_type) (applied_functor m.ml_mod_expr);
      walk_expr m.ml_mod_expr
    | SEdecl _ | SEmodtype _ -> ()
  in
  List.iter
    (fun (_mp, sel) ->
      List.iter
        (fun (_l, se) -> match se with SEmodule m -> collect_expr (body_of m.ml_mod_expr) | _ -> ())
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
    | Tglob ((GlobRef.IndRef (kn, _) as r), l, _) ->
      if is_typeclass r then demote kn;
      List.iter scan_arg l
    | Tglob (_, l, _) -> List.iter scan_arg l
    | Tarr (a, b) ->
      scan_arg a;
      scan_arg b
    | Tmeta {contents = Some t} -> scan_arg t
    | _ -> ()
  in
  let rec scan_type = function
    | Tglob (_, l, _) -> List.iter scan_arg l
    | Tarr (a, b) ->
      scan_type a;
      scan_type b
    | Tmeta {contents = Some t} -> scan_type t
    | _ -> ()
  in
  (* A constructor field is data outright, so a class named as the field's own
     type is used as data too -- not only one buried in its arguments.  A
     class's own field is not: a superclass field is what a concept refines,
     and demoting it would turn the refinement into a member. *)
  let scan_ind kn ind =
    let scan_field =
      match kind_after prior kn ind with TypeClass _ -> scan_type | _ -> scan_arg
    in
    Array.iter (fun p -> Array.iter (List.iter scan_field) p.ip_types) ind.ind_packets
  in
  (* A class value a definition computes from data is data: the struct an
     instance is otherwise emitted as is fixed at compile time, so it cannot
     stand for [mkDict base], whose fields depend on an argument.  Type and
     instance arguments do not count -- those an instance struct takes as
     template parameters. *)
  let scan_computed_class ty =
    let rec walk had_value = function
      | Tarr (a, b) ->
        let is_erased =
          match a with
          | Tdummy _ -> true
          | Tglob (r, _, _) -> is_typeclass r
          | _ -> false
        in
        walk (had_value || not is_erased) b
      | Tmeta {contents = Some t} -> walk had_value t
      | Tglob ((GlobRef.IndRef (kn, _) as r), _, _) when had_value ->
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
      (Mlutil.ast_map_types
         (fun t ->
           scan_type t;
           t )
         body)
  in
  let scan_decl = function
    | Dind (kn, ind) -> scan_ind kn ind
    | Dtype (_, _, u) -> scan_type u
    | (Dterm _ | Dfix _) as d ->
      List.iter
        (fun fd ->
          scan_term_type fd.fd_type;
          scan_body fd.fd_body )
        (Mlutil.term_defs d)
  in
  let scan_spec = function
    | Sind (kn, ind) -> scan_ind kn ind
    | Stype (_, _, ot) -> Option.iter scan_type ot
    | Sval (_, _, u) -> scan_term_type u
  in
  Modutil.struct_iter scan_decl scan_spec (fun _ -> ()) struc;
  let decisions = ref [] in
  let decide kn ind =
    match kind_after prior kn ind with
    | TypeClass fields when Mindmap_env.mem kn !demoted ->
      decisions := {block = kn; kind = Record fields; reason = Used_as_value} :: !decisions
    | _ -> ()
  in
  if not (Mindmap_env.is_empty !demoted) then
    Modutil.struct_iter
      (function Dind (kn, ind) -> decide kn ind | _ -> ())
      (function Sind (kn, ind) -> decide kn ind | _ -> ())
      (fun _ -> ())
      struc;
  List.rev !decisions

let plan (_ : Program_facts.t) struc =
  let input =
    if Pipeline_trace.enabled () || Sys.getenv_opt "CRANE_CHECK_IR" <> None then
      Some (Ml_fingerprint.structure struc)
    else None
  in
  let aligned = functor_alignment struc in
  { input;
    inductive_kinds = aligned @ value_use_demotion aligned struc;
    template_kinds = [];
    modules = Module_plan.empty;
    representation = {module_names = []; names = []; referenced_names = []; field_names = []; pointer_fields = []; unmerged_wrappers = [];
        promoted_inductives = [];
        accessors = [];
        nested_structs = [];
        scopes = Scope_plan.empty;
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
           List.equal (fun (n, abi) (n', abi') -> Id.equal n n' && Callable_abi.equal abi abi') ms ms'
         | None -> false )
       a

let same_callables a b =
  List.length a = List.length b
  && List.for_all
       (fun abi ->
         List.exists
           (fun abi' ->
             GlobRef.UserOrd.equal (Callable_abi.callee abi) (Callable_abi.callee abi')
             && Callable_abi.equal abi abi' )
           b )
       a

let kind_equal a b =
  let fields_equal = List.equal (fun (r, _) (r', _) -> Option.equal GlobRef.UserOrd.equal r r') in
  match (a, b) with
  | Coinductive, Coinductive | Standard, Standard -> true
  | Record f, Record f' | TypeClass f, TypeClass f' -> fields_equal f f'
  | (Coinductive | Standard | Record _ | TypeClass _), _ -> false

let same_name (r, s) (r', s') = GlobRef.UserOrd.equal r r' && String.equal s s'

let equal a b =
  List.equal
    (fun d d' -> MutInd.UserOrd.equal d.block d'.block && d.reason = d'.reason && kind_equal d.kind d'.kind)
    a.inductive_kinds b.inductive_kinds
  && List.equal
       (fun (r, k) (r', k') -> GlobRef.UserOrd.equal r r' && Tparam_kinds.equal k k')
       a.template_kinds b.template_kinds
  && Module_plan.equal a.modules b.modules
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
  && List.equal String.equal a.representation.unmerged_wrappers b.representation.unmerged_wrappers
  && List.equal GlobRef.UserOrd.equal a.representation.promoted_inductives b.representation.promoted_inductives
  && List.equal GlobRef.UserOrd.equal a.representation.accessors b.representation.accessors
  && List.equal
       (fun (n, o) (n', o') -> String.equal n n' && Cpp_state.nested_struct_owner_equal o o')
       a.representation.nested_structs b.representation.nested_structs
  && Scope_plan.equal_plans a.representation.scopes b.representation.scopes
  && List.equal
       (fun (r, bs) (r', bs') ->
         GlobRef.UserOrd.equal r r'
         && List.equal (fun (v, t) (v', t') -> Id.equal v v' && Mlutil.eq_ml_type t t') bs bs' )
       a.representation.instance_promoted_types b.representation.instance_promoted_types
  && same_callables a.callables b.callables
  && same_instance_methods a.instance_methods b.instance_methods
  && List.equal
       (fun (r, ps) (r', ps') -> GlobRef.UserOrd.equal r r' && List.equal Param_pos.equal ps ps')
       a.assumed_callables b.assumed_callables
