(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ types of bound variables during lowering: a binder's type
    recorded when it is pushed (parameters, let and pattern binders) and read
    back, whether a read is of a box, and the representation plan's answer
    for a binder or a position, held to lowering's under [CRANE_CHECK_IR]. *)

open Names
open Util
open Translation_state
open Type_util

(** Binder-type state: {!Translation_state.cpp_binder_types}, every binder's
    C++ type tagged with what decided it. *)
type binder_env = (Cpp_ir.Lowered.Type.t * binder_origin) IntMap.t

(** Strip the const/reference decoration a parameter type carries, leaving the
    type of the value the binder denotes.  [const auto &] assigns [Tauto]:
    a deduced parameter is never physically a box. *)
let rec strip_param_wrappers : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Reference (_, t) | Const t -> strip_param_wrappers t
  | t -> t

(** Whether the binder at de Bruijn index [i] was typed by a pattern match.
    A binding-site assignment does not overwrite such an entry: the
    instantiation the branch pinned down is the more precise of the two. *)
let pinned_by_pattern i =
  match IntMap.find_opt i (!tctx).lexical.cpp_binder_types with
  | Some (_, Bpattern) -> true
  | _ -> false

(** The C++ type the binder at de Bruijn index [i] was decided to have: the
    instantiation a pattern match pinned down where there is one, and
    otherwise the type assigned where the binder was bound. *)
let binder_cpp_type i : Cpp_ir.Lowered.Type.t option =
  Option.map fst (IntMap.find_opt i (!tctx).lexical.cpp_binder_types)

(** The C++ type a pattern match pinned down for the binder at de Bruijn index
    [i], if this branch pinned one.  A binding-site assignment is not an
    answer here: it says what the binder's Core type converts to, which for a
    field read out of an erased carrier is the type the value {e would} have
    had, not the [std::any] it is actually stored as. *)
let pattern_binder_type i : Cpp_ir.Lowered.Type.t option =
  match IntMap.find_opt i (!tctx).lexical.cpp_binder_types with
  | Some (t, Bpattern) -> Some t
  | _ -> None

(** Save the current binder-type state for later restoration. *)
let save_erased_env () : binder_env = (!tctx).lexical.cpp_binder_types

(** Restore binder-type state saved by {!save_erased_env}. *)
let restore_erased_env saved = set_lexical (fun l -> { l with cpp_binder_types = saved })

(** Record the C++ type of the pattern variable at de Bruijn index [i].

    A box is never overwritten by a concrete type.  Several passes describe
    the same binder -- an outer erased pair match says every field is a
    [std::any], and the per-field pass then reports the definition-site type
    the scrutinee instantiates -- and the erased view is the one that
    describes the runtime value. *)
let record_binder_type i (t : Cpp_ir.Lowered.Type.t) =
  let boxed_by_pattern =
    match IntMap.find_opt i (!tctx).lexical.cpp_binder_types with
    | Some (Obligation Opaque_type, Bpattern) -> false
    | Some (t', Bpattern) -> Translation_types.resolves_to_any_type t'
    | _ -> false
  in
  if not boxed_by_pattern then
    set_lexical (fun l -> { l with cpp_binder_types = IntMap.add i (t, Bpattern) l.cpp_binder_types })

(** Whether the pattern variable at de Bruijn index [i] holds a box, and so
    must be recovered with an [any_cast] before it is used at a concrete
    type.  Read off the recorded type rather than tracked alongside it: a
    binder is boxed exactly when the scrutinee's instantiation erased its
    field. *)
let binder_is_boxed i =
  (* [Topaque] prints as [std::any] but admits only that the representation is
     unknown here; nothing may be unboxed on the strength of it.  The
     distinction is {!Translation_coerce.coerce}'s, and a binder's answer has to draw it too. *)
  match binder_cpp_type i with
  | Some (Obligation Opaque_type) | None -> false
  | Some t -> Translation_types.resolves_to_any_type t

(* How a binder kind is named in probe output. *)
let binder_kind_name = function
  | Kouter -> "outer"
  | Kparameter -> "parameter"
  | Klet -> "let"
  | Kfix -> "fix"
  | Kpattern -> "pattern"

(** [read_is_boxed i occ] -- whether the variable read at [occ], of the
    binder at de Bruijn index [i], holds a box: the answer the region's
    representation plan ({!Representation_plan.region}) gives for [occ],
    which plans every read of every region.  A read it has no answer for is
    an anomaly.  Under [CRANE_CHECK_IR] the answer is held to
    {!binder_is_boxed}, the one read off the binder's recorded C++ type. *)
let read_is_boxed i occ =
  let live () = binder_is_boxed i in
  let describe live planned =
    Pp.(
      str "a read"
      ++ (match (!tctx).input.body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
      ++ str ": lowering "
      ++ str (if live then "boxes" else "does not box")
      ++ str " its binder, the plan " ++ str planned)
  in
  match List.assq_opt occ (!tctx).lexical.planned_reads with
  | Some {rd_boxed; rd_kind} ->
    ( if Probe.checking () then
        let live = live () in
        let agrees = rd_boxed = live in
        Probe.hit "repr-read" (fun () ->
            (if agrees then "agree " else "disagree ")
            ^ binder_kind_name rd_kind
            ^ if live then " live-boxed" else " live-value");
        if not agrees then
          Probe.violation "variable read representation"
            (describe live ((if rd_boxed then "boxes" else "does not") ^ " (" ^ binder_kind_name rd_kind ^ ")")) );
    rd_boxed
  | None ->
    CErrors.anomaly
      Pp.(
        str "a read of " ++ int i
        ++ (match (!tctx).input.body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
        ++ str " is in no representation plan of the region it is lowered in")

(** [planned_binder_type ~use ~agree i occ] -- the C++ type the region's
    representation plan ({!Representation_plan.region}) gives the binder of
    the variable [i] read at [occ], where it plans one.  Under
    [CRANE_CHECK_IR] held to the type lowering recorded for the binder
    ({!binder_cpp_type}) through [agree], which says whether the two give
    the decision [use] names the same answer.  A read the plan has no answer
    for is an anomaly. *)
(* A C++ type, written compactly for a probe or a violation report. *)
let rec type_shape : Cpp_ir.Lowered.Type.t -> string = function
  | Function (dom, cod) -> "fn(" ^ String.concat "," (List.map type_shape dom) ^ ")->" ^ type_shape cod
  | Any -> "any"
  | Auto -> "auto"
  | Obligation Opaque_type -> "opaque"
  | Const t -> "const " ^ type_shape t
  | Reference (_, t) -> "ref " ^ type_shape t
  | Entity_application (g, args, _) ->
    Pp.string_of_ppcmds (GlobRef.print g) ^ "<" ^ String.concat "," (List.map type_shape args) ^ ">"
  | Variable (Index (i, Some id)) -> "T" ^ string_of_int i ^ ":" ^ Id.to_string id
  | Variable (Index (i, None)) -> "T" ^ string_of_int i
  | Variable (Named id) -> "N:" ^ Id.to_string id
  | Shared_pointer t -> "sp " ^ type_shape t
  | Variant _ -> "variant"
  | Member (t, id) -> type_shape t ^ "::" ^ Id.to_string id
  | Named (id, args) -> "id:" ^ Id.to_string id ^ "<" ^ String.concat "," (List.map type_shape args) ^ ">"
  | External (n, _) -> "ext:" ^ n
  | Promoted_member id -> "prom:" ^ Id.to_string id
  | Instance (id, _) -> "inst:" ^ Id.to_string id
  | Erased _ -> "erased"
  | Apply (h, args) -> "app(" ^ type_shape h ^ ")<" ^ String.concat "," (List.map type_shape args) ^ ">"
  | In_namespace (_, t) -> "ns " ^ type_shape t
  | _ -> "other"

let planned_binder_type ~use ~agree i occ =
  let show = function Some t -> type_shape t | None -> "none" in
  match List.assq_opt occ (!tctx).lexical.planned_reads with
  | Some {rd_type; rd_kind; _} ->
    ( if Probe.checking () then
        let live = binder_cpp_type i in
        let agrees = agree rd_type live in
        Probe.hit "repr-type" (fun () ->
            use ^ (if agrees then " agree " else " disagree ") ^ binder_kind_name rd_kind ^ " plan " ^ show rd_type
            ^ " live " ^ show live
            ^
              (match (!tctx).input.body_owner with Some r -> " in "
                ^ Pp.string_of_ppcmds (GlobRef.print r) | None -> ""));
        if not agrees then
          Probe.violation "variable read binder type"
            Pp.(
              str "a read for " ++ str use
              ++ (match (!tctx).input.body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
              ++ str ": lowering's binder is " ++ str (show live) ++ str ", the plan's "
              ++ str (show rd_type)) );
    rd_type
  | None ->
    CErrors.anomaly
      Pp.(
        str "a read of " ++ int i
        ++ (match (!tctx).input.body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
        ++ str " is in no representation plan of the region it is lowered in")

(** [planned_position occ ~live] -- the C++ type the position of the
    coercion at [occ] is generated against, as the region's position plan
    ({!Position_plan.region}) gives it, under [CRANE_CHECK_IR] held to
    [live], the type lowering threaded there.  A coercion the plan of the
    region it is lowered in does not reach is an anomaly. *)
let planned_position occ ~(live : Cpp_ir.Lowered.Type.t option) =
  let show = function Some t -> type_shape t | None -> "none" in
  let owner () =
    match (!tctx).input.body_owner with Some r -> " in " ^ Pp.string_of_ppcmds (GlobRef.print r) | None -> "" in
  match List.find_opt (fun (o, _) -> Core.Occurrence.equal o occ) (!tctx).lexical.planned_positions with
  | Some (_, planned) ->
    if Probe.checking () then begin
      let agrees = planned = live in
      Probe.hit "magic-pos"
        (fun () -> if agrees then "agree" else "disagree plan " ^ show planned ^ " live " ^ show live ^ owner ());
      if not agrees then
        Probe.violation "coercion position"
          Pp.(str
              ("a coercion" ^ owner () ^ " is lowered against " ^ show live
                ^ ", the plan's position is " ^ show planned))
    end;
    planned
  | None ->
    CErrors.anomaly Pp.(str ("a coercion" ^ owner () ^ " is in no position plan of the region it is lowered in"))

(** [planned_binder_type_or_derive ~use ~agree env i occ] -- the
    planned C++ type of the binder of the variable [i] read at [occ]
    ({!planned_binder_type}), and failing one the conversion of its Core type
    under the current scope: an answer for every binder, where the plan
    deliberately has none for one at [Topaque], a dummy, or a conversion
    that failed.  Under [CRANE_CHECK_IR] the answer is held, through
    [agree], to the same derivation from the type lowering recorded for the
    binder ({!binder_cpp_type}). *)
let planned_binder_type_or_derive ~use ~agree env i occ =
  let derive = function
    | Some _ as t -> t
    | None -> Option.map (Translation_types.cpp_of_core env) (get_env_type_opt i)
  in
  derive (planned_binder_type ~use ~agree:(fun p l -> agree (derive p) (derive l)) i occ)

(** Record the C++ type of each of the [ids] most recently pushed binders,
    without pushing them again.  [?cpp] overrides the conversion for binders
    whose declared C++ type the caller has already computed; a declaration is
    always a better answer than re-deriving from the Core type, because it is
    what the emitted code actually says.  Call sites that only learn the
    declared types after pushing (a lambda decides [const auto &] for its
    erased parameters well after opening their scope) call this a second time
    to correct the assignment. *)
let assign_binder_types ?(cpp = []) env (ids : (Id.t * Core.Type.t) list) =
  List.iteri
    (fun j (_, core_ty) ->
      let assigned : Cpp_ir.Lowered.Type.t option =
        match List.nth_opt cpp j with
        | Some (Some t) -> Some (strip_param_wrappers t)
        | _ -> (try Some (Translation_types.cpp_of_core env core_ty) with _ -> None)
      in
      match assigned with
      | Some t
        when t <> Obligation Opaque_type && not (is_cpp_dummy_type t)
             && not (pinned_by_pattern (j + 1)) ->
        set_lexical (fun l -> { l with cpp_binder_types = IntMap.add (j + 1) (t, Bbinding) l.cpp_binder_types })
      | _ -> ())
    ids

(** [push_binders env ids] is {!push_env_types} plus the C++ type assignment:
    each binder's C++ type is decided here, once, at the point it is bound,
    and recorded in {!Translation_state.cpp_binder_types}.

    This is the assignment that use sites are being migrated onto.  Today they
    re-derive a binder's C++ type wherever they need it, from whatever type
    variable scope happens to be in effect, so two uses of one binder can
    disagree about whether it holds a box -- which is what a [bad_any_cast]
    is.  Deciding at the binding site makes that disagreement unrepresentable.

    [?cpp] overrides the conversion for a binder whose type the caller already
    knows better than its Core type says, which is the case for pattern
    variables: it is the scrutinee's instantiation, not the field's
    definition-site type, that fixes those.  A [None] entry (or a short list)
    falls back to converting the Core type.

    The assignment records only types it actually knows.  A conversion that
    yields [Topaque] means the scope could not resolve the binder at all, and
    a dummy stands for a value that is not there; recording either would turn
    ignorance into the assertion "this binder holds a box", which is the one
    thing an opaque type exists to refuse.  Such binders keep no entry, so
    a reader still falls through to whatever it does today.  Conversion
    failures are skipped for the same reason, and so that a binder Crane
    cannot currently type does not become a new way for extraction to fail. *)
let push_binders ?(cpp = []) env (ids : (Id.t * Core.Type.t) list) =
  push_env_types ids;
  assign_binder_types ~cpp env ids

(** [with_binders env ids f] runs [f] with [ids] (innermost first) pushed by
    {!push_binders}, and closes that scope however [f] leaves.

    It is the type half of a [push_vars'] that bound the same [ids] in the
    name environment: a body generated under the extended name environment
    reads its binders' types by de Bruijn index, so a name pushed without its
    type makes every lookup beneath it read the binder one further out. *)
let with_binders ?cpp env ids f =
  let saved = (!tctx).lexical.env_types in
  push_binders ?cpp env ids;
  Fun.protect ~finally:(fun () -> restore_env_types saved) f

(** [push_parameters env ids] is {!push_binders} for a declaration's
    parameters, whose class-typed ones are its dictionaries. *)
let push_parameters ?(cpp = []) env (ids : (Id.t * Core.Type.t) list) =
  push_env_parameters ids;
  assign_binder_types ~cpp env ids
