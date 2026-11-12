(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** The passes a MiniCpp declaration goes through between translation and the
    printer.  See [cpp_pipeline.mli]. *)

open Minicpp

(** {2 Tracing}

    [CRANE_TRACE_PASSES] names declarations to trace through {!finish}: all
    of them when it is [1], otherwise those whose name contains it.  For each,
    one line reports which passes changed the declaration and how many nodes
    it held before and after -- enough to see which pass did something,
    without a printer, whose queues a dump would disturb. *)

(** The name of [decl] if [CRANE_TRACE_PASSES] asks for it. *)
let trace_pattern = lazy (Sys.getenv_opt "CRANE_TRACE_PASSES")

let traced decl =
  match Lazy.force trace_pattern with
  | None | Some "" -> None
  | Some pattern ->
    (* An unnamed declaration -- an assignment, an alias, a group -- is named
       by what it declares. *)
    let rec names = function
      | Dnspace (None, ds) -> List.concat_map names ds
      | Dtemplate (_, _, d) -> names d
      | Dfields {ds_ref = r; _} | Denum {de_ref = r; _} | Dasgn {da_ref = r; _} -> [r]
      | Dusing {du_name = r; _} -> [r]
      | d -> Option.List.cons (decl_globref d) []
    in
    let name =
      match names decl with
      | [] -> "<anonymous>"
      | rs ->
        String.concat ", "
          (List.map (fun r -> Pp.string_of_ppcmds (Table.safe_pr_global r)) rs)
    in
    let contains s sub =
      let n = String.length s and m = String.length sub in
      let rec at i = i + m <= n && (String.sub s i m = sub || at (i + 1)) in
      at 0
    in
    if pattern = "1" || contains name pattern then Some name else None

(** How many expressions, statements and types [d] holds. *)
let node_count (d : cpp_decl) =
  let n = ref 0 in
  let ft t = map_cpp_type (fun t -> incr n; t) t in
  let rec fe e = incr n; map_expr fe fs ft e
  and fs s = incr n; map_stmt fe fs ft s in
  ignore (map_decl fe fs ft d);
  !n

(** A pass over a declaration on its way to the seam. *)
let on_decl = Pipeline_trace.pass

(** The passes below that discharge an {!obligation}, named once so that
    the list of obligations refers to the pass rather than to its name. *)
let constraints = on_decl "constraints" Minicpp.settle_constraints

let casts = Pipeline_trace.pass "casts" Cpp_erasure.resolve_casts
let free_tvars = Pipeline_trace.pass "free_tvars" Cpp_erasure.bind_free_tvars
let boxed_reads = Pipeline_trace.pass "boxed_reads" Cpp_erasure.lower_boxed_reads
let template_args = Pipeline_trace.pass "template_args" Cpp_erasure.supply_template_args
let method_calls = Pipeline_trace.pass "method_calls" Cpp_erasure.lower_method_calls
let projections = Pipeline_trace.pass "projections" Cpp_erasure.lower_projections
let conditionals = Pipeline_trace.pass "conditionals" Cpp_erasure.lower_conditionals
let access_moves = Pipeline_trace.pass "access_moves" Cpp_erasure.lower_access_moves
let constexpr = Pipeline_trace.pass "constexpr" Cpp_erasure.decide_constexpr
let foreign = Pipeline_trace.pass "foreign" Cpp_erasure.instantiate_foreign
let qualifiers = Pipeline_trace.pass "qualifiers" Cpp_erasure.lower_qualifiers
let pointer_slots = Pipeline_trace.pass "pointer_slots" Cpp_erasure.lower_pointer_slots
let scrutinees = Pipeline_trace.pass "scrutinees" Cpp_erasure.name_scrutinees
let captures = Pipeline_trace.pass "captures" Cpp_erasure.decide_captures
let initialisers = Pipeline_trace.pass "initialisers" Cpp_erasure.invoke_capturing_initialisers

(** A pass before the seam: over CppIR, or over the MiniCpp a lowered
    declaration converts back to ({!Cpp_ir_to_legacy_minicpp}). *)
type stage =
  | Ir of Cpp_ir.Lowered.Decl.t Pipeline_trace.pass
  | Legacy of cpp_decl Pipeline_trace.pass
[@@warning "-37"]

let stage_name = function Ir p -> p.name | Legacy p -> p.name

(** Every pass before the {!Cpp_erasure} seam, in the order they run. *)
let minicpp_passes : stage list =
  List.map (fun p -> Legacy p) @@
  [ (* Control is lowered as it is generated, from its ControlIR
       ({!Control_to_legacy_minicpp}): nothing is left here to lower.  Under
       [CRANE_CHECK_IR] what is emitted must be what control lowering
       recorded deciding, every loop the plan commits to decided, and no
       lowered loop still makes a call it takes. *)
    on_decl "control" (fun d ->
        if Probe.checking () then Control_to_legacy_minicpp.check_lowered d;
        d );
    (* Closures made and used in one place become the code they stand for.
       The moves they hold were decided over Core, the arguments a local
       fixpoint applied in place binds its parameters to in order
       ({!Ownership_ir.evaluated_first}). *)
    on_decl "local_closures" Cpp_local_closures.transform_decl;
    (* A function's constants are declared once at its top, now that nothing
       moves code between functions -- and before the passes that rewrite what
       an initialiser holds: [depth] splits a deep one into bindings, which in
       a static's initialiser run once. *)
    on_decl "constants" Cpp_constants.decl;
    (* The temporaries Normalize named for loopification and loopification did
       not need go back where they are read. *)
    on_decl "temporaries" Cpp_temporaries.decl;
    (* An argument a mapping would splice, and so evaluate, more than once is
       named once -- after the temporaries went back, so that none of them is
       put back into the text that repeats it. *)
    on_decl "shared_args" Cpp_shared_args.transform_decl;
    (* Small local simplifications, before ownership reads the uses. *)
    on_decl "simplify" Cpp_simplify.transform_decl;
    (* An initialiser nested deeper than a compiler will parse becomes a run of
       bindings; everything shallower is left as it stands. *)
    on_decl "depth" Cpp_depth.flatten;
    (* A returned value is moved by the language; writing the move there
       only suppresses copy elision. *)
    on_decl "return_moves" Return_moves.drop_return_moves;
    (* Which callable parameters keep a constraint is decided here, with the
       body that decides it in hand; the printer writes what it is given. *)
    constraints ]

(** Writing a type down is what decides its representation, so the [Topaque]
    slots are settled before anything reads the declaration as final.
    Crossing this seam is what gives {!Cpp_erasure.settled}, the printer's
    input type. *)
let seam = "materialise"

(** Every pass after the seam, in the order they run. *)
let settled_passes : Cpp_erasure.settled Pipeline_trace.pass list =
  [ casts;
    (* With the heads final, a body naming a type variable no head declares
       is a name nothing in scope introduces; spell it [std::any] rather than
       emit it. *)
    free_tvars;
    (* With every type final, a read of a boxed value the context needs at a
       concrete type is written down. *)
    boxed_reads;
    (* A type argument a mapping's template names and the call does not
       supply was erased, and is written down as one. *)
    template_args;
    (* A call of a methodified function becomes the member call it is, so
       the printer spells the call it is given. *)
    method_calls;
    (* So does a projection, applied or named as a value. *)
    projections;
    (* A lambda invoked only to choose between two values is the choice. *)
    conditionals;
    (* A member read moves the member, not the object it is read from. *)
    access_moves;
    (* With every type final, which definitions may be [constexpr]. *)
    constexpr ]

(** With the declaration resolved, each mapping's text is instantiated on
    the way to the printer: what is left to it is to write the pieces.  The
    checks of what a declaration moves and borrows read the instantiated
    pieces, a pair projection's included ({!Minicpp.foreign_pair_projection}).
    A type qualifying a member in value position is spelled as the value it
    names.  A pointer is written in the slot its pointee is held in.  Each
    match's computed scrutinee is declared, named, in front of it.  With
    every body final, what each lambda captures is written down; last, an
    initialiser holding a lambda that captures is invoked in place. *)
let instantiation_passes = [foreign; qualifiers; pointer_slots; scrutinees; captures; initialisers]

let pass_names =
  List.map stage_name minicpp_passes @ [seam] @ Pipeline_trace.names settled_passes
  @ Pipeline_trace.names instantiation_passes

(** {2 What the printer is not owed}

    A declaration leaves translation owing the printer decisions C++ cannot
    be handed undecided ({!Cpp_ir.Representation_obligation}).  Each is
    discharged by one pass above, and {!Cpp_erasure.settled} claims that by
    the end none is outstanding. *)
type obligation = Cpp_ir.Representation_obligation.t

let obligations = Cpp_ir.Representation_obligation.all

(** Whether [o] is checked before the instantiation passes rather than on
    the declaration the printer is handed.  A choice is recognised by the
    shape of its lambda's body, and {!scrutinees} reshapes that body --
    naming a match's computed scrutinee puts a declaration in front of the
    match -- so on the final declaration a second run of {!conditionals}
    finds nothing to do whether or not the first paid what it owed. *)
let checked_before_instantiation : obligation -> bool = function Unlowered_conditional -> true | _ -> false

let describe : obligation -> string = function
  | Unresolved_type -> "an undetermined type (Tunresolved), owed by the pass that wrote it"
  | Opaque_type -> "an unsettled representation (Topaque), owed by " ^ seam
  | Unspellable_binder -> "a custom match binder's unspellable type, owed by " ^ seam
  | Unsettled_callable -> "an unsettled callable constraint, owed by " ^ constraints.name
  | Unresolved_cast -> "an unresolved cast, owed by " ^ casts.name
  | Free_type_variable -> "an undeclared type variable, owed by " ^ free_tvars.name
  | Implicit_boxed_read -> "an implicit boxed read, owed by " ^ boxed_reads.name
  | Missing_template_argument -> "a mapping's unsupplied type argument, owed by " ^ template_args.name
  | Unlowered_method_call -> "a method called as a function, owed by " ^ method_calls.name
  | Unlowered_projection -> "a projection called as a function, owed by " ^ projections.name
  | Unlowered_conditional -> "a choice written as an invoked lambda, owed by " ^ conditionals.name
  | Move_under_access -> "a member read of a moved object, owed by " ^ access_moves.name
  | Undecided_constexpr -> "an undecided constexpr eligibility, owed by " ^ constexpr.name
  | Uninstantiated_mapping -> "an uninstantiated mapping, owed by " ^ foreign.name
  | Unlowered_qualifier -> "a type qualifier in value position, owed by " ^ qualifiers.name
  | Unslotted_pointer -> "a pointer's unchosen slot, owed by " ^ pointer_slots.name
  | Unnamed_scrutinee -> "a match's unnamed scrutinee, owed by " ^ scrutinees.name
  | Undecided_capture -> "an undecided lambda capture, owed by " ^ captures.name
  | Capture_outside_a_block -> "a capturing lambda in an initialiser, owed by " ^ initialisers.name

(** Whether [decl] writes down a type [p] holds of. *)
let mentions p (decl : cpp_decl) =
  let exception Found in
  (* {!rewrite_cpp_type} rather than {!map_cpp_type}: it reaches a carrier
     abstraction's body too. *)
  let ft t = rewrite_cpp_type (fun t -> if p t then raise_notrace Found else None) t in
  let rec fe e = map_expr fe fs ft e
  and fs s = map_stmt fe fs ft s in
  match ignore (map_decl fe fs ft decl) with () -> false | exception Found -> true

(** Whether [decl] still owes [o].  Every pass that discharges an obligation
    leaves nothing for a second run to do, so a declaration that has paid one
    is a fixed point of the pass that pays it -- a check that cannot drift
    from what the pass decides. *)
let owes (decl : Cpp_erasure.settled) (o : obligation) =
  let d = (decl :> cpp_decl) in
  let rewrites (p : Cpp_erasure.settled Pipeline_trace.pass) = compare (p.run decl) decl <> 0 in
  match o with
  | Unresolved_type -> mentions (function Tunresolved -> true | _ -> false) d
  | Opaque_type -> mentions (function Topaque -> true | _ -> false) d
  | Unspellable_binder -> Cpp_erasure.writes_unspellable_binder decl
  | Unsettled_callable -> compare (constraints.run d) d <> 0
  | Unresolved_cast -> rewrites casts
  | Free_type_variable -> rewrites free_tvars
  | Implicit_boxed_read -> rewrites boxed_reads
  | Missing_template_argument -> rewrites template_args
  | Unlowered_method_call -> rewrites method_calls
  | Unlowered_projection -> rewrites projections
  | Unlowered_conditional -> rewrites conditionals
  | Move_under_access -> rewrites access_moves
  | Undecided_constexpr -> rewrites constexpr
  | Uninstantiated_mapping -> rewrites foreign
  | Unlowered_qualifier -> rewrites qualifiers
  | Unslotted_pointer -> rewrites pointer_slots
  | Unnamed_scrutinee -> rewrites scrutinees
  | Undecided_capture -> rewrites captures
  | Capture_outside_a_block -> rewrites initialisers

(** [check_settled obligations decl] fails if [decl] still owes any of
    [obligations]: called with those {!checked_before_instantiation} once the
    settled passes have run, and with the rest on what the printer is handed,
    so that between them [decl] owes the printer nothing.

    The claim is about the {e whole} declaration and so cannot be carried by
    the type of its root, which is why it is checked here rather than enforced
    by construction.  The check runs only under [CRANE_CHECK_IR], set by the
    test suite: it re-runs the discharging passes over every declaration, and
    it protects an invariant the compiler is meant to establish rather than
    one a user's input can break.  The declaration is named as {!Table} names
    any global, since one a pass generated -- a lifted helper -- is not in the
    name table [Printer.pr_global] reads, and would fail the report itself. *)
let check_settled obligations (decl : Cpp_erasure.settled) =
  match List.filter (owes decl) obligations with
  | [] -> ()
  | owed ->
    CErrors.user_err
      Pp.(
        str "Crane: a declaration reached the printer owing "
        ++ prlist_with_sep (fun () -> str "; ") (fun o -> str (describe o)) owed
        ++
        match decl_globref (decl :> cpp_decl) with
        | Some r -> str " in " ++ Table.safe_pr_global r
        | None -> mt () )

(** A declaration on its way through the passes before the seam, in the
    representation the last pass left it in. *)
type staged =
  | In_ir of Cpp_ir.Lowered.Decl.t
  | In_minicpp of cpp_decl

let to_minicpp = function In_ir d -> Cpp_ir_to_legacy_minicpp.decl d | In_minicpp d -> d

(** [lower d] is [d] in CppIR.  Under [CRANE_CHECK_IR] it fails unless
    converting it back gives [d] again: a pass left on MiniCpp then reads
    exactly what it read before the declaration was lowered. *)
let lower d =
  let ir = Legacy_minicpp_to_cpp_ir.lower d in
  if Probe.checking () && compare (Cpp_ir_to_legacy_minicpp.decl ir) d <> 0 then
    CErrors.anomaly
      Pp.(
        str "Crane: a declaration does not convert back from CppIR to the MiniCpp it was lowered from"
        ++ match decl_globref d with Some r -> str " in " ++ Table.safe_pr_global r | None -> mt () );
  ir

let to_ir = function In_ir d -> d | In_minicpp d -> lower d

(** [run_stages ~tracing note stages decl] lowers [decl] and runs [stages]
    over it, converting only where a stage over the other representation
    follows, and hands back the MiniCpp the seam takes.  [note] is told what
    each stage did, in MiniCpp, which a stage over CppIR converts to only
    when [tracing]. *)
let run_stages ~tracing note stages decl =
  let step d = function
    | Ir p ->
      let before = to_ir d in
      let after = p.run before in
      if tracing then
        note p.name (Cpp_ir_to_legacy_minicpp.decl before) (Cpp_ir_to_legacy_minicpp.decl after);
      In_ir after
    | Legacy p ->
      let before = to_minicpp d in
      let after = p.run before in
      note p.name before after;
      In_minicpp after
  in
  to_minicpp (List.fold_left step (In_ir (lower decl)) stages)

let finish decl =
  let trace = traced decl in
  let steps = ref [] in
  let note name (before : cpp_decl) (after : cpp_decl) =
    if trace <> None then
      steps :=
        ( if compare before after = 0 then name ^ " unchanged"
          else
            Printf.sprintf "%s %d -> %d" name (node_count before)
              (node_count after) )
        :: !steps
  in
  let run : type a. (a -> cpp_decl) -> a Pipeline_trace.pass list -> a -> a =
   fun inj passes d ->
    List.fold_left
      (fun d (p : _ Pipeline_trace.pass) ->
        let d' = p.run d in
        note p.name (inj d) (inj d');
        d' )
      d passes
  in
  let decl = run_stages ~tracing:(trace <> None) note minicpp_passes decl in
  let settled = Cpp_erasure.materialise decl in
  note seam decl (settled :> cpp_decl);
  let inj (d : Cpp_erasure.settled) = (d :> cpp_decl) in
  let checking = Sys.getenv_opt "CRANE_CHECK_IR" <> None in
  let decl = run inj settled_passes settled in
  let early, late = List.partition checked_before_instantiation obligations in
  if checking then check_settled early decl;
  let decl = run inj instantiation_passes decl in
  if checking then begin
    Borrow_projection.check_decl (decl :> cpp_decl);
    Move_check.check_decl (decl :> cpp_decl);
    check_settled late decl
  end;
  Option.iter
    (fun name ->
      Feedback.msg_notice
        Pp.(
          str ("Crane: passes on " ^ name ^ ": ")
          ++ prlist_with_sep (fun () -> str ", ") str (List.rev !steps) ) )
    trace;
  decl
