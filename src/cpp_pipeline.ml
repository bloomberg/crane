(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** The passes a MiniCpp declaration goes through between translation and the
    printer.  See [cpp_pipeline.mli]. *)

open Minicpp
open Names

(** Whether [decl] is loopified, given what the user asked for. *)
let should_loopify decl =
  match decl_globref decl with
  | Some (GlobRef.IndRef _ as r) -> Table.loopifies_methods_of r
  | Some r -> Table.should_loopify r
  | None -> Table.loopify ()

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
      | Dfields {ds_ref = r; _} | Denum {de_ref = r; _} | Dasgn (r, _, _) -> [r]
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

(** A declaration on its way to the seam, and whether a pass lowering control
    has rewritten it: the plan of its moves was made over Core, before the
    loops, frames and sequenced bindings those passes make, and does not
    see the last uses they create. *)
type unsettled = {decl : cpp_decl; control_lowered : bool}

(** A pass over the declaration alone. *)
let on_decl name f = Pipeline_trace.pass name (fun u -> {u with decl = f u.decl})

(** A pass lowering control, noting whether it rewrote anything. *)
let lowering name f =
  Pipeline_trace.pass name (fun u ->
      let d = f u.decl in
      {decl = d; control_lowered = u.control_lowered || not (d == u.decl || compare d u.decl = 0)} )

(** The passes below that discharge an {!obligation}, named once so that
    the list of obligations refers to the pass rather than to its name. *)
let constraints = on_decl "constraints" Minicpp.settle_constraints

let casts = Pipeline_trace.pass "casts" Cpp_erasure.resolve_casts
let free_tvars = Pipeline_trace.pass "free_tvars" Cpp_erasure.bind_free_tvars
let method_calls = Pipeline_trace.pass "method_calls" Cpp_erasure.lower_method_calls
let projections = Pipeline_trace.pass "projections" Cpp_erasure.lower_projections

(** Every pass before the {!Cpp_erasure} seam, in the order they run. *)
let minicpp_passes : unsettled Pipeline_trace.pass list =
  [ lowering "loopify" (fun d ->
        if should_loopify d then Loopify.transform_decl d
        else Loopify.transform_local_tail_loops d );
    (* Closures made and used in one place become the code they stand for,
       before ownership is decided, so what they captured is seen as local. *)
    lowering "local_closures" Cpp_local_closures.transform_decl;
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
    (* Where control was lowered after the plan, with the frames and
       temporaries in their final places, a local's last read is visible, and
       becomes a move.  Elsewhere the plan moved every read it could. *)
    Pipeline_trace.pass "last_use" (fun u ->
        if u.control_lowered && Table.move_last_use () then {u with decl = Last_use.transform_decl u.decl}
        else u );
    (* A returned value is moved by the language; writing the move there
       only suppresses copy elision. *)
    on_decl "return_moves" Last_use.drop_return_moves;
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
  let open Pipeline_trace in
  [ casts;
    (* With the heads final, a body naming a type variable no head declares
       is a name nothing in scope introduces; spell it [std::any] rather than
       emit it. *)
    free_tvars;
    (* With every type final, a read of a boxed value the context needs at a
       concrete type is written down. *)
    pass "boxed_reads" Cpp_erasure.lower_boxed_reads;
    (* A call of a methodified function becomes the member call it is, so
       the printer spells the call it is given. *)
    method_calls;
    (* So does a projection, applied or named as a value. *)
    projections;
    (* A lambda invoked only to choose between two values is the choice. *)
    pass "conditionals" Cpp_erasure.lower_conditionals ]

let pass_names =
  Pipeline_trace.names minicpp_passes @ [seam] @ Pipeline_trace.names settled_passes

(** {2 What the printer is not owed}

    A declaration leaves translation owing the printer decisions C++ cannot be
    handed undecided: a type with no spelling, a callable parameter whose
    constraint the body has not settled, a cast whose caster is not chosen, a
    type variable nothing declares, a call of a method or a projection written
    as a call of a function.  Each is discharged by one pass above, and
    {!Cpp_erasure.settled} claims that by the end none is outstanding.  The
    list is closed: a new kind of debt the printer must not see is a new
    constructor here, with the pass that pays it. *)
type obligation =
  | Unresolved_type
      (** {!Minicpp.Tunresolved}: no pass determined the type, so no pass
          below can discharge it; whatever wrote it owes it. *)
  | Opaque_type  (** {!Minicpp.Topaque}, settled by the seam. *)
  | Unsettled_callable  (** a {!Minicpp.TTfun} parameter *)
  | Unresolved_cast  (** an [any_cast] whose caster is still to choose *)
  | Free_type_variable  (** a type variable no enclosing head declares *)
  | Unlowered_method_call
  | Unlowered_projection

let obligations =
  [ Unresolved_type; Opaque_type; Unsettled_callable; Unresolved_cast; Free_type_variable;
    Unlowered_method_call; Unlowered_projection ]

let describe = function
  | Unresolved_type -> "an undetermined type (Tunresolved), owed by the pass that wrote it"
  | Opaque_type -> "an unsettled representation (Topaque), owed by " ^ seam
  | Unsettled_callable -> "an unsettled callable constraint, owed by " ^ constraints.name
  | Unresolved_cast -> "an unresolved cast, owed by " ^ casts.name
  | Free_type_variable -> "an undeclared type variable, owed by " ^ free_tvars.name
  | Unlowered_method_call -> "a method called as a function, owed by " ^ method_calls.name
  | Unlowered_projection -> "a projection called as a function, owed by " ^ projections.name

(** Whether [decl] writes down a type [p] holds of. *)
let mentions p (decl : cpp_decl) =
  let exception Found in
  let ft t = map_cpp_type (fun t -> if p t then raise_notrace Found else t) t in
  let rec fe e = map_expr fe fs ft e
  and fs s = map_stmt fe fs ft s in
  match ignore (map_decl fe fs ft decl) with () -> false | exception Found -> true

(** Whether [decl] still owes [o].  Every pass that discharges an obligation
    leaves nothing for a second run to do, so a declaration that has paid one
    is a fixed point of the pass that pays it -- a check that cannot drift
    from what the pass decides. *)
let owes (decl : Cpp_erasure.settled) o =
  let d = (decl :> cpp_decl) in
  let rewrites (p : Cpp_erasure.settled Pipeline_trace.pass) = compare (p.run decl) decl <> 0 in
  match o with
  | Unresolved_type -> mentions (function Tunresolved -> true | _ -> false) d
  | Opaque_type -> mentions (function Topaque -> true | _ -> false) d
  | Unsettled_callable -> compare (constraints.run {decl = d; control_lowered = false}).decl d <> 0
  | Unresolved_cast -> rewrites casts
  | Free_type_variable -> rewrites free_tvars
  | Unlowered_method_call -> rewrites method_calls
  | Unlowered_projection -> rewrites projections

(** [check_settled decl] fails if [decl] still owes the printer anything.

    The claim is about the {e whole} declaration and so cannot be carried by
    the type of its root, which is why it is checked here rather than enforced
    by construction.  The check runs only under [CRANE_CHECK_IR], set by the
    test suite: it re-runs the discharging passes over every declaration, and
    it protects an invariant the compiler is meant to establish rather than
    one a user's input can break.  The declaration is named as {!Table} names
    any global, since one a pass generated -- a lifted helper -- is not in the
    name table [Printer.pr_global] reads, and would fail the report itself. *)
let check_settled (decl : Cpp_erasure.settled) =
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
  let {decl; _} = run (fun u -> u.decl) minicpp_passes {decl; control_lowered = false} in
  let settled = Cpp_erasure.materialise decl in
  note seam decl (settled :> cpp_decl);
  let decl =
    run (fun (d : Cpp_erasure.settled) -> (d :> cpp_decl)) settled_passes settled
  in
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    check_settled decl;
    Borrow_projection.check_decl (decl :> cpp_decl);
    Move_check.check_decl (decl :> cpp_decl)
  end;
  Option.iter
    (fun name ->
      Feedback.msg_notice
        Pp.(
          str ("Crane: passes on " ^ name ^ ": ")
          ++ prlist_with_sep (fun () -> str ", ") str (List.rev !steps) ) )
    trace;
  decl
