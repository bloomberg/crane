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

(** The name a type has here when it has no C++ spelling, and [None] for every
    type that has one.

    {!Minicpp.Tunresolved} is the back end's bottom, and {!Minicpp.Topaque} is
    an admission of ignorance that {!Cpp_erasure.materialise} is supposed to
    have settled.  Neither has an honest spelling, and neither announces
    itself: [Topaque] prints as [std::any] and so quietly says the wrong
    thing, and [Tunresolved] aborts extraction with a message about Crane
    rather than about the user's code. *)
let unspellable = function
  | Tunresolved -> Some "Tunresolved"
  | Topaque -> Some "Topaque"
  | _ -> None

(** [check_settled decl] fails if [decl] still writes down a type that has no
    C++ spelling, which the {!Cpp_erasure.settled} type claims it does not.

    That claim is about the {e whole} declaration and so cannot be carried by
    the type of its root, which is why it is checked here rather than enforced
    by construction.  The check runs only under [CRANE_CHECK_IR], set by the
    test suite: it is a second traversal of every declaration, and it protects
    an invariant the compiler is meant to establish rather than one a user's
    input can break. *)
let check_settled (decl : Cpp_erasure.settled) =
  let found = ref [] in
  let note t =
    ( match unspellable t with
    | Some name when not (List.mem name !found) -> found := name :: !found
    | _ -> () );
    t
  in
  let ft t = map_cpp_type note t in
  let rec fe e = map_expr fe fs ft e
  and fs s = map_stmt fe fs ft s in
  ignore (map_decl fe fs ft (decl :> cpp_decl));
  if !found <> [] then
    CErrors.user_err
      Pp.(
        str "Crane: unspellable type reaching the printer ("
        ++ prlist_with_sep (fun () -> str ", ") str (List.rev !found)
        ++ str ")"
        ++
        match decl_globref (decl :> cpp_decl) with
        | Some r -> str " in " ++ Printer.pr_global r
        | None -> mt () )

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

(** Every pass before the {!Cpp_erasure} seam, in the order they run. *)
let minicpp_passes : cpp_decl Pipeline_trace.pass list =
  let open Pipeline_trace in
  [ pass "loopify" (fun d ->
        if should_loopify d then Loopify.transform_decl d
        else Loopify.transform_local_tail_loops d );
    (* Closures made and used in one place become the code they stand for,
       before ownership is decided, so what they captured is seen as local. *)
    pass "local_closures" Cpp_local_closures.transform_decl;
    (* A function's constants are declared once at its top, now that nothing
       moves code between functions -- and before the passes that rewrite what
       an initialiser holds: [depth] splits a deep one into bindings, which in
       a static's initialiser run once. *)
    pass "constants" Cpp_constants.decl;
    (* The temporaries Normalize named for loopification and loopification did
       not need go back where they are read. *)
    pass "temporaries" Cpp_temporaries.decl;
    (* An argument a mapping would splice, and so evaluate, more than once is
       named once -- after the temporaries went back, so that none of them is
       put back into the text that repeats it. *)
    pass "shared_args" Cpp_shared_args.transform_decl;
    (* Small local simplifications, before ownership reads the uses. *)
    pass "simplify" Cpp_simplify.transform_decl;
    (* An initialiser nested deeper than a compiler will parse becomes a run of
       bindings; everything shallower is left as it stands. *)
    pass "depth" Cpp_depth.flatten;
    (* With the frames and temporaries in their final places, a local's last
       read is visible, and becomes a move. *)
    pass "last_use" (fun d ->
        if Table.move_last_use () then Last_use.transform_decl d else d );
    (* A returned value is moved by the language; writing the move there
       only suppresses copy elision. *)
    pass "return_moves" Last_use.drop_return_moves;
    (* Which callable parameters keep a constraint is decided here, with the
       body that decides it in hand; the printer writes what it is given. *)
    pass "constraints" Minicpp.settle_constraints ]

(** Writing a type down is what decides its representation, so the [Topaque]
    slots are settled before anything reads the declaration as final.
    Crossing this seam is what gives {!Cpp_erasure.settled}, the printer's
    input type. *)
let seam = "materialise"

(** Every pass after the seam, in the order they run. *)
let settled_passes : Cpp_erasure.settled Pipeline_trace.pass list =
  let open Pipeline_trace in
  [ pass "casts" Cpp_erasure.resolve_casts;
    (* With the heads final, a body naming a type variable no head declares
       is a name nothing in scope introduces; spell it [std::any] rather than
       emit it. *)
    pass "free_tvars" Cpp_erasure.bind_free_tvars;
    (* With every type final, a read of a boxed value the context needs at a
       concrete type is written down. *)
    pass "boxed_reads" Cpp_erasure.lower_boxed_reads;
    (* A call of a methodified function becomes the member call it is, so
       the printer spells the call it is given. *)
    pass "method_calls" Cpp_erasure.lower_method_calls;
    (* So does a projection, applied or named as a value. *)
    pass "projections" Cpp_erasure.lower_projections;
    (* A lambda invoked only to choose between two values is the choice. *)
    pass "conditionals" Cpp_erasure.lower_conditionals ]

let pass_names =
  Pipeline_trace.names minicpp_passes @ [seam] @ Pipeline_trace.names settled_passes

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
  let decl = run Fun.id minicpp_passes decl in
  let settled = Cpp_erasure.materialise decl in
  note seam decl (settled :> cpp_decl);
  let decl =
    run (fun (d : Cpp_erasure.settled) -> (d :> cpp_decl)) settled_passes settled
  in
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    check_settled decl;
    Borrow_projection.check_decl (decl :> cpp_decl)
  end;
  Option.iter
    (fun name ->
      Feedback.msg_notice
        Pp.(
          str ("Crane: passes on " ^ name ^ ": ")
          ++ prlist_with_sep (fun () -> str ", ") str (List.rev !steps) ) )
    trace;
  decl
