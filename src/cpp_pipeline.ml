(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** The passes a MiniCpp declaration goes through between translation and the
    printer.  See [cpp_pipeline.mli]. *)

open Minicpp
open Names

(** Whether [decl] is loopified, given what the user asked for. *)
let should_loopify decl =
  match decl_globref decl with
  (* The methods generated on an inductive are structural recursion over that
     inductive, one C++ frame per cell, and the user has no name to hang
     [Crane Loopify] on.  Loopify them by default.

     A coinductive is exempt: its recursion sits under a lazy thunk, so it
     never builds a deep C++ stack in the first place. *)
  | Some (GlobRef.IndRef _ as r) ->
    Table.should_loopify ~default:(not (Table.is_coinductive r)) r
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
          (List.map (fun r -> Pp.string_of_ppcmds (Printer.pr_global r)) rs)
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
  let pass name f d =
    let d' = f d in
    note name d d';
    d'
  in
  let settled_pass name (f : Cpp_erasure.settled -> Cpp_erasure.settled) d =
    let d' = f d in
    note name (d :> cpp_decl) (d' :> cpp_decl);
    d'
  in
  let decl =
    pass "loopify"
      (fun d -> if should_loopify d then Loopify.transform_decl d else d)
      decl
  in
  (* An initialiser nested deeper than a compiler will parse becomes a run of
     bindings; everything shallower is left as it stands. *)
  let decl = pass "depth" Cpp_depth.flatten decl in
  (* With the frames and temporaries in their final places, a local's last
     read is visible, and becomes a move. *)
  let decl =
    pass "last_use"
      (fun d -> if Table.move_last_use () then Last_use.transform_decl d else d)
      decl
  in
  (* A coinductive's field projection hands out a reference into an lvalue
     receiver, and a copy only to a temporary one. *)
  let decl = pass "borrow_projection" Borrow_projection.transform_decl decl in
  (* Which callable parameters keep a constraint is decided here, with the
     body that decides it in hand; the printer writes what it is given. *)
  let decl = pass "constraints" Minicpp.settle_constraints decl in
  (* Writing a type down is what decides its representation, so settle the
     [Topaque] slots before anything reads the declaration as final.  Crossing
     this seam is what gives {!Cpp_erasure.settled}, the printer's input
     type. *)
  let settled = Cpp_erasure.materialise decl in
  note "materialise" decl (settled :> cpp_decl);
  let decl = settled_pass "casts" Cpp_erasure.resolve_casts settled in
  (* With the heads final, a body naming a type variable no head declares is
     a name nothing in scope introduces; spell it [std::any] rather than emit
     it. *)
  let decl = settled_pass "free_tvars" Cpp_erasure.bind_free_tvars decl in
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then check_settled decl;
  Option.iter
    (fun name ->
      Feedback.msg_notice
        Pp.(
          str ("Crane: passes on " ^ name ^ ": ")
          ++ prlist_with_sep (fun () -> str ", ") str (List.rev !steps) ) )
    trace;
  decl

let finish_group decls =
  List.iter Loopify.register_decl decls;
  List.map finish decls
