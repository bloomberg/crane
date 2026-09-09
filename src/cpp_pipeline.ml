(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** The passes a MiniCpp declaration goes through between translation and the
    printer.  See [cpp_pipeline.mli]. *)

open Minicpp
open Names

(** The primary [GlobRef.t] a declaration is about, if it has one.  This is
    what a [Crane Loopify] directive names. *)
let rec decl_globref = function
  | Dtemplate (_, _, inner) -> decl_globref inner
  | Dfundef ((r, _) :: _, _, _, _, _) -> Some r
  | Dstruct ds -> Some ds.ds_ref
  | Dnspace (Some r, _) -> Some r
  | _ -> None

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

let finish ~loopify decl =
  let decl = if loopify then Loopify.transform_decl decl else decl in
  (* An initialiser nested deeper than a compiler will parse becomes a run of
     bindings; everything shallower is left as it stands. *)
  let decl = Cpp_depth.flatten decl in
  (* Writing a type down is what decides its representation, so settle the
     [Topaque] slots before anything reads the declaration as final.  Crossing
     this seam is what gives {!Cpp_erasure.settled}, the printer's input
     type. *)
  let decl = Cpp_erasure.resolve_casts (Cpp_erasure.materialise decl) in
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then check_settled decl;
  decl
