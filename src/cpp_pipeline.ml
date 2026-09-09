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

let finish ~pp_expr ~loopify decl =
  let decl = if loopify then Loopify.transform_decl ~pp_expr decl else decl in
  (* An initialiser nested deeper than a compiler will parse becomes a run of
     bindings; everything shallower is left as it stands. *)
  let decl = Cpp_depth.flatten decl in
  (* Writing a type down is what decides its representation, so settle the
     [Topaque] slots before anything reads the declaration as final.  Crossing
     this seam is what gives {!Cpp_erasure.settled}, the printer's input
     type. *)
  Cpp_erasure.resolve_casts (Cpp_erasure.materialise decl)
