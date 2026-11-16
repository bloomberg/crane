(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Freezing extracted types and terms: each solved metavariable replaced by
    its solution, each unsolved one by an open annotation, the same one for
    every annotation that shared the cell.  A freezer remembers the open
    annotations it minted, so that what it freezes in several calls shares
    them as the cells did. *)

open Grammar

(* A metavariable is its cell: extraction numbers each declaration's afresh. *)
module Cells = Hashtbl.Make (struct
  type t = Phase.extracted Meta.t

  let equal = ( == )
  let hash (m : t) = Hashtbl.hash m.id
end)

(** The open annotations minted so far, by cell. *)
type t = Open.t Cells.t

(** A freezer that has minted nothing. *)
let create () : t = Cells.create 64

(** [type_ z t] is [t] frozen.  A node with nothing to freeze in it is kept
    as it is ({!Retype.type_leaf}). *)
let rec type_ (z : t) (t : Phase.extracted Type.at) : Phase.frozen Type.at =
  match t with
  | Type.Meta {contents = Some u; _} -> type_ z u
  | Type.Meta ({contents = None; _} as m) -> (
    match Cells.find_opt z m with
    | Some o -> Type.Open o
    | None ->
      let o = Open.fresh m.id in
      Cells.add z m o;
      Type.Open o )
  | Type.Arrow {parameter = a; result = b} -> Type.Arrow {parameter = type_ z a; result = type_ z b}
  | Type.Global_app {head = r; type_arguments = ts; index_arguments = args} ->
    Type.Global_app {head = r; type_arguments = List.map (type_ z) ts; index_arguments = List.map (expr z) args}
  | Type.Variable_app {head = i; arguments = ts} -> Type.Variable_app {head = i; arguments = List.map (type_ z) ts}
  | Type.Variable _ | Type.Hole _ | Type.Open _ | Type.Erased _ | Type.Unknown | Type.Axiom | Type.String ->
    Retype.type_leaf t

(** [expr z e] is [e] with every annotation frozen. *)
and expr z e = Retype.expr (type_ z) e
