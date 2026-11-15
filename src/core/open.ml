(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* An open annotation is told apart from another by its cell, as the
   metavariable it replaces was; its number, the metavariable's, is all
   structural equality and hashing see of it. *)
type t = { id : int; cell : Occurrence.t }

let fresh id = { id; cell = Occurrence.fresh () }
let id o = o.id
let equal a b = Occurrence.equal a.cell b.cell
let hash o = Hashtbl.hash o.id
