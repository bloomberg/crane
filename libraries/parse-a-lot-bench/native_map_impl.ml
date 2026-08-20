(* SPDX-License-Identifier: BSD-3-Clause *)
(* OCaml realization of Crane.Libraries.ParseALot.Utils.NativeMap (the axiomatized native map
   used by the lexer memo). The Crane C++ backend realizes NativeMap as
   immer::map; this is the parallel realization for the plain-OCaml extraction
   used as the benchmark baseline.

   Backed by the stdlib balanced AVL Map for an O(log n) persistent map, keyed by
   polymorphic structural comparison. Keys (Coq [Z] positions) have a canonical
   representation, so [Stdlib.compare] yields a consistent total order and correct
   equality. The [Obj.t] key erasure is safe here: each program run instantiates
   the map with a single, fixed key type. *)

module M = Map.Make (struct
  type t = Obj.t
  let compare = Stdlib.compare
end)

type ('k, 'v) t = 'v M.t

let empty : ('k, 'v) t = M.empty

let get (m : ('k, 'v) t) (k : 'k) : 'v option = M.find_opt (Obj.repr k) m

let set (m : ('k, 'v) t) (k : 'k) (v : 'v) : ('k, 'v) t = M.add (Obj.repr k) v m
