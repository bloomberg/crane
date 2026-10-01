(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The one registry of mutable cells that must be emptied between runs.

    A cell enrols its reset where it is defined, with the scope it lives for,
    and is emptied by {!reset} for that scope.  There used to be three such
    registries ([Table.on_reset], [Cpp_state.owned_*] and
    [Common.register_cleanup]) plus resets written out by hand at the call
    sites, and a cell could sit in none of them. *)

type scope = Extraction | Unit

let actions : (scope * (unit -> unit)) list ref = ref []

let on_reset scope f = actions := (scope, f) :: !actions

let reset scope =
  List.iter (fun (s, f) -> if s = scope then f ()) (List.rev !actions)

let cell scope init =
  let r = ref init in
  on_reset scope (fun () -> r := init);
  r

let table scope n =
  let t = Hashtbl.create n in
  on_reset scope (fun () -> Hashtbl.reset t);
  t
