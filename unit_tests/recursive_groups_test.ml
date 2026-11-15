(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* The recursive groups of a program: the cycles of its call graph. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "recursive_groups: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let mp = ModPath.MPfile (DirPath.make [Id.of_string "M"])
let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}
let call f = Core.Expr.Apply {callee = Core.Expr.Global (Core.Global_use.monomorphic (r f));
                              arguments = [Core.Expr.fresh_rel 1]}
let calling fs = Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous;
                                   parameter_type = nat;
                                   body = List.fold_left
                                     (fun b f ->
                                       Core.Expr.Let
                                         {binder = Core.Binder_name.Anonymous; binder_type = nat; value = call f;
                                           body = b; occurrence = Core.Occurrence.fresh ()}) (Core.Expr.fresh_rel 1) fs}
let fd name fs = {Core.Recursion.Definition.entity = r name;
                  body = calling fs;
                  type_ = Core.Type.Arrow {parameter = nat; result = nat}}
let term name fs =
  (Label.make name,
    Core.Module.Structure_item.Declaration
      (Core.Decl.Value {entity = r name; body = calling fs; type_ = Core.Type.Arrow {parameter = nat; result = nat}}))
let fix fds =
  (Label.make "fix", Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group (Core.Nonempty.of_list_exn fds)))
let names = Option.map (List.map (function GlobRef.VarRef id -> Id.to_string id | _ -> "?"))

let program =
  [ ( mp,
      [ term "leaf" [];
        term "self" ["self"; "leaf"];
        fix [fd "even" ["odd"]; fd "odd" ["even"; "leaf"]];
        (* A cycle through three functions, declared apart. *)
        term "c" ["a"];
        term "a" ["b"];
        term "b" ["c"];
        term "caller" ["even"; "self"] ] ) ]

let () =
  let groups = Recursive_groups.analyze program in
  check "a function calling nothing is on no cycle" (Recursive_groups.group groups (r "leaf") = None);
  check "a caller of a cycle is not on it" (Recursive_groups.group groups (r "caller") = None);
  check "a function calling itself is a group of one"
    (names (Recursive_groups.group groups (r "self")) = Some ["self"]);
  check "a mutual pair is one group, in definition order"
    (names (Recursive_groups.group groups (r "odd")) = Some ["even"; "odd"]);
  check "a longer cycle is one group, in definition order"
    (names (Recursive_groups.group groups (r "a")) = Some ["c"; "a"; "b"]);
  check "a member is in its own group" (Recursive_groups.in_group groups (r "b") (r "b"));
  check "partners are in each other's groups"
    (Recursive_groups.in_group groups (r "even") (r "odd")
    && Recursive_groups.in_group groups (r "odd") (r "even"));
  check "a callee off the cycle is not in the group"
    (not (Recursive_groups.in_group groups (r "odd") (r "leaf")));
  check "a function on no cycle has no group, not even itself"
    (not (Recursive_groups.in_group groups (r "leaf") (r "leaf")));
  check "analysis is deterministic"
    (Recursive_groups.equal groups (Recursive_groups.analyze program))
