(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* The recursive groups of a program: the cycles of its call graph. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "recursive_groups: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let mp = ModPath.MPfile (DirPath.make [Id.of_string "M"])
let nat = Tglob (r "nat", [], [])
let call f = MLapp (MLglob (Global_use.monomorphic (r f)), [MLrel 1])
let calling fs = MLlam (Dummy, nat, List.fold_left (fun b f -> MLletin (Dummy, nat, call f, b)) (MLrel 1) fs)
let fd name fs = {fd_ref = r name; fd_body = calling fs; fd_type = Tarr (nat, nat)}
let term name fs = (Label.make name, SEdecl (Dterm (r name, calling fs, Tarr (nat, nat))))
let fix fds = (Label.make "fix", SEdecl (Dfix fds))
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
