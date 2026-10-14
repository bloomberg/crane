(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* The phase-indexed Core facade and what freezing checks. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "core: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let mp s = ModPath.MPfile (DirPath.make [Id.of_string s])
let term name body ty = (Label.make name, SEdecl (Dterm (r name, body, ty)))
let frozen sel = Core.freeze (Core.optimize Fun.id (Core.extracted [(mp "M", sel)]))

let refused sel =
  match frozen sel with
  | _ -> false
  | exception e -> CErrors.is_anomaly e

let () =
  Unix.putenv "CRANE_CHECK_IR" "1";
  let nat = Tglob (r "nat", [], []) in
  let lam = MLlam (Dummy, nat, MLrel 1) in
  let fine = [term "f" lam (Tarr (nat, nat))] in
  check "a well-formed program freezes" (not (refused fine));
  check "an empty recursive group is refused"
    (refused [(Label.make "g", SEdecl (Dfix []))]);
  check "a local group selecting a missing member is refused"
    (refused [term "h" (MLfix (2, [|(Id.of_string "go", nat)|], [|lam|], false)) nat]);
  check "a declaration made twice is refused" (refused (fine @ fine));
  let shared = Tmeta {id = 1; contents = None} in
  let solved = Tmeta {id = 2; contents = Some nat} in
  let open_term = term "k" (MLlam (Dummy, shared, MLrel 1)) (Tarr (shared, solved)) in
  check "each unsolved metavariable is counted once"
    (Core.unsolved_metas (frozen [open_term]) = 1);
  let two = Core.extracted [(mp "A", fine); (mp "B", [])] in
  let a, b = Core.partition (ModPath.equal (mp "A")) two in
  check "partition splits by top-level module"
    (List.map fst (Core.structure a) = [mp "A"] && List.map fst (Core.structure b) = [mp "B"]);
  check "modules keep each module with its own program"
    (List.map fst (Core.modules two) = [mp "A"; mp "B"])
