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
  let use_at scheme ty =
    MLglob
      (Global_use.polymorphic (r "g")
         (Scheme.Instantiation.make scheme (fun _ ->
              {Scheme.solution = Scheme.Type ty; source = Scheme.Not_written} ) ) )
  in
  check "a use at its callee's scheme freezes"
    (not (refused [term "u" (use_at (Scheme.Id.fresh (r "g") ~arity:1) nat) nat]));
  check "a use instantiated at another declaration's scheme is refused"
    (refused [term "v" (use_at (Scheme.Id.fresh (r "h") ~arity:1) nat) nat]);
  check "a use holding a metavariable in its instantiation is refused"
    (refused [term "w" (use_at (Scheme.Id.fresh (r "g") ~arity:1) (Tmeta (Meta.fresh 3))) nat]);
  let shared = Tmeta (Meta.fresh 1) in
  let solved = Tmeta (Meta.solved 2 nat) in
  let open_term = term "k" (MLlam (Dummy, shared, MLrel 1)) (Tarr (shared, solved)) in
  check "each unsolved metavariable is counted once"
    (Core.unsolved_metas (frozen [open_term]) = 1);
  let two = Core.extracted [(mp "A", fine); (mp "B", [])] in
  let a, b = Core.partition (ModPath.equal (mp "A")) two in
  check "partition splits by top-level module"
    (List.map fst (Core.structure a) = [mp "A"] && List.map fst (Core.structure b) = [mp "B"]);
  check "modules keep each module with its own program"
    (List.map fst (Core.modules two) = [mp "A"; mp "B"])

(* After freezing, nothing solves a metavariable. *)
let () =
  let nat = Tglob (r "nat", [], []) in
  let m = Meta.fresh 7 and m' = Meta.fresh 8 in
  Meta.freeze ();
  check "a solve of the frozen program is refused"
    (match Meta.solve m nat with () -> false | exception e -> CErrors.is_anomaly e);
  check "a refused solve writes nothing" (m.contents = None);
  Meta.thaw ();
  Meta.solve m' nat;
  check "a thawed program solves freely" (m'.contents = Some nat)

(* A slot fills a hole without writing it: a hole met twice is filled once,
   and the fill is carried to the terms that mention the hole. *)
let () =
  let nat = Tglob (r "nat", [], []) and bool = Tglob (r "bool", [], []) in
  let pair a b = Tglob (r "pair", [a; b], []) in
  let m = Meta.fresh 15 in
  Meta.freeze ();
  let fills = ref [] in
  let refined =
    Ml_type_util.refine_erased ~fills ~writable:(fun _ -> true) (pair (Tmeta m) (Tmeta m))
      (pair nat bool)
  in
  check "a hole met twice is filled once" (refined = pair nat nat);
  check "the hole is not written" (m.contents = None);
  check "the fill is reported" (List.length !fills = 1);
  let body = MLlam (Dummy, Tmeta m, MLrel 1) in
  check "a term mentioning the hole is generated with it filled"
    (Ml_type_util.fill_holes !fills body = MLlam (Dummy, nat, MLrel 1));
  Meta.thaw ()

(* A local definition's open types are minted before freezing, rigid: each
   recursive group's from 1, a let-bound lambda's, its groups' included,
   past the variables of the declaration it is in. *)
let () =
  let nat = Tglob (r "nat", [], []) in
  let list t = Tglob (r "list", [t], []) in
  let go = Id.of_string "go" in
  let group m =
    MLfix (0, [|(go, Tarr (list (Tmeta m), nat))|], [|MLlam (Dummy, list (Tmeta m), MLrel 1)|], false)
  in
  let a = Meta.fresh 11 and b = Meta.fresh 12 and c = Meta.fresh 13 and d = Meta.fresh 14 in
  let body =
    MLletin
      ( Id go, nat, group a,
        MLletin
          ( Dummy, Tarr (Tmeta d, nat), MLlam (Dummy, Tmeta d, group c),
            MLapp (group b, [MLrel 1]) ) )
  in
  Local_types.structure [(mp "M", [term "f" body (Tarr (Tvar (Schematic, 1), nat))])];
  check "a let-bound group's open type is its first rigid variable" (a.contents = Some (Tvar (Rigid, 1)));
  check "each group numbers its own from 1" (b.contents = Some (Tvar (Rigid, 1)));
  check "a let-bound lambda's are numbered past the declaration's" (d.contents = Some (Tvar (Rigid, 2)));
  check "a group inside a let-bound lambda is the lambda's" (c.contents = Some (Tvar (Rigid, 3)))
