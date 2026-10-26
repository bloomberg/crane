(* Which constructions take the storage a rebuilding branch frees: those of
   the rebuilt constructor the branch returns, one per path, and none it
   passes to a call or builds inside a closure. *)

open Names
open Crane_plugin
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "reuse_plan: %s\n" name;
    exit 1 )

let ind = (MutInd.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string "T"])) (Label.make "lst")), 0)
let nil = GlobRef.ConstructRef (ind, 1)
let cons = GlobRef.ConstructRef (ind, 2)
let other = GlobRef.ConstructRef ((fst ind, 1), 1)
let nat = Tglob (GlobRef.VarRef (Id.of_string "nat"), [], [])
let lst = Tglob (GlobRef.IndRef ind, [], [])
let call f args = MLapp (MLglob (Global_use.monomorphic (GlobRef.VarRef (Id.of_string f))), args)
let x = Id (Id.of_string "x")
let t = Id (Id.of_string "t")
let reused p e = Ownership_plan.allocation p e = Ownership_plan.Allocation.Reuse

(* [fun l => match l with nil => nil | cons x t => body], [body] under
   [l], [x] and [t]; and the plan of its cons branch rebuilding a cons. *)
let arm body =
  let scrutinee = fresh_rel 1 in
  let root =
    MLlam
      ( Id (Id.of_string "l"),
        lst,
        MLcase
          ( lst,
            scrutinee,
            [| ([], lst, Pusual nil, MLcons (lst, nil, []));
               ([(x, nat); (t, lst)], lst, Pusual cons, body) |] ) )
  in
  let p = Ownership_plan.region ~owned:[1] ~n_outer:0 root in
  (p, Ownership_plan.reuse_arm p ~scrutinee ~branch:1 ~constructor:cons)

let () =
  let inner = MLcons (lst, cons, [fresh_rel 1; fresh_rel 2]) in
  let closure = MLlam (Id (Id.of_string "y"), nat, call "suml" [inner]) in
  let tail = MLcons (lst, cons, [call "twice" [closure; fresh_rel 2]; call "g" [fresh_rel 1]]) in
  let region, p = arm tail in
  check "the construction returned takes the storage" (reused p tail);
  check "a construction inside a closure does not" (not (reused p inner));
  check "nothing is reused outside the rebuilding branch" (not (reused region tail));
  let temporary = MLcons (lst, cons, [fresh_rel 2; MLcons (lst, nil, [])]) in
  let tail = MLcons (lst, cons, [call "suml" [temporary]; fresh_rel 1]) in
  let _, p = arm tail in
  check "a construction passed to a call does not" (not (reused p temporary));
  check "the one returned around it does" (reused p tail);
  let left = MLcons (lst, cons, [fresh_rel 3; fresh_rel 2]) in
  let right = MLcons (lst, cons, [fresh_rel 3; MLcons (lst, nil, [])]) in
  let ended = MLcons (lst, nil, []) in
  let bool = Tglob (GlobRef.VarRef (Id.of_string "bool"), [], []) in
  let tail =
    MLletin
      ( Id (Id.of_string "b"),
        bool,
        call "test" [fresh_rel 2],
        MLcase
          ( bool,
            fresh_rel 1,
            [| ([], lst, Pusual other, left); ([], lst, Pusual other, right); ([], lst, Pwild, ended) |] ),
        Occurrence.fresh () )
  in
  let _, p = arm tail in
  check "each branch of a match the arm ends in returns its own"
    (reused p left && reused p right);
  check "a construction of another constructor does not" (not (reused p ended))

(* [let r := weigh s in g s r], [s] an owned parameter: the call's argument
   is [s]'s last use only where a machine resumes at the let with a frame
   keeping [s], saved before the call's arguments are evaluated. *)
let () =
  let origin = GlobRef.VarRef (Id.of_string "weigh") in
  let arg = fresh_rel 1 in
  let value = call "weigh" [arg] in
  let site = Occurrence.fresh () in
  let root = MLletin (Id (Id.of_string "r"), nat, value, call "g" [fresh_rel 2; fresh_rel 1], site) in
  let read = match arg with MLrel (_, o) -> o | _ -> assert false in
  let call_site = match value with MLapp (MLglob g, _) -> g.occurrence | _ -> assert false in
  let s = Core_binder.make ~origin ~level:0 () in
  let resumes calls : Ownership_plan.resumes =
    { origin;
      depth = 1;
      resume_at =
        (fun b ->
          if Core_binder.equal b (Core_binder.make ~origin ~level:1 ()) && Core_binder.same_site b (Core_binder.make ~origin ~level:1 ~site ())
          then Some {calls; kept = [s]}
          else None ) }
  in
  let use resumes = Ownership_plan.use (Ownership_plan.region ~owned:[1] ?resumes ~n_outer:0 root) read in
  check "an argument read again after the call is copied" (use None = Some Ownership_plan.Use.Copy);
  check "one a frame keeps across the call is moved" (use (Some (resumes [call_site])) = Some Ownership_plan.Use.Move);
  check "not where the let resumes after another call" (use (Some (resumes [Occurrence.fresh ()])) = Some Ownership_plan.Use.Copy)
