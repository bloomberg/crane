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
let copied (u : Ownership_plan.Use.t option) = match u with Some (Share | Clone | Copy) -> true | Some (Move | Borrow) | None -> false

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
      entry_captures = None;
      parameter_type = (fun _ -> None);
      resume_at =
        (fun b ->
          if Core_binder.equal b (Core_binder.make ~origin ~level:1 ()) && Core_binder.same_site b (Core_binder.make ~origin ~level:1 ~site ())
          then Some {calls; kept = [s]; held = [s]; passed = []}
          else None ) }
  in
  let use resumes = Ownership_plan.use (Ownership_plan.region ~owned:[1] ?resumes ~n_outer:0 root) read in
  check "an argument read again after the call is copied" (copied (use None));
  check "one a frame keeps across the call is moved" (use (Some (resumes [call_site])) = Some Ownership_plan.Use.Move);
  check "not where the let resumes after another call" (copied (use (Some (resumes [Occurrence.fresh ()]))))

(* [let y := h s in let r := weigh y in g s r], a frame keeping [s] across
   [weigh]: saving the frame reads [s] after [h] does, so [h] copies it. *)
let () =
  let origin = GlobRef.VarRef (Id.of_string "weigh") in
  let arg = fresh_rel 1 in
  let value = call "weigh" [fresh_rel 1] in
  let site = Occurrence.fresh () in
  let resumed = MLletin (Id (Id.of_string "r"), nat, value, call "g" [fresh_rel 3; fresh_rel 1], site) in
  let root = MLletin (Id (Id.of_string "y"), nat, call "h" [arg], resumed, Occurrence.fresh ()) in
  let read = match arg with MLrel (_, o) -> o | _ -> assert false in
  let call_site = match value with MLapp (MLglob g, _) -> g.occurrence | _ -> assert false in
  let at_let = Core_binder.make ~origin ~level:2 ~site () in
  let resumes : Ownership_plan.resumes =
    { origin;
      depth = 1;
      entry_captures = None;
      parameter_type = (fun _ -> None);
      resume_at =
        (fun b ->
          if Core_binder.equal b at_let && Core_binder.same_site b at_let
          then
            let s = Core_binder.make ~origin ~level:0 () in
            Some {calls = [call_site]; kept = [s]; held = [s]; passed = []}
          else None ) }
  in
  let use = Ownership_plan.use (Ownership_plan.region ~owned:[1] ~resumes ~n_outer:0 root) read in
  check "a read before the frame keeping it is saved is copied" (copied use)

(* [let r := weigh a in g s r] under [t] and [s], a frame keeping [s]
   across [weigh]: the save may move [s] where the region owns it and the
   call's argument [a] does not read it. *)
let () =
  let origin = GlobRef.VarRef (Id.of_string "weigh") in
  let s = Core_binder.make ~origin ~level:1 () in
  let moves ~owned arg =
    let value = call "weigh" [arg] in
    let site = Occurrence.fresh () in
    let root = MLletin (Id (Id.of_string "r"), nat, value, call "g" [fresh_rel 2; fresh_rel 1], site) in
    let call_site = match value with MLapp (MLglob g, _) -> g.occurrence | _ -> assert false in
    let at_let = Core_binder.make ~origin ~level:2 ~site () in
    let resumes : Ownership_plan.resumes =
      { origin;
        depth = 2;
        entry_captures = None;
        parameter_type = (fun _ -> None);
        resume_at =
          (fun b ->
            if Core_binder.equal b at_let && Core_binder.same_site b at_let then
              Some {calls = [call_site]; kept = [s]; held = [s]; passed = []}
            else None ) }
    in
    Ownership_plan.save_moves (Ownership_plan.region ~owned ~resumes ~n_outer:0 root) site
  in
  let moved = function Some [b] -> Core_binder.equal b s | _ -> false in
  check "a save moves what the region owns and the call does not read" (moved (moves ~owned:[1] (fresh_rel 2)));
  check "not what the call reads after it" (moves ~owned:[1] (fresh_rel 1) = Some []);
  check "nor what the region does not own" (moves ~owned:[] (fresh_rel 2) = Some []);
  check "a let no machine resumes at saves nothing"
    (Ownership_plan.save_moves (Ownership_plan.region ~owned:[1] ~n_outer:0 (fresh_rel 1)) (Occurrence.fresh ()) = None)

(* [let y := weigh t in let r := weigh t in g s y r] under [t] and [s], [s]
   lent: the first frame holds [s], so the handler resuming there owns it,
   and the second save may move it; the first may not. *)
let () =
  let origin = GlobRef.VarRef (Id.of_string "weigh") in
  let s = Core_binder.make ~origin ~level:1 () in
  let outer_value = call "weigh" [fresh_rel 2] and inner_value = call "weigh" [fresh_rel 3] in
  let outer_site = Occurrence.fresh () and inner_site = Occurrence.fresh () in
  let inner = MLletin (Id (Id.of_string "r"), nat, inner_value, call "g" [fresh_rel 3; fresh_rel 2; fresh_rel 1], inner_site) in
  let root = MLletin (Id (Id.of_string "y"), nat, outer_value, inner, outer_site) in
  let call_of = function MLapp (MLglob g, _) -> g.occurrence | _ -> assert false in
  let point level site value =
    (Core_binder.make ~origin ~level ~site (), {Ownership_plan.calls = [call_of value]; kept = [s]; held = [s]; passed = []})
  in
  let points = [point 2 outer_site outer_value; point 3 inner_site inner_value] in
  let resumes : Ownership_plan.resumes =
    { origin;
      depth = 2;
      entry_captures = None;
      parameter_type = (fun _ -> None);
      resume_at =
        (fun b -> List.find_map (fun (at, r) -> if Core_binder.equal b at && Core_binder.same_site b at then Some r else None) points) }
  in
  let p = Ownership_plan.region ~resumes ~n_outer:0 root in
  check "the first save keeps what the region lends" (Ownership_plan.save_moves p outer_site = Some []);
  check "the second moves what the first frame holds"
    (match Ownership_plan.save_moves p inner_site with Some [b] -> Core_binder.equal b s | _ -> false)

(* The body of a fixpoint [f a] a machine adopts as an entry, capturing [c]:
   [let r := f a in g r c].  The entry's frame holds [c], which the region
   does not own, so a save may move it -- but not where the call it is saved
   for re-enters the entry, which passes [c] again; a call of another
   function does not. *)
let () =
  let origin = GlobRef.VarRef (Id.of_string "outer") in
  let c = Core_binder.make ~origin ~level:0 () in
  let moves value =
    let site = Occurrence.fresh () in
    let root = MLletin (Id (Id.of_string "r"), nat, value, call "g" [fresh_rel 1; fresh_rel 4], site) in
    let call_site = match value with MLapp ((MLrel (_, o) | MLglob {occurrence = o; _}), _) -> o | _ -> assert false in
    let at_let = Core_binder.make ~origin ~level:3 ~site () in
    let resumes : Ownership_plan.resumes =
      { origin;
        depth = 3;
        entry_captures = Some 2;
        parameter_type = (fun _ -> None);
        resume_at =
          (fun b ->
            if Core_binder.equal b at_let && Core_binder.same_site b at_let then
              Some {calls = [call_site]; kept = [c]; held = [c]; passed = []}
            else None ) }
    in
    Ownership_plan.save_moves (Ownership_plan.region ~resumes ~n_outer:0 root) site
  in
  check "a save keeps a capture the call re-entering the entry passes" (moves (MLapp (fresh_rel 2, [fresh_rel 1])) = Some []);
  check "another call's save moves a capture the entry holds"
    (match moves (call "h" [fresh_rel 1]) with Some [b] -> Core_binder.equal b c | _ -> false)

(* The body of a fixpoint [f a] a machine adopts as an entry, capturing [c],
   [a] owned: [let u := h c in f a] -- a call of [f] enters the entry with
   [c] besides its argument, and takes both where nothing after it reads
   them; [let u := h c in g (f a) c] reads [c] beside it, which the call
   then copies. *)
let () =
  let origin = GlobRef.VarRef (Id.of_string "outer") in
  let c = Core_binder.make ~origin ~level:0 () and a = Core_binder.make ~origin ~level:2 () in
  let resumes : Ownership_plan.resumes = {origin; depth = 3; entry_captures = Some 2; parameter_type = (fun _ -> None); resume_at = (fun _ -> None)} in
  let moves body =
    let f = fresh_rel 3 in
    let at = match f with MLrel (_, o) -> o | _ -> assert false in
    let root = MLletin (Id (Id.of_string "u"), nat, call "h" [fresh_rel 3], body (MLapp (f, [fresh_rel 2])), Occurrence.fresh ()) in
    let planned = Ownership_plan.entry_moves (Ownership_plan.region ~owned:[1] ~resumes ~n_outer:0 root) in
    match List.find_map (fun (o, bs) -> if Occurrence.equal o at then Some bs else None) planned with
    | Some bs -> bs
    | None -> []
  in
  let same xs ys = List.length xs = List.length ys && List.for_all (fun x -> List.exists (Core_binder.equal x) ys) xs in
  check "a call re-entering the entry takes its argument and the capture" (same (moves Fun.id) [c; a]);
  check "not a capture read beside it" (same (moves (fun app -> call "g" [app; fresh_rel 4])) [a])

(* [(fix f n l := g n l) (len s) s], [s] an owned parameter: the fixpoint's
   parameters are bound to its arguments in order, so the second argument
   is [s]'s last use, and the first, reading [s] too, is evaluated before
   the call.  A fixpoint reading [s] as it runs leaves [s] read after them. *)
let () =
  let applied body =
    let s = fresh_rel 1 in
    let at = Occurrence.fresh () in
    let fix =
      MLfix
        ( 0,
          [|(Id.of_string "f", Tarr (nat, Tarr (lst, lst)))|],
          [|MLlam (Id (Id.of_string "n"), nat, MLlam (Id (Id.of_string "l"), lst, body))|],
          false,
          at )
    in
    let root = MLapp (fix, [call "len" [fresh_rel 1]; s]) in
    let read = match s with MLrel (_, o) -> o | _ -> assert false in
    let p = Ownership_plan.region ~owned:[1] ~n_outer:0 root in
    (Ownership_plan.use p read, Ownership_plan.evaluated_first p at)
  in
  let use, first = applied (call "g" [fresh_rel 2; fresh_rel 1]) in
  check "the last argument takes the variable" (use = Some Ownership_plan.Use.Move);
  check "the argument reading it before is evaluated first" (first = [0]);
  (* The body under f, n and l reads [s] at index 4. *)
  let use, first = applied (call "g" [fresh_rel 4; fresh_rel 1]) in
  check "a fixpoint reading it as it runs keeps it" (copied use);
  check "and nothing is evaluated first" (first = [])

(* [let r := weigh t in g s r] under [k], [t] and [s], [s] lent and kept
   by the frame saved at the let: the handler resuming there owns the
   frame's copy, so the read of [s] after the call moves it -- where the
   machine is certainly made; where it may not be, it is read as it was
   bound.  Not where the frame may keep [s] as a pointer, nor where [s] is
   passed to the function [k] the region is handed ([k s r]), whose
   signature is not the machine's to change, nor where moving [s] takes
   nothing a copy would not. *)
let () =
  let origin = GlobRef.VarRef (Id.of_string "weigh") in
  let s = Core_binder.make ~origin ~level:2 () in
  let value = call "weigh" [fresh_rel 2] in
  let site = Occurrence.fresh () in
  let call_site = match value with MLapp (MLglob g, _) -> g.occurrence | _ -> assert false in
  let at_let = Core_binder.make ~origin ~level:3 ~site () in
  let use ?(passed = []) ?(handed = false) ?(ty = Tvar (Rigid, 1)) certain =
    let read = fresh_rel 2 in
    let body = if handed then MLapp (fresh_rel 4, [read; fresh_rel 1]) else call "g" [read; fresh_rel 1] in
    let root = MLletin (Id (Id.of_string "r"), nat, value, body, site) in
    let o = match read with MLrel (_, o) -> o | _ -> assert false in
    let resumes : Ownership_plan.resumes =
      { origin;
        depth = 3;
        entry_captures = None;
        parameter_type = (fun level -> if level = 2 then Some ty else None);
        resume_at =
          (fun b ->
            if Core_binder.equal b at_let && Core_binder.same_site b at_let then
              Some {calls = [call_site]; kept = [s]; held = [s]; passed}
            else None ) }
    in
    Ownership_plan.use (Ownership_plan.region ~resumes ~certain ~n_outer:0 root) o
  in
  let moved = Some Ownership_plan.Use.Move in
  check "what follows a resume owns what the frame holds" (use true = moved);
  check "not where the machine may not be made" (use false <> moved);
  check "not what the frame may keep as a pointer" (use ~passed:[s] true <> moved);
  check "not an argument of a function the region is handed" (use ~handed:true true <> moved);
  check "not a parameter of a type not worth moving" (use ~ty:(Tdummy Ktype) true <> moved)

(* [g s s], [s] bound outside at the type [outer] gives it: a read that
   leaves the variable copies it as its Core type says -- a closure is
   retained, an inductive's value cloned, an erased value's bits copied; a
   type inference gave up on, as its declaration says, or as a box. *)
let () =
  let mode ?declared ty =
    let read = fresh_rel 1 in
    let root = call "g" [read; fresh_rel 1] in
    let o = match read with MLrel (_, o) -> o | _ -> assert false in
    Ownership_plan.use ?declared (Ownership_plan.region ~owned:[1] ~outer:(fun _ -> Some ty) ~n_outer:0 root) o
  in
  check "a closure is shared" (mode (Tarr (lst, lst)) = Some Share);
  check "an inductive's value is cloned" (mode lst = Some Clone);
  check "an erased value is copied" (mode (Tdummy Kprop) = Some Copy);
  check "a type abstraction is what it returns" (mode (Tarr (Tdummy Kprop, Tarr (lst, lst))) = Some Share);
  check "an unknown type is copied as declared" (mode ~declared:Minicpp.Tvoid Tunknown = Some Copy);
  check "or as a box" (mode Tunknown = Some Clone)

(* [g (fun _ => h s) t] and [g (fun _ => h s) s], [s] and [t] owned: a
   closure made where nothing after reads what it captures takes it by
   move, one beside a later read shares it, and one generated in place
   reads it where it stands. *)
let () =
  let closure () = MLlam (Id (Id.of_string "u"), nat, call "h" [fresh_rel 2]) in
  let modes ?in_place last =
    let lam = closure () in
    let root = call "g" [lam; fresh_rel last] in
    Ownership_plan.captures ?in_place (Ownership_plan.region ~owned:[1; 2] ~n_outer:0 root) lam
  in
  check "a last capture takes by move" (modes 2 = [(1, Ownership_plan.Capture.By_move)]);
  check "one read again shares" (modes 1 = [(1, Ownership_plan.Capture.Shared)]);
  check "in place, by reference" (modes ~in_place:true 2 = [(1, Ownership_plan.Capture.By_reference)])
