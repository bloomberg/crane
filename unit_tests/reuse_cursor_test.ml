(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* The Perceus reuse cursor of a loop built tail modulo cons: which
   parameter it walks, the turns it steps at, and what each step reads
   first; and the loops it cannot follow. *)

open Crane_plugin
open Names
open Miniml
open Control_ir

let check name cond =
  if not cond then (
    Printf.eprintf "reuse_cursor: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let id s = Id (Id.of_string s)
let nat = Tglob (r "nat", [], [])
let lst = Tglob (r "lst", [], [])
let other = Tglob (r "other", [], [])
let nil = r "nil"
let cons = r "cons"
let target = Loop.Function (r "f")

(* [cons] stores its tail, its argument 1, behind the pointer. *)
let pointer_fields c = if GlobRef.UserOrd.equal c cons then Some [1] else None
let plan ?(parameters = [(id "l", lst)]) body =
  Reuse_cursor.plan ~pointer_fields ~in_place:(fun _ _ -> false) {loop = target; parameters; body}

let app f args = MLapp (MLglob (Global_use.monomorphic (r f)), args)
let cell ?(hole = 1) arguments : Term.cell = {constructor = cons; hole; arguments}
let continue_ occurrence arguments : Term.continue_ = {target; occurrence; arguments}

(* match <scrutinee> with nil => nil | cons x xs => <body>, [body] under x
   and xs, xs innermost; the branch yields [result]. *)
let on_list ?(result = lst) scrutinee body =
  Term.Match
    { scrutinee_type = lst;
      scrutinee;
      branches =
        [ {binders = []; result_type = result; pattern = Pusual nil; body = Return (MLcons (lst, nil, []))};
          { binders = [(id "x", nat); (id "xs", lst)];
            result_type = result;
            pattern = Pcons (cons, [Prel 2; Prel 1]);
            body } ] }

let cells_read_first (s : Reuse_cursor.step) =
  match s.action with Recycle {cells_read_first} -> cells_read_first | Release -> []

let steps_of = function
  | Some (c : Reuse_cursor.t) -> List.map (fun (s : Reuse_cursor.step) -> (s.turn, cells_read_first s, s.arguments_read_first)) c.steps
  | None -> []

let releases = function
  | Some (c : Reuse_cursor.t) ->
    List.filter_map (fun (s : Reuse_cursor.step) -> match s.action with Release -> Some s.turn | Recycle _ -> None) c.steps
  | None -> []

let () =
  (* map: cons (g x) (f xs) walks [l] on to its tail, reading nothing first. *)
  let o = Occurrence.fresh () in
  let map = on_list (fresh_rel 1) (Continue_into {cells = [cell [app "g" [fresh_rel 2]]]; next = continue_ o [fresh_rel 1]}) in
  ( match plan map with
  | Some c ->
    check "map walks its one parameter" (c.parameter = 0);
    check "map steps where it builds, reading nothing first" (steps_of (Some c) = [(o, [], [])])
  | None -> check "map has a cursor" false );

  (* suffix_sums: cons (sum l) (f xs) reads the list whole after the steal. *)
  let o = Occurrence.fresh () in
  let whole = on_list (fresh_rel 1) (Continue_into {cells = [cell [app "sum" [fresh_rel 3]]]; next = continue_ o [fresh_rel 1]}) in
  check "the outermost cell reads the walked list first" (steps_of (plan whole) = [(o, [(0, 0)], [])]);

  (* let s = sum l in cons s (f xs): the let is evaluated where it stands,
     before the steal, into a value of its own; the cell reads that, not
     the list. *)
  let under_let ?(ty = nat) value cell_arg =
    let o = Occurrence.fresh () in
    ( o,
      on_list (fresh_rel 1)
        (Term.Let
           { binder = id "s";
             binder_type = ty;
             value;
             body = Continue_into {cells = [cell [cell_arg]]; next = continue_ o [fresh_rel 2]} }) )
  in
  let o, summed = under_let (app "sum" [fresh_rel 3]) (fresh_rel 1) in
  check "a let holding a call's value reads nothing of the cell later" (steps_of (plan summed) = [(o, [], [])]);
  (* let s = l in cons (sum s) (f xs): the let names the list itself. *)
  let o, aliased = under_let ~ty:lst (fresh_rel 3) (app "sum" [fresh_rel 1]) in
  check "a let naming the walked list reads it later" (steps_of (plan aliased) = [(o, [(0, 0)], [])]);
  (* let s = fun _ => sum l in cons (s x) (f xs): the closure reads the list
     when it is called, after the steal. *)
  let o, closure =
    under_let ~ty:(Tarr (nat, nat)) (MLlam (id "_", nat, app "sum" [fresh_rel 4])) (MLapp (fresh_rel 1, [fresh_rel 3]))
  in
  check "a let holding a closure reads what it captures later" (steps_of (plan closure) = [(o, [(0, 0)], [])]);

  (* stutter: cons (S x) (cons x (f xs)): the inner cell reads the element
     the outer one is rebuilt over, the outer one reads it before. *)
  let o = Occurrence.fresh () in
  let stutter =
    on_list (fresh_rel 1)
      (Continue_into {cells = [cell [app "S" [fresh_rel 2]]; cell [fresh_rel 2]]; next = continue_ o [fresh_rel 1]})
  in
  check "an inner cell reads the rebuilt cell first" (steps_of (plan stutter) = [(o, [(1, 0)], [])]);

  (* scale acc l: cons (x * acc) (f (acc + x) xs): the next accumulator
     reads the element; the walked parameter is the second. *)
  let o = Occurrence.fresh () in
  let scale =
    on_list (fresh_rel 1)
      (Continue_into
         { cells = [cell [app "mul" [fresh_rel 2; fresh_rel 4]]];
           next = continue_ o [app "add" [fresh_rel 4; fresh_rel 2]; fresh_rel 1] })
  in
  let parameters = [(id "acc", nat); (id "l", lst)] in
  ( match plan ~parameters scale with
  | Some c ->
    check "scale walks its list" (c.parameter = 1);
    check "the next accumulator is read first" (steps_of (Some c) = [(o, [], [0])]);
    (* Lowered with its parameters swapped, the accumulator is the second. *)
    ( match Reuse_cursor.positioned c [Some 1; Some 0] with
    | Some p ->
      check "positioned: the cursor's position" (p.parameter = 0);
      check "positioned: what is read first" (steps_of (Some p) = [(o, [], [1])])
    | None -> check "positioned keeps the cursor" false );
    check "a cursor standing for no parameter is none" (Reuse_cursor.positioned c [Some 0; None] = None)
  | None -> check "scale has a cursor" false );

  (* filter: a turn walking on building nothing releases the cell it leaves. *)
  let kept = Occurrence.fresh () and skipped = Occurrence.fresh () in
  let filter =
    on_list (fresh_rel 1)
      (Term.Match
         { scrutinee_type = nat;
           scrutinee = app "even" [fresh_rel 2];
           branches =
             [ { binders = [];
                 result_type = lst;
                 pattern = Pwild;
                 body = Continue_into {cells = [cell [fresh_rel 2]]; next = continue_ kept [fresh_rel 1]} };
               {binders = []; result_type = lst; pattern = Pwild; body = Continue (continue_ skipped [fresh_rel 1])} ] })
  in
  check "filter steps at both turns" (steps_of (plan filter) = [(kept, [], []); (skipped, [], [])]);
  check "filter's turn building nothing releases" (releases (plan filter) = [skipped]);

  (* count_skip acc l: the turn building nothing passes an accumulator
     reading the element, which is read before the release. *)
  let kept = Occurrence.fresh () and skipped = Occurrence.fresh () in
  let count_skip =
    on_list (fresh_rel 1)
      (Term.Match
         { scrutinee_type = nat;
           scrutinee = app "even" [fresh_rel 2];
           branches =
             [ { binders = [];
                 result_type = lst;
                 pattern = Pwild;
                 body = Continue_into {cells = [cell [fresh_rel 4]]; next = continue_ kept [fresh_rel 4; fresh_rel 1]} };
               { binders = [];
                 result_type = lst;
                 pattern = Pwild;
                 body = Continue (continue_ skipped [app "add" [fresh_rel 4; fresh_rel 2]; fresh_rel 1]) } ] })
  in
  check "a released cell's element is read first"
    (steps_of (plan ~parameters:[(id "acc", nat); (id "l", lst)] count_skip) = [(kept, [], []); (skipped, [], [0])]);

  (* drop_all: every turn walking on builds nothing -- nothing to recycle. *)
  let drop_all = on_list (fresh_rel 1) (Continue (continue_ (Occurrence.fresh ()) [fresh_rel 1])) in
  check "a loop recycling nothing has no cursor" (plan drop_all = None);

  (* swap: two cells a turn walks on to a field of the second cell. *)
  let swap =
    on_list (fresh_rel 1)
      (on_list (fresh_rel 1)
         (Continue_into {cells = [cell [fresh_rel 2]; cell [fresh_rel 4]]; next = continue_ (Occurrence.fresh ()) [fresh_rel 1]}))
  in
  check "walking on to a field of another cell declines the cursor" (plan swap = None);

  (* A cell of another type has no room for the cursor's. *)
  let resized =
    on_list ~result:other (fresh_rel 1)
      (Continue_into {cells = [cell [fresh_rel 2]]; next = continue_ (Occurrence.fresh ()) [fresh_rel 1]})
  in
  check "a cell of another type declines the cursor" (plan resized = None);

  (* A turn passing the list itself keeps the cursor where it stands. *)
  let o = Occurrence.fresh () in
  let kept =
    on_list (fresh_rel 1)
      (Term.Match
         { scrutinee_type = nat;
           scrutinee = app "even" [fresh_rel 2];
           branches =
             [ {binders = []; result_type = lst; pattern = Pwild; body = Continue_into {cells = [cell [fresh_rel 2]]; next = continue_ o [fresh_rel 1]}};
               { binders = [];
                 result_type = lst;
                 pattern = Pwild;
                 body = Continue_into {cells = [cell [fresh_rel 2]]; next = continue_ (Occurrence.fresh ()) [fresh_rel 3]} } ] })
  in
  check "a turn passing the walked list on as it is takes no step" (List.map (fun (t, _, _) -> t) (steps_of (plan kept)) = [o]);

  (* Two parameters each walked on: no one cursor. *)
  let both =
    on_list (fresh_rel 2)
      (on_list (fresh_rel 3)
         (Continue_into {cells = [cell [fresh_rel 2]]; next = continue_ (Occurrence.fresh ()) [fresh_rel 3; fresh_rel 1]}))
  in
  check "two walked parameters have no cursor" (plan ~parameters:[(id "a", lst); (id "b", lst)] both = None)
