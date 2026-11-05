(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Which parameters a tail loop's turn moves into their own next value
   (Ownership_plan.continue_moves): an accumulator rebuilt around itself
   is; one read again by another argument, or beside a part of itself,
   passed on as it is, or read by a closure, is not; a machine moves
   nothing so. *)

open Crane_plugin
open Names
open Miniml
open Control_ir

let check name cond =
  if not cond then (
    Printf.eprintf "continue_moves: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let id s = Id (Id.of_string s)
let nat = Tglob (r "nat", [], [])
let lst = Tglob (r "lst", [], [])
let nil = r "nil"
let cons = r "cons"
let target = Loop.Function (r "f")
let app f args = MLapp (MLglob (Global_use.monomorphic (r f)), args)
let continue_ occurrence arguments = Term.Continue {target; occurrence; arguments}

(* A loop over [l] and [acc], acc innermost: match l with nil => acc |
   cons x xs => <turn>, [turn] under x and xs, xs innermost; there [acc]
   is [MLrel 3], [x] [MLrel 2], [xs] [MLrel 1]. *)
let loop turn : Term.loop =
  { loop = target;
    parameters = [(id "l", lst); (id "acc", lst)];
    body =
      Term.Match
        { scrutinee_type = lst;
          scrutinee = fresh_rel 2;
          branches =
            [ {binders = []; result_type = lst; pattern = Pusual nil; body = Return (fresh_rel 1)};
              { binders = [(id "x", nat); (id "xs", lst)];
                result_type = lst;
                pattern = Pcons (cons, [Prel 2; Prel 1]);
                body = turn } ] } }

let moves turn = Ownership_plan.continue_moves (loop turn)
let flags o turn = List.find_map (fun (o', f) -> if Occurrence.equal o o' then Some f else None) (moves turn)

let () =
  let acc = fresh_rel 3 and x = fresh_rel 2 and xs = fresh_rel 1 in
  let consed a = MLcons (lst, cons, [x; a]) in
  let o = Occurrence.fresh () in
  check "rev: the accumulator rebuilt around itself is moved, the list walked on is not"
    (flags o (continue_ o [xs; consed acc]) = Some [false; true]);
  let o = Occurrence.fresh () in
  check "an accumulator another argument reads too is not moved"
    (flags o (continue_ o [app "drop" [xs; fresh_rel 3]; consed acc]) = Some [false; false]);
  let o = Occurrence.fresh () in
  check "an accumulator passed on as it is is not moved" (flags o (continue_ o [xs; acc]) = Some [false; false]);
  let o = Occurrence.fresh () in
  check "an accumulator a closure reads is not moved"
    (flags o (continue_ o [xs; app "g" [MLlam (id "y", nat, fresh_rel 4)]]) = Some [false; false]);
  (* match acc with cons y ys => f xs (cons y acc): [y] is a part of
     [acc], read beside it. *)
  let o = Occurrence.fresh () in
  let on_acc =
    Term.Match
      { scrutinee_type = lst;
        scrutinee = acc;
        branches =
          [ { binders = [(id "y", nat); (id "ys", lst)];
              result_type = lst;
              pattern = Pcons (cons, [Prel 2; Prel 1]);
              body = continue_ o [fresh_rel 3; MLcons (lst, cons, [fresh_rel 2; fresh_rel 5])] } ] }
  in
  check "an accumulator read beside a part of itself is not moved" (flags o on_acc = Some [false; false]);
  (* A machine's turn resumes after a call: nothing is planned. *)
  let o = Occurrence.fresh () in
  let resumed =
    Term.Resume {binder = id "r"; binder_type = lst; value = continue_ o [xs; consed acc]; body = Return (fresh_rel 1)}
  in
  check "a machine's loop moves nothing so" (moves resumed = [])
