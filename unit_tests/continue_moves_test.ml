(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* What a tail loop's turn moves into its parameters' next values
   (Ownership_ir.continue_moves): an accumulator rebuilt around itself
   is moved; one read again by another argument, or beside a part of
   itself, passed on as it is, or read by a closure, is not.  A local of
   the turn passed whole is moved, even where another argument names it
   (the lowering moves it at its last read), but not where another reads a
   part of it.  A machine moves nothing so. *)

open Crane_plugin
open Names
open Control_ir

let check name cond =
  if not cond then (
    Printf.eprintf "continue_moves: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let id s = Core.Binder_name.Source (Id.of_string s)
let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}
let lst = Core.Type.Global_app {head = r "lst"; type_arguments = []; index_arguments = []}
let nil = r "nil"
let cons = r "cons"
let target = Loop.Function (r "f")
let app f args = Core.Expr.Apply {callee = Core.Expr.Global (Core.Global_use.monomorphic (r f)); arguments = args}
let continue_ occurrence arguments = Term.Continue {target; occurrence; arguments}

(* A loop over [l] and [acc], acc innermost: match l with nil => acc |
   cons x xs => <turn>, [turn] under x and xs, xs innermost; there [acc]
   is [Core.Expr.Bound_variable 3], [x] [Core.Expr.Bound_variable 2], [xs] [Core.Expr.Bound_variable 1]. *)
let loop turn : Term.loop =
  { loop = target;
    parameters = [(id "l", lst); (id "acc", lst)];
    body =
      Term.Match
        { scrutinee_type = lst;
          scrutinee = Core.Expr.fresh_rel 2;
          branches =
            [ {binders = [];
               result_type = lst;
               pattern = Core.Pattern.binding_all nil 0;
               body = Return (Core.Expr.fresh_rel 1)};
              { binders = [(id "x", nat); (id "xs", lst)];
                result_type = lst;
                pattern = Core.Pattern.Constructor {constructor = cons;
                                                    fields = [Core.Pattern.Bound_variable 2; Core.Pattern.Bound_variable 1]};
                body = turn } ] } }

let moves turn = Ownership_ir.continue_moves ~effects:Core_effects.empty (loop turn)
let k = Ownership_ir.Continue_move.Keep
let p = Ownership_ir.Continue_move.Move_parameter
let a = Ownership_ir.Continue_move.Move_argument
let flags o turn = List.find_map (fun (o', f) -> if Core.Occurrence.equal o o' then Some f else None) (moves turn)

let () =
  let acc = Core.Expr.fresh_rel 3 and x = Core.Expr.fresh_rel 2 and xs = Core.Expr.fresh_rel 1 in
  let consed a = Core.Expr.Construct {result_type = lst;
                                      constructor = cons;
                                      arguments = [x; a];
                                      occurrence = Core.Occurrence.fresh ()} in
  let o = Core.Occurrence.fresh () in
  check "rev: the accumulator rebuilt around itself is moved, the list walked on is not"
    (flags o (continue_ o [xs; consed acc]) = Some [k; p]);
  let o = Core.Occurrence.fresh () in
  check "an accumulator another argument reads too is not moved"
    (flags o (continue_ o [app "drop" [xs; Core.Expr.fresh_rel 3]; consed acc]) = Some [k; k]);
  let o = Core.Occurrence.fresh () in
  check "an accumulator passed on as it is is not moved" (flags o (continue_ o [xs; acc]) = Some [k; k]);
  let o = Core.Occurrence.fresh () in
  check "an accumulator a closure reads is not moved"
    (flags o (continue_ o [xs; app "g" [Core.Expr.Lambda {parameter = id "y"; parameter_type = nat; body = Core.Expr.fresh_rel 4}]]) = Some [k; k]);
  (* match acc with cons y ys => f xs (cons y acc): [y] is a part of
     [acc], read beside it. *)
  let o = Core.Occurrence.fresh () in
  let on_acc =
    Term.Match
      { scrutinee_type = lst;
        scrutinee = acc;
        branches =
          [ { binders = [(id "y", nat); (id "ys", lst)];
              result_type = lst;
              pattern = Core.Pattern.Constructor {constructor = cons;
                                                  fields = [Core.Pattern.Bound_variable 2; Core.Pattern.Bound_variable 1]};
              body = continue_ o [Core.Expr.fresh_rel 3; Core.Expr.Construct {result_type = lst;
                                                                              constructor = cons;
                                                                              arguments = [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 5];
                                                                              occurrence = Core.Occurrence.fresh ()}] } ] }
  in
  check "an accumulator read beside a part of itself is not moved" (flags o on_acc = Some [k; k]);
  (* let next := cons x acc in f xs next: [next] is [Core.Expr.Bound_variable 1], [xs] [Core.Expr.Bound_variable 2]. *)
  let let_next body = Term.Let {binder = id "next"; binder_type = lst; value = consed acc; body} in
  let o = Core.Occurrence.fresh () in
  check "a local passed whole, read nowhere else, is moved"
    (flags o (let_next (continue_ o [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1])) = Some [k; a]);
  let o = Core.Occurrence.fresh () in
  check "a local another argument names is moved at the last read"
    (flags o (let_next (continue_ o [app "drop" [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1]; Core.Expr.fresh_rel 1])) = Some [k; a]);
  (* match next with cons y ys => f ys next: [ys] is a part of [next]. *)
  let o = Core.Occurrence.fresh () in
  let on_next =
    Term.Match
      { scrutinee_type = lst;
        scrutinee = Core.Expr.fresh_rel 1;
        branches =
          [ { binders = [(id "y", nat); (id "ys", lst)];
              result_type = lst;
              pattern = Core.Pattern.Constructor {constructor = cons;
                                                  fields = [Core.Pattern.Bound_variable 2; Core.Pattern.Bound_variable 1]};
              body = continue_ o [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 3] } ] }
  in
  check "a local another argument reads a part of is not moved" (flags o (let_next on_next) = Some [k; k]);
  (* A machine's turn resumes after a call: nothing is planned. *)
  let o = Core.Occurrence.fresh () in
  let resumed =
    Term.Resume {binder = id "r"; binder_type = lst; value = continue_ o [xs; consed acc]; body = Return (Core.Expr.fresh_rel 1)}
  in
  check "a machine's loop moves nothing so" (moves resumed = [])
