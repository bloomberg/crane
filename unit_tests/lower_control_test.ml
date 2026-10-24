(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* LowerControl's tail loops: where a body of a function recursing only by
   tail calls continues its loop, and where it returns. *)

open Crane_plugin
open Names
open Miniml
open Control_ir

let check name cond =
  if not cond then (
    Printf.eprintf "lower_control: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Tglob (r "nat", [], [])
let count = r "count"
let target = Loop.Function count

(* [count] takes two parameters. *)
let callee ~depth:_ = function
  | MLglob use when GlobRef.UserOrd.equal use.callee count -> Some 2
  | _ -> None

let use () = Global_use.monomorphic count
let call u args = MLapp (MLglob u, args)
let plus a b = MLapp (MLglob (Global_use.monomorphic (r "plus")), [a; b])
let lower ?inlined body = Lower_control.tail_loop ?inlined ~effects:Core_effects.empty ~target ~callee body
let continues_at us t = List.equal Occurrence.equal (continues t) (List.map Global_use.occurrence us)
let id s = Id (Id.of_string s)

let () =
  (* match n with O => acc | S m => count m (acc + 1), under [n; acc]. *)
  let u = use () in
  let body =
    MLcase
      ( nat,
        fresh_rel 2,
        [| ([], nat, Pwild, fresh_rel 1);
           ([(id "m", nat)], nat, Pwild, call u [fresh_rel 1; plus (fresh_rel 2) (fresh_rel 2)]) |] )
  in
  ( match lower body with
  | Term.Match {branches = [{body = Return _; _}; {body = Continue c; _}]; _} ->
    check "the recursive call continues the function's loop" (Loop.equal c.target target);
    check "with the call's arguments" (List.length c.arguments = 2)
  | _ -> check "a match continues in one branch and returns from the other" false );
  check "the continue is the call's occurrence" (continues_at [u] (lower body));

  (* let x := plus n acc in count x x *)
  let u = use () in
  ( match lower (MLletin (id "x", nat, plus (fresh_rel 2) (fresh_rel 1), call u [fresh_rel 1; fresh_rel 1], Occurrence.fresh ())) with
  | Term.Let {body = Continue _; _} -> ()
  | _ -> check "a let's body continues" false );

  (* A call with fewer arguments than the parameters is a closure, and a
     call under a lambda runs where the lambda does: both are returned. *)
  let partial = call (use ()) [fresh_rel 1] in
  check "a partial application is returned as it is" (lower partial = Term.Return partial);
  let under_lambda = MLlam (id "y", nat, call (use ()) [fresh_rel 1; fresh_rel 1]) in
  check "a call under a lambda is returned with it" (lower under_lambda = Term.Return under_lambda);

  (* A coercion of a recursive call continues, and keeps coercing what
     another branch returns. *)
  let u = use () in
  let coerced =
    MLmagic
      ( Mboxed,
        MLcase (nat, fresh_rel 2, [| ([], nat, Pwild, fresh_rel 1); ([], nat, Pwild, call u [fresh_rel 2; fresh_rel 1]) |]) )
  in
  ( match lower coerced with
  | Term.Match {branches = [{body = Return (MLmagic (Mboxed, _)); _}; {body = Continue _; _}]; _} -> ()
  | _ -> check "a coerced body continues, its returns coerced" false );

  (* A partner the function continues in: its body in place, its
     parameter bound to the argument, its own call of the function a
     continue. *)
  let into_partner = Global_use.monomorphic (r "partner") and back = use () in
  let partner_body = call back [fresh_rel 1; fresh_rel 1] in
  let inlined u =
    if Occurrence.equal (Global_use.occurrence u) (Global_use.occurrence into_partner) then
      Some ([(id "p", nat)], partner_body)
    else None
  in
  ( match lower ~inlined (call into_partner [fresh_rel 2]) with
  | Term.Let {binder; body = Continue c; _} ->
    check "the partner's parameter is bound" (binder = id "p");
    check "the partner's call back continues" (Occurrence.equal c.occurrence (Global_use.occurrence back))
  | _ -> check "a continued partner is inlined" false )

(* The parameters a loop keeps: those every Continue passes on as they
   are, read at the depth the Continue is under. *)
let invariant body =
  invariant_parameters {loop = target; parameters = [(id "n", nat); (id "acc", nat)]; body = lower body}

let () =
  (* match n with O => acc | S m => count n m *)
  let step =
    MLcase
      ( nat,
        fresh_rel 2,
        [| ([], nat, Pwild, fresh_rel 1); ([(id "m", nat)], nat, Pwild, call (use ()) [fresh_rel 3; fresh_rel 1]) |] )
  in
  check "a parameter passed on under a binder is kept, one passed the binder is not" (invariant step = [true; false]);
  check "parameters passed on as they are are kept" (invariant (call (use ()) [fresh_rel 2; fresh_rel 1]) = [true; true]);
  check "parameters passed each other are not" (invariant (call (use ()) [fresh_rel 1; fresh_rel 2]) = [false; false])

(* Tail modulo cons: a recursive call held in a chain of constructors
   returned continues into the hole the chain leaves. *)
let cons = r "cons"
let lower_cons body = Lower_control.tail_loop ~modulo_cons:true ~effects:Core_effects.empty ~target ~callee body

let () =
  (* cons n (cons acc (count n acc)): two cells, the call in the second's hole. *)
  let u = use () in
  let body = MLcons (nat, cons, [fresh_rel 2; MLcons (nat, cons, [fresh_rel 1; call u [fresh_rel 2; fresh_rel 1]])]) in
  ( match lower_cons body with
  | Term.Continue_into {cells = [outer; inner]; next} ->
    check "each cell's hole is the argument holding the call" (outer.hole = 1 && inner.hole = 1);
    check "a cell keeps its other arguments" (List.length outer.arguments = 1);
    check "the chain continues by the call" (Occurrence.equal next.occurrence (Global_use.occurrence u))
  | _ -> check "a chain around a call continues into its hole" false );
  check "a chain's call is among the loop's continues" (continues_at [u] (lower_cons body));
  check "without modulo cons a chain is returned" (lower body = Term.Return body);
  (* cons (count n acc) (count n acc): two calls, no chain. *)
  let twice = MLcons (nat, cons, [call (use ()) [fresh_rel 2; fresh_rel 1]; call (use ()) [fresh_rel 2; fresh_rel 1]]) in
  check "a constructor holding two calls is returned" (lower_cons twice = Term.Return twice);
  (* A chain's call passing the parameters on keeps them. *)
  let kept = MLcons (nat, cons, [fresh_rel 2; call (use ()) [fresh_rel 2; fresh_rel 1]]) in
  check "a chain's call counts as a turn"
    (invariant_parameters {loop = target; parameters = [(id "n", nat); (id "acc", nat)]; body = lower_cons kept}
    = [true; true] )

(* A machine with a stack: a recursive call a let binds resumes into the
   let's body once it returns. *)
let lower_frames body = Lower_control.tail_loop ~frames:true ~effects:Core_effects.empty ~target ~callee body

let () =
  (* let x := count n acc in plus x x *)
  let u = use () in
  let body = MLletin (id "x", nat, call u [fresh_rel 2; fresh_rel 1], plus (fresh_rel 1) (fresh_rel 1), Occurrence.fresh ()) in
  ( match lower_frames body with
  | Term.Resume {binder; value = Continue c; body = Return _; _} ->
    check "the call's result is bound to the let's binder" (binder = id "x");
    check "the call enters the loop afresh" (Occurrence.equal c.occurrence (Global_use.occurrence u))
  | _ -> check "a let binding a recursive call resumes" false );
  check "the call is resumed after" (List.equal Occurrence.equal (resumed (lower_frames body)) [Global_use.occurrence u]);
  check "and continues the loop" (continues_at [u] (lower_frames body));
  check "without frames a let binding a call is returned with it" (lower body = Term.Return body);
  (* let x := (match n with O => acc | S m => count m acc) in count x acc:
     the call in a branch resumes, the tail call continues. *)
  let inner = use () and tail = use () in
  let rhs = MLcase (nat, fresh_rel 2, [| ([], nat, Pwild, fresh_rel 1); ([(id "m", nat)], nat, Pwild, call inner [fresh_rel 1; fresh_rel 2]) |]) in
  let body = MLletin (id "x", nat, rhs, call tail [fresh_rel 1; fresh_rel 2], Occurrence.fresh ()) in
  let t = lower_frames body in
  check "a call ending a branch of a let's right-hand side is resumed after"
    (List.equal Occurrence.equal (resumed t) [Global_use.occurrence inner]);
  check "the tail call after it continues" (continues_at [inner; tail] t);
  check "a parameter passed on under the resumed binder is kept"
    (invariant_parameters {loop = target; parameters = [(id "n", nat); (id "acc", nat)]; body = t} = [false; true])
