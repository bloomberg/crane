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
