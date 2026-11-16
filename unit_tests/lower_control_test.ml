(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* LowerControl's tail loops: where a body of a function recursing only by
   tail calls continues its loop, and where it returns. *)

open Crane_plugin
open Names
open Control_ir

let check name cond =
  if not cond then (
    Printf.eprintf "lower_control: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}
let count = r "count"
let target = Loop.Function count

(* [count] takes two parameters. *)
let callee ~depth:_ = function
  | Core.Expr.Global (use : Core.Global_use.t) when GlobRef.UserOrd.equal use.callee count -> Some 2
  | _ -> None

let use () = Core.Global_use.monomorphic count
let call u args = Core.Expr.Apply {callee = Core.Expr.Global u; arguments = args}
let plus a b = Core.Expr.Apply {callee = Core.Expr.Global (Core.Global_use.monomorphic (r "plus")); arguments = [a; b]}
let lower body = Lower_control.tail_loop ~effects:Core_effects.empty ~target ~callee body
let continues_at us t = List.equal Core.Occurrence.equal (Term.continues t) (List.map Core.Global_use.occurrence us)
let id s = Core.Binder_name.Source (Id.of_string s)

let () =
  (* match n with O => acc | S m => count m (acc + 1), under [n; acc]. *)
  let u = use () in
  let body =
    Core.Expr.Match
      {scrutinee_type = nat; scrutinee = Core.Expr.fresh_rel 2;
        branches =
          [|
            {Core.Match.Branch.binders = []; result_type = nat; pattern = Core.Pattern.Wildcard;
              body = Core.Expr.fresh_rel 1};
           { Core.Match.Branch.binders = [(id "m", nat)];
             result_type = nat;
             pattern = Core.Pattern.Wildcard;
             body = call u [Core.Expr.fresh_rel 1; plus (Core.Expr.fresh_rel 2) (Core.Expr.fresh_rel 2)] } |];
               occurrence = Core.Occurrence.fresh ()}
  in
  ( match lower body with
  | Term.Match {branches = [{body = Return _; _}; {body = Continue c; _}]; _} ->
    check "the recursive call continues the function's loop" (Loop.equal c.target target);
    check "with the call's arguments" (List.length c.arguments = 2)
  | _ -> check "a match continues in one branch and returns from the other" false );
  check "the continue is the call's occurrence" (continues_at [u] (lower body));

  (* let x := plus n acc in count x x *)
  let u = use () in
  ( match lower
    (Core.Expr.Let
      {binder = id "x"; binder_type = nat; value = plus (Core.Expr.fresh_rel 2) (Core.Expr.fresh_rel 1);
        body = call u [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 1]; occurrence = Core.Occurrence.fresh ()}) with
  | Term.Let {body = Continue _; _} -> ()
  | _ -> check "a let's body continues" false );

  (* A call with fewer arguments than the parameters is a closure, and a
     call under a lambda runs where the lambda does: both are returned. *)
  let partial = call (use ()) [Core.Expr.fresh_rel 1] in
  check "a partial application is returned as it is" (lower partial = Term.Return partial);
  let under_lambda =
    Core.Expr.Lambda
      {parameter = id "y"; parameter_type = nat; body = call (use ()) [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 1]} in
  check "a call under a lambda is returned with it" (lower under_lambda = Term.Return under_lambda);

  (* A coercion of a recursive call continues, and keeps coercing what
     another branch returns. *)
  let u = use () in
  let coerced =
    Core.Expr.Boxed_value
      {value = Core.Expr.Match
        {scrutinee_type = nat; scrutinee = Core.Expr.fresh_rel 2;
          branches =
            [|
              {Core.Match.Branch.binders = []; result_type = nat; pattern = Core.Pattern.Wildcard;
                body = Core.Expr.fresh_rel 1};
               {Core.Match.Branch.binders = [];
                result_type = nat;
                pattern = Core.Pattern.Wildcard;
                body = call u [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1]} |];
                  occurrence = Core.Occurrence.fresh ()}; occurrence = Core.Occurrence.fresh ()}
  in
  match lower coerced with
  | Term.Match {branches = [{body = Return (Core.Expr.Boxed_value _); _}; {body = Continue _; _}]; _} -> ()
  | _ -> check "a coerced body continues, its returns coerced" false

(* The parameters a loop keeps: those every Continue passes on as they
   are, read at the depth the Continue is under. *)
let invariant body =
  Term.invariant_parameters {loop = target; parameters = [(id "n", nat); (id "acc", nat)]; body = lower body}

let () =
  (* match n with O => acc | S m => count n m *)
  let step =
    Core.Expr.Match
      {scrutinee_type = nat; scrutinee = Core.Expr.fresh_rel 2;
        branches =
          [|
            {Core.Match.Branch.binders = []; result_type = nat; pattern = Core.Pattern.Wildcard;
              body = Core.Expr.fresh_rel 1};
           { Core.Match.Branch.binders = [(id "m", nat)];
             result_type = nat;
             pattern = Core.Pattern.Wildcard;
             body = call (use ()) [Core.Expr.fresh_rel 3; Core.Expr.fresh_rel 1] } |];
               occurrence = Core.Occurrence.fresh ()}
  in
  check "a parameter passed on under a binder is kept, one passed the binder is not" (invariant step = [true; false]);
  check "parameters passed on as they are are kept"
    (invariant (call (use ()) [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1]) = [true; true]);
  check "parameters passed each other are not"
    (invariant (call (use ()) [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 2]) = [false; false])

(* Tail modulo cons: a recursive call held in a chain of constructors
   returned continues into the hole the chain leaves. *)
let cons = r "cons"
let lower_cons body = Lower_control.tail_loop ~modulo_cons:true ~effects:Core_effects.empty ~target ~callee body

let () =
  (* cons n (cons acc (count n acc)): two cells, the call in the second's hole. *)
  let u = use () in
  let body = Core.Expr.Construct {result_type = nat;
                                  constructor = cons;
                                  arguments =
                                    [Core.Expr.fresh_rel 2;
                                      Core.Expr.Construct
                                        {result_type = nat; constructor = cons;
                                          arguments =
                                            [Core.Expr.fresh_rel 1;
                                              call u [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1]];
                                                occurrence = Core.Occurrence.fresh ()}];
                                  occurrence = Core.Occurrence.fresh ()} in
  ( match lower_cons body with
  | Term.Continue_into {cells = [outer; inner]; next} ->
    check "each cell's hole is the argument holding the call" (outer.hole = 1 && inner.hole = 1);
    check "a cell keeps its other arguments" (List.length outer.arguments = 1);
    check "the chain continues by the call" (Core.Occurrence.equal next.occurrence (Core.Global_use.occurrence u))
  | _ -> check "a chain around a call continues into its hole" false );
  check "a chain's call is among the loop's continues" (continues_at [u] (lower_cons body));
  check "without modulo cons a chain is returned" (lower body = Term.Return body);
  (* cons (count n acc) (count n acc): two calls, no chain. *)
  let twice = Core.Expr.Construct {result_type = nat;
                                   constructor = cons;
                                   arguments =
                                     [call (use ()) [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1];
                                       call (use ()) [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1]];
                                   occurrence = Core.Occurrence.fresh ()} in
  check "a constructor holding two calls is returned" (lower_cons twice = Term.Return twice);
  (* A chain's call passing the parameters on keeps them. *)
  let kept = Core.Expr.Construct {result_type = nat;
                                  constructor = cons;
                                  arguments =
                                    [Core.Expr.fresh_rel 2;
                                      call (use ()) [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1]];
                                  occurrence = Core.Occurrence.fresh ()} in
  check "a chain's call counts as a turn"
    (Term.invariant_parameters {loop = target; parameters = [(id "n", nat); (id "acc", nat)]; body = lower_cons kept}
    = [true; true] )

(* A machine with a stack: a recursive call a let binds resumes into the
   let's body once it returns. *)
let lower_frames body = Lower_control.tail_loop ~frames:true ~effects:Core_effects.empty ~target ~callee body

let () =
  (* let x := count n acc in plus x x *)
  let u = use () in
  let body =
    Core.Expr.Let
      {binder = id "x"; binder_type = nat; value = call u [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 1];
        body = plus (Core.Expr.fresh_rel 1) (Core.Expr.fresh_rel 1); occurrence = Core.Occurrence.fresh ()} in
  ( match lower_frames body with
  | Term.Resume {binder; value = Continue c; body = Return _; _} ->
    check "the call's result is bound to the let's binder" (binder = id "x");
    check "the call enters the loop afresh" (Core.Occurrence.equal c.occurrence (Core.Global_use.occurrence u))
  | _ -> check "a let binding a recursive call resumes" false );
  check "the call is resumed after"
    (List.equal Core.Occurrence.equal (Term.resumed (lower_frames body)) [Core.Global_use.occurrence u]);
  check "and continues the loop" (continues_at [u] (lower_frames body));
  check "without frames a let binding a call is returned with it" (lower body = Term.Return body);
  (* let x := (match n with O => acc | S m => count m acc) in count x acc:
     translation runs a let's match that is neither custom nor a record's
     in a lambda invoked in place, where the call in a branch is an
     ordinary call; the tail call continues. *)
  let inner = use () and tail = use () in
  let rhs =
    Core.Expr.Match
      {scrutinee_type = nat; scrutinee = Core.Expr.fresh_rel 2;
        branches =
          [|
            {Core.Match.Branch.binders = []; result_type = nat; pattern = Core.Pattern.Wildcard;
              body = Core.Expr.fresh_rel 1};
           { Core.Match.Branch.binders = [(id "m", nat)];
             result_type = nat;
             pattern = Core.Pattern.Wildcard;
             body = call inner [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 2] } |];
               occurrence = Core.Occurrence.fresh ()}
  in
  let body =
    Core.Expr.Let
      {binder = id "x"; binder_type = nat; value = rhs; body = call tail [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 2];
        occurrence = Core.Occurrence.fresh ()} in
  let t = lower_frames body in
  check "a call ending a branch of a let's match run in a lambda is no turn" (Term.resumed t = []);
  check "the tail call after it continues alone" (continues_at [tail] t);
  (* let x := (match p with {a} => count a acc) in count x acc, a record's
     one branch: generated as statements assigning the binder, the call in
     the branch resumes. *)
  let kn = MutInd.make1 (KerName.make (ModPath.MPfile (DirPath.make [Id.of_string "T"])) (Label.make "R")) in
  Base.Table.add_inductive_kind kn (Core.Inductive.Kind.Record [{Core.Record.Field.projection = Some (r "a"); type_ = nat}]);
  let record = Core.Type.Global_app {head = GlobRef.IndRef (kn, 0); type_arguments = []; index_arguments = []} in
  let inner = use () and tail = use () in
  let rhs =
    Core.Expr.Match
      {scrutinee_type = record; scrutinee = Core.Expr.fresh_rel 2;
        branches = [| { Core.Match.Branch.binders = [(id "a", nat)];
             result_type = nat;
             pattern = Core.Pattern.Wildcard;
             body = call inner [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 2] } |];
               occurrence = Core.Occurrence.fresh ()}
  in
  let body =
    Core.Expr.Let
      {binder = id "x"; binder_type = nat; value = rhs; body = call tail [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 2];
        occurrence = Core.Occurrence.fresh ()} in
  let t = lower_frames body in
  check "a call ending a branch of a let's record match is resumed after"
    (List.equal Core.Occurrence.equal (Term.resumed t) [Core.Global_use.occurrence inner]);
  check "the tail call after it continues" (continues_at [inner; tail] t);
  check "a parameter passed on under the resumed binder is kept"
    (Term.invariant_parameters {loop = target; parameters = [(id "n", nat); (id "acc", nat)]; body = t} = [false; true])

(* A machine adopting a local fixpoint of one member: where it is applied,
   an Entry of its function, entered by a Continue of it; its body
   continues both the fixpoint and the function. *)
let lower_adopting adopted body =
  Lower_control.tail_loop ~frames:true ~adopted ~effects:Core_effects.empty ~target ~callee body

let () =
  (* (fix go k := match k with O => count n acc | S j => let y := go j in count n y) acc,
     under [n; acc]. *)
  let fix = Core.Occurrence.fresh () and go_read = Core.Occurrence.fresh () in
  let back = use () and back' = use () in
  let go_body =
    Core.Expr.Match
      {scrutinee_type = nat; scrutinee = Core.Expr.fresh_rel 1;
        branches =
          [|
            {Core.Match.Branch.binders = []; result_type = nat; pattern = Core.Pattern.Wildcard;
              body = call back [Core.Expr.fresh_rel 4; Core.Expr.fresh_rel 3]};
           { Core.Match.Branch.binders = [(id "j", nat)];
             result_type = nat;
             pattern = Core.Pattern.Wildcard;
             body =
               Core.Expr.Let
                 {binder = id "y"; binder_type = nat;
                   value = Core.Expr.Apply
                     {callee = Core.Expr.Bound_variable {index = 3; occurrence = go_read};
                       arguments = [Core.Expr.fresh_rel 1]};
                         body = call back' [Core.Expr.fresh_rel 6; Core.Expr.fresh_rel 1];
                           occurrence = Core.Occurrence.fresh ()}
           } |]; occurrence = Core.Occurrence.fresh ()}
  in
  let fixpoint =
    Core.Expr.Fixpoint
      (Core.Recursion.Group.singleton (Id.of_string "go") (Core.Type.Arrow {parameter = nat; result = nat})
        (Core.Expr.Lambda {parameter = id "k"; parameter_type = nat; body = go_body}) fix) in
  let t = lower_adopting fix (Core.Expr.Apply {callee = fixpoint; arguments = [Core.Expr.fresh_rel 1]}) in
  ( match t with
  | Term.Entry {entered; name = None; scope = Continue c} ->
    check "the entry is the fixpoint's function" (Loop.equal entered.loop (Loop.Member (fix, 0)));
    check "over its parameters" (List.length entered.parameters = 1);
    check "the fixpoint applied enters it" (Loop.equal c.target entered.loop && Core.Occurrence.equal c.occurrence fix)
  | _ -> check "an adopted fixpoint applied is an entry" false );
  check "an entry's body continues the function and the fixpoint"
    (List.equal Core.Occurrence.equal (Term.continues t)
       [Core.Global_use.occurrence back; go_read; Core.Global_use.occurrence back'; fix] );
  check "only the call a let binds is resumed after" (List.equal Core.Occurrence.equal (Term.resumed t) [go_read]);
  check "the function's parameters are read under the entry's binders"
    (Term.invariant_parameters
      {loop = target; parameters = [(id "n", nat); (id "acc", nat)]; body = t} = [true; false]);
  check "a fixpoint not adopted is returned"
    (lower_frames (Core.Expr.Apply {callee = fixpoint; arguments = [Core.Expr.fresh_rel 1]}) = Term.Return
      (Core.Expr.Apply {callee = fixpoint; arguments = [Core.Expr.fresh_rel 1]}));
  (* let g := fix go k := ... in g n: the let's binder names the entry. *)
  let g_read = Core.Occurrence.fresh () in
  let t =
    lower_adopting fix
      (Core.Expr.Let
        {binder = id "g"; binder_type = Core.Type.Arrow {parameter = nat; result = nat}; value = fixpoint;
          body = Core.Expr.Apply
            {callee = Core.Expr.Bound_variable {index = 1; occurrence = g_read}; arguments = [Core.Expr.fresh_rel 3]};
              occurrence = Core.Occurrence.fresh ()}) in
  match t with
  | Term.Entry {name = Some (x, _); scope = Continue c; _} ->
    check "the let's binder is the entry's name" (x = id "g");
    check "a call by that name enters it" (Core.Occurrence.equal c.occurrence g_read)
  | _ -> check "a let binding an adopted fixpoint is an entry" false
