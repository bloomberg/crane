(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* What follows a bound match, copied into its branches: under each
   branch's binders and lets, a copy of its own past the first, and
   refused past the budget. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "normalize: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let x s = Core.Binder_name.Source (Id.of_string s)
let tmp n = Core.Binder_name.Generated (Core_util.temporary_id n)
let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}
let tree = Core.Type.Global_app {head = r "tree"; type_arguments = []; index_arguments = []}
let h = Core.Global_use.monomorphic (r "h")
let k = Core.Global_use.monomorphic (r "k")

let rec occurrences e =
  let here =
    match e with
    | Core.Expr.Bound_variable {occurrence = o; _}
    | Core.Expr.Let {occurrence = o; _}
    | Core.Expr.Match {occurrence = o; _}
    | Core.Expr.Fixpoint {occurrence = o; _} | Core.Expr.Cofixpoint {occurrence = o; _} ->
      [o]
    | Core.Expr.Global u -> [Core.Global_use.occurrence u]
    | _ -> []
  in
  let below = ref [] in
  Core_util.ast_iter (fun c -> below := !below @ occurrences c) e;
  here @ !below

let shared es = Core.Occurrence.shared (fun visit -> List.iter (fun e -> List.iter visit (occurrences e)) es) <> []

let fresh =
  let n = ref 10 in
  fun () ->
    incr n;
    tmp !n

(* [let _tmp1 : nat := match _ with Node l => l | Leaf => let z := k y in z
   in let _tmp2 := h _tmp1 y in _tmp2], [y] the variable around. *)
let () =
  let occ = Core.Occurrence.fresh () in
  let branches =
    [|
      {Core.Match.Branch.binders = [(x "l", tree)]; result_type = nat; pattern = Core.Pattern.binding_all (r "Node") 1;
        body = Core.Expr.fresh_rel 1};
       { Core.Match.Branch.binders = [];
         result_type = nat;
         pattern = Core.Pattern.binding_all (r "Leaf") 0;
         body = Core.Expr.Let
           {binder = x "z"; binder_type = nat;
             value = Core.Expr.Apply {callee = Core.Expr.Global k; arguments = [Core.Expr.fresh_rel 1]};
               body = Core.Expr.fresh_rel 1; occurrence = Core.Occurrence.fresh ()} } |]
  in
  let rest =
    Core.Expr.Let {binder = tmp 2;
                   binder_type = nat;
                   value = Core.Expr.Apply {callee = Core.Expr.Global h;
                                            arguments = [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 2]};
                   body = Core.Expr.fresh_rel 1;
                   occurrence = Core.Occurrence.fresh ()}
  in
  match Normalize.into_branches ~fresh ~rty:tree (tmp 1, nat, occ) branches rest with
  | Some [| {Core.Match.Branch.result_type = rty0;
             body = b0; _}; {Core.Match.Branch.result_type = rty1; body = b1; _} |] ->
    check "each branch is of the type of what follows" (rty0 = tree && rty1 = tree);
    ( match b0 with
    | Core.Expr.Let {binder = id;
                     binder_type = ty;
                     value = Core.Expr.Bound_variable {index = 1; _};
                     body = Core.Expr.Let
                       {binder = t2;
                         value = Core.Expr.Apply
                           {arguments =
                             [Core.Expr.Bound_variable {index = 1; _}; Core.Expr.Bound_variable {index = 3; _}]; _}; _};
                     occurrence = o} ->
      check "the first branch keeps the let" (id = tmp 1 && ty = nat && Core.Occurrence.equal o occ);
      check "the first branch keeps what follows" (t2 = tmp 2)
    | _ -> check "what follows is read past a branch's binders" false );
    ( match b1 with
    | Core.Expr.Let {binder = z;
                     value = Core.Expr.Apply {arguments = [Core.Expr.Bound_variable {index = 1; _}]; _};
                     body = Core.Expr.Let {binder = id;
                                           value = Core.Expr.Bound_variable {index = 1; _};
                                           body = Core.Expr.Let
                                             {binder = t2;
                                               value = Core.Expr.Apply
                                                 {arguments =
                                                   [Core.Expr.Bound_variable {index = 1; _};
                                                     Core.Expr.Bound_variable {index = 3; _}]; _};
                                                                 body = Core.Expr.Bound_variable {index = 1; _}; _};
                                           occurrence = o; _}; _} ->
      check "the branch's own let stays outermost" (z = x "z");
      check "a later branch binds a temporary of its own"
        (id <> tmp 1 && match id with Core.Binder_name.Generated v -> Core_util.is_temporary_id v | _ -> false);
      check "a copy binds temporaries of its own" (t2 <> tmp 2);
      check "a later branch's let is an occurrence of its own" (not (Core.Occurrence.equal o occ))
    | _ -> check "what follows is read past a branch's own lets" false );
    check "no occurrence is in two branches" (not (shared [b0; b1]))
  | _ -> check "what follows is copied into every branch" false

(* The budget: what the copies add, the size of what follows once per branch
   past the first. *)
let () =
  let rec sized n = if n <= 1 then Core.Expr.fresh_rel 1 else Core.Expr.Apply {callee = Core.Expr.Global h;
                                                                               arguments = [sized (n - 2)]} in
  let branch = {Core.Match.Branch.binders = [];
                result_type = nat;
                pattern = Core.Pattern.Wildcard;
                body = Core.Expr.Erased_value Core.Erasure_reason.Type_argument} in
  let at n arity =
    Normalize.into_branches ~fresh ~rty:nat (tmp 1, nat, Core.Occurrence.fresh ())
      (Array.make arity branch) (sized n) in
  check "a size whose copies fit the budget is copied" (Option.has_some (at 15 3));
  check "one more node per copy is refused" (not (Option.has_some (at 17 3)));
  check "a single branch copies nothing, whatever follows" (Option.has_some (at 1001 1));
  check "a long rest into two branches is refused" (not (Option.has_some (at 33 2)))
