(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* What follows a bound match, copied into its branches: under each
   branch's binders and lets, a copy of its own past the first, and
   refused past the budget. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "normalize: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let x s = Id (Id.of_string s)
let tmp n = Tmp (Mlutil.temporary_id n)
let nat = Tglob (r "nat", [], [])
let tree = Tglob (r "tree", [], [])
let h = Global_use.monomorphic (r "h")
let k = Global_use.monomorphic (r "k")

let rec occurrences e =
  let here =
    match e with
    | MLrel (_, o) | MLletin (_, _, _, _, o) | MLfix (_, _, _, _, o) -> [o]
    | MLglob u -> [Global_use.occurrence u]
    | _ -> []
  in
  let below = ref [] in
  Mlutil.ast_iter (fun c -> below := !below @ occurrences c) e;
  here @ !below

let shared es = Occurrence.shared (fun visit -> List.iter (fun e -> List.iter visit (occurrences e)) es) <> []

let fresh =
  let n = ref 10 in
  fun () ->
    incr n;
    tmp !n

(* [let _tmp1 : nat := match _ with Node l => l | Leaf => let z := k y in z
   in let _tmp2 := h _tmp1 y in _tmp2], [y] the variable around. *)
let () =
  let occ = Occurrence.fresh () in
  let branches =
    [| ([(x "l", tree)], nat, Pusual (r "Node"), fresh_rel 1);
       ([], nat, Pusual (r "Leaf"), MLletin (x "z", nat, MLapp (MLglob k, [fresh_rel 1]), fresh_rel 1, Occurrence.fresh ())) |]
  in
  let rest =
    MLletin (tmp 2, nat, MLapp (MLglob h, [fresh_rel 1; fresh_rel 2]), fresh_rel 1, Occurrence.fresh ())
  in
  match Normalize.into_branches ~fresh ~rty:tree (tmp 1, nat, occ) branches rest with
  | Some [| (_, rty0, _, b0); (_, rty1, _, b1) |] ->
    check "each branch is of the type of what follows" (rty0 = tree && rty1 = tree);
    ( match b0 with
    | MLletin (id, ty, MLrel (1, _), MLletin (t2, _, MLapp (_, [MLrel (1, _); MLrel (3, _)]), _, _), o) ->
      check "the first branch keeps the let" (id = tmp 1 && ty = nat && Occurrence.equal o occ);
      check "the first branch keeps what follows" (t2 = tmp 2)
    | _ -> check "what follows is read past a branch's binders" false );
    ( match b1 with
    | MLletin
        ( z, _, MLapp (_, [MLrel (1, _)]),
          MLletin (id, _, MLrel (1, _), MLletin (t2, _, MLapp (_, [MLrel (1, _); MLrel (3, _)]), MLrel (1, _), _), o),
          _ ) ->
      check "the branch's own let stays outermost" (z = x "z");
      check "a later branch binds a temporary of its own" (id <> tmp 1 && match id with Tmp v -> Mlutil.is_temporary_id v | _ -> false);
      check "a copy binds temporaries of its own" (t2 <> tmp 2);
      check "a later branch's let is an occurrence of its own" (not (Occurrence.equal o occ))
    | _ -> check "what follows is read past a branch's own lets" false );
    check "no occurrence is in two branches" (not (shared [b0; b1]))
  | _ -> check "what follows is copied into every branch" false

(* The budget: what the copies add, the size of what follows once per branch
   past the first. *)
let () =
  let rec sized n = if n <= 1 then fresh_rel 1 else MLapp (MLglob h, [sized (n - 2)]) in
  let branch = ([], nat, Pwild, MLdummy Ktype) in
  let at n arity = Normalize.into_branches ~fresh ~rty:nat (tmp 1, nat, Occurrence.fresh ()) (Array.make arity branch) (sized n) in
  check "a size whose copies fit the budget is copied" (Option.has_some (at 15 3));
  check "one more node per copy is refused" (not (Option.has_some (at 17 3)));
  check "a single branch copies nothing, whatever follows" (Option.has_some (at 1001 1));
  check "a long rest into two branches is refused" (not (Option.has_some (at 33 2)))
