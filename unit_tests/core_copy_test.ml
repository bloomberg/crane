(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* A copy of a Core term is new terms: occurrences, holes and open
   annotations of its own, and the callee's variables solved as the use
   solves them. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "core_copy: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let x s = Id (Id.of_string s)
let nat = Tglob (r "nat", [], [])
let bool = Tglob (r "bool", [], [])
let a = Tvar (Schematic, 1)

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

let shares e e' =
  Occurrence.shared (fun visit -> List.iter visit (occurrences e); List.iter visit (occurrences e')) <> []

let slot solution = {Scheme.solution; source = Scheme.Not_written}
let use_at scheme f = Global_use.polymorphic (r "g") (Scheme.Instantiation.make scheme f)

let rec holes = function
  | Thole h -> [h]
  | Tarr (s, t) -> holes s @ holes t
  | Tglob (_, ts, _) | Tapp (_, ts) -> List.concat_map holes ts
  | _ -> []

let use_holes = function
  | MLglob u ->
    let hs = ref [] in
    Global_use.iter_types (fun t -> hs := !hs @ holes t) u;
    !hs
  | _ -> []

let () =
  let scheme = Scheme.Id.fresh (r "g") ~arity:1 in
  let self = MLglob (Global_use.identity (r "g") scheme) in
  let fix = MLfix (0, [|(Id.of_string "go", Tarr (a, a))|], [|MLlam (x "y", a, MLapp (fresh_rel 2, [fresh_rel 1]))|], false, Occurrence.fresh ()) in
  let body =
    MLlam (x "n", a, MLletin (x "m", a, fresh_rel 1, MLapp (fix, [MLapp (self, [fresh_rel 1])]), Occurrence.fresh ()))
  in
  let copied = Core_copy.copy body in
  check "a copy is the term it copies" (copied = body);
  check "a copy shares no occurrence with its original" (not (shares body copied));
  check "the copied term itself has every occurrence once" (not (shares copied (MLdummy Ktype)));
  check "a term sharing an occurrence is told apart" (shares body body);
  (* Holes: renamed apart from the original's, the same new one wherever
     the original shares one. *)
  let h = Thole (Scheme.Hole.fresh ()) in
  let two = MLapp (MLglob (use_at scheme (fun _ -> slot (Scheme.Type h))), [MLglob (use_at scheme (fun _ -> slot (Scheme.Type h)))]) in
  ( match Core_copy.copy two with
  | MLapp (f, [g]) ->
    let hf = use_holes f and hg = use_holes g in
    check "a copied hole is a new hole" (hf <> holes h);
    check "a hole shared in the original is shared in the copy" (hf = hg && List.length hf = 1)
  | _ -> check "a copy keeps the shape" false );
  (* Open annotations: likewise, in the frozen program copies are made in. *)
  let o = Topen (Open.fresh 7) in
  Meta.freeze ();
  let opened = Core_copy.copy (MLlam (x "p", o, MLlam (x "q", o, fresh_rel 1))) in
  Meta.thaw ();
  ( match opened with
  | MLlam (_, Topen p, MLlam (_, Topen q, _)) ->
    check "a copied open annotation is a new one" (not (Open.equal p (match o with Topen o -> o | _ -> assert false)));
    check "an open annotation shared in the original is shared in the copy" (Open.equal p q)
  | _ -> check "a copy keeps the lambdas" false );
  (* Instantiation: the use's solutions replace the callee's variables, in
     annotations and in a rigid self-reference's slots. *)
  let at_nat = use_at scheme (fun _ -> slot (Scheme.Type nat)) in
  let inst = Core_copy.instance at_nat body in
  ( match inst with
  | MLlam (_, t, MLletin (_, t', _, MLapp (MLfix (_, [|(_, ft)|], _, _, _), [MLapp (MLglob u, _)]), _)) ->
    check "a parameter's variable is solved" (t = nat && t' = nat);
    check "a local fixpoint's signature is solved" (ft = Tarr (nat, nat));
    ( match Global_use.instantiation u with
    | Some i ->
      check "a rigid self-reference is solved where the use solves its variable"
        (List.for_all
           (fun v -> (Scheme.Instantiation.slot i v).solution = Scheme.Type nat)
           (Scheme.Var.all scheme) )
    | None -> check "the self-reference stays polymorphic" false )
  | _ -> check "an instance keeps the shape" false );
  check "an instance shares no occurrence with its original" (not (shares body inst));
  let rigid = Core_copy.instance (Global_use.identity (r "g") scheme) body in
  ( match rigid with
  | MLlam (_, _, MLletin (_, _, _, MLapp (_, [MLapp (MLglob u, _)]), _)) ->
    check "a rigid use leaves the self-reference rigid"
      (match Global_use.instantiation u with
       | Some i -> Scheme.Instantiation.for_all (fun _ s -> s.Scheme.solution = Scheme.Identity) i
       | None -> false )
  | _ -> check "a rigid instance keeps the shape" false );
  check "a rigid instance is the body itself" (rigid = body)

(* A call: the callee's body under a let per parameter passed a term to
   evaluate, outermost first, each argument lifted past the lets before it;
   a parameter passed a variable or an erased value reads it. *)
let () =
  let ty = Tarr (nat, Tarr (bool, Tarr (nat, nat))) in
  let h = Global_use.monomorphic (r "h") and k = Global_use.monomorphic (r "k") in
  let body =
    MLlam
      ( x "p", nat,
        MLlam (x "q", bool, MLlam (x "s", nat, MLapp (MLglob h, [fresh_rel 3; fresh_rel 2; fresh_rel 1; fresh_rel 1]))) )
  in
  let use = Global_use.monomorphic (r "f") in
  let a1 = MLapp (MLglob k, [fresh_rel 3]) and a2 = fresh_rel 1 and a3 = MLapp (MLglob k, [fresh_rel 2]) in
  ( match Core_copy.call ~ty use body [a1; a2; a3] with
  | Some
      (MLletin
         (p, tp, a1', MLletin (s, ts, a3', MLapp (_, [MLrel (2, _); MLrel (3, o); MLrel (1, _); MLrel (1, _)]), _), _)) ->
    check "the parameters passed a term are bound outermost first" (p = x "p" && s = x "s");
    check "each binder takes its parameter's type" (tp = nat && ts = nat);
    check "the first argument stands where the call did" (a1' == a1);
    check "a later argument is lifted past the lets before it"
      (match a3' with MLapp (_, [MLrel (3, _)]) -> true | _ -> false);
    check "a parameter passed a variable reads it as a read of its own"
      (match a2 with MLrel (_, o2) -> not (Occurrence.equal o o2) | _ -> false)
  | _ -> check "a call is lets around the body" false );
  ( match Core_copy.call ~ty:(Tarr (nat, nat)) use (MLlam (x "p", nat, fresh_rel 1)) [MLdummy Ktype] with
  | Some (MLdummy Ktype) -> ()
  | _ -> check "a parameter passed an erased value is that value" false );
  check "a call with too few arguments is not made" (Core_copy.call ~ty use body [a1] = None);
  check "a call with too many arguments is not made" (Core_copy.call ~ty use body [a1; a2; a3; a2] = None);
  check "a body binding fewer parameters than its type is not called"
    (Core_copy.call ~ty use (MLlam (x "p", nat, MLdummy Ktype)) [a1; a2; a3] = None)
