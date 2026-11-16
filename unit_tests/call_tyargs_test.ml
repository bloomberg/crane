(* A call's reading of its callee's scheme variables: it starts as exactly
   the arguments the use wrote, a resolution fills only holes and never with
   an erased placeholder, and the list view spells every hole before the
   last known variable as the placeholder the erasure filters drop.  The
   view is keyed by the callee's own variables. *)

open Crane_plugin

let check name cond =
  if not cond then (
    Printf.eprintf "call_tyargs: %s\n" name;
    exit 1 )

let callee = Names.GlobRef.VarRef (Names.Id.of_string "f")
let nat =
  Core.Type.Global_app
    {head = Names.GlobRef.VarRef (Names.Id.of_string "nat"); type_arguments = []; index_arguments = []}
let bool =
  Core.Type.Global_app
    {head = Names.GlobRef.VarRef (Names.Id.of_string "bool"); type_arguments = []; index_arguments = []}
let binder = Core.Scheme.Binder.of_position 0

let source () =
  match Random.int 3 with
  | 0 -> Core.Scheme.Written {binder; observed = Some nat}
  | 1 -> Core.Scheme.Written {binder; observed = None}
  | _ -> Core.Scheme.Not_written

let () =
  Random.init 20261013;
  for _ = 1 to 500 do
    let arity = 1 + Random.int 5 in
    let scheme = Core.Scheme.Id.fresh callee ~arity in
    let sources = List.map (fun v -> (v, source ())) (Core.Scheme.Var.all scheme) in
    let use =
      Core.Global_use.polymorphic callee
        (Core.Scheme.Instantiation.make scheme (fun v ->
             { Core.Scheme.solution = Core.Scheme.Type (Core.Type.Hole (Core.Scheme.Hole.fresh ()));
               source = List.assoc v sources } ) )
    in
    let t = Call_tyargs.of_use use in
    check "starts as what the use wrote"
      (Base.Core_util.Var_types.equal (Call_tyargs.by_variable t) (Base.Core_util.written_type_args use));
    check "a variable is a hole unless the use wrote a readable type"
      (List.for_all
         (fun (v, s) ->
           Call_tyargs.is_hole t v
           = match s with Core.Scheme.Written {observed = Some _; _} -> false | _ -> true )
         sources );
    check "a variable is unwritten exactly where the use wrote nothing"
      (List.for_all
         (fun (v, s) -> Call_tyargs.is_unwritten t v = (s = Core.Scheme.Not_written))
         sources );
    let spoken = List.map fst (Base.Core_util.Var_types.bindings (Call_tyargs.by_variable t)) in
    let within v = List.exists (Core.Scheme.Var.equal v) spoken in
    check "interior holes and the variables beyond partition by the extent"
      (List.for_all within (Call_tyargs.interior_holes t)
       && List.for_all (fun v -> not (within v)) (Call_tyargs.beyond_extent t)
       && List.for_all
            (fun v -> within v || List.exists (Core.Scheme.Var.equal v) (Call_tyargs.beyond_extent t))
            (Call_tyargs.vars t));
    let asked = List.filter (fun _ -> Random.bool ()) (Call_tyargs.vars t) in
    let answer v =
      match Random.int 3 with
      | 0 -> None
      | 1 -> Some (Core.Type.Erased Core.Erasure_reason.Type_argument)
      | _ -> Some (if Core.Scheme.Var.ordinal v mod 2 = 0 then bool else nat)
    in
    let answers = List.map (fun v -> (v, answer v)) (Call_tyargs.vars t) in
    let answer v = List.assoc v answers in
    let r = Call_tyargs.resolve Call_tyargs.Argument_types answer asked t in
    let after = Call_tyargs.by_variable r in
    let before = Call_tyargs.by_variable t in
    List.iter
      (fun (j, ty) ->
        match Base.Core_util.Var_types.find before j with
        | Some (Core.Type.Erased _) | None -> ()
        | Some b -> check "a known variable keeps its type" (b = ty) )
      (Base.Core_util.Var_types.bindings after);
    check "no resolution is an erased placeholder"
      (List.for_all
         (fun v ->
           Call_tyargs.is_hole r v
           || (not (Call_tyargs.is_hole t v))
           || match Base.Core_util.Var_types.find after v with
              | Some (Core.Type.Erased _) | None -> false
              | Some _ -> true )
         (Call_tyargs.vars t) );
    check "only an asked hole with an answer is resolved"
      (List.for_all
         (fun v ->
           Call_tyargs.is_hole r v
           = ( Call_tyargs.is_hole t v
               && not
                    ( List.exists (Core.Scheme.Var.equal v) asked
                    && match answer v with Some (Core.Type.Erased _) | None -> false | Some _ -> true ) ) )
         (Call_tyargs.vars t) );
    check "a resolved variable is no longer unwritten"
      (List.for_all
         (fun v -> Call_tyargs.is_hole r v || not (Call_tyargs.is_unwritten r v))
         (Call_tyargs.vars t) );
    let all = Call_tyargs.resolve_all Call_tyargs.Argument_types answer asked t in
    check "all or nothing"
      ( Call_tyargs.holes all = Call_tyargs.holes t
      || List.for_all
           (fun v -> not (Call_tyargs.is_hole all v))
           asked );
    check "the evidence is recorded"
      (Call_tyargs.resolved_from Call_tyargs.Argument_types r
       = (Call_tyargs.holes r <> Call_tyargs.holes t));
    let tys = Call_tyargs.by_variable r in
    check "a variable is found where the callee's type spells it"
      (List.for_all
         (fun v ->
           Base.Core_util.Var_types.find tys v = Base.Core_util.Var_types.find_tvar tys (Core.Scheme.Var.ordinal v) )
         (Call_tyargs.vars r) );
    let other = List.hd (Core.Scheme.Var.all (Core.Scheme.Id.fresh callee ~arity)) in
    check "another scheme's variable is never read as this one's"
      ( Base.Core_util.Var_types.is_empty tys
      || match Base.Core_util.Var_types.find tys other with
         | exception Invalid_argument _ -> true
         | _ -> false )
  done
