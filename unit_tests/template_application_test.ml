(* The legal-prefix planner over generated heads: every result is a prefix
   of the head, kind-correct, written by identity, never longer than the
   head, and it covers every parameter a value or a phantom requires unless
   a parameter nothing can stand in for comes first. *)

open Crane_plugin
open Callable_abi

let check name cond =
  if not cond then (
    Printf.eprintf "template_application: %s\n" name;
    exit 1 )

let callee = Names.GlobRef.VarRef (Names.Id.of_string "f")
let ty name = Minicpp.Tid_external (name, [])

let () =
  Random.init 20261013;
  for _ = 1 to 500 do
    let arity = Random.int 5 in
    let scheme = Scheme.Id.fresh callee ~arity in
    let vars = Scheme.Var.all scheme in
    (* A head: dictionaries, the variables in a shuffled order with random
       kinds, some deduced callables, some defaults. *)
    let shuffled =
      List.map snd
        (List.sort compare (List.map (fun v -> (Random.bits (), v)) vars))
    in
    let entries =
      List.init (Random.int 2) (fun k ->
          (Minicpp.TTtypename, Common.tc_instance_id k) )
      @ List.concat_map
          (fun v ->
            let name = Minicpp.tvar_id (Scheme.Var.ordinal v) in
            let kind =
              match Random.int 4 with
              | 0 -> Minicpp.TTtemplate 1
              | 1 -> Minicpp.TTtypename_default Minicpp.Tvoid
              | _ -> Minicpp.TTtypename
            in
            (kind, name)
            :: ( if Random.int 4 = 0 then
                   [(Minicpp.TTfun ([], Minicpp.Tvoid), Common.fun_tparam_id (Scheme.Var.ordinal v))]
                 else [] ) )
          shuffled
    in
    let abi =
      of_head ~phantom_prefix:(Random.int 2) ~callee ~scheme:(Some scheme) entries
    in
    let value_of v = if Random.bool () then Some (ty ("V" ^ string_of_int (Scheme.Var.ordinal v))) else None in
    let values = List.map (fun v -> (v, value_of v)) vars in
    let app =
      Template_application.plan abi
        ~instance:(fun k -> Some (ty ("D" ^ string_of_int k)))
        ~scheme:(fun v -> Option.flatten (List.assoc_opt v values))
    in
    let args = Template_application.to_list app in
    let head = template_head abi in
    check "valid" (Template_application.validate abi app = []);
    check "no longer than the head" (List.length args <= List.length head);
    (* Written by identity: an argument at a variable's parameter is that
       variable's value, or the parameter's filler. *)
    List.iteri
      (fun k a ->
        let p = List.nth head k in
        match p.origin with
        | From_scheme v -> (
          match Option.flatten (List.assoc_opt v values) with
          | Some t ->
            check "a value lands at its own variable"
              (a = t || a = Minicpp.Ttyctor t)
          | None ->
            check "a missing value is filled only as the plan allows"
              ( match p.write with
              | Defaulted d | Phantom d -> a = d
              | Writable | Deduce_only -> false ) )
        | From_callable _ -> check "a deduced callable is never written" false
        | From_instance _ | Derived _ -> () )
      args
  done
