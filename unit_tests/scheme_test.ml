(* The scheme identities and the instantiation indexed by them. *)

open Crane_plugin
open Scheme

let check name cond =
  if not cond then (
    Printf.eprintf "scheme: %s\n" name;
    exit 1 )

let owner = Names.GlobRef.VarRef (Names.Id.of_string "f")

let raises f =
  try
    ignore (f ());
    false
  with Invalid_argument _ -> true

let () =
  Random.init 20261013;
  for _ = 1 to 200 do
    let arity = Random.int 6 in
    let id = Id.fresh owner ~arity in
    let other = Id.fresh owner ~arity in
    check "fresh schemes differ" (not (Id.equal id other));
    check "one variable per ordinal"
      (List.map Var.ordinal (Var.all id) = List.init arity succ);
    check "of_tvar is in range"
      (List.for_all
         (fun i -> Option.has_some (Var.of_tvar id i) = (1 <= i && i <= arity))
         (List.init (arity + 3) (fun i -> i - 1)));
    let written = List.filter (fun _ -> Random.bool ()) (Var.all id) in
    let inst =
      Instantiation.make id (fun v ->
          if List.exists (Var.equal v) written then
            { solution = Type (Var.ordinal v);
              source =
                Written
                  { binder = Binder.of_position (Var.ordinal v);
                    observed = Some (Var.ordinal v) } }
          else {solution = Type 0; source = Not_written} )
    in
    check "one slot per variable"
      (Instantiation.fold (fun _ _ n -> n + 1) inst 0 = arity);
    check "slots stay owned"
      (Instantiation.for_all (fun v _ -> Id.equal (Var.owner v) id) inst);
    let mapped = Instantiation.map (fun t -> t * 2) inst in
    check "map keeps the scheme" (Id.equal (Instantiation.scheme mapped) id);
    check "map keeps the evidence"
      (List.for_all
         (fun v ->
           match
             ((Instantiation.slot inst v).source, (Instantiation.slot mapped v).source)
           with
           | Not_written, Not_written -> true
           | Written a, Written b ->
             Binder.equal a.binder b.binder
             && Option.map (fun t -> t * 2) a.observed = b.observed
           | _ -> false )
         (Var.all id));
    List.iter
      (fun v ->
        check "a foreign variable is refused"
          (raises (fun () -> Instantiation.slot inst v)) )
      (Var.all other)
  done
