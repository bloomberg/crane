(* Freezing a use's metavariables into an instantiation, and reading a
   callee's type at it. *)

open Crane_plugin
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "instantiation: %s\n" name;
    exit 1 )

let owner = Names.GlobRef.VarRef (Names.Id.of_string "f")
let nat = Tglob (Names.GlobRef.VarRef (Names.Id.of_string "nat"), [], [])
let list t = Tglob (Names.GlobRef.VarRef (Names.Id.of_string "list"), [t], [])
let meta id = function None -> Tmeta (Meta.fresh id) | Some t -> Tmeta (Meta.solved id t)

let rec gen_type depth metas =
  match Random.int (if depth = 0 then 3 else 5) with
  | 0 -> nat
  | 1 -> List.nth metas (Random.int (List.length metas))
  | 2 -> Tvar (Schematic, 1 + Random.int 3)
  | 3 -> list (gen_type (depth - 1) metas)
  | _ -> Tarr (gen_type (depth - 1) metas, gen_type (depth - 1) metas)

let () =
  Random.init 20261013;
  let earlier = Mlutil.freeze_types [meta 0 None] in
  for _ = 1 to 200 do
    let open_metas = List.init 3 (fun i -> meta (100 + i) None) in
    let solved = [meta 200 (Some nat); meta 201 (Some (list (List.hd open_metas)))] in
    let metas = open_metas @ solved in
    let arity = 1 + Random.int 4 in
    let tys = List.init arity (fun _ -> gen_type 3 metas) in
    let frozen = Mlutil.freeze_types tys in
    check "one type per slot" (List.length frozen = arity);
    check "no metavariable survives" (not (List.exists Mlutil.type_has_meta frozen));
    let rec holes = function
      | Thole h -> [h]
      | Tarr (a, b) -> holes a @ holes b
      | Tglob (_, l, _) -> List.concat_map holes l
      | _ -> []
    in
    check "fresh against earlier holes"
      (List.for_all
         (fun h -> not (List.mem h (List.concat_map holes frozen)))
         (List.concat_map holes earlier));
    (* One metavariable is one hole wherever it occurs. *)
    let same = Mlutil.freeze_types [List.hd open_metas; list (List.hd open_metas)] in
    ( match same with
    | [Thole a; Tglob (_, [Thole b], _)] -> check "a shared meta is one hole" (a = b)
    | _ -> check "a lone open meta freezes to a hole" false );
    let id = Scheme.Id.fresh owner ~arity in
    let inst =
      Scheme.Instantiation.make id (fun v ->
          { Scheme.solution = Scheme.Type (List.nth frozen (Scheme.Var.ordinal v - 1));
            source = Scheme.Not_written } )
    in
    check "slots stay owned"
      (Scheme.Instantiation.for_all
         (fun v _ -> Scheme.Id.equal (Scheme.Var.owner v) id) inst);
    let body = Tarr (Tvar (Schematic, 1), Tvar (Schematic, arity)) in
    let p = Mlutil.Partial.instantiate inst body in
    let filled = Mlutil.Partial.resolve (fun _ -> Some nat) p in
    check "only a resolver closes a hole"
      (Mlutil.Partial.holes p = [] || Mlutil.Partial.close p = None);
    check "a resolved type is closed" (Mlutil.Partial.close filled <> None)
  done
