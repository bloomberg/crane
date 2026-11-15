(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

let violation r what =
  Probe.violation "global use"
    Pp.(str "the use of " ++ GlobRef.print r ++ str " " ++ str what)

(* The types an instantiation holds: each slot's solution, and the type
   observed at each written argument. *)
let solution_types inst =
  Scheme.Instantiation.fold
    (fun _ {Scheme.solution; source} acc ->
      let acc =
        match solution with
        | Scheme.Type t -> t :: acc
        | Scheme.Identity -> acc
      in
      match source with
      | Scheme.Written {observed = Some t; _} -> t :: acc
      | _ -> acc )
    inst []

(* The holes ({!Core.Type.Hole}) occurring in a type, through solved
   metavariables. *)
let rec holes acc = function
  | Core.Type.Hole h -> h :: acc
  | Core.Type.Arrow {parameter = a; result = b} -> holes (holes acc a) b
  | Core.Type.Global_app {type_arguments = l; _} | Core.Type.Variable_app {arguments = l; _} ->
    List.fold_left holes acc l
  | Core.Type.Meta {contents = Some t} -> holes acc t
  | _ -> acc

(* [owners] maps each hole met so far to the instantiation holding it: a
   hole belongs to one use, and only a copy of that whole use may hold it
   again. *)
let check_instantiation owners r inst =
  let owner = Scheme.Id.owner (Scheme.Instantiation.scheme inst) in
  if not (GlobRef.UserOrd.equal owner r) then
    violation r
      ( "is instantiated at the scheme of "
      ^ Pp.string_of_ppcmds (GlobRef.print owner) );
  let tys = solution_types inst in
  if List.exists Core_util.type_has_meta tys then
    violation r "holds a metavariable in its frozen instantiation";
  List.iter
    (fun h ->
      match Hashtbl.find_opt owners h with
      | None -> Hashtbl.add owners h inst
      | Some inst' when inst' = inst -> ()
      | Some inst' ->
        let show i = String.concat ", " (List.map Core_util.debug_ml_type (solution_types i)) in
        violation r
          (Printf.sprintf
             "shares hole _%d with a different use (%s against %s); a copied use was not freshened"
             h (show inst) (show inst') ) )
    (List.fold_left holes [] tys)

let check_global_use owners (use : Core.Global_use.t) =
  Option.iter (check_instantiation owners use.callee) (Core.Global_use.instantiation use)

let structure struc =
  if Probe.checking () then
    let owners = Hashtbl.create 64 in
    ignore
      (Modutil.struct_ast_search
         (fun a ->
           ( match a with
           | Core.Expr.Global use -> check_global_use owners use
           | _ -> () );
           false )
         struc )
