(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

let violation r what =
  Base.Probe.violation "global use"
    Pp.(str "the use of " ++ GlobRef.print r ++ str " " ++ str what)

(* The types an instantiation holds: each slot's solution, and the type
   observed at each written argument. *)
let solution_types inst =
  Core.Scheme.Instantiation.fold
    (fun _ {Core.Scheme.solution; source} acc ->
      let acc =
        match solution with
        | Core.Scheme.Type t -> t :: acc
        | Core.Scheme.Identity -> acc
      in
      match source with
      | Core.Scheme.Written {observed = Some t; _} -> t :: acc
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
  let owner = Core.Scheme.Id.owner (Core.Scheme.Instantiation.scheme inst) in
  if not (GlobRef.UserOrd.equal owner r) then
    violation r
      ( "is instantiated at the scheme of "
      ^ Pp.string_of_ppcmds (GlobRef.print owner) );
  let tys = solution_types inst in
  if List.exists Base.Core_util.type_has_meta tys then
    violation r "holds a metavariable in its frozen instantiation";
  List.iter
    (fun h ->
      match Hashtbl.find_opt owners h with
      | None -> Hashtbl.add owners h inst
      | Some inst' when inst' = inst -> ()
      | Some inst' ->
        let show i = String.concat ", " (List.map Base.Core_util.debug_core_type (solution_types i)) in
        violation r
          (Printf.sprintf
             "shares hole _%d with a different use (%s against %s); a copied use was not freshened"
             h (show inst) (show inst') ) )
    (List.fold_left holes [] tys)

let check_global_use owners (use : _ Core.Global_use.at) =
  Option.iter (check_instantiation owners use.callee) (Core.Global_use.instantiation use)

(* The inductive a type names, through solved metavariables; [None] for any
   other type, which says too little to compare. *)
let inductive_head t =
  match Base.Core_util.core_resolve t with
  | Core.Type.Global_app {head = GlobRef.IndRef _ as r; _} -> Some r
  | _ -> None

(* The inductive a branch body evidently returns: a construction's, a
   numeral's, or what the branches of a match it ends in say they return.
   A coercion, a call or a variable says nothing checked here. *)
let rec returned_heads = function
  | Core.Expr.Let {body; _} -> returned_heads body
  | Core.Expr.Construct {result_type = t; _} -> (match inductive_head t with Some r -> [r] | None -> [])
  | Core.Expr.Numeral {inductive = r; _} -> [r]
  | Core.Expr.Match {branches; _} ->
    List.filter_map (fun (b : _ Core.Match.Branch.at) -> inductive_head b.result_type) (Array.to_list branches)
  | _ -> []

(* Every branch of a match returns what its result type says.  The custom
   match's immediately invoked lambda is annotated with that type, so a
   simplification that moves a branch's value and leaves the type it had
   before converts the value silently: [151] returned through [-> bool]
   is [1]. *)
let check_branch_types (branches : _ Core.Match.Branch.at array) =
  Array.iter
    (fun (b : _ Core.Match.Branch.at) ->
      match inductive_head b.result_type with
      | None -> ()
      | Some r ->
        List.iter
          (fun r' ->
            if not (GlobRef.CanOrd.equal r r') then
              Base.Probe.violation "match result type"
                Pp.(str "a branch typed " ++ Printer.pr_global r ++ str " returns a value of "
                    ++ Printer.pr_global r' ++ str "; a simplification moved it and kept its old type") )
          (returned_heads b.body) )
    branches

let structure struc =
  if Base.Probe.checking () then
    let owners = Hashtbl.create 64 in
    ignore
      (Modutil.struct_ast_search
         (fun a ->
           ( match a with
           | Core.Expr.Global use -> check_global_use owners use
           | Core.Expr.Match {branches; _} -> check_branch_types branches
           | _ -> () );
           false )
         struc )
