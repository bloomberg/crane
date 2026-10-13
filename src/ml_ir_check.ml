(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml

let violation r what =
  Probe.violation "global use"
    Pp.(str "the use of " ++ GlobRef.print r ++ str " " ++ str what)

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

let rec holes acc = function
  | Thole h -> h :: acc
  | Tarr (a, b) -> holes (holes acc a) b
  | Tglob (_, l, _) | Tapp (_, l) -> List.fold_left holes acc l
  | Tmeta {contents = Some t} -> holes acc t
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
  if List.exists Mlutil.type_has_meta tys then
    violation r "holds a metavariable in its frozen instantiation";
  List.iter
    (fun h ->
      match Hashtbl.find_opt owners h with
      | None -> Hashtbl.add owners h inst
      | Some inst' when inst' = inst -> ()
      | Some inst' ->
        let show i = String.concat ", " (List.map Mlutil.debug_ml_type (solution_types i)) in
        violation r
          (Printf.sprintf
             "shares hole _%d with a different use (%s against %s); a copied use was not freshened"
             h (show inst) (show inst') ) )
    (List.fold_left holes [] tys)

let check_global_use owners use =
  Option.iter (check_instantiation owners use.callee) (Global_use.instantiation use)

let structure struc =
  if Probe.checking () then
    let owners = Hashtbl.create 64 in
    ignore
      (Modutil.struct_ast_search
         (fun a ->
           ( match a with
           | MLglob use -> check_global_use owners use
           | _ -> () );
           false )
         struc )
