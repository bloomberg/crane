(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

type extracted
type optimized
type frozen

type 'phase program = { structure : ml_structure }

let extracted structure = { structure }
let optimize passes p = { structure = passes p.structure }
let structure p = p.structure

let partition keep p =
  let kept, rest = List.partition (fun (mp, _) -> keep mp) p.structure in
  ({ structure = kept }, { structure = rest })

let modules p = List.map (fun ((mp, _) as m) -> (mp, { structure = [m] })) p.structure

(** Every type annotation of the structure: declared types, the types bodies
    annotate, constructor argument types and type definitions. *)
let iter_types f p =
  let visit_body b = ignore (Mlutil.ast_map_types (fun t -> f t; t) b) in
  let visit_ind ind = Array.iter (fun pk -> Array.iter (List.iter f) pk.ip_types) ind.ind_packets in
  Modutil.struct_iter
    (function
      | Dind (_, ind) -> visit_ind ind
      | Dtype (_, _, t) -> f t
      | (Dterm _ | Dfix _) as d ->
        List.iter (fun fd -> f fd.fd_type; visit_body fd.fd_body) (Mlutil.term_defs d) )
    (function
      | Sind (_, ind) -> visit_ind ind
      | Stype (_, _, t) -> Option.iter f t
      | Sval (_, b, t) -> f t; visit_body b )
    (fun _ -> ())
    p.structure

let unsolved_metas p =
  let seen = Hashtbl.create 16 in
  let rec walk = function
    | Tmeta {contents = Some t; _} -> walk t
    | Tmeta {id; contents = None} -> Hashtbl.replace seen id ()
    | Tarr (a, b) -> walk a; walk b
    | Tglob (_, ts, _) | Tapp (_, ts) -> List.iter walk ts
    | Tvar _ | Thole _ | Tdummy _ | Tunknown | Taxiom | Tstring -> ()
  in
  iter_types walk p;
  Hashtbl.length seen

let fail what = CErrors.anomaly Pp.(str ("Crane: the frozen Core program " ^ what ^ "."))

(** Every recursive group is nonempty, and a local one selects a member it
    has. *)
let check_recursive_groups p =
  let rec check_body = function
    | MLfix (i, ids, funs, _) as e ->
      if Array.length ids <> Array.length funs || Array.length ids = 0 then
        fail "has a local recursive group whose names and bodies disagree";
      if i < 0 || i >= Array.length ids then fail "selects a recursive function its group lacks";
      Mlutil.ast_iter check_body e
    | e -> Mlutil.ast_iter check_body e
  in
  Modutil.struct_iter
    (function
      | Dfix [] -> fail "has an empty recursive group"
      | (Dterm _ | Dfix _) as d -> List.iter (fun fd -> check_body fd.fd_body) (Mlutil.term_defs d)
      | Dind _ | Dtype _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    p.structure

(** No reference is declared twice. *)
let check_declared_once p =
  let declared = ref Ref.User.Set.empty in
  let declare r =
    if Ref.User.Set.mem r !declared then
      fail ("declares " ^ Pp.string_of_ppcmds (Printer.pr_global r) ^ " twice");
    declared := Ref.User.Set.add r !declared
  in
  Modutil.struct_iter
    (function
      | Dind (kn, ind) -> Array.iteri (fun i _ -> declare (Names.GlobRef.IndRef (kn, i))) ind.ind_packets
      | Dtype (r, _, _) -> declare r
      | (Dterm _ | Dfix _) as d -> List.iter (fun fd -> declare fd.fd_ref) (Mlutil.term_defs d) )
    (fun _ -> ())
    (fun _ -> ())
    p.structure

let freeze p =
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    check_recursive_groups p;
    check_declared_once p
  end;
  if Pipeline_trace.enabled () then
    Pipeline_trace.event "freeze" (Printf.sprintf "unsolved metavariables: %d" (unsolved_metas p));
  { structure = p.structure }
