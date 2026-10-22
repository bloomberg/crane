(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

type extracted
type optimized
type frozen
type normalized

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

(* A metavariable is its cell: extraction numbers each declaration's afresh. *)
module Cells = Hashtbl.Make (struct
  type t = ml_meta

  let equal = ( == )
  let hash (m : ml_meta) = Hashtbl.hash m.id
end)

module Opens = Hashtbl.Make (Open)

let open_annotations p =
  let seen = Opens.create 16 in
  let rec walk = function
    | Topen o -> Opens.replace seen o ()
    | Tarr (a, b) -> walk a; walk b
    | Tglob (_, ts, _) | Tapp (_, ts) -> List.iter walk ts
    | Tvar _ | Thole _ | Tmeta _ | Tdummy _ | Tunknown | Taxiom | Tstring -> ()
  in
  iter_types walk p;
  Opens.length seen

let fail what = CErrors.anomaly Pp.(str ("Crane: the frozen Core program " ^ what ^ "."))

(** [zonk p]: [p] with every metavariable gone from its annotations -- a
    solved one replaced by its solution, an unsolved one by an open
    annotation, the same one for every annotation that shared the cell -- and
    from the types its globals are registered at, which share cells with
    them.  A packet's constructor types are rewritten in place: the inductive
    is shared with the tables extraction registered it in. *)
let zonk p =
  let opens = Cells.create 64 in
  let rec ty t =
    match t with
    | Tmeta {contents = Some u} -> ty u
    | Tmeta ({contents = None} as m) -> (
      match Cells.find_opt opens m with
      | Some o -> Topen o
      | None ->
        let o = Open.fresh m.id in
        Cells.add opens m o;
        Topen o )
    | Tarr (a, b) -> Tarr (ty a, ty b)
    | Tglob (r, ts, args) -> Tglob (r, List.map ty ts, List.map body args)
    | Tapp (i, ts) -> Tapp (i, List.map ty ts)
    | Tvar _ | Thole _ | Topen _ | Tdummy _ | Tunknown | Taxiom | Tstring -> t
  and body e = Mlutil.ast_map_types ty e in
  let inductive ind =
    Array.iter (fun pk -> Array.iteri (fun i ts -> pk.ip_types.(i) <- List.map ty ts) pk.ip_types) ind.ind_packets
  in
  let decl = function
    | Dterm (r, b, t) -> Dterm (r, body b, ty t)
    | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = body fd.fd_body; fd_type = ty fd.fd_type}) fds)
    | Dtype (r, vars, t) -> Dtype (r, vars, ty t)
    | Dind (_, ind) as d -> inductive ind; d
  in
  let spec = function
    | Sind (_, ind) as s -> inductive ind; s
    | Stype (r, vars, t) -> Stype (r, vars, Option.map ty t)
    | Sval (r, b, t) -> Sval (r, body b, ty t)
  in
  Table.map_types ty;
  { structure = Modutil.map_struct ~spec ~with_type:ty decl p.structure }

(** No metavariable, solved or not, is reachable from an annotation, nor
    from the type a global is registered at. *)
let check_zonked p =
  let rec walk = function
    | Tmeta _ -> fail "holds a metavariable"
    | Tarr (a, b) -> walk a; walk b
    | Tglob (_, ts, args) -> List.iter walk ts; List.iter (fun a -> ignore (Mlutil.ast_map_types (fun t -> walk t; t) a)) args
    | Tapp (_, ts) -> List.iter walk ts
    | Tvar _ | Thole _ | Topen _ | Tdummy _ | Tunknown | Taxiom | Tstring -> ()
  in
  iter_types walk p;
  Table.iter_types walk

(** Every recursive group is nonempty, and a local one selects a member it
    has. *)
let check_recursive_groups p =
  let rec check_body = function
    | MLfix (i, ids, funs, _, _) as e ->
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

(** Every polymorphic use is instantiated at its callee's own scheme, the
    one {!Mlutil.reference_scheme} names, so that two readings of one
    callee's variables meet the same variables; and no instantiation holds a
    metavariable: extraction froze each into an immutable hole. *)
let check_instantiations p =
  (* Frozen, a metavariable an instantiation held is an open annotation. *)
  let rec open_meta = function
    | Tmeta {contents = None} | Topen _ -> true
    | Tmeta {contents = Some t} -> open_meta t
    | Tarr (a, b) -> open_meta a || open_meta b
    | Tglob (_, ts, _) | Tapp (_, ts) -> List.exists open_meta ts
    | Tvar _ | Thole _ | Tdummy _ | Tunknown | Taxiom | Tstring -> false
  in
  let check_use use =
    let r = Global_use.callee use in
    let name () = Pp.string_of_ppcmds (Printer.pr_global r) in
    Option.iter
      (fun inst ->
        let scheme = Scheme.Instantiation.scheme inst in
        if not (Names.GlobRef.UserOrd.equal (Scheme.Id.owner scheme) r) then
          fail ("instantiates a use of " ^ name () ^ " at another declaration's scheme");
        match Mlutil.reference_scheme r with
        | Some own when Scheme.Id.equal own scheme -> ()
        | Some own when Scheme.Id.arity own <> Scheme.Id.arity scheme ->
          fail ("instantiates a use of " ^ name () ^ " at a scheme of another arity")
        | Some _ -> fail ("instantiates a use of " ^ name () ^ " at a scheme other than its own")
        | None -> () )
      (Global_use.instantiation use);
    if Global_use.exists_type open_meta use then
      fail ("holds a metavariable in the instantiation of a use of " ^ name ())
  in
  let rec check_body = function
    | MLglob use as e -> check_use use; Mlutil.ast_iter check_body e
    | e -> Mlutil.ast_iter check_body e
  in
  Modutil.struct_iter
    (function
      | (Dterm _ | Dfix _) as d -> List.iter (fun fd -> check_body fd.fd_body) (Mlutil.term_defs d)
      | Dind _ | Dtype _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    p.structure

let freeze p =
  let p = zonk p in
  Meta.freeze ();
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    check_recursive_groups p;
    check_declared_once p;
    check_instantiations p;
    check_zonked p
  end;
  if Pipeline_trace.enabled () then
    Pipeline_trace.event "freeze" (Printf.sprintf "open annotations: %d" (open_annotations p));
  { structure = p.structure }

let normalize pass p = { structure = pass p.structure }
