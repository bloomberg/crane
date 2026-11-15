(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)


type extracted
type optimized
type frozen
type normalized

type normalizing = { structure : Core.Program.t; splices : Splices.t }
type 'phase program = normalizing

let extracted structure = { structure; splices = Splices.empty }
let optimize passes p = { p with structure = passes p.structure }
let structure p = p.structure
let splices p = p.splices

let partition keep p =
  let kept, rest = List.partition (fun (mp, _) -> keep mp) p.structure in
  ({ p with structure = kept }, { p with structure = rest })

let modules p = List.map (fun ((mp, _) as m) -> (mp, { p with structure = [m] })) p.structure

(** [iter_types f p] calls [f] on every type annotation of the structure:
    declared types, the types bodies annotate, constructor argument types and
    type definitions. *)
let iter_types f p =
  let visit_body b = ignore (Mlutil.ast_map_types (fun t -> f t; t) b) in
  let visit_ind (ind : Core.Inductive.t) = Array.iter (fun (pk : Core.Inductive.Packet.t) -> Array.iter (List.iter f) pk.constructor_argument_types) ind.packets in
  Modutil.struct_iter
    (function
      | Core.Decl.Inductive {definition = ind; _} -> visit_ind ind
      | Core.Decl.Type_alias {body = t; _} -> f t
      | (Core.Decl.Value _ | Core.Decl.Recursive_group _) as d ->
        List.iter (fun (fd : Core.Recursion.Definition.t) -> f fd.type_; visit_body fd.body) (Mlutil.term_defs d) )
    (function
      | Core.Signature.Declaration.Inductive {definition = ind; _} -> visit_ind ind
      | Core.Signature.Declaration.Type {body = t; _} -> Option.iter f t
      | Core.Signature.Declaration.Value {body = b; type_ = t; _} -> f t; visit_body b )
    (fun _ -> ())
    p.structure

(* A metavariable is its cell: extraction numbers each declaration's afresh. *)
module Cells = Hashtbl.Make (struct
  type t = Core.Meta.t

  let equal = ( == )
  let hash (m : Core.Meta.t) = Hashtbl.hash m.id
end)

module Opens = Hashtbl.Make (Core.Open)

let open_annotations p =
  let seen = Opens.create 16 in
  let rec walk = function
    | Core.Type.Open o -> Opens.replace seen o ()
    | Core.Type.Arrow {parameter = a; result = b} -> walk a; walk b
    | Core.Type.Global_app {type_arguments = ts; _} | Core.Type.Variable_app {arguments = ts; _} -> List.iter walk ts
    | Core.Type.Variable _
    | Core.Type.Hole _
    | Core.Type.Meta _
    | Core.Type.Erased _
    | Core.Type.Unknown
    | Core.Type.Axiom
    | Core.Type.String -> ()
  in
  iter_types walk p;
  Opens.length seen

(* An anomaly: the program at [phase] breaks an invariant, [what] saying
   which. *)
let failure phase what =
  CErrors.anomaly Pp.(str ("Crane: the " ^ phase ^ " Core program " ^ what ^ "."))

let fail = failure "frozen"

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
    | Core.Type.Meta {contents = Some u} -> ty u
    | Core.Type.Meta ({contents = None} as m) -> (
      match Cells.find_opt opens m with
      | Some o -> Core.Type.Open o
      | None ->
        let o = Core.Open.fresh m.id in
        Cells.add opens m o;
        Core.Type.Open o )
    | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = ty a; result = ty b}
    | Core.Type.Global_app {head = r; type_arguments = ts; index_arguments = args} ->
      Core.Type.Global_app {head = r; type_arguments = List.map ty ts; index_arguments = List.map body args}
    | Core.Type.Variable_app {head = i; arguments = ts} -> Core.Type.Variable_app {head = i; arguments = List.map ty ts}
    | Core.Type.Variable _
    | Core.Type.Hole _
    | Core.Type.Open _
    | Core.Type.Erased _
    | Core.Type.Unknown
    | Core.Type.Axiom
    | Core.Type.String -> t
  and body e = Mlutil.ast_map_types ty e in
  let inductive (ind : Core.Inductive.t) =
    Array.iter (fun (pk : Core.Inductive.Packet.t) -> Array.iteri (fun i ts -> pk.constructor_argument_types.(i) <- List.map ty ts) pk.constructor_argument_types) ind.packets
  in
  let decl = function
    | Core.Decl.Value {entity = r; body = b; type_ = t} -> Core.Decl.Value {entity = r; body = body b; type_ = ty t}
    | Core.Decl.Recursive_group fds ->
      Core.Decl.Recursive_group (Core.Nonempty.map (fun (fd : Core.Recursion.Definition.t) -> {fd with Core.Recursion.Definition.body = body fd.body;
                                                                                               type_ = ty fd.type_}) fds)
    | Core.Decl.Type_alias {entity = r; parameters = vars; body = t} ->
      Core.Decl.Type_alias {entity = r; parameters = vars; body = ty t}
    | Core.Decl.Inductive {definition = ind; _} as d -> inductive ind; d
  in
  let spec = function
    | Core.Signature.Declaration.Inductive {definition = ind; _} as s -> inductive ind; s
    | Core.Signature.Declaration.Type {entity = r; parameters = vars; body = t} ->
      Core.Signature.Declaration.Type {entity = r; parameters = vars; body = Option.map ty t}
    | Core.Signature.Declaration.Value {entity = r; body = b; type_ = t} ->
      Core.Signature.Declaration.Value {entity = r; body = body b; type_ = ty t}
  in
  Table.map_types ty;
  { p with structure = Modutil.map_struct ~spec ~with_type:ty decl p.structure }

(** No metavariable, solved or not, is reachable from an annotation, nor
    from the type a global is registered at. *)
let check_zonked p =
  let rec walk = function
    | Core.Type.Meta _ -> fail "holds a metavariable"
    | Core.Type.Arrow {parameter = a; result = b} -> walk a; walk b
    | Core.Type.Global_app {type_arguments = ts; index_arguments = args; _} ->
      List.iter walk ts; List.iter (fun a -> ignore (Mlutil.ast_map_types (fun t -> walk t; t) a)) args
    | Core.Type.Variable_app {arguments = ts; _} -> List.iter walk ts
    | Core.Type.Variable _
    | Core.Type.Hole _
    | Core.Type.Open _
    | Core.Type.Erased _
    | Core.Type.Unknown
    | Core.Type.Axiom
    | Core.Type.String -> ()
  in
  iter_types walk p;
  Table.iter_types walk

(** Every local recursive group is nonempty and selects a member it has (a
    top-level group is nonempty by its type). *)
let check_recursive_groups p =
  let rec check_body = function
    | Core.Expr.Fixpoint {selected = i;
                          functions = ids;
                          bodies = funs; _} | Core.Expr.Cofixpoint {selected = i;
                                                                    functions = ids;
                                                                    bodies = funs; _} as e ->
      if Array.length ids <> Array.length funs || Array.length ids = 0 then
        fail "has a local recursive group whose names and bodies disagree";
      if i < 0 || i >= Array.length ids then fail "selects a recursive function its group lacks";
      Mlutil.ast_iter check_body e
    | e -> Mlutil.ast_iter check_body e
  in
  Modutil.struct_iter
    (function
      | (Core.Decl.Value _ | Core.Decl.Recursive_group _) as d ->
        List.iter (fun (fd : Core.Recursion.Definition.t) -> check_body fd.body) (Mlutil.term_defs d)
      | Core.Decl.Inductive _ | Core.Decl.Type_alias _ -> () )
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
      | Core.Decl.Inductive {entity = kn; definition = (ind : Core.Inductive.t)} ->
        Array.iteri (fun i _ -> declare (Names.GlobRef.IndRef (kn, i))) ind.packets
      | Core.Decl.Type_alias {entity = r; _} -> declare r
      | (Core.Decl.Value _ | Core.Decl.Recursive_group _) as d ->
        List.iter (fun (fd : Core.Recursion.Definition.t) -> declare fd.entity) (Mlutil.term_defs d) )
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
    | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
    | Core.Type.Meta {contents = Some t} -> open_meta t
    | Core.Type.Arrow {parameter = a; result = b} -> open_meta a || open_meta b
    | Core.Type.Global_app {type_arguments = ts; _} | Core.Type.Variable_app {arguments = ts; _} ->
      List.exists open_meta ts
    | Core.Type.Variable _
    | Core.Type.Hole _
    | Core.Type.Erased _
    | Core.Type.Unknown
    | Core.Type.Axiom
    | Core.Type.String -> false
  in
  let check_use use =
    let r = Core.Global_use.callee use in
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
      (Core.Global_use.instantiation use);
    if Core.Global_use.exists_type open_meta use then
      fail ("holds a metavariable in the instantiation of a use of " ^ name ())
  in
  let rec check_body = function
    | Core.Expr.Global use as e -> check_use use; Mlutil.ast_iter check_body e
    | e -> Mlutil.ast_iter check_body e
  in
  Modutil.struct_iter
    (function
      | (Core.Decl.Value _ | Core.Decl.Recursive_group _) as d ->
        List.iter (fun (fd : Core.Recursion.Definition.t) -> check_body fd.body) (Mlutil.term_defs d)
      | Core.Decl.Inductive _ | Core.Decl.Type_alias _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    p.structure

(** [f r what o] for every occurrence [o] the body of the definition [r]
    holds, [what] saying whose: a read's, a let's, a match's, a
    construction's, a coercion's, a fixpoint's or a global use's. *)
let iter_occurrences f p =
  Modutil.struct_iter
    (function
      | (Core.Decl.Value _ | Core.Decl.Recursive_group _) as d ->
        List.iter
          (fun (fd : Core.Recursion.Definition.t) ->
            let rec walk e =
              ( match e with
              | Core.Expr.Bound_variable {occurrence = o; _} -> f fd.entity "read" o
              | Core.Expr.Let {occurrence = o; _} -> f fd.entity "let" o
              | Core.Expr.Match {occurrence = o; _} -> f fd.entity "match" o
              | Core.Expr.Construct {occurrence = o; _} -> f fd.entity "construction" o
              | Core.Expr.Coerce {occurrence = o; _} | Core.Expr.Boxed_value {occurrence = o; _} | Core.Expr.Lambda_group_barrier {occurrence = o; _} -> f fd.entity "coercion" o
              | Core.Expr.Fixpoint {occurrence = o; _} | Core.Expr.Cofixpoint {occurrence = o; _} -> f fd.entity "local fixpoint" o
              | Core.Expr.Global use -> f fd.entity "use" (Core.Global_use.occurrence use)
              | _ -> () );
              Mlutil.ast_iter walk e
            in
            walk fd.body )
          (Mlutil.term_defs d)
      | Core.Decl.Inductive _ | Core.Decl.Type_alias _ -> () )
    (fun _ -> ())
    (fun _ -> ())
    p.structure

(** No two terms of the program are one occurrence: every consumer keyed on
    occurrences -- the recursion plan's calls, ControlIR's turns, the
    ownership plan's reads, the C++ call a Core call makes -- reads each as
    one place in one definition. *)
let check_occurrences phase p =
  match Core.Occurrence.shared (fun visit -> iter_occurrences (fun _ _ o -> visit o) p) with
  | [] -> ()
  | o :: _ ->
    let holders = ref [] in
    iter_occurrences
      (fun r what o' ->
        if Core.Occurrence.equal o o' then
          holders := (what ^ " in " ^ Table.kername_of_global r) :: !holders )
      p;
    failure phase ("holds one occurrence at several terms: " ^ String.concat ", " (List.rev !holders))

let freeze p =
  let p = zonk p in
  Core.Meta.freeze ();
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    check_recursive_groups p;
    check_declared_once p;
    check_instantiations p;
    check_zonked p;
    check_occurrences "frozen" p
  end;
  if Pipeline_trace.enabled () then
    Pipeline_trace.event "freeze" (Printf.sprintf "open annotations: %d" (open_annotations p));
  p

(** The top-level elements of [p] that normalizing [p] again would
    rewrite, and whether it would decide the partners it splices alike. *)
let not_normal pass p =
  let again = Mlutil.preserving_meta_supply (fun () -> pass p) in
  ( List.filter_map
      (fun ((l, fp), (_, fp')) -> if Ml_fingerprint.equal fp fp' then None else Some l)
      (List.combine (Ml_fingerprint.elements p.structure) (Ml_fingerprint.elements again.structure)),
    Splices.equal p.splices again.splices )

let normalize pass p =
  let p = pass p in
  if Sys.getenv_opt "CRANE_CHECK_IR" <> None then begin
    check_occurrences "normalized" p;
    match not_normal pass p with
    | [], true -> ()
    | l :: _, _ ->
      failure "normalized"
        ("is not in normal form: normalizing " ^ Names.Label.to_string l ^ " again rewrites it")
    | [], false -> failure "normalized" "is not in normal form: normalizing it again splices partners otherwise"
  end;
  p
