(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* The phase-indexed Core facade and what freezing checks. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "core: %s\n" name;
    exit 1 )

let r s = GlobRef.VarRef (Id.of_string s)
let mp s = ModPath.MPfile (DirPath.make [Id.of_string s])
let term name body ty =
  (Label.make name, Core.Module.Structure_item.Declaration (Core.Decl.Value {entity = r name; body; type_ = ty}))
let frozen sel = Core_phase.freeze (Core_phase.optimize Fun.id (Core_phase.extracted [(mp "M", sel)]))

let refused sel =
  match frozen sel with
  | _ -> false
  | exception e -> CErrors.is_anomaly e

let () =
  Unix.putenv "CRANE_CHECK_IR" "1";
  let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []} in
  let lam = Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous;
                              parameter_type = nat;
                              body = Core.Expr.fresh_rel 1} in
  let fine = [term "f" lam (Core.Type.Arrow {parameter = nat; result = nat})] in
  check "a well-formed program freezes" (not (refused fine));
  check "a local group selecting a missing member cannot be made"
    (match Core.Recursion.Group.of_arrays ~selected:2 [|(Id.of_string "go", nat)|] [|lam|]
      (Core.Occurrence.fresh ()) with
     | _ -> false
     | exception Invalid_argument _ -> true);
  check "an empty local group cannot be made"
    (match Core.Recursion.Group.make ~selected:0 [||] (Core.Occurrence.fresh ()) with
     | _ -> false
     | exception Invalid_argument _ -> true);
  check "a declaration made twice is refused" (refused (fine @ fine));
  let read = Core.Expr.fresh_rel 1 in
  let f = Core.Expr.Global (Core.Global_use.monomorphic (r "f")) in
  check "two reads of their own freeze"
    (not
      (refused
        [term "d"
          (Core.Expr.Lambda
            {parameter = Core.Binder_name.Anonymous; parameter_type = nat;
              body = Core.Expr.Apply {callee = f; arguments = [Core.Expr.fresh_rel 1; Core.Expr.fresh_rel 1]}})
                (Core.Type.Arrow {parameter = nat; result = nat})]));
  check "one read at two terms is refused"
    (refused
      [term "e"
        (Core.Expr.Lambda
          {parameter = Core.Binder_name.Anonymous; parameter_type = nat;
            body = Core.Expr.Apply {callee = f; arguments = [read; read]}})
              (Core.Type.Arrow {parameter = nat; result = nat})]);
  check "one use in two definitions is refused" (refused [term "a" f nat; term "b" f nat]);
  let use_at scheme ty =
    Core.Expr.Global
      (Core.Global_use.polymorphic (r "g")
         (Scheme.Instantiation.make scheme (fun _ ->
              {Scheme.solution = Scheme.Type ty; source = Scheme.Not_written} ) ) )
  in
  check "a use at its callee's scheme freezes"
    (not (refused [term "u" (use_at (Scheme.Id.fresh (r "g") ~arity:1) nat) nat]));
  check "a use instantiated at another declaration's scheme is refused"
    (refused [term "v" (use_at (Scheme.Id.fresh (r "h") ~arity:1) nat) nat]);
  Table.add_type (r "p")
    (Core.Type.Arrow
      {parameter = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1};
        result = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}});
  let use_of_p scheme =
    Core.Expr.Global
      (Core.Global_use.polymorphic (r "p")
         (Scheme.Instantiation.make scheme (fun _ ->
              {Scheme.solution = Scheme.Type nat; source = Scheme.Not_written} ) ) )
  in
  check "a use at the scheme its callee is referenced at freezes"
    (not (refused [term "x" (use_of_p (Option.get (Core_util.reference_scheme (r "p")))) nat]));
  check "a use at a look-alike of its callee's scheme is refused"
    (refused [term "y" (use_of_p (Scheme.Id.fresh (r "p") ~arity:1)) nat]);
  check "a use holding a metavariable in its instantiation is refused"
    (refused [term "w" (use_at (Scheme.Id.fresh (r "g") ~arity:1) (Core.Type.Meta (Core.Extracted.Meta.fresh 3))) nat]);
  let shared = Core.Type.Meta (Core.Extracted.Meta.fresh 1) in
  let solved = Core.Type.Meta (Core.Extracted.Meta.solved 2 nat) in
  let open_term =
    term "k"
      (Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous; parameter_type = shared; body = Core.Expr.fresh_rel 1})
        (Core.Type.Arrow {parameter = shared; result = solved}) in
  let zonked = frozen [open_term] in
  check "each unsolved metavariable becomes one open annotation"
    (Core_phase.open_annotations zonked = 1);
  ( match Core_phase.structure zonked with
  | [(_,
        [(_,
            Core.Module.Structure_item.Declaration
              (Core.Decl.Value
                {body = Core.Expr.Lambda {parameter_type = Core.Type.Open o; _};
                  type_ = Core.Type.Arrow {parameter = Core.Type.Open o'; result = t}; _}))])] ->
    check "the annotations sharing a cell share its open annotation" (Core.Open.equal o o');
    check "a solved metavariable is replaced by its solution" (t = nat)
  | _ -> check "freezing leaves no metavariable in the program" false );
  Core.Extracted.Meta.thaw ();
  let two = Core_phase.extracted [(mp "A", fine); (mp "B", [])] in
  let a, b = Core_phase.partition (ModPath.equal (mp "A")) two in
  check "partition splits by top-level module"
    (List.map fst (Core_phase.structure a) = [mp "A"] && List.map fst (Core_phase.structure b) = [mp "B"]);
  check "modules keep each module with its own program"
    (List.map fst (Core_phase.modules two) = [mp "A"; mp "B"])

(* Normalizing the frozen program checks that the result is a fixed point of
   the pass, and leaves the metavariable supply where the pass left it. *)
let () =
  let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []} in
  let fine =
    [term "n"
      (Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous; parameter_type = nat; body = Core.Expr.fresh_rel 1})
        (Core.Type.Arrow {parameter = nat; result = nat})] in
  let normalizes pass =
    match Core_phase.normalize pass (frozen fine) with
    | _ -> true
    | exception e when CErrors.is_anomaly e -> false
  in
  let coerce (p : Core_phase.normalizing) =
    { p with
      structure =
        Modutil.map_struct_decls
          (function
            | Core.Decl.Value {entity = r; body = b; type_ = t} ->
              Core.Decl.Value {entity = r;
                               body = Core.Expr.Coerce
                                 {source_type = t; target_type = t; value = b; occurrence = Core.Occurrence.fresh ()};
                               type_ = t}
            | d -> d )
          p.structure }
  in
  let decide_once (p : Core_phase.normalizing) =
    if Splices.decided p.splices (r "n") then p else {p with splices = Splices.decide (r "n") p.splices}
  in
  let decide_anew (p : Core_phase.normalizing) =
    {p with splices = Splices.decide ~entered:(Core.Occurrence.fresh ()) (r "n") p.splices} in
  check "a pass its result is a fixed point of normalizes" (normalizes Fun.id);
  check "a pass that would rewrite its own result is refused" (not (normalizes coerce));
  check "a pass that decides once what it splices normalizes" (normalizes decide_once);
  check "a pass that would splice its own result otherwise is refused" (not (normalizes decide_anew));
  check "the splices decided are the program's"
    (Splices.decided (Core_phase.splices (Core_phase.normalize decide_once (frozen fine))) (r "n"));
  let minting s = ignore (Core_util.new_meta ()); s in
  let before = Core_util.new_meta () in
  ignore (Core_phase.normalize minting (frozen fine));
  ( match (before, Core_util.new_meta ()) with
  | Core.Type.Open o, Core.Type.Open o' ->
    check "checking a normal form makes no number" (Core.Open.id o' = Core.Open.id o + 2)
  | _ -> check "a frozen program makes open annotations" false );
  Core.Extracted.Meta.thaw ()

(* After freezing, nothing solves a metavariable. *)
let () =
  let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []} in
  let m = Core.Extracted.Meta.fresh 7 and m' = Core.Extracted.Meta.fresh 8 in
  Core.Extracted.Meta.freeze ();
  check "a solve of the frozen program is refused"
    (match Core.Extracted.Meta.solve m nat with () -> false | exception e -> CErrors.is_anomaly e);
  check "a refused solve writes nothing" (m.contents = None);
  Core.Extracted.Meta.thaw ();
  Core.Extracted.Meta.solve m' nat;
  check "a thawed program solves freely" (m'.contents = Some nat)

(* A slot fills an open annotation without writing it: one met twice is
   filled once, and the fill is carried to the terms that mention it. *)
let () =
  let nat =
    Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []}
      and bool = Core.Type.Global_app {head = r "bool"; type_arguments = []; index_arguments = []} in
  let pair a b = Core.Type.Global_app {head = r "pair"; type_arguments = [a; b]; index_arguments = []} in
  let o = Core.Open.fresh 15 and other = Core.Open.fresh 15 in
  let fills = ref [] in
  let refined =
    Type_util.refine_erased ~fills ~writable:(fun _ -> true) (pair (Core.Type.Open o) (Core.Type.Open o))
      (pair nat bool)
  in
  check "a hole met twice is filled once" (refined = pair nat nat);
  check "the fill is reported" (List.length !fills = 1);
  let body = Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous;
                               parameter_type = Core.Type.Open o;
                               body = Core.Expr.fresh_rel 1} in
  check "a term mentioning the hole is generated with it filled"
    (Type_util.fill_holes !fills body = Core.Expr.Lambda
      {parameter = Core.Binder_name.Anonymous; parameter_type = nat; body = Core.Expr.fresh_rel 1});
  check "another hole of the same number is not filled"
    (Type_util.fill_holes !fills
      (Core.Expr.Lambda
        {parameter = Core.Binder_name.Anonymous; parameter_type = Core.Type.Open other; body = Core.Expr.fresh_rel 1}) =
          Core.Expr.Lambda
            {parameter = Core.Binder_name.Anonymous; parameter_type = Core.Type.Open other;
              body = Core.Expr.fresh_rel 1})

(* A local definition's open types are minted before freezing, rigid: each
   recursive group's from 1, a let-bound lambda's, its groups' included,
   past the variables of the declaration it is in. *)
let () =
  let nat = Core.Type.Global_app {head = r "nat"; type_arguments = []; index_arguments = []} in
  let list t = Core.Type.Global_app {head = r "list"; type_arguments = [t]; index_arguments = []} in
  let go = Id.of_string "go" in
  let group m =
    Core.Expr.Fixpoint
      (Core.Recursion.Group.singleton go (Core.Type.Arrow {parameter = list (Core.Type.Meta m); result = nat})
        (Core.Expr.Lambda
          {parameter = Core.Binder_name.Anonymous; parameter_type = list (Core.Type.Meta m);
            body = Core.Expr.fresh_rel 1}) (Core.Occurrence.fresh ()))
  in
  let a =
    Core.Extracted.Meta.fresh 11 and b = Core.Extracted.Meta.fresh 12 and c = Core.Extracted.Meta.fresh 13
      and d = Core.Extracted.Meta.fresh 14 in
  let body =
    Core.Expr.Let {binder = Core.Binder_name.Source go;
                   binder_type = nat;
                   value = group a;
                   body = Core.Expr.Let
                     {binder = Core.Binder_name.Anonymous;
                       binder_type = Core.Type.Arrow {parameter = Core.Type.Meta d; result = nat};
                         value = Core.Expr.Lambda
                           {parameter = Core.Binder_name.Anonymous; parameter_type = Core.Type.Meta d; body = group c};
                             body = Core.Expr.Apply {callee = group b; arguments = [Core.Expr.fresh_rel 1]};
                               occurrence = Core.Occurrence.fresh ()};
                   occurrence = Core.Occurrence.fresh ()}
  in
  Local_types.structure
    [(mp "M",
        [term "f" body
          (Core.Type.Arrow
            {parameter = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}; result = nat})])];
  check "a let-bound group's open type is its first rigid variable"
    (a.contents = Some (Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = 1}));
  check "each group numbers its own from 1"
    (b.contents = Some (Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = 1}));
  check "a let-bound lambda's are numbered past the declaration's"
    (d.contents = Some (Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = 2}));
  check "a group inside a let-bound lambda is the lambda's"
    (c.contents = Some (Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = 3}))
