(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Planning inductive kinds is a function of the structure: alignment reads
   the functor body's copy, and demotion sees alignment's decisions without
   either writing a table. *)

open Crane_plugin
open Names

let check name cond =
  if not cond then (
    Printf.eprintf "target_plan: %s\n" name;
    exit 1 )

let dir s = DirPath.make [Id.of_string s]
let mp s = ModPath.MPfile (dir s)
let lbl = Label.make
let kn m l = MutInd.make2 (mp m) (lbl l)
let field =
  {Core.Record.Field.projection = Some (GlobRef.VarRef (Id.of_string "op"));
   type_ = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}}

let ind kind =
  { Core.Inductive.kind = kind;
    parameter_count = 0;
    packets =
      [| { Core.Inductive.Packet.name = Id.of_string "cl";
           constructor_names = [||];
           logical = false;
           signature = [];
           type_variables = [];
           constructor_argument_types = [||];
           constructor_argument_names = [||] } |];
    equivalence = Core.Inductive.Equivalence.Distinct }

let () =
  let body_kn = kn "F" "Cl" and app_kn = kn "FN" "Cl" in
  let app_ind = ind (Core.Inductive.Kind.Record [field]) in
  let functor_elem =
    ( lbl "F",
      Core.Module.Structure_item.Module
        { Core.Module.expr =
            Core.Module.Expr.Functor {parameter = MBId.make (dir "Top") (Id.of_string "X"); parameter_type = Core.Module.Type.Path (mp "S"); body = Core.Module.Expr.Structure {path = mp "F"; items = [(lbl "Cl", Core.Module.Structure_item.Declaration (Core.Decl.Inductive {entity = body_kn; definition = ind (Core.Inductive.Kind.Type_class [field])}))]}};
          type_ = Core.Module.Type.Path (mp "S") } )
  in
  let app_elem =
    ( lbl "FN",
      Core.Module.Structure_item.Module
        { Core.Module.expr = Core.Module.Expr.Apply {functor_ = Core.Module.Expr.Path (mp "F"); argument = Core.Module.Expr.Path (mp "N")};
          type_ = Core.Module.Type.Signature {path = mp "FN"; items = [(lbl "Cl", Core.Module.Signature_item.Declaration (Core.Signature.Declaration.Inductive {entity = app_kn; definition = app_ind}))]} } )
  in
  let struc = [(mp "Top", [functor_elem; app_elem])] in
  let facts = Program_facts.analyze struc in
  let plan = Target_plan.plan facts struc in
  check "the application takes the body's kind"
    (Option.equal Target_plan.kind_equal (Target_plan.kind_of plan app_kn) (Some (Core.Inductive.Kind.Type_class [field])));
  check "the body is not re-decided" (Target_plan.kind_of plan body_kn = None);
  check "planning writes nothing into the structure"
    (match app_ind.kind with Core.Inductive.Kind.Record _ -> true | _ -> false);
  check "planning is deterministic" (Target_plan.equal plan (Target_plan.plan facts struc));
  (* A class the structure handles as data is demoted, seen through the
     alignment decided before it: nothing installed it anywhere. *)
  let use =
    ( lbl "use",
      Core.Module.Structure_item.Declaration
        (Core.Decl.Value {entity = GlobRef.VarRef (Id.of_string "use"); body = Core.Expr.Erased_value Core.Erasure_reason.Proof; type_ = Core.Type.Global_app {head = GlobRef.IndRef (kn "L" "list", 0); type_arguments = [Core.Type.Global_app {head = GlobRef.IndRef (app_kn, 0); type_arguments = []; index_arguments = []}]; index_arguments = []}}) )
  in
  let struc = [(mp "Top", [functor_elem; app_elem; use])] in
  let plan = Target_plan.plan facts struc in
  check "a class used as data ends a struct"
    (Option.equal Target_plan.kind_equal (Target_plan.kind_of plan app_kn) (Some (Core.Inductive.Kind.Record [field])));
  check "both decisions are kept, in order"
    (List.map (fun (d : Target_plan.kind_decision) -> d.reason) plan.inductive_kinds
     = [Target_plan.Functor_alignment; Target_plan.Used_as_value])
