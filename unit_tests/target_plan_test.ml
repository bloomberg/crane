(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Planning inductive kinds is a function of the structure: alignment reads
   the functor body's copy, and demotion sees alignment's decisions without
   either writing a table. *)

open Crane_plugin
open Names
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "target_plan: %s\n" name;
    exit 1 )

let dir s = DirPath.make [Id.of_string s]
let mp s = ModPath.MPfile (dir s)
let lbl = Label.make
let kn m l = MutInd.make2 (mp m) (lbl l)
let field = (Some (GlobRef.VarRef (Id.of_string "op")), Tvar (Schematic, 1))

let ind kind =
  { ind_kind = kind;
    ind_nparams = 0;
    ind_packets =
      [| { ip_typename = Id.of_string "cl";
           ip_consnames = [||];
           ip_logical = false;
           ip_sign = [];
           ip_vars = [];
           ip_types = [||];
           ip_consarg_names = [||] } |];
    ind_equiv = NoEquiv }

let () =
  let body_kn = kn "F" "Cl" and app_kn = kn "FN" "Cl" in
  let app_ind = ind (Record [field]) in
  let functor_elem =
    ( lbl "F",
      SEmodule
        { ml_mod_expr =
            MEfunctor
              ( MBId.make (dir "Top") (Id.of_string "X"),
                MTident (mp "S"),
                MEstruct (mp "F", [(lbl "Cl", SEdecl (Dind (body_kn, ind (TypeClass [field]))))]) );
          ml_mod_type = MTident (mp "S") } )
  in
  let app_elem =
    ( lbl "FN",
      SEmodule
        { ml_mod_expr = MEapply (MEident (mp "F"), MEident (mp "N"));
          ml_mod_type = MTsig (mp "FN", [(lbl "Cl", Spec (Sind (app_kn, app_ind)))]) } )
  in
  let struc = [(mp "Top", [functor_elem; app_elem])] in
  let facts = Program_facts.analyze struc in
  let plan = Target_plan.plan facts struc in
  check "the application takes the body's kind"
    (Option.equal Target_plan.kind_equal (Target_plan.kind_of plan app_kn) (Some (TypeClass [field])));
  check "the body is not re-decided" (Target_plan.kind_of plan body_kn = None);
  check "planning writes nothing into the structure"
    (match app_ind.ind_kind with Record _ -> true | _ -> false);
  check "planning is deterministic" (Target_plan.equal plan (Target_plan.plan facts struc));
  (* A class the structure handles as data is demoted, seen through the
     alignment decided before it: nothing installed it anywhere. *)
  let use =
    ( lbl "use",
      SEdecl
        (Dterm
           ( GlobRef.VarRef (Id.of_string "use"),
             MLdummy Kprop,
             Tglob (GlobRef.IndRef (kn "L" "list", 0), [Tglob (GlobRef.IndRef (app_kn, 0), [], [])], []) )) )
  in
  let struc = [(mp "Top", [functor_elem; app_elem; use])] in
  let plan = Target_plan.plan facts struc in
  check "a class used as data ends a struct"
    (Option.equal Target_plan.kind_equal (Target_plan.kind_of plan app_kn) (Some (Record [field])));
  check "both decisions are kept, in order"
    (List.map (fun (d : Target_plan.kind_decision) -> d.reason) plan.inductive_kinds
     = [Target_plan.Functor_alignment; Target_plan.Used_as_value])
