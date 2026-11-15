(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* What the structure fingerprint distinguishes and what it does not. *)

open Crane_plugin

let check name cond =
  if not cond then (
    Printf.eprintf "ml_fingerprint: %s\n" name;
    exit 1 )

let r s = Names.GlobRef.VarRef (Names.Id.of_string s)
let fp d = Ml_fingerprint.decl d
let same a b = Ml_fingerprint.equal (fp a) (fp b)
let term ty body = Core.Decl.Value {entity = r "f"; body; type_ = ty}
let id_ty = Core.Type.Arrow {parameter = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1};
                             result = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}}
let lam = Core.Expr.Lambda {parameter = Core.Binder_name.Source (Names.Id.of_string "x"); parameter_type = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}; body = Core.Expr.fresh_rel 1}

let () =
  let d = term id_ty lam in
  check "deterministic" (same d (term id_ty lam));
  check "body matters" (not (same d (term id_ty (Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous; parameter_type = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}; body = Core.Expr.fresh_rel 1}))));
  check "type matters" (not (same d (term (Core.Type.Arrow {parameter = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}; result = Core.Type.String}) lam)));
  check "rigidity matters" (not (same d (term (Core.Type.Arrow {parameter = Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = 1}; result = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = 1}}) lam)));
  check "name matters" (not (same d (Core.Decl.Value {entity = r "g"; body = lam; type_ = id_ty})));
  let solved = Core.Type.Meta (Core.Meta.solved 7 (Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                                       variable = 1})) in
  check "a solved meta reads as its solution" (same d (term (Core.Type.Arrow {parameter = solved; result = solved}) lam));
  let hole_pair a b = term (Core.Type.Arrow {parameter = Core.Type.Hole a; result = Core.Type.Hole b}) lam in
  check "hole numbering is canonical" (same (hole_pair 3 3) (hole_pair 41 41));
  check "hole sharing matters" (not (same (hole_pair 3 3) (hole_pair 3 4)));
  let meta i = Core.Type.Meta (Core.Meta.fresh i) in
  check "unsolved metas are numbered canonically"
    (same (term (Core.Type.Arrow {parameter = meta 1;
                                  result = meta 2}) lam) (term (Core.Type.Arrow {parameter = meta 8;
                                                                                 result = meta 9}) lam));
  check "a meta is not a hole" (not (same (term (Core.Type.Arrow {parameter = meta 1; result = meta 1}) lam) (hole_pair 1 1)));
  check "fix and cofix differ"
    (not
       (same
          (term id_ty (Core.Expr.Fixpoint {selected = 0; functions = [|(Names.Id.of_string "f", id_ty)|]; bodies = [|lam|]; occurrence = Core.Occurrence.fresh ()}))
          (term id_ty (Core.Expr.Cofixpoint {selected = 0; functions = [|(Names.Id.of_string "f", id_ty)|]; bodies = [|lam|]; occurrence = Core.Occurrence.fresh ()}))));
  check "list boundaries are encoded"
    (not
       (same
          (term id_ty (Core.Expr.Apply {callee = Core.Expr.fresh_rel 1;
                                        arguments = [Core.Expr.Tuple [Core.Expr.fresh_rel 2]; Core.Expr.fresh_rel 3]}))
          (term id_ty (Core.Expr.Apply {callee = Core.Expr.fresh_rel 1;
                                        arguments = [Core.Expr.Tuple [Core.Expr.fresh_rel 2; Core.Expr.fresh_rel 3]]}))));
  let s1 = [(Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "M"]),
             [(Names.Label.make "f", Core.Module.Structure_item.Declaration d)])] in
  check "structure deterministic"
    (Ml_fingerprint.equal (Ml_fingerprint.structure s1) (Ml_fingerprint.structure s1));
  check "hex is a digest" (String.length (Ml_fingerprint.to_hex (Ml_fingerprint.structure s1)) = 32)
