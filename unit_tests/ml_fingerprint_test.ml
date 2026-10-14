(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* What the structure fingerprint distinguishes and what it does not. *)

open Crane_plugin
open Miniml

let check name cond =
  if not cond then (
    Printf.eprintf "ml_fingerprint: %s\n" name;
    exit 1 )

let r s = Names.GlobRef.VarRef (Names.Id.of_string s)
let fp d = Ml_fingerprint.decl d
let same a b = Ml_fingerprint.equal (fp a) (fp b)
let term ty body = Dterm (r "f", body, ty)
let id_ty = Tarr (Tvar (Schematic, 1), Tvar (Schematic, 1))
let lam = MLlam (Id (Names.Id.of_string "x"), Tvar (Schematic, 1), MLrel 1)

let () =
  let d = term id_ty lam in
  check "deterministic" (same d (term id_ty lam));
  check "body matters" (not (same d (term id_ty (MLlam (Dummy, Tvar (Schematic, 1), MLrel 1)))));
  check "type matters" (not (same d (term (Tarr (Tvar (Schematic, 1), Tstring)) lam)));
  check "rigidity matters" (not (same d (term (Tarr (Tvar (Rigid, 1), Tvar (Schematic, 1))) lam)));
  check "name matters" (not (same d (Dterm (r "g", lam, id_ty))));
  let solved = Tmeta (Meta.solved 7 (Tvar (Schematic, 1))) in
  check "a solved meta reads as its solution" (same d (term (Tarr (solved, solved)) lam));
  let hole_pair a b = term (Tarr (Thole a, Thole b)) lam in
  check "hole numbering is canonical" (same (hole_pair 3 3) (hole_pair 41 41));
  check "hole sharing matters" (not (same (hole_pair 3 3) (hole_pair 3 4)));
  let meta i = Tmeta (Meta.fresh i) in
  check "unsolved metas are numbered canonically"
    (same (term (Tarr (meta 1, meta 2)) lam) (term (Tarr (meta 8, meta 9)) lam));
  check "a meta is not a hole" (not (same (term (Tarr (meta 1, meta 1)) lam) (hole_pair 1 1)));
  check "fix and cofix differ"
    (not
       (same
          (term id_ty (MLfix (0, [|(Names.Id.of_string "f", id_ty)|], [|lam|], false)))
          (term id_ty (MLfix (0, [|(Names.Id.of_string "f", id_ty)|], [|lam|], true)))));
  check "list boundaries are encoded"
    (not
       (same
          (term id_ty (MLapp (MLrel 1, [MLtuple [MLrel 2]; MLrel 3])))
          (term id_ty (MLapp (MLrel 1, [MLtuple [MLrel 2; MLrel 3]])))));
  let s1 = [(Names.ModPath.MPfile (Names.DirPath.make [Names.Id.of_string "M"]),
             [(Names.Label.make "f", SEdecl d)])] in
  check "structure deterministic"
    (Ml_fingerprint.equal (Ml_fingerprint.structure s1) (Ml_fingerprint.structure s1));
  check "hex is a digest" (String.length (Ml_fingerprint.to_hex (Ml_fingerprint.structure s1)) = 32)
