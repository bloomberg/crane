(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Entity identities, and the check that emission generates what the plan
   accounts for. *)

open Crane_plugin
open Minicpp

let check name cond =
  if not cond then (
    Printf.eprintf "generated_program: %s\n" name;
    exit 1 )

let r s = Names.GlobRef.VarRef (Names.Id.of_string s)

let raises_anomaly f =
  match f () with
  | () -> false
  | exception e -> CErrors.is_anomaly e

let raises_user_error f =
  match f () with
  | () -> false
  | exception CErrors.UserError _ -> true

let () =
  Unix.putenv "CRANE_CHECK_IR" "1";
  let helper =
    Lifted.make ~origin:None ~binder:(Names.Id.of_string "go") (Let (Miniml.Occurrence.fresh ()))
  in
  let helper_decl =
    Dfun
      (mk_dfun ~ret:Tvoid (Lifted.ref_of helper)
         (Ddef ([], [Sreturn (Some (CPPglob (r "callee", [], None)))])))
  in
  let h =
    match Generated_program.helper helper_decl with
    | Some h -> h
    | None -> check "a lifted helper is recognised" false; assert false
  in
  check "a helper lifted outside any declaration has no owner"
    (Generated_entity_id.owner h.helper_id = None);
  check "a helper is keyed by itself"
    (match Generated_entity_id.role h.helper_id with Lifted_helper h -> Lifted.equal h helper);
  check "an ordinary declaration is not a helper"
    (Generated_program.helper (Dfun (mk_dfun ~ret:Tvoid (r "f") (Ddef ([], []))))
     = None);
  check "dependencies are the globals named"
    (Entity_id.Set.mem (Entity_id.of_ref (r "callee"))
       (Generated_program.dependencies [helper_decl]));
  let entity name helpers =
    { Generated_program.entity_id = Entity_id.of_ref (r name); decls = []; helpers }
  in
  check "nothing is generated while planning"
    (raises_anomaly (fun () -> ignore (Generated_program.record (entity "a" []))));
  let declares r' = List.exists (Names.GlobRef.UserOrd.equal r') [r "a"; r "owner"] in
  let check_plan () = Generated_program.check_against_plan ~declares in
  Common.end_planning ();
  ignore (Generated_program.record (entity "a" [h]));
  Generated_program.record_lifted_ahead [helper_decl];
  check "emitting what the unit declares passes" (not (raises_anomaly check_plan));
  check "the files took something generated ahead of nothing"
    (raises_anomaly Generated_program.check_against_ahead);
  Generated_program.record_ahead (entity "a" [h]);
  check "the files took what was generated ahead of them"
    (not (raises_anomaly Generated_program.check_against_ahead));
  ignore (Generated_program.record (entity "b" []));
  check "an entity the unit does not declare is refused" (raises_anomaly check_plan);
  State.reset State.Unit;
  let owned =
    Lifted.make ~origin:(Some (r "stray")) ~binder:(Names.Id.of_string "go")
      (Let (Miniml.Occurrence.fresh ()))
  in
  let owned_decl = Dfun (mk_dfun ~ret:Tvoid (Lifted.ref_of owned) (Ddef ([], []))) in
  Generated_program.record_lifted_ahead [owned_decl];
  check "a helper lifted out of nothing the unit declares or emits is refused"
    (raises_anomaly check_plan);
  State.reset State.Unit;
  let again = Dfun (mk_dfun ~ret:Tvoid (Lifted.ref_of owned) (Ddef ([], []))) in
  Generated_program.record_lifted_ahead [owned_decl; owned_decl];
  check "a helper handed on to another generation is one helper"
    (not (raises_user_error (fun () -> Generated_program.record_lifted_ahead [owned_decl])));
  check "a helper two generations lifted is refused"
    (raises_user_error (fun () -> Generated_program.record_lifted_ahead [again]))
