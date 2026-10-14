(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Entity identities, and the check that emission generates what discovery
   did. *)

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

let () =
  Unix.putenv "CRANE_CHECK_IR" "1";
  let helper = Lifted.make ~origin:None ~binder:(Names.Id.of_string "go") in
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
  check "a helper is keyed by its binder"
    (Generated_entity_id.role h.helper_id = Lifted_helper (Names.Id.of_string "go"));
  check "an ordinary declaration is not a helper"
    (Generated_program.helper (Dfun (mk_dfun ~ret:Tvoid (r "f") (Ddef ([], []))))
     = None);
  check "dependencies are the globals named"
    (Entity_id.Set.mem (Entity_id.of_ref (r "callee"))
       (Generated_program.dependencies [helper_decl]));
  let entity name helpers =
    { Generated_program.entity_id = Entity_id.of_ref (r name); decls = []; helpers }
  in
  Common.set_phase Common.Discover;
  ignore (Generated_program.record (entity "a" [h]));
  Common.set_phase (Common.Emit Common.Impl);
  ignore (Generated_program.record (entity "a" []));
  Common.set_phase (Common.Emit Common.Intf);
  Generated_program.record_helper h;
  check "emission matching discovery passes"
    (not (raises_anomaly Generated_program.check_emission_matches_discovery));
  check "the emitted program keeps what it recorded"
    (List.length (Generated_program.entities (Generated_program.emitted Common.Impl)) = 1);
  ignore (Generated_program.record (entity "b" []));
  check "an entity first generated during emission is refused"
    (raises_anomaly Generated_program.check_emission_matches_discovery)
