(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A finished declaration in both IRs.  See [finished_decl.mli]. *)

type t = {
  settled : Cpp_erasure.settled;
  ir : Cpp_ir.Resolved.Decl.t;
}

type view =
  | Template of t
  | Namespace of Minicpp.nspace_wrapper option * t list
  | Decl

let view {settled; ir} =
  let mismatch () = CErrors.anomaly (Pp.str "Crane: a finished declaration's two IRs differ in shape.") in
  match (Cpp_erasure.view settled, ir) with
  | Template (_, _, settled), Template (_, _, ir) -> Template {settled; ir}
  | Namespace (w, settled), Namespace (_, ir) ->
    if List.length settled <> List.length ir then mismatch ();
    Namespace (w, List.map2 (fun settled ir -> {settled; ir}) settled ir)
  | Decl _, (Template _ | Namespace _) | (Template _ | Namespace _), _ -> mismatch ()
  | Decl _, _ -> Decl
