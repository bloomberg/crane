(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

type t = {
  used_customs : Ref.User.Set.t;
  higher_order_projections : Ref.User.Set.t;
}

type program = {
  throwing_values : Names.GlobRef.t list;
  parameter_ownership : (Names.GlobRef.t * bool list) list;
}

let analyze_program frozen =
  let struc = Core.structure frozen in
  { throwing_values = Structure_analysis.throwing_values struc;
    parameter_ownership = Ownership.summarize struc }

let used_customs struc =
  let used = ref Ref.User.Set.empty in
  let add r = used := Ref.User.Set.add r !used in
  let mark r =
    if Table.is_custom r then begin
      add r;
      (* Imports registered on an inductive are due when a constructor of it
         is used. *)
      match r with Names.GlobRef.ConstructRef (ip, _) -> add (Names.GlobRef.IndRef ip) | _ -> ()
    end
  in
  Modutil.struct_iter
    (Modutil.decl_iter_references mark mark mark)
    (Modutil.spec_iter_references mark mark mark)
    (fun _ -> ())
    struc;
  !used

let higher_order_projections struc =
  let found = ref Ref.User.Set.empty in
  let rec scan = function
    | MLglob {callee = r; _} when Table.is_projection r -> found := Ref.User.Set.add r !found
    | a -> Mlutil.ast_iter scan a
  in
  Modutil.struct_iter
    (fun d -> List.iter (fun fd -> scan fd.fd_body) (Mlutil.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  !found

let analyze struc =
  { used_customs = used_customs struc; higher_order_projections = higher_order_projections struc }

let equal a b =
  Ref.User.Set.equal a.used_customs b.used_customs
  && Ref.User.Set.equal a.higher_order_projections b.higher_order_projections
