(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

let check_global_use r tys =
  if List.exists (function Tdummy Kprop -> true | _ -> false) tys then
    Probe.violation "global use"
      Pp.(
        str "the type arguments of " ++ Names.GlobRef.print r
        ++ str " hold a proof placeholder, which no scheme variable stands for" )

let check_node = function
  | MLglob ({callee = r; _} as use) -> check_global_use r (Global_use.legacy_source_order use)
  | _ -> ()

let structure struc =
  if Probe.checking () then
    ignore
      (Modutil.struct_ast_search
         (fun a ->
           check_node a;
           false )
         struc )
