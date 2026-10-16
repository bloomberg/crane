(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp

let acquire_fence = "std::atomic_thread_fence(std::memory_order_acquire);"

let of_external name =
  if String.equal name Crane_rt.small_vector then Some (Table.Runtime "small_vector")
  else if String.equal name Crane_rt.field then Some (Table.Runtime Crane_rt.field_header)
  else if String.equal name ((Cpp_state.sn ()).ns ^ "::optional") then Some (Table.Standard "optional")
  else None

let demand d =
  let rec ty t =
    ignore
      (map_cpp_type
         (fun t ->
           ( match t with
           | Tid_external (name, _) -> Option.iter Table.demand_header (of_external name)
           | Tglob (_, _, args) -> List.iter (fun e -> ignore (expr e)) args
           | Texpr_type e -> ignore (expr e)
           | _ -> () );
           t )
         t );
    t
  and expr e = map_expr expr stmt ty e
  and stmt s =
    ( match s with
    | Sraw text when String.equal text acquire_fence -> Table.demand_header (Table.Standard "atomic")
    | _ -> () );
    map_stmt expr stmt ty s
  in
  let rec decl = function
    | Dtemplate (tps, c, inner) ->
      ignore (map_tparams ty tps);
      Option.iter (fun e -> ignore (expr e)) c;
      decl inner
    | Dnspace (_, ds) -> List.iter decl ds
    | d -> ignore (map_decl expr stmt ty d)
  in
  decl d
