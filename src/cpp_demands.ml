(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp

let acquire_fence = "std::atomic_thread_fence(std::memory_order_acquire);"

let of_external name =
  if String.equal name Crane_rt.small_vector then Some (Table.Runtime "small_vector")
  else if String.equal name Crane_rt.itree then Some (Table.Runtime "itree_header")
  else if String.equal name Crane_rt.field then Some (Table.Runtime Crane_rt.field_header)
  else if String.equal name ((Cpp_state.sn ()).ns ^ "::optional") then Some (Table.Standard "optional")
  else None

let at_type_variable = function Tvar _ | Tapply (Tvar _, _) -> true | _ -> false

let of_decl d =
  let found = ref [] in
  let need h = found := h :: !found in
  let obj () = need (Table.Runtime Crane_rt.obj_header) in
  let rec ty t =
    ignore
      (map_cpp_type
         (fun t ->
           ( match t with
           | Tid_external (name, _) -> Option.iter need (of_external name)
           | Tglob (_, _, args) -> List.iter (fun e -> ignore (expr e)) args
           | Texpr_type e -> ignore (expr e)
           | _ -> () );
           t )
         t );
    t
  and expr e =
    ( match e with
    (* A type parameter may be instantiated at an erased type, which a
       converting construction then builds. *)
    | CPPconverting_ctor (t, _) when at_type_variable t -> obj ()
    (* A pointer read at another instantiation of its pointee: allocated
       afresh, or null. *)
    | CPPcond (_, CPPfun_call (_, CPPalloc (Alloc_heap, _), _), CPPnullptr) ->
      need (Table.Standard "memory")
    | _ -> () );
    map_expr expr stmt ty e
  and stmt s =
    ( match s with
    | Sraw text when String.equal text acquire_fence -> need (Table.Standard "atomic")
    | Sif_constexpr (Tt_convertible (t, _), _, _) when at_type_variable t -> obj ()
    | _ -> () );
    map_stmt expr stmt ty s
  in
  let rec decl = function
    | Dtemplate (tps, c, inner) ->
      ignore (map_tparams ty tps);
      Option.iter (fun e -> ignore (expr e)) c;
      decl inner
    | Dnspace (_, ds) -> List.iter decl ds
    (* An axiom's type, which the user has yet to realise, is erased. *)
    | Dusing {du_rhs = Some Tany; _} -> obj ()
    | d -> ignore (map_decl expr stmt ty d)
  in
  decl d;
  !found
