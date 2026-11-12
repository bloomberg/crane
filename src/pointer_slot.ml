(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type t = Shared | At_instantiation | Pointer

let rec of_pointee : type p. p Cpp_ir.Type.t -> t = function
  | Entity_application (r, _, _) when Table.is_shared_variant r -> Shared
  | Entity_application (GlobRef.IndRef (kn, _), _, _)
    when Table.shared_variant () && Common.under_mp_bound (MutInd.modpath kn) ->
    At_instantiation
  | In_namespace (_, t) | Const t -> of_pointee t
  | _ -> Pointer
