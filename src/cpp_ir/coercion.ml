(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a value is adapted to the slot it is put in ({!Grammar.Coercion}).
    There is no identity plan: a value that needs no adaptation is left as
    it is. *)

include Grammar.Coercion

(** The name of [d]'s outermost step, for diagnostics and the census. *)
let rec decision_name : 'p decision -> string = function
  | Regroup _ -> "regroup"
  | Name _ -> "name"
  | Eta _ -> "eta"
  | Box _ -> "box"
  | Deep_box -> "deep box"
  | Unbox _ -> "unbox"
  | Erase _ -> "erase"
  | Recover _ -> "recover"
  | Convert _ -> "convert"
  | Container_cast _ -> "container cast"
  | Then (a, b) -> decision_name a ^ " then " ^ decision_name b

(** [cast_box ?tolerant into e]: [e], which its builder knows is a box,
    read at [into]: the coercion {!Cpp_passes.Coercions} expands to the cast
    ([Cast_box]).  For control lowering, which builds below
    {!Core_to_cpp.Coerce}. *)
let cast_box ?(tolerant = false) (into : Grammar.lowered Grammar.Type.t) (e : Grammar.lowered Grammar.Expr.t) :
    Grammar.lowered Grammar.Expr.t =
  Coerce ({from = Typed Any; into = Exactly into; plan = Cast_box {into; tolerant}}, e)
