(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A frozen type or term as one of any phase: it holds no metavariable, the
    one form whose payload depends on the phase, so the copy keeps every
    node, occurrence, hole and open annotation as it is.  For an extracted
    reader of what is frozen already: the type a global was registered at
    before the program it is used in was extracted. *)

open Grammar

(** The frozen type [t] at any phase. *)
let rec type_ : Phase.frozen Type.at -> 'p Type.at = function
  | Type.Arrow {parameter; result} -> Type.Arrow {parameter = type_ parameter; result = type_ result}
  | Type.Global_app {head; type_arguments; index_arguments} ->
    Type.Global_app
      {head; type_arguments = List.map type_ type_arguments; index_arguments = List.map expr index_arguments}
  | Type.Variable_app {head; arguments} -> Type.Variable_app {head; arguments = List.map type_ arguments}
  | Type.Meta {phase = _; _} -> .
  | (Type.Variable _ | Type.Hole _ | Type.Open _ | Type.Erased _ | Type.Unknown | Type.Axiom | Type.String) as t ->
    Retype.type_leaf t

(** The frozen term [e] at any phase. *)
and expr : Phase.frozen Expr.at -> 'p Expr.at = fun e -> Retype.expr type_ e
