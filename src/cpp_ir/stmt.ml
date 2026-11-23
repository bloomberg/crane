(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** C++ statements ({!Grammar.Stmt}), with the families only a statement
    names. *)

include Grammar.Stmt
module Binding = struct
  include Grammar.Binding

  (** The type a declaring, non-static, binding writes and the Core binder
      it stands for: [auto] for a deduced one. *)
  let written : type p. p t -> (p Grammar.Type.t * Core.Binder.t option) option = function
    | Declare (t, b) -> Some (t, b)
    | Declare_deduced (_, b) -> Some (Auto, b)
    | Existing | Declare_static _ -> None
end
module Match = Grammar.Match
module Custom_match = Grammar.Custom_match
module Foreign_block = Grammar.Foreign_block
module Precondition = Grammar.Precondition
