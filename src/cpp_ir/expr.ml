(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** C++ expressions ({!Grammar.Expr}), with the families only an expression
    names. *)

include Grammar.Expr
module Call = Grammar.Call
module Lambda = Grammar.Lambda
module Capture = Grammar.Capture
module Written_capture = Grammar.Written_capture
module Local_fixpoint = Grammar.Local_fixpoint
module Method_call = Grammar.Method_call
module Method_value = Grammar.Method_value
module Projection = Grammar.Projection
module Aggregate = Grammar.Aggregate
module Requires = Grammar.Requires
module Literal = Grammar.Literal
module Numeral = Grammar.Numeral
module Unbox = Grammar.Unbox
module Access = Grammar.Access
module Allocation = Grammar.Allocation
module Erase_shape = Grammar.Erase_shape
