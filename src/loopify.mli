(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Loopify pass: transforms recursive MiniCpp functions into iterative ones.

    Operates on {!Minicpp.cpp_decl} nodes after translation produces them but
    before pretty-printing. Detects self-recursive function/method bodies and
    rewrites them using while loops and explicit stacks to prevent stack
    overflow on deep inputs. *)

open Names
open Minicpp

(** Transform a single top-level declaration. Recursion through [Dtemplate]
    wrappers to find inner [Dfundef] nodes. Also transforms recursive methods
    inside [Dstruct] fields ([Fmethod]).

    @param pp_type
      converts a [cpp_type] to its C++ string representation. Used by the
      non-tail recursion pass to generate frame type declarations and vector
      element types as raw C++ strings.

    @param pp_expr
      converts a [cpp_expr] to its C++ string representation. Used to generate
      [decltype(expr)] for struct fields when the type cannot be inferred. *)
val transform_decl :
  ?tparams:(template_type * Id.t) list ->
  pp_type:(cpp_type -> string) ->
  pp_expr:(cpp_expr -> string) ->
  cpp_decl ->
  cpp_decl
