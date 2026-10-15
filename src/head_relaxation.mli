(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What one relaxation of a function's head decided, as data
    (docs/Pipeline-Disentangling-Plan.md, Milestone 4).

    A relaxation ({!Plan_templates.relax_function_head}) answers a template
    parameter a call cannot supply by spelling the declaration differently,
    and the declaration, its body included, must then be rewritten to match.
    The decision is made once, when the head is planned, and recorded in the
    callee's plan ({!Callable_abi.relaxations}); a declaration generated
    under that head applies it ({!apply}) rather than deciding it again. *)

type t =
  | Computed_return of Minicpp.cpp_type
      (** The return type is the result of the callback that produces it:
          a template template parameter nothing deduces is dropped for it. *)
  | Param_applications of {
      relaxed : Names.Id.t list;
      deduced : ((Names.Id.t * Minicpp.cpp_type list) * Names.Id.t) list;
    }
      (** Each application of a [relaxed] variable, by the variable and the
          arguments it is applied to, is the template parameter [deduced]
          names, in the parameters and the body. *)
  | Deapplied of {
      plain : Names.Id.t list;
      in_scope : Names.Id.t list;
    }
      (** An application of a variable declared a plain [typename] is taken
          back off it ({!Minicpp.rebind_plain_var}), [in_scope] being the
          head's parameters. *)
  | Unmentioned of Names.Id.t list
      (** The variables the head defaults because the signature no longer
          mentions them are erased wherever they are still spelled, an
          [any_cast]'s target excepted. *)

val equal : t -> t -> bool

(** [deapplied ~plain ~in_scope ty] -- {!Deapplied}'s rewrite of one type. *)
val deapplied : plain:Names.Id.t list -> in_scope:Names.Id.t list -> Minicpp.cpp_type -> Minicpp.cpp_type

(** [apply r d] -- the declaration [d] rewritten as [r] decided. *)
val apply : t -> Minicpp.cpp_decl -> Minicpp.cpp_decl

(** Each relaxation applied in turn, the first first. *)
val apply_all : t list -> Minicpp.cpp_decl -> Minicpp.cpp_decl
