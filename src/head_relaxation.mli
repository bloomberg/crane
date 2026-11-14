(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What one relaxation of a function's head decided, as data, so that the
    decision belongs to the callee's plan and not to whichever emitter
    happens to generate the declaration.

    A relaxation ({!Plan_templates.relax_function_head}) answers a template
    parameter a call cannot supply by spelling the declaration differently,
    and the declaration, its body included, must then be rewritten to match.
    The decision is made once, when the head is planned, and recorded in the
    callee's plan ({!Callable_abi.relaxations}); a declaration generated
    under that head applies it ({!apply}) rather than deciding it again. *)

type t =
  | Computed_return of Cpp_ir.Lowered.Type.t
      (** The return type is the result of the callback that produces it:
          a template template parameter nothing deduces is dropped for it. *)
  | Param_applications of {
      relaxed : Names.Id.t list;
      deduced : ((Names.Id.t * Cpp_ir.Lowered.Type.t list) * Names.Id.t) list;
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

(** Structural equality, by which two {!Callable_abi.t} plans of one callee
    are compared. *)
val equal : t -> t -> bool

(** [deapplied_lowered ~plain ~in_scope ty] -- {!Deapplied}'s rewrite of one
    type. *)
val deapplied_lowered :
  plain:Names.Id.t list -> in_scope:Names.Id.t list -> Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t

(** [rebind_plain_var_lowered ~in_scope head args] -- {!Minicpp.rebind_plain_var}
    over CppIR types: the variable [head], declared a plain [typename],
    applied to [args]. *)
val rebind_plain_var_lowered :
  in_scope:Names.Id.t list -> Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t list -> Cpp_ir.Lowered.Type.t

(** [apply r d] -- the declaration [d] rewritten as [r] decided.  A
    declaration of a kind [r] does not concern is returned unchanged. *)
val apply : t -> Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t

(** [apply_signature r ~params ~ret] -- a signature, its value parameters'
    types [params] and its return type [ret], rewritten as [r] decided: what
    {!apply} does to a function declaration's own types. *)
val apply_signature :
  t ->
  params:Cpp_ir.Lowered.Type.t list ->
  ret:Cpp_ir.Lowered.Type.t ->
  Cpp_ir.Lowered.Type.t list * Cpp_ir.Lowered.Type.t

(** Each relaxation applied in turn by {!apply}, the first first. *)
val apply_all : t list -> Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t

(** [deapply_struct ~plain ~in_scope d] -- {!Deapplied}'s rewrite of a
    generated struct [d] in CppIR: its members, their bodies, and its
    template parameters, a lambda whose parameter deduced a template
    parameter only through an application taken off settled again
    ({!Minicpp.settle_lambda_tparams}). *)
val deapply_struct :
  plain:Names.Id.t list -> in_scope:Names.Id.t list -> Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t

(** [settle_lowered_lambda l] is [l] without the template parameters none of
    its parameters names, each use of them erased
    ({!Minicpp.settle_lambda_tparams} in CppIR). *)
val settle_lowered_lambda :
  Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t -> Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t
