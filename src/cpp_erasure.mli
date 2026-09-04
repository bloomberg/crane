(** Erasure decisions over the MiniCpp IR.

    A value that crosses into a [std::any] has to be read back out at the shape
    it was written in, and how to do that is not always knowable where the cast
    is built.  This module owns that decision, and with it the single answer to
    "is this type spelled [std::any]".

    See [docs/nanopass-plan.md]. *)

open Names
open Minicpp

(** {2 Axiom types}

    A Rocq axiom has no computational content, so its type extracts to
    [std::any].  The registry is populated by {!Cpp_ind} as declarations are
    processed. *)

(** Register a GlobRef as an axiom type. *)
val register_axiom_type : GlobRef.t -> unit

(** Whether a GlobRef has been registered as an axiom type. *)
val is_axiom_type_ref : GlobRef.t -> bool

(** {2 The boxedness oracle} *)

(** Names introduced by [using X = std::any;], accumulated in emission order. *)
val any_type_aliases : Id.Set.t ref

(** [is_any_shaped ty] — [ty] is spelled [std::any] in the generated code,
    whether directly, through a type modifier, through a [using] alias, or
    because it is an axiom type. *)
val is_any_shaped : cpp_type -> bool

(** {2 The pass} *)

(** [resolve_casts decl] rewrites every {!Minicpp.CPPany_cast} in [decl] to say
    which caster the printer should emit: dropped where the cast is the
    identity, {!Minicpp.CPPany_cast_tolerant} where the shape is only knowable
    when C++ instantiates the surrounding template, and left alone otherwise.

    Call it on declarations in emission order: [using] aliases are recorded as
    they are met, mirroring where C++ would have them in scope. *)
val resolve_casts : cpp_decl -> cpp_decl
