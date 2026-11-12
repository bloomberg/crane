(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A generated declaration finished once, and the two views of it a file
    writes: its declaration and its definition.

    The whole definition is finished ({!Cpp_pipeline.finish}) before it is
    split, so the declaration states the template head the finished body
    settled -- which callback constraints survive is decided with the body in
    hand.  A declaration and a definition that differ in a constraint are two
    different functions. *)

(** A finished declaration with its two views. *)
type t

(** [of_finished d ir] splits [d], already finished, and [ir], its CppIR,
    where they define a function.  Under [CRANE_CHECK_IR], [ir] splits as
    [d] does. *)
val of_finished : Cpp_erasure.settled -> Cpp_ir.Resolved.Decl.t -> t

(** The declaration of the function the entity defines; anything else is its
    own declaration. *)
val declaration : t -> Cpp_erasure.settled

(** What is written where the entity is defined, when nothing declared it
    before. *)
val definition : t -> Cpp_erasure.settled

(** The definition written after the {!declaration} in the same file: the
    declaration gave the template defaults, which C++ allows once per
    parameter. *)
val definition_after_declaration : t -> Cpp_erasure.settled

(** {!declaration} in CppIR. *)
val declaration_ir : t -> Cpp_ir.Resolved.Decl.t

(** {!definition} in CppIR. *)
val definition_ir : t -> Cpp_ir.Resolved.Decl.t

(** {!definition_after_declaration} in CppIR. *)
val definition_after_declaration_ir : t -> Cpp_ir.Resolved.Decl.t

(** Whether the entity is a function, with a declaration distinct from its
    definition. *)
val defines_function : t -> bool
