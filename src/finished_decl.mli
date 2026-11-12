(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A finished declaration in both IRs: its MiniCpp, which the printer
    still reads, and its CppIR ({!Unit_program.declaration}).  A leaf of the
    tree a file is written from carries both, so that what plans and prints
    it can read either. *)

type t = {
  settled : Cpp_erasure.settled;
  ir : Cpp_ir.Resolved.Decl.t;  (** [settled], in CppIR *)
}

(** A finished declaration taken apart one level in both IRs at once, as
    {!Cpp_erasure.view} takes its MiniCpp apart. *)
type view =
  | Template of t  (** a template, by what it is a template of *)
  | Namespace of Minicpp.nspace_wrapper option * t list
  | Decl  (** any other declaration: none nested inside *)

(** [view d] is [d] taken apart one level.
    @raise Anomaly if its two IRs are not of the same shape. *)
val view : t -> view
