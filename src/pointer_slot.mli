(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a pointer to a value is held in: which spelling a smart pointer to
    it gets, and so which header that spelling needs. *)

type t =
  | Shared
      (** A shared slot ([crane::shared_box]): the pointee is an inductive
          stored as a shared variant, whose value is already the shared
          handle a pointer would otherwise add. *)
  | At_instantiation
      (** An inductive a functor's body reaches through its parameter, which
          is a shared variant or not according to the argument -- known to
          the C++ instantiation only, so the slot is chosen there
          ([crane::shared_or_t]). *)
  | Pointer  (** An ordinary pointer. *)

(** [of_pointee t] is what a pointer to a value of type [t] is held in. *)
val of_pointee : Minicpp.cpp_type -> t
