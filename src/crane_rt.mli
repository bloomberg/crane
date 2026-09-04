(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The names of the runtime helpers declared in [theories/cpp/].

    These are the only C++ symbols Crane emits that it does not derive from a
    [GlobRef.t], so they are the only ones a rename in the runtime headers can
    silently desynchronise from.  Spelling them once here makes the whole
    runtime surface greppable from one place; every emitter reads them rather
    than repeating the string. *)

(** {2 [crane_rc.h]} -- reference counting under [Crane NonAtomicRc]. *)

val rc : string  (** [crane::rc<T>] -- the non-atomic [shared_ptr]. *)

val make_rc : string  (** [crane::make_rc<T>] *)

val enable_rc_from_this : string  (** [crane::enable_rc_from_this<T>] *)

(** {2 [crane_reuse.h]} -- Perceus in-place reuse. *)

val make_rc_reusing : string
(** [crane::make_rc_reusing<T>] -- rebuild into a token's storage, checking
    that the token is sole-owned and large enough. *)

val make_rc_reusing_unchecked : string
(** [crane::make_rc_reusing_unchecked<T>] -- as {!make_rc_reusing}, where the
    caller has already established the guard. *)

val reuse_step : string
(** [crane::reuse_step] -- advance a reuse token along a spine. *)

(** {2 [crane_arena.h]} -- arena allocation. *)

val arena_alloc : string  (** [crane::arena_alloc<T>] *)

val arena_shared_alloc : string  (** [crane::arena_shared_alloc<T>] *)

val arena_make_shared : string  (** [crane::arena_make_shared<T>] *)

(** {2 [crane_fn.h]} -- erasure. *)

val any_cast : string
(** [crane_any_cast<T>] -- the tolerant caster, which defers the shape
    question to [if constexpr] at instantiation time. *)

val erase_fn : string
(** [crane_erase_fn<Ret>] -- adapt a concrete callable to the canonical erased
    signature. *)

(** {2 Containers} *)

val small_vector : string  (** [crane::small_vector<T>] *)

val lazy_ : string  (** [crane::lazy<T>] *)
