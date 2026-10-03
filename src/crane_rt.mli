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

val call_erased : string
(** [crane_call_erased] -- apply a callable whose parameter types are only
    known once C++ instantiates the enclosing template, recovering them by
    CTAD. *)

val convert : string
(** [crane_convert<Dst>(e)] -- read a value at another instantiation of its
    own type, by whichever route that type offers: a converting constructor
    where it has one, and the [crane_cast_to] hook where it does not. *)

val convertible : string
(** [crane_convertible<Dst, Src>] -- whether {!convert} has a route. *)

val container_cast : string
(** [crane_container_cast<Dst>(e)] -- converts a type-erased container
    elementwise. *)


(** {2 Containers} *)

val small_vector : string  (** [crane::small_vector<T>] *)

val lazy_ : string  (** [crane::lazy<T>] *)

val fn : string
(** [crane::fn<R(A...)>] -- a closure as a shared, immutable value: what a
    Rocq function type is written as. *)

val obj : string
(** [crane::obj] -- an erased value, shared rather than copied: what an
    erased type is written as. *)

val obj_cast : string
(** [crane::any_cast<T>] -- reads a [crane::obj] back at [T]. *)

val obj_header : string  (** [obj.h] *)

val lazy_header : string  (** [lazy.h] -- {!lazy_}. *)

val erasure_header : string
(** [crane_fn.h] -- the erasure and conversion helpers: {!erase_fn},
    {!call_erased}, {!any_cast}, {!convert}, {!container_cast}. *)

val itree_header : string  (** [crane_itree.h] -- reified interaction trees. *)

val rebind : string  (** [crane::rebind_t], a plain carrier read at an element *)

val variant : string  (** [crane::variant], the tagged union of [Crane FastVariant] *)

val variant_header : string  (** [crane_variant.h] -- {!variant}. *)

val fn_header : string
(** [fn.h], the header declaring {!fn}; demanded by the type printer. *)

val counting_ptr : string
(** [crane::counting_ptr<T>] -- the measurement-only reference-count-counting
    shared pointer of count_rc.h, selected by [CRANE_COUNT_RC]. *)

val make_counting : string  (** [crane::make_counting<T>] *)

(** {2 Helpers a MiniCpp expression may name} *)

(** The runtime helpers that appear in the IR rather than only in the
    printer.  A {!Minicpp.CPPrt} carries one of these instead of the helper's
    spelling, so a call into the runtime cannot be built out of a string that
    no runtime header defines. *)
type helper =
  | Make_rc_reusing_unchecked
  | Reuse_step
  | Raw  (** [crane_raw(p)] -- the raw pointer a smart pointer holds. *)

(** [crane_raw], in {!erasure_header}. *)
val raw : string

val name : helper -> string
(** [name h] -- the C++ spelling of [h]. *)
