(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The slot a subterm is generated into: what the position it occupies tells
    lowering about how to build it -- the representation the value takes, the
    Core type the position expects and states, whether it is a constructor
    argument or part of a constant -- and the boxing of a slot.  Depends on
    nothing else in translation; every lowering module and the position and
    representation plans pass slots. *)

open Base.Type_util

(** What the position a subterm occupies tells the generator about how to
    build it.  These properties travel together down every position whose
    value ends up in the same slot -- an argument, a coercion's operand, a
    branch result, a tail expression, the body of a lambda that is itself the
    stored value.  A position that opens a new slot (a let-bound right-hand
    side, a non-tail statement) starts again from {!empty_slot}. *)
type slot = {
  ret : Cpp_ir.Lowered.Type.t option;
      (** The result type of the function or lambda whose body the position
          is in ([None] where C++ deduces it). *)
  into : Cpp_ir.Lowered.Slot_type.t;
      (** The type the position itself states: [Exactly t], or [Free] where
          it states none.  Restated by every position ({!at}), never
          inherited. *)
  repr : slot_repr;
      (** How the value is represented in the slot.  [Boxed]: the slot is
          really [std::any], so a constructor built for it has to use the
          canonical erased shape -- every producer of the same Coq type must
          agree with the fixed [any_cast] that reads it back.  A "cons"
          production keeping [deque<Prod<Nat, Nat>>] where the matching "nil"
          erased to [deque<Prod<any, any>>] is what [std::bad_any_cast] at the
          consumer looks like. *)
  expected_core_ty : Core.Type.t option;
      (** The Core type of the slot, when the caller knows it more precisely than
          the expression's own annotation does.  It lets a constructor whose
          annotation carries unresolved metas (a [nil] whose element type
          extraction left open, say) recover the concrete type arguments from
          the position it occupies. *)
  in_ctor_arg : bool;
      (** The slot is an argument of a constructor, so a nested constructor
          filling it cannot name a template parameter of its own: an
          out-of-range [Core.Type.Variable] here is an erased field, which is [std::any]. *)
  eta_keep_moves : bool;
      (** The slot holds a single-use partial application whose closure may
          capture by reference and keep its [Move] wrappers.  Read once, by
          the {!Application.eta_fun} that builds that closure. *)
  call_result : Cpp_ir.Lowered.Type.t option;
      (** The type the call this slot is an argument of is expected to
          produce.  An instance passed as a value -- [MonadIter_itree] as
          [interp]'s dictionary, whose own slot erases with the class's
          carrier -- has its carrier head that type, and so is where an
          argument extraction erased from it is read back
          ({!Calls.instance_family_binding}). *)
  stated_core_ty : Core.Type.t option;
      (** The Core type the position states, erased parts and all -- the
          parameter an argument is passed at, [stateT nat (itree BotE) T] with
          [BotE] applied at its erased index.  [expected_core_ty] withholds a
          type with erasures in it, which is right for what it is used for;
          this is read only where an erased part is expected, to recover an
          event family nothing deduces. *)
  building_constant : bool;
      (** The constructor in this slot is part of a constant
          ({!Cpp_ir.Crane_rt.Constant}), so it is built here rather than hoisted
          again: the constant is the outermost closed term. *)
}

(** The slot properties of a position that constrains nothing. *)
let empty_slot =
  { ret = None;
    into = Free;
    repr = Native;
    expected_core_ty = None;
    in_ctor_arg = false;
    eta_keep_moves = false;
    call_result = None;
    stated_core_ty = None;
    building_constant = false }

(** Whether the value of [slot] is built inside a [std::any], at the
    canonical erased shape. *)
let boxed slot = match slot.repr with Boxed _ -> true | Native -> false

(** [slot], its value boxed as [kind] says unless it already is: an erasure
    the slot already carries is kept, being the outer and earlier one. *)
let into_box kind slot = if boxed slot then slot else { slot with repr = Boxed kind }

(** The slot of a position inside a body returning [ret], stating
    [expected_ty] where it states a type, with [slot]'s other properties
    (none by default). *)
let at ~ret ?expected_ty ?(slot = empty_slot) () : slot =
  { slot with ret; into = (match expected_ty with Some t -> Exactly t | None -> Free) }

(** The type the position states, if any. *)
let expected (s : slot) : Cpp_ir.Lowered.Type.t option = match s.into with Exactly t -> Some t | _ -> None
