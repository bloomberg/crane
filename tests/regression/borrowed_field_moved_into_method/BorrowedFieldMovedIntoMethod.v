From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List ZArith NArith.
Import ListNotations.

(** [walk] recurses into the element type [ta] of an array type, and adds
    [size_of ta] into the offset on the way.  [ta] is a field of the borrowed
    parameter [t] ([const ty &]); [ty]'s recursive field is a [shared_ptr], so
    the element node is shared with whoever built [t] -- here the global
    [arr].

    The call is emitted as [_tcI0::size_of(std::move( *t0))]: the last read of
    [ta] is moved into the by-value class method.  That hollows out the element
    node of [arr] itself, so the second [walk] over [arr] reads a moved-from
    [positive] (an [XO] whose child is null) and segfaults.

    It takes a class with three methods.  With [Size] cut to one or two
    methods the same call is emitted as [size_of( *t0)], no move.  It also
    takes the [let k := ...]: without it, no move.

    Found in Vellvm's [Gep.handle_gep_h] (its [Sizeof] class has three
    methods): a loop executing one getelementptr twice segfaulted on the
    second, in [N.div] under [Sizeof_dtyp].

    [Size] lives in its own module only because in one module Crane emits the
    [Size] concept after the struct whose template uses it (a separate,
    smaller problem). *)

Module BfmTypes.

  Inductive ty :=
  | TB (n : positive)
  | TS (packed : bool) (fields : list ty)
  | TA (vector : bool) (sz : N) (t : ty).

  Class Size : Type :=
    { bit_size_of : ty -> N; size_of : ty -> N; align_of : ty -> N }.

End BfmTypes.
Import BfmTypes.

Module BorrowedFieldMovedIntoMethod.

  Section Walk.
    Context {S : Size}.

    Fixpoint walk (t : ty) (off : Z) (vs : list nat) : option Z :=
      match vs with
      | i :: vs' =>
          let k := Z.of_nat i in
          match t with
          | TA _ _ ta => walk ta (off + k * Z.of_N (size_of ta))%Z vs'
          | _ => None
          end
      | [] => Some off
      end.
  End Walk.

  Fixpoint sz (t : ty) : N :=
    match t with
    | TB n => N.div (Npos n) 8
    | TS _ _ => 0
    | TA _ n t => n * sz t
    end%N.

  #[export] Instance SizeI : Size :=
    { bit_size_of := fun t => (8 * sz t)%N; size_of := sz; align_of := sz }.

  Definition arr : ty := TA false 4 (TB 64).

  Definition get (o : option Z) : Z :=
    match o with Some z => z | None => 0%Z end.

  (** Each walk is 3 * 8 = 24. *)
  Definition check (_ : unit) : bool :=
    Z.eqb (get (walk arr 0 [3]) + get (walk arr 0 [3])) 48.

End BorrowedFieldMovedIntoMethod.

Crane Extraction "borrowed_field_moved_into_method" BorrowedFieldMovedIntoMethod.
