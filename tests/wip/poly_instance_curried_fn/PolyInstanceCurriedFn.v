(** Found by Ephyra round 24 (through the generator's own typed mappings:
    [mb_of_opt : option A -> maybe A] at [A := option bool -> nat -> nat];
    the mapping is not needed). A polymorphic function over [option A] at
    [A := bool -> nat -> nat]: Crane instantiates the template at the
    curried [crane::fn<crane::fn<uint64_t(uint64_t)>(bool)>] while values
    of type [bool -> nat -> nat] are the flat
    [crane::fn<uint64_t(bool, uint64_t)>], and converts only some of them.

    - [none_const]: [id2 None]: the [None] literal is built at the flat type
      and passed unconverted, "no matching function for call to 'id2'".
    - [none_fn]: the same inside a function.
    - [use_result]: [match id2 o with Some f => f true 1 | None => 0 end]:
      the argument is converted to the curried type, but the field bound
      from the result is declared flat, "no viable conversion from
      'fn<crane::fn<uint64_t (uint64_t)> (bool)>' to
      'const fn<uint64_t (bool, uint64_t)>'".
    - [pass]: [id2 o] returned: compiles (a [crane_convert] each way) but the
      typed-fit check under [CRANE_CHECK_IR] refuses the converted argument,
      "(argument, convert)".

    Expected: compiles and extracts under [CRANE_CHECK_IR], the template
    instantiated at the type its values have; [result = 4].
    Actual: under [CRANE_CHECK_IR] (the suite's setting) extraction stops
    at the typed-fit refusal; without it, the C++ errors above. *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Extraction.

Module PolyInstanceCurriedFn.

Definition id2 {A : Type} (o : option A) : option A := o.

Definition none_const : option (bool -> nat -> nat) := id2 None.

Definition none_fn (b : bool) : option (bool -> nat -> nat) := id2 None.

Definition use_result (o : option (bool -> nat -> nat)) : nat :=
  match id2 o with Some f => f true 1 | None => 0 end.

Definition pass (o : option (bool -> nat -> nat)) : option (bool -> nat -> nat) := id2 o.

Definition result : nat :=
  match none_const, none_fn true with None, None => 1 | _, _ => 0 end
  + use_result (pass (Some (fun (b : bool) (n : nat) => if b then n + 2 else 0))).

End PolyInstanceCurriedFn.

Crane Extraction "poly_instance_curried_fn" PolyInstanceCurriedFn.
