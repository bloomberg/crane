(** Found by Ephyra round 24 (through the generator's own typed mappings:
    [mb_of_opt : option A -> maybe A] at [A := option bool -> nat -> nat];
    the mapping is not needed). A polymorphic function over [option A] at
    [A := bool -> nat -> nat]: Crane instantiated the template at the
    curried [crane::fn<crane::fn<uint64_t(uint64_t)>(bool)>] while values
    of type [bool -> nat -> nat] are the flat
    [crane::fn<uint64_t(bool, uint64_t)>], and converted only some of them:
    [id2 None] passed the [None] built flat ("no matching function for call
    to 'id2'"), [match id2 o with Some f => ...] bound the field flat from
    the curried result, and [id2 o] compiled through a [crane_convert] each
    way that the typed-fit check refused ("(argument, convert)").

    Fixed: a type variable instantiated at a function type was spelled
    curried, as a template argument and wherever a declaration names the
    variable (Arrow_site Through_tvar), while values of the type are
    spelled flat in every declared position.  A type argument is now
    spelled as the values of its type are ([Types.template_arg_of_core_type]
    at [Declared], [Calls.spell_as_declared]); the arrows a declaration
    writes are one group and the instantiated variable's own arrows the
    next ([Declared_at n]).

    Expected: compiles and extracts under [CRANE_CHECK_IR]; [result = 4]. *)
From Crane Require Import Mapping.NatInt.
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
