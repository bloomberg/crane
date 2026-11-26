(** Found by Ephyra round 28. [Datatypes.id] (whose type is the alias
    [ID := forall A, A -> A], so its argument and result are erased to
    [std::any]) applied to a two-argument function transformer, the result
    the step of [twice] at [A := (nat -> nat) -> nat -> nat]. The result was
    cast back with [crane::any_cast] to the flat
    [crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>], while
    [twice]'s template argument wanted the curried
    [crane::fn<crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>]
    ("no matching function for call to 'twice'"; under CRANE_CHECK_IR,
    "coercion position"). The cast itself could not succeed either: the
    lambda went into the box through [crane_erase_fn], as the boxed-whole
    [crane::fn<crane::obj(crane::obj)>], which a strict cast at the concrete
    signature does not read.

    Fixed: the recovered callable is regrouped to the slot
    ([Application.gen_call_args], [Cpp_passes.Coercions.regroup_curried],
    which now regroups a flat value to a curried slot too), the position
    plan places the coercion where lowering does ([Calls.argument_position]),
    and a callable is recovered from a box by the tolerant caster
    ([Cpp_passes.Erasure.tolerant]), which reads a boxed-whole callable at
    a concrete signature ([crane_any_cast], [crane_boxed_callable]). *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.

Module IdAnyCastFlatFn.

Definition twice {A : Type} (f : A -> A) (x : A) : A := f (f x).
Definition result : nat :=
  twice (id (fun (c : nat -> nat) (n : nat) => c n + 1)) (fun n : nat => n) 0.

End IdAnyCastFlatFn.

Crane Extraction "id_any_cast_flat_fn" IdAnyCastFlatFn.
