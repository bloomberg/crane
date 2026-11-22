(** Found by Ephyra round 23 (BDE flavour). A tail-recursive local
    fixpoint whose accumulator is an [option (nat -> PrimString.string)]
    and whose recursive call passes [if b then Some (fun _ => "a") else acc],
    under [Mapping.BDE] ([PrimString.string] is [bsl::string]).
    Expected: compiles, [result = 1].
    Actual: "conditional expression is ambiguous;
    'optional<fn<std::string (unsigned int)>>' can be converted to
    'optional<fn<bsl::string (unsigned int)>>' and vice versa": the loop's
    accumulator update spells the constructed closure's result type as
    [std::string], the accumulator itself as [bsl::string]. More
    generally a value constructed as the argument of a local fixpoint's
    call spells [PrimString.string] as [std::string] (also seen:
    [List<bsl::pair<std::string, rs>>] in a [?:] branch); it compiles
    while a conversion bridges it and fails where a [?:] must pick a
    common type. The same [if] outside a loop, or an
    [option PrimString.string] accumulator, compiles. Also on main. *)
From Crane Require Import Mapping.NatIntBDE Mapping.BDE.
From Crane Require Import Extraction.
From Stdlib Require Import List.
From Corelib Require Import PrimString.
Import ListNotations.

Module BdeLoopAccFnStdString.

Definition last_fn (b : bool) (l : list nat) (z : option (nat -> PrimString.string))
    : option (nat -> PrimString.string) :=
  let fix go (l : list nat) (acc : option (nat -> PrimString.string)) {struct l}
      : option (nat -> PrimString.string) :=
    match l with [] => acc | _ :: r => go r (if b then Some (fun _ : nat => "a"%pstring) else acc) end
  in go l z.

Definition result : nat := match last_fn true [1] None with None => 0 | Some _ => 1 end.

End BdeLoopAccFnStdString.

Crane Extraction "bde_loop_acc_fn_std_string" BdeLoopAccFnStdString.
