(** Found by Ephyra (round 23, BDE flavour). A tail-recursive local
    fixpoint whose accumulator is an [option (nat -> PrimString.string)]
    and whose recursive call passes [if b then Some (fun _ => "a") else acc],
    under [Mapping.BDE] ([PrimString.string] is [bsl::string]).

    Expected: compiles, [result = 1].

    Fixed: "conditional expression is ambiguous;
    'optional<fn<std::string (unsigned int)>>' can be converted to
    'optional<fn<bsl::string (unsigned int)>>' and vice versa".  A string
    literal's Core type ([Core.Type.String], the type extraction gives
    ["a"%pstring]) was spelled [std::string] whatever mapped
    [PrimString.string]; where it reached a written type -- here the
    closure's result in the constructed argument -- it disagreed with the
    flavour's [bsl::string].  It is now spelled as the type mapping
    [PrimString.string] spells it. *)
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
