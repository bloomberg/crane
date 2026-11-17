(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an inductive with a [Crane Extract Inductive] mapping, reached
    through a module alias, gets its mapped C++ type but not the rest of its
    mapping.  The type mapping is keyed by the definition (canonical
    identity), so [N.opt] for [Module N := M] is [std::optional<uint64_t>];
    the match template is keyed by the name it was registered under, so a
    match on an [N.opt] is generated as for an ordinary Crane variant --
    [std::holds_alternative<...::No>(o.v())] on a [std::optional]: "no type
    named 'No'". *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module AliasMappedInductiveMatch.

Module M. Inductive opt := No | Yes : nat -> opt. End M.

Module N := M.

Definition get (o : N.opt) : nat := match o with N.No => 0 | N.Yes n => n end.

Definition result : nat := get (N.Yes 4) + get N.No.

End AliasMappedInductiveMatch.

Crane Extract Inductive AliasMappedInductiveMatch.M.opt =>
  "std::optional<uint64_t>"
  [ "std::optional<uint64_t>()" "std::make_optional<uint64_t>(%a0)" ]
  "if (%scrut.has_value()) { const uint64_t& %b1a0 = *%scrut; %br1 } else { %br0 }"
  From "optional".
Crane Extraction "alias_mapped_inductive_match" AliasMappedInductiveMatch.
