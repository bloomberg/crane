(** A nullary constant of a functor, reached through a chain of functor
    applications across files, under separate extraction.

    [PredFn] (Pred.v) defines [empty_cache], which C++ writes as a Meyers
    accessor ([static const cache &empty_cache()]): a value of a type that
    mentions the functor's parameter.  [SoundFn] (Sound.v) applies [PredFn]
    as [SLLP]; [ParserFn] here applies [SoundFn] as [SLLS] and reads
    [empty_cache] through [SLLS.SLLP].  Reduced from ParseALot's Parser.h,
    where [SLLPC::SLLPEF::SLLS::SLLP::empty_cache] is read the same way.

    Expected: compiles; [result = 3].

    Actual: the use is written [SLLS::SLLP::empty_cache], without the call:
    "reference to type 'const cache' could not bind to an lvalue of type
    'const cache &()'". *)
From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From CraneTestsWIP Require Import sep_ext_accessor_functor_chain.Pred.
From CraneTestsWIP Require Import sep_ext_accessor_functor_chain.Sound.

Module ParserFn (D : T).
  Module Export SLLS := SoundFn D.
  Definition run (n : nat) : nat := n + size empty_cache.
End ParserFn.

Module N <: T. Definition t := nat. End N.
Module P := ParserFn N.

Definition result : nat := P.run 3.

Crane Separate Extraction result.
