(** A lifted helper called with a type argument the enclosing function's
    return type made up.

    [list_to_dvalue] is a let-bound function whose body is a local [fix]
    written with ExtLib's monad notation.  [bind] extracts with its carrier
    erased, so [m A] pins nothing, and the continuation's binder [f] keeps a
    free meta where Rocq says [dvalue].  Lifting generalises that meta into a
    template parameter [T1], and the call site, finding nothing to read it
    off, gives it the enclosing function's whole return type:

      template <Params _tcI0, typename T1> auto _to_dvalue_list_to_dvalue(...)
      ... _to_dvalue_list_to_dvalue<_tcI0, std::optional<Dvalue<...>>>(...)

    which compiles and then fails at run time.  In Vellvm, where the
    declaration's head had also shed the parameter, the same call is
    "too many template arguments".

    Reduced from Vellvm's [memory_bytes_to_dvalue] (Semantics/MemoryBytes.v:274),
    two of the install #18 residue. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads Structures.Functor Data.Monads.OptionMonad.
From Stdlib Require Import List.
Import ListNotations MonadNotation FunctorNotation.
Open Scope monad_scope.

Class Params := { ptr : Type ; nullp : ptr }.

Section S.
  Context {Pa : Params}.

  Inductive dtyp : Type := DLeaf : dtyp | DStruct : list dtyp -> dtyp.
  Inductive dvalue : Type := DV0 : ptr -> dvalue | DVS : list dvalue -> dvalue.

  Fixpoint to_dvalue (dbs : list nat) (dt : dtyp) : option dvalue :=
    let list_to_dvalue (pad : option nat) :=
      fix go (offset : nat) dts dbs :=
        match dts with
        | [] => ret []
        | dt :: dts =>
            let padding := match pad with Some p => p | None => 0 end in
            f <- to_dvalue dbs dt ;;
            rest <- go (offset + padding) dts dbs ;;
            ret (f :: rest)
        end
    in
    match dt with
    | DLeaf => ret (DV0 nullp)
    | DStruct fields => DVS <$> list_to_dvalue (Some 1) 0 fields dbs
    end.
End S.

#[global] Instance natParams : Params := {| ptr := nat ; nullp := 0 |}.

Module LiftedFixExtraTargAtCall.
  Definition run : option dvalue := @to_dvalue natParams [1; 2] (DStruct [DLeaf; DLeaf]).
End LiftedFixExtraTargAtCall.
Crane Extraction "lifted_fix_extra_targ_at_call" LiftedFixExtraTargAtCall.
