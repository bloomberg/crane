(** Crane bug: a type field reached through a class *substructure*
    ([mm_state :: MemState], [state] a field of [MemState]) under
    [Existing Instance] is left unresolved, and the call site boxes the
    whole argument pair.

    Observed (86aac86af):
      static Nat interp_it(const std::pair<state, std::pair<List<Nat>, Nat>> &s)   // [state]: file-scope std::any
      ...
      return interp_it<_tcI0>(std::make_pair(
          std::any(MemStateV<_tcI0>::initial_state()),
          std::any(std::make_pair(List<Nat>::cons(...), ...))));
    The second component is boxed although the parameter's second
    component is the concrete [std::pair<List<Nat>, Nat>].  Diagnostic:
      error: no matching function for call to 'interp_it'
    With the type field on a flat class ([Class MM := { mstate : Type ; ... }],
    no substructure, no Existing Instance) the same shape compiles.

    Reduced from Vellvm: [Interfaces/Memory.v] ([MemoryModelState.state],
    [MemoryModelPrimitives.mm_state :: MemoryModelState]),
    [Semantics/InterpretationStack.v] ([Existing Instance
    MemoryModelPrimitivesV], [FusedS := state * ...],
    [interp_mcfg {R} (t : MCFGtop R) s := ...]) and [TopLevel.v:304]
    ([interp_mcfg t (initial_state, ((Build_stack_frame ...,[]), Maps.empty))]):
    Vellvm's remaining [no matching function for call to 'interp_mcfg'],
    whose argument is
      std::make_pair(std::any(MemoryModelPrimitivesV<_tcI0>::mm_state::initial_state()),
                     std::any(std::make_pair(...stack...)))  *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Module NestedClassStateArg.
  Class Params : Type := { ptr : Type ; zero : ptr }.

  (* Vellvm's Interfaces/Memory.v: a state class, and a primitives class
     with it as a substructure ([mm_state :: MemoryModelState]). *)
  Class MemState {Pa : Params} : Type := { state : Type ; initial_state : state }.
  Class MemPrims {Pa : Params} : Type := { mm_state :: @MemState Pa ; bump : nat -> nat }.

  Section Impl.
    Context {Pa : Params}.
    Record St : Type := mkSt { mem : list ptr }.
    #[global] Instance MemStateV : @MemState Pa := { state := St ; initial_state := mkSt [] }.
    #[global] Instance MemPrimsV : @MemPrims Pa := { mm_state := MemStateV ; bump := S }.
  End Impl.

  Definition run_st {S : Type} (f : S -> nat) (s : S) : nat := f s.

  Section Stack.
    Context {Pa : Params}.
    Existing Instance MemPrimsV.
    (* Vellvm's InterpretationStack.FusedS and interp_mcfg (unannotated s). *)
    Definition FusedS : Type := (state * (list nat * nat))%type.
    Definition interp_it s : nat := run_st (fun st : FusedS => snd (snd st)) s.
    (* Vellvm's TopLevel.interpreter_gen. *)
    Definition start (_ : unit) : nat := interp_it (initial_state, ([1; 2], 3)).
  End Stack.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition is_three : bool := Nat.eqb (start tt) 3.
End NestedClassStateArg.

Crane Extraction "nested_class_state_arg" NestedClassStateArg.
