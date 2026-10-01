(** Crane bug (regression in f296b8556 / 287b34bb5): definitions that use a
    section-local instance's type field ([state] of [MemStateV]) spell it
    two different ways: [typename MemStateV<_tcI0>::state] in one
    definition, bare [state] (the file-scope [std::any] fallback) in the
    next.

    Observed (287b34bb5):
      template <Params _tcI0>
      static memM<typename MemStateV<_tcI0>::state, Nat> get_size() { ... }
      template <Params _tcI0>
      static memM<state, Nat> get_size2() { return ... get_size<_tcI0>() ... }
    Diagnostic:
      error: no viable conversion from returned value of type
             'memM<typename MemStateV<natParams>::state, [...]>' to function
             return type 'memM<state, [...]>'

    In Vellvm the same split shows up in [Memory1] (Implementations/Memory.v,
    [Instance MemoryModelStateV] at :353 and [get_frame_stack : memM
    Framestack] at :413 onwards), with more consequences: the declarations
    in the struct say [MemoryModelStateV<_tcI0>::state] while the struct
    [MemoryModelStateV] is only declared later ([no template named
    'MemoryModelStateV'] x6, [expected member name or ';'] x5), the
    out-of-line definitions say [state] ([out-of-line definition of
    'get_frame_stack' does not match any declaration in 'Memory1'] etc.),
    and one body writes [MemoryModelStateV<std::any>] ([constraints not
    satisfied ... with _tcI0 = std::any]).  27 of Vellvm's 33 errors on
    287b34bb5. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

Module SectionInstanceStateField.
  Class Params : Type := { ptr : Type ; zero : ptr }.

  (* Vellvm's Interfaces/Memory.v *)
  Class MemState {Pa : Params} : Type := { state : Type ; initial_state : state ; size_of : state -> nat }.
  Definition memM {Pa : Params} {MS : @MemState Pa} (A : Type) : Type := state -> (state * A).

  Section Implementation.
    Context {Pa : Params}.
    Record St : Type := mkSt { mem : list ptr }.
    (* Implementations/Memory.v:353, a section-local instance ... *)
    Instance MemStateV : @MemState Pa :=
      { state := St ; initial_state := mkSt [] ; size_of := fun s => length (mem s) }.
    (* ... used implicitly by later definitions in the same section
       (Memory.v:413 [get_frame_stack : memM Framestack]). *)
    Definition get_size : memM nat := fun s => (s, size_of s).
    Definition get_size2 : memM nat := fun s => get_size s.
  End Implementation.

  #[global] Instance natParams : Params := { ptr := nat ; zero := 0 }.
  Definition is_zero : bool := Nat.eqb (snd (get_size2 (mkSt []))) 0.
End SectionInstanceStateField.

Crane Extraction "section_instance_state_field" SectionInstanceStateField.
