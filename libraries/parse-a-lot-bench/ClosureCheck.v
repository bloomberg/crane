(* SPDX-License-Identifier: BSD-3-Clause *)
(** Empirical check of the interned DFA's closure certificate
    ([Lexer.DFA.IntDFA.closed_check]) on every lexical rule of every example
    grammar. Run it with [make closure-check].

    Interning a DFA state list is only sound when the list is closed under
    the transition function, and the Brzozowski table fill's fuel is not
    proved to achieve that. [IntDFA] therefore saturates the list it interns
    ([int_states]), which [int_states_closed] proves closed unconditionally.
    This diagnostic measures the gap that saturation has to make up: it runs
    [closed_check] on the *unsaturated* [build_states] of every rule. As of
    writing all 34 rules across the four grammars are already closed, so
    saturation converges after a single round.

    This lives here rather than in [theories] because it needs OCaml
    extraction to run: [canon] goes through [merge], whose termination
    argument is an opaque [Acc] witness, so [vm_compute] cannot evaluate it
    inside the kernel. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ExtrOcamlBasic ExtrOcamlString.

From Crane.Libraries.ParseALot.Examples.JSON.Lexer   Require Literal.
From Crane.Libraries.ParseALot.Examples.Newick.Lexer Require Literal.
From Crane.Libraries.ParseALot.Examples.PPM.Lexer    Require Literal.
From Crane.Libraries.ParseALot.Examples.XML.Lexer    Require Literal.

Set Extraction Output Directory "extracted".
Extraction Blacklist List String.

From Crane.Libraries.ParseALot.Utils Require Import NativeMap.
Extract Constant NativeMap.t "'k" "'v" => "('k, 'v) Native_map_impl.t".
Extract Constant NativeMap.empty => "Native_map_impl.empty".
Extract Constant NativeMap.get => "Native_map_impl.get".
Extract Constant NativeMap.set => "Native_map_impl.set".

Module J. Import Crane.Libraries.ParseALot.Examples.JSON.Lexer.Literal.
  Definition chk : list bool :=
    map (fun ru => let d := regex2dfa (snd ru) in closed_check d (build_states d)) rus.
End J.
Module N. Import Crane.Libraries.ParseALot.Examples.Newick.Lexer.Literal.
  Definition chk : list bool :=
    map (fun ru => let d := regex2dfa (snd ru) in closed_check d (build_states d)) rus.
End N.
Module P. Import Crane.Libraries.ParseALot.Examples.PPM.Lexer.Literal.
  Definition chk : list bool :=
    map (fun ru => let d := regex2dfa (snd ru) in closed_check d (build_states d)) rus.
End P.
Module X. Import Crane.Libraries.ParseALot.Examples.XML.Lexer.Literal.
  Definition chk : list bool :=
    map (fun ru => let d := regex2dfa (snd ru) in closed_check d (build_states d)) rus.
End X.

(** Fuzzing hook: closure of an arbitrary regex, plus its interned state
    count, so a driver can hunt for a rule whose table fill runs out of fuel.
    (Any grammar's [Literal] would do -- they all instantiate the same
    ascii-alphabet functor; JSON's is picked arbitrarily.) *)
Module F. Import Crane.Libraries.ParseALot.Examples.JSON.Lexer.Literal.
  Definition chk1 (r : regex) : bool :=
    let d := regex2dfa r in closed_check d (build_states d).
  Definition nstates1 (r : regex) : nat :=
    length (build_states (regex2dfa r)).
End F.

Definition chk1 := F.chk1.
Definition nstates1 := F.nstates1.

Definition chk_json := J.chk.
Definition chk_newick := N.chk.
Definition chk_ppm := P.chk.
Definition chk_xml := X.chk.

Separate Extraction chk_json chk_newick chk_ppm chk_xml chk1 nstates1.
