From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

(** FAITHFUL repro of the RESIDUAL parse-a-lot leaf-forward shapes that
    survive after grammar_tuple_leaf_ctor was fixed.

    grammar_tuple_leaf_ctor covered: a SINGLE leaf forwarded into a
    single-arg inductive constructor in RETURN position (Json_value::jstring(s),
    Newick, XML -- all now compile). Two shapes still fail, both in PPM's
    Triples/Document productions (examples/PPM/Parser/PPM.v), and identically
    in JSON's Obj production:

      SHAPE A (PPM.h:218, action of Triples -> [NAT;NAT;NAT;Triples]):
        action = fun tup => match tup with (x,(y,(z,(tpls,_)))) =>
                              mkRGBTriple x y z :: tpls end
        -> generates rgb_triple{x, y, z} (a single-ctor Record => C++ aggregate
        brace-init) with x,y,z still std::any, NOT in return position (it is
        the head argument of cons/push_front), plus tpls forwarded as
        std::deque<std::any> where std::deque<rgb_triple> is expected.

      SHAPE B (JSON.h:660 nodupKeys, PPM.h:145 triples_le_max, predicate of
        Document): an erased CONTAINER leaf (list rgb / list (string*_)) is
        forwarded into a function whose parameter is a concretely-typed
        container -- deque<std::any> vs deque<rgb_triple>/deque<pair<string,_>>.

    This repro mirrors the PPM Triples production faithfully: [tuple (map
    symbol_semty gamma)] domain (the essential ingredient established in
    grammar_tuple_leaf_ctor), a single-constructor Record [rgb] with three
    scalar fields (=> aggregate brace-init like rgb_triple), an action doing
    [mkRGB x y z :: tpls] (SHAPE A), and a predicate forwarding the erased list
    [tpls] into [triples_le_max] (SHAPE B). Uses Mapping.DequeList so lists
    become std::deque, matching the real deque<any> vs deque<rgb> mismatch. *)

(* Mirror Utils.tuple exactly. *)
Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

(* Single-constructor Record => C++ aggregate, mirrors PPM's rgb_triple. *)
Record rgb : Type := mkRGB { red : nat ; green : nat ; blue : nat }.

(* Mirrors PPM's triples_le_max: takes a list of the concrete record type. *)
Fixpoint triples_le_max (ts : list rgb) (m : nat) : bool :=
  match ts with
  | [] => true
  | t :: ts' => Nat.leb (red t) m && triples_le_max ts' m
  end.

Inductive terminal := TNAT.
Inductive nonterminal := Triples.

Definition t_semty (a : terminal) : Type := match a with TNAT => nat end.
Definition nt_semty (x : nonterminal) : Type := match x with Triples => list rgb end.

Inductive symbol := T : terminal -> symbol | NT : nonterminal -> symbol.
Definition symbol_semty (s : symbol) : Type :=
  match s with T a => t_semty a | NT x => nt_semty x end.
Definition symbols_semty (gamma : list symbol) : Type :=
  tuple (List.map symbol_semty gamma).

Definition production := (nonterminal * list symbol)%type.
Definition predicate_semty (p : production) : Type :=
  let (_, ys) := p in symbols_semty ys -> bool.
Definition action_semty (p : production) : Type :=
  let (x, ys) := p in symbols_semty ys -> nt_semty x.
Definition production_semty (p : production) : Type :=
  (predicate_semty p * action_semty p)%type.
Definition grammar_entry : Type := { p : production & production_semty p }.

Definition entries : list grammar_entry :=
  [ @existT _ _
      (Triples, [T TNAT ; T TNAT ; T TNAT ; NT Triples])
      (* SHAPE B: predicate forwards erased list [tpls] into triples_le_max. *)
      (fun tup =>
         match tup with
         | (x, (y, (z, (tpls, _)))) => triples_le_max tpls x
         end,
       (* SHAPE A: action builds record aggregate [mkRGB x y z] (not in return
          position, head of cons) and conses onto erased list [tpls]. *)
       fun tup =>
         match tup with
         | (x, (y, (z, (tpls, _)))) => mkRGB x y z :: tpls
         end)
  ; @existT _ _
      (Triples, [])
      (fun _ => true, fun _ => [])
  ].

Definition num_entries (u : unit) : nat := List.length entries.
Crane Extraction "grammar_tuple_record_cons" num_entries entries.
