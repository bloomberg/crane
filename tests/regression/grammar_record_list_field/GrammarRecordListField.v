From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

(** Reproduced the compile error the extracted C++ PPM parser hits after the
    grammar_action_pairlist_crash fix:

      PPM.h: no viable conversion from 'deque<std::any>' to 'deque<rgb_triple>'

    A semantic ACTION that constructs a RECORD (aggregate) whose field type is a
    concrete-element list (e.g. ppm_value's [triples : list rgb_triple]) forwards
    an erased list leaf ([nt_semty Triples], boxed at runtime as
    std::deque<std::any>) straight into that field. Crane used to emit a plain
      std::any_cast<std::deque<std::any>>(std::any_cast<std::deque<std::any>>(ts))
    with NO crane_container_cast, so the erased std::deque<std::any> could not
    convert to the record field's concrete std::deque<elt>.

    The earlier fix added crane_container_cast only for the inductive-constructor
    FACTORY path (e.g. json_value's JList/JAssoc factories, [gen_and_wrap] in
    translation.ml); the RECORD / aggregate-construction path ([mkRec ... ts],
    [record_arg_exprs]) was not covered. Fixed by extracting the factory path's
    container-cast logic into a shared helper, [container_cast_erased_field] in
    translation.ml, and calling it from both the constructor/factory path and the
    record/aggregate path. This mirrors PPM's [Document -> ... NT Triples]
    production whose action is [mkPPMValue w h m ts]. *)

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

(** Concrete element type, like rgb_triple. *)
Record elt : Type := mkElt { a : nat ; b : nat }.

(** Record with a concrete-element list field, like ppm_value's [triples]. *)
Record rec : Type := mkRec { items : list elt }.

Inductive terminal := TNat.
Inductive nonterminal := Doc | Items.

Definition t_semty (a : terminal) : Type := match a with TNat => nat end.
Definition nt_semty (x : nonterminal) : Type :=
  match x with
  | Doc   => rec
  | Items => list elt
  end.

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

(* Mirrors PPM's Document -> [ ... NT Triples ] (record ctor forwarding the
   erased list leaf) and Triples -> [] / [NAT NT Triples]. *)
Definition entries : list grammar_entry :=
  [ @existT _ _
      (Doc, [NT Items])
      (fun tup => match tup with (ts, _) => true end,
       fun tup => match tup with (ts, _) => mkRec ts end)
  ; @existT _ _
      (Items, [])
      (fun _ => true,
       fun _ => @nil elt)
  ; @existT _ _
      (Items, [T TNat; NT Items])
      (fun _ => true,
       fun tup => match tup with (n, (ts, _)) => mkElt n n :: ts end)
  ].

Definition num_entries (u : unit) : nat := List.length entries.
Crane Extraction "grammar_record_list_field" num_entries entries.
