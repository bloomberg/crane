From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.DequeList.

(** Regression test (now fixed).  Minimal, standalone reproduction of a Crane
    erasure bug found while parsing real JSON with the extracted C++ LL parser
    (rocq-parse-a-lot): JSON's grammar has a nonterminal [Obj] (and [Pairs]) of
    type [list (string * json_value)], built by two productions:
      - a "cons" production: [pr :: prs]
      - a "nil" production (empty right-hand side): [[]]
    Both productions' actions live together in a *heterogeneous* list
    (a [list (sigT (fun sym => unit -> semty sym))], mirroring the parser's
    grammar_entry list, where each entry's action return type depends on
    which nonterminal symbol it belongs to). Because the codomain varies
    per entry, Crane erases every action's return value to [std::any].

    The bug: for [list (nat * nat)]-typed actions, the "cons" case (built from
    concrete pair values) stayed concretely typed ([std::deque<Prod<Nat,Nat>>])
    while the "nil" case ([[]], whose element type is already opaque in the ML
    annotation) erased to [std::deque<Prod<std::any,std::any>>] -- a different
    C++ type for the *same* Coq type. Any caller that [std::any_cast]s the nil
    case's value using the shape established by the cons case (as JSON's parser
    does) got a [std::bad_any_cast] at runtime.

    The fix (in [src/translation.ml]): a lambda stored into an abstract
    type-variable constructor field (the predicate [P] of [sigT A P],
    instantiated to the value-dependent action type [unit -> semty s]) now has
    its body generated with [wrap_for_any_param] set (see
    [field_stores_erased_fn_value]).  That flag makes the body's list/pair/
    record producers deep-erase to a single canonical C++ representation
    ([std::deque<std::any>], each element a [std::any] holding a
    [Prod<std::any,std::any>]), so the cons and nil productions of the same
    nonterminal agree and a single [any_cast] shape works for both.

    Two supporting changes were needed: (1) plain value-type constructors
    (like the regular [Prod] struct -- [prod] is not custom-extracted here)
    now erase their factory type arguments under [wrap_for_any_param], mirroring
    the custom-list element erasure; and (2) the erasure uses a
    namespace-collapsing helper so a namespaced leaf like [Nat] becomes plain
    [std::any] rather than the malformed [typename Nat::std::any] the shared
    [erase_type_to_any] would produce.

    The directly-callable [top_cons_action]/[top_nil_action] copies keep their
    concrete [std::deque<Prod<Nat,Nat>>] type: their return type is declared
    concretely ([list (nat*nat)]), so no value-dependent erasure applies. *)

Inductive Sym := TOPSYM | PAIRSYM | PAIRSSYM.

Definition semty (s : Sym) : Type :=
  match s with
  | TOPSYM   => list (nat * nat)
  | PAIRSYM  => (nat * nat)%type
  | PAIRSSYM => list (nat * nat)
  end.

Definition entries : list (sigT (fun s : Sym => unit -> semty s)) :=
  [ existT (fun s : Sym => unit -> semty s) PAIRSYM  (fun (_ : unit) => (5, 6) : semty PAIRSYM)
  ; existT (fun s : Sym => unit -> semty s) PAIRSSYM (fun (_ : unit) => ((1, 2) :: (3, 4) :: nil) : semty PAIRSSYM)
  ; existT (fun s : Sym => unit -> semty s) PAIRSSYM (fun (_ : unit) => (@nil (nat * nat)) : semty PAIRSSYM)
  ; existT (fun s : Sym => unit -> semty s) TOPSYM   (fun (_ : unit) => ((7, 8) :: nil) : semty TOPSYM)
  ; existT (fun s : Sym => unit -> semty s) TOPSYM   (fun (_ : unit) => (@nil (nat * nat)) : semty TOPSYM)
  ].

(** Directly-callable copies of the two [TOPSYM]-shaped actions, so the C++
    test driver can invoke the "cons" and "nil" cases individually and
    observe the mismatched erased shapes. *)
Definition top_cons_action (_ : unit) : list (nat * nat) := (7, 8) :: nil.
Definition top_nil_action  (_ : unit) : list (nat * nat) := nil.

Crane Extraction "obj_nil_erasure_mismatch" entries top_cons_action top_nil_action.
