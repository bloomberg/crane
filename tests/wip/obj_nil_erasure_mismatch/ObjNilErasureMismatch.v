From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.DequeList.

(** Minimal, standalone reproduction of a Crane erasure bug found while
    parsing real JSON with the extracted C++ LL parser (rocq-parse-a-lot):
    JSON's grammar has a nonterminal [Obj] (and [Pairs]) of type
    [list (string * json_value)], built by two productions:
      - a "cons" production: [pr :: prs]
      - a "nil" production (empty right-hand side): [[]]
    Both productions' actions live together in a *heterogeneous* list
    (a [list (sigT (fun sym => unit -> semty sym))], mirroring the parser's
    grammar_entry list, where each entry's action return type depends on
    which nonterminal symbol it belongs to). Because the codomain varies
    per entry, Crane erases every action's return value to [std::any].

    For [list (nat * nat)]-typed actions, the "cons" case erases to a
    [std::deque<std::any>] (each pair wrapped individually as [any]), but
    the "nil" case ([[]]) erases directly to a
    [std::deque<std::pair<std::any, std::any>>] instead -- a different C++
    type for the *same* Coq type. Any caller that [std::any_cast]s the nil
    case's value using the shape established by the cons case (as JSON's
    parser does) gets a [std::bad_any_cast] at runtime. *)

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
