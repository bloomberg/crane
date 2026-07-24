From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.DequeList.

(** Reproduces the std::bad_any_cast the extracted C++ JSON parser still throws
    on every array/object, including the empty ones "[]" and "{}".

    Root cause (verified in the real generated JSON.h): a semantic ACTION of
    type [symbols_semty gamma -> nt_semty x], where
       symbols_semty gamma := tuple (List.map symbol_semty gamma)
       symbol_semty (NT x)  := nt_semty x
    is erased to std::any. A nonterminal whose semty is a list (here
    [NArr : list R], like JSON's Arr : list json_value) is built by its nil
    action as an erased std::deque<std::any>. When the consuming action feeds
    that erased list to a constructor taking a CONCRETE list
    ([RArr : list R -> R], mirroring json_value's JList : list json_value ->
    json_value), Crane must convert std::deque<std::any> -> std::deque<R>.

    The PREDICATE path does this correctly with crane_container_cast (see the
    real JSON.h nodupKeys predicate, which emits crane_container_cast<...>).
    The ACTION path does NOT: in the real JSON parser it emits
       std::any_cast<std::deque<Json_value>>(std::any_cast<std::deque<std::any>>(vs))
    whose OUTER any_cast is applied to an already-unwrapped std::deque<std::any>
    -> std::bad_any_cast at runtime. In this minimal repro the same defective
    action path generates an invalid conversion from std::deque<std::any> to the
    constructor's concrete std::deque<R> (and a malformed target type
    std::deque<typename R::std::any>) for the [NVal -> NT NArr] action. *)

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

Inductive R :=
| RArr : list R -> R      (* like JList : list json_value -> json_value *)
| RNum : nat -> R.

Inductive terminal := TDummy.
Inductive nonterminal := NArr | NVal.

Definition t_semty (a : terminal) : Type :=
  match a with TDummy => unit end.
Definition nt_semty (x : nonterminal) : Type :=
  match x with
  | NArr => list R
  | NVal => R
  end.

Inductive symbol :=
| T  : terminal    -> symbol
| NT : nonterminal -> symbol.

Definition symbol_semty (s : symbol) : Type :=
  match s with
  | T a  => t_semty a
  | NT x => nt_semty x
  end.

Definition symbols_semty (gamma : list symbol) : Type :=
  tuple (List.map symbol_semty gamma).

Definition production := (nonterminal * list symbol)%type.
Definition predicate_semty (p : production) : Type :=
  let (_, ys) := p in symbols_semty ys -> bool.
Definition action_semty (p : production) : Type :=
  let (x, ys) := p in symbols_semty ys -> nt_semty x.
Definition production_semty (p : production) : Type :=
  predicate_semty p * action_semty p.

Definition grammar_entry := sigT production_semty.

(** Minimal grammar isolating the container conversion:
    - NArr -> []        (nil):  builds the empty [list R] -> erased deque<any>
    - NVal -> NT NArr   (JList): applies RArr to that erased list leaf. *)
Definition entries : list grammar_entry :=
  [ existT production_semty (NArr, [])
      ( (fun _ => true)
      , (fun (_ : symbols_semty []) => @nil R) )
  ; existT production_semty (NVal, [NT NArr])
      ( (fun _ => true)
      , (fun (ss : symbols_semty [NT NArr]) =>
           match ss with (l, _) => RArr l end) )
  ].

Crane Extraction "action_container_cast" entries.
