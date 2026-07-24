From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.DequeList.

(** Regression test (now fixed).  Reproduces the std::bad_any_cast the extracted
    C++ JSON parser threw on every array/object, including the empty ones "[]"
    and "{}".

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

    The PREDICATE path already did this correctly with crane_container_cast (see
    [eta_fun]'s function-argument path).  The ACTION path did NOT: extracting
    [RArr l] (where [l] is the value-dependent leaf destructured from the erased
    [ss] tuple) emitted a plain [any_cast] to a malformed target type
    [std::deque<typename R::std::any>], instead of unboxing the erased
    [std::deque<std::any>] into the constructor's concrete [std::deque<R>].

    The fix (in [src/translation.ml]) has three parts:

    1. The [MLmagic] erased-var path (used when a value-dependent leaf is coerced
       to its concrete type) unwraps the erased var to its runtime
       representation ([std::deque<std::any>]) using a NAMESPACE-COLLAPSING erase
       so a namespaced leaf like [R] becomes plain [std::any] (not the malformed
       [typename R::std::any] the shared [erase_type_to_any] produces for a
       [Tnamespace]-wrapped [Tglob]).

    2. The constructor-argument path ([gen_and_wrap]) now, when an erased leaf
       flows into a constructor field whose concrete type is a custom list with a
       NON-erased element type (e.g. [RArr]'s [std::deque<R>]), wraps the erased
       [std::deque<std::any>] in [crane_container_cast<std::deque<R>>] — mirroring
       the predicate/function path.  Inline-custom callees (e.g. [length], which
       operate on the erased container directly) are unaffected: they go through
       [eta_fun], not this path.

    3. The pattern-match field substitution ([gen_match_branch]) no longer wraps
       an erased leaf whose declared type is itself an erased alias
       ([symbol_semty = std::any]) in a spurious [any_cast<symbol_semty>] — the
       binding already holds the erased value directly, and casting a [std::any]
       holding a container to [std::any] would throw.  The guard was widened from
       [is_erased_type] to [resolves_to_any_type]. *)

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
