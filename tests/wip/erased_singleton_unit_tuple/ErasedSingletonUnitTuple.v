From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** Runtime bad_any_cast repro. After all the compile-time leaf-forward bugs
    were fixed, the extracted parsers COMPILE but crash at runtime with
    std::bad_any_cast during parse_*. Root cause is Crane's codegen for
    theories/Parser/Defs.v's [rev_tuple_cons_case]:
      exact (concat_tuple (rev xs') [x] (f xs' vs) (v, tt)).
    The singleton tuple [(v, tt) : symbols_semty [x]] -- where [symbols_semty
    gamma := tuple (map symbol_semty gamma)] erases to std::any and [v] is
    destructured from an erased tuple (so it is std::any) -- is emitted by Crane
    (Defs.h:340) as
      std::make_pair(s, std::monostate{})
    i.e. a [std::pair<std::any, std::monostate>]: the [tt : unit] component is
    left as a raw [std::monostate{}] instead of being erased to
    [std::any(std::monostate{})]. So the value's dynamic type is
    [pair<any, monostate>]. But every consumer of an erased [symbols_semty]
    destructures with [std::any_cast<std::pair<std::any, std::any>>(...)], which
    requires the boxed type to be EXACTLY [pair<any,any>] -> std::bad_any_cast at
    runtime (the LL parser hits this in Parser.h applying a production's
    predicate/action to the reversed RHS-values tuple [vs_ = rev_tuple ...]).

    Repro: [cons_sem] builds erased tuples correctly (generic over head symbol
    and tail list -> Crane emits make_pair(any(v), rest), a proper pair<any,any>).
    [head1] mirrors rev_tuple_cons_case's [(v, tt)]: a singleton erased tuple
    from an erased head -> Crane emits the buggy make_pair(any_v, monostate{}).
    [firstOf] is a generic consumer destructuring an erased tuple as pair<any,any>.
    [check] feeds head1's output into firstOf and throws std::bad_any_cast at
    runtime, because head1 produced pair<any,monostate> but firstOf any_casts to
    pair<any,any>. (cons_sem is used to build the input so we avoid an unrelated
    concrete-literal-to-erased coercion artifact at static-init time.) *)

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

Inductive sym := A | B.
Definition sym_semty (s : sym) : Type := match s with A => nat | B => nat end.
Definition syms_semty (g : list sym) : Type := tuple (map sym_semty g).

(* Correct erased cons: generic over head symbol x and tail list g. *)
Definition cons_sem (x : sym) (g : list sym)
                    (v : sym_semty x) (rest : syms_semty g) : syms_semty (x :: g) :=
  (v, rest).

(* Mirrors rev_tuple_cons_case's [(v, tt)]: singleton erased tuple from an
   erased head. Crane emits std::make_pair(any_v, std::monostate{}). *)
Definition head1 (g : list sym) (vs : syms_semty (A :: g)) : syms_semty [A] :=
  match vs with (v, _) => (v, tt) end.

(* Generic consumer of an erased tuple: emits any_cast<pair<any,any>>. *)
Definition firstOf (g : list sym) (t : syms_semty (A :: g)) : nat :=
  match t with (v, _) => v end.

(* Build the [A;B] tuple from a RUNTIME [n] so Crane cannot constant-fold it to a
   literal (folding triggers an unrelated any_cast<syms_semty>(literal) coercion
   artifact at static-init). cons_sem then genuinely emits make_pair(any(n), rest). *)
Definition check (n : nat) : nat :=
  firstOf [] (head1 [B] (cons_sem A [B] n (cons_sem B [] n tt))).

Crane Extraction "erased_singleton_unit_tuple" check.
