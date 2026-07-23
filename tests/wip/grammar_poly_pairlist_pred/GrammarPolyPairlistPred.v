From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List Ascii String.
Import ListNotations.

(** Repro of the LAST residual leaf-forward shape after grammar_tuple_record_cons
    was fixed (PPM.h now 0 errors; only JSON.h's nodupKeys remains, 2 errors:
    JSON.h:660 "no matching function for call to 'nodupKeys'" /
    "candidate template ignored: could not match 'std::string' against 'std::any'").

    JSON's (Value, [NT Obj]) production PREDICATE forwards its erased
    [list (string * json_value)] leaf (nt_semty Obj) into [nodupKeys], which in
    Coq is POLYMORPHIC: [nodupKeys {A} (prs : list (string * A)) : bool] -> Crane
    emits a C++ FUNCTION TEMPLATE
    [template<typename T1> bool nodupKeys(const std::deque<std::pair<std::string, T1>>&)].
    The erased leaf is any_cast to [std::deque<std::pair<std::any, std::any>>], but
    the template parameter is [deque<pair<string, T1>>] -- the KEY is concretely
    [std::string], not [std::any] -> template argument deduction fails. The sibling
    ACTION [JAssoc prs] compiles because [Json_value::jassoc]'s fully-concrete
    signature gives Crane a type to cast toward (real JSON.h emits
    [any_cast<deque<pair<string,Json_value>>>] there); the polymorphic predicate
    callee has no concrete element type to cast toward, so Crane emits a wrong
    outer any_cast for the [nodupKeys] argument.

    Root defect = wrong/missing any_cast type when an erased CONTAINER
    (deque<pair<...>>) is forwarded into a POLYMORPHIC/template function.
    NOTE ON FIDELITY: the real (separate/functor) extraction degrades the bad
    outer cast to a clean redundant [deque<pair<any,any>>] (hence the
    "string vs any" template error). This minimal FLAT single-file extraction
    degrades it slightly differently, to [deque<pair<any, typename Val::std::any>>]
    (an extra "no member named 'std' in 'Val'" render artifact) -- same root
    cause (Crane cannot compute the element type for the template callee), just a
    messier fallback. The primary "could not match 'std::string' against
    'std::any'" error on the [nodupKeys] call is identical to real JSON.h:660. *)

Crane Extract Inductive Ascii.ascii => "char"
  [ "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))" ]
  "bool %b0a0 = %scrut & 1; bool %b0a1 = (%scrut >> 1) & 1; bool %b0a2 = (%scrut >> 2) & 1; bool %b0a3 = (%scrut >> 3) & 1; bool %b0a4 = (%scrut >> 4) & 1; bool %b0a5 = (%scrut >> 5) & 1; bool %b0a6 = (%scrut >> 6) & 1; bool %b0a7 = (%scrut >> 7) & 1; %br0"
  From "".

Crane Extract Inductive String.string => "std::string"
  [ "std::string()"
    "std::string(1, %a0) + %a1" ]
  "if (%scrut.empty()) { %br0 } else { char %b1a0 = %scrut[0]; std::string %b1a1 = %scrut.substr(1); %br1 }"
  From "string".

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

(* Replicates json_value (7 ctors, recursive incl. assoc-list). *)
Inductive val :=
| VAssoc  : list (string * val) -> val
| VBool   : bool -> val
| VFloat  : nat -> val
| VInt    : nat -> val
| VList   : list val -> val
| VNull   : val
| VStr    : string -> val.

(* POLYMORPHIC in the value type -- mirrors JSON.v's nodupKeys {A}. *)
Definition nodupKeys {A : Type} (prs : list (string * A)) : bool :=
  match prs with
  | [] => true
  | _ => false
  end.

Inductive terminal := TSTRING.
Inductive nonterminal := Value | Obj.

Definition t_semty (a : terminal) : Type := match a with TSTRING => string end.
Definition nt_semty (x : nonterminal) : Type :=
  match x with
  | Value => val
  | Obj   => list (string * val)
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

(* Mirrors JSON's (Value, [NT Obj]): predicate = nodupKeys prs (polymorphic,
   pair-list leaf); action = VAssoc prs (concrete constructor, forwards leaf). *)
Definition entries : list grammar_entry :=
  [ @existT _ _
      (Value, [NT Obj])
      (fun tup => match tup with (prs, _) => nodupKeys prs end,
       fun tup => match tup with (prs, _) => VAssoc prs end)
  ; @existT _ _
      (Value, [T TSTRING])
      (fun _ => true,
       fun tup => match tup with (s, _) => VStr s end)
  ].

Definition num_entries (u : unit) : nat := List.length entries.
Crane Extraction "grammar_poly_pairlist_pred" num_entries entries.
