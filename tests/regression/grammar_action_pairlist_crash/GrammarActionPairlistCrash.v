From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List Ascii String.
Import ListNotations.

(** Regression test (now fixed).  RUNTIME repro: after the action_container_cast
    fix, the extracted C++ JSON parser STILL threw std::bad_any_cast on every
    array/object. The consuming ACTION emitted a redundant, WRONG middle cast:
       crane_container_cast<deque<Concrete>>(     (* correct, added by the fix *)
         any_cast<deque<Concrete>>(               (* redundant middle -- CRASHED *)
           any_cast<deque<any>>(prs)))            (* correct erased unwrap *)
    The middle any_cast<deque<Concrete>> was applied to an already-unwrapped
    deque<any> value: because std::any has an implicit converting constructor,
    that deque<any> was silently re-boxed into a fresh std::any and then
    any_cast to the concrete-element container -> the fresh any held a
    deque<pair<any,any>>, not deque<pair<string,Val>>, so it threw at runtime.
    The sibling PREDICATE survived only because its middle cast is to the ERASED
    type (a matching round-trip). See grammar_poly_pairlist_pred for the
    compile-time history; this variant exercises the crash at runtime.

    Fix (src/translation.ml, bare [MLrel] erased-var case in [gen_expr]): when an
    erased pattern-var whose runtime representation is a CUSTOM-LIST container
    (boxed as [deque<...erased...>]) is coerced toward a concrete-element
    container target ([deque<pair<string,Val>>]), unwrap it to the ERASED
    container ([any_cast<deque<pair<any,any>>>]) rather than emitting a direct
    [any_cast] to the concrete-element type.  The concrete conversion is left to
    the downstream consumer that knows the concrete field/parameter type: the
    value-type CONSTRUCTOR path ([VAssoc]) wraps it in [crane_container_cast]
    (from the action_container_cast fix), and the FUNCTION path ([nodupKeys], via
    [eta_fun]) does the same.  Scalar targets keep the direct concrete
    [any_cast].  This makes the action's middle cast the erased type — a matching
    round-trip that survives — exactly like the predicate.

    Original context:

    JSON's (Value, [NT Obj]) production PREDICATE forwards its erased
    [list (string * json_value)] leaf (nt_semty Obj) into [nodupKeys], which in
    Coq is POLYMORPHIC: [nodupKeys {A} (prs : list (string * A)) : bool] -> Crane
    emits a C++ FUNCTION TEMPLATE
    [template<typename T1> bool nodupKeys(const std::deque<std::pair<std::string, T1>>&)].
    The erased leaf is [std::deque<std::pair<std::any, std::any>>] at runtime, but
    the template parameter is [deque<pair<string, T1>>] -- the KEY is concretely
    [std::string]. Casting the argument to the fully-erased [deque<pair<any,any>>]
    made template argument deduction fail ("could not match 'std::string' against
    'std::any'"). The sibling ACTION [VAssoc prs] compiled because it goes through
    the value-type CONSTRUCTOR path, whose fully-concrete factory signature
    ([vassoc(deque<pair<string,Val>>)]) gives Crane a concrete type to cast toward.

    Fix (translation.ml, MLapp custom-list erased-arg branch): when the callee is
    a REAL function (not inline-custom) whose parameter element type has ANY
    concrete content ([et <> erase_type_to_any et]) -- an opaque wholesale-boxed
    element (deque<rgb>) OR a structural element with a concrete component
    (deque<pair<string,T1>>) -- route the erased container through
    [crane_container_cast<Dst>] toward that concrete element type instead of the
    fully-erased cast. This both makes template deduction succeed and unboxes
    wholesale-boxed elements at runtime. Inline-custom callees ([length]'s
    [.size()]) and callees whose element is already fully erased keep the erased
    container. A flat-extraction artifact that wraps a module-local inductive in a
    self-referential [Tnamespace(g, Tglob(g,..))] (rendered [typename G::...]) is
    stripped first so the concrete callee element type is well-formed. *)

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
Crane Extraction "grammar_action_pairlist_crash" num_entries entries.
