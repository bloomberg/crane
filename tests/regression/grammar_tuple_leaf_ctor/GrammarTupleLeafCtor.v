From Crane Require Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Stdlib Require Import List Ascii String.
Import ListNotations.

(** FAITHFUL repro of the parse-a-lot grammar's residual leaf-forward bug
    (now fixed).

    Every prior repro (sigt_leaf_forward_{string,topfn,dispatcher,ctor},
    sigt_leaf_list_dispatch, ...) approximated the RHS-values domain type
    with a DIRECT [match n with 0 => (string*unit) | _ => (nat*unit)]. Crane
    can partially see through such a direct match, so the fixes made for those
    repros never transferred to the real grammar. The REAL domain
    (theories/Parser/Defs.v:318) is
      [symbols_semty gamma := tuple (List.map symbol_semty gamma)]
    i.e. a FIXPOINT ([tuple], Utils.v:378) applied to a MAPPED list
    ([List.map symbol_semty gamma]), where [symbol_semty] dispatches through
    [t_semty]/[nt_semty]. Crane does NOT reduce [tuple (map symbol_semty ys)]
    to a concrete nested [prod ... unit] at translation time even when [ys] is
    a concrete literal -- it erases the whole thing to [std::any]. THAT is what
    forces the generic [crane_erase_fn([](const auto &tup){...})] lambda whose
    body destructures via [any_cast<pair<any,any>>] and then forwards a leaf
    (still [std::any]) into a concrete constructor.

    The fix: the value-type constructor argument path
    ([gen_and_wrap]/[gen_ctor_arg], translation.ml) now threads the field's
    CONCRETE C++ type as the expected type when the argument is an erased
    ([std::any]) pattern variable, so the leaf gets a final
    [any_cast<concrete>] before entering the factory (e.g.
    [Val::vstr(any_cast<string>(s))]).  Previously only the plain
    function-call path inserted that cast, so [wrap_string v] worked but a
    constructor forward [VStr s] did not.

    This repro mirrors examples/JSON/Parser/JSON.v byte-for-byte in structure:
    [tuple (map symbol_semty gamma)] domain, action returning [nt_semty x] via
    a constructor application ([VStr s] mirrors [JString s]), entries built as
    inline [@existT _ _ (nt, symbol_list) (pred, action)] literals in a
    [list grammar_entry], defined after everything is concrete. *)

Crane Extract Inductive Ascii.ascii => "char"
  [ "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))" ]
  "bool %b0a0 = %scrut & 1; bool %b0a1 = (%scrut >> 1) & 1; bool %b0a2 = (%scrut >> 2) & 1; bool %b0a3 = (%scrut >> 3) & 1; bool %b0a4 = (%scrut >> 4) & 1; bool %b0a5 = (%scrut >> 5) & 1; bool %b0a6 = (%scrut >> 6) & 1; bool %b0a7 = (%scrut >> 7) & 1; %br0"
  From "".

Crane Extract Inductive String.string => "std::string"
  [ "std::string()"
    "std::string(1, %a0) + %a1" ]
  "if (%scrut.empty()) { %br0 } else { char %b1a0 = %scrut[0]; std::string %b1a1 = %scrut.substr(1); %br1 }"
  From "string".

(* Mirror Utils.tuple exactly. *)
Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

(* Concrete terminals/nonterminals, as in the JSON instantiation. *)
Inductive terminal := TSTRING | TINT.
Inductive nonterminal := Value.

(* Result inductive with constructors taking the leaf (mirrors json_value/JString). *)
Inductive val := VStr : string -> val | VInt : nat -> val.

Definition t_semty (a : terminal) : Type :=
  match a with TSTRING => string | TINT => nat end.
Definition nt_semty (x : nonterminal) : Type :=
  match x with Value => val end.

Inductive symbol := T : terminal -> symbol | NT : nonterminal -> symbol.
Definition symbol_semty (s : symbol) : Type :=
  match s with T a => t_semty a | NT x => nt_semty x end.

(* The essential ingredient: domain is tuple over a mapped list, NOT a direct match. *)
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

(* Entries mirror jsonGrammarEntries: action returns nt_semty via a constructor
   application forwarding the destructured leaf (VStr s mirrors JString s). *)
Definition entries : list grammar_entry :=
  [ @existT _ _
      (Value, [T TSTRING])
      (fun _ => true,
       fun tup => match tup with (s, _) => VStr s end)
  ; @existT _ _
      (Value, [T TINT])
      (fun _ => true,
       fun tup => match tup with (i, _) => VInt i end)
  ].

Definition num_entries (u : unit) : nat := List.length entries.
Crane Extraction "grammar_tuple_leaf_ctor" num_entries entries.
