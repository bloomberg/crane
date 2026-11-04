From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import List Ascii String.
Import ListNotations.

(** A container cast into a callee generic over the element, over a list
    mapped with a [Boxed Element] wrapper.

    [val] recurses through [list], so [list (string * val)] is
    [crane::list<crane::box<std::pair<std::string, Val>>>] wherever it is
    written.  The predicate below hands an erased [list (string * val)] to
    [nodupKeys], a function template over [list (string * A)] whose own
    declaration never boxes its element (a bare type variable never recurses).
    The cast that recovers the argument must therefore name the element
    unboxed, as the declaration does, or template argument deduction fails;
    the action hands the same leaf to [VAssoc]'s concrete factory, whose cast
    keeps the box.  [run_entry] and [action_size] run both. *)
Module BoxedElementContainerCast.

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

Inductive val :=
| VAssoc : list (string * val) -> val
| VList : list val -> val
| VNull : val
| VStr : string -> val.

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
  | Obj => list (string * val)
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

Definition sample_t (a : terminal) : t_semty a :=
  match a with TSTRING => "s"%string end.
Definition sample_nt (x : nonterminal) : nt_semty x :=
  match x with
  | Value => VNull
  | Obj => [("k"%string, VNull); ("l"%string, VNull)]
  end.
Definition sample_symbol (s : symbol) : symbol_semty s :=
  match s with T a => sample_t a | NT x => sample_nt x end.
Fixpoint sample_symbols (ys : list symbol) : symbols_semty ys :=
  match ys with
  | [] => tt
  | y :: ys' => (sample_symbol y, sample_symbols ys')
  end.

Definition run_entry (e : grammar_entry) : bool :=
  match e with
  | existT _ (_, ys) (pr, _) => pr (sample_symbols ys)
  end.

Definition size_of (x : nonterminal) : nt_semty x -> nat :=
  match x return nt_semty x -> nat with
  | Value => fun v => match v with VAssoc l => List.length l | VStr _ => 100 | _ => 0 end
  | Obj => fun l => List.length l
  end.

Definition action_size (e : grammar_entry) : nat :=
  match e with
  | existT _ (x, ys) (_, act) => size_of x (act (sample_symbols ys))
  end.

Definition predicates : list bool := map run_entry entries.
Definition action_sizes : list nat := map action_size entries.

End BoxedElementContainerCast.

Crane Extract Inductive Ascii.ascii => "char"
  [ "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))" ]
  "bool %b0a0 = %scrut & 1; bool %b0a1 = (%scrut >> 1) & 1; bool %b0a2 = (%scrut >> 2) & 1; bool %b0a3 = (%scrut >> 3) & 1; bool %b0a4 = (%scrut >> 4) & 1; bool %b0a5 = (%scrut >> 5) & 1; bool %b0a6 = (%scrut >> 6) & 1; bool %b0a7 = (%scrut >> 7) & 1; %br0"
  From "".

Crane Extract Inductive String.string => "std::string"
  [ "std::string()"
    "std::string(1, %a0) + %a1" ]
  "if (%scrut.empty()) { %br0 } else { char %b1a0 = %scrut[0]; std::string %b1a1 = %scrut.substr(1); %br1 }"
  From "string".

Crane Extract Inductive list =>
  "crane::list<%elem>"
  [ "crane::list<%elem>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  From "conslist.h".

Crane Extraction "boxed_element_container_cast" BoxedElementContainerCast.
