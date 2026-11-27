(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Regression test for the "erased-context unresolved type variable" codegen bug
   that blocks the default [Datatypes::List<T>] (no immer mapping).

   Faithful reduction of parse-a-lot's grammar + parser semantic-action encoding
   (theories/Parser/Defs.v + examples/JSON/Parser/JSON.v).  The key ingredient is
   that the parser ASSEMBLES a production's RHS-values tuple from a stack of
   individually-boxed ([{s & symbol_semty s}], each a bare [std::any]) semantic
   values, then applies the action.  So each tuple slot — including a list-valued
   one — is a bare [std::any], and the list-consing action must re-cast the tail
   via [any_cast<list (nt_semty elem)>], leaving the element as an unsubstituted
   type variable: the bogus, undeclared [any_cast<Datatypes::List<T1>>] inside
   the (non-template) [crane_erase_fn] lambda body.

   Uses the default [Datatypes::List<T>] (Crane's normal test config). *)

From Stdlib Require Import List.
Import ListNotations.

(* Match parse-a-lot's config: [prod] -> [std::pair], nat -> int.  The custom
   [std::pair] mapping routes pair construction through the custom-cons codegen
   path that performs the erased-context type-variable erasure (the bug site). *)
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatInt.

Module Type SYM.
  Parameter terminal nonterminal : Type.
  Parameter t_eq_dec  : forall x y : terminal,    {x = y} + {x <> y}.
  Parameter nt_eq_dec : forall x y : nonterminal, {x = y} + {x <> y}.
  Parameter t_semty  : terminal    -> Type.
  Parameter nt_semty : nonterminal -> Type.
End SYM.

Module DefsFn (Export Ty : SYM).

  Inductive symbol := T : terminal -> symbol | NT : nonterminal -> symbol.

  Definition symbol_eq_dec : forall s1 s2 : symbol, {s1 = s2} + {s1 <> s2}.
  Proof. decide equality; [apply t_eq_dec | apply nt_eq_dec]. Defined.

  Definition symbol_semty (s : symbol) : Type :=
    match s with
    | T a  => t_semty  a
    | NT x => nt_semty x
    end.

  Fixpoint tuple (xs : list Type) : Type :=
    match xs with
    | [] => unit
    | x :: xs' => (x * tuple xs')%type
    end.

  Definition production := (nonterminal * list symbol)%type.
  Definition symbols_semty (ys : list symbol) : Type := tuple (map symbol_semty ys).

  Definition predicate_semty (p : production) : Type :=
    let (_, ys) := p in symbols_semty ys -> bool.
  Definition action_semty (p : production) : Type :=
    let (x, ys) := p in symbols_semty ys -> nt_semty x.
  Definition production_semty (p : production) : Type :=
    (predicate_semty p * action_semty p)%type.

  Definition grammar_entry : Type := { p : production & production_semty p }.
  Definition grammar := list grammar_entry.

  (* A boxed semantic value on the parser's stack. *)
  Definition sem_val := { s : symbol & symbol_semty s }.

  (* Assemble a stack of boxed values into a production's RHS tuple (the parser's
     core; mirrors [cast_ss] / the value-stack folding).  Each value is boxed
     ([sem_val]) so each tuple slot is a bare [std::any]. *)
  Fixpoint assemble (ys : list symbol) (stk : list sem_val)
    : option (symbols_semty ys) :=
    match ys return option (symbols_semty ys) with
    | [] => Some tt
    | y :: ys' =>
        match stk with
        | [] => None
        | existT _ s v :: stk' =>
            match symbol_eq_dec s y with
            | left H =>
                match assemble ys' stk' with
                | Some rest => Some (eq_rect s symbol_semty v y H, rest)
                | None => None
                end
            | right _ => None
            end
        end
    end.

  Definition action_of (e : grammar_entry)
    : symbols_semty (snd (projT1 e)) -> nt_semty (fst (projT1 e)).
  Proof. destruct e as [[x ys] [pred act]]. exact act. Defined.

  (* Run an entry: assemble its RHS values from the boxed stack, then apply. *)
  Definition run_entry (e : grammar_entry) (stk : list sem_val)
    : option (nt_semty (fst (projT1 e))) :=
    match assemble (snd (projT1 e)) stk with
    | Some vs => Some (action_of e vs)
    | None => None
    end.

End DefsFn.

(* --- concrete grammar ------------------------------------------------- *)
Inductive val := VN : nat -> val | VL : list val -> val.

Module MySym <: SYM.
  Inductive term := LBRACE | RBRACE.
  Inductive nt := ELEM | LST.
  Definition terminal := term.
  Definition nonterminal := nt.
  Definition t_eq_dec  : forall x y : terminal,    {x = y} + {x <> y}.
  Proof. decide equality. Defined.
  Definition nt_eq_dec : forall x y : nonterminal, {x = y} + {x <> y}.
  Proof. decide equality. Defined.
  Definition t_semty (_ : terminal) : Type := unit.
  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | ELEM => (nat * val)%type
    | LST  => list (nat * val)
    end.
End MySym.

Module MyDefs := DefsFn MySym.
Import MyDefs MySym.

Definition entries : grammar :=
  [ @existT _ production_semty
            (LST, [T LBRACE; NT ELEM; NT LST; T RBRACE])
            (fun _ => true,
             fun tup => match tup with
                        | (_, (pr, (prs, (_, _)))) => pr :: prs
                        end) ].

Require Crane.Extraction.
Crane Extraction "erased_list_cons" MyDefs entries run_entry.
