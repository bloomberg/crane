From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List String.
Import ListNotations.

(** Reproduces a std::bad_any_cast thrown by the extracted C++ JSON parser on
    ANY non-empty object (e.g. {"a":1}), while {} succeeds. Root cause: for a
    nonterminal typed [list (string * T)] (JSON's [Pairs]), the NIL production
    ([Pairs, []] -> []) and the CONS production ([Pairs, [COMMA; Pair; Pairs]]
    -> pr :: prs) erase to two DIFFERENT runtime container shapes:

      nil  emits: std::deque<std::pair<std::any, std::any>>{}   (* concrete-pair elements *)
      cons emits: std::deque<std::any>{ any(pr), ... }          (* any-wrapped elements *)

    The consuming action ([Obj]'s [pr :: prs] -> [jassoc prs]) always unwraps
    via the CONS shape:
      crane_container_cast<deque<pair<string,Val>>>(
        any_cast<deque<pair<any,any>>>(
          any_cast<deque<pair<any,any>>>(prs)))
    which matches the NIL production's shape exactly (so {} works) but throws
    std::bad_any_cast whenever the actual runtime value came from the CONS
    production instead (any non-empty object).

    This is a narrower recurrence of the earlier obj_nil_erasure_mismatch bug:
    that fix aligned nil/cons erasure for PLAIN-element lists ([list T]), but a
    list whose element type is itself a PAIR/tuple ([list (T1 * T2)]) still
    hits the same nil/cons shape mismatch.

    Mirrors JSON.v's:
      Obj   -> [T LEFT_BRACE; NT Pair; NT Pairs; T RIGHT_BRACE], action: pr :: prs
      Obj   -> [T LEFT_BRACE; T RIGHT_BRACE], action: []
      Pairs -> [T COMMA; NT Pair; NT Pairs], action: pr :: prs
      Pairs -> [], action: []
      Pair  -> [T STRING; T COLON; T NAT], action: (s, v) *)

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

(* Concrete record standing in for json_value's VAssoc/jassoc factory. *)
Record val : Type := mkVal { pairs : list (string * nat) }.

Inductive terminal := LBRACE | RBRACE | COMMA | COLON | STR | NAT.
Inductive nonterminal := Doc | Obj | Pair | Pairs.

Definition t_semty (a : terminal) : Type :=
  match a with
  | STR => string
  | NAT => nat
  | _   => unit
  end.
Definition nt_semty (x : nonterminal) : Type :=
  match x with
  | Doc   => val
  | Obj   => list (string * nat)
  | Pair  => string * nat
  | Pairs => list (string * nat)
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
      (Doc, [NT Obj])
      (fun _ => true,
       fun tup => match tup with (prs, _) => mkVal prs end)
  ; @existT _ _
      (Obj, [T LBRACE; NT Pair; NT Pairs; T RBRACE])
      (fun _ => true,
       fun tup =>
         match tup with
         | (_, (pr, (prs, (_, _)))) => pr :: prs
         end)
  ; @existT _ _
      (Obj, [T LBRACE; T RBRACE])
      (fun _ => true,
       fun _ => [])
  ; @existT _ _
      (Pairs, [T COMMA; NT Pair; NT Pairs])
      (fun _ => true,
       fun tup =>
         match tup with
         | (_, (pr, (prs, _))) => pr :: prs
         end)
  ; @existT _ _
      (Pairs, [])
      (fun _ => true,
       fun _ => [])
  ; @existT _ _
      (Pair, [T STR; T COLON; T NAT])
      (fun _ => true,
       fun tup =>
         match tup with
         | (s, (_, (n, _))) => (s, n)
         end)
  ].

Definition num_entries (u : unit) : nat := List.length entries.
Crane Extraction "grammar_pairlist_nil_cons_mismatch" num_entries entries.
