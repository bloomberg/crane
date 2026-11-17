(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** Recursive functions where one constructor holds several recursive calls.
    Tail modulo cons can continue by only one of them, so these are lowered
    with an explicit frame stack instead, and must not overflow the C++
    stack on deep inputs. *)
Module TmcAmbiguousCalls.

(** The OCaml manual's example: the definition sits in a pair, the body is a
    direct constructor argument. *)
Inductive exp :=
| Var (v : nat)
| Let (b : nat * exp) (body : exp).

Fixpoint map_vars (f : nat -> nat) (e : exp) : exp :=
  match e with
  | Var v => Var (f v)
  | Let (v, def) body => Let (f v, map_vars f def) (map_vars f body)
  end.

(** The same with a separate binding type holding the definition. *)
Inductive binding (A : Type) := Bind (v : nat) (def : A).
Arguments Bind {A} v def.

Inductive bexp :=
| BVar (v : nat)
| BLet (b : binding bexp) (body : bexp).

Fixpoint map_bvars (f : nat -> nat) (e : bexp) : bexp :=
  match e with
  | BVar v => BVar (f v)
  | BLet (Bind v def) body => BLet (Bind (f v) (map_bvars f def)) (map_bvars f body)
  end.

(** Two recursive calls directly in one constructor. *)
Inductive tree :=
| Leaf
| Node (l : tree) (x : nat) (r : tree).

Fixpoint map_tree (f : nat -> nat) (t : tree) : tree :=
  match t with
  | Leaf => Leaf
  | Node l x r => Node (map_tree f l) (f x) (map_tree f r)
  end.

(** One branch that tail modulo cons could take alone, one with two calls. *)
Inductive term :=
| Lit (n : nat)
| Neg (t : term)
| Add (a : term) (b : term).

Fixpoint scale (k : nat) (t : term) : term :=
  match t with
  | Lit n => Lit (k * n)
  | Neg t => Neg (scale k t)
  | Add a b => Add (scale k a) (scale k b)
  end.

Fixpoint eval (t : term) : nat :=
  match t with
  | Lit n => n
  | Neg t => eval t
  | Add a b => eval a + eval b
  end.

End TmcAmbiguousCalls.

Set Crane Loopify.
Set Crane Loopify Strict.
Crane Extraction "tmc_ambiguous_calls" TmcAmbiguousCalls.
