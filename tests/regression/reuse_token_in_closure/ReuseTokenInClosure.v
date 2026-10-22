(* A reuse arm whose body builds the rebuilt constructor somewhere other
   than where it returns one.

   The arm's token -- the cell the match frees -- went to whichever
   construction of the constructor translation reached first, and the
   arguments of the returned [cons] are reached before it.  In [g] that is
   the [cons] inside the closure handed to [twice]; translating the closure
   restored the context it started from, token included, so the returned
   [cons] took the token as well:

     return lst::cons_crane_reuse(
         std::move(std::get<typename lst::Cons>(l.v_mut()).a1),
         twice([=](uint64_t y) {
                 return suml(lst::cons_crane_reuse(
                     std::move(std::get<typename lst::Cons>(l.v_mut()).a1),
                     y, t)); }, ...), g(t));

     error: 'this' argument to member function 'v_mut' has type
            'const ReuseTokenInClosure::lst', but function is not marked
            const

   -- and, had it compiled, the closure, run twice, would have moved the
   token twice.  In [h] the token went to the temporary [cons x nil] that
   [suml] consumes, not to the [cons] returned.

   The plan now names the constructions that take the token: those of the
   rebuilt constructor the arm returns, one per path. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Set Crane NonAtomicRc.
Set Crane Reuse.

Module ReuseTokenInClosure.
  Inductive lst : Type := nil : lst | cons : nat -> lst -> lst.

  Fixpoint suml (l : lst) : nat := match l with nil => 0 | cons x t => x + suml t end.

  Definition twice (f : nat -> nat) (x : nat) : nat := f (f x).

  Fixpoint g (l : lst) : lst :=
    match l with
    | nil => nil
    | cons x t => cons (twice (fun y => suml (cons y t)) x) (g t)
    end.

  Fixpoint h (l : lst) : lst :=
    match l with
    | nil => nil
    | cons x t => cons (suml (cons x (cons x nil))) (h t)
    end.

  Fixpoint upto (n : nat) : lst := match n with O => nil | S k => cons n (upto k) end.
End ReuseTokenInClosure.

Crane Extraction "reuse_token_in_closure" ReuseTokenInClosure.
