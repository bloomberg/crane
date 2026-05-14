(* Regression: nullary definitions from a module type parameter must
   be called with () when used inside a functor in separate extraction.
   This covers the pattern seen in MSetAVL where I::_1 (a nullary
   integer constant from module type Int) is used without parentheses,
   causing type errors like:
     cannot initialize a parameter of type 'long long'
     with an lvalue of type 'const int64_t &()'
   The key distinction: the nullary definition is from a MODULE TYPE
   parameter, and the functor is used with a concrete module argument
   that defines the constant as a static function. *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.

Module Type IntLike.
  Parameter t : Type.
  Parameter zero : t.
  Parameter one : t.
  Parameter add : t -> t -> t.
  Parameter eqb : t -> t -> bool.
End IntLike.

Module NatAsIntLike <: IntLike.
  Definition t := nat.
  Definition zero := 0.
  Definition one := 1.
  Definition add := Nat.add.
  Definition eqb := Nat.eqb.
End NatAsIntLike.

Module Counter (I : IntLike).

  Definition init : I.t := I.zero.

  Definition step (x : I.t) : I.t := I.add x I.one.

  Definition is_zero (x : I.t) : bool := I.eqb x I.zero.

End Counter.

Module NatCounter := Counter NatAsIntLike.

Crane Separate Extraction Counter NatAsIntLike NatCounter.
