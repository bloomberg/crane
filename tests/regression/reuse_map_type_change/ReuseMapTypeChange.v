From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Set Crane NonAtomicRc.
Set Crane Reuse.

(** Reuse bug: the Perceus reuse pass recycles a cell of the *input* type to
    build a value of the *output* type.

    For a type-changing [map : (A -> B) -> lst A -> lst B], the cons arm
    rebuilds [lst B] while the recycled cell belongs to [lst A], so codegen
    emits

      return lst<T2>::cons__reuse(std::move(std::get<1>(l.v_mut()).a1), ...)
                                  ^ crane::rc<lst<T1>>, parameter wants
                                    crane::rc<lst<T2>>

    and clang rejects it ("no viable conversion"). The types are not merely
    inconvenient: [lst<A>] and [lst<B>] have different size, alignment and
    destructor, so constructing one in the other's storage would be undefined
    behaviour even if the token were castable. The reuse candidate search
    never checks that the matched inductive and the rebuilt constructor agree
    on their type arguments.

    [go1] (A = B = nat) compiles, so the failure needs a map that actually
    changes the element type. Removing [Set Crane Reuse.] makes the file
    compile. *)

Module ReuseMapTypeChange.

Inductive lst (A : Type) : Type :=
| nil : lst A
| cons : A -> lst A -> lst A.
Arguments nil {A}.
Arguments cons {A} _ _.

Fixpoint build (n : nat) (acc : lst nat) : lst nat :=
  match n with O => acc | S m => build m (cons n acc) end.

Fixpoint suml (l : lst nat) : nat :=
  match l with nil => 0 | cons x t => x + suml t end.

Fixpoint mapl {A B : Type} (f : A -> B) (l : lst A) : lst B :=
  match l with nil => nil | cons x t => cons (f x) (mapl f t) end.

(* same element type: fine *)
Definition go1 (n : nat) : nat := suml (mapl (fun x => x + 1) (build n nil)).

(* nat -> lst nat, then back: the type-changing instantiations *)
Definition go2 (n : nat) : nat :=
  suml (mapl (fun (p : lst nat) => suml p)
             (mapl (fun x => cons x (cons x nil)) (build n nil))).

End ReuseMapTypeChange.

Crane Extraction "reuse_map_type_change" ReuseMapTypeChange.
