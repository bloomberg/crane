From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module TmcNestedCtorWrap.

(** [spine] is tail-modulo-cons, but the constructor that wraps the recursive
    call is nested: [rnode] takes a [list rose], so the recursive result sits
    under a [cons] of a *different* inductive.  Loopification builds the cell
    for the wrong type:

      auto _cell = std::make_shared<rose>(typename rose::Rnode(nullptr));
      auto _cell1 = std::make_shared<rose>(typename List<rose>::Cons(...));

    error: no viable conversion from 'std::nullptr_t' to 'rose'
    error: incompatible pointer types assigning to 'std::shared_ptr<rose> *'
           from 'rose *' *)
Inductive rose : Type := rnode : list rose -> rose.

Fixpoint rsize (r : rose) : nat :=
  match r with
  | rnode l => S (fold_left (fun acc c => acc + rsize c) l 0)
  end.

Fixpoint spine (n : nat) : rose :=
  match n with
  | O => rnode nil
  | S k => rnode (cons (spine k) nil)
  end.

End TmcNestedCtorWrap.

Crane Loopify TmcNestedCtorWrap.spine.
Crane Extraction "tmc_nested_ctor_wrap" TmcNestedCtorWrap.rsize TmcNestedCtorWrap.spine.
