From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

(** Reproduces TWO bugs in generated C++:

    Bug A (dangling reference): Pattern-matching an erased pair generates
      const std::any &b = any_cast<pair<any,any>>(t).first;
    The temporary pair dies at the semicolon; b dangles.

    Bug B (no .first on std::any): "let tail := snd vs in fst tail" generates
      auto tail = any_cast<pair<any,any>>(vs).second;   // tail : std::any
      Ty::sym_semty b = std::move(tail).first;          // error: any has no .first
    Crane should emit any_cast<pair<any,any>>(tail).first instead. *)

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | nil => unit
  | cons x xs' => prod x (tuple xs')
  end.

Module Type SymTypes.
  Parameter sym : Type.
  Parameter sym_semty : sym -> Type.
End SymTypes.

Module Destruct (Ty : SymTypes).
  Definition symbols_semty (gamma : list Ty.sym) : Type :=
    tuple (List.map Ty.sym_semty gamma).

  (** Bug A: match destructuring generates dangling const-ref bindings *)
  Definition swap_pair
    (x y : Ty.sym) (rest : list Ty.sym)
    (vs : symbols_semty (x :: y :: rest))
    : prod (Ty.sym_semty y) (Ty.sym_semty x) :=
    match vs with
    | (a, (b, _)) => (b, a)
    end.

  (** Bug B: let-chain through snd generates .first on std::any *)
  Definition use_both
    (x y : Ty.sym) (rest : list Ty.sym)
    (vs : symbols_semty (x :: y :: rest))
    : prod (Ty.sym_semty x) (Ty.sym_semty y) :=
    let a := fst vs in
    let tail := snd vs in
    let b := fst tail in
    (a, b).
End Destruct.

Crane Separate Extraction Destruct.
