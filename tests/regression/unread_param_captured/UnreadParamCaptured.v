(** Found by Ephyra (round 21). A fold step lambda containing a local
    fixpoint that passes the function's parameter [v] as an accumulator the
    fixpoint never reads ([go rest v], [a] unused).

    Expected: compiles; [result = 3] ([go [] u = u = "abc"]).

    Fixed: compile error "use of undeclared identifier 'v'". [op]'s
    parameter was printed unnamed ([String op(String u, String)]) because
    nothing reads it once Loopify drops the unread accumulator, but the step
    lambda still captured it ([[=, u = std::move(u), v = std::move(v)]]):
    the planned moves were written as captures whether or not the final
    body read them.  A lambda now captures by move only what its body
    reads. *)
From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List String Ascii.
Import ListNotations.
Module UnreadParamCaptured.
Definition op (u v : string) : string :=
  fold_left (fun (acc : string) (e : ascii) =>
               let fix go (l : list (option nat)) (a : string) {struct l} : string :=
                 match l with [] => u | _ :: rest => go rest v end in
               go [] u) ["a"%char; "b"%char] "x"%string.
Definition result : nat := String.length (op "abc"%string "de"%string).
End UnreadParamCaptured.
Crane Extraction "unread_param_captured" UnreadParamCaptured.
