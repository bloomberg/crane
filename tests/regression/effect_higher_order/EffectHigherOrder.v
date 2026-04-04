(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Tests higher-order functions with effectful callbacks and effect
   operations used in complex type-level interactions.
*)
From Corelib Require Import PrimString PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.Env.
Local Open Scope pstring_scope.

Module EffectHigherOrder.

  Definition myE := ioE +' envE.
  Crane Extract Skip myE.

  (** 1. Higher-order function with effectful callback *)
  Definition apply_effect (f : string -> itree myE unit) (s : string) : itree myE unit :=
    f s.

  (** 2. Map-like function over a list with effects *)
  Fixpoint for_each_str (f : string -> itree myE unit)
                        (xs : list string) : itree myE unit :=
    match xs with
    | nil => Ret tt
    | cons x rest =>
      f x ;;
      for_each_str f rest
    end.

  (** 3. Callback that returns a value *)
  Definition with_line (f : string -> itree myE string) : itree myE string :=
    line <- get_line ;;
    f line.

  (** 4. Nested bind in callback *)
  Definition transform_input (f : string -> string) : itree myE string :=
    line <- get_line ;;
    Ret (f line).

  (** 5. Effectful callback passed as argument *)
  Definition greet_all (names : list string) : itree myE unit :=
    for_each_str (fun name =>
      print_endline (cat "Hello, " name)
    ) names.

  (** 6. Callback with env effect *)
  Definition lookup_or_ask (name : string) : itree myE string :=
    mv <- get_env name ;;
    match mv with
    | Some v => Ret v
    | None =>
      print_endline (cat "Enter " (cat name ":")) ;;
      line <- get_line ;;
      set_env name line ;;
      Ret line
    end.

  (** 7. Chain of lookups *)
  Fixpoint lookup_all (names : list string)
    : itree myE (list string) :=
    match names with
    | nil => Ret nil
    | cons name rest =>
      v <- lookup_or_ask name ;;
      vs <- lookup_all rest ;;
      Ret (cons v vs)
    end.

  (** 8. Effect in let-bound function *)
  Definition process_input : itree myE string :=
    let format := fun s => cat "[" (cat s "]") in
    line <- get_line ;;
    Ret (format line).

End EffectHigherOrder.

Crane Extraction "effect_higher_order" EffectHigherOrder.
