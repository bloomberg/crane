From Crane Require Extraction.
From Crane Require Import Mapping.NatIntStd.
From Stdlib Require Import BinPos.

(** A helper lifted out of a module member's initialiser is defined after the
    struct it came out of, so its call site -- the initialiser, which is not a
    complete-class context -- names it before it is declared: "use of
    undeclared identifier '_shifted_F'".

    The declaration belongs at the top of the file, above every definition.
    Two members so that the pair exercises the claim table that decides which
    emission path owns a lifted helper; one alone does not distinguish them. *)

Module LiftedHelperInMemberInit.
  Definition shifted : bool * positive :=
    (false, nat_rect (fun _ => positive) xH (fun _ r => xO r) 4).

  Definition doubled : bool * positive :=
    (true, nat_rect (fun _ => positive) xH (fun _ r => xI r) 3).
End LiftedHelperInMemberInit.

Crane Extraction "lifted_helper_in_member_init" LiftedHelperInMemberInit.
