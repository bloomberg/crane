From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

(** A class with several [Type]-valued fields, reached through a second class
    that holds it as a promoted dictionary field.  Each associated type must
    keep its own name at a use site; they all collapse onto the last one. *)
Class Prov := {
  provenance : Type;
  allocationId : Type;
  prov : Type;
  prov_size : prov -> nat;
}.

Class Params := {
  PROV :: Prov;
  width : nat;
}.

Module PromotedVarCollapse.
  Section S.
    Context `{Params}.

    Definition takes_three (a : allocationId) (p : prov) (ps : list prov)
                           (n : nat) : nat := n + width.
  End S.
End PromotedVarCollapse.

Crane Extraction "promoted_var_collapse" PromotedVarCollapse.
