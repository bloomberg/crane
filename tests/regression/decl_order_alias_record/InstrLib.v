From Stdlib Require Import List.

(* An enum used by a parameterised inductive, an alias of one instance of
   it, and a record holding a list of the alias. *)

Inductive cop := CEq | CLt.

Inductive instr (target : Type) :=
| IGo   : target -> instr target
| ICmp  : cop -> instr target
| IStop : instr target.
Arguments IGo {target}. Arguments ICmp {target}. Arguments IStop {target}.

Definition final_instr := instr nat.

Record prog := { code : list final_instr; nregs : nat }.
