From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List.
From CraneTestsRegression Require Import decl_order_alias_record.InstrLib.
Import ListNotations.

(**
  A record holding a list of an alias of a parameterised inductive, where the
  inductive depends on an enum declared before it.

  The header must declare [struct Instr] and [using final_instr] before
  [struct prog]. Crane used to emit [struct prog] first ("use of undeclared
  identifier 'final_instr'"): it placed a whole Kahn layer of inductives per
  round, which moved [instr] behind [prog], and it did not follow [prog]'s
  dependency on [instr] through the alias.
*)

Definition sample : prog :=
  {| code := [IGo 3; ICmp CEq; IStop]; nregs := 2 |}.

Definition sample_size : nat := length (code sample).

Definition sample_regs : nat := nregs sample.

Crane Extraction "decl_order_alias_record" sample_size sample_regs.
