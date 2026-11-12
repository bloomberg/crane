(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Numeral literals: a registered numeral converter applied to a digit
    chain, decided here once, and written into Core as the literal
    ([Miniml.MLnumeral]) it computes, so that no later pass reads the
    chain. *)

(** [registered_constructor name r]: [r]'s 1-based constructor index, where
    [r] is a constructor of the inductive Rocq registers as [name]
    ([num.pos.type], [num.uint.type], ...).  Digit chains and binary
    numerals are read by constructor index, which only means anything once
    the inductive is known. *)
val registered_constructor : string -> Names.GlobRef.t -> int option

(** [converter_literal r arg]: the numeral mapping and the value of the
    converter [r] (a registered one, see {!Table.extract_numeral}) applied to
    the digit chain [arg], a [Number.uint] or a [Number.int], where it is
    one.  The one place both Core, which writes the application as the
    literal ({!fold}), and dependency collection, which then leaves the
    converter and its digit inductives out, decide that it folds. *)
val converter_literal : Names.GlobRef.t -> Miniml.ml_ast -> (Table.numeral_info * Z.t) option

(** [fold e]: [e], where it is the application of a numeral converter to a
    digit chain ({!converter_literal}), as the literal it computes, at the
    converter's numeral inductive; otherwise [e] itself.  Reads [e]'s head
    node only. *)
val fold : Miniml.ml_ast -> Miniml.ml_ast

(** Whether [e]'s head node is an application {!fold} writes as a
    literal. *)
val folds : Miniml.ml_ast -> bool
