(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Settling the constraints of callable template parameters.

    A callable parameter leaves translation typed by its declaration
    ({!Cpp_ir.Grammar.Parameter_kind.Callable_declared}).  Whether it keeps
    a constraint, and which, depends on what the finished body does with
    it, so it is decided here, with the body in hand. *)

(** [settle decl] decides, everywhere in [decl], which callable template
    parameters keep a constraint, and demotes the rest to a plain
    [typename]:
    {ul
    {- one the body only erases into storage has no representation to claim
       -- [crane_erase_fn] adapts whatever it is handed.  The body decides
       this, so it is decided on the definition, before its declaration is
       split off, and both state the same head;}
    {- one whose constraint is vacuous claims nothing either: a rank-2
       callback's result is [std::any] standing in for a type the body
       chooses;}
    {- every other states the body's own calls
       ({!Cpp_ir.Grammar.Parameter_kind.Invocable}), or nothing when they
       cannot be read exactly.}}
    No {!Cpp_ir.Grammar.Parameter_kind.Callable_declared} survives. *)
val settle : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
