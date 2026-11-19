(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A short, ordered list of small local simplifications on CppIR, each
    independent and each removing something:

    {ul
    {- A condition that is a literal selects its branch.}
    {- [if (c) return true; else return false;] returns [c], for a [c] that
       is a comparison or a connective, and so a [bool].}
    {- A binding of a pure value nothing reads is dropped, and so is a local
       declared without one that nothing reads, with the pure values -- a
       choice among them on pure tests included -- assigned to it.}
    {- A local copied out of a member of another, neither assigned
       afterwards, is a [const] reference to it.}
    {- A local closure whose result is applied at once, [k(a)(b)], is
       [crane::apply2(k, a, b)], which skips the closure in between; and a
       lambda that only returns a lambda returns it unboxed, so that the
       skip has something to skip.}
    {- A match on a local that is [const] where it is written borrows its
       scrutinee ({!borrow_matches_on}): one declared [const], a [const]
       reference or a pointer to [const], a field a borrowing match binds,
       or one a by-copy lambda captured -- closures are never [mutable].  A
       [const] value cannot be taken apart, whatever the ownership plan
       decided over Core; nor can a coinductive one, whose variant sits in
       a lazy cell read only through [v()].}}

    Effects and evaluation counts are kept: a mapped constant is never pure,
    so nothing its text might do is removed. *)

(** [transform_decl d]: [d] with every simplification above applied
    throughout its statements and expressions. *)
val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t

(** [borrow_matches_on ids stmts]: [stmts] with every destructive match on
    one of the locals [ids] made borrowing, and the moves out of the fields
    such a match binds dropped.  Always sound: it only copies where it could
    have moved. *)
val borrow_matches_on : Names.Id.t list -> Cpp_ir.Lowered.Stmt.t list -> Cpp_ir.Lowered.Stmt.t list
