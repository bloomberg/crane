(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Local closures made and used in one place, rewritten as the code they
    stand for, so that what they captured is the function's own: a local a
    lambda returned through a by-reference capture then leaves the function
    by an implicit move.  The moves the closures hold were decided over Core
    and carry over unchanged.  Each rule is independent and declines unless
    every use is visible in the same body:
    {ul
    {- a lambda invoked where it is written, for an initialiser, becomes its
       statements;}
    {- a local record of lambdas whose every use is a call through one of its
       fields becomes those lambdas' bodies at the calls;}
    {- a lambda bound once and called once, as what the function returns,
       becomes the end of the function, wherever in its body it is bound;}
    {- a lambda only ever called directly borrows its scope, and drops a
       parameter of a mapped type that every call passes the same
       variable, capturing the variable instead.}}

    The last two let a reference or array a local loop helper takes stay
    where it was created, so that {!Local_storage} may keep it in a
    local. *)

(** Apply every rule to each function and method body [d] defines, each
    body on its own: R1 and R2 at the statement level of the body itself,
    the last two in every statement list of it but none inside a lambda. *)
val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
