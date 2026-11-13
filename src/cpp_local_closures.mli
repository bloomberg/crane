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
       becomes the end of the function.}} *)

(** Apply every rule to each function and method body [d] defines, each
    body on its own, at the statement level of the body itself: a lambda or
    block nested in a body is not rewritten. *)
val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
