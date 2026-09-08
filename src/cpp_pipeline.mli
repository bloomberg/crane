(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The passes a MiniCpp declaration goes through between translation and the
    printer.

    Loopification, depth flattening and the {!Cpp_erasure} seam have to run in
    that order, and every one of them has to run: a declaration that skipped
    flattening crashes the C++ parser, and one that skipped the seam is not a
    {!Cpp_erasure.settled} declaration at all.  So the sequence is a single
    function rather than a sequence its callers spell out -- there are no
    intermediate declarations to hand to the wrong pass, because none of them
    is nameable from outside. *)

(** [should_loopify decl] -- whether [decl] is loopified, given what the user
    asked for and what kind of declaration it is. *)
val should_loopify : Minicpp.cpp_decl -> bool

(** [finish ~pp_expr ~loopify decl] runs every pass between translation and
    printing, and hands back the printable declaration.

    @param pp_expr renders an expression as a string, for the diagnostics
                   {!Loopify} emits about what it declined to transform.
    @param loopify whether to loopify, normally {!should_loopify} of the same
                   declaration. *)
val finish :
  pp_expr:(Minicpp.cpp_expr -> string) ->
  loopify:bool ->
  Minicpp.cpp_decl ->
  Cpp_erasure.settled
