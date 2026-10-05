(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Local closures made and used in one place, rewritten as the code they
    stand for -- before ownership is decided, so that what they captured is
    seen as the function's own.  Each rule is independent and declines unless
    every use is visible in the same body:
    - a lambda invoked where it is written, for an initialiser, becomes its
      statements;
    - a local record of lambdas whose every use is a call through one of its
      fields becomes those lambdas' bodies at the calls;
    - a lambda bound once and called once, as what the function returns,
      becomes the end of the function. *)

val transform_decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
