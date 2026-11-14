(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The name a declaration's type variable has when nothing else names it:
    the one at index [i] of its parameter list is [T<i>].  A fact about the
    program, not about its C++: Core elaboration asks it to tell whether a
    callee's variable would collide with one its caller is generated under,
    and CppIR spells a variable by it ({!Cpp_ir.Type.positional_name}). *)

(** [name i] is [T<i>]. *)
let name i = "T" ^ string_of_int i

(** {!name} as an identifier. *)
let id i = Names.Id.of_string (name i)
