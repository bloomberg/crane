(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** String literals where C++ deduces the type.  See [deduced_literals.mli]. *)

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

let transform_decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  match Base.Mapping_plan.mapped_prim_string () with
  | None -> d
  | Some g ->
    (* The string object, constructed from the characters, and from their
       count where they hold a NUL (an array read as a string stops at
       it). *)
    let object_of s : expr =
      let text = Pstring.to_string s in
      let count : expr list = if String.contains text '\000' then [Literal (Int (String.length text))] else [] in
      Converting_construct (Entity_application (g, [], []), Literal (Characters s) :: count)
    in
    let rec fe (e : expr) : expr =
      match e with
      | Lambda ({return_type = None; _} as l) -> Lambda (Cpp_ir.Map.lambda (rw ~deduced:true) l)
      | _ -> Cpp_ir.Map.expr (rw ~deduced:false) e
    and fs ~deduced (s : stmt) : stmt =
      match s with
      | Return (Some (Literal (String s))) when deduced -> Return (Some (object_of s))
      | Bind_variable (x, (Declare_deduced _ as b), Literal (String s)) -> Bind_variable (x, b, object_of s)
      | _ -> Cpp_ir.Map.stmt (rw ~deduced) s
    and rw ~deduced = Cpp_ir.Map.make ~expr:fe ~stmt:(fs ~deduced) ~type_:Fun.id () in
    Cpp_ir.Map.decl (rw ~deduced:false) d
