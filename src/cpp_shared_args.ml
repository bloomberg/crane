(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** An argument a mapping splices more than once, evaluated once.  See
    [cpp_shared_args.mli]. *)

open Names

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

(* Whether evaluating [e] a second time costs nothing and does nothing. *)
let rec free_to_repeat : expr -> bool = function
  | Local _ | Literal _ | Enum_value _ | Numeral _ -> true
  | Dereference e | Project (e, _, _) | Access (_, e, _) -> free_to_repeat e
  | _ -> false

(* The text of a mapping that splices some argument more than once. *)
let repeating_text : expr -> string option = function
  | Entity (_, _, Some {inline = Some {linear = false; text; _}; _}) -> Some text
  | _ -> None

(* Whether [e] evaluates each of its operands whenever it is evaluated: not a
   lambda, a conditional or a connective. *)
let evaluates_operands : expr -> bool = function
  | Lambda _ | Conditional _ | Binary ((And | Or), _, _) -> false
  | _ -> true

(* [e] with each argument it must evaluate once named, at every position [e]
   evaluates unconditionally; [bind x a] binds [x] to [a] ahead of [e], in
   evaluation order. *)
let rec name_args fresh bind (e : expr) : expr =
  if not (evaluates_operands e) then e
  else
    let e = Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:(name_args fresh bind) ~stmt:Fun.id ~type_:Fun.id ()) e in
    match e with
    | Call (sg, f, args) -> (
      match repeating_text f with
      | Some text ->
        let named =
          List.mapi
            (fun i a ->
              if Foreign_template.arg_mentions text i > 1 && not (free_to_repeat a) then (
                let x = fresh () in
                bind x a;
                (Local x : expr) )
              else a )
            args
        in
        Call (sg, f, named)
      | None -> e )
    | _ -> e

(* The statements a rewrite of [s] puts ahead of it, and [s] rewritten: only
   where [s] evaluates its expression once, as its first act. *)
let in_stmt fresh (s : stmt) : stmt list =
  let bound = ref [] in
  let bind x a = bound := (Bind_variable (x, Declare (Reference (Forwarding, Auto), None), a) : stmt) :: !bound in
  let e' e = name_args fresh bind e in
  let s : stmt =
    match s with
    | Return (Some e) -> Return (Some (e' e))
    | Expression e -> Expression (e' e)
    | Bind_variable (y, t, e) -> Bind_variable (y, t, e' e)
    | If i -> If {i with condition = e' i.condition}
    | s -> s
  in
  List.rev !bound @ [s]

(* Fresh names avoid every name declared or read in a block seen so far,
   each block noted before its statements are rewritten. *)
let transform_decl d =
  let used = ref Id.Set.empty in
  let note_ids stmts =
    used := Id.Set.union !used (Id.Set.of_list (Cpp_ir.Variables.declared stmts @ Cpp_ir.Variables.free_in_body stmts))
  in
  let n = ref 0 in
  let rec fresh () =
    incr n;
    let x = Id.of_string (Printf.sprintf "_once%d" !n) in
    if Id.Set.mem x !used then fresh () else x
  in
  let rec block stmts =
    note_ids stmts;
    List.concat_map (fun s -> in_stmt fresh (stmt s)) stmts
  and stmt s = Cpp_ir.Map.stmt (children ()) s
  and expr e = Cpp_ir.Map.expr (children ()) e
  and children () = Cpp_ir.Map.make ~stmts:block ~expr ~stmt ~type_:Fun.id () in
  Cpp_ir.Map.decl (children ()) d
