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

let evaluates_operands = Cpp_ir.Variables.evaluates_operands

(* Whether [e] names an object that outlives the statement: a variable,
   [this], a member of one, or a move of one -- an xvalue, which binding by
   value would move from before the statement reads it.  Anything else is a
   computation, and nothing says a computation's result outlives the
   statement: [std::max(b, 1)] returns a reference to one of its own
   temporaries, and so may any mapping's text or function returning a
   reference.  Such an argument is bound by value: a prvalue initialises the
   local in place, and a reference is copied out while it is still live. *)
let rec names_storage : expr -> bool = function
  | Local _ | This -> true
  | Dereference e | Move e | Member (e, _) | Project (e, _, _) | Access (_, e, _) -> names_storage e
  | _ -> false

(* The text of an operation mapping ({!Base.Mapping_operation}), and the
   positions of the arguments it writes or replaces in place. *)
let operation_text : expr -> (string * int list) option = function
  | Entity (r, _, Some {inline = Some {text; _}; _}) when Base.Table.is_mapped_operation r ->
    Some (text, Base.Mapping_operation.in_place_positions (Base.Mapping_operation.find r))
  | _ -> None

(* How many times the text splices argument [i]. *)
let splices text i =
  List.length
    (List.filter (function Cpp_ir.Foreign_template.Arg j -> j = i | _ -> false) (Cpp_ir.Foreign_template.term_template text))

(* An operation mapping's arguments, evaluated once each, in source order,
   before its text (design 11.9): unless at most one of them computes
   anything and the text splices that one once, each argument that is not
   free to repeat is bound ahead of the call, in order -- or, where the text
   does not splice it (an [Ignore] argument), evaluated as a statement and
   discarded.  An argument bound by value and spliced once is moved from its
   temporary, so that a [Take] still receives an rvalue -- unless the text
   writes or replaces it in place ([in_place]), which takes the temporary as
   the lvalue it is. *)
let prepare_operation_args fresh bind discard (text, in_place) (args : expr list) : expr list =
  let computing = List.filter (fun (_, a) -> not (free_to_repeat a)) (List.mapi (fun i a -> (i, a)) args) in
  match computing with
  | [] -> args
  | [(i, _)] when splices text i = 1 -> args
  | _ ->
    List.mapi
      (fun i (a : expr) ->
        if free_to_repeat a then a
        else
          match splices text i with
          | 0 ->
            discard a;
            a
          | n ->
            let x = fresh () in
            let by_value = match a with Move _ -> true | a -> not (names_storage a) in
            bind ~by_value x a;
            if by_value && n = 1 && not (List.mem i in_place) then (Move (Local x) : expr) else (Local x : expr))
      args

(* [e] with each argument it must evaluate once named, at every position [e]
   evaluates unconditionally; [bind x a] binds [x] to [a] ahead of [e], in
   evaluation order. *)
let rec name_args fresh bind discard (e : expr) : expr =
  if not (evaluates_operands e) then e
  else
    let e = Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:(name_args fresh bind discard) ~stmt:Fun.id ~type_:Fun.id ()) e in
    match e with
    | Call (sg, f, args) when Option.has_some (operation_text f) ->
      Call (sg, f, prepare_operation_args fresh bind discard (Option.get (operation_text f)) args)
    | Call (sg, f, args) -> (
      match repeating_text f with
      | Some text ->
        let named =
          List.mapi
            (fun i a ->
              if Cpp_ir.Foreign_template.arg_mentions text i > 1 && not (free_to_repeat a) then (
                let x = fresh () in
                bind ~by_value:(not (names_storage a)) x a;
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
  let bind ~by_value x a =
    let ty : Cpp_ir.Lowered.Type.t = if by_value then Auto else Reference (Forwarding, Auto) in
    bound := (Bind_variable (x, Declare (ty, None), a) : stmt) :: !bound
  in
  let discard a = bound := (Expression a : stmt) :: !bound in
  let e' e = name_args fresh bind discard e in
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
