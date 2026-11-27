(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A copy of a by-value parameter that is its last use is the parameter
    itself.  See [param_copies.mli]. *)

open Names
module IdSet = Id.Set
module V = Cpp_ir.Variables

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type ty = Cpp_ir.Lowered.Type.t
type lambda = Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t

(** The variables [stmts] read or write, a lambda's included. *)
let used (stmts : stmt list) = IdSet.of_list (V.free_in_body stmts)

(** Whether some lambda in [stmts] names [x]. *)
let named_by_lambda x (stmts : stmt list) =
  let found = ref false in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> fe e); stmt = (fun s -> Cpp_ir.Children.stmt v s); type_ = ignore}
  and fe (e : expr) =
    match e with
    | Lambda _ -> if V.mem x (V.free_in_expr e) then found := true
    | _ -> Cpp_ir.Children.expr v e
  in
  List.iter (Cpp_ir.Children.stmt v) stmts;
  !found

(** [stmts] with the variable [v] renamed to [x], wherever it is read,
    written or assigned. *)
let rename v x (stmts : stmt list) =
  let r y = if Id.equal y v then x else y in
  let rec fe (e : expr) : expr =
    match e with Local y -> Local (r y) | _ -> Cpp_ir.Map.expr (m ()) e
  and fs (s : stmt) : stmt =
    let s : stmt = match s with Bind_variable (y, (Existing as b), e) -> Bind_variable (r y, b, e) | s -> s in
    Cpp_ir.Map.stmt (m ()) s
  and m () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.map fs stmts

(** Whether [stmts] move out of [x], anywhere. *)
let moves_out x (stmts : stmt list) =
  let found = ref false in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> fe e); stmt = (fun s -> Cpp_ir.Children.stmt v s); type_ = ignore}
  and fe (e : expr) =
    (match e with Move (Local y) when Id.equal x y -> found := true | _ -> ());
    Cpp_ir.Children.expr v e
  in
  List.iter (Cpp_ir.Children.stmt v) stmts;
  !found

(** [body], the body of a function or lambda whose by-value parameters are
    [params] -- each with its declared type, and whether the function owns
    what it holds -- with every copy of one that is its last use dropped.
    A parameter the function is only lent, though by value, may not be
    moved out of: its copy is dropped only where nothing after it moves out
    of the copy.  [live] is what is read after the statement list being
    rewritten, in the statements around it. *)
let rec body (params : (Id.t * (ty * bool)) list) (stmts : stmt list) : stmt list =
  let candidates = List.filter (fun (x, _) -> not (named_by_lambda x stmts)) params in
  let rec list live (ss : stmt list) : stmt list =
    match ss with
    | [] -> []
    | Bind_variable (v, Declare (t, _), Local x) :: rest
      when (not (Id.equal v x))
           && (match List.assoc_opt x candidates with
               | Some (t', owned) -> t = t' && (owned || not (moves_out v rest))
               | None -> false)
           && (not (IdSet.mem x live))
           && (not (IdSet.mem x (used rest)))
           && not (V.mem x (V.declared rest)) ->
      list live (rename v x rest)
    | s :: rest ->
      let rest = list live rest in
      stmt (IdSet.union live (used rest)) s :: rest
  (* A statement, its statement lists rewritten with [live] read after it;
     a loop's body also with everything the loop reads. *)
  and stmt live (s : stmt) : stmt =
    match s with
    | While (c, ss) ->
      let live = IdSet.union live (IdSet.union (used ss) (used [Expression c])) in
      While (lambdas c, list live ss)
    | _ -> Cpp_ir.Map.stmt (Cpp_ir.Map.make ~stmts:(list live) ~expr:lambdas ~stmt:(stmt live) ~type_:Fun.id ()) s
  in
  list IdSet.empty stmts

(** [e] with each lambda's body rewritten by its own by-value parameters. *)
and lambdas (e : expr) : expr =
  match e with
  | Lambda l -> Lambda {l with body = body (by_value_params l) l.body}
  | _ -> Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:lambdas ~stmt:(fun s -> s) ~type_:Fun.id ()) e

(** A lambda's parameters passed by value, by name, with their types and
    whether the lambda owns them ({!owned}). *)
and by_value_params (l : lambda) =
  List.filter_map
    (fun (t, x) ->
      match x with
      | Some x when by_value t (List.assoc_opt x l.modes) -> Some (x, (t, owned (List.assoc_opt x l.modes)))
      | _ -> None)
    l.params

(** Whether a parameter recorded [mode] is owned by its function: the
    caller moved or copied it in.  One recorded nothing is taken to be lent,
    the safer reading. *)
and owned (mode : Cpp_ir.Param_mode.t option) =
  match mode with Some m -> m.ownership = Owned | None -> false

(** Whether a parameter declared [t] and recorded [mode] is passed by value
    and may be written: not a reference, not [const]. *)
and by_value (t : ty) (mode : Cpp_ir.Param_mode.t option) =
  (match t with Reference _ | Const _ -> false | _ -> true)
  && match mode with Some m -> Cpp_ir.Param_mode.by_value m | None -> true

(** [body] with the lambdas inside its statements rewritten too. *)
let with_lambdas params (stmts : stmt list) =
  let rec fs (s : stmt) : stmt = Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:lambdas ~stmt:fs ~type_:Fun.id ()) s in
  body params (List.map fs stmts)

let transform_decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  let params ps modes =
    List.filter_map
      (fun (x, t) ->
        let m = List.assoc_opt x modes in
        if by_value t m then Some (x, (t, owned m)) else None)
      ps
  in
  let rec member ((f, a, b) : _ Cpp_ir.Field.member) : _ Cpp_ir.Field.member =
    match f with
    | Method m -> (Method {m with body = with_lambdas (params m.params m.modes) m.body}, a, b)
    | Nested_struct (x, ms) -> (Nested_struct (x, List.map member ms), a, b)
    | _ -> (f, a, b)
  in
  let rec decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
    match d with
    | Function ({shape = Definition (ps, stmts); _} as fn) ->
      Function {fn with shape = Definition (ps, with_lambdas (params ps fn.modes) stmts)}
    | Template (ps, c, d) -> Template (ps, c, decl d)
    | Namespace (x, ds) -> Namespace (x, List.map decl ds)
    | Struct s -> Struct {s with fields = List.map member s.fields}
    | Merged_struct_members s -> Merged_struct_members {s with fields = List.map member s.fields}
    | _ -> d
  in
  decl d
