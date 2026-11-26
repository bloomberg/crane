(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A move of a local whose value is copied as its bits is the local.  See
    [plain_moves.mli]. *)

open Names

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type ty = Cpp_ir.Lowered.Type.t

(** Whether a value of type [t] is copied as its bits: a builtin scalar, a
    pointer, an enumeration, a typed mapping's [BitCopy] type, or one of
    these [const] or behind a [const] reference.  A type variable, a
    deduced type and anything else may hold a value worth moving. *)
let rec bit_copied (t : ty) =
  match t with
  | Const t | In_namespace (_, t) | Reference (Lvalue, Const t) -> bit_copied t
  | Pointer _ -> true
  | Named (x, []) -> Base.Table.is_trivially_copyable_cpp_name (Id.to_string x)
  | External (s, []) -> Base.Table.is_trivially_copyable_cpp_name s
  | Entity_application (r, _, _) when Base.Mapping_plan.is_type_head r ->
    (Base.Mapping_plan.find r).copy = Base.Mapping_descriptor.Bit_copy
  | Entity_application (r, [], _) -> Base.Table.is_enum_inductive r
  | _ -> false

(* [env], the locals in scope copied as their bits ({!bit_copied}), after
   [x] is declared at [t]. *)
let declare (env : Id.Set.t) x (t : ty option) =
  match t with Some t when bit_copied t -> Id.Set.add x env | _ -> Id.Set.remove x env

(* [env] after the statement [s], which may declare a local. *)
let after env (s : stmt) =
  match s with
  | Declare (x, t, _) | Declare_value_initialized (x, t) | Bind_variable (x, Declare (t, _), _) ->
    declare env x (Some t)
  | Bind_variable (x, Declare_deduced (Typed t, _), _) -> declare env x (Some t)
  | _ -> List.fold_left (fun env x -> Id.Set.remove x env) env (Cpp_ir.Variables.declared [s])

(* [env] without what [ss] declares anywhere: the statements of a nested
   list declare theirs again in order, with their types, and what binds a
   name otherwise -- a match's bindings -- is not known to be bit-copied. *)
let without_declared env (ss : stmt list) =
  List.fold_left (fun env x -> Id.Set.remove x env) env (Cpp_ir.Variables.declared ss)

let rec block env (ss : stmt list) : stmt list =
  match ss with
  | [] -> []
  | s :: rest ->
    let s' = stmt env s in
    s' :: block (after env s) rest

and stmt env (s : stmt) : stmt = Cpp_ir.Map.stmt (rw (without_declared env [s])) s

and expr env (e : expr) : expr =
  match e with
  | Move (Local x) when Id.Set.mem x env -> Local x
  | Lambda l -> Cpp_ir.Map.expr (rw (with_params (without_declared env l.body) l.params)) e
  | _ -> Cpp_ir.Map.expr (rw env) e

and with_params env params =
  List.fold_left (fun env (t, x) -> match x with Some x -> declare env x (Some t) | None -> env) env params

and rw env = Cpp_ir.Map.make ~stmts:(block env) ~expr:(expr env) ~stmt:(stmt env) ~type_:Fun.id ()

let transform_decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  let params ps = List.fold_left (fun env (x, t) -> declare env x (Some t)) Id.Set.empty ps in
  let rec member ((f, a, b) : _ Cpp_ir.Field.member) : _ Cpp_ir.Field.member =
    match f with
    | Method m -> (Method {m with body = block (params m.params) m.body}, a, b)
    | Nested_struct (x, ms) -> (Nested_struct (x, List.map member ms), a, b)
    | Out_of_line_declaration (Method m) -> (Out_of_line_declaration (Method {m with body = block (params m.params) m.body}), a, b)
    | _ -> (f, a, b)
  in
  let rec decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
    match d with
    | Function ({shape = Definition (ps, body); _} as fn) -> Function {fn with shape = Definition (ps, block (params ps) body)}
    | Template (ps, c, d) -> Template (ps, c, decl d)
    | Namespace (x, ds) -> Namespace (x, List.map decl ds)
    | Struct s -> Struct {s with fields = List.map member s.fields}
    | Merged_struct_members s -> Merged_struct_members {s with fields = List.map member s.fields}
    | Member_definition ({member = Method m; _} as md) ->
      Member_definition {md with member = Method {m with body = block (params m.params) m.body}}
    | _ -> d
  in
  decl d
