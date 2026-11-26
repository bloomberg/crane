(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Mapped identities held in a local.  See [local_storage.mli]. *)

open Names
module Plan = Base.Mapping_plan
module Op = Base.Mapping_operation

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type ty = Cpp_ir.Lowered.Type.t

let rec mapped_type (t : ty) =
  match t with
  | Const t | In_namespace (_, t) -> mapped_type t
  | Entity_application (r, tys, _) when Plan.is_type_head r -> Some (r, tys)
  | _ -> None

(* The stored type and the view template of a local holding a value of the
   declared type [t], where its mapping declares [LocalStorage]. *)
let local_form (t : ty) =
  match mapped_type t with
  | Some (g, tys) -> (
    match (Base.Mapping_discovery.local_storage g, (Plan.find g).components) with
    | Some view, [(_, pos)] -> Option.map (fun stored -> (g, stored, view)) (List.nth_opt tys pos)
    | _ -> None )
  | None -> None

(* The argument a fresh identity is initialised from, where [init] creates
   one whose single component is set once from an argument. *)
let initial_argument (init : expr) =
  match init with
  | Call (_, Entity (r, _, Some {inline = Some _; _}), args) when Base.Table.is_mapped_operation r -> (
    let op = Op.find r in
    match op.result with
    | Return_fresh_identity
        [{initial_source_argument = Some a; initial_multiplicity = Initialise_once; _}] -> (
      match List.find_opt (fun (x : Op.argument) -> x.name = a) op.arguments with
      | Some x -> List.nth_opt args x.position
      | None -> None )
    | _ -> None )
  | _ -> None

(* Whether the conversion [custom] takes a view of a value of [g]: the
   mapping's own conversion, or an operation's for an argument of [g]. *)
let converts_view_of g custom =
  GlobRef.CanOrd.equal custom g
  || Base.Table.is_mapped_operation custom
     && List.exists
          (fun (a : Op.argument) ->
            match a.view with Some c -> GlobRef.CanOrd.equal c.mapped g | None -> false)
          (Op.find custom).arguments

(** Whether a lambda runs only where it is written, inside the scope that
    made it, borrowing that scope: what it uses of the scope is used there,
    so a local it names outlives it. *)
let borrows_scope (l : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t) =
  match l.capture with
  | Runs_in_place | Written (By_reference | Nothing) -> true
  | Stored | Written (By_copy _) -> false

(* Whether every occurrence of [x] in [ss] is the operand of a view
   conversion of [g], outside every lambda that may outlive its scope
   ({!borrows_scope}). *)
let only_viewed g x (ss : stmt list) =
  let ok = ref true in
  let in_lambda = ref false in
  let rec fe (e : expr) : expr =
    match e with
    | Local y when Id.equal x y ->
      ok := false;
      e
    | Foreign (Call, {custom; values = [Local y]; _}) when Id.equal x y ->
      if !in_lambda || not (converts_view_of g custom) then ok := false;
      e
    | Lambda l ->
      let saved = !in_lambda in
      in_lambda := saved || not (borrows_scope l);
      let e = Cpp_ir.Map.expr (rw ()) e in
      in_lambda := saved;
      e
    | _ -> Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) : stmt = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.iter (fun s -> ignore (fs s)) ss;
  !ok

let pieces text : Cpp_ir.Foreign.piece list =
  List.map
    (function
      | Cpp_ir.Foreign_template.Text s -> Cpp_ir.Foreign.Text s
      | Arg i -> Value i
      | _ -> CErrors.anomaly (Pp.str "Local_storage: a hole other than %value in a local view."))
    (Cpp_ir.Foreign_template.term_template text)

let replace_value text =
  let b = Buffer.create (String.length text) in
  let n = String.length text in
  let rec go i =
    if i >= n then ()
    else if i + 6 <= n && String.sub text i 6 = "%value" then (
      Buffer.add_string b "%a0";
      go (i + 6) )
    else (
      Buffer.add_char b text.[i];
      go (i + 1) )
  in
  go 0;
  Buffer.contents b

(* [ss] with each view conversion of [x] the local view [view] of [g]. *)
let respell g x view (ss : stmt list) =
  let text = replace_value view in
  let rec fe (e : expr) : expr =
    match e with
    | Foreign (Call, {values = [Local y]; _}) when Id.equal x y ->
      Foreign (Call, {custom = g; types = []; values = [Local y]; yields = None; pieces = pieces text})
    | _ -> Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) : stmt = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.map fs ss

let traced = Option.has_some (Sys.getenv_opt "CRANE_TRACE_LOCAL_STORAGE")

let rec stmts (ss : stmt list) : stmt list =
  match ss with
  | [] -> []
  | (Bind_variable (x, Declare (t, b), init) as s) :: rest -> (
    let rest = stmts rest in
    match (local_form t, initial_argument init) with
    | Some (g, stored, view), Some arg when only_viewed g x rest ->
      if traced then Printf.eprintf "local storage: %s\n%!" (Id.to_string x);
      Bind_variable (x, Declare (stored, b), arg) :: respell g x view rest
    | _ -> fs s :: rest )
  | s :: rest ->
    let s = fs s in
    s :: stmts rest

and fs (s : stmt) : stmt = Cpp_ir.Map.stmt (rw ()) s
and fe (e : expr) : expr = Cpp_ir.Map.expr (rw ()) e
and rw () = Cpp_ir.Map.make ~stmts ~expr:fe ~stmt:fs ~type_:Fun.id ()

let transform_decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  let rec member ((f, a, b) : _ Cpp_ir.Field.member) : _ Cpp_ir.Field.member =
    match f with
    | Method m -> (Method {m with body = stmts m.body}, a, b)
    | Nested_struct (x, ms) -> (Nested_struct (x, List.map member ms), a, b)
    | Out_of_line_declaration (Method m) -> (Out_of_line_declaration (Method {m with body = stmts m.body}), a, b)
    | _ -> (f, a, b)
  in
  let rec decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
    match d with
    | Function ({shape = Definition (params, body); _} as fn) -> Function {fn with shape = Definition (params, stmts body)}
    | Template (ps, c, d) -> Template (ps, c, decl d)
    | Namespace (x, ds) -> Namespace (x, List.map decl ds)
    | Struct s -> Struct {s with fields = List.map member s.fields}
    | Merged_struct_members s -> Merged_struct_members {s with fields = List.map member s.fields}
    | Member_definition ({member = Method m; _} as md) ->
      Member_definition {md with member = Method {m with body = stmts m.body}}
    | _ -> d
  in
  decl d
