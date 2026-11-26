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

(** The position of the argument a mapped operation [r] only writes
    through: an effectful operation returning a value, whose argument at
    that position is used to [Write], and none of whose facts reads,
    retains or releases what that argument holds, or does anything outside
    the program.  Such a call stores into the identity and nothing else
    observes it, unless something else reads the identity. *)
let blind_write_position r =
  if not (Base.Table.is_mapped_operation r) then None
  else
    let op = Op.find r in
    let names_arg (a : Op.argument) : Base.Mapping_descriptor.operation_fact -> bool = function
      | Reads_component p | Invalidates_views p -> String.equal p.path_argument a.name
      | Retains_argument (x, p) -> String.equal x a.name || String.equal p.path_argument a.name
      | Releases_identity x -> String.equal x a.name
      | External_effect _ -> true
      | Writes_component _ | Invalidates_element_borrows _ -> false
    in
    match (op.purity, op.result) with
    | Effectful, Return_value -> (
      match List.filter (fun (a : Op.argument) -> a.use = Write) op.arguments with
      | [a] when not (List.exists (names_arg a) op.facts) -> Some a.position
      | _ -> None )
    | _ -> None

(** Whether evaluating [e] has no effect but its value: it calls no
    mapped operation other than a pure one, and runs no lambda.  A value of
    the program is computed by functions of Gallina, which have no effect;
    an effect is the event of a mapped operation the value would call. *)
let rec effect_free (e : expr) =
  let calls_effect =
    match e with
    | Call (_, Entity (r, _, _), _) when Base.Table.is_mapped_operation r -> (Op.find r).purity <> Pure
    | Call (_, Lambda _, _) | Lambda _ -> true
    | _ -> false
  in
  (not calls_effect)
  &&
  let ok = ref true in
  Cpp_ir.Subterms.expr ~expr:(fun e -> if not (effect_free e) then ok := false) ~stmts:(fun _ -> ok := false) e;
  !ok

(* Whether [s] is a call of an operation that only writes, through the
   argument {!blind_write_position} names, a view of [x], its other
   arguments {!effect_free}. *)
let blind_write_to x (s : stmt) =
  match s with
  | Expression (Call (_, Entity (r, _, Some {inline = Some _; _}), args)) -> (
    match blind_write_position r with
    | Some pos -> (
      match List.nth_opt args pos with
      | Some (Foreign (Call, {values = [Local y]; _})) when Id.equal x y ->
        List.for_all effect_free (List.filteri (fun i _ -> i <> pos) args)
      | _ -> false )
    | None -> false )
  | _ -> false

(** [ss] without the blind writes to [x] ({!blind_write_to}), where [x] is
    a local identity that nothing else in [ss] uses: such a local is only
    ever set, so it and every store into it are dead.  [None] where
    something else uses [x]. *)
let without_blind_writes x (ss : stmt list) =
  let rec drop (s : stmt) : stmt list =
    if blind_write_to x s then []
    else
      match s with
      | Block b -> [Block (List.concat_map drop b)]
      | While (c, b) -> [While (c, List.concat_map drop b)]
      | If i -> [If {i with then_ = List.concat_map drop i.then_; else_ = List.concat_map drop i.else_}]
      | Match (scrut, branches, default) ->
        let branches =
          List.map (fun (b : _ Cpp_ir.Stmt.Match.branch) -> {b with body = List.concat_map drop b.body}) branches
        in
        [Match (scrut, branches, Option.map (List.concat_map drop) default)]
      | s -> [s]
  in
  let ss' = List.concat_map drop ss in
  if Cpp_ir.Variables.mem x (Cpp_ir.Variables.free_in_body ss') then None else Some ss'

let rec stmts (ss : stmt list) : stmt list =
  match ss with
  | [] -> []
  | (Bind_variable (x, Declare (t, b), init) as s) :: rest -> (
    let rest = stmts rest in
    match (local_form t, initial_argument init) with
    | Some (g, stored, view), Some arg when only_viewed g x rest -> (
      if traced then Printf.eprintf "local storage: %s\n%!" (Id.to_string x);
      match without_blind_writes x rest with
      | Some rest when effect_free arg -> rest
      | Some rest -> Expression arg :: rest
      | None -> Bind_variable (x, Declare (stored, b), arg) :: respell g x view rest )
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
