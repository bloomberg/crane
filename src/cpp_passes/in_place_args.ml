(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Arguments a callee writes or replaces in place.  See
    [in_place_args.mli]. *)

open Names

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type ty = Cpp_ir.Lowered.Type.t

(* Whether a variable declared at [t] may be written: held by value and not
   [const], or a reference to non-[const]. *)
let rec writable_type (t : ty) =
  match t with
  | Const _ | Pointer _ | Reference (Forwarding, _) | Reference (_, Const _) -> false
  | Reference (Lvalue, _) -> true
  | In_namespace (_, t) -> writable_type t
  | _ -> true

(* The names declared writable by [params] and by what [visit] walks: a name
   also declared otherwise -- [const], a reference to [const], a structured
   or a match binding -- is not taken to be writable. *)
let writable_names params visit =
  let writable = ref Id.Set.empty and other = ref Id.Set.empty in
  let note x t = if writable_type t then writable := Id.Set.add x !writable else other := Id.Set.add x !other in
  let not_writable x = other := Id.Set.add x !other in
  List.iter (fun (x, t) -> note x t) params;
  let rec fe (e : expr) =
    ( match e with
    | Lambda l -> List.iter (fun (t, x) -> Option.iter (fun x -> note x t) x) l.params
    | _ -> () );
    Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) =
    ( match s with
    | Bind_variable (x, Declare (t, _), _) | Declare (x, t, _) | Declare_value_initialized (x, t) -> note x t
    | Bind_variable (x, Declare_deduced _, _) -> note x Auto
    | Bind_variable (x, Declare_static t, _) -> note x t
    | If_declaration {name; type_; _} -> note name type_
    | For_range (x, _, _) -> not_writable x
    | Structured_binding (xs, _) -> List.iter not_writable xs
    | Match (_, branches, _) ->
      List.iter
        (fun (b : _ Cpp_ir.Grammar.Match.branch) ->
          Option.iter not_writable b.var;
          List.iter (fun (f : _ Cpp_ir.Grammar.Match.field_binding) -> not_writable f.name) b.field_bindings )
        branches
    | Custom_match m ->
      List.iter
        (fun (b : _ Cpp_ir.Grammar.Custom_match.branch) ->
          List.iter (fun (p : _ Cpp_ir.Grammar.Custom_match.param) -> not_writable p.name) b.params )
        m.branches
    | _ -> () );
    Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  visit (rw ());
  Id.Set.diff !writable !other

(* The parameters every function and method [d] defines declares. *)
let parameters (d : Cpp_ir.Lowered.Decl.t) =
  let acc = ref [] in
  let add ps = acc := ps @ !acc in
  let out_of_line : _ Cpp_ir.Field.Out_of_line.t -> unit = function
    | Method m -> add m.params
    | Destructor _ -> ()
  in
  let rec member ((f, _, _) : _ Cpp_ir.Field.member) =
    match f with
    | Method m -> add m.params
    | Constructor c -> add c.params
    | Nested_struct (_, ms) -> List.iter member ms
    | Out_of_line_declaration o -> out_of_line o
    | _ -> ()
  in
  let rec decl (d : Cpp_ir.Lowered.Decl.t) =
    match d with
    | Function {shape = Definition (params, _); _} -> add params
    | Template (_, _, d) -> decl d
    | Namespace (_, ds) -> List.iter decl ds
    | Struct s | Merged_struct_members s -> List.iter member s.fields
    | Member_definition m -> out_of_line m.member
    | _ -> ()
  in
  decl d;
  !acc

(* Whether a lambda captured [c] holds copies of what it names from its
   scope, which it may not write: one stored, or written [[=]]. *)
let copies_scope : _ Cpp_ir.Grammar.Capture.t -> bool = function
  | Stored | Written (By_copy _ | Nothing) -> true
  | Runs_in_place | Written By_reference -> false

(* [crane::writable(e).ref()]. *)
let materialise (e : expr) : expr =
  Access_call (Dot, Cpp_ir.Build.call (Runtime Cpp_ir.Crane_rt.Writable) [e], Id.of_string "ref", [])

(* The positions of the arguments the callee [f] of a call of [n] arguments
   writes or replaces in place: an operation mapping's [in_place] ones, or
   the parameters a generated function's plan passes by reference. *)
let in_place_positions (u : Unit_plan.Context.t) (f : expr) n =
  match f with
  | Entity (r, _, Some {inline = Some _; _}) when Base.Table.is_mapped_operation r ->
    Base.Mapping_operation.in_place_positions (Base.Mapping_operation.find r)
  | Entity (r, _, _) when not (Base.Table.is_custom r) -> (
    match Option.bind (Core_plan.Callable_abi.lookup u.callables r) Core_plan.Callable_abi.modes with
    | Some modes when List.length modes = n ->
      List.concat (List.mapi (fun i (m : Cpp_ir.Param_mode.t) -> if m.form = By_reference then [i] else []) modes)
    | _ -> [] )
  | _ -> []

let transform_decl u (d : Cpp_ir.Lowered.Decl.t) =
  let writable = ref (writable_names (parameters d) (fun m -> ignore (Cpp_ir.Map.decl m d))) in
  let rec fe (e : expr) : expr =
    match e with
    | Lambda l when copies_scope l.capture ->
      (* Inside, what the lambda names from its scope is a copy it holds
         [const]: only its own parameters and locals are writable. *)
      let saved = !writable in
      writable :=
        writable_names
          (List.filter_map (fun (t, x) -> Option.map (fun x -> (x, t)) x) l.params)
          (fun m -> ignore (m.stmts l.body));
      let e = Cpp_ir.Map.expr (rw ()) e in
      writable := saved;
      e
    | _ -> (
      let e = Cpp_ir.Map.expr (rw ()) e in
      match e with
      | Call (sg, f, args) -> (
        match in_place_positions u f (List.length args) with
        | [] -> e
        | positions ->
          Call
            ( sg,
              f,
              List.mapi
                (fun i (a : expr) ->
                  match a with
                  | Local x when Id.Set.mem x !writable -> a
                  | _ when List.mem i positions -> materialise a
                  | _ -> a )
                args ) )
      | _ -> e )
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:(fun s -> Cpp_ir.Map.stmt (rw ()) s) ~type_:Fun.id () in
  Cpp_ir.Map.decl (rw ()) d
