(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A coinductive's field projection hands out a reference.  See
    [borrow_projection.mli]. *)

open Names
open Cpp_ir.Grammar

type method_ = Cpp_ir.Lowered.phase Cpp_ir.Field.Method.t

(* Whether [e] mentions [this] anywhere. *)
let rec reads_this (e : Cpp_ir.Lowered.Expr.t) =
  match e with
  | This -> true
  | _ ->
    let found = ref false in
    Cpp_ir.Subterms.expr ~expr:(fun e -> if reads_this e then found := true) ~stmts:(fun _ -> ()) e;
    !found

(* What the C++ body of a projection looks like: a single-branch match on
   [this], borrowed, whose body returns one of the fields it binds.  Not what
   decides a split -- the Core function does ([returns_field] of
   {!Cpp_ir.Field.Receiver.t}) -- but what that decision promises, checked. *)
let reads_one_field (m : method_) =
  m.params = [] && (not m.is_conversion)
  &&
  match m.body with
  | [Match (sc, [b], None)] ->
    (not sc.owned) && b.extra_conditions = [] && reads_this sc.expr
    &&
    ( match b.body with
    | [Return (Some (Local x))] ->
      List.exists (fun (fb : _ Match.field_binding) -> Id.equal x fb.name) b.field_bindings
    | _ -> false )
  | _ -> false

(* Whether the method [m] returns one field of its receiver, not yet split,
   and the field has a value a reference can name. *)
let lends_field (m : method_) =
  ( match m.receiver with
  | Instance {returns_field = true; is_const = true; ref_qualifier = Any; _} -> true
  | _ -> false )
  &&
  match m.return_type with
  | Reference _ | Void -> false
  | _ -> true

(* Whether [m] is split, as the Core decision ({!lends_field}) says.  Under
   [CRANE_CHECK_IR], a body that does not have the shape that decision
   promises ({!reads_one_field}) is a violation. *)
let is_projection (m : method_) =
  let lends = lends_field m in
  ( if Probe.checking () then
      let unsplit =
        match m.receiver with
        | Instance {is_const = true; ref_qualifier = Any; _} -> true
        | _ -> false
      in
      let shaped =
        unsplit && reads_one_field m
        && match m.return_type with Reference _ | Void -> false | _ -> true
      in
      if shaped <> lends then
        Probe.violation "borrowed projection"
          Pp.(
            str "the Core function of " ++ Id.print m.name
            ++ str (if lends then " returns a receiver field its body does not read"
                    else " does not return the receiver field its body reads") ) );
  lends

(* The projection as the pair that cannot dangle: a reference for an lvalue
   receiver, and a copy for a temporary one, which dies at the end of the
   full expression that called it. *)
let split (m : method_) : Cpp_ir.Lowered.phase Cpp_ir.Field.t list =
  let with_ref_qual ref_qualifier : Receiver.t =
    match m.receiver with
    | Instance r -> Instance {r with ref_qualifier}
    | Static -> Static
  in
  [ Method {m with return_type = Reference (Lvalue, Const m.return_type); receiver = with_ref_qual Lvalue};
    Method {m with receiver = with_ref_qual Rvalue} ]

(* [field] as the struct declares it: a coinductive's projection as its two
   overloads, in its place. *)
let lend ~coinductive (((f, vis, tag) as field) : Cpp_ir.Lowered.phase Cpp_ir.Field.member) =
  match f with
  | Method m when coinductive && is_projection m -> List.map (fun f -> (f, vis, tag)) (split m)
  | _ -> [field]

(* A coinductive struct whose method still lends a field unsplit was
   generated without {!lend}. *)
let rec check_decl (d : Cpp_ir.Lowered.Decl.t) =
  match d with
  | Template (_, _, inner) -> check_decl inner
  | Namespace (_, ds) -> List.iter check_decl ds
  | (Struct s | Merged_struct_members s) when Table.is_coinductive s.ref_ ->
    List.iter
      (fun ((f, _, _) : _ Cpp_ir.Field.member) ->
        match f with
        | Method m when lends_field m ->
          Probe.violation "borrowed projection"
            Pp.(str "the projection " ++ Id.print m.name ++ str " reached the printer unsplit")
        | _ -> () )
      s.fields
  | _ -> ()
