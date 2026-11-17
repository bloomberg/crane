(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The globals a declaration names, and the one it declares. *)

open Grammar

(** Whether an application's head is written as the erased box, so that the
    application is too, and its arguments are not written. *)
let erased_head : 'p Type.t -> bool = function
  | Type_constructor (Any | Erased _) | Any | Erased _ -> true
  | _ -> false

(** [iter note d] calls [note] at every global [d] names, wherever it is
    named: a type's head, a value, a namespace a type is qualified by, a
    class constraining an instance parameter or a template parameter, a
    projection, a method, a switch's enum.  Not below a type constructor,
    whose head alone is written, nor in the arguments of an application
    whose head is erased. *)
let iter (note : Names.GlobRef.t -> unit) (d : 'p Decl.t) =
  let rec visitor = {Children.expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = (fun t -> ty t)}
  and ty t =
    ( match t with
    | Entity_application (r, _, args) ->
      note r;
      List.iter expr args
    | Foreign {custom = r; values = args; _} ->
      note r;
      List.iter expr args
    | In_namespace (r, _) | Instance (_, r) -> note r
    | Type_of e -> expr e
    | _ -> () );
    match t with
    | Type_constructor _ -> ()
    | Apply (h, ts) ->
      ty h;
      if not (erased_head h) then List.iter ty ts
    | _ -> Children.type_children ty t
  and expr e =
    ( match e with
    | Entity (r, _, _)
    | Foreign (_, {custom = r; _})
    | Aggregate {struct_ = r; _}
    | Project (_, r, _)
    | Projection_value r
    | Enum_value (r, _)
    | Numeral (r, _) ->
      note r
    | Concept_application (c, r, _) ->
      note c;
      note r
    | Method_call m -> note m.method_
    | Method_value m -> note m.method_
    | Projection p -> note p.projection
    | _ -> () );
    Children.expr visitor e
  and stmt s =
    (match s with Switch {enum = r; _} -> note r | _ -> ());
    Children.stmt visitor s
  in
  let rec decl : 'p Decl.t -> unit = function
    | Template (ps, c, inner) ->
      List.iter (fun ((k : _ Parameter_kind.t), _) -> match k with Concept (r, _) -> note r | _ -> ()) ps;
      Children.template_parameters visitor ps;
      Option.iter expr c;
      decl inner
    | Namespace (_, ds) -> List.iter decl ds
    | d -> Children.decl visitor d
  in
  decl d

(** The global a declaration declares: a function's, a struct's, the owner
    of a member defined out of line, a wrapper namespace's. *)
let rec declared : 'p Decl.t -> Names.GlobRef.t option = function
  | Template (_, _, inner) -> declared inner
  | Function f -> Some (fst f.path.outer)
  | Struct s -> Some s.ref_
  | Member_definition m -> Some m.owner
  | Namespace (w, _) -> Option.map (fun (w : Namespace.wrapper) -> w.ref_) w
  | _ -> None
