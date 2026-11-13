(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Cpp_ir.Grammar

type decl = Cpp_ir.Lowered.Decl.t
type member = Cpp_ir.Lowered.phase Field.member

(** The member [f] as one that can be declared in its struct and defined
    after it, if it is one. *)
let out_of_line : Cpp_ir.Lowered.phase Field.t -> Cpp_ir.Lowered.phase Out_of_line.t option = function
  | Method m -> Some (Method m)
  | Destructor body -> Some (Destructor body)
  | _ -> None

(** Whether a member names a global satisfying [p], in its signature or in
    its body: a type's head or the namespace qualifying it, a value, a
    method, a projection, a concept and the instance it is applied to.

    Asked as a predicate rather than answered with the set of everything the
    member names: the caller only ever wants to know whether the member
    crosses the cycle, and a walk that stops at the first hit cannot be read
    as anything else. *)
let field_names ?(body_only = false) (p : GlobRef.t -> bool) ((f, _, _) as m : member) : bool =
  let found = ref false in
  let note r = if p r then found := true in
  let ty t =
    ignore
      (Cpp_ir.Types.map
         (fun (t : Cpp_ir.Lowered.Type.t) ->
           (match t with Entity_application (r, _, _) | In_namespace (r, _) -> note r | _ -> ());
           t )
         t );
    t
  in
  let rec ex (e : Cpp_ir.Lowered.Expr.t) =
    ( match e with
    | Entity (r, _, _) | Method_call {method_ = r; _} | Method_value {method_ = r; _}
    | Projection {projection = r; _} | Projection_value r | Project (_, r, _) ->
      note r
    | Concept_application (r1, r2, _) ->
      note r1;
      note r2
    | _ -> () );
    Cpp_ir.Map.expr (rw ()) e
  and st s = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:ex ~stmt:st ~type_:ty () in
  ( if body_only then
      match out_of_line f with
      | Some o -> ignore (Cpp_ir.Map.out_of_line (Cpp_ir.Map.make ~expr:ex ~stmt:st ~type_:Fun.id ()) o)
      | None -> ()
    else ignore (Cpp_ir.Map.member (rw ()) m) );
  !found

(** [split_struct ~names d] is [d] with the members that name a global
    satisfying [names] left as declarations, paired with their definitions,
    to be written once every struct those globals name is complete.
    [enclosing] is the nearest named namespace around [d], which the hoisted
    definitions are qualified by; [body_only] is {!split_named}'s.

    A mutually recursive group of inductives has no order in which each struct
    can be written whole: [Tree::leaf] takes a [List<Branch>] by value, which
    needs [Branch] complete, and [Branch::branch0] takes a [Tree] the same
    way.  A member that names no sibling is left where it is -- both because
    it does not have to move, and because moving it would take its return type
    out of the struct's scope, where a nested name like [variant_t] no longer
    resolves. *)
let rec split_struct ?(body_only = false) ?enclosing ~(names : GlobRef.t -> bool) (d : decl) : decl * decl list =
  let split_struct ?(enclosing = enclosing) d = split_struct ~body_only ?enclosing ~names d in
  match d with
  | Template (tps, cstr, inner) ->
    let inner, defs = split_struct inner in
    (Template (tps, cstr, inner), defs)
  | Namespace (r, decls) ->
    (* What the struct below is spelled under from outside.  Only the nearest
       one: a member is written [Outer::inner::m], and anything further out is
       already in scope where the definition lands. *)
    let enclosing = match r with None -> enclosing | Some _ -> r in
    let decls, defs =
      List.fold_right
        (fun d (decls, defs) ->
          let d, ds = split_struct ~enclosing d in
          (d :: decls, ds @ defs) )
        decls ([], [])
    in
    (Namespace (r, decls), defs)
  | Struct s ->
    let defs = ref [] in
    let fields =
      List.map
        (fun ((f, vis, tag) as m : member) : member ->
          match out_of_line f with
          | Some o when field_names ~body_only names m ->
            let def : decl = Member_definition {owner = s.ref_; enclosing; type_params = s.type_params; member = o} in
            defs := def :: !defs;
            (Out_of_line_declaration o, vis, tag)
          | _ -> m )
        s.fields
    in
    (Struct {s with fields}, List.rev !defs)
  | _ -> (d, [])

(** [split_named ?body_only ~names decls] is [decls] with every member that
    names a global satisfying [names] left as a declaration, its definition
    written after all of them. *)
let split_named ?body_only ~names (decls : ('a * decl) list) : ('a * decl) list * ('a * decl) list =
  (* A hoisted definition keeps the payload of the struct it came out of:
     carrying it along is what stops the two lists from being re-zipped by
     position once one of them has grown. *)
  List.fold_right
    (fun (x, d) (structs, defs) ->
      let d, ds = split_struct ?body_only ~names d in
      ((x, d) :: structs, List.map (fun d -> (x, d)) ds @ defs) )
    decls ([], [])

let split_group (decls : ('a * decl) list) : ('a * decl) list =
  let group =
    List.fold_left
      (fun acc (_, d) -> match Cpp_ir.Globrefs.declared d with Some r -> GlobRef.Set.add r acc | None -> acc)
      GlobRef.Set.empty decls
  in
  let structs, defs = split_named ~names:(fun r -> GlobRef.Set.mem r group) decls in
  structs @ defs
