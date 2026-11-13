(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

let acquire_fence = "std::atomic_thread_fence(std::memory_order_acquire);"

(* The header an external type, spelled [name], is declared in. *)
let of_external name =
  if String.equal name Crane_rt.small_vector then Some Table.small_vector_header
  else if String.equal name Crane_rt.itree then Some Table.itree_header
  else if String.equal name Crane_rt.field then Some (Table.Runtime Crane_rt.field_header)
  else if String.equal name ((Cpp_state.sn ()).ns ^ "::optional") then Some (Table.Standard "optional")
  else if String.equal name "std::vector" then Some (Table.Standard "vector")
  else if String.equal name Crane_rt.constant_tc then Some (Table.Runtime Crane_rt.obj_header)
  else if String.equal name Crane_rt.shared_box || String.equal name Crane_rt.shared_or then
    Some (Table.Runtime Crane_rt.shared_variant_header)
  else if String.equal name Crane_rt.rc then Some (Table.Standard "memory")
  else None

(* Where a mapping is written -- a match, a block, a type or a term --
   only what its instantiated pieces name is written: the type it is matched
   or applied at, a type argument (an absent one is written erased), a
   branch's binder's type (erased where it has no spelling), a branch's body,
   the scrutinee, a value argument -- a string literal among the last two
   spliced in as a [std::string].

   The headers [collect] finds a declaration, statement, expression or type
   needs, written down where the printer writes it: the annotations a node
   carries for later passes -- a call's signature, a projection's field type,
   a structured binding's field types -- are not written, and neither is
   what a printing rule drops (the type of an abort that is returned, a move
   out of a returned variable).  [visit] is handed the declaration and the
   type visitors. *)
module Ir = struct
  open Cpp_ir

  type ty = Resolved.Type.t
  type expr = Resolved.Expr.t
  type stmt = Resolved.Stmt.t

  let at_type_variable : ty -> bool = function Variable _ | Apply (Variable _, _) -> true | _ -> false

  let collect ?(global = ignore) ?(promoted = ignore) ?(tyctor = fun ~vl:_ ~owner:_ _ -> ()) ?(vl = []) visit =
    let found = ref [] in
    (* The names of the template parameters the type variables written are
       read as, and the struct whose members are being written. *)
    let names = ref vl and owner = ref None in
    let scoped cell v k =
      let saved = !cell in
      cell := v;
      Fun.protect ~finally:(fun () -> cell := saved) k
    in
    let need h = if not (List.mem h !found) then found := h :: !found in
    let std h = need (Table.Standard h) in
    let rt h = need (Table.Runtime h) in
    let obj () = rt Crane_rt.obj_header in
    let variant () = need (Cpp_state.sn ()).variant_header in
    let erase_fn () = need Table.erase_fn_header in
    let string_literal : expr -> unit = function Literal (String _) -> std "string" | _ -> () in
    let rec ty (t : ty) =
      ( match t with
      | Rebind _ | Erased _ | Any -> obj ()
      | External (name, _) -> Option.iter need (of_external name)
      | Function _ -> rt Crane_rt.fn_header
      | Variant (Inline, _) -> variant ()
      | Variant (Shared, _) -> rt Crane_rt.shared_variant_header
      | Shared_pointer t -> (
        match Pointer_slot.of_pointee t with
        | Shared -> rt Crane_rt.shared_variant_header
        | At_instantiation ->
          rt Crane_rt.shared_variant_header;
          std "memory"
        | Pointer -> std "memory" )
      | Decay _ -> std "type_traits"
      | In_namespace (r, _) -> global r
      | Promoted_member id ->
        promoted id;
        Option.iter global (Table.promoted_type_var_field id)
      | _ -> () );
      match t with
      | In_namespace ((Names.GlobRef.IndRef _ as r), Entity_application (r', tys, _)) when Common.globref_equal r r' ->
        List.iter ty tys
      | Entity_application (r, tys, _) -> (
        match Table.inline_custom_text r with
        | Some "" -> List.iter ty tys
        | Some _ -> CErrors.anomaly Pp.(str "a mapped type reached demands uninstantiated: " ++ Names.GlobRef.print r)
        | None ->
          global r;
          List.iter ty tys )
      | Foreign fr -> foreign Foreign.Constant fr
      (* Only its head is written. *)
      | Type_constructor _ -> tyctor ~vl:!names ~owner:!owner t
      | Type_of e -> expr e
      (* In the order written. *)
      | Function (dom, cod) ->
        ty cod;
        List.iter ty dom
      | _ -> Children.type_children ty t
    and foreign (use : Foreign.use) (fr : Resolved.phase Foreign.t) =
      (match use with Block_value _ | Statements -> ty (Option.default Type.Auto fr.yields) | Constant | Call -> ());
      List.iter
        (fun (p : Foreign.piece) ->
          match p with
          | Type_argument i | Element (i, _) -> ty (Option.default Type.Any (List.nth_opt fr.types i))
          | Value i ->
            Option.iter
              (fun e ->
                expr e;
                string_literal e )
              (List.nth_opt fr.values i)
          | Yields -> Option.iter ty fr.yields
          | Text _ | Result | Statement_end -> () )
        fr.pieces
    and visitor = {Children.expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = (fun t -> ty t)}
    and expr (e : expr) =
      ( match e with
      | Move _ | In_place | In_place_index _ | Declval _ -> std "utility"
      | Lambda {capture = Written (By_copy {moved = _ :: _; _}); _} -> std "utility"
      | Allocate (Heap, _) -> std "memory"
      | Allocate (Arena_scoped, _) ->
        if Table.non_atomic_rc () then std "memory"
        else if not (String.equal (Table.std_lib ()) "BDE") then need Table.arena_header
      | Converting_construct (t, _) when at_type_variable t -> obj ()
      | Conditional (_, Call (_, Allocate (Heap, _), _), Literal Null_pointer) -> std "memory"
      | Convertible_to _ -> std "concepts"
      | Abort _ -> std "stdexcept"
      | Variant_get _ | Holds_alternative _ | Variant_get_if _ -> variant ()
      | Runtime h -> (
        match h with
        | Crane_rt.Raw | Crane_rt.Deep_box -> erase_fn ()
        | Crane_rt.Unbox_field -> rt Crane_rt.field_header
        | Crane_rt.Apply2 -> rt Crane_rt.fn_header
        | Crane_rt.Constant _ | Crane_rt.Immortal -> rt Crane_rt.shared_block_header
        | Crane_rt.Make_rc_reusing_unchecked | Crane_rt.Reuse_step | Crane_rt.Share_child -> () )
      | Unbox (To _, _) | Any_cast _ -> obj ()
      | Unbox (Or_keep _, _) -> std "type_traits"
      | Tolerant_any_cast _ ->
        obj ();
        erase_fn ()
      | Erase_callable _ | Tolerant_call _ | Convert _ | Container_cast _ -> erase_fn ()
      | Erased_call _ ->
        obj ();
        std "functional";
        rt Crane_rt.fn_header
      | Function_value _ -> rt Crane_rt.fn_header
      | Aggregate {struct_ = r; _} | Enum_value (r, _) -> global r
      | Concept_application (concept, subject, _) ->
        global concept;
        global subject
      | _ -> () );
      match e with
      | Foreign (use, fr) -> foreign use fr
      | Entity (r, _, Some {inline = Some _; _}) | Call (_, Entity (r, _, Some {inline = Some _; _}), _) ->
        Cpp_ir.Foreign.uninstantiated r
      | Entity (r, tys, _) ->
        global r;
        List.iter ty tys
      | Call (_, f, args) ->
        expr f;
        List.iter expr args
      | Project (e, _, _) -> expr e
      | _ -> Children.expr visitor e
    and stmt (s : stmt) =
      ( match s with
      | Throw _ -> std "stdexcept"
      | Switch {enum = r; _} ->
        std "utility";
        global r
      | Assert (Checked _) -> std "cassert"
      | If_constexpr {test = Convertible (t, _); _} ->
        erase_fn ();
        if at_type_variable t then obj ()
      | Foreign_text text when String.equal text acquire_fence -> std "atomic"
      | Foreign_text text when Common.contains_substring text "std::vector" -> std "vector"
      | Match (scrut, _, _) ->
        variant ();
        if scrut.owned then std "utility"
      | _ -> () );
      match s with
      | Return (Some (Abort _)) -> std "stdexcept"
      | Return
          (Some
            (Move
              ((Local _ | Call _ | Access_call _ | Method_call _ | Projection _ | Aggregate _ | Local_aggregate _) as
               returned))) ->
        expr returned
      | Custom_match m ->
        let nth l i = List.nth_opt l i in
        let pieces : Stmt.Custom_match.piece list = match m.pieces with Instantiated pieces -> pieces in
        List.iter
          (fun (p : Stmt.Custom_match.piece) ->
            match p with
            | Scrutinee _ ->
              expr m.scrutinee;
              string_literal m.scrutinee
            | Matched_type -> ty m.return_type
            | Type_argument i -> ty (Option.default Type.Any (nth m.type_args i))
            | Branch i -> Option.iter (fun (b : _ Stmt.Custom_match.branch) -> List.iter stmt b.body) (nth m.branches i)
            | Binder_type (i, j) ->
              Option.iter
                (fun (b : _ Stmt.Custom_match.branch) ->
                  Option.iter (fun (p : _ Stmt.Custom_match.param) -> ty p.type_) (nth b.params j) )
                (nth m.branches i)
            | Text _ | Binder _ -> () )
          pieces
      | Match (scrut, branches, default) ->
        expr scrut.expr;
        List.iter
          (fun (br : _ Stmt.Match.branch) ->
            ty br.ctor_type;
            List.iter expr br.extra_conditions;
            List.iter stmt br.body )
          branches;
        Option.iter (List.iter stmt) default
      | _ -> Children.stmt visitor s
    in
    let tparams (tps : Resolved.phase Template.parameters) =
      List.iter
        (fun ((k : _ Template.Parameter_kind.t), _) ->
          match k with
          | Invocable _ -> std "type_traits"
          | Concept (r, _) -> global r
          | _ -> () )
        tps;
      Children.template_parameters visitor tps
    in
    let rec field ((f, _, _) : _ Field.member) =
      match f with
      | Method m -> tparams m.type_params
      | Nested_struct (_, fs) -> List.iter field fs
      | _ -> ()
    in
    let rec decl : Resolved.Decl.t -> unit = function
      | Template (tps, c, inner) ->
        tparams tps;
        Option.iter expr c;
        decl inner
      | Namespace (_, ds) -> List.iter decl ds
      | Variable {type_ = t; init = Abort _; _} ->
        ty t;
        std "stdexcept"
      | d -> (
        let members () =
          ( match d with
          | Struct {fields; _} | Merged_struct_members {fields; _} -> List.iter field fields
          | _ -> () );
          Children.decl visitor d
        in
        match d with
        | Type_alias a -> scoped names (List.map snd a.type_params) members
        | Struct {ref_ = r; _} | Merged_struct_members {ref_ = r; _} | Member_definition {owner = r; _} ->
          scoped owner (Some r) members
        | _ -> members () )
    in
    visit ~decl ~ty;
    !found
end

let of_decl d = Ir.collect (fun ~decl ~ty:_ -> decl d)

let of_type t = Ir.collect (fun ~decl:_ ~ty -> ty t)

(* The globals [visit] writes the names of, as {!Ir.collect} meets them. *)
let ir_globals visit =
  let found = ref [] in
  ignore (Ir.collect ~global:(fun r -> found := r :: !found) visit);
  !found

let globals_of_decl d = ir_globals (fun ~decl ~ty:_ -> decl d)

let globals_of_type t = ir_globals (fun ~decl:_ ~ty -> ty t)

let tyctors_of_decl tyctor d = ignore (Ir.collect ~tyctor (fun ~decl ~ty:_ -> decl d))

let tyctors_of_type tyctor ~vl t = ignore (Ir.collect ~tyctor ~vl (fun ~decl:_ ~ty -> ty t))

(* The promoted type variables [visit] writes, each once, in the order
   written. *)
let ir_promoted visit =
  let found = ref [] in
  ignore
    (Ir.collect ~promoted:(fun id -> if not (List.exists (Names.Id.equal id) !found) then found := id :: !found) visit);
  List.rev !found

let promoted_of_decl d = ir_promoted (fun ~decl ~ty:_ -> decl d)

let promoted_of_type t = ir_promoted (fun ~decl:_ ~ty -> ty t)

let of_modtype_concept (c : Modtype_concept.t) =
  let found = ref [] in
  let need hs = List.iter (fun h -> if not (List.mem h !found) then found := h :: !found) hs in
  let concepts () = need [Table.Standard "concepts"] in
  let rec cty : Modtype_concept.concept_type -> unit = function
    | Member {arguments; _} -> List.iter cty arguments
    | Parameter t | Plain t -> need (of_type t)
    | Foreign {pieces; arguments; _} ->
      List.iter
        (function Cpp_ir.Foreign.Type_argument i | Element (i, _) -> Option.iter cty (List.nth_opt arguments i) | _ -> ())
        pieces
    | Global (r, args) ->
      need (of_type (Entity_application (r, [], [])));
      List.iter cty args
    | Namespaced (r, r', e, args) ->
      need (of_type (In_namespace (r, Entity_application (r', [], e))));
      List.iter cty args
    | Shared_pointer t -> cty t
    | Variant (_, ts) -> List.iter cty ts
    | Function (dom, cod) ->
      need [Table.Runtime Crane_rt.fn_header];
      List.iter cty dom;
      cty cod
  in
  let requirement : Modtype_concept.requirement -> unit = function
    (* Its arguments are written as erased placeholders. *)
    | Inductive_member {arity; _} -> if arity > 0 then need (of_type Any)
    | Type_member _ | Submodule _ -> ()
    | Instance_member {arguments; _} ->
      concepts ();
      List.iter cty arguments
    | Nullary_member {result; _} ->
      concepts ();
      cty result
    | Function_member {parameters; result; _} ->
      concepts ();
      List.iter cty parameters;
      cty result
  in
  let rec constraint_ : Modtype_concept.constraint_ -> unit = function
    | Named _ -> ()
    | Requirements {items; _} ->
      List.iter
        (function Modtype_concept.Requirement r -> requirement r | Nested (_, c) -> constraint_ c)
        items
  in
  ( match c with
  | Alias {refinements; _} ->
    if refinements <> [] then concepts ();
    List.iter (fun (_, t) -> need (of_type t)) refinements
  | Constraint c -> constraint_ c );
  !found
