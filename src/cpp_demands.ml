(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp

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

(* Whether [t] is a template parameter, bare or applied. *)
let at_type_variable = function Tvar _ | Tapply (Tvar _, _) -> true | _ -> false

(* Where a mapping is written -- a match, a block, a type or a term --
   only what its instantiated pieces name is written: the type it is matched
   or applied at, a type argument (an absent one is written erased), a
   branch's binder's type (erased where it has no spelling), a branch's body,
   the scrutinee, a value argument -- a string literal among the last two
   spliced in as a [std::string].

   The headers [visit] finds a declaration, statement, expression or type
   needs, written down where the printer writes it: the annotations a node
   carries for later passes -- a call's signature, a projection's field type,
   a structured binding's field types -- are not written, and neither is
   what a printing rule drops (the type of an abort that is returned, a move
   out of a returned variable). *)
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
  let string_literal = function CPPstring _ -> std "string" | _ -> () in
  let rec ty t = ignore (rewrite_cpp_type ty_node t)
  and ty_node t =
    ( match t with
    | Trebind _ | Terased _ | Tany | Topaque -> obj ()
    | Tid_external (name, _) -> Option.iter need (of_external name)
    | Tfun _ -> rt Crane_rt.fn_header
    | Tvariant (Inline_variant, _) -> variant ()
    | Tvariant (Shared_variant, _) -> rt Crane_rt.shared_variant_header
    (* Planning reads types that have not crossed the seam
       ({!Cpp_erasure.lower_pointer_slots}): their slot is chosen here as the
       seam would choose it. *)
    | Tshared_ptr t -> (
      match Pointer_slot.of_pointee t with
      | Pointer_slot.Shared -> rt Crane_rt.shared_variant_header
      | Pointer_slot.At_instantiation ->
        rt Crane_rt.shared_variant_header;
        std "memory"
      | Pointer_slot.Pointer -> std "memory" )
    | Tdecay _ -> std "type_traits"
    | Tnamespace (r, _) -> global r
    (* Spelled bare, a class's type field is imported by name from the class's
       file ([using ProvDef::prov;]). *)
    | Tpromoted id ->
      promoted id;
      Option.iter global (Table.promoted_type_var_field id)
    | _ -> () );
    match t with
    (* Written through the inductive's own head, whatever it is mapped to:
       the head and its arguments. *)
    | Tnamespace ((Names.GlobRef.IndRef _ as r), Tglob (r', tys, _)) when Common.globref_equal r r' ->
      List.iter ty tys;
      Some t
    | Tglob (r, tys, args) -> (
      match Table.inline_custom_text r with
      (* A mapped type is instantiated before demands read it
         ({!Cpp_erasure.instantiate_foreign}; a record's field types are
         instantiated when they are planned, {!Cpp_ind.record_field_types}):
         only one mapped to nothing is still a [Tglob], a head written as
         its arguments. *)
      | Some "" ->
        List.iter ty tys;
        Some t
      | Some _ -> CErrors.anomaly Pp.(str "a mapped type reached demands uninstantiated: " ++ Names.GlobRef.print r)
      | None ->
        global r;
        List.iter ty tys;
        Some t )
    | Tforeign fr ->
      foreign Foreign_constant fr;
      Some t
    (* Only its head is written. *)
    | Ttyctor _ ->
      tyctor ~vl:!names ~owner:!owner t;
      Some t
    | Texpr_type e ->
      expr e;
      Some t
    | _ -> None
  (* An instantiated mapping writes what its pieces name; a block, the type
     of its result too. *)
  and foreign use fr =
    (match use with Foreign_block _ | Foreign_statements -> ty (Option.default Tauto fr.fr_yields) | Foreign_constant | Foreign_call -> ());
    List.iter
      (function
        | Fp_type i | Fp_element (i, _) -> ty (Option.default Tany (List.nth_opt fr.fr_types i))
        | Fp_value i ->
          Option.iter
            (fun e ->
              expr e;
              string_literal e )
            (List.nth_opt fr.fr_values i)
        | Fp_yields -> Option.iter ty fr.fr_yields
        | Fp_text _ | Fp_result | Fp_statement_end -> () )
      fr.fr_pieces
  and expr e =
    ( match e with
    | CPPmove _ | CPPin_place | CPPin_place_index _ | CPPdeclval _ -> std "utility"
    (* A variable whose last use is a closure's capture is moved into it. *)
    | CPPlambda {cl_capture = Written (By_copy {moved = _ :: _; _}); _} -> std "utility"
    | CPPalloc (Alloc_heap, _) -> std "memory"
    | CPPalloc (Alloc_arena_scoped, _) ->
      if Table.non_atomic_rc () then std "memory"
      else if not (String.equal (Table.std_lib ()) "BDE") then need Table.arena_header
    (* A type parameter may be instantiated at an erased type, which a
       converting construction then builds. *)
    | CPPconverting_ctor (t, _) when at_type_variable t -> obj ()
    (* A pointer read at another instantiation of its pointee: allocated
       afresh, or null. *)
    | CPPcond (_, CPPfun_call (_, CPPalloc (Alloc_heap, _), _), CPPnullptr) -> std "memory"
    | CPPconvertible_to _ -> std "concepts"
    | CPPabort _ -> std "stdexcept"
    | CPPstd_get _ | CPPstd_holds_alternative _ | CPPstd_get_if _ -> variant ()
    | CPPrt h -> (
      match h with
      | Crane_rt.Raw | Crane_rt.Deep_box -> erase_fn ()
      | Crane_rt.Unbox_field -> rt Crane_rt.field_header
      | Crane_rt.Apply2 -> rt Crane_rt.fn_header
      | Crane_rt.Constant _ | Crane_rt.Immortal -> rt Crane_rt.shared_block_header
      | Crane_rt.Make_rc_reusing_unchecked | Crane_rt.Reuse_step | Crane_rt.Share_child -> () )
    | CPPunbox (Unbox_to _, _) | CPPany_cast _ -> obj ()
    | CPPunbox (Unbox_or_keep _, _) -> std "type_traits"
    | CPPany_cast_tolerant _ ->
      obj ();
      erase_fn ()
    | CPPerase_fn _ | CPPtolerant_call _ | CPPconvert _ | CPPcontainer_cast _ -> erase_fn ()
    (* Applied at the one erased signature, [crane::fn<obj(obj)>]. *)
    | CPPerased_call _ ->
      obj ();
      std "functional";
      rt Crane_rt.fn_header
    | CPPfn_value _ -> rt Crane_rt.fn_header
    | CPPnamespace (r, _) | CPPstructmk (r, _, _) | CPPstruct (r, _, _) | CPPenum_val (r, _) -> global r
    | CPPconcept_app (concept, subject, _) ->
      global concept;
      global subject
    | _ -> () );
    match e with
    | CPPforeign (use, fr) -> foreign use fr
    (* Every inline mapping was instantiated at the seam, and what reads
       demands reads instantiated declarations. *)
    | CPPglob (r, _, Some {ci_inline = Some _; _}) | CPPfun_call (_, CPPglob (r, _, Some {ci_inline = Some _; _}), _) ->
      uninstantiated_mapping r
    | CPPglob (r, tys, _) ->
      global r;
      List.iter ty tys
    | CPPfun_call (_, f, args) ->
      expr f;
      List.iter expr args.rev
    | CPPget' (e, _, _) -> expr e
    | _ -> ignore (map_expr (fun e -> expr e; e) (fun s -> stmt s; s) (fun t -> ty t; t) e)
  and stmt s =
    ( match s with
    | Sthrow _ -> std "stdexcept"
    | Sswitch (_, r, _, _) ->
      std "utility";
      global r
    | Sassert (Pchecked _) -> std "cassert"
    | Sif_constexpr (Tt_convertible (t, _), _, _) ->
      erase_fn ();
      if at_type_variable t then obj ()
    | Sraw text when String.equal text acquire_fence -> std "atomic"
    | Sraw text when Common.contains_substring text "std::vector" -> std "vector"
    | Smatch (scrut, _, _) ->
      variant ();
      (* An owned scrutinee's alternative is moved out of it. *)
      if scrut.sc_owned then std "utility"
    | _ -> () );
    match s with
    (* Written as a [throw]. *)
    | Sreturn (Some (CPPabort _)) -> std "stdexcept"
    (* A returned variable or temporary is moved implicitly. *)
    | Sreturn
        (Some
          (CPPmove
            (( CPPvar _ | CPPfun_call _ | CPPaccess_call _ | CPPmethod_call _ | CPPprojection _
             | CPPstruct _ | CPPstructmk _ | CPPstruct_id _ ) as returned))) ->
      expr returned
    (* A match writes what its pieces name. *)
    | Scustom_case (typ, scrut, tyargs, cases, cm) ->
      let nth l i = List.nth_opt l i in
      List.iter
        (function
          | Mp_scrutinee _ ->
            expr scrut;
            string_literal scrut
          | Mp_matched_type -> ty typ
          | Mp_type_arg i -> ty (Option.default Tany (nth tyargs i))
          | Mp_branch i -> Option.iter (fun (_, _, ss) -> List.iter stmt ss) (nth cases i)
          | Mp_binder_type (i, j) ->
            Option.iter (fun (ps, _, _) -> Option.iter (fun p -> ty p.cp_type) (nth ps j)) (nth cases i)
          | Mp_text _ | Mp_binder _ -> ())
        (match cm.cm_pieces with Some pieces -> pieces | None -> uninstantiated_mapping cm.cm_inductive)
    | Sblock_custom (r, _, _, _, _, _, _) -> uninstantiated_mapping r
    | Smatch (scrut, branches, default) ->
      expr scrut.sc_expr;
      List.iter
        (fun br ->
          ty br.smb_ctor_type;
          List.iter expr br.smb_extra_conds;
          List.iter stmt br.smb_body )
        branches;
      Option.iter (List.iter stmt) default
    | _ -> ignore (map_stmt (fun e -> expr e; e) (fun s -> stmt s; s) (fun t -> ty t; t) s)
  in
  let tparams tps =
    List.iter
      (fun (tt, _) ->
        match tt with
        | TTinvocable _ -> std "type_traits"
        | TTconcept (r, _) -> global r
        | _ -> () )
      tps;
    ignore (map_tparams (fun t -> ty t; t) tps)
  in
  let rec field (f, _, _) =
    match f with
    | Fmethod mf -> tparams mf.mf_tparams
    | Fnested_struct (_, fs) -> List.iter field fs
    | _ -> ()
  in
  let rec decl = function
    | Dtemplate (tps, c, inner) ->
      tparams tps;
      Option.iter expr c;
      decl inner
    | Dnspace (_, ds) -> List.iter decl ds
    (* Initialised by a lambda that throws, of the declared type. *)
    | Dasgn {da_type = t; da_init = CPPabort _; _} ->
      ty t;
      std "stdexcept"
    | d -> (
      let members () =
        ( match d with
        | Dstruct {ds_fields; _} | Dfields {ds_fields; _} -> List.iter field ds_fields
        | _ -> () );
        ignore (map_decl (fun e -> expr e; e) (fun s -> stmt s; s) (fun t -> ty t; t) d)
      in
      match d with
      | Dusing u -> scoped names (List.map snd u.du_tparams) members
      | Dstruct {ds_ref = r; _} | Dfields {ds_ref = r; _} | Dmember_def {dm_owner = r; _} ->
        scoped owner (Some r) members
      | _ -> members () )
  in
  visit ~decl ~ty;
  !found


let of_type t = collect (fun ~decl:_ ~ty -> ty t)

(* The globals [visit] writes the names of, as [collect] meets them. *)
let globals visit =
  let found = ref [] in
  ignore (collect ~global:(fun r -> found := r :: !found) visit);
  !found


let globals_of_type t = globals (fun ~decl:_ ~ty -> ty t)

let tyctors_of_decl tyctor d = ignore (collect ~tyctor (fun ~decl ~ty:_ -> decl d))

let tyctors_of_type tyctor ~vl t = ignore (collect ~tyctor ~vl (fun ~decl:_ ~ty -> ty t))

(* The promoted type variables [visit] writes, each once, in the order
   written. *)
let promoted visit =
  let found = ref [] in
  ignore
    (collect ~promoted:(fun id -> if not (List.exists (Names.Id.equal id) !found) then found := id :: !found) visit);
  List.rev !found


let promoted_of_type t = promoted (fun ~decl:_ ~ty -> ty t)

module Legacy = struct
  let of_decl d = collect (fun ~decl ~ty:_ -> decl d)
  let globals_of_decl d = globals (fun ~decl ~ty:_ -> decl d)
  let promoted_of_decl d = promoted (fun ~decl ~ty:_ -> decl d)
end

(* [collect] of a finished declaration, read off CppIR: the same rules, where
   nothing is left that only a lowered declaration may hold.  [visit] is
   handed the declaration visitor. *)
module Ir = struct
  open Cpp_ir

  type ty = Resolved.Type.t
  type expr = Resolved.Expr.t
  type stmt = Resolved.Stmt.t

  let at_type_variable : ty -> bool = function Variable _ | Apply (Variable _, _) -> true | _ -> false

  let rec pointee_slot : ty -> Pointer_slot.t = function
    | Entity_application (r, _, _) when Table.is_shared_variant r -> Shared
    | Entity_application (Names.GlobRef.IndRef (kn, _), _, _)
      when Table.shared_variant () && Common.under_mp_bound (Names.MutInd.modpath kn) ->
      At_instantiation
    | In_namespace (_, t) | Const t -> pointee_slot t
    | _ -> Pointer

  let collect ?(global = ignore) ?(promoted = ignore) visit =
    let found = ref [] in
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
        match pointee_slot t with
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
      | Type_constructor _ -> ()
      | Type_of e -> expr e
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
        uninstantiated_mapping r
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
      | d ->
        ( match d with
        | Struct {fields; _} | Merged_struct_members {fields; _} -> List.iter field fields
        | _ -> () );
        Children.decl visitor d
    in
    visit decl;
    !found
end

let of_decl d = Ir.collect (fun decl -> decl d)

let globals_of_decl d =
  let found = ref [] in
  ignore (Ir.collect ~global:(fun r -> found := r :: !found) (fun decl -> decl d));
  !found

let promoted_of_decl d =
  let found = ref [] in
  ignore
    (Ir.collect
       ~promoted:(fun id -> if not (List.exists (Names.Id.equal id) !found) then found := id :: !found)
       (fun decl -> decl d));
  List.rev !found

let of_modtype_concept (c : Modtype_concept.t) =
  let found = ref [] in
  let need hs = List.iter (fun h -> if not (List.mem h !found) then found := h :: !found) hs in
  let concepts () = need [Table.Standard "concepts"] in
  let rec cty : Modtype_concept.concept_type -> unit = function
    | Member {arguments; _} -> List.iter cty arguments
    | Parameter t | Plain t -> need (of_type t)
    | Foreign {pieces; arguments; _} ->
      List.iter
        (function Fp_type i | Fp_element (i, _) -> Option.iter cty (List.nth_opt arguments i) | _ -> ())
        pieces
    | Global (r, args) ->
      need (of_type (Tglob (r, [], [])));
      List.iter cty args
    | Namespaced (r, r', e, args) ->
      need (of_type (Tnamespace (r, Tglob (r', [], e))));
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
    | Inductive_member {arity; _} -> if arity > 0 then need (of_type Tany)
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
