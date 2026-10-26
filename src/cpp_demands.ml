(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp

let acquire_fence = "std::atomic_thread_fence(std::memory_order_acquire);"

let of_external name =
  if String.equal name Crane_rt.small_vector then Some Table.small_vector_header
  else if String.equal name Crane_rt.itree then Some Table.itree_header
  else if String.equal name Crane_rt.field then Some (Table.Runtime Crane_rt.field_header)
  else if String.equal name ((Cpp_state.sn ()).ns ^ "::optional") then Some (Table.Standard "optional")
  else if String.equal name "std::vector" then Some (Table.Standard "vector")
  else if String.equal name Crane_rt.constant_tc then Some (Table.Runtime Crane_rt.obj_header)
  else None

let at_type_variable = function Tvar _ | Tapply (Tvar _, _) -> true | _ -> false

(* Where a custom mapping is printed, only what its placeholders name is
   written: the type it is matched or applied at, a type argument (an absent
   one is written erased), a branch's binder's type (erased where it has no
   spelling), a branch's body, the scrutinee and a value argument -- a string
   literal among the last two spliced in as a [std::string]. *)
type custom_holes = {
  typ : cpp_type option;
  scrut : cpp_expr option;
  tyargs : cpp_type list;
  cases : (custom_param list * cpp_type * cpp_stmt list) list;
  args : cpp_expr list;
}

let no_holes = {typ = None; scrut = None; tyargs = []; cases = []; args = []}

(* The headers [visit] finds a declaration, statement, expression or type
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
    | Tglob (r, tys, args) -> (
      match Table.find_custom_opt r with
      | Some s when Table.to_inline r ->
        custom {no_holes with tyargs = tys; args}
          (Foreign_template.term_template (Foreign_template.custom_template_with_args s (List.length tys)));
        Some t
      | _ ->
        global r;
        List.iter ty tys;
        Some t )
    (* Only its head is written. *)
    | Ttyctor _ ->
      tyctor ~vl:!names ~owner:!owner t;
      Some t
    | Texpr_type e ->
      expr e;
      Some t
    | _ -> None
  and custom holes cmds =
    let nth l i = List.nth_opt l i in
    List.iter
      (function
        | Foreign_template.CCscrut ->
          Option.iter
            (fun e ->
              expr e;
              string_literal e )
            holes.scrut
        | CCty -> Option.iter ty holes.typ
        | CCbody i -> Option.iter (fun (_, _, ss) -> List.iter stmt ss) (nth holes.cases i)
        | CCty_arg i | CCelem i -> ty (Option.default Tany (nth holes.tyargs i))
        | CCbr_var_ty (i, j) ->
          Option.iter
            (fun (ids, _, _) ->
              Option.iter
                (fun p -> if Ml_type_util.has_no_cpp_spelling p.cp_type then obj () else ty p.cp_type)
                (nth ids j) )
            (nth holes.cases i)
        | CCarg i ->
          Option.iter
            (fun e ->
              expr e;
              string_literal e )
            (nth holes.args i)
        | CCbr_var _ | CCstring _ -> () )
      cmds
  and block_template ?yields holes text =
    ty (Option.default Tauto yields);
    custom holes (Foreign_template.term_template (Foreign_template.with_result "_r" text))
  and expr e =
    ( match e with
    | CPPmove _ | CPPin_place | CPPin_place_index _ | CPPdeclval _ -> std "utility"
    | CPPalloc ((Alloc_heap | Alloc_arena_scoped), t)
      when Pointer_slot.of_pointee t = Pointer_slot.Shared ->
      rt Crane_rt.shared_variant_header
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
    | CPPglob (_, tys, Some {ci_inline = Some tmpl; ci_yields; _}) ->
      if tmpl.it_form = Block_iife then block_template ?yields:ci_yields {no_holes with tyargs = tys} tmpl.it_text
      else custom {no_holes with tyargs = tys} (Foreign_template.type_template tmpl.it_text)
    | CPPglob (r, tys, _) ->
      global r;
      List.iter ty tys
    | CPPfun_call (res, CPPglob (_, tys, Some {ci_inline = Some tmpl; _}), call) -> (
      let args = call_args call in
      let yields = match res.cs_yields with Ryields t -> Some t | Ropaque -> None in
      match tmpl.it_form with
      | Block_iife -> block_template ?yields {no_holes with tyargs = tys; args} tmpl.it_text
      | Bare_callee ->
        List.iter ty tys;
        List.iter expr args
      | _ ->
        (* [%ret] is spelled as the type the call yields; an argument past the
           last one the template names is not written. *)
        if Common.contains_substring tmpl.it_text "%ret" then Option.iter ty yields;
        let cmds = Foreign_template.term_template tmpl.it_text in
        let named =
          List.fold_left (fun n -> function Foreign_template.CCarg i -> max n (i + 1) | _ -> n) 0 cmds
        in
        custom {no_holes with tyargs = tys; args = CList.firstn (min named (List.length args)) args} cmds )
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
    | Smatch _ -> variant ()
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
    | Scustom_case (typ, scrut, tyargs, cases, cm) ->
      custom {typ = Some typ; scrut = Some scrut; tyargs; cases; args = []}
        (Foreign_template.match_template cm.cm_template)
    | Sblock_custom (_, text, _, result_ty, args, tyargs, _) ->
      block_template ~yields:result_ty {no_holes with tyargs; args} text
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

let of_decl d = collect (fun ~decl ~ty:_ -> decl d)

let of_type t = collect (fun ~decl:_ ~ty -> ty t)

let globals visit =
  let found = ref [] in
  ignore (collect ~global:(fun r -> found := r :: !found) visit);
  !found

let globals_of_decl d = globals (fun ~decl ~ty:_ -> decl d)

let globals_of_type t = globals (fun ~decl:_ ~ty -> ty t)

let tyctors_of_decl tyctor d = ignore (collect ~tyctor (fun ~decl ~ty:_ -> decl d))

let tyctors_of_type tyctor ~vl t = ignore (collect ~tyctor ~vl (fun ~decl:_ ~ty -> ty t))

let promoted visit =
  let found = ref [] in
  ignore
    (collect ~promoted:(fun id -> if not (List.exists (Names.Id.equal id) !found) then found := id :: !found) visit);
  List.rev !found

let promoted_of_decl d = promoted (fun ~decl ~ty:_ -> decl d)

let promoted_of_type t = promoted (fun ~decl:_ ~ty -> ty t)

let of_modtype_concept (c : Modtype_concept.t) =
  let found = ref [] in
  let need hs = List.iter (fun h -> if not (List.mem h !found) then found := h :: !found) hs in
  let concepts () = need [Table.Standard "concepts"] in
  let rec cty : Modtype_concept.concept_type -> unit = function
    | Member {arguments; _} -> List.iter cty arguments
    | Parameter t | Plain t -> need (of_type t)
    | Foreign (template, args) ->
      List.iter
        (function
          | Foreign_template.CCty_arg i | CCelem i -> Option.iter cty (List.nth_opt args i)
          | _ -> () )
        (Foreign_template.type_template template)
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
