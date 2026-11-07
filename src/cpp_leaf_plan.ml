(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a leaf of the tree asks of resolution and of scheduling, decided
    before it is printed: the names it is resolved for, the declarations it
    needs placed ahead of it, and the synthesised templates it writes.

    These are planning's questions about a declaration, not the printer's:
    {!Cpp_print} prints a leaf from what this module decided.  Planning the
    templates still spells types to find them, with the printer's own
    spelling; under [CRANE_CHECK_IR] a printed leaf is checked to need what
    was planned for it. *)

open Names
open Minicpp
open Cpp_state
open Cpp_names
open Cpp_print

(** The synthesised templates spelled at the position [ctx] at the type
    constructors [visit] calls its argument at, in the order spelled -- one
    written in another's body ahead of it -- each spelled as the printer
    spells it there, inside the struct of the inductive whose members are
    written around it, if any ({!Cpp_resolution.Inductive_struct}); and how
    each type constructor is written, in the order first spelled. *)
let ctor_aliases_found ctx visit =
  let found = ref [] and uses = ref [] in
  let ctx = {ctx with rc_aliases = Some found; rc_tyctors = Noting uses} in
  visit (fun ~vl ~owner t ->
      match t with
      | Ttyctor _ ->
        (* Which templates are spelled, not what they are named: named live,
           as planning names them, not from the names of a declaration
           resolved at the frames its printing enters. *)
        let spell ctx = ignore (pp_cpp_type_at {ctx with rc_names = None} false vl t) in
        ( match owner with Some r -> enter_from ctx (Inductive_struct r) spell | None -> spell ctx )
      | _ -> () );
  (!found, !uses)

let ctor_aliases_written ctx (d : Cpp_erasure.settled) =
  let aliases, uses = ctor_aliases_found ctx (fun f -> Cpp_demands.tyctors_of_decl f (d :> cpp_decl)) in
  {read_written = (module_written ctx, Written_declaration (d :> cpp_decl)); read_aliases = aliases; read_uses = uses}

let ctor_aliases_of_fields ctx ~vl r types =
  let aliases, uses = ctor_aliases_found ctx (fun f -> List.iter (Cpp_demands.tyctors_of_type f ~vl) types) in
  {read_written = (module_written ctx, Written_fields r); read_aliases = aliases; read_uses = uses}

(** The synthesised templates the finished declaration [d], written in the
    module [module_], writes in the file [file], as planned. *)
let planned_ctor_aliases ~file ~module_ (d : Cpp_erasure.settled) =
  planned_aliases ~file ~module_ (Written_declaration (d :> cpp_decl))

(** The synthesised templates the finished declaration [d] writes at the
    position [ctx], as an element of the module it names, as planned; under
    [CRANE_CHECK_IR], spelled again and compared. *)
let ctor_aliases_planned ctx (d : Cpp_erasure.settled) =
  if not (alias_plan_made ()) then []
  else
    let file = ctx.rc_file in
    let aliases = planned_ctor_aliases ~file ~module_:(module_written ctx) d in
    if Probe.checking () && (ctor_aliases_written ctx d).read_aliases <> aliases then
      Probe.violation "constructor aliases"
        Pp.(str "a declaration of the " ++ str (Common.file_name file)
            ++ str " writes other templates than were planned for it");
    aliases

(* Of the structs the file has constrained forward declarations of
   ({!constrained_structs}), those named by [names ()] or [defined ()], and
   those defined. *)
let constrained_named ~names ~defined =
  match !constrained_structs with
  | [] -> ([], [])
  | constrained ->
    let of_refs refs = List.filter (fun r -> List.exists (GlobRef.UserOrd.equal r) refs) constrained in
    let defined = defined () in
    (of_refs (defined @ names ()), of_refs defined)

(** What placing the declarations a written declaration needs reads: the
    synthesised templates it writes, [templates], as planned
    ({!planned_ctor_aliases}); and, of the structs the file has constrained
    forward declarations of, those it names or defines, and those it
    defines.  The declarations of a wrapper module it writes into a struct
    of its own ({!Cpp_ast.Wrapper_struct}) are members of that struct, and
    need what they need themselves. *)
let needs_of ~templates (settled : Cpp_erasure.settled) =
  let names, defines =
    constrained_named
      ~names:(fun () -> Cpp_demands.globals_of_decl (settled :> cpp_decl))
      ~defined:(fun () -> List.map defined_ref (structs_defined settled))
  in
  {Cpp_ast.Needs.templates; names; defines}

let fields_needs ctx ~module_ ~vl r types =
  let file = ctx.rc_file in
  let aliases = planned_aliases ~file ~module_ (Written_fields r) in
  if Probe.checking () && alias_plan_made () && (ctor_aliases_of_fields ctx ~vl r types).read_aliases <> aliases
  then
    Probe.violation "constructor aliases"
      Pp.(str "the fields of a record in the " ++ str (Common.file_name file)
          ++ str " write other templates than were planned for them");
  let names, _ =
    constrained_named ~names:(fun () -> List.concat_map Cpp_demands.globals_of_type types) ~defined:(fun () -> [])
  in
  {Cpp_ast.Needs.templates = List.map ctor_alias_name aliases; names; defines = []}

let printed_needs ctx settled = needs_of ~templates:(List.map ctor_alias_name (ctor_aliases_planned ctx settled)) settled

(* The frames printing [d] enters names at: {!pp_cpp_decl}'s scopes, read
   without printing. *)
let declaration_frames (d : Cpp_erasure.settled) =
  let entered frame l = List.rev_append l frame in
  let template_body tps = if tps = [] then [] else [Cpp_resolution.In_template] in
  let rec decl frame (d : Cpp_erasure.settled) =
    match Cpp_erasure.view d with
    | Template (_, _, inner) -> frame :: decl frame inner
    | Namespace (None, decls) -> List.concat_map (decl frame) decls
    | Namespace (Some id, members) -> (
      match (members :> cpp_decl list) with
      | [Dstruct {ds_ref; ds_tparams; _}] when nspace_merges {dw_ref = id; dw_sole_child = true} ->
        [frame; entered frame ((Cpp_resolution.In_struct :: template_body ds_tparams) @ [Inductive_struct ds_ref])]
      | _ -> frame :: List.concat_map (decl (Cpp_resolution.In_struct :: frame)) members )
    | Decl (Dfun {df_path; df_shape; _}) ->
      let defines = match df_shape with Ddef _ -> true | Ddecl _ -> false in
      [Cpp_resolution.Function {owner = fst df_path.dp_outer; defines} :: frame]
    | Decl (Dstruct {ds_ref; ds_tparams; _}) ->
      [frame; entered frame (Cpp_resolution.Inductive_struct ds_ref :: template_body ds_tparams)]
    | Decl (Dmember_def {dm_owner; dm_tparams; _}) ->
      [frame; entered frame (template_body dm_tparams @ [Cpp_resolution.Inductive_struct dm_owner])]
    | Decl (Dfields {ds_ref; ds_tparams; _}) ->
      [frame; entered frame ((Cpp_resolution.In_struct :: template_body ds_tparams) @ [Inductive_struct ds_ref])]
    | Decl _ -> [frame]
  in
  decl [] d

(* The globals [d] declares, which it names where it declares them, and the
   classes its template parameters are constrained by: no expression or type
   of it names them. *)
let rec declared_globals (d : cpp_decl) =
  let concepts tps = List.filter_map (function TTconcept (r, _), _ -> Some r | _ -> None) tps in
  let rec field (f, _, _) =
    match f with
    | Fmethod {mf_tparams = tps; _} | Fconstructor {fc_tparams = tps; _} | Fnested_using (tps, _, _) -> concepts tps
    | Fnested_struct (_, fs) -> List.concat_map field fs
    | Fmember_decl m -> field (field_of_member m, VPublic, SNoTag)
    | _ -> []
  in
  match d with
  | Dtemplate (tps, _, inner) -> concepts tps @ declared_globals inner
  | Dnspace (id, ds) -> (match id with Some r -> [r] | None -> []) @ List.concat_map declared_globals ds
  | Dfun {df_path; _} -> List.map fst (dfun_path_list df_path)
  | Dstruct {ds_ref; ds_tparams; ds_fields; _} | Dfields {ds_ref; ds_tparams; ds_fields; _} ->
    (ds_ref :: concepts ds_tparams) @ List.concat_map field ds_fields
  | Dasgn {da_ref; _} -> [da_ref]
  | Dusing {du_name; du_tparams; _} -> du_name :: concepts du_tparams
  | Dstruct_fwd (tps, r) -> r :: concepts tps
  | Dmember_def {dm_owner; dm_enclosing; dm_tparams; dm_field} ->
    (dm_owner :: Option.cata (fun w -> [w.dw_ref]) [] dm_enclosing)
    @ concepts dm_tparams
    @ field (field_of_member dm_field, VPublic, SNoTag)
  | Denum {de_ref; _} -> [de_ref]
  | Dconcept (id, _) -> [id]
  | Dstatic_assert _ -> []

(* Of [globals], those whose name is decided -- printing decides none --
   asked for at each of [frames], each as the type and the expression
   printers may name it. *)
let global_names frames globals =
  let decided r = Option.has_some (Common.decided_global_name r) in
  let globals =
    List.sort_uniq GlobRef.UserOrd.compare
      (List.concat_map (function GlobRef.ConstructRef (ind, _) as r -> [r; GlobRef.IndRef ind] | r -> [r]) globals)
  in
  let keys =
    List.concat_map
      (fun r ->
        Cpp_resolution.[Unmapped (Type, r); Unmapped (Term, r); Class_concept r]
        @ match r with GlobRef.IndRef _ -> [Cpp_resolution.Inductive_value r] | _ -> [] )
      (List.filter decided globals)
    @ Cpp_names.custom_texts_named globals
  in
  List.concat_map (fun frame -> List.map (fun key -> (frame, key)) keys) frames

(* The globals writing [ty] names: those its printing writes the names of
   ({!Cpp_demands.globals_of_type}), and the head of every global type in
   it, a custom whose text it is written from among them. *)
let type_globals ty = Cpp_demands.globals_of_type ty @ type_heads ty

let template_param_globals tps =
  let types = ref [] in
  ignore (map_tparams (fun t -> types := t :: !types; t) tps);
  List.filter_map (function TTconcept (r, _), _ -> Some r | _ -> None) tps @ List.concat_map type_globals !types

let declaration_globals (d : Cpp_erasure.settled) =
  let globals = ref [] in
  Minicpp.iter_globrefs (fun r -> globals := r :: !globals) (d :> cpp_decl);
  !globals @ globals_written_beside (d :> cpp_decl) @ declared_globals (d :> cpp_decl)

let declaration_names d = global_names (declaration_frames d) (declaration_globals d)

let unprinted_names : Cpp_ast.declaration -> _ = function
  | Declaration {settled; _} | Absorbed {settled; _} -> declaration_names settled
  | Fields {fields; _} -> global_names [[]] (List.concat_map (fun (_, ty) -> type_globals ty) fields)
  | Assertion {subject = Instance {args; _}; _} -> global_names [[]] (List.concat_map type_globals args)
  | Global_alias (Alias_of_type {tparams; _}) -> global_names [[]] (template_param_globals tparams)
  | Forward_declaration {defined = Defined_struct {struct_; tparams; constraint_; _}; _} ->
    let constraint_globals c =
      let found = ref [] in
      Minicpp.iter_globrefs (fun r -> found := r :: !found) (Dstatic_assert (c, None));
      !found
    in
    global_names [[]] ((struct_ :: template_param_globals tparams) @ Option.cata constraint_globals [] constraint_)
  | Forward_declaration {defined = Defined_enum r; _} -> global_names [[]] [r]
  | Synthesised_template {body; _} -> global_names [[]] (type_globals body)
  | Assertion {subject = Module _; _} | Global_alias (Alias_of_module _) | Modtype_concept _ | Module_alias _
  | Functor_alias _ | Derived_functor _ ->
    []

let printed_decl ctx env settled =
  let text = read_cpp_decl ctx env settled in
  (text, printed_needs ctx settled)

(** [settled], printed where it is made, with what placing the declarations
    it needs reads ({!needs_of}). *)
let write_decl ctx env settled =
  let text, needs = printed_decl ctx env settled in
  Cpp_ast.decl ~needs text

(** [settled], which {!absorbs}, written where it is made ({!absorbing_at}),
    behind what placing the declarations it needs reads. *)
let write_absorbing ctx ~homed env (settled : Cpp_erasure.settled) =
  let tyctors =
    planned_tyctors ~file:ctx.rc_file ~module_:(module_written ctx) (Written_declaration (settled :> cpp_decl))
  in
  let tree = absorbing_at ctx ~homed ?tyctors env settled in
  let needs = printed_needs ctx settled in
  ( if Probe.checking () then
      let written = Cpp_ast.wrapper_structs tree and absorbing = absorbed_by ~homed settled in
      if List.sort String.compare written <> List.sort String.compare absorbing then
        Probe.violation "wrapper homes"
          Pp.(
            str "a declaration wrote the declarations of the wrappers "
            ++ prlist_with_sep pr_comma str written
            ++ str " into its structs, and needs what those of "
            ++ prlist_with_sep pr_comma str absorbing
            ++ str " need" ) );
  Cpp_ast.seq [Cpp_ast.decl ~needs (Pp.mt ()); tree]

let planned_needs ~file ~module_ settled =
  needs_of ~templates:(List.map ctor_alias_name (planned_ctor_aliases ~file ~module_ settled)) settled

let unprinted ctx ~module_ env (settled : Cpp_erasure.settled) =
  let file = ctx.rc_file in
  Cpp_ast.unprinted ~needs:(planned_needs ~file ~module_ settled)
    ?tyctors:(planned_tyctors ~file ~module_ (Written_declaration (settled :> cpp_decl)))
    env settled

let unprinted_fields ctx ~module_ ~vl r fields =
  Cpp_ast.fields
    ~needs:(fields_needs ctx ~module_ ~vl r (List.map snd fields))
    ?tyctors:(planned_tyctors ~file:ctx.rc_file ~module_ (Written_fields r))
    ~record:r ~vars:vl fields


(** [u] printed as {!Cpp_print.print_unprinted} prints it; under
    [CRANE_CHECK_IR], what a declaration or a record's fields need, read
    again where they are printed, must be what was planned where they were
    made. *)
let print_unprinted ctx ~modtype_concept ~assertion (u : Cpp_ast.unprinted) =
  let text = Cpp_print.print_unprinted ctx ~modtype_concept ~assertion u in
  ( if Probe.checking () then
      let needs =
        match u.declaration with
        | Declaration {settled; _} -> printed_needs ctx settled
        | Fields {record; vars; fields} ->
          fields_needs ctx ~module_:(module_written ctx) ~vl:vars record (List.map snd fields)
        | _ -> u.needs
      in
      if needs <> u.needs then
        Probe.violation "unprinted declarations"
          (Pp.str "a declaration printed where the tree puts it needs other declarations than planned where it was made") );
  text
