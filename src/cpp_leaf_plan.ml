(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a leaf of the tree asks of resolution and of scheduling, decided
    before it is printed: the names it is resolved for, the declarations it
    needs placed ahead of it, and the synthesised templates it writes.

    These are planning's questions about a declaration, not the printer's:
    {!Cpp_print} prints a leaf from what this module decided.  Planning the
    templates walks the type constructors a declaration writes and decides
    each, without rendering it; a template's body is rendered once its own
    type constructors are decided, for the text its name digests.  Under
    [CRANE_CHECK_IR] a printed leaf is checked to need, and write, what was
    planned for it. *)

open Names
open Minicpp
open Cpp_state
open Cpp_names
open Cpp_print

(** Whether text no name was written through -- an external name, a custom
    mapping's replacement -- qualifies a name into something other than one
    of the included libraries' namespaces: the identifier in front of each
    [::] is the qualifier. *)
let text_names_into_a_struct text =
  let libraries = ["std"; "crane"; (sn ()).ns] in
  let n = String.length text in
  let is_ident c =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'
  in
  let rec scan i =
    if i + 1 >= n then false
    else if text.[i] = ':' && text.[i + 1] = ':' then
      let stop = ref i in
      while !stop > 0 && is_ident text.[!stop - 1] do decr stop done;
      let qualifier = String.sub text !stop (i - !stop) in
      if List.mem qualifier libraries then scan (i + 2) else true
    else scan (i + 1)
  in
  scan 0

(** Whether one thing a rendering writes ({!Cpp_name.written}) is a qualifier
    naming into a struct or a template parameter rather than a namespace. *)
let writes_into_a_struct = function
  | Cpp_name.Scope (Cpp_name.Namespace _ | Cpp_name.Global) -> false
  | Cpp_name.Scope (Cpp_name.Class _ | Cpp_name.Parameter _) -> true
  | Cpp_name.Foreign_text text | Cpp_name.Untagged text -> text_names_into_a_struct text

let scopes_name_into_a_struct = List.exists (fun s -> writes_into_a_struct (Cpp_name.Scope s))

(** Whether the head [h] is written through a struct or a template
    parameter. *)
let head_names_into_a_struct h =
  scopes_name_into_a_struct (h.outer @ Cpp_name.scopes h.head)
  || match h.head with Cpp_name.Foreign text -> text_names_into_a_struct text | Cpp_name.Name _ -> false

(** Whether the type [t] writes a qualifier into a struct or a template
    parameter, asked of the type rather than of its rendering: each name is
    the one {!pp_cpp_type} writes, from the same heads, at the position
    [ctx].  [None] where only the rendering can tell -- an
    expression's type, and a type constructor named as a template argument,
    which may be written through a synthesised alias ({!Cpp_leaf_plan.ctor_alias_at}). *)
let type_names_into_a_struct ctx t =
  let rec names_into t =
  let any ts =
    List.fold_left
      (fun acc t -> match acc with Some true | None -> acc | Some false -> names_into t)
      (Some false) ts
  in
  let ( ||? ) b rest = if b then Some true else rest in
  match t with
  | Tvar _ | Tinstance _ | Tvoid | Thole | Tdecltype_auto | Terased _ | Tany | Topaque -> Some false
  | Tunresolved -> None
  | Tpromoted id -> Some (scopes_name_into_a_struct (Option.default [] (member_scopes ctx id)))
  | Tid (id, args) -> scopes_name_into_a_struct (Option.default [] (member_scopes ctx id)) ||? any args
  | Tid_external (id_s, args) -> text_names_into_a_struct (external_type_name id_s) ||? any args
  | Tglob (r, tys, _) -> (
    match Cpp_names.inline_custom_text ctx r with
    | Some s -> text_names_into_a_struct s ||? any tys
    | None ->
      head_names_into_a_struct (glob_head ctx r ~applied:(tys <> [])) ||? any tys )
  | Tforeign fr -> text_names_into_a_struct (foreign_text fr) ||? any fr.fr_types
  | Tnamespace ((GlobRef.IndRef _ as r), Tglob (r', args, _)) when Common.globref_equal r r' ->
    head_names_into_a_struct (inductive_head ctx r' ~applied:(args <> [])) ||? any args
  | Tnamespace _ | Tqualified _ | Tapply (Tqualified _, _) -> Some true
  | Tapply (head, args) -> any (head :: args)
  | Tfun (dom, cod) -> any (cod :: dom)
  | Tnondeduced t | Tref (_, t) | Tptr t | Tconst t | Tshared_ptr t -> names_into t
  | Trebind (h, x) -> any [h; x]
  | Tvariant (_, tys) -> any tys
  | Texpr_type _ | Ttyctor _ | Tdecay _ | Tauto -> None
  in
  names_into t

(** Whether [d], written as a member of a struct body, is a static function
    declaration ending at its semicolon: no body, no initialiser, no
    template head. *)
let is_static_member_declaration (d : cpp_decl) =
  match d with Dfun {df_shape = Ddecl _; _} -> true | _ -> false

(** Whether the function declaration [d] writes a qualifier into a struct or
    a template parameter ({!type_names_into_a_struct}): in its name, result
    and parameters, and in its template head -- a concept constraining a
    parameter, a type a parameter defaults to or a callable one is invoked
    with.  [None] for anything else, a declaration under a [requires]
    clause, or where only its rendering can tell.  Each name is asked at
    the frame the printer writes it at ({!pp_cpp_decl}). *)
let rec declaration_names_into_a_struct ctx (d : cpp_decl) =
  let any_type ctx ts =
    List.fold_left
      (fun acc t -> match acc with Some false -> type_names_into_a_struct ctx t | _ -> acc)
      (Some false) ts
  in
  let names_through n = head_names_into_a_struct (unqualified_head n) in
  match d with
  | Dfun {df_path = {dp_outer; dp_inner}; df_ret; df_shape = Ddecl params; _} ->
    let ctx = next (Function {owner = fst dp_outer; defines = false}) ctx in
    let path = dp_outer :: dp_inner in
    if List.exists (fun (n, _) -> names_through (global_name ctx Type n)) path then Some true
    else any_type ctx ((df_ret :: List.map snd params) @ List.concat_map snd path)
  | Dtemplate (tparams, None, inner) ->
    let concept_names_through c = (not (class_concept_held_back ctx c)) && names_through (concept_name ctx c) in
    let param_types (tt, _) =
      match tt with
      | TTtypename | TTtemplate _ -> []
      | TTtypename_default t -> [t]
      | TTfun (dom, cod) -> cod :: dom
      | TTinvocable (invs, cod) -> cod :: List.concat_map (fun inv -> List.map snd inv.inv_args) invs
      | TTconcept (_, args) -> args
    in
    if List.exists (function TTconcept (c, _), _ -> concept_names_through c | _ -> false) tparams
    then Some true
    else (
      match any_type ctx (List.concat_map param_types tparams) with
      | Some false -> declaration_names_into_a_struct ctx inner
      | answer -> answer )
  | _ -> None

(* The head of every global type in [ty], a type constructor written as a
   template template argument entered too ({!exists_cpp_type}). *)
let type_heads ty =
  let heads = ref [] in
  ignore
    (exists_cpp_type
       (fun t ->
         (match t with Tglob (r, _, _) | Tforeign {fr_custom = r; _} -> heads := r :: !heads | _ -> ());
         false )
       ty );
  !heads

(* What writing [d] names that its globals ({!Minicpp.iter_globrefs}) do not:
   the head of each type constructor written as a template template
   argument, a leaf to a type's traversal, the primitive integer type,
   through whose mapping each literal of that type is spelled, and the
   custom whose template a custom match or a block custom writes. *)
let globals_written_beside (d : cpp_decl) =
  let found = ref [] in
  let rec ty t =
    ignore
      (map_cpp_type
         (fun t ->
           ( match t with
           | Tglob (_, _, args) | Tforeign {fr_values = args; _} -> List.iter (fun e -> ignore (expr e)) args
           | Texpr_type e -> ignore (expr e)
           | Ttyctor head -> found := type_heads head @ !found
           | _ -> () );
           t )
         t );
    t
  and expr e =
    ( match e with
    | CPPuint _ -> found := Option.cata (fun r -> [r]) [] (uint63_type ()) @ !found
    | CPPglob (x, _, _) -> (
      match Module_plan.eponymous_record_containing x with
      | Some {Module_plan.record; _} -> found := record :: !found
      | None -> () )
    | _ -> () );
    map_expr expr stmt ty e
  and stmt s =
    ( match s with
    | Scustom_case (_, _, _, _, cm) -> found := cm.cm_inductive :: !found
    | Sblock_custom (r, _, _, _, _, _, _) -> found := r :: !found
    | _ -> () );
    map_stmt expr stmt ty s
  in
  let rec decl = function
    | Dtemplate (tps, c, inner) ->
      ignore (map_tparams ty tps);
      Option.iter (fun e -> ignore (expr e)) c;
      decl inner
    | Dnspace (_, ds) -> List.iter decl ds
    | d -> ignore (map_decl expr stmt ty d)
  in
  decl d;
  !found

(* Whether [probe], a type constructor applied to the sentinel, is written as
   a template name applied to the sentinel alone, read off its structure and
   not off its rendering; [None] where the structure does not say.  An
   instantiated mapping is that name where its text is a head with no
   argument list of its own, then the sentinel's hole -- an element hole
   written bare, as the sentinel's always is ({!Cpp_leaf_plan.ctor_alias_at}) -- then the
   list's close; any other global is its name applied to its arguments.  A
   value argument is written only where a mapping's text splices it, which
   is then not that shape. *)
let rec applied_to_sentinel_alone ctx = function
  | Tid (_, args) | Tid_external (_, args) -> Some (args = [Thole])
  | Tnamespace (_, t) -> applied_to_sentinel_alone ctx t
  | Tglob (_, args, _) -> Some (args = [Thole])
  | Tforeign {fr_types = args; fr_pieces; _} -> (
    match fr_pieces with
    | [Fp_text head; (Fp_type i | Fp_element (i, None)); Fp_text ">"] when List.nth_opt args i = Some Thole ->
      Some (String.index_opt head '<' = Some (String.length head - 1))
    | _ -> Some false )
  | _ -> None

(** The types [d] declares under a name no struct qualifies, each with how
    it is declared and the template parameters it is declared over, which an
    alias of it written elsewhere repeats: an alias, an enum, and a struct
    planned at namespace scope. *)
let rec declared_types ?(outer = []) = function
  | Dtemplate (tparams, _, inner) -> declared_types ~outer:(outer @ tparams) inner
  | Dusing u -> [(u.du_name, Cpp_ast.Alias_definition, outer @ u.du_tparams)]
  | Denum {de_ref; _} -> [(de_ref, Cpp_ast.Enum_definition, outer)]
  | Dstruct {ds_ref; ds_tparams; _} when Module_plan.is_namespace_scope_ref ds_ref ->
    [(ds_ref, Cpp_ast.Struct_definition, outer @ ds_tparams)]
  | Dnspace (Some w, ds) when Module_plan.is_namespace_scope_ref w.nw_ref -> List.concat_map (declared_types ~outer) ds
  | _ -> []

let stand_ins t =
  List.concat_map
    (function
      | Cpp_ast.Declared (Declaration {settled; _} | Absorbed {settled; _}) ->
        List.map
          (fun (target, definition, tparams) ->
            Cpp_ast.(global_alias (Alias_of_type {target = global_ref target; definition; tparams})) )
          (declared_types (settled :> cpp_decl))
      | Declared
          ( Fields _ | Modtype_concept _ | Global_alias _ | Assertion _ | Module_alias _ | Functor_alias _ | Derived_functor _
          | Forward_declaration _ | Synthesised_template _ ) ->
        []
      | Struct_of mp -> [Cpp_ast.(global_alias (Alias_of_module (module_ref mp)))] )
    (Cpp_ast.declared t)

(** Whether [d] is an assertion the struct being written holds back
    ({!held_back_assertions}), which it writes nothing for. *)
let is_held_back_assertion ctx (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Decl (Dstatic_assert (CPPconcept_app (class_ref, _, _), None)) -> class_concept_held_back ctx class_ref
  | _ -> false

let resolved_names_into_a_struct ctx names (settled : Cpp_erasure.settled) =
  declaration_names_into_a_struct {ctx with rc_names = Names_resolved names} (settled :> cpp_decl)

(** What a file writes that places the templates it writes: a declaration,
    or the fields of the eponymous record merged into a module's struct,
    which no declaration holds. *)
type written = Written_declaration of cpp_decl | Written_fields of GlobRef.t

(** What a file writes, in the module it is written in. *)
module Written = Hashtbl.Make (struct
  type t = ModPath.t * written

  (* [compare] rather than [=]: a NaN literal is equal to itself. *)
  let equal (mp, w) (mp', w') =
    ModPath.equal mp mp'
    &&
    match (w, w') with
    | Written_declaration d, Written_declaration d' -> compare d d' = 0
    | Written_fields r, Written_fields r' -> GlobRef.UserOrd.equal r r'
    | (Written_declaration _ | Written_fields _), _ -> false

  let hash (mp, w) =
    Hashtbl.hash
      ( ModPath.hash mp,
        match w with
        | Written_declaration d -> Hashtbl.hash_param 40 160 d
        | Written_fields r -> GlobRef.UserOrd.hash r )
end)

(** What planning reads off something a file writes: what it is, as the
    render reads it back, the synthesised templates it writes, in the
    order written, and how it writes each type constructor it writes as a
    template template argument. *)
type ctor_aliases_read = {
  read_written : Written.key;
  read_aliases : ctor_alias list;
  read_uses : tyctor_use list;
}

(** The synthesised templates each file writes, planned before either is
    rendered ({!Cpp.plan_ctor_aliases}): each file's, in the order it first
    writes them, and those each declaration it writes writes, with how it
    writes its type constructors. *)
type ctor_alias_plan = {
  intf : ctor_alias list;
  impl : ctor_alias list;
  intf_writes : (ctor_alias list * tyctor_use list) Written.t;
  impl_writes : (ctor_alias list * tyctor_use list) Written.t;
}

(** [None] until the unit's templates are planned: a declaration rendered
    before then, for its text, or on its own
    ({!Extract_env.print_one_decl}), places none. *)
let ctor_alias_plan : ctor_alias_plan option ref = State.cell State.Unit None

(** Plan the templates each file writes, [written file] those of [file] in
    the order written: the header's, then the implementation's. *)
let plan_ctor_aliases written =
  let dedup l = List.fold_left (fun acc a -> if List.mem a acc then acc else acc @ [a]) [] l in
  let planned file =
    let reads = written file in
    let writes = Written.create 64 in
    List.iter
      (fun r ->
        if not (Written.mem writes r.read_written) then
          Written.add writes r.read_written (r.read_aliases, r.read_uses) )
      reads;
    (dedup (List.concat_map (fun r -> r.read_aliases) reads), writes)
  in
  let intf, intf_writes = planned Common.Intf in
  let impl, impl_writes = planned Common.Impl in
  ctor_alias_plan := Some {intf; impl; intf_writes; impl_writes}

(** The declaration of [alias], printed where the tree puts it as declared
    where it is ({!Cpp_ast.Template_in}). *)
let ctor_alias_declaration a =
  Cpp_ast.synthesised_template ~tyctors:a.ca_uses
    { name = ctor_alias_name a;
      holder = a.ca_holder;
      declared_in = a.ca_declared;
      body = a.ca_type;
      vars = a.ca_vars;
      planned = a.ca_body }

(** The templates the file [file] declares, each once, in the order planned:
    the aliases it writes, and, in the header, every holder the unit writes.

    A holder is a struct, and a struct may be defined once.  An alias may be
    declared in whichever file writes the use, because repeating a [using]
    with the same definition is legal; repeating a [struct] is not, so the
    header, the one file everything sees, declares every holder. *)
let ctor_aliases_declared_in ~file =
  let declared =
    match (!ctor_alias_plan, file) with
    | None, _ -> []
    | Some plan, Common.Intf -> plan.intf @ List.filter (fun a -> Option.has_some a.ca_holder) plan.impl
    | Some plan, Common.Impl -> List.filter (fun a -> Option.is_empty a.ca_holder) plan.impl
  in
  List.fold_left
    (fun acc a ->
      if List.exists (fun a' -> String.equal (ctor_alias_name a') (ctor_alias_name a)) acc then acc else acc @ [a] )
    [] declared

let alias_plan_made () = Option.has_some !ctor_alias_plan

(* What is planned for [w], written in the module [module_], in the file
   [file]: the synthesised templates it writes and how it writes its type
   constructors; none before the unit's templates are planned. *)
let planned_writes ~file ~module_ w =
  match !ctor_alias_plan with
  | None -> None
  | Some plan -> (
    let writes = match file with Common.Intf -> plan.intf_writes | Common.Impl -> plan.impl_writes in
    match Written.find_opt writes (module_, w) with
    | Some planned -> Some planned
    | None ->
      let what = match w with Written_declaration _ -> "a declaration" | Written_fields _ -> "the fields of a record" in
      CErrors.anomaly
        Pp.(str "Crane: " ++ str what ++ str " of the " ++ str (Common.file_name file) ++ str " in "
            ++ str (ModPath.to_string module_)
            ++ str " are written that were not read when their templates were planned.") )

(** The synthesised templates [w], written in the module [module_], writes
    in the file [file], as planned. *)
let planned_aliases ~file ~module_ w = match planned_writes ~file ~module_ w with Some (aliases, _) -> aliases | None -> []

(** How [w], written in the module [module_], writes its type constructors
    in the file [file], as planned; none before the unit's templates are
    planned. *)
let planned_tyctors ~file ~module_ w = Option.map snd (planned_writes ~file ~module_ w)

(** Under [CRANE_CHECK_IR], the templates the file [file] spelled must be
    the ones planned for it. *)
let check_ctor_alias_plan ~file =
  if Probe.checking () then begin
    let planned =
      match (!ctor_alias_plan, file) with
      | None, _ -> []
      | Some plan, Common.Intf -> plan.intf
      | Some plan, Common.Impl -> plan.impl
    in
    let spelled = take_ctor_aliases_spelled () in
    let describe a =
      Printf.sprintf "%s %s%s" (if Option.has_some a.ca_holder then "holder" else "alias") a.ca_body
        (match a.ca_declared with In_struct_of mp -> " in " ^ ModPath.to_string mp | At_namespace_scope _ -> "")
    in
    let missing l l' = List.filter (fun a -> not (List.mem a l')) l in
    match (missing spelled planned, missing planned spelled) with
    | [], [] -> ()
    | unplanned, unspelled ->
      Probe.violation "constructor aliases"
        Pp.(
          str "the " ++ str (Common.file_name file) ++ str " spells "
          ++ prlist_with_sep pr_comma (fun a -> str (describe a)) unplanned
          ++ str " unplanned, and does not spell "
          ++ prlist_with_sep pr_comma (fun a -> str (describe a)) unspelled
          ++ str " planned" )
  end

(** The structs the file being written has constrained forward declarations
    of, planned with its layout, each by its reference and the name its
    declaration declares. *)
let constrained_structs : GlobRef.t list ref = State.cell State.Unit []

(* The frames printing [d] enters names at: {!pp_cpp_decl}'s scopes, read
   without printing. *)
let declaration_frames (d : Cpp_erasure.settled) =
  let entered frame l = List.rev_append l frame in
  let template_body tps = if tps = [] then [] else [Cpp_resolution.In_template] in
  let rec decl frame (d : Cpp_erasure.settled) =
    match Cpp_erasure.view d with
    | Template (_, _, inner) -> frame :: decl frame inner
    | Namespace (None, decls) -> List.concat_map (decl frame) decls
    | Namespace (Some w, members) -> (
      match (members :> cpp_decl list) with
      | [Dstruct {ds_ref; ds_tparams; _}] when w.nw_merges ->
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
    | Fvar' (r, _) -> [r]
    | _ -> []
  in
  match d with
  | Dtemplate (tps, _, inner) -> concepts tps @ declared_globals inner
  | Dnspace (w, ds) -> (match w with Some w -> [w.nw_ref] | None -> []) @ List.concat_map declared_globals ds
  | Dfun {df_path; _} -> List.map fst (dfun_path_list df_path)
  | Dstruct {ds_ref; ds_tparams; ds_fields; _} | Dfields {ds_ref; ds_tparams; ds_fields; _} ->
    (ds_ref :: concepts ds_tparams) @ List.concat_map field ds_fields
  | Dasgn {da_ref; _} -> [da_ref]
  | Dusing {du_name; du_tparams; _} -> du_name :: concepts du_tparams
  | Dstruct_fwd (tps, r) -> r :: concepts tps
  | Dmember_def {dm_owner; dm_enclosing; dm_tparams; dm_field} ->
    (dm_owner :: Option.cata (fun w -> [w.nw_ref]) [] dm_enclosing)
    @ concepts dm_tparams
    @ field (field_of_member dm_field, VPublic, SNoTag)
  | Denum {de_ref; _} -> [de_ref]
  | Dconcept (id, _) -> [id]
  | Dstatic_assert _ -> []

(* Of [globals], those whose name is decided -- printing decides none --
   asked for at each of [frames], each as the type and the expression
   printers may name it, and as the type printer may write it as a type's
   head. *)
let global_names frames globals =
  let decided r = Option.has_some (Common.decided_global_name r) in
  let globals =
    List.sort_uniq GlobRef.UserOrd.compare
      (List.concat_map (function GlobRef.ConstructRef (ind, _) as r -> [r; GlobRef.IndRef ind] | r -> [r]) globals)
  in
  let keys =
    List.concat_map
      (fun r ->
        Cpp_resolution.
          [ Unmapped (Type, r); Unmapped (Term, r); Short (Type, r); Short (Term, r); Class_concept r;
            Type_head (Glob_head, r) ]
        @
        match r with
        | GlobRef.IndRef _ -> Cpp_resolution.[Inductive_value r; Inductive_scope r; Type_head (Inductive_head, r)]
        | _ -> [] )
      (List.filter decided globals)
    @ Cpp_names.custom_texts_named globals @ Cpp_names.inline_customs_named globals
  in
  List.concat_map (fun frame -> List.map (fun key -> (frame, key)) keys) frames

(* The globals writing [ty] names: those its printing writes the names of
   ({!Cpp_demands.globals_of_type}), and the head of every global type in
   it, a custom whose text it is written from among them. *)
let type_globals ty = Cpp_demands.globals_of_type ty @ type_heads ty

(** The assertions [d] holds back, in the order it writes them: those that
    a class's concept holds of an instance where the concept is declared
    after the struct being written, because its requirements name the
    struct's own types. *)
let rec held_back_assertions ctx (d : Cpp_erasure.settled) =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> held_back_assertions ctx inner
  | Namespace (None, decls) -> List.concat_map (held_back_assertions ctx) decls
  | Namespace (Some w, members) ->
    if w.nw_merges then [] else List.concat_map (held_back_assertions ctx) members
  | Decl (Dstatic_assert (CPPconcept_app (class_ref, subject, tys), None)) when class_concept_held_back ctx class_ref ->
    [ { Cpp_ast.concept = Of_class (Cpp_ast.global_ref class_ref);
        subject = Instance {instance = Cpp_ast.global_ref subject; args = tys} } ]
  | Decl _ -> []

(** The structs and scoped enums [d] defines at namespace scope, written
    in the scope being written, in the order it defines them, each with the
    reference it is declared under, its definition's template head and its
    constraint. *)
let rec structs_defined (d : Cpp_erasure.settled) : Cpp_ast.defined list =
  match Cpp_erasure.view d with
  | Template (_, _, inner) -> structs_defined inner
  | Namespace (None, decls) -> List.concat_map structs_defined decls
  | Namespace (Some w, members) -> (
    match (members :> cpp_decl list) with
    | [Dstruct {ds_tparams; ds_constraint; _}] when w.nw_merges ->
      [Defined_struct {struct_ = w.nw_ref; name = As_inductive_wrapper; tparams = ds_tparams; constraint_ = ds_constraint}]
    | _ -> [] )
  | Decl (Dstruct {ds_ref; ds_tparams; ds_constraint; _}) ->
    [Defined_struct {struct_ = ds_ref; name = As_defined; tparams = ds_tparams; constraint_ = ds_constraint}]
  | Decl (Denum {de_ref; _}) -> [Defined_enum de_ref]
  | Decl _ -> []

let defined_ref : Cpp_ast.defined -> _ = function Defined_struct {struct_ = r; _} | Defined_enum r -> r

(** A forward declaration of a struct defined at namespace scope.

    A module struct can be emitted before an inductive a later module pulled
    up to global scope, so a member declaration may name a type whose
    definition comes further down the header ([static Prod<nat, nat>
    divmod(...)] ahead of [struct Prod]).  A declaration only needs the name
    to have been introduced, so the header's prologue declares them up front.
    Printed by the function that prints the definition's template head, so
    the two spellings of the parameter list cannot drift apart.

    A constrained template -- a [requires] clause on the struct, or a
    concept-kinded parameter -- names its concept, which need not be declared
    by that prologue, nor anywhere above the struct's first use; its
    declaration goes in front of the first chunk of the file that names the
    struct before defining it ({!Cpp.do_struct_with_decl_tracking}): a
    section-local instance's struct and the file module's struct can each
    name the other, [typename StateV<_tcI0>::state] in a member's signature
    against a call to that member in the instance's body.

    An opaque declaration of a scoped enum is one too: [enum class E;] is a
    complete type -- a scoped enum has a fixed underlying type -- so replaying
    it in the header prologue is enough for the members naming it ahead of
    its definition, which still follows in its own place. *)
type forward_declaration = {fwd_ref : GlobRef.t; fwd_tree : Cpp_ast.t; fwd_constrained : bool}

(* Whether [tparams] make the [requires] clause {!pp_requires_of_tparams}
   prints. *)
let makes_requires_clause ctx tparams =
  List.exists
    (fun (tt, _) ->
      match tt with
      | TTinvocable _ -> true
      | TTconcept (concept, _ :: _) -> not (class_concept_held_back ctx concept)
      | _ -> false )
    tparams

let constrained ctx : Cpp_ast.defined -> bool = function
  | Defined_struct {tparams; constraint_; _} ->
    Option.has_some constraint_ || makes_requires_clause ctx tparams
    || List.exists (function TTconcept _, _ -> true | _ -> false) tparams
  | Defined_enum _ -> false

(** The forward declarations of the structs and scoped enums [d], an element
    of the module [module_], written at the position [ctx], defines at
    namespace scope, in the order it defines them: none inside a struct,
    where a member is not nameable before its enclosing struct anyway. *)
let forward_declarations ctx ~module_ env (d : Cpp_erasure.settled) =
  if ctx.rc_in_struct then []
  else
    List.map
      (fun defined ->
        { fwd_ref = defined_ref defined;
          fwd_tree = Cpp_ast.elements ~source:module_ (Cpp_ast.forward_declaration env defined);
          fwd_constrained = constrained ctx defined } )
      (structs_defined d)

(* What writing the type constructor [x] -- a template template argument,
   naming the variables [vl] by index -- at [ctx] decides, without writing
   it: how it is written, decided there and noted ({!Cpp_print.tyctor_written}),
   the template synthesised for it collected where [ctx] collects them
   ({!Cpp_print.note_ctor_alias_spelled}); and, where it is written through
   its own head instead, the same for each type constructor that head
   writes.  A mapped or global head applied to arguments is written alone
   (its leading text, its bare name); a dependent member through its
   qualifier; anything else as its head, which is what its rendering up to
   its argument list writes. *)
let rec tyctor_spelled ctx vl x =
  let c = tyctor_constructor x in
  match tyctor_written ctx vl c with
  | Some (alias, _) -> note_ctor_alias_spelled ctx alias
  | None -> (
    match c with
    | Tglob (_, _ :: _, _) | Tforeign {fr_types = _ :: _; _} -> ()
    | Tqualified (base, _) -> tyctors_spelled ctx vl base
    | _ -> tyctors_spelled ctx vl c )

(* {!tyctor_spelled} at each type constructor writing [t] writes, in the
   order demands find them ({!Cpp_demands.tyctors_of_type}). *)
and tyctors_spelled ctx vl t =
  Cpp_demands.tyctors_of_type (fun ~vl ~owner:_ t -> match t with Ttyctor x -> tyctor_spelled ctx vl x | _ -> ()) ~vl t

(* [ctx], naming what writing [t] there names as resolved there. *)
let resolved_for ctx t =
  { ctx with
    rc_names =
      Names_resolved (Cpp_resolution.resolve (fun _ key -> live_value ctx key) (global_names [ctx.rc_frame] (type_globals t)))
  }

(** {2 Synthesised templates}

    Whether a type constructor written as a template template argument has
    a template name of its own, and the template synthesised for it where
    it has not, decided where planning spells it ({!Cpp_state.Deciding}):
    the printer reads the decision off the plan of the leaf it prints. *)

(** The module struct the template abbreviating [body], written in [file],
    has to be declared inside, if any: that of the module whose element is
    being written ({!Cpp_state.render_ctx}), where [body] names a global
    declared anywhere in the struct at namespace scope that encloses it --
    of that module, of one enclosing it, or of one nested in either.  Such
    a global is incomplete, or written bare, in front of that struct, and
    so means nothing at namespace scope; inside the module being written,
    every one declared ahead of the use is in scope.  In the implementation
    file, which writes no module struct, it is the struct whose members are
    defined out of line around it.  Where no module's element is being
    written, there is none. *)
let ctor_alias_home ctx body =
  match ctx.rc_module with
  | None -> None
  | Some cur ->
    let modpath_of = function
      | GlobRef.ConstRef c -> Some (Names.Constant.modpath c)
      | GlobRef.IndRef (kn, _) | GlobRef.ConstructRef ((kn, _), _) -> Some (Names.MutInd.modpath kn)
      | GlobRef.VarRef _ -> None
    in
    (* The struct at namespace scope [cur] is written in: what it declares,
       at any depth, is incomplete in front of it. *)
    let rec outermost mp =
      match mp with ModPath.MPdot (parent, _) when not (Table.is_modfile parent) -> outermost parent | _ -> mp
    in
    let struct_ = outermost cur in
    let rec inside mp =
      ModPath.equal mp struct_ || match mp with ModPath.MPdot (parent, _) -> inside parent | _ -> false
    in
    let names_struct =
      exists_cpp_type
        (function
          | Tglob (r, _, _) | Tforeign {fr_custom = r; _} -> (
            match modpath_of r with Some mp -> inside mp | None -> false )
          | _ -> false )
        body
    in
    if names_struct && not (Table.is_modfile cur) then Some cur else None

(** Where the template abbreviating [body], spelled at [ctx], is declared:
    in the struct of its home ({!ctor_alias_home}), or at namespace scope
    beneath the unit's files as what is visible at [ctx] sees them -- a
    module body's, or, spelled in another template's body, that
    template's. *)
let ctor_alias_declared ctx body : Cpp_ast.declared_in =
  match ctor_alias_home ctx body with
  | Some home -> In_struct_of home
  | None ->
    let visible = visibility_at ctx (Pp.str "a template is declared at namespace scope") in
    At_namespace_scope (List.rev (List.filter Table.is_modfile (Common.visible_mps visible)))

(** The visibility a template is declared, and so its body written, in: the
    body of its home module, as planned, or outside every module body. *)
let ctor_alias_visibility : Cpp_ast.declared_in -> _ = function
  | In_struct_of home -> (
    match Scope_plan.visibility home with
    | Some v -> v
    | None ->
      CErrors.anomaly
        Pp.(str "Crane: the module " ++ str (ModPath.to_string home) ++ str " has no planned visibility.") )
  | At_namespace_scope files -> Common.toplevel_visibility files

(** The position a template declared at [declared] is written at, in the
    file [ctx] is written in: at namespace scope; in the header, inside its
    home's struct, a class template where the home's struct is one; in the
    implementation, beside the definitions of its home's members, which are
    written out of line and qualify what they name by the struct they are
    members of.  The templates its body spells are collected where those
    spelled at [ctx] are. *)
let ctor_alias_render_ctx ctx (declared : Cpp_ast.declared_in) =
  let start =
    { (file_start ctx.rc_file) with
      rc_visibility = Some (ctor_alias_visibility declared);
      rc_aliases = ctx.rc_aliases }
  in
  match (declared, ctx.rc_file) with
  | At_namespace_scope _, _ -> start
  | In_struct_of home, Common.Intf ->
    {start with rc_in_struct = true; rc_in_template = Scope_plan.templated home; rc_module = Some home}
  | In_struct_of home, Common.Impl ->
    let out_of_line ol_scope = {ol_scope; ol_file_scope_types = file_scope_types_of Common.Impl} in
    {start with rc_scope = Option.map out_of_line (Scope_plan.of_module home); rc_module = Some home}

(* The indices of the type variables writing [t], naming the variables [vl]
   by index, writes, its type constructors written as [uses] says, read off
   its structure as the type printer walks it: a mapping writes the holes its
   pieces name and no other; a type constructor written through a synthesised
   template writes what a holder of it is applied to and nothing of its
   body, and one written through its own head writes what that head writes
   -- a mapped or global head applied to arguments writes none of them, a
   dependent member its qualifier, a variable itself. *)
let vars_written uses vl t =
  let rec go t =
    match t with
    | Tvar (Tv_index (i, _)) -> [i]
    | Tvar (Tv_named _) | Tinstance _ | Tpromoted _ | Thole | Tvoid | Tany | Topaque | Tauto | Tdecltype_auto
    | Terased _ | Tunresolved | Texpr_type _ ->
      []
    | Tid (_, args) | Tid_external (_, args) | Tglob (_, args, _) | Tvariant (_, args) -> List.concat_map go args
    | Tforeign {fr_types; fr_pieces; _} ->
      List.concat_map
        (function
          | Fp_type i | Fp_element (i, _) -> go (Option.default Tany (List.nth_opt fr_types i))
          | Fp_text _ | Fp_value _ | Fp_yields | Fp_result | Fp_statement_end -> [] )
        fr_pieces
    | Tfun (dom, cod) -> go cod @ List.concat_map go dom
    | Tconst t | Tshared_ptr t | Tref (_, t) | Tptr t | Tdecay t | Tnondeduced t | Tnamespace (_, t) | Tqualified (t, _) ->
      go t
    | Trebind (h, x) -> go h @ go x
    | Tapply (head, args) -> go head @ List.concat_map go args
    | Ttyctor x -> (
      let c = tyctor_constructor x in
      match List.find_opt (fun u -> compare u.tu_constructor c = 0 && u.tu_vars = vl) uses with
      | Some {tu_alias = Some (_, args); _} ->
        List.filter_map (function Captured_variable (i, _) -> Some i | Captured_instance _ -> None) args
      | Some {tu_alias = None; _} -> (
        match c with
        | Tglob (_, _ :: _, _) | Tforeign {fr_types = _ :: _; _} -> []
        | Tqualified (base, _) -> go base
        | c -> head c )
      | None ->
        CErrors.anomaly
          Pp.(str "Crane: a type constructor in a synthesised template's body was not decided where the body was.") )
  (* What a head written up to its argument list writes. *)
  and head = function
    | Tvar (Tv_index (i, _)) -> [i]
    | Tnamespace (_, t) -> head t
    | _ -> []
  in
  go t

(** The template synthesised for the type constructor [t], written as a
    template template argument, if it has no template name of its own, with
    the arguments a holder is applied to where it is written.

    A constructor applied to the sentinel is both the test and the alias body:
    where the rendering comes out as a head plus that one argument, the head
    is a template name and naming it is enough; where it does not, there is
    no head to name and an alias template is introduced.  [itree] is
    [std::shared_ptr<ITree<%t1>>] and a composite Rocq carrier is
    [std::pair<_CraneTcArg, Box<_CraneTcArg>>]; neither can be cut back, and
    the same reading of the same rendering covers both.

    A carrier built by the front end already has the sentinel standing where
    its argument goes -- it is the abstraction, not an application of one.  A
    custom mapping arrives applied to its real arguments, so the sentinel is
    put in the carrier's place first. *)
let rec ctor_alias_at ctx vl t =
  let custom () =
    match t with
    (* The sentinel in the last argument's place, its element hole holding
       the sentinel bare: the sentinel recurses through nothing. *)
    | Tforeign ({fr_types = _ :: _ as args; _} as fr) ->
      let last = List.length args - 1 in
      let probe =
        { fr with
          fr_types = List.filteri (fun i _ -> i < last) args @ [Thole];
          fr_values = [];
          fr_pieces = List.map (function Fp_element (i, _) when i = last -> Fp_element (i, None) | p -> p) fr.fr_pieces }
      in
      ctor_alias_of_probe ctx vl ~base:(Common.pp_global_name Type fr.fr_custom) (Tforeign probe)
    | _ -> None
  in
  if exists_cpp_type (fun s -> s = Thole) t then
    match ctor_alias_of_probe ctx vl ~base:"crane_carrier" t with
    | Some _ as alias -> alias
    | None -> custom ()
  else custom ()

(** The template synthesised for [probe], a type constructor applied to the
    sentinel, if its rendering is not a head applied to the sentinel.

    The body is rendered where the template is declared ({!ctor_alias_render_ctx}),
    what is visible there included, because that is where a [using] is read; every name it writes
    has to mean there what it means at the use. *)
and ctor_alias_of_probe ctx vl ~base probe =
  (* Every node of a type, in the order written, a type constructor's
     included: a carrier nested in the body as a template template argument
     is written through its own template, whose arguments name what it
     names. *)
  let visit t f = ignore (exists_cpp_type (fun t -> f t; false) t) in
  (* The template parameters of the enclosing declaration that the body
     names, each as the body writes it.  An alias whose body mentions one
     cannot live at namespace scope, so those are what the holder abstracts
     over. *)
  let captured probe =
    let seen = ref [] in
    visit probe (function
      | Tvar (Tv_index (i, name)) when not (List.mem_assoc i !seen) -> seen := !seen @ [(i, name)]
      | _ -> () );
    !seen
  in
  let written_var i name = Pp.string_of_ppcmds (pp_cpp_type_at ctx false vl (Tvar (Tv_index (i, name)))) in
  (* A captured parameter is named {e applied} to the alias's own
     argument -- that is what makes the body an abstraction rather than a
     type, and it is what lets the holder declare every parameter it
     takes as a type constructor.  A variable the body names bare is not
     a carrier parameter; it is a type the body mentions, and mentioning
     it at the use site writes a name from the declaration's quantifier.
     An instance method's body is emitted without that quantifier, so
     [crane_carrier_tch<T1>] there names a scope the function is not in.
     What the body has instead is the erasure it was emitted under, and
     [std::any] is how the rest of it already spells that. *)
  let applied_vars =
    let seen = ref [] in
    visit probe (function Tapply (Tvar (Tv_index (i, _)), _) -> seen := i :: !seen | _ -> ());
    !seen
  in
  (* A variable the body names bare is kept where it is a declared
     parameter -- named, as a plain family the declaration deapplied is
     -- and becomes a [typename] parameter of the holder. *)
  let bare_vars =
    let seen = ref [] in
    visit probe (function
      | Tvar (Tv_index (i, Some _)) when not (List.mem i applied_vars) -> seen := i :: !seen
      | _ -> () );
    !seen
  in
  let probe =
    map_cpp_type
      (function
        | Tvar (Tv_index (i, _))
          when not (List.mem i applied_vars || List.mem i bare_vars) ->
          Tany
        | t -> t )
      probe
  in
  let declared_in = ctor_alias_declared ctx probe in
  let render t = written_body (ctor_alias_render_ctx ctx declared_in) vl t in
  let rendered_with_uses = lazy (render probe) in
  let rendered = lazy (fst (Lazy.force rendered_with_uses)) in
  let head_alone () =
    let rendered = Lazy.force rendered in
    String.equal rendered (cut_at_argument_list rendered ^ "<" ^ ctor_alias_tvar ^ ">")
  in
  let alone =
    match applied_to_sentinel_alone ctx probe with
    | Some alone ->
      if Probe.checking () && alone <> head_alone () then
        Probe.violation "constructor alias shape"
          Pp.(str "the type constructor written " ++ str (Lazy.force rendered) ++ str " is read off its structure as "
              ++ str (if alone then "" else "not ") ++ str "a template name applied to its argument alone");
      alone
    | None ->
      Probe.hit "CTORALIAS_UNDECIDED" (fun () -> Lazy.force rendered);
      head_alone ()
  in
  if alone then None
  else
    let rendered = Lazy.force rendered in
    (* Only a name the body actually {e writes} has to be abstracted
       over.  A custom mapping's replacement text need not use every
       argument -- [itree]'s spells only its last -- so a parameter that
       the probe carries structurally but the rendering drops would
       otherwise mint a holder with an unused parameter, and the alias
       would be declared as a partial specialisation of nothing.  Which
       it writes is read off the structure the rendering walks
       ({!vars_written}); under [CRANE_CHECK_IR], reading it off the
       rendered text, as planning did before, must find the same. *)
    let written = vars_written (snd (Lazy.force rendered_with_uses)) vl probe in
    let all = captured probe in
    let captured = List.filter (fun (i, _) -> List.mem i written) all in
    ( if Probe.checking () then
        let names = identifier_tokens rendered in
        if List.filter (fun (i, name) -> List.mem (written_var i name) names) all <> captured then
          Probe.violation "captured variables"
            Pp.(str "the body " ++ str rendered ++ str " is read off its structure as writing other variables than its text names") );
    (* A class instance the body reads a type out of -- [typename
       _tcI0::ptr] -- is the enclosing declaration's parameter as much
       as a variable is, and is captured the same way. *)
    let instances =
      let seen = ref [] in
      visit probe (function
        | Tinstance (id, _) when not (List.exists (Id.equal id) !seen) -> seen := !seen @ [id]
        | _ -> () );
      !seen
    in
    match (captured, instances) with
    | [], [] ->
      Some
        ( { ca_base = base;
            ca_holder = None;
            ca_declared = declared_in;
            ca_body = rendered;
            ca_type = probe;
            ca_vars = vl;
            ca_uses = snd (Lazy.force rendered_with_uses) },
          [] )
    | vars, instances ->
      (* Rendered a second time with the captured names replaced by the
         holder's own, so that two declarations differing only in what
         they call their parameters share one holder.  A renamed variable
         is still a variable: a holder nested in the body captures it under
         its new name, and is applied to that. *)
      let var_names =
        List.mapi (fun k (i, _) -> (i, Generated_name.indexed (if List.mem i bare_vars then "P" else "F") k)) vars
      and instance_names = List.mapi (fun j id -> (id, Generated_name.indexed "P" (List.length vars + j))) instances in
      let renamed =
        rewrite_cpp_type
          (function
            | Tvar (Tv_index (i, _)) -> Option.map (fun name -> Tvar (Tv_index (i, Some name))) (List.assoc_opt i var_names)
            | Tinstance (id, c) -> (
              match List.find_opt (fun (id', _) -> Id.equal id id') instance_names with
              | Some (_, name) -> Some (Tinstance (name, c))
              | None -> None )
            | _ -> None )
          probe
      in
      let body, uses = render renamed in
      let params =
        List.map
          (fun (i, name) -> if List.mem i bare_vars then Cpp_ast.Type_parameter name else Constructor_parameter name)
          var_names
        @ List.map (fun (_, name) -> Cpp_ast.Type_parameter name) instance_names
      in
      Some
        ( {ca_base = base; ca_holder = Some params; ca_declared = declared_in; ca_body = body; ca_type = renamed; ca_vars = vl; ca_uses = uses},
          List.map (fun (i, name) -> Cpp_state.Captured_variable (i, name)) vars
          @ List.map (fun id -> Cpp_state.Captured_instance id) instances )

(** [t] as the type constructors in it are written at [ctx]: decided there
    and noted ({!Cpp_state.Deciding}). *)
and deciding ctx noted = {ctx with rc_tyctors = Deciding {decide = ctor_alias_at; noted}}

(** The body [t] of a synthesised template, naming the variables [vl] by
    index, written at [at], where the template is declared: how it writes
    the type constructors in it, decided there first ({!tyctors_spelled}),
    and the text, its names resolved there, which is the template's name's
    digest.  Under [CRANE_CHECK_IR], deciding them by rendering the body,
    as planning did before, must decide the same. *)
and written_body at vl t =
  let noted = ref [] in
  let found_before = Option.map ( ! ) at.rc_aliases in
  tyctors_spelled (deciding at noted) vl t;
  let uses = !noted in
  let body = Pp.string_of_ppcmds (pp_cpp_type_at {(resolved_for at t) with rc_tyctors = Planned uses} false vl t) in
  ( if Probe.checking () then
      let noted' = ref [] in
      let at' = {at with rc_aliases = Option.map ref found_before} in
      let body' = Pp.string_of_ppcmds (pp_cpp_type_at (deciding (resolved_for at' t) noted') false vl t) in
      if (not (String.equal body body')) || compare !noted' uses <> 0
         || compare (Option.map ( ! ) at'.rc_aliases) (Option.map ( ! ) at.rc_aliases) <> 0
      then
        Probe.violation "structural spelling"
          (Pp.str ("the body " ^ body ^ " decides other type constructors than rendering it does")) );
  (body, uses)

(** The synthesised templates spelled at the position [ctx] at the type
    constructors [visit] calls its argument at, in the order spelled -- one
    written in another's body ahead of it -- each decided there without
    writing it ({!tyctor_spelled}), inside the struct of the inductive whose
    members are written around it, if any ({!Cpp_resolution.Inductive_struct});
    and how each type constructor is written, in the order first spelled.
    Under [CRANE_CHECK_IR], rendering each, as planning did before, must
    decide the same. *)
let ctor_aliases_found ctx visit =
  let found = ref [] and noted = ref [] in
  let ctx = deciding {ctx with rc_aliases = Some found} noted in
  visit (fun ~vl ~owner t ->
      match t with
      | Ttyctor x ->
        let spell ctx = tyctor_spelled ctx vl x in
        ( match owner with Some r -> enter_from ctx (Inductive_struct r) spell | None -> spell ctx )
      | _ -> () );
  ( if Probe.checking () then
      let found' = ref [] and noted' = ref [] in
      let ctx' = deciding {ctx with rc_aliases = Some found'} noted' in
      visit (fun ~vl ~owner t ->
          match t with
          | Ttyctor _ ->
            let spell ctx = ignore (pp_cpp_type_at (resolved_for ctx t) false vl t) in
            ( match owner with Some r -> enter_from ctx' (Inductive_struct r) spell | None -> spell ctx' )
          | _ -> () );
      if compare !found' !found <> 0 || compare !noted' !noted <> 0 then
        Probe.violation "structural spelling"
          (Pp.str "a declaration decides other type constructors than rendering them does") );
  (!found, !noted)

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

let template_param_globals tps =
  let types = ref [] in
  ignore (map_tparams (fun t -> types := t :: !types; t) tps);
  List.filter_map (function TTconcept (r, _), _ -> Some r | _ -> None) tps @ List.concat_map type_globals !types

let declaration_globals (d : Cpp_erasure.settled) =
  let globals = ref [] in
  Minicpp.iter_globrefs (fun r -> globals := r :: !globals) (d :> cpp_decl);
  !globals @ globals_written_beside (d :> cpp_decl) @ declared_globals (d :> cpp_decl)

(* The structs and scoped enums [d] defines, each as its definition is
   named. *)
let rec defined_types : cpp_decl -> _ = function
  | Dtemplate (_, _, inner) -> defined_types inner
  | Dnspace (_, ds) -> List.concat_map defined_types ds
  | Dstruct {ds_ref; _} -> [Cpp_resolution.Definition (Struct_definition, ds_ref)]
  | Denum {de_ref; _} -> [Definition (Enum_definition, de_ref)]
  | _ -> []

let declaration_names d =
  let frames = declaration_frames d in
  global_names frames (declaration_globals d)
  @ List.concat_map (fun frame -> List.map (fun key -> (frame, key)) (defined_types (d :> cpp_decl))) frames

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
    ([], Cpp_resolution.Definition (Struct_definition, struct_))
    :: global_names [[]] ((struct_ :: template_param_globals tparams) @ Option.cata constraint_globals [] constraint_)
  | Forward_declaration {defined = Defined_enum r; _} -> ([], Cpp_resolution.Definition (Enum_definition, r)) :: global_names [[]] [r]
  | Synthesised_template {body; _} -> global_names [[]] (type_globals body)
  | Assertion {subject = Module _; _} | Global_alias (Alias_of_module _) | Modtype_concept _ | Module_alias _
  | Functor_alias _ | Derived_functor _ ->
    []

(* [ctx], writing the declaration [settled] written in the module it names
   there: its names resolved there first, at each frame printing it enters,
   and its type constructors written as planned, or, where nothing is
   planned yet, as decided. *)
let writing ctx (settled : Cpp_erasure.settled) =
  let names =
    Cpp_resolution.resolve (fun frame key -> at_frame ctx frame (fun c -> live_value c key)) (declaration_names settled)
  in
  let ctx = {ctx with rc_names = Names_resolved names} in
  if not (alias_plan_made ()) then deciding ctx (ref [])
  else
    match planned_tyctors ~file:ctx.rc_file ~module_:(module_written ctx) (Written_declaration (settled :> cpp_decl)) with
    | Some uses -> {ctx with rc_tyctors = Planned uses}
    | None -> deciding ctx (ref [])

(** The type names [d], written at namespace scope at the position [ctx],
    introduces there, as the printer writes them ({!Cpp_print.decl_type_name}), the names it writes
    resolved there first: those of the structs it defines, and the inline
    custom texts of the aliases and wrappers it declares. *)
let file_scope_types ctx (d : Cpp_erasure.settled) =
  let rec declared : cpp_decl -> _ = function
    | Dtemplate (_, _, inner) -> declared inner
    | Dusing u -> [u.du_name]
    | Dnspace (Some w, _) -> [w.nw_ref]
    | _ -> []
  in
  let rec keys (d : Cpp_erasure.settled) =
    let declared = declared (d :> cpp_decl) in
    Cpp_names.inline_customs_named declared
    @ List.map (fun r -> Cpp_resolution.Short (Type, r)) declared
    @
    match Cpp_erasure.view d with
    | Template (_, _, inner) -> keys inner
    | Namespace (None, decls) -> List.concat_map keys decls
    | Decl (Dstruct {ds_ref; _}) -> [Cpp_resolution.Definition (Struct_definition, ds_ref)]
    | Namespace (Some _, _) | Decl _ -> []
  in
  let names = Cpp_resolution.resolve (fun _ key -> live_value ctx key) (List.map (fun key -> (ctx.rc_frame, key)) (keys d)) in
  let ctx = {ctx with rc_names = Names_resolved names} in
  let rec go (d : Cpp_erasure.settled) =
    (match decl_type_name ctx (d :> cpp_decl) with Some name -> [name] | None -> [])
    @
    match Cpp_erasure.view d with
    | Template (_, _, inner) -> go inner
    | Namespace (None, decls) -> List.concat_map go decls
    | Decl (Dstruct {ds_ref; _}) -> [struct_definition_name ctx ds_ref]
    | Namespace (Some _, _) | Decl _ -> []
  in
  List.map Pp.string_of_ppcmds (go d)

(** The names of the wrapper structs [d] writes around something other than
    a sole struct merged into them, in the order it writes them: the structs
    another wrapper's declarations can be written into, spelled to be
    compared with them ({!Cpp_names.wrapper_spelling}). *)
let unmerged_wrappers_written d = unmerged_wrappers_named ~name:wrapper_spelling d

(** The wrapper structs [d] writes that hold a wrapper module's
    declarations: those [homed] names, each with the module. *)
let absorbed_by ~homed d = List.filter (fun name -> List.mem_assoc name homed) (unmerged_wrappers_written d)

let absorbs ~homed d = absorbed_by ~homed d <> []

let read_decl ctx env settled = read_cpp_decl (writing ctx settled) env settled

let printed_decl ctx env settled = (read_decl ctx env settled, printed_needs ctx settled)

(** [settled], printed where it is made, with what placing the declarations
    it needs reads ({!needs_of}). *)
let write_decl ctx env settled =
  let text, needs = printed_decl ctx env settled in
  Cpp_ast.decl ~needs text

(** [settled], which {!absorbs}, written where it is made ({!absorbing_at}),
    behind what placing the declarations it needs reads. *)
let write_absorbing ctx ~homed env (settled : Cpp_erasure.settled) =
  let tyctors =
    if not (alias_plan_made ()) then None
    else planned_tyctors ~file:ctx.rc_file ~module_:(module_written ctx) (Written_declaration (settled :> cpp_decl))
  in
  let tree = absorbing_at (writing ctx settled) ~homed ?tyctors env settled in
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
    [CRANE_CHECK_IR], what a declaration, a record's fields or a synthesised
    template need, and how they write their type constructors, read again
    where they are printed, must be what was planned where they were made. *)
let print_unprinted ctx ~modtype_concept ~assertion (u : Cpp_ast.unprinted) =
  let text = Cpp_print.print_unprinted ctx ~modtype_concept ~assertion u in
  ( if Probe.checking () then
      let tyctors =
        match u.declaration with
        | Declaration {settled; _} -> Some (ctor_aliases_written ctx settled).read_uses
        | Fields {record; vars; fields} -> Some (ctor_aliases_of_fields ctx ~vl:vars record (List.map snd fields)).read_uses
        | Synthesised_template s -> Some (snd (written_body ctx s.vars s.body))
        | _ -> u.tyctors
      in
      if Option.has_some u.tyctors && tyctors <> u.tyctors then
        Probe.violation "constructor alias uses"
          (Pp.str "a declaration printed where the tree puts it writes its type constructors otherwise than planned");
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
