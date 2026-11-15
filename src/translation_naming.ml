(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ names of an inductive's constructors: the factory method a
    constructor is built through, and the struct field each of its arguments
    is stored in, from the kernel's binder names and an [Arguments]
    renaming, registered in {!Common.ctor_field_names}.  Read by lowering,
    {!Gen_inductives} and the printer. *)

open Common
open Names
open Util
open Type_util

(** The C++ name of the inductive that [cref] constructs, or [""] when [cref]
    is not a constructor reference. *)
let owning_type_name cref =
  match cref with
  | GlobRef.ConstructRef ((kn, i), _) ->
    Common.pp_global_name Type (GlobRef.IndRef (kn, i))
  | _ -> ""

(** Whether the module that declares constructor [cref]'s inductive also
    declares an inductive labelled [s].  Its struct sits in that module's
    scope, so a member named [s] would hide the type from the members after
    it: a record [pt] spelled in a later factory's signature. *)
let shadows_module_type cref s =
  match cref with
  | GlobRef.ConstructRef ((kn, _), _) ->
    Environ.mem_mind (MutInd.make2 (MutInd.modpath kn) (Label.make s)) (Global.env ())
  | _ -> false

(** The factory method name for constructor [cref] (its struct's name falls
    back to [ctor<fallback_idx>] when [cref] is not a constructor).
    Factory names are the lowercase of the constructor struct name
    (e.g. [Cons] -> ["cons"]). If the lowercased name collides with a C++
    keyword, one of {!Common.inductive_generated_members}, the enclosing
    type's own name (which C++ treats as a constructor declaration), or a
    type declared in the inductive's module ({!shadows_module_type}), the
    original PascalCase is kept with a trailing underscore
    (e.g. [Char] -> ["Char_"]). *)
let factory_name_of_ctor ?fallback_idx cref =
  let ctor_struct_name = ctor_struct_name_of_ref ?fallback_idx cref in
  let lc = String.lowercase_ascii ctor_struct_name in
  let collides =
    Common.is_reserved_cpp_name lc
    || lc = String.lowercase_ascii (owning_type_name cref)
    || Id.Set.mem (Id.of_string lc) Common.inductive_generated_members
    || shadows_module_type cref lc
  in
  if collides then Generated_name.separate_underscores (ctor_struct_name ^ "_")
  else lc

(** {2 Named Constructor Fields}

    Constructor struct fields in C++ are named using Rocq binder names when
    available.  For example, [Node (left : tree) (v : A) (right : tree)]
    generates fields [d_left], [d_v], [d_right] instead of [d_a0], [d_a1],
    [d_a2].

    The pipeline:
    + Extraction ({!Extraction.extract_really_ind}) populates
      [Core.Inductive.Packet.t.constructor_argument_names] from the kernel binder names.
    + {!compute_and_register_field_names} transforms each binder into a
      C++-safe identifier and registers the mapping in
      {!Common.ctor_field_names}.
    + Access sites (the inductive and record method generators in
      {!Gen_inductives}, record reuse, {!Loopify_tmc.patch_cell_field})
      call {!Common.lookup_ctor_field_name} to resolve field names. *)

(** Sanitize a Rocq binder name for use as a C++ struct field identifier.
    Lowercases the name, strips trailing primes ([a'] -> [a], [x''] -> [x]),
    and replaces non-alphanumeric characters (except [_]) with underscores.
    Returns [None] if the result is empty or starts with a digit, in which
    case the caller falls back to the generic positional name [d_aJ].

    @param name  the raw Rocq binder name (e.g. ["left"], ["a'"], ["1st"]) *)
let sanitize_binder_name name =
  let lc = String.lowercase_ascii name in
  let len = String.length lc in
  (* Strip trailing primes: [a'''] → [a] *)
  let rec strip_end i =
    if i <= 0 then 0
    else if lc.[i - 1] = '\'' then strip_end (i - 1)
    else i
  in
  let end_pos = strip_end len in
  if end_pos = 0 then None
  else
    let s = String.sub lc 0 end_pos in
    (* Replace non-C++ chars with underscores *)
    let buf = Buffer.create (String.length s) in
    String.iter
      (fun c ->
        if (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_' then
          Buffer.add_char buf c
        else
          Buffer.add_char buf '_' )
      s;
    let result = Buffer.contents buf in
    if String.length result = 0 || (result.[0] >= '0' && result.[0] <= '9') then
      None
    else
      Some result

(** Derive the C++ field name string for constructor argument [k].
    Returns ["d_<sanitized_name>"] when a valid binder name exists and does
    not collide with a C++ keyword, or the positional name ["d_a<k>"]
    otherwise.

    @param consarg_names  binder names from [Core.Inductive.Packet.t.constructor_argument_names]
    @param k              0-based field index *)
let field_name_str_of_idx consarg_names k =
  match List.nth_opt consarg_names k with
  | Some (Some id) -> (
    match sanitize_binder_name (Id.to_string id) with
    | Some sanitized ->
      if Common.is_reserved_cpp_name sanitized then
        field_param_name k
      else
        if Table.std_lib () = "BDE" then "d_" ^ sanitized else sanitized
    | None -> field_param_name k )
  | _ -> field_param_name k

(** Compute and register the C++ field name for constructor field [j].
    Registers two entries:
    - [ctor_field_names]: the pretty field name (used for struct declarations
      and member access), derived from [field_consarg_names] which may include
      names supplied by [Arguments_renaming].
    - [ctor_bind_names]: the base name for structured-binding variables in
      pattern matches, derived from [bind_consarg_names] (kernel-only).  When
      the kernel binder is anonymous ([None]) the indexed fallback [a0]/[a1]/...
      is used unconditionally to prevent variable-shadowing in nested matches.

    @param ctor_struct_name   PascalCase name of the constructor struct
    @param field_consarg_names  field declaration names (kernel + Arguments override)
    @param bind_consarg_names   binding variable names (kernel only)
    @param _n_fields            total field count (unused but kept for symmetry)
    @param j                    0-based field index *)
let compute_field_name ~owner ctor_struct_name field_consarg_names
    bind_consarg_names _n_fields j =
  let base_str = field_name_str_of_idx field_consarg_names j in
  (* A field shares its scope with the earlier fields, with the factory method,
     with the members the struct generates for itself, and with the type names
     visible there -- its own struct and the inductive that struct belongs to,
     either of which a same-named member would hide.  All are resolved the same
     way, by falling back to the indexed form. *)
  let type_name = owning_type_name owner in
  let reserved =
    Id.Set.union Common.inductive_generated_members
      (Id.Set.of_list
         (List.map Id.of_string
            ( ctor_struct_name :: type_name
              :: factory_name_of_ctor owner
              :: List.init j (field_name_str_of_idx field_consarg_names) ) ))
  in
  let needs_index = Id.Set.mem (Id.of_string base_str) reserved in
  let field_str =
    if needs_index then base_str ^ "_" ^ string_of_int j else base_str
  in
  let field_id = Id.of_string field_str in
  register_ctor_field_name ~owner ctor_struct_name j field_id;
  (* Binding variable name: use indexed fallback for anonymous kernel binders
     to prevent shadowing when nested matches on the same type reuse [a0]/[l0]. *)
  let bind_id =
    match List.nth_opt bind_consarg_names j with
    | Some (Some _) -> field_id  (* kernel-named: same as field for readability *)
    | _ -> field_param_id j      (* anonymous kernel binder: safe indexed fallback *)
  in
  register_ctor_bind_name ~owner ctor_struct_name j bind_id;
  field_id

(** Compute and register field names for all [n_fields] fields of a
    constructor struct.  [field_consarg_names] supplies the pretty names used
    for struct field declarations (may include [Arguments_renaming] overrides);
    [bind_consarg_names] supplies the kernel-only names used for structured-
    binding variable generation. *)
let compute_and_register_field_names ~owner ctor_struct_name
    field_consarg_names bind_consarg_names n_fields =
  List.init n_fields (fun j ->
    compute_field_name ~owner ctor_struct_name field_consarg_names
      bind_consarg_names n_fields j)

(** Augment [kernel_arg_names] with names from an [Arguments] declaration.
    Where [kernel_arg_names] has [None] (anonymous binder), the corresponding
    entry from [Arguments_renaming.arguments_names] is used if present and
    non-anonymous.  Kernel-named entries ([Some _]) are never overridden.
    Returns [kernel_arg_names] unchanged if [Arguments_renaming] has no entry
    for [cref] or if all kernel binders are already named. *)
let augment_with_args_renaming cref kernel_arg_names =
  if List.for_all (fun n -> n <> None) kernel_arg_names then
    kernel_arg_names
  else
    try
      let n_params =
        match cref with
        | GlobRef.ConstructRef ((kn, _), _) ->
          (try (Global.lookup_mind kn).mind_nparams
           with _ -> 0)
        | _ -> 0
      in
      let all_override = Arguments_renaming.arguments_names cref in
      let override = List.skipn n_params all_override in
      List.map2
        (fun kern over ->
          match kern with
          | Some _ -> kern
          | None ->
            (match over with
             | Names.Name id -> Some id
             | Names.Anonymous -> None))
        kernel_arg_names override
    with Not_found | Invalid_argument _ -> kernel_arg_names
