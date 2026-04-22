(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Pretty-printing utilities, name resolution, and renaming for extracted code.
*)

open Pp
open Util
open Names
open ModPath
open Namegen
open Nameops
open Table
open Miniml
open Mlutil

(** {2 Generic utility functions} *)

(** [contains_substring haystack needle] checks if [haystack] contains [needle].
    Note: String.contains checks for a char; this checks for a substring. *)
let contains_substring haystack needle =
  try
    ignore (Str.search_forward (Str.regexp_string needle) haystack 0);
    true
  with Not_found -> false

(** [last lst] returns the last element of a non-empty list.
    @raise Failure if the list is empty. *)
let last lst =
  let rec aux a = function
    | [] -> a
    | b :: rest -> aux b rest
  in
  match lst with
  | a :: rest -> aux a rest
  | [] -> failwith "last: empty list"

(** [last_two lst] returns the last two elements of a list with at least two
    elements.
    @raise Failure if the list has fewer than two elements. *)
let last_two lst =
  let rec aux (a, b) = function
    | [] -> (a, b)
    | c :: rest -> aux (b, c) rest
  in
  match lst with
  | a :: b :: rest -> aux (a, b) rest
  | _ -> failwith "last_two: list has fewer than 2 elements"

(** [extract_at_pos pos lst] extracts the element at position [pos] from [lst].
    Returns (Some element, remaining_list) or (None, original_list) if pos is
    out of bounds. *)
let extract_at_pos pos lst =
  let rec aux i acc = function
    | [] -> (None, List.rev acc)
    | x :: rest ->
      if i = pos then
        (Some x, List.rev_append acc rest)
      else
        aux (i + 1) (x :: acc) rest
  in
  aux 0 [] lst

(** [intersperse sep lst] inserts [sep] between each element of [lst]. *)
let rec intersperse sep = function
  | [] -> []
  | x :: xs -> x :: prepend_to_all sep xs

(** Prepend [sep] before every element of the list. *)
and prepend_to_all sep = function
  | [] -> []
  | x :: xs -> sep :: x :: prepend_to_all sep xs

(** Convert an identifier to ASCII, warning on double underscores. *)
let ascii_of_id id =
  let s = Id.to_string id in
  for i = 0 to String.length s - 2 do
    if s.[i] == '_' && s.[i + 1] == '_' then warning_id s
  done;
  Unicode.ascii_of_ident s

(** Test if a module path is a bound module parameter. *)
let is_mp_bound = function
  | MPbound _ -> true
  | _ -> false

(** {2 Pretty-print utility functions} *)

(** Wrap in parentheses if [par] is true. *)
let pp_par par st = if par then str "(" ++ st ++ str ")" else st

(** [pp_apply] : a head part applied to arguments, possibly with parenthesis *)

let pp_apply st par args =
  match args with
  | [] -> st
  | _ -> hov 2 (pp_par par (st ++ spc () ++ prlist_with_sep spc identity args))

(** Apply function to arguments with C++ syntax (commas, parens). *)
let pp_apply_cpp st args =
  match args with
  | [] -> st
  | _ ->
    hov 2 (st ++ str "(" ++ prlist_with_sep (fun _ -> str ", ") identity args)
    ++ str ")"

(** Same as [pp_apply], but with also protection of the head by parenthesis *)

let pp_apply2 st par args =
  let par' = (not (List.is_empty args)) || par in
  pp_apply (pp_par par' st) par args

(** Print a list of identifiers as space-separated bindings. *)
let pr_binding = function
  | [] -> mt ()
  | l -> str " " ++ prlist_with_sep (fun () -> str " ") Id.print l

(** Print elements as a tuple; single elements are not parenthesized. *)
let pp_tuple_light f = function
  | [] -> mt ()
  | [x] -> f true x
  | l -> pp_par true (prlist_with_sep (fun () -> str "," ++ spc ()) (f false) l)

(** Print elements as a comma-separated tuple with parens. *)
let pp_tuple f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (prlist_with_sep (fun () -> str "," ++ spc ()) f l)

(** Print elements as comma-separated list without parens. *)
let pp_list f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> prlist_with_sep (fun () -> str "," ++ spc ()) f l

(** Print elements as comma-separated list with newlines. *)
let pp_list_newline f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> prlist_with_sep (fun () -> str "," ++ fnl ()) f l

(** Print elements as newline-separated statements. *)
let pp_list_stmt f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> prlist_with_sep fnl f l

(** Print elements as a boxed tuple with line-break hints. *)
let pp_boxed_tuple f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (hov 0 (prlist_with_sep (fun () -> str "," ++ spc ()) f l))

(** Print elements as semicolon-separated array. *)
let pp_array f = function
  | [] -> mt ()
  | [x] -> f x
  | l -> pp_par true (prlist_with_sep (fun () -> str ";" ++ spc ()) f l)

(** By default, in module Format, you can do horizontal placing of blocks even
    if they include newlines, as long as the number of chars in the blocks is
    less that a line length. To avoid this awkward situation, we attach a big
    virtual size to [fnl] newlines. *)

(* EG: This looks quite suspicious... but beware of bugs *)
(* let fnl () = stras (1000000,"") ++ fnl () *)
(** Shadow [Pp.fnl] to attach a large virtual size, preventing Pp from
    collapsing lines. *)
let fnl () = fnl ()

(** Two consecutive newlines. *)
let fnl2 () = fnl () ++ fnl ()

(** Space or empty based on boolean. *)
let space_if = function
  | true -> str " "
  | false -> mt ()

(** Test if string starts with prefix. *)
let begins_with s prefix =
  let len = String.length prefix in
  String.length s >= len && String.equal (String.sub s 0 len) prefix

(** Test if string matches the pattern "CoqNNN" (legacy naming). *)
let begins_with_CoqXX s =
  let n = String.length s in
  n >= 4
  && s.[0] == 'C'
  && s.[1] == 'o'
  && s.[2] == 'q'
  &&
  let i = ref 3 in
  try
    while !i < n do
      match s.[!i] with
      | '_' -> i := n (*Stop*)
      | '0' .. '9' -> incr i
      | _ -> raise Not_found
    done;
    true
  with Not_found -> false

(** Identity function (historically removed quotes). *)
let unquote s = s

(** Join non-empty strings with a delimiter. *)
let rec qualify delim = function
  | [] -> CErrors.anomaly (Pp.str "qualify: empty list")
  | [s] -> s
  | "" :: l -> qualify delim l
  | s :: l -> s ^ delim ^ qualify delim l

(** Join strings with "::" for C++ namespace qualification. *)
let dottify = qualify "::"

(** {2 Uppercase/lowercase renamings} *)

(** Test if string starts with uppercase. *)
let is_upper s =
  match s.[0] with
  | 'A' .. 'Z' -> true
  | _ -> false

(** Test if string starts with lowercase. *)
let is_lower s =
  match s.[0] with
  | 'a' .. 'z' | '_' -> true
  | _ -> false

(** Convert identifier to lowercase. *)
let lowercase_id id = Id.of_string (String.uncapitalize_ascii (ascii_of_id id))

(** Convert identifier to uppercase. *)
let uppercase_id id =
  let s = ascii_of_id id in
  assert (not (String.is_empty s));
  if s.[0] == '_' then
    Id.of_string ("Coq_" ^ s)
  else
    Id.of_string (String.capitalize_ascii s)

(** Replace prime characters (') with underscores. *)
let remove_prime_id id =
  let s = String.map (fun c -> if c = '\'' then '_' else c) (ascii_of_id id) in
  Id.of_string s

(** Kind of global identifier: term, type, constructor, or module. *)
type kind =
  | Term
  | Type
  | Cons
  | Mod

(** Ordered comparison for (kind, string) pairs. *)
module KOrd = struct
  type t = kind * string

  let compare (k1, s1) (k2, s2) =
    let c =
      Stdlib.compare k1 k2
      (* OK *)
    in
    if c = 0 then
      String.compare s1 s2
    else
      c
end

(** Map keyed by (kind, string) pairs. *)
module KMap = Map.Make (KOrd)

(** Test if kind requires uppercase (constructors, modules). *)
let upperkind = function
  | Type -> false
  | Term -> false
  | Cons | Mod -> true

(** Apply case convention to identifier based on kind (currently identity). *)
let kindcase_id k id =
  id (* if upperkind k then uppercase_id id else lowercase_id id *)

(** {2 de Bruijn environments for programs} *)

(** de Bruijn environment: names in scope and avoided names. *)
type env = Id.t list * Id.Set.t

(** {2 Generic renaming for local variable names} *)

(** Find a fresh name for [id] by incrementing subscript until no collision. *)
let rec rename_id id avoid =
  let id = remove_prime_id id in
  if Id.Set.mem id avoid then rename_id (increment_subscript id) avoid else id

(** Shared helper for renaming variables with optional extra data. Takes a
    projection to extract the identifier, a constructor to rebuild the element,
    and processes the list in reverse order to maintain the same renaming
    behavior as the original functions. *)
let rec rename_vars_gen project rebuild avoid = function
  | [] -> ([], avoid)
  | elem :: elems ->
    let elems', avoid = rename_vars_gen project rebuild avoid elems in
    let id = project elem in
    let id' = rename_id (lowercase_id id) avoid in
    (rebuild id' elem :: elems', Id.Set.add id' avoid)

(** Rename a list of variables to fresh lowercase names. *)
let rename_vars avoid ids =
  rename_vars_gen (fun id -> id) (fun id' _ -> id') avoid ids

(** Rename a list of (id, type) pairs to fresh lowercase names. *)
let rename_vars' avoid pairs =
  rename_vars_gen (fun (id, _) -> id) (fun id' (_, ty) -> (id', ty)) avoid pairs

(** Rename type variables to fresh lowercase names. *)
let rename_tvars avoid l =
  let rec rename avoid = function
    | [] -> ([], avoid)
    | id :: idl ->
      let id = rename_id (lowercase_id id) avoid in
      let idl, avoid = rename (Id.Set.add id avoid) idl in
      (id :: idl, avoid)
  in
  fst (rename avoid l)

(** Push new variable names into the de Bruijn environment. *)
let push_vars ids (db, avoid) =
  let ids', avoid' = rename_vars avoid ids in
  (ids', (ids' @ db, avoid'))

(** Push new (id, type) pairs into the de Bruijn environment. *)
let push_vars' ids (db, avoid) =
  let ids', avoid' = rename_vars' avoid ids in
  (ids', (List.map fst ids' @ db, avoid'))

(** Look up a de Bruijn index in the environment. *)
let get_db_name n (db, _) = List.nth db (pred n)

(** {1 Renamings of global objects} *)

(** {2 Tables of global renamings} *)

(** Register/run cleanup functions for renaming tables. *)
let register_cleanup, do_cleanup =
  let funs = ref [] in
  ((fun f -> funs := f :: !funs), fun () -> List.iter (fun f -> f ()) !funs)

(** Extraction phase: pre-scan, implementation, or interface. *)
type phase =
  | Pre
  | Impl
  | Intf

(** Get/set the current extraction phase. *)
let set_phase, get_phase =
  let ph = ref Impl in
  (( := ) ph, fun () -> !ph)

(** Get/set the set of reserved keywords. *)
let set_keywords, get_keywords =
  let k = ref Id.Set.empty in
  (( := ) k, fun () -> !k)

(** Track globally used identifiers to avoid collisions. *)
let add_global_ids, get_global_ids =
  let ids = ref Id.Set.empty in
  register_cleanup (fun () -> ids := get_keywords ());
  let add s = ids := Id.Set.add s !ids
  and get () = !ids in
  (add, get)

(** Map keyed by (MutInd.t, int) pairs for per-inductive tracking. Per-inductive
    constructor name tracking: constructors of the same inductive must have
    distinct C++ names (e.g. enum members must be unique). *)
module IndKey = struct
  type t = Names.MutInd.t * int

  let compare (m1, i1) (m2, i2) =
    let c = Names.MutInd.CanOrd.compare m1 m2 in
    if c = 0 then Int.compare i1 i2 else c
end

(** Map keyed by IndKey. *)
module IndMap = Map.Make (IndKey)

(** Track constructor names per inductive to prevent duplicates. *)
let add_ctor_sibling, get_ctor_siblings =
  let tbl = ref IndMap.empty in
  register_cleanup (fun () -> tbl := IndMap.empty);
  let add ind id =
    let cur = try IndMap.find ind !tbl with Not_found -> Id.Set.empty in
    tbl := IndMap.add ind (Id.Set.add id cur) !tbl
  and get ind = try IndMap.find ind !tbl with Not_found -> Id.Set.empty in
  (add, get)

(** Track sibling names per module path to prevent duplicates from escaping.
    Per-module-path sibling name tracking for non-constructor globals. Used to
    detect collisions caused by keyword/prime escaping (e.g. double → double_
    colliding with an existing double_). *)
let add_mp_sibling, get_mp_siblings =
  let tbl = ref MPmap.empty in
  register_cleanup (fun () -> tbl := MPmap.empty);
  let add mp id =
    let cur = try MPmap.find mp !tbl with Not_found -> Id.Set.empty in
    tbl := MPmap.add mp (Id.Set.add id cur) !tbl
  and get mp = try MPmap.find mp !tbl with Not_found -> Id.Set.empty in
  (add, get)

(* When a module and an inductive type with the same C++ name are siblings
   in the same enclosing scope, the module is renamed with a "_Mod" suffix.
   Maps the module's ModPath.t to the renamed C++ name.  Populated by
   detect_sibling_module_inductive_collisions, consulted by mp_renaming_fun. *)
let sibling_collision_renames : (ModPath.t, string) Hashtbl.t =
  Hashtbl.create 8

let () = register_cleanup (fun () -> Hashtbl.clear sibling_collision_renames)

(** Create a fresh de Bruijn environment with current global ids. *)
let empty_env () = ([], get_global_ids ())

(** We might have built [global_reference] whose canonical part is inaccurate.
    We must hence compare only the user part, hence using a Hashtbl might be
    incorrect *)

(** Create a mutable Id.Map with optional auto-cleanup. *)
let mktable_id autoclean =
  let m = ref Id.Map.empty in
  let clear () = m := Id.Map.empty in
  if autoclean then register_cleanup clear;
  ((fun r v -> m := Id.Map.add r v !m), (fun r -> Id.Map.find r !m), clear)

(** Create a mutable Refmap' with optional auto-cleanup. *)
let mktable_ref autoclean =
  let m = ref Refmap'.empty in
  let clear () = m := Refmap'.empty in
  if autoclean then register_cleanup clear;
  ((fun r v -> m := Refmap'.add r v !m), (fun r -> Refmap'.find r !m), clear)

(** Create a mutable MPmap with optional auto-cleanup. *)
let mktable_modpath autoclean =
  let m = ref MPmap.empty in
  let clear () = m := MPmap.empty in
  if autoclean then register_cleanup clear;
  ((fun r v -> m := MPmap.add r v !m), (fun r -> MPmap.find r !m), clear)

(** Table recording first-level content of each MPfile. *)
let add_mpfiles_content, get_mpfiles_content, clear_mpfiles_content =
  mktable_modpath false

(** Retrieve module file content, raising [Failure] if not registered. *)
let get_mpfiles_content mp =
  try get_mpfiles_content mp with Not_found -> failwith "get_mpfiles_content"

(** The list of external modules that will be opened initially *)

let mpfiles_add, mpfiles_mem, mpfiles_list, mpfiles_clear =
  let m = ref MPset.empty in
  let add mp = m := MPset.add mp !m
  and mem mp = MPset.mem mp !m
  and list () = MPset.elements !m
  and clear () = m := MPset.empty in
  register_cleanup clear;
  (add, mem, list, clear)

(** List of module parameters that we should alpha-rename *)

let params_ren_add, params_ren_mem =
  let m = ref MPset.empty in
  let add mp = m := MPset.add mp !m
  and mem mp = MPset.mem mp !m
  and clear () = m := MPset.empty in
  register_cleanup clear;
  (add, mem)

(** Table indicating the visible horizon at a precise moment, i.e. the stack of
    structures we are inside.

    - The sequence of [mp] parts should have the following form: a [MPfile] at
      the beginning, and then more and more [MPdot] over this [MPfile], or
      [MPbound] when inside the type of a module parameter.

    - the [params] are the [MPbound] when [mp] is a functor, the innermost
      [MPbound] coming first in the list.

    - The [content] part is used to record all the names already seen at this
      level. *)

(** A layer of the visibility stack, tracking names visible at one scope level.
*)
type visible_layer = {
  mp : ModPath.t;
  params : ModPath.t list;
  mutable content : Label.t KMap.t;
}

(** Visibility stack for module rendering: tracks which module paths are in
    scope and their label-to-key content mappings. *)
let pop_visible, push_visible, get_visible =
  let vis = ref [] in
  register_cleanup (fun () -> vis := []);
  let pop () =
    match !vis with
    | [] -> CErrors.anomaly (Pp.str "pop_visible: empty visibility stack")
    | v :: vl ->
      vis := vl;
      (* we save the 1st-level-content of MPfile for later use *)
      if get_phase () == Impl && modular () && is_modfile v.mp then
        add_mpfiles_content v.mp v.content
  and push mp mps = vis := {mp; params = mps; content = KMap.empty} :: !vis
  and get () = !vis in
  (pop, push, get)

(** Get module paths of all visible layers. *)
let get_visible_mps () =
  List.map
    (function
      | v -> v.mp )
    (get_visible ())

(** Get the innermost visible layer. *)
let top_visible () =
  match get_visible () with
  | [] -> CErrors.anomaly (Pp.str "top_visible: empty visibility stack")
  | v :: _ -> v

(** Get the module path of the innermost visible layer. *)
let top_visible_mp () = (top_visible ()).mp

(** Register a name in the current visible layer. *)
let add_visible ks l =
  let visible = top_visible () in
  visible.content <- KMap.add ks l visible.content

(** Ordered comparison for (ModPath.t, Label.t) pairs. Table of local module
    wrappers used to provide non-ambiguous names *)

module DupOrd = struct
  type t = ModPath.t * Label.t

  let compare (mp1, l1) (mp2, l2) =
    let c = Label.compare l1 l2 in
    if Int.equal c 0 then ModPath.compare mp1 mp2 else c
end

(** Map keyed by DupOrd. *)
module DupMap = Map.Make (DupOrd)

(** Table of local module wrappers for non-ambiguous names. *)
let add_duplicate, get_duplicate =
  let index = ref 0
  and dups = ref DupMap.empty in
  register_cleanup (fun () ->
    index := 0;
    dups := DupMap.empty );
  let add mp l =
    incr index;
    let ren = "Coq__" ^ string_of_int !index in
    (* let ren = ModPath.to_string mp ^ "__" ^ string_of_int !index in *)
    dups := DupMap.add (mp, l) ren !dups
  and get mp l =
    try Some (DupMap.find (mp, l) !dups) with Not_found -> None
  in
  (add, get)

(** What to reset: all renaming tables, or also external file content. *)
type reset_kind =
  | AllButExternal
  | Everything

(** Reset all renaming tables. *)
let reset_renaming_tables flag =
  do_cleanup ();
  if flag == Everything then clear_mpfiles_content ()

(** {1 Renaming functions} *)

(** This function creates from [id] a correct uppercase/lowercase identifier.
    This is done by adding a [Coq_] or [coq_] prefix. To avoid potential clashes
    with previous [Coq_id] variable, these prefixes are duplicated if already
    existing. *)

(** Returns (escaped_name, was_changed) where was_changed indicates whether
    keyword escaping or prime replacement modified the identifier. *)
let modular_rename_ex _k id =
  let s = ascii_of_id id in
  let is_kw = Id.Set.mem id (get_keywords ()) in
  let s = if is_kw then s ^ "_" else s in
  let has_prime = String.contains s '\'' in
  let s = String.map (fun c -> if c = '\'' then '_' else c) s in
  (s, is_kw || has_prime)

(** Rename an identifier for modular extraction (keyword escaping, prime
    replacement). *)
let modular_rename k id = fst (modular_rename_ex k id)

let detect_sibling_module_inductive_collisions (s : ml_structure) =
  Hashtbl.clear sibling_collision_renames;
  let rec scan_sel parent_mp sel =
    let module_entries =
      List.filter_map
        (fun (l, se) ->
          match se with
          | SEmodule _ ->
            Some (l, modular_rename Mod (Label.to_id l))
          | _ -> None )
        sel
    in
    let inductive_names =
      List.concat_map
        (fun (_l, se) ->
          match se with
          | SEdecl (Dind (_kn, ind)) ->
            Array.to_list
              (Array.map
                 (fun p -> modular_rename Type p.ip_typename)
                 ind.ind_packets)
          | _ -> [] )
        sel
    in
    List.iter
      (fun (l, mod_name) ->
        if List.exists (String.equal mod_name) inductive_names then
          Hashtbl.replace sibling_collision_renames
            (MPdot (parent_mp, l))
            (mod_name ^ "_Mod") )
      module_entries;
    List.iter
      (fun (_l, se) ->
        match se with
        | SEmodule m ->
          ( match m.ml_mod_expr with
          | MEstruct (inner_mp, inner_sel) -> scan_sel inner_mp inner_sel
          | _ -> () )
        | _ -> () )
      sel
  in
  List.iter (fun (mp, sel) -> scan_sel mp sel) s

(** For monolithic extraction, first-level modules might have to be renamed with
    unique numbers *)

(** Rename first-level module labels with unique numeric suffixes. *)
let modfstlev_rename =
  let add_index, get_index, _ = mktable_id true in
  fun l ->
    let id = Label.to_id l in
    try
      let n = get_index id in
      add_index id (n + 1);
      let s = if n == 0 then "" else string_of_int (n - 1) in
      "Coq" ^ s ^ "_" ^ ascii_of_id id
    with Not_found ->
      let s = ascii_of_id id in
      (* if is_lower s || begins_with_CoqXX s then (add_index id 1; "Coq_"^s)
         else *)
      add_index id 0;
      s

(** {2 Creating renaming for a module_path} *)

(** First, the real function ... *)
let rec mp_renaming_fun full_mp =
  match full_mp with
  | _ when (not (modular ())) && at_toplevel full_mp -> [""]
  | MPdot (parent_mp, l) ->
    let lmp = mp_renaming parent_mp in
    let name =
      match Hashtbl.find_opt sibling_collision_renames full_mp with
      | Some renamed -> renamed
      | None ->
        ( match lmp with
        | [""] -> modfstlev_rename l
        | _ -> modular_rename Mod (Label.to_id l) )
    in
    name :: lmp
  | MPbound mbid ->
    let s = modular_rename Mod (MBId.to_id mbid) in
    if not (params_ren_mem full_mp) then
      [s]
    else
      let i, _, _ = MBId.repr mbid in
      [s ^ "__" ^ string_of_int i]
  | MPfile _ ->
    assert (modular ());
    (* see [at_toplevel] above *)
    assert (get_phase () == Pre);
    let current_mpfile = (List.last (get_visible ())).mp in
    if not (ModPath.equal full_mp current_mpfile) then mpfiles_add full_mp;
    [string_of_modfile full_mp]

(** ... and its version using a cache *)

and mp_renaming =
  let add, get, _ = mktable_modpath true in
  fun x ->
    try
      if is_mp_bound (base_mp x) then raise Not_found;
      get x
    with Not_found ->
      let y = mp_renaming_fun x in
      add x y;
      y

(** {2 Renamings creation for a global_reference} *)

(** We build its fully-qualified name in a [string list] form (head is the short
    name). *)
let ref_renaming_fun (k, r) =
  let mp = modpath_of_r r in
  let l = mp_renaming mp in
  let l = if lang () != Cpp && not (modular ()) then [""] else l in
  let s =
    let idg = safe_basename_of_global r in
    match l with
    | [""] ->
      (* this happens only at toplevel of the monolithic case *)
      let globs = get_global_ids () in
      (* For constructors, also reserve the parent inductive type's name (and
         its capitalized form) so that eponymous constructors like Ascii.Ascii
         get renamed to avoid C++ struct name conflicts. *)
      let globs =
        match r with
        | GlobRef.ConstructRef (ind, _) ->
          let parent_idg = safe_basename_of_global (GlobRef.IndRef ind) in
          let parent_s = ascii_of_id parent_idg in
          let globs = Id.Set.add (Id.of_string parent_s) globs in
          let parent_cap = String.capitalize_ascii parent_s in
          if parent_cap <> parent_s then
            Id.Set.add (Id.of_string parent_cap) globs
          else
            globs
        | _ -> globs
      in
      let id = next_ident_away (kindcase_id k idg) globs in
      Id.to_string id
    | _ ->
      let s, changed = modular_rename_ex k idg in
      let is_bound = is_mp_bound (base_mp mp) in
      (* Avoid collisions caused by keyword/prime escaping. For constructors,
         track per inductive type. For other globals, track per module path.
         Only resolve collisions when escaping changed the name; always register
         so later escaped names detect conflicts. Skip MPbound refs (functor
         parameters) since those bypass the ref_renaming cache and would
         accumulate stale entries. *)
      ( match r with
      | GlobRef.ConstructRef (ind, _) when not is_bound ->
        let siblings = get_ctor_siblings ind in
        (* In C++, a nested struct cannot share its name with the enclosing
           struct. Reserve the parent inductive type's C++ name so that any
           constructor with the same name is automatically renamed. We reserve
           both the raw name and the capitalized form, because an eponymous
           Dnspace merge may capitalize the enclosing struct name (e.g. module
           Ascii + type ascii -> struct Ascii). *)
        let parent_idg = safe_basename_of_global (GlobRef.IndRef ind) in
        let parent_s, _ = modular_rename_ex k parent_idg in
        let siblings = Id.Set.add (Id.of_string parent_s) siblings in
        let parent_cap = String.capitalize_ascii parent_s in
        let siblings =
          if parent_cap <> parent_s then
            Id.Set.add (Id.of_string parent_cap) siblings
          else
            siblings
        in
        let id = next_ident_away (Id.of_string s) siblings in
        let s = Id.to_string id in
        add_ctor_sibling ind (Id.of_string s);
        s
      | _ when not is_bound ->
        let siblings = get_mp_siblings mp in
        let id = next_ident_away (Id.of_string s) siblings in
        let s = Id.to_string id in
        add_mp_sibling mp (Id.of_string s);
        s
      | _ -> s )
  in
  add_global_ids (Id.of_string s);
  s :: l

(** Cached version of ref_renaming_fun. *)
let ref_renaming =
  let add, get, _ = mktable_ref true in
  fun ((k, r) as x) ->
    try
      if is_mp_bound (base_mp (modpath_of_r r)) then raise Not_found;
      get r
    with Not_found ->
      let y = ref_renaming_fun x in
      add r y;
      y

(** {2 On-the-fly qualification} *)

(** [visible_clash mp0 (k,s)] checks if [mp0-s] of kind [k] can be printed as
    [s] in the current context of visible modules. More precisely, we check if
    there exists a visible [mp] that contains [s]. The verification stops if we
    encounter [mp=mp0]. *)

let rec clash mem mp0 ks = function
  | [] -> false
  | mp :: _ when ModPath.equal mp mp0 -> false
  | mp :: _ when mem mp ks -> true
  | _ :: mpl -> clash mem mp0 ks mpl

(** Check if a name clashes with content from opened files. *)
let mpfiles_clash mp0 ks =
  clash
    (fun mp k -> KMap.mem k (get_mpfiles_content mp))
    mp0
    ks
    (List.rev (mpfiles_list ()))

(** Check if a module path matches a functor parameter. *)
let rec params_lookup mp0 ks = function
  | [] -> false
  | param :: _ when ModPath.equal mp0 param -> true
  | param :: params ->
    let () =
      match ks with
      | Mod, mp when String.equal (List.hd (mp_renaming param)) mp ->
        params_ren_add param
      | _ -> ()
    in
    params_lookup mp0 ks params

(** Check if a name clashes with a visible module's content. *)
let visible_clash mp0 ks =
  let rec clash = function
    | [] -> false
    | v :: _ when ModPath.equal v.mp mp0 -> false
    | v :: vis ->
      let b = KMap.mem ks v.content in
      if b && not (is_mp_bound mp0) then
        true
      else (
        if b then params_ren_add mp0;
        if params_lookup mp0 ks v.params then
          false
        else
          clash vis )
  in
  clash (get_visible ())

(** Like visible_clash but returns the conflicting module path (and mp0
    shouldn't be a MPbound). *)
let visible_clash_dbg mp0 ks =
  let rec clash = function
    | [] -> None
    | v :: _ when ModPath.equal v.mp mp0 -> None
    | v :: vis ->
    try Some (v.mp, KMap.find ks v.content)
    with Not_found ->
      if params_lookup mp0 ks v.params then
        None
      else
        clash vis
  in
  clash (get_visible ())

(** Compute which libraries should be opened initially. After the 1st pass, we
    can decide which modules will be opened initially *)
let opened_libraries () =
  if not (modular ()) then
    []
  else
    let used_files = mpfiles_list () in
    let used_ks = List.map (fun mp -> (Mod, string_of_modfile mp)) used_files in
    (* By default, we open all used files. Ambiguities will be resolved later by
       using qualified names. Nonetheless, we don't open any file A that
       contains an immediate submodule A.B hiding another file B : otherwise,
       after such an open, there's no unambiguous way to refer to objects of
       B. *)
    let to_open =
      List.filter
        (fun mp ->
          not
            (List.exists (fun k -> KMap.mem k (get_mpfiles_content mp)) used_ks) )
        used_files
    in
    mpfiles_clear ();
    List.iter mpfiles_add to_open;
    mpfiles_list ()

(** On-the-fly qualification issues for both monolithic or modular extraction.

    [pp_ocaml_gen] below is a function that factorize the printing of both
    [global_reference] and module names for ocaml. When [k=Mod] then
    [olab=None], otherwise it contains the label of the reference to print.
    [rls] is the string list giving the qualified name, short name at the end.

    In Rocq, we can qualify [M.t] even if we are inside [M], but in Ocaml we
    cannot do that. So, if [t] gets hidden and we need a long name for it, we
    duplicate the _definition_ of t in a Coq__XXX module, and similarly for a
    sub-module [M.N] *)

(** Print a reference using a duplicate wrapper module. *)
let pp_duplicate k' prefix mp rls olab =
  let rls', lbl =
    if k' != Mod then
      (* Here rls=[s], the ref to print is <prefix>.<s>, and olab<>None *)
      (rls, Option.get olab)
    else (* Here rls=s::rls', we search the label for s inside mp *)
      (List.tl rls, get_nth_label_mp (mp_length mp - mp_length prefix) mp)
  in
  match get_duplicate prefix lbl with
  | Some ren -> dottify (ren :: rls')
  | None ->
    assert (get_phase () == Pre);
    (* otherwise it's too late *)
    add_duplicate prefix lbl;
    dottify rls

(** Extract the kind and name for first-level clash detection. *)
let fstlev_ks k = function
  | [] -> CErrors.anomaly (Pp.str "fstlev_ks: empty renaming list")
  | [s] -> (k, s)
  | s :: _ -> (Mod, s)

(** Print a locally-visible reference. [pp_ocaml_local] : [mp] has something in
    common with [top_visible ()] but isn't equal to it *)
let pp_ocaml_local k prefix mp rls olab =
  (* what is the largest prefix of [mp] that belongs to [visible]? *)
  assert (k != Mod || not (ModPath.equal mp prefix));
  (* mp as whole module isn't in itself *)
  let rls' = List.skipn (mp_length prefix) rls in
  let k's = fstlev_ks k rls' in
  (* Reference r / module path mp is of the form [<prefix>.s.<...>]. *)
  if not (visible_clash prefix k's) then
    dottify rls'
  else
    pp_duplicate (fst k's) prefix mp rls' olab

(** Print a reference from a bound module parameter. [pp_ocaml_bound] : [mp]
    starts with a [MPbound], and we are not inside (i.e. we are not printing the
    type of the module parameter) *)
let pp_ocaml_bound base rls =
  (* clash with a MPbound will be detected and fixed by renaming this MPbound *)
  if get_phase () == Pre then ignore (visible_clash base (Mod, List.hd rls));
  dottify rls

(** Print an externally-defined reference. [pp_ocaml_extern] : [mp] isn't local,
    it is defined in another [MPfile]. *)
let pp_ocaml_extern k base rls =
  match rls with
  | [] -> CErrors.anomaly (Pp.str "pp_ocaml_extern: empty renaming list")
  | base_s :: rls' ->
    if
      (not (modular ())) (* Pseudo qualification with "" *)
      || List.is_empty rls' (* Case of a file A.v used as a module later *)
      || (not (mpfiles_mem base)) (* Module not opened *)
      || mpfiles_clash base (fstlev_ks k rls') (* Conflict in opened files *)
      || visible_clash base (fstlev_ks k rls')
      (* Local conflict *)
    then
      (* We need to fully qualify. Last clash situation is unsupported *)
        match
          visible_clash_dbg base (Mod, base_s)
        with
      | None -> dottify rls
      | Some (mp, l) -> error_module_clash base (MPdot (mp, l))
    else (* Standard situation : object in an opened file *)
      dottify rls'

(** Main name printer: dispatch between local, bound, and external.
    [pp_ocaml_gen] : choosing between [pp_ocaml_local] or [pp_ocaml_extern] *)
let pp_ocaml_gen k mp rls olab =
  match common_prefix_from_list mp (get_visible_mps ()) with
  | Some prefix -> pp_ocaml_local k prefix mp rls olab
  | None ->
    let base = base_mp mp in
    if is_mp_bound base then
      pp_ocaml_bound base rls
    else
      pp_ocaml_extern k base rls

(** C++ variant of pp_ocaml_gen. *)
let pp_cpp_gen k mp rls olab =
  match common_prefix_from_list mp (get_visible_mps ()) with
  | Some prefix -> pp_ocaml_local k prefix mp rls olab
  | None ->
    let base = base_mp mp in
    if is_mp_bound base then
      pp_ocaml_bound base rls
    else
      pp_ocaml_extern k base rls

(** Main name printing function for a reference, using a kernel name key. *)
let pp_global_with_key k key r =
  let ls = ref_renaming (k, r) in
  assert (List.length ls > 1);
  let s = List.hd ls in
  let mp, l = KerName.repr key in
  if ModPath.equal mp (top_visible_mp ()) then (
    (* simplest situation: definition of r (or use in the same context) *)
    (* we update the visible environment *)
    add_visible (k, s) l;
    unquote s )
  else
    let rls = List.rev ls in
    (* for what come next it's easier this way *)
    match lang () with
    | Cpp -> pp_cpp_gen k mp rls (Some l)

(** Print a reference using its canonical kernel name. *)
let pp_global k r = pp_global_with_key k (repr_of_r r) r

(** Print just the short name of a reference (for declarations). Main name
    printing function for declaring a reference *)
let pp_global_name k r =
  let ls = ref_renaming (k, r) in
  assert (List.length ls > 1);
  List.hd ls

(** Print the type name for an eponymous record reference.  Returns the
    enclosing module name (from [mp_renaming]) so that type references match
    the struct definition name and qualified field accesses.  Eponymous
    detection is case-insensitive, so the record and module names may differ
    in casing (e.g. [Module Shadow] with [Record shadow]).  The struct
    definition uses the module name, so type references must too. *)
let pp_type_name_capitalized r =
  let mp = modpath_of_r r in
  List.hd (mp_renaming mp)

(** Print a module path. The next function is used only in Ocaml extraction...
*)
let pp_module mp =
  let ls = mp_renaming mp in
  match mp with
  | MPdot (mp0, l) when ModPath.equal mp0 (top_visible_mp ()) ->
    (* simplest situation: definition of mp (or use in the same context) *)
    (* we update the visible environment *)
    let s = List.hd ls in
    add_visible (Mod, s) l;
    s
  | _ -> pp_ocaml_gen Mod mp (List.rev ls) None

(** Special hack for constants of type Ascii.ascii : if an
    [Extract Inductive ascii => char] has been declared, then the constants are
    directly turned into chars *)

let ascii_type_name = "core.ascii.type"

(** Rocq library reference for the [ascii] constructor. *)
let ascii_constructor_name = "core.ascii.ascii"

(** Check if both ascii type and constructor are registered in the library. *)
let is_ascii_registered () =
  Rocqlib.has_ref ascii_type_name && Rocqlib.has_ref ascii_constructor_name

(** Get the [GlobRef] for the ascii type. *)
let ascii_type_ref () = Rocqlib.lib_ref ascii_type_name

(** Check if ascii has been extracted to the language's native char type. *)
let check_extract_ascii () =
  try
    let char_type =
      match lang () with
      | Cpp -> "char"
    in
    String.equal (find_custom @@ ascii_type_ref ()) char_type
  with Not_found -> false

(** Check if a list of ML AST nodes consists entirely of nullary constructors
    (used for char list → string optimization). *)
let is_list_cons l =
  List.for_all
    (function
      | MLcons (_, GlobRef.ConstructRef (_, _), []) -> true
      | _ -> false )
    l

let is_native_char = function
  | MLcons (_, gr, l) ->
    is_ascii_registered ()
    && Rocqlib.check_ref ascii_constructor_name gr
    && check_extract_ascii ()
    && is_list_cons l
  | _ -> false

(** Decode an [ascii] constructor application into a native [char] value. *)
let get_native_char c =
  let rec cumul = function
    | [] -> 0
    | MLcons (_, GlobRef.ConstructRef (_, j), []) :: l -> 2 - j + (2 * cumul l)
    | _ ->
      CErrors.anomaly
        (Pp.str "get_native_char: malformed ascii constructor list")
  in
  let l =
    match c with
    | MLcons (_, _, l) -> l
    | _ -> CErrors.anomaly (Pp.str "get_native_char: expected MLcons")
  in
  Char.chr (cumul l)

(** Pretty-print an ascii constructor as a C++ char literal. *)
let pp_native_char c = str ("'" ^ Char.escaped (get_native_char c) ^ "'")

(** Special hack for constants of type String.string : if an
    [Extract Inductive string => string] has been declared, then the constants
    are directly turned into string literals *)

let string_type_name = "core.string.type"

(** Rocq library reference for the empty string constructor. *)
let empty_string_name = "core.string.empty"

(** Rocq library reference for the string constructor. *)
let string_constructor_name = "core.string.string"

(** Check if all string-related types are registered in the library. *)
let is_string_registered () =
  Rocqlib.has_ref string_type_name
  && Rocqlib.has_ref empty_string_name
  && Rocqlib.has_ref string_constructor_name

(** Get the [GlobRef] for the string type. *)
let string_type_ref () = Rocqlib.lib_ref string_type_name

(** Check if string has been extracted to the language's native string type. *)
let check_extract_string () =
  try
    let string_type =
      match lang () with
      | Cpp -> "string"
    in
    String.equal (find_custom @@ string_type_ref ()) string_type
  with Not_found -> false

(** The argument is known to be of type Strings.String.string. Check that it is
    built from constructors EmptyString and String with constant ascii
    arguments. *)
let rec is_native_string_rec empty_string_ref string_constructor_ref = function
  (* "EmptyString" constructor *)
  | MLcons (_, gr, []) -> Rocqlib.check_ref empty_string_ref gr
  (* "String" constructor *)
  | MLcons (_, gr, [hd; tl]) ->
    Rocqlib.check_ref string_constructor_ref gr
    && is_native_char hd
    && is_native_string_rec empty_string_ref string_constructor_ref tl
  (* others *)
  | _ -> false

(** Here we first check that the argument is the type registered as
    core.string.type and that extraction to native strings was requested. Then
    we check every character via [is_native_string_rec]. *)
let is_native_string c =
  match c with
  | MLcons (_, GlobRef.ConstructRef (ind, j), l) ->
    is_string_registered ()
    && Rocqlib.check_ref string_type_name (GlobRef.IndRef ind)
    && check_extract_string ()
    && is_native_string_rec empty_string_name string_constructor_name c
  | _ -> false

(** Extract the underlying string. *)
let get_native_string c =
  let buf = Buffer.create 64 in
  let rec get = function
    (* "EmptyString" constructor *)
    | MLcons (_, gr, []) when Rocqlib.check_ref empty_string_name gr ->
      Buffer.contents buf
    (* "String" constructor *)
    | MLcons (_, gr, [hd; tl]) when Rocqlib.check_ref string_constructor_name gr
      ->
      Buffer.add_char buf (get_native_char hd);
      get tl
    (* others *)
    | _ ->
      CErrors.anomaly (Pp.str "get_native_string: malformed string constructor")
  in
  get c

(** Printing the underlying string. *)
let pp_native_string c = str ("\"" ^ String.escaped (get_native_string c) ^ "\"")

(** Registered sig type *)
let sig_type_name = "core.sig.type"

(** {2 Synthetic name generators} *)

(** Synthetic name generators. Centralized here so that naming conventions are
    defined in one place. *)

let tvar_name i = "T" ^ string_of_int i

let tvar_id i = Id.of_string (tvar_name i)

let anon_tvar_name i = "_tvar" ^ string_of_int i

let anon_tvar_id i = Id.of_string (anon_tvar_name i)

let fun_tparam_name i = "F" ^ string_of_int i

let fun_tparam_id i = Id.of_string (fun_tparam_name i)

let field_param_name i = "d_a" ^ string_of_int i

let field_param_id i = Id.of_string (field_param_name i)

(** {2 Constructor Field Name Registry}

    Maps [(ctor_struct_name, field_idx)] pairs to the C++ field identifier
    derived from the Rocq binder name.  Populated by
    {!Translation.compute_and_register_field_names} at definition sites
    (struct field declarations, factory methods) and queried at access sites
    (pattern-match lambdas, record reuse, loopification cell patching).

    The registry lives in {!Common} rather than {!Cpp_state} to avoid a
    dependency cycle: [Translation] depends on [Common] but not on
    [Cpp_state], while [Cpp_state] transitively depends on [Translation]
    through [Method_registry].  Cleared by {!reset_ctor_field_names}
    between extraction passes (called from {!Cpp_state.reset_cpp_state}). *)

let ctor_field_names : (string * int, Id.t) Hashtbl.t = Hashtbl.create 64

(** [register_ctor_field_name ctor_name field_idx field_id] records that
    field [field_idx] of the C++ constructor struct [ctor_name] should be
    named [field_id].

    @param ctor_name  PascalCase name of the constructor struct (e.g. ["Cons"])
    @param field_idx  0-based field position
    @param field_id   The identifier to use (e.g. [d_hd], or [d_a0] as fallback) *)
let register_ctor_field_name ctor_name field_idx field_id =
  Hashtbl.replace ctor_field_names (ctor_name, field_idx) field_id

(** [lookup_ctor_field_name ctor_name field_idx] retrieves the registered
    field name, falling back to the generic positional name
    [d_a{field_idx}] when no name was registered (e.g. for custom-extracted
    inductives or when the registry hasn't been populated yet). *)
let lookup_ctor_field_name ctor_name field_idx =
  match Hashtbl.find_opt ctor_field_names (ctor_name, field_idx) with
  | Some id -> id
  | None -> field_param_id field_idx

(** Clear the field name registry.  Must be called between extraction
    passes to avoid stale names from one module leaking into another. *)
let reset_ctor_field_names () = Hashtbl.clear ctor_field_names

(** {3 More synthetic name generators} *)

let eta_param_name i = "_x" ^ string_of_int i

let eta_param_id i = Id.of_string (eta_param_name i)

let tc_instance_name i = "_tcI" ^ string_of_int i

let tc_instance_id i = Id.of_string (tc_instance_name i)

let ctor_fallback_name i = "Ctor" ^ string_of_int i

let ctor_fallback_id i = Id.of_string (ctor_fallback_name i)

let db_fallback_name i = "_db" ^ string_of_int i

let db_fallback_id i = Id.of_string (db_fallback_name i)

let tparam_name id = Id.of_string ("t_" ^ Id.to_string id)

let enum_ctor_name s = "e_" ^ String.uppercase_ascii s

(** Capitalize only the last [::]-separated component of a qualified name. *)
let capitalize_last_component s =
  match String.rindex_opt s ':' with
  | Some i when i > 0 && i < String.length s - 1 && s.[i - 1] = ':' ->
    let prefix = String.sub s 0 (i + 1) in
    let suffix = String.sub s (i + 1) (String.length s - i - 1) in
    prefix ^ String.capitalize_ascii suffix
  | _ -> String.capitalize_ascii s
