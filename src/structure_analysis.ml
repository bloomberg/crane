(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Structure analysis: pre-analyzes the full extraction structure before
   rendering begins.  Computes module ordering, enum registrations,
   inductive name maps, and wrapper module classifications.

   This is the second pass in the extraction pipeline, running after
   Method_registry.create and before cpp.ml's rendering.  It produces
   a Structure_analysis.t record that cpp.ml consumes to iterate modules
   in the correct dependency order.

   See structure_analysis.mli for the full interface documentation. *)

open Util
open Names
open Table
open Miniml
open Common
open Modutil

type module_info = {
  modpath : ModPath.t;
  sels : (Label.t * ml_structure_elem) list;
  wrapper_name : string option;
  is_main : bool;
}

type t = {
  sorted_modules : module_info list;
  inductive_names : (string * ModPath.t) list;
  global_scope_enums : GlobRef.t list;
}

(* ------------------------------------------------------------------ *)
(* Enum registration                                                   *)
(* ------------------------------------------------------------------ *)

(* Register enum inductives by scanning a module's declaration list.

   An inductive qualifies as an enum when ALL of the following hold:
   - It is not a custom-extracted type ([is_custom] returns false).
   - It is not part of a mutual inductive block (only single inductives).
   - All constructors are nullary (no arguments — [ip_types] are all [[]]).
   - It has no kept type parameters ([num_param_vars = 0]).
   - It has at least one constructor ([Array.length p.ip_types > 0]).

   Records and type classes are excluded upfront since they have different
   representations.

   Detected enums are registered via [Table.add_enum_inductive], which
   sets a global flag queryable by [Table.is_enum_inductive].

   Recurses into sub-modules ([SEmodule] with [MEstruct]) to find enums
   at any nesting depth. *)
let rec register_enum_inductives (sel : (Label.t * ml_structure_elem) list) : unit =
  List.iter (fun (_l, se) ->
    match se with
    | SEdecl (Dind (kn, ind)) ->
      (match ind.ind_kind with
       | Record _ | TypeClass _ -> ()
       | _ ->
         let is_mutual = Array.length ind.ind_packets > 1 in
         Array.iteri (fun i p ->
           let ind_ref = GlobRef.IndRef (kn, i) in
           if not (is_custom ind_ref) && not is_mutual then begin
             let all_nullary = Array.for_all (fun tys_list -> tys_list = []) p.ip_types in
             let param_sign = List.firstn ind.ind_nparams p.ip_sign in
             let num_param_vars = List.length (List.filter (fun x -> x == Miniml.Keep) param_sign) in
             if all_nullary && num_param_vars = 0 && Array.length p.ip_types > 0 then
               Table.add_enum_inductive ind_ref
           end
         ) ind.ind_packets)
    | SEmodule m ->
      (match m.ml_mod_expr with
       | MEstruct (_mp, inner_sel) ->
         register_enum_inductives inner_sel
       | _ -> ())
    | _ -> ()
  ) sel

(* ------------------------------------------------------------------ *)
(* Inductive name collection                                           *)
(* ------------------------------------------------------------------ *)

(* Collect (capitalized_name, defining_modpath) for every inductive type
   in the structure.

   This information is used by cpp.ml for name collision detection.
   When multiple modules define inductives with the same capitalized name,
   or when a wrapper module name collides with an inductive name from
   a different module, the rendering needs to disambiguate (e.g. by
   using a qualified name or a different wrapper name).

   Recurses into sub-modules to collect inductives at all nesting depths. *)
let collect_inductive_names (s : ml_structure) : (string * ModPath.t) list =
  let acc = ref [] in
  let rec collect sel =
    List.iter (fun (_l, se) ->
      match se with
      | SEdecl (Dind (kn, ind)) ->
        let ind_mp = Names.MutInd.modpath kn in
        Array.iteri (fun i _p ->
          let ind_ref = GlobRef.IndRef (kn, i) in
          let ind_name = Common.pp_global_name Type ind_ref in
          let ind_name_cap = String.capitalize_ascii ind_name in
          acc := (ind_name_cap, ind_mp) :: !acc
        ) ind.ind_packets
      | SEmodule m ->
        (match m.ml_mod_expr with
         | MEstruct (_mp, inner_sel) -> collect inner_sel
         | _ -> ())
      | _ -> ()
    ) sel
  in
  List.iter (fun (_mp, sel) -> collect sel) s;
  !acc

(* ------------------------------------------------------------------ *)
(* Global scope enum collection                                        *)
(* ------------------------------------------------------------------ *)

(* Collect enum inductives that appear at global scope (top-level SEdecl
   entries, not nested inside sub-modules).

   This must run AFTER [register_enum_inductives] has been called,
   because it relies on [Table.is_enum_inductive] to identify enums.

   Global-scope enums are emitted as [enum class] declarations before
   any wrapper modules or the main module, ensuring they are in scope
   for all subsequent C++ declarations that reference them.

   Note: only the top-level declarations are scanned (no recursion into
   sub-modules).  Enums inside sub-modules are emitted within their
   containing module's scope by the module rendering code in cpp.ml. *)
let collect_global_scope_enums (s : ml_structure) : GlobRef.t list =
  let acc = ref [] in
  List.iter (fun (_mp, sel) ->
    List.iter (fun (_l, se) ->
      match se with
      | SEdecl (Dind (kn, ind)) ->
        Array.iteri (fun i _p ->
          let ind_ref = GlobRef.IndRef (kn, i) in
          if Table.is_enum_inductive ind_ref then
            acc := ind_ref :: !acc
        ) ind.ind_packets
      | _ -> ()
    ) sel
  ) s;
  !acc

(* ------------------------------------------------------------------ *)
(* Module classification                                               *)
(* ------------------------------------------------------------------ *)

(* Test whether a structure element is a function declaration (Dterm or
   Dfix).  Used by [classify_module] to determine if a module contains
   any functions — a prerequisite for wrapping. *)
let is_func_decl (_, se) = match se with
  | SEdecl (Dterm _ | Dfix _) -> true
  | _ -> false

(* Classify a module as a wrapper or non-wrapper.

   A module becomes a wrapper (its declarations are emitted inside a
   C++ struct) when ALL of these hold:
   - [has_bare]:    It contains at least one bare [SEdecl] entry.
   - [all_bare]:    It contains ONLY bare declarations (no [SEmodule]
                    or [SEmodtype] children).
   - [is_modfile]:  It is a file-level module (not a sub-module).
   - [has_func]:    It contains at least one function ([Dterm] or [Dfix]).
   - [not is_main]: It is not the main module being extracted.

   When a module qualifies, returns [Some name] where [name] is the
   capitalized form of the module file name (e.g. "List" for list.v).
   Otherwise returns [None].

   The main module is excluded because its declarations are emitted
   directly at top level, not inside a wrapper struct. *)
let classify_module ~main_mp (mp, sel) =
  let has_func = List.exists is_func_decl sel in
  let has_bare = List.exists (fun (_, se) -> match se with SEdecl _ -> true | _ -> false) sel in
  let all_bare = not (List.exists (fun (_, se) -> match se with SEmodule _ | SEmodtype _ -> true | _ -> false) sel) in
  let is_main = match main_mp with Some m -> ModPath.equal mp m | None -> false in
  if has_bare && all_bare && is_modfile mp && has_func && not is_main then
    Some (String.capitalize_ascii (string_of_modfile mp))
  else
    None

(* ------------------------------------------------------------------ *)
(* Topological sort                                                    *)
(* ------------------------------------------------------------------ *)

(* Topologically sort non-main modules by cross-module dependencies.

   This ensures that when module A references a type or function from
   module B, module B appears before module A in the output.  This is
   important for C++ compilation: forward declarations are limited, so
   definitions must generally precede their uses.

   The algorithm is Kahn's algorithm (BFS-based topological sort):
   1. Build a dependency graph: for each non-main module, scan all
      declarations for GlobRef references to other modules.
   2. Additionally, check the method registry: if a function calls a
      method on a type from another module, that creates an implicit
      dependency (the method is defined inside the other module's struct).
   3. Compute in-degrees and process nodes with in-degree 0 first.
   4. If a cycle is detected (not all nodes processed), fall back to
      the original order rather than failing.

   The main module (last in the input list) is always placed last in
   the output, regardless of dependencies.  This is because the main
   module is the "entry point" and may depend on everything.

   Trivial case: if there are 0 or 1 modules, or no dependencies exist,
   the input order is returned unchanged. *)
let topological_sort (reg : Method_registry.t) (entries : ((ModPath.t * ml_module_structure) * string option) list) :
    ((ModPath.t * ml_module_structure) * string option) list =
  let n = List.length entries in
  if n <= 1 then entries
  else
  (* By convention, the main module is the last entry. *)
  let is_main_entry i = (i = n - 1) in
  (* Step 1: Map from ModPath to array index for non-main modules. *)
  let mp_to_idx : (ModPath.t, int) Hashtbl.t = Hashtbl.create 16 in
  List.iteri (fun i ((mp, _sel), _wn) ->
    if not (is_main_entry i) then
      Hashtbl.replace mp_to_idx mp i
  ) entries;
  (* Step 2: Build dependency graph.
     deps maps module index -> list of module indices it depends on. *)
  let deps : (int, int list) Hashtbl.t = Hashtbl.create 16 in
  List.iteri (fun i ((_mp, sel), _wn) ->
    if is_main_entry i then ()
    else begin
      (* Collect unique dependencies for this module. *)
      let dep_set : (int, unit) Hashtbl.t = Hashtbl.create 8 in
      let add_dep r =
        (* Direct reference: check if [r] is defined in another module. *)
        let rmp = modpath_of_r r in
        (match Hashtbl.find_opt mp_to_idx rmp with
         | Some j when j <> i -> Hashtbl.replace dep_set j ()
         | _ -> ());
        (* Method reference: if [r] is a registered method, its eponymous
           type lives in another module — add that as a dependency too. *)
        match Method_registry.is_registered_method reg r with
        | Some (epon_ref, _pos) ->
          let epon_mp = modpath_of_r epon_ref in
          (match Hashtbl.find_opt mp_to_idx epon_mp with
           | Some j when j <> i -> Hashtbl.replace dep_set j ()
           | _ -> ())
        | None -> ()
      in
      (* Scan all declarations in this module for references. *)
      List.iter (fun (_l, se) ->
        match se with
        | SEdecl d -> Modutil.decl_iter_references add_dep add_dep add_dep d
        | _ -> ()
      ) sel;
      let dep_list = Hashtbl.fold (fun k () acc -> k :: acc) dep_set [] in
      if dep_list <> [] then
        Hashtbl.replace deps i dep_list
    end
  ) entries;
  (* Step 3: Kahn's algorithm. *)
  if Hashtbl.length deps = 0 then
    entries  (* No dependencies — original order is fine. *)
  else begin
    let non_main_indices = List.init (n - 1) (fun i -> i) in
    (* Compute in-degree for each non-main module. *)
    let in_degree : (int, int) Hashtbl.t = Hashtbl.create 16 in
    List.iter (fun i -> Hashtbl.replace in_degree i 0) non_main_indices;
    (* Build reverse dependency index: dep -> list of modules that depend on it.
       This avoids O(n²) scanning in the main loop below. *)
    let reverse_deps : (int, int list) Hashtbl.t = Hashtbl.create 16 in
    Hashtbl.iter (fun idx dep_list ->
      let valid_deps = List.filter (fun dep -> Hashtbl.mem in_degree dep) dep_list in
      let count = List.length valid_deps in
      if count > 0 then begin
        Hashtbl.replace in_degree idx ((try Hashtbl.find in_degree idx with Not_found -> 0) + count);
        List.iter (fun dep ->
          let existing = match Hashtbl.find_opt reverse_deps dep with
            | Some l -> l | None -> []
          in
          Hashtbl.replace reverse_deps dep (idx :: existing)
        ) valid_deps
      end
    ) deps;
    (* Seed the queue with modules that have no incoming dependencies. *)
    let queue = Queue.create () in
    List.iter (fun i ->
      if Hashtbl.find in_degree i = 0 then Queue.push i queue
    ) non_main_indices;
    (* Process the queue: emit each module, then decrement in-degree
       for all modules that depend on it. *)
    let sorted = ref [] in
    while not (Queue.is_empty queue) do
      let idx = Queue.pop queue in
      sorted := idx :: !sorted;
      (match Hashtbl.find_opt reverse_deps idx with
       | Some dependents ->
         List.iter (fun dependent ->
           let new_deg = Hashtbl.find in_degree dependent - 1 in
           Hashtbl.replace in_degree dependent new_deg;
           if new_deg = 0 then Queue.push dependent queue
         ) dependents
       | None -> ())
    done;
    let sorted_indices = List.rev !sorted in
    if List.length sorted_indices <> List.length non_main_indices then
      entries  (* Cycle detected: fall back to original order. *)
    else
      let arr = Array.of_list entries in
      let sorted_entries = List.map (fun i -> arr.(i)) sorted_indices in
      (* Append the main module at the end. *)
      sorted_entries @ [arr.(n - 1)]
  end

(* ------------------------------------------------------------------ *)
(* Main analysis entry point                                           *)
(* ------------------------------------------------------------------ *)

(* Perform all structure analysis in a single call.

   This is called once from cpp.ml's [do_struct_with_decl_tracking],
   immediately after creating the Method_registry.  The steps are:

   1. Register enum inductives across all modules (side-effect on Table).
   2. Collect inductive names for collision detection.
   3. Collect global-scope enums for early emission.
   4. Classify modules as wrapper vs. non-wrapper.
   5. Topologically sort modules by cross-module dependencies.

   The main module is identified as the last module in the input
   structure (following Rocq's convention that the extracted module
   is listed last). *)
let analyze (reg : Method_registry.t) (s : ml_structure) : t =
  (* 1. Register enum inductives (side-effect: populates Table). *)
  List.iter (fun (_mp, sel) -> register_enum_inductives sel) s;
  (* 2. Collect inductive names for name collision detection. *)
  let inductive_names = collect_inductive_names s in
  (* 3. Collect global-scope enums (must run after enum registration). *)
  let global_scope_enums = collect_global_scope_enums s in
  (* 4. Classify each module and topologically sort.
     The main module is the last in the structure by convention. *)
  let main_mp = match List.rev s with
    | (mp, _) :: _ -> Some mp
    | [] -> None
  in
  let entries = List.map (fun (mp, sel) ->
    ((mp, sel), classify_module ~main_mp (mp, sel))
  ) s in
  let sorted = topological_sort reg entries in
  let sorted_modules = List.map (fun ((mp, sels), wrapper_name) ->
    let is_main = match main_mp with Some m -> ModPath.equal mp m | None -> false in
    { modpath = mp; sels; wrapper_name; is_main }
  ) sorted in
  { sorted_modules; inductive_names; global_scope_enums }
