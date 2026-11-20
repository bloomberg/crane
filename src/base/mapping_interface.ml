(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** See [mapping_interface.mli]. *)

open Names

type entry = {
  head : GlobRef.t;
  operation : bool;  (** an operation mapping, else a type mapping *)
  instance : GlobRef.t;
  abi : string;  (** a digest of the compiled plan, references by kernel name *)
  spelled : string;  (** the canonical type, or the operation's template *)
}

(* A reference by kernel name: the same in every file, unlike the shortest
   name the printer finds. *)
let ref_string = function
  | GlobRef.VarRef id -> Id.to_string id
  | GlobRef.ConstRef c -> Constant.to_string c
  | GlobRef.IndRef (m, i) -> Printf.sprintf "%s#%d" (MutInd.to_string m) i
  | GlobRef.ConstructRef ((m, i), j) -> Printf.sprintf "%s#%d#%d" (MutInd.to_string m) i j

(* Plain data only (strings, ints, variants of them), so that equal plans
   marshal to equal bytes. *)
let digest v = Digest.to_hex (Digest.string (Marshal.to_string v [Marshal.No_sharing]))

let declaration (d : Mapping_descriptor.declaration) = ref_string d.reference

let type_abi (p : Mapping_plan.t) =
  let lifetime : string list =
    match p.lifetime with
    | Native_raii -> ["native"]
    | Region_owned d -> ["region"; declaration d]
    | Externally_owned -> ["external"]
    | Manual_shared (retain, release) -> ["manual"; declaration retain; declaration release]
  in
  let interface =
    match p.interface with
    | Abstract -> None
    | Algebraic ctors ->
      Some (List.map (fun (c : Mapping_plan.constructor) -> (snd c.source, c.build, c.view)) ctors)
  in
  digest
    ( Mapping_plan.type_text p,
      p.canonical,
      p.components,
      (p.copy, p.access, p.value_model),
      lifetime,
      p.release,
      interface,
      p.views,
      p.headers )

let operation_abi (p : Mapping_operation.t) =
  let view (v : Mapping_operation.view_conversions) =
    (v.kind, ref_string v.mapped, v.from_canonical, v.read_from_write, v.materialise)
  in
  digest
    ( p.template,
      List.map
        (fun (a : Mapping_operation.argument) ->
          (a.name, a.use, a.position, a.binder, a.in_place, Option.map view a.view))
        p.arguments,
      (p.binder_count, p.call_binders),
      p.result,
      Option.map view p.result_view,
      p.facts,
      p.purity,
      p.headers )

let type_entry (p : Mapping_plan.t) =
  {head = p.head; operation = false; instance = p.instance; abi = type_abi p; spelled = Mapping_plan.type_text p}

let operation_entry (p : Mapping_operation.t) =
  {head = p.source; operation = true; instance = p.instance; abi = operation_abi p; spelled = p.template}

(* The interfaces of the units extracted so far, by unit; persisted in the
   [.vo] of the file that extracted each, so that [Require]-ing it carries
   them, as {!Table.claim_extracted_unit} carries the claims. *)
let interfaces : entry list CString.Map.t ref = Summary.ref CString.Map.empty ~name:"CraneUnitInterfaces"

let interface_object : string * entry list -> Libobject.obj =
  Libobject.declare_object
  @@ Libobject.superglobal_object_nodischarge "Crane Unit Interfaces"
       ~cache:(fun (target, entries) ->
         if not (CString.Map.mem target !interfaces) then interfaces := CString.Map.add target entries !interfaces)
       ~subst:
         (Some
            (fun (s, (target, entries)) ->
              ( target,
                List.map
                  (fun e ->
                    {e with head = fst (Globnames.subst_global s e.head); instance = fst (Globnames.subst_global s e.instance)})
                  entries )))

let record target =
  if not (CString.Map.mem target !interfaces) then
    let entries = List.map type_entry (Mapping_plan.compiled ()) @ List.map operation_entry (Mapping_operation.compiled ()) in
    Lib.add_leaf (interface_object (target, entries))

(* This extraction's entry for the head of [e], if it maps the head. *)
let current e =
  if e.operation then
    if Mapping_operation.is_operation_head e.head then Some (operation_entry (Mapping_operation.find e.head)) else None
  else if Mapping_plan.is_type_head e.head then Some (type_entry (Mapping_plan.find e.head))
  else None

let mismatch target e now =
  let what = if e.operation then "operation" else "type" in
  let theirs =
    Pp.(
      Printer.pr_global e.instance ++ spc () ++ str "(" ++ str e.spelled ++ str ")")
  in
  let ours =
    match now with
    | None -> Pp.(strbrk ("no typed " ^ what ^ " mapping"))
    | Some n when GlobRef.CanOrd.equal n.instance e.instance ->
      Pp.(
        str "the same instance," ++ spc () ++ strbrk "compiled to a different ABI" ++ spc () ++ str "("
        ++ str n.spelled ++ str ")")
    | Some n -> Pp.(Printer.pr_global n.instance ++ spc () ++ str "(" ++ str n.spelled ++ str ")")
  in
  CErrors.user_err
    Pp.(
      hov 0
        ( strbrk "Crane: this extraction includes the unit" ++ spc () ++ str "\"" ++ str target ++ str "\","
        ++ spc () ++ strbrk ("whose header was written with the typed " ^ what ^ " mapping") ++ spc () ++ theirs ++ spc () ++ str "of"
        ++ spc () ++ Printer.pr_global e.head ++ str ";" ++ spc () ++ strbrk "this extraction resolves" ++ spc ()
        ++ ours ++ str "." ++ spc ()
        ++ strbrk
             "A unit and the units that include its header must select the same \
              mappings: import the same mapping files in both." ))

let check targets =
  List.iter
    (fun target ->
      match CString.Map.find_opt target !interfaces with
      | None -> ()
      | Some entries ->
        List.iter
          (fun e ->
            let now = current e in
            match now with
            | Some n when GlobRef.CanOrd.equal n.instance e.instance && String.equal n.abi e.abi -> ()
            | _ -> mismatch target e now)
          entries)
    targets
