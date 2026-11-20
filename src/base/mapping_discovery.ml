(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** See [mapping_discovery.mli]. *)

open Names
open Mapping_descriptor

type resolved_type_mapping = {
  type_instance : GlobRef.t;
  type_source : Constr.t;
  type_mapping : type_mapping;
}

type resolved_operation_mapping = {
  operation_instance : GlobRef.t;
  operation_source : declaration;
  operation_mapping : operation_mapping;
}

let tracing =
  let on = lazy (Sys.getenv_opt "CRANE_TRACE_MAPPINGS" <> None) in
  fun () -> Lazy.force on

let trace pp = if tracing () then Feedback.msg_notice Pp.(str "[crane:mappings] " ++ pp)

(** {1 Heads} *)

let type_heads : GlobRef.t list GlobRef.Map.t ref = State.cell State.Extraction GlobRef.Map.empty

let operation_heads : GlobRef.t list GlobRef.Map.t ref =
  State.cell State.Extraction GlobRef.Map.empty

module Constr_table = Hashtbl.Make (struct
  type t = Constr.t

  let equal = Constr.equal
  let hash = Constr.hash
end)

let type_cache : resolved_type_mapping option Constr_table.t = Constr_table.create 16
let operation_cache : resolved_operation_mapping option Constr_table.t = Constr_table.create 16

let () =
  State.on_reset State.Extraction (fun () ->
      Constr_table.reset type_cache;
      Constr_table.reset operation_cache )

let global_of_head sigma head =
  match EConstr.kind sigma head with
  | Constr.Const (k, _) -> Some (GlobRef.ConstRef k)
  | Constr.Ind (i, _) -> Some (GlobRef.IndRef i)
  | Constr.Construct (k, _) -> Some (GlobRef.ConstructRef k)
  | Constr.Var id -> Some (GlobRef.VarRef id)
  | _ -> None

let head_of sigma t = global_of_head sigma (fst (EConstr.decompose_app sigma t))

let path_name gr = Libnames.string_of_path (Nametab.path_of_global gr)

let pr_instances l = Pp.prlist_with_sep (fun () -> Pp.(str "," ++ spc ())) Printer.pr_global l

(* The class argument of an instance's conclusion: [T] in [TypeMapping T],
   [Ref d] in [OperationMapping (Ref d)]. *)
let class_argument sigma cls ty =
  let head, args = EConstr.decompose_app_list sigma ty in
  match (global_of_head sigma head, args) with
  | Some g, [arg] when GlobRef.CanOrd.equal g cls -> Some arg
  | _ -> None

(* [d] in [Ref {T} d], unreduced. *)
let ref_argument sigma decl =
  let head, args = EConstr.decompose_app_list sigma decl in
  match (EConstr.kind sigma head, args) with
  | Constr.Construct ((ind, 1), _), [_; d]
    when Option.equal GlobRef.CanOrd.equal (Some (GlobRef.IndRef ind))
           (Mapping_decode.registered "Declaration") ->
    Some d
  | _ -> None

let instance_head env sigma cls ~operation gr =
  let ty, _ = Typeops.type_of_global_in_context env gr in
  let _, concl = Term.decompose_prod_decls ty in
  let concl = EConstr.of_constr concl in
  match class_argument sigma cls concl with
  | None -> None
  | Some arg ->
    if operation then Option.bind (ref_argument sigma arg) (head_of sigma)
    else head_of sigma arg

let sorted l = List.sort (fun a b -> String.compare (path_name a) (path_name b)) l

let collect env sigma ~operation name =
  match Mapping_decode.registered name with
  | None -> GlobRef.Map.empty
  | Some cls ->
    let instances = Option.default [] (Typeclasses.instances cls) in
    List.fold_left
      (fun heads inst ->
        let gr = Typeclasses.instance_impl inst in
        match instance_head env sigma cls ~operation gr with
        | Some h ->
          let l = Option.default [] (GlobRef.Map.find_opt h heads) in
          GlobRef.Map.add h (gr :: l) heads
        | None ->
          CErrors.user_err
            Pp.(
              str "Crane: the " ++ str name ++ str " instance "
              ++ Printer.pr_global gr
              ++ spc ()
              ++ strbrk
                   ( if operation then
                       "does not name its operation by a reference: the \
                        argument of Ref must be a constant, inductive or \
                        constructor, possibly applied to parameters."
                     else
                       "maps no particular type: the mapped type must be \
                        headed by a constant, inductive or constructor." ) ))
      GlobRef.Map.empty instances
    |> GlobRef.Map.map sorted

let discover () =
  Constr_table.reset type_cache;
  Constr_table.reset operation_cache;
  let env = Global.env () in
  let sigma = Evd.from_env env in
  type_heads := collect env sigma ~operation:false "TypeMapping";
  operation_heads := collect env sigma ~operation:true "OperationMapping";
  if tracing () then
    List.iter
      (fun (what, heads) ->
        GlobRef.Map.iter
          (fun head insts ->
            trace
              Pp.(
                str what ++ str " head " ++ Printer.pr_global head ++ str ": "
                ++ pr_instances insts ))
          heads)
      [("type", !type_heads); ("operation", !operation_heads)]

let has_new_style_mapping g =
  GlobRef.Map.mem g !type_heads || GlobRef.Map.mem g !operation_heads

let has_type_mapping g = GlobRef.Map.mem g !type_heads

let type_mapping_heads () = GlobRef.Map.bindings !type_heads

let has_operation_mapping g = GlobRef.Map.mem g !operation_heads

let operation_mapping_heads () = GlobRef.Map.bindings !operation_heads

(** {1 Resolution} *)

(* The instance applied to a fresh evar for each of its binders, and the
   instantiated conclusion. *)
let instantiate env sigma gr =
  let sigma, c = Evd.fresh_global env sigma gr in
  let rec go sigma c ty =
    match EConstr.kind sigma (Reductionops.whd_all env sigma ty) with
    | Constr.Prod (_, dom, codom) ->
      let sigma, ev = Evarutil.new_evar env sigma dom in
      go sigma (EConstr.mkApp (c, [|ev|])) (EConstr.Vars.subst1 ev codom)
    | _ -> (sigma, c, ty)
  in
  go sigma c (Retyping.get_type_of env sigma c)

let unify env sigma a b =
  try
    let sigma = Evarconv.unify_delay env sigma a b in
    let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
    Some (Typeclasses.resolve_typeclasses ~fail:false env sigma)
  with e when CErrors.noncritical e -> None

(* The instances of [candidates] whose class argument, put through [matches],
   unifies: each with its evar map and instantiated dictionary. *)
let applicable env sigma cls candidates matches =
  List.filter_map
    (fun gr ->
      let sigma, dict, concl = instantiate env sigma gr in
      match class_argument sigma cls concl with
      | None -> None
      | Some arg -> (
        match matches sigma arg with
        | Some (sigma, extra) -> Some (gr, sigma, dict, extra)
        | None -> None ))
    candidates

let ambiguous what subject l =
  CErrors.user_err
    Pp.(
      hov 0
        ( str "Ambiguous " ++ str what ++ str " for" ++ spc () ++ subject
        ++ str ":" ++ spc () ++ str "the instances" ++ spc ()
        ++ Pp.prlist_with_sep
             (fun () -> str "," ++ spc ())
             (fun (gr, _, _, _) -> Libnames.pr_path (Nametab.path_of_global gr))
             l
        ++ spc () ++ str "all apply." ++ spc ()
        ++ strbrk
             "Crane never chooses between mappings by instance priority or \
              import order; import only one of them." ))

let closed_dictionary env sigma what subject gr dict =
  let dict = Evarutil.nf_evar sigma dict in
  if Evarutil.has_undefined_evars sigma dict then
    CErrors.user_err
      Pp.(
        hov 0
          ( str "The " ++ str what ++ str " " ++ Printer.pr_global gr ++ str " for"
          ++ spc () ++ subject ++ spc ()
          ++ strbrk "leaves some of its parameters undetermined:"
          ++ spc ()
          ++ Printer.pr_econstr_env env sigma dict
          ++ str "." ));
  dict

let cache_key sigma t =
  if Evarutil.has_undefined_evars sigma t then None else Some (EConstr.to_constr sigma t)

let cached table key compute =
  match key with
  | None -> compute ()
  | Some k -> (
    match Constr_table.find_opt table k with
    | Some r -> r
    | None ->
      let r = compute () in
      Constr_table.replace table k r;
      r )

let resolve_type_mapping env sigma ty =
  let ty = Evarutil.nf_evar sigma ty in
  match head_of sigma ty with
  | None -> None
  | Some h -> (
    match GlobRef.Map.find_opt h !type_heads with
    | None | Some [] -> None
    | Some candidates ->
      cached type_cache (cache_key sigma ty) (fun () ->
          let cls = Option.get (Mapping_decode.registered "TypeMapping") in
          let subject = Printer.pr_econstr_env env sigma ty in
          let matches sigma pat =
            Option.map (fun s -> (s, ())) (unify env sigma pat ty)
          in
          match applicable env sigma cls candidates matches with
          | [] -> None
          | _ :: _ :: _ as l -> ambiguous "type mapping" subject l
          | [(gr, sigma, dict, ())] ->
            let dict = closed_dictionary env sigma "type mapping" subject gr dict in
            let source = Evarutil.nf_evar sigma ty in
            let mapping = Mapping_decode.type_mapping env sigma dict in
            Mapping_validate.type_mapping env sigma ~instance:gr ~source mapping;
            trace
              Pp.(
                v 0
                  ( str "type " ++ subject ++ str " uses " ++ Printer.pr_global gr ++ cut ()
                  ++ Mapping_decode.pr_type_mapping env mapping ));
            Some
              { type_instance = gr;
                type_source = EConstr.to_constr sigma source;
                type_mapping = mapping } ) )

(** {1 Operation binders} *)

type binder_role = Type_parameter of int | Runtime of int | Instance | Erased

type operation_binder = {
  binder_id : Id.t;
  binder_name : Name.t;
  binder_type : EConstr.types;
  role : binder_role;
}

type operation_binders = {
  binders_env : Environ.env;
  binders : operation_binder list;
  result_type : EConstr.types;
  generic_use : EConstr.t;
}

let implicit_positions : (GlobRef.t -> Int.Set.t) ref = ref (fun _ -> Int.Set.empty)

(* As [Extraction.flag_of_type]: whether a term of type [t] is logical, and
   whether it is a type scheme. *)
let logical_quality = function
  | UnivGen.QualityOrSet.Qual (QConstant (QSProp | QProp)) -> true
  | Set | Qual (QConstant QType | QVar _) -> false

let rec flag_of_type env sigma t =
  let t = Reductionops.whd_all env sigma t in
  match EConstr.kind sigma t with
  | Constr.Prod (x, a, c) -> flag_of_type (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, a)) env) sigma c
  | Constr.Sort s -> (logical_quality (UnivGen.QualityOrSet.of_sort (EConstr.ESorts.kind sigma s)), true)
  | _ ->
    let logical =
      try logical_quality (Retyping.get_sort_quality_of ~polyprop:false env sigma t)
      with e when CErrors.noncritical e -> false
    in
    (logical, false)

let is_class_type env sigma t =
  let t = Reductionops.whd_all env sigma t in
  match head_of sigma (snd (EConstr.decompose_prod sigma t)) with
  | Some g -> Typeclasses.is_class g
  | None -> false

let binder_id k = Id.of_string (Printf.sprintf "crane_operation_binder_%d" k)

let operation_binders env sigma g =
  let sigma, head = Evd.fresh_global env sigma g in
  let implicits = !implicit_positions g in
  let rec go env k ntypes nruntime acc ty =
    match EConstr.kind sigma (Reductionops.whd_all env sigma ty) with
    | Constr.Prod (na, dom, codom) ->
      let id = binder_id k in
      let role, ntypes, nruntime =
        match flag_of_type env sigma dom with
        | true, _ -> (Erased, ntypes, nruntime)
        | false, true -> (Type_parameter ntypes, ntypes + 1, nruntime)
        | false, false ->
          if Int.Set.mem (k + 1) implicits then (Erased, ntypes, nruntime)
          else if is_class_type env sigma dom then (Instance, ntypes, nruntime)
          else (Runtime nruntime, ntypes, nruntime + 1)
      in
      let b = {binder_id = id; binder_name = na.Context.binder_name; binder_type = dom; role} in
      let decl = Context.Named.Declaration.LocalAssum (Context.make_annot id na.Context.binder_relevance, dom) in
      go (EConstr.push_named decl env) (k + 1) ntypes nruntime (b :: acc)
        (EConstr.Vars.subst1 (EConstr.mkVar id) codom)
    | _ -> (env, List.rev acc, ty)
  in
  let binders_env, binders, result_type = go env 0 0 0 [] (Retyping.get_type_of env sigma head) in
  let generic_use = EConstr.mkApp (head, Array.of_list (List.map (fun b -> EConstr.mkVar b.binder_id) binders)) in
  {binders_env; binders; result_type; generic_use}

let runtime_binders b = List.filter (fun b -> match b.role with Runtime _ -> true | _ -> false) b.binders

(* The retained runtime binders of the operation [g] and the type mappings
   of their types and of its result, where those are mapped. *)
let operation_context env g =
  let sigma = Evd.from_env env in
  let b = operation_binders env sigma g in
  let known t =
    Option.map (fun r -> r.type_mapping) (resolve_type_mapping b.binders_env sigma t)
  in
  let runtime =
    List.map
      (fun (x : operation_binder) ->
        { Mapping_validate.binder_name =
            (match x.binder_name with Name id -> Some (Id.to_string id) | Anonymous -> None);
          binder_mapping = lazy (known x.binder_type) })
      (runtime_binders b)
  in
  {Mapping_validate.runtime_binders = Some runtime; result_mapping = known b.result_type}

let resolve_operation_mapping env sigma term =
  let term = Evarutil.nf_evar sigma term in
  let qhead, qargs = EConstr.decompose_app_list sigma term in
  match global_of_head sigma qhead with
  | None -> None
  | Some h -> (
    match GlobRef.Map.find_opt h !operation_heads with
    | None | Some [] -> None
    | Some candidates ->
      cached operation_cache (cache_key sigma term) (fun () ->
          let cls = Option.get (Mapping_decode.registered "OperationMapping") in
          let subject = Printer.pr_econstr_env env sigma term in
          (* An instance for [Ref (f a1 .. ak)] covers the uses of [f] with
             at least k arguments; the first k must unify. *)
          let matches sigma arg =
            match ref_argument sigma arg with
            | None -> None
            | Some d ->
              let _, dargs = EConstr.decompose_app_list sigma d in
              let k = List.length dargs in
              if List.length qargs < k then None
              else
                let query = EConstr.mkApp (qhead, Array.of_list (CList.firstn k qargs)) in
                Option.map (fun s -> (s, d)) (unify env sigma d query)
          in
          match applicable env sigma cls candidates matches with
          | [] -> None
          | _ :: _ :: _ as l -> ambiguous "operation mapping" subject l
          | [(gr, sigma, dict, d)] ->
            let dict = closed_dictionary env sigma "operation mapping" subject gr dict in
            let d = Evarutil.nf_evar sigma d in
            let source =
              match Mapping_decode.reference_of env sigma d with
              | Some s -> s
              | None -> CErrors.anomaly Pp.(str "Crane: an operation head without a reference.")
            in
            let mapping = Mapping_decode.operation_mapping env sigma dict in
            Mapping_validate.operation_mapping env ~instance:gr ~source
              (operation_context (Global.env ()) h) mapping;
            trace
              Pp.(
                v 0
                  ( str "operation " ++ subject ++ str " uses " ++ Printer.pr_global gr
                  ++ cut ()
                  ++ Mapping_decode.pr_operation_mapping mapping ));
            Some
              { operation_instance = gr;
                operation_source = source;
                operation_mapping = mapping } ) )

(** {1 Commands} *)

type resolved =
  | Resolved_type of resolved_type_mapping
  | Resolved_operation of resolved_operation_mapping
  | Unmapped

let resolve_query c =
  discover ();
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, t = Constrintern.interp_constr_evars env sigma c in
  let is_type =
    EConstr.isSort sigma (Reductionops.whd_all env sigma (Retyping.get_type_of env sigma t))
  in
  let r =
    if is_type then Option.map (fun r -> Resolved_type r) (resolve_type_mapping env sigma t)
    else Option.map (fun r -> Resolved_operation r) (resolve_operation_mapping env sigma t)
  in
  (env, sigma, t, Option.default Unmapped r)

let show c =
  let env, sigma, t, r = resolve_query c in
  let subject = Printer.pr_econstr_env env sigma t in
  Feedback.msg_notice
    Pp.(
      match r with
      | Unmapped -> str "No typed mapping applies to " ++ subject ++ str "."
      | Resolved_type r ->
        v 0
          ( subject ++ str " is mapped by " ++ Printer.pr_global r.type_instance ++ str ":"
          ++ cut ()
          ++ Mapping_decode.pr_type_mapping env r.type_mapping )
      | Resolved_operation r ->
        v 0
          ( subject ++ str " is mapped by "
          ++ Printer.pr_global r.operation_instance
          ++ str ":" ++ cut ()
          ++ Mapping_decode.pr_operation_mapping r.operation_mapping ))

let check_selects c qid =
  let expected = Smartlocate.global_with_alias qid in
  let env, sigma, t, r = resolve_query c in
  let subject = Printer.pr_econstr_env env sigma t in
  let selected =
    match r with
    | Unmapped -> None
    | Resolved_type r -> Some r.type_instance
    | Resolved_operation r -> Some r.operation_instance
  in
  match selected with
  | Some g when GlobRef.CanOrd.equal g expected ->
    Feedback.msg_notice Pp.(subject ++ str " is mapped by " ++ Printer.pr_global g ++ str ".")
  | Some g ->
    CErrors.user_err
      Pp.(
        subject ++ str " is mapped by " ++ Printer.pr_global g ++ str ", not "
        ++ Printer.pr_global expected ++ str ".")
  | None ->
    CErrors.user_err
      Pp.(str "No typed mapping applies to " ++ subject ++ str ", expected "
          ++ Printer.pr_global expected ++ str ".")

let check_unmapped c =
  let env, sigma, t, r = resolve_query c in
  let subject = Printer.pr_econstr_env env sigma t in
  match r with
  | Unmapped -> Feedback.msg_notice Pp.(str "No typed mapping applies to " ++ subject ++ str ".")
  | Resolved_type {type_instance = g; _} | Resolved_operation {operation_instance = g; _} ->
    CErrors.user_err
      Pp.(subject ++ str " is mapped by " ++ Printer.pr_global g ++ str ", expected no mapping.")

let normalise_space s =
  String.split_on_char '\n' s
  |> List.concat_map (String.split_on_char ' ')
  |> List.filter (fun w -> w <> "")
  |> String.concat " "

let contains ~sub s =
  let n = String.length s and k = String.length sub in
  let rec go i = i + k <= n && (String.sub s i k = sub || go (i + 1)) in
  go 0

let check_fails c expected =
  match resolve_query c with
  | _, _, _, (Unmapped | Resolved_type _ | Resolved_operation _) ->
    CErrors.user_err
      Pp.(str "Expected resolving the typed mapping to fail with \"" ++ str expected
          ++ str "\", but it succeeded.")
  | exception e when CErrors.noncritical e ->
    let message = normalise_space (Pp.string_of_ppcmds (CErrors.print e)) in
    if contains ~sub:(normalise_space expected) message then
      Feedback.msg_notice Pp.(str "Failed as expected: " ++ str message)
    else
      CErrors.user_err
        Pp.(str "Expected a failure containing \"" ++ str expected ++ str "\", got:"
            ++ spc () ++ str message)
