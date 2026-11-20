(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** See [mapping_operation.mli]. *)

open Names
open Mapping_descriptor

type purity = Pure | Effectful | Opaque

type view_conversions = {
  kind : Mapping_plan.view_kind;
  mapped : GlobRef.t;
  from_canonical : string;
  read_from_write : string option;
  materialise : string option;
}

type argument = {
  name : string;
  use : input_use;
  position : int;
  binder : int;
  in_place : bool;
  view : view_conversions option;
}

type t = {
  instance : GlobRef.t;
  source : GlobRef.t;
  template : string;
  arguments : argument list;
  binder_count : int;
  call_binders : int list;
  result : result_spec;
  result_view : view_conversions option;
  facts : operation_fact list;
  purity : purity;
  headers : string list;
}

let is_operation_head g = Mapping_discovery.has_operation_mapping g

let fail_operation g detail =
  CErrors.user_err
    Pp.(hov 0 (str "Crane: the operation mapping of" ++ spc () ++ Printer.pr_global g ++ str ":" ++ spc () ++ detail))

let starts_at text i s =
  let k = String.length s in
  i + k <= String.length text && String.sub text i k = s

(* [text] with each [%name(x)] hole replaced by [f name x]. *)
let compile_template ~fail ~arg ~stored text =
  let n = String.length text in
  let b = Buffer.create n in
  let named hole i k =
    let close = try String.index_from text i ')' with Not_found -> n in
    let start = i + String.length hole in
    let x = String.trim (String.sub text start (max 0 (close - start))) in
    Buffer.add_string b (k x);
    close + 1
  in
  let rec go i =
    if i >= n then ()
    else if starts_at text i "%arg(" then go (named "%arg(" i (fun x -> Printf.sprintf "%%a%d" (arg x)))
    else if starts_at text i "%stored(" then go (named "%stored(" i (fun x -> Printf.sprintf "%%t%d" (stored x)))
    else if starts_at text i "%tmp" && i + 4 < n && text.[i + 4] >= '0' && text.[i + 4] <= '9' then
      fail
        (Pp.strbrk
           "operation_cpp uses a fresh-name hole (%tmpN), which operation \
            templates do not support yet; use a WithBody construction and \
            assign %result instead.")
    else (
      Buffer.add_char b text.[i];
      go (i + 1) )
  in
  go 0;
  Buffer.contents b

(* The type parameter of the operation that component [c] of a mapped type
   is stored at, searched in [candidates] in order: the first mapped type
   declaring [c] decides. *)
let stored_parameter ~fail sigma (binders : Mapping_discovery.operation_binders) candidates c =
  let parameter_of id =
    List.find_map
      (fun (b : Mapping_discovery.operation_binder) ->
        match b.role with
        | Type_parameter m when Id.equal b.binder_id id -> Some m
        | _ -> None)
      binders.binders
  in
  let declaring t =
    let head, args = EConstr.decompose_app_list sigma t in
    let g =
      match EConstr.kind sigma head with
      | Constr.Ind (i, _) -> Some (GlobRef.IndRef i)
      | Constr.Const (k, _) -> Some (GlobRef.ConstRef k)
      | _ -> None
    in
    match g with
    | Some g when Mapping_plan.is_type_head g -> (
      match List.assoc_opt c (Mapping_plan.find g).component_binders with
      | Some p -> Some (g, List.nth_opt args p)
      | None -> None )
    | _ -> None
  in
  let rec inside t =
    match declaring t with
    | Some r -> Some r
    | None -> List.find_map inside (snd (EConstr.decompose_app_list sigma t))
  in
  let found =
    List.find_map (fun (whole, t) -> if whole then declaring t else inside t) candidates
  in
  match found with
  | None ->
    fail
      (Pp.strbrk
         (Printf.sprintf
            "operation_cpp uses %%stored(%s), but neither the type of an \
             argument nor the result type is a mapped type declaring a \
             component \"%s\"."
            c c))
  | Some (g, arg) -> (
    (* A type family parameter applied to terms ([V idx]) is the type
       variable [V]: extraction drops a type variable's term arguments. *)
    let head = Option.map (fun a -> EConstr.kind sigma (fst (EConstr.decompose_app sigma a))) arg in
    match head with
    | Some (Constr.Var id) when Option.has_some (parameter_of id) -> Option.get (parameter_of id)
    | _ ->
      fail
        Pp.(
          strbrk (Printf.sprintf "operation_cpp uses %%stored(%s), the component of" c)
          ++ spc () ++ Printer.pr_global g ++ spc ()
          ++ strbrk
               "found first, but its type there is not one of the operation's \
                type parameters, so Crane cannot name its C++ type in the \
                template.") )

let compile g =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let binders = Mapping_discovery.operation_binders env sigma g in
  let resolved =
    match Mapping_discovery.resolve_operation_mapping binders.binders_env sigma binders.generic_use with
    | Some r -> r
    | None ->
      fail_operation g
        (Pp.strbrk
           "no OperationMapping instance applies to every instantiation of \
            its parameters; an instance for one particular instantiation is \
            not supported yet.")
  in
  let m = resolved.operation_mapping in
  let fail detail =
    fail_operation g Pp.(str "the instance" ++ spc () ++ Printer.pr_global resolved.operation_instance ++ spc () ++ detail)
  in
  let runtime =
    List.filter_map
      (fun ((b : Mapping_discovery.operation_binder), k) ->
        match b.role with Runtime pos -> Some (b, k, pos) | _ -> None)
      (List.mapi (fun k b -> (b, k)) binders.binders)
  in
  let purity, specs, result, facts =
    match m.operation_contract with
    | Pure_operation (a, r, f) -> (Pure, Some a, r, f)
    | Effectful_operation (a, r, f) -> (Effectful, Some a, r, f)
    | Opaque_operation -> (Opaque, None, Return_opaque, [])
  in
  (* Whether an argument used as [use] at a binder of type [t] is passed to
     the template as a mutable lvalue: a [Replace] of a mapped type, or a
     write of one whose write-through form is [T&] (design 6.6). *)
  let mapped_head t =
    let head, _ = EConstr.decompose_app_list sigma t in
    match EConstr.kind sigma head with
    | Constr.Ind (i, _) when Mapping_plan.is_type_head (GlobRef.IndRef i) -> Some (GlobRef.IndRef i)
    | Constr.Const (k, _) when Mapping_plan.is_type_head (GlobRef.ConstRef k) -> Some (GlobRef.ConstRef k)
    | _ -> None
  in
  (* The view an argument used as [use] at a binder of type [t] is given to
     the template as (design 7.5): a [Read] the read view, a [Write] the
     writable view, where its mapped type declares one. *)
  let view_of use t =
    match mapped_head t with
    | None -> None
    | Some g -> (
      let p = Mapping_plan.find g in
      match use with
      | Read when Mapping_plan.has_view p Read_view -> Some (g, Mapping_plan.Read_view)
      | Write when Mapping_plan.has_view p Write_view -> Some (g, Mapping_plan.Write_view)
      | _ -> None )
  in
  let in_place use t =
    match mapped_head t with
    | Some _ when Option.has_some (view_of use t) -> false
    | Some g -> (
      let p = Mapping_plan.find g in
      match use with
      | Replace -> Mapping_plan.replace_form p = Mapping_plan.Physical_mutable_reference
      | Write | Write_canonical -> Mapping_plan.write_through p = Mapping_plan.Physical_mutable_reference
      | Ignore | Read | Read_canonical | Take | Opaque_use -> false )
    | _ -> false
  in
  let arguments =
    match specs with
    | Some specs ->
      (* Validated one to one when the mapping was resolved. *)
      List.map2
        (fun s ((b : Mapping_discovery.operation_binder), k, pos) ->
          { name = s.argument_name;
            use = s.argument_use;
            position = pos;
            binder = k;
            in_place = in_place s.argument_use b.binder_type;
            view = None })
        specs runtime
    | None ->
      List.map
        (fun ((b : Mapping_discovery.operation_binder), k, pos) ->
          let name = match b.binder_name with Name id -> Id.to_string id | Anonymous -> "" in
          {name; use = Opaque_use; position = pos; binder = k; in_place = false; view = None})
        runtime
  in
  let arg x =
    match List.find_opt (fun a -> a.name = x) arguments with
    | Some a -> a.position
    | None ->
      fail
        (Pp.strbrk
           (Printf.sprintf "operation_cpp names argument \"%s\", which is not a retained runtime binder of the operation." x))
  in
  let candidates =
    List.map (fun ((b : Mapping_discovery.operation_binder), _, _) -> (true, b.binder_type)) runtime
    @ [(false, binders.result_type)]
  in
  (* A call's type arguments are its kept dictionaries' first, then the
     type parameters ({!Core_to_cpp.Calls.call_type_args}). *)
  let dictionaries =
    List.length
      (List.filter
         (fun (b : Mapping_discovery.operation_binder) ->
           b.role = Instance && Mapping_discovery.is_kept_instance binders.binders_env sigma b.binder_type)
         binders.binders)
  in
  let stored c = dictionaries + stored_parameter ~fail sigma binders candidates c in
  let template t = compile_template ~fail ~arg ~stored t in
  (* A view's conversions, in the operation's vocabulary: the component
     types are the operation's type parameters ([%tN]) the type [t] stores
     them at. *)
  let conversions ~whole (g, kind) t =
    let p = Mapping_plan.find g in
    let at text =
      (* [text] is in the plan's vocabulary: [%tI] is the mapped type's type
         argument [I], stored at the operation's type parameter named by
         the component declared there. *)
      let component i = List.find_map (fun (c, j) -> if j = i then Some c else None) p.components in
      let n = String.length text in
      let b = Buffer.create n in
      let rec go i =
        if i >= n then ()
        else if text.[i] = '%' && i + 2 < n && text.[i + 1] = 't' && text.[i + 2] >= '0' && text.[i + 2] <= '9' then (
          let j = ref (i + 2) in
          while !j < n && text.[!j] >= '0' && text.[!j] <= '9' do incr j done;
          let k = int_of_string (String.sub text (i + 2) (!j - i - 2)) in
          ( match component k with
          | Some c ->
            Buffer.add_string b
              (Printf.sprintf "%%t%d" (dictionaries + stored_parameter ~fail sigma binders [(whole, t)] c))
          | None ->
            fail
              (Pp.strbrk
                 (Printf.sprintf
                    "a view conversion of the type of an argument names its type argument %d, which no component \
                     names, so Crane cannot name its C++ type at a call."
                    k)) );
          go !j )
        else (
          Buffer.add_char b text.[i];
          go (i + 1) )
      in
      go 0;
      Buffer.contents b
    in
    let v = Option.get (Mapping_plan.view p kind) in
    { kind;
      mapped = g;
      from_canonical = at v.from_canonical;
      read_from_write = (match kind with Write_view -> Option.map at p.views.read_from_write | Read_view -> None);
      materialise = (match v.escape with Materialise e -> Some (at e) | Borrow_only -> None) }
  in
  let arguments =
    List.map
      (fun a ->
        match List.find_opt (fun ((b : Mapping_discovery.operation_binder), k, _) -> k = a.binder) runtime with
        | Some (b, _, _) ->
          {a with view = Option.map (fun gv -> conversions ~whole:true gv b.binder_type) (view_of a.use b.binder_type)}
        | None -> a)
      arguments
  in
  (* A result borrowed as a view, which a call materialises where it
     escapes (design 12.8). *)
  let result_view =
    match result with
    | Return_borrowed (((Read_view_borrow | Writable_view_borrow) as form), _) -> (
      let kind = match form with Writable_view_borrow -> Mapping_plan.Write_view | _ -> Mapping_plan.Read_view in
      let rec find t =
        match mapped_head t with
        | Some g -> Some (g, t)
        | None -> List.find_map find (snd (EConstr.decompose_app_list sigma t))
      in
      match find binders.result_type with
      | Some (g, t) when Mapping_plan.has_view (Mapping_plan.find g) kind -> Some (conversions ~whole:true (g, kind) t)
      | _ -> None )
    | _ -> None
  in
  let text =
    match m.operation_cpp with
    | Expr e -> template e
    | With_body (i, b) -> "%result = " ^ template i ^ "; " ^ template b
  in
  { instance = resolved.operation_instance;
    source = g;
    template = text;
    arguments;
    binder_count = List.length binders.binders;
    call_binders =
      List.concat
        (List.mapi
           (fun k (b : Mapping_discovery.operation_binder) ->
             match b.role with Runtime _ | Instance -> [k] | Type_parameter _ | Erased -> [])
           binders.binders);
    result;
    result_view;
    facts;
    purity;
    headers = m.operation_headers }

let plans : t GlobRef.Map.t ref = State.cell State.Extraction GlobRef.Map.empty

let find g =
  match GlobRef.Map.find_opt g !plans with
  | Some p -> p
  | None ->
    let p = compile g in
    plans := GlobRef.Map.add g p !plans;
    p

let arity p = List.length p.arguments

let owns p a =
  match a.use with
  | Take | Opaque_use -> true
  | Ignore | Read | Read_canonical | Write | Write_canonical | Replace ->
    List.exists (function Retains_argument (x, _) -> x = a.name | _ -> false) p.facts

let owned_call_arguments p =
  List.map
    (fun k -> match List.find_opt (fun a -> a.binder = k) p.arguments with Some a -> owns p a | None -> false)
    p.call_binders

let headers g = if is_operation_head g then (find g).headers else []

let call_argument_uses p =
  List.map
    (fun k -> Option.map (fun a -> a.use) (List.find_opt (fun a -> a.binder = k) p.arguments))
    p.call_binders

let in_place_positions p = List.filter_map (fun a -> if a.in_place then Some a.position else None) p.arguments
