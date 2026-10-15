(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

module Template_param = struct
  type t = {
    position : int;
    name : Id.t;
  }

  let position p = p.position
  let name p = p.name
  let equal a b = Int.equal a.position b.position && Id.equal a.name b.name
end

type origin =
  | From_scheme of Scheme.Var.t
  | From_instance of int
  | From_callable of int
  | Derived of Id.t

type write_policy =
  | Writable
  | Deduce_only
  | Defaulted of Minicpp.cpp_type
  | Phantom of Minicpp.cpp_type

type template_parameter = {
  id : Template_param.t;
  origin : origin;
  kind : Minicpp.template_type;
  write : write_policy;
}

type receiver = {
  dropped : Scheme.Var.t list;
  dropped_names : Id.t list;
  params : Minicpp.cpp_type list;
  ret : Minicpp.cpp_type;
  return_only : Id.t list;
}

type omission =
  | Class_carrier
  | Unmentioned

type passing =
  | Owned
  | Borrowed
  | Forwarded

type t = {
  callee : GlobRef.t;
  head : template_parameter list;
  deduced_callables : Param_pos.orig Param_pos.pos list;
  receiver : receiver option;
  passing : passing list option;
  variables : (Scheme.Var.t * omission option) list;
  relaxations : Head_relaxation.t list;
  phase : Common.phase;
}

let callee abi = abi.callee
let relaxations abi = abi.relaxations
let declared_head abi = List.map (fun p -> (p.kind, Template_param.name p.id)) abi.head
let template_head abi = abi.head
let receiver abi = abi.receiver

let scheme_variables ?(omitted = fun _ -> None) scheme =
  List.map (fun v -> (v, omitted v)) (Option.cata Scheme.Var.all [] scheme)

let keeps abi v =
  match List.find_opt (fun (v', _) -> Scheme.Var.equal v v') abi.variables with
  | Some (_, Some _) -> false
  | Some (_, None) | None -> true

let keeps_tvar abi i =
  match List.find_opt (fun (v, _) -> Int.equal (Scheme.Var.ordinal v) i) abi.variables with
  | Some (v, _) -> keeps abi v
  | None -> true

let dictionary_carriers abi =
  let mentioned =
    List.fold_left
      (fun n (v, o) -> if o = Some Unmentioned then n else max n (Scheme.Var.ordinal v))
      0 abi.variables
  in
  List.filter_map
    (fun (v, o) -> if o <> None && Scheme.Var.ordinal v <= mentioned then Some v else None)
    abi.variables

(* The [n] for which [spell n] is [name]: the number a generated name
   carries, read back through the function that minted it. *)
let numbered spell name =
  let s = Id.to_string name in
  let rec digits_from i =
    if i > 0 && s.[i - 1] >= '0' && s.[i - 1] <= '9' then digits_from (i - 1) else i
  in
  let start = digits_from (String.length s) in
  Option.bind
    (int_of_string_opt (String.sub s start (String.length s - start)))
    (fun n -> if String.equal (spell n) s then Some n else None)

let origin_of ?(relaxed = fun _ -> false) ?(renumber = Fun.id) ~scheme name =
  let var =
    Option.bind (Minicpp.tvar_number name) (fun i ->
        if relaxed i then None
        else Option.bind scheme (fun s -> Scheme.Var.of_tvar s (renumber i)) )
  in
  match var with
  | Some v -> From_scheme v
  | None -> (
    match numbered Common.tc_instance_name name with
    | Some k -> From_instance k
    | None -> (
      match numbered Common.fun_tparam_name name with
      | Some i -> From_callable i
      | None -> Derived name ) )

(* The first [n] parameters standing for scheme variables are the
   declaration's leading phantoms: no signature mentions them, so nothing
   deduces them, and a call writes them -- as their default, or [void]. *)
let mark_phantoms n head =
  let rec go n = function
    | [] -> []
    | ({origin = From_scheme _; kind; _} as p) :: rest when n > 0 ->
      let filler =
        match kind with Minicpp.TTtypename_default d -> d | _ -> Minicpp.Tvoid
      in
      let p =
        match kind with
        | Minicpp.TTtypename | Minicpp.TTtypename_default _ -> {p with write = Phantom filler}
        | _ -> p
      in
      p :: go (n - 1) rest
    | p :: rest -> p :: go n rest
  in
  go n head

let of_head ?omitted ?(phantom_prefix = 0) ?relaxed ?renumber ?(deduced_callables = []) ?receiver
    ?passing ?(relaxations = []) ~callee ~scheme temps =
  let head =
    List.mapi
      (fun position (kind, name) ->
        let origin = origin_of ?relaxed ?renumber ~scheme name in
        let write =
          match (kind, origin) with
          | Minicpp.TTtypename_default d, _ -> Defaulted d
          | _, From_callable _ -> Deduce_only
          | _ -> Writable
        in
        {id = {Template_param.position; name}; origin; kind; write} )
      temps
  in
  { callee;
    head = mark_phantoms phantom_prefix head;
    deduced_callables;
    receiver;
    passing;
    variables = scheme_variables ?omitted scheme;
    relaxations;
    phase = Common.get_phase () }

let passing abi = abi.passing

(* A method of an instance's struct belongs to the instance: it has no
   global of its own, and no scheme -- its variables are the method's own
   quantifiers and the class-typed arguments it takes, all named. *)
let of_instance_method ~instance (mf : Minicpp.method_field) =
  of_head ~callee:instance ~scheme:None
    ~receiver:
      { dropped = [];
        dropped_names = [];
        params = List.map snd mf.mf_params;
        ret = mf.mf_ret_type;
        return_only = [] }
    mf.mf_tparams

let deduces_callable_at abi pos = List.exists (Param_pos.equal pos) abi.deduced_callables

let parameter_of_var abi v =
  List.find_opt
    (fun p ->
      match p.origin with
      | From_scheme v' -> Scheme.Var.equal v v'
      | _ -> false )
    abi.head

let validate abi =
  let positions =
    List.concat
      (List.mapi
         (fun k p ->
           if Template_param.position p.id = k then []
           else [Printf.sprintf "parameter %d out of order" k] )
         abi.head )
  in
  let names = List.map (fun p -> Template_param.name p.id) abi.head in
  let unique_names =
    if List.length (List.sort_uniq Id.compare names) = List.length names then []
    else ["two parameters share a name"]
  in
  let scheme_origins = List.filter_map (fun p -> match p.origin with From_scheme v -> Some v | _ -> None) abi.head in
  let owned =
    List.filter_map
      (fun v ->
        if GlobRef.UserOrd.equal (Scheme.Id.owner (Scheme.Var.owner v)) abi.callee then None
        else Some "a parameter declares another declaration's variable" )
      scheme_origins
  in
  let unique_origins =
    if List.length (List.sort_uniq Scheme.Var.compare scheme_origins) = List.length scheme_origins
    then []
    else ["two parameters declare one variable"]
  in
  positions @ unique_names @ owned @ unique_origins

(* Two plans of one declaration agree when their heads do; a scheme origin
   is compared by its variable's place, as a scheme minted for a declaration
   with none recorded is a new identity each time it is asked for. *)
let same_head a b =
  let origin_key = function
    | From_scheme v -> `Scheme (Scheme.Var.ordinal v)
    | From_instance k -> `Instance k
    | From_callable i -> `Callable i
    | Derived n -> `Derived (Id.to_string n)
  in
  let key p = (Id.to_string (Template_param.name p.id), origin_key p.origin, p.kind, p.write) in
  let receiver_key r =
    ( List.map Scheme.Var.ordinal r.dropped,
      List.map Id.to_string r.dropped_names,
      r.params,
      r.ret,
      List.map Id.to_string r.return_only )
  in
  let variables_key abi = List.map (fun (v, o) -> (Scheme.Var.ordinal v, o)) abi.variables in
  List.equal (fun p q -> key p = key q) a.head b.head
  && List.equal Param_pos.equal a.deduced_callables b.deduced_callables
  && Option.equal ( = ) (Option.map receiver_key a.receiver) (Option.map receiver_key b.receiver)
  && Option.equal (List.equal ( = )) a.passing b.passing
  && variables_key a = variables_key b
  && List.equal Head_relaxation.equal a.relaxations b.relaxations

let equal a b = GlobRef.UserOrd.equal a.callee b.callee && same_head a b

let plans : t GlobRef.Map_env.t ref = State.cell State.Extraction GlobRef.Map_env.empty

let assumed : Param_pos.orig Param_pos.pos list Ref.User.Map.t ref =
  State.cell State.Extraction Ref.User.Map.empty

let () =
  Table.register_census "callable ABI plans" (fun () -> GlobRef.Map_env.cardinal !plans)

let describe abi =
  let kind = function
    | Minicpp.TTtypename -> "typename"
    | Minicpp.TTtypename_default _ -> "typename="
    | Minicpp.TTtemplate n -> Printf.sprintf "template/%d" n
    | Minicpp.TTfun _ -> "callable"
    | Minicpp.TTinvocable _ -> "invocable"
    | Minicpp.TTconcept _ -> "concept"
  in
  let origin = function
    | From_scheme v -> Printf.sprintf "var %d" (Scheme.Var.ordinal v)
    | From_instance k -> Printf.sprintf "instance %d" k
    | From_callable i -> Printf.sprintf "callable %d" i
    | Derived _ -> "derived"
  in
  String.concat ", "
    (List.map
       (fun p ->
         Printf.sprintf "%s %s (%s)" (kind p.kind)
           (Id.to_string (Template_param.name p.id))
           (origin p.origin) )
       abi.head )

let phase_name = function
  | Common.Plan -> "while planning"
  | Common.Emit Common.Impl -> "emitting the implementation"
  | Common.Emit Common.Intf -> "emitting the interface"

let validated abi =
  List.iter
    (fun problem ->
      Probe.violation "callable ABI"
        Pp.(str "the plan of " ++ GlobRef.print abi.callee ++ str ": " ++ str problem) )
    (validate abi)

(* [abi], decided after [old], against it. *)
let reproduces old abi =
  if not (same_head old abi) then
    Probe.violation "callable ABI"
      Pp.(
        str "the declaration of " ++ GlobRef.print abi.callee ++ str " was decided with the head <"
        ++ str (describe abi) ++ str "> " ++ str (phase_name abi.phase)
        ++ str " where its plan, decided " ++ str (phase_name old.phase) ++ str ", says <"
        ++ str (describe old) ++ str ">" )

let install callables assume =
  plans :=
    List.fold_left
      (fun m abi ->
        validated abi;
        match GlobRef.Map_env.find_opt abi.callee m with
        | Some old -> reproduces old abi; m
        | None -> GlobRef.Map_env.add abi.callee abi m )
      GlobRef.Map_env.empty callables;
  assumed := List.fold_left (fun m (r, ps) -> Ref.User.Map.add r ps m) Ref.User.Map.empty assume

let lookup r = GlobRef.Map_env.find_opt r !plans

(* The methods of each instance's struct, by name. *)
let instance_methods : (Id.t * t) list Ref.User.Map.t ref = State.cell State.Extraction Ref.User.Map.empty

let install_instance_methods planned =
  instance_methods :=
    List.fold_left
      (fun m (instance, methods) ->
        List.iter (fun (_, abi) -> validated abi) methods;
        Ref.User.Map.add instance methods m )
      Ref.User.Map.empty planned

let instance_method ~instance name =
  Option.bind (Ref.User.Map.find_opt instance !instance_methods) (fun methods ->
      List.find_map (fun (n, abi) -> if Id.equal n name then Some abi else None) methods )

let check_instance_method ~instance name abi =
  validated abi;
  match instance_method ~instance name with
  | Some old -> reproduces old abi
  | None ->
    Probe.violation "callable ABI"
      Pp.(
        str "the method " ++ Id.print name ++ str " of " ++ GlobRef.print instance
        ++ str " was generated with no plan: planning the callables missed it" )

let check abi =
  validated abi;
  match lookup abi.callee with
  | Some old -> reproduces old abi
  | None ->
    Probe.violation "callable ABI"
      Pp.(
        str "the declaration of " ++ GlobRef.print abi.callee
        ++ str " was generated with no plan: planning the callables missed it" )

let deduces_callable r pos =
  match lookup r with
  | Some abi -> deduces_callable_at abi pos
  | None -> List.exists (Param_pos.equal pos) (Option.default [] (Ref.User.Map.find_opt r !assumed))

(* [abi] with [instances] dictionaries in front of its head, as a call
   passing that many writes it. *)
let with_dictionaries instances abi =
  let dictionaries =
    List.init instances (fun k ->
        let name = Common.tc_instance_id k in
        { id = {Template_param.position = k; name};
          origin = From_instance k;
          kind = Minicpp.TTtypename;
          write = Writable } )
  in
  let shift p = {p with id = {p.id with Template_param.position = p.id.position + instances}} in
  {abi with head = dictionaries @ List.map shift abi.head}

let foreign ?omitted ?(instances = 0) ?(higher_kinded = fun _ -> false) ?(kept = fun _ -> true)
    ?(reachable = max_int) ?(relaxed = fun _ -> false) ?(phantom_prefix = 0) ~callee ~scheme () =
  let variables =
    List.map
      (fun v ->
        let name = Minicpp.tvar_id (Scheme.Var.ordinal v) in
        if relaxed (Scheme.Var.ordinal v) then
          (Minicpp.TTtypename_default Minicpp.Tvoid, name, Derived name)
        else
          ( (if higher_kinded v then Minicpp.TTtemplate 1 else Minicpp.TTtypename),
            name,
            From_scheme v ) )
      (List.filteri (fun k _ -> k < reachable)
         (List.filter kept (Option.cata Scheme.Var.all [] scheme)) )
  in
  let head =
    List.mapi
      (fun position (kind, name, origin) ->
        let write = match kind with Minicpp.TTtypename_default d -> Defaulted d | _ -> Writable in
        {id = {Template_param.position; name}; origin; kind; write} )
      variables
  in
  with_dictionaries instances
    { callee;
      head = mark_phantoms phantom_prefix head;
      deduced_callables = [];
      receiver = None;
      passing = None;
      variables = scheme_variables ?omitted scheme;
      relaxations = [];
      phase = Common.get_phase () }

(* The unit's foreign plans, without dictionaries, by callee. *)
let foreign_plans : t GlobRef.Map_env.t ref = State.cell State.Unit GlobRef.Map_env.empty

type foreign_tally = {found : int; derived : int}

let foreign_tally = State.cell State.Unit {found = 0; derived = 0}

let install_foreign derive callees =
  (* [derive] plans through {!plan}, which must derive afresh rather than
     answer from plans this replaces. *)
  foreign_plans := GlobRef.Map_env.empty;
  foreign_plans :=
    List.fold_left
      (fun m r ->
        match lookup r with
        | Some {receiver = None; _} -> m
        | Some {receiver = Some _; _} | None -> GlobRef.Map_env.add r (derive r) m )
      GlobRef.Map_env.empty callees

(* A method's call is still written as its function's would be, against the
   conventions of a callee generated nowhere, and printed on its receiver
   without the variables the receiver carries or the method dropped
   ({!dropped_positions}). *)
let plan ?omitted ?(instances = 0) ?higher_kinded ?kept ?reachable ?relaxed ?phantom_prefix callee
    ~scheme =
  match lookup callee with
  | Some ({receiver = None; _} as abi) -> abi
  | Some {receiver = Some _; _} | None ->
    let derive () =
      foreign ?omitted ?higher_kinded ?kept ?reachable ?relaxed ?phantom_prefix ~callee ~scheme ()
    in
    let emitting = match Common.get_phase () with Common.Emit _ -> true | Common.Plan -> false in
    let base =
      match GlobRef.Map_env.find_opt callee !foreign_plans with
      | Some base ->
        if emitting then foreign_tally := {!foreign_tally with found = !foreign_tally.found + 1};
        if Probe.checking () && not (same_head base (derive ())) then
          Probe.violation "callable ABI"
            Pp.(str "the foreign plan of " ++ GlobRef.print callee ++ str " differs from the one planned");
        base
      | None ->
        if emitting then begin
          foreign_tally := {!foreign_tally with derived = !foreign_tally.derived + 1};
          Probe.violation "callable ABI"
            Pp.(str "no plan was made for " ++ GlobRef.print callee ++ str " before bodies were generated")
        end;
        derive ()
    in
    with_dictionaries instances base

let report_foreign () =
  Printf.sprintf "foreign callable plans: %d planned; emission found %d, derived %d"
    (GlobRef.Map_env.cardinal !foreign_plans) !foreign_tally.found !foreign_tally.derived

let dropped_positions r =
  match lookup r with
  | Some {receiver = Some {dropped; _}; _} -> List.map (fun v -> Scheme.Var.ordinal v - 1) dropped
  | _ -> []

let method_params r =
  match lookup r with
  | Some {receiver = Some {params; _}; _} -> Some params
  | _ -> None
