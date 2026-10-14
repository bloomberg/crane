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
  params : Minicpp.cpp_type list;
}

type t = {
  callee : GlobRef.t;
  head : template_parameter list;
  deduced_callables : Param_pos.orig Param_pos.pos list;
  receiver : receiver option;
  phase : Common.phase;
}

let callee abi = abi.callee
let template_head abi = abi.head
let receiver abi = abi.receiver

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

let of_head ?(phantom_prefix = 0) ?relaxed ?renumber ?(deduced_callables = []) ?receiver ~callee
    ~scheme temps =
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
    phase = Common.get_phase () }

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
  let receiver_key r = (List.map Scheme.Var.ordinal r.dropped, r.params) in
  List.equal (fun p q -> key p = key q) a.head b.head
  && List.equal Param_pos.equal a.deduced_callables b.deduced_callables
  && Option.equal ( = ) (Option.map receiver_key a.receiver) (Option.map receiver_key b.receiver)

let equal a b = GlobRef.UserOrd.equal a.callee b.callee && same_head a b

let plans : t GlobRef.Map_env.t ref = ref GlobRef.Map_env.empty
let frozen = ref false
let open_for_planning () = frozen := false
let freeze () = frozen := true

let () =
  Table.register_census "callable ABI plans" (fun () -> GlobRef.Map_env.cardinal !plans)
let () =
  State.on_reset State.Extraction (fun () ->
      plans := GlobRef.Map_env.empty;
      frozen := false )

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
  | Common.Discover -> "in discovery"
  | Common.Emit Common.Impl -> "emitting the implementation"
  | Common.Emit Common.Intf -> "emitting the interface"

let record abi =
  List.iter
    (fun problem ->
      Probe.violation "callable ABI"
        Pp.(str "the plan of " ++ GlobRef.print abi.callee ++ str ": " ++ str problem) )
    (validate abi);
  match GlobRef.Map_env.find_opt abi.callee !plans with
  | Some old when same_head old abi -> ()
  | Some old ->
    Probe.violation "callable ABI"
      Pp.(
        str "the declaration of " ++ GlobRef.print abi.callee
        ++ str " was generated with the head <" ++ str (describe abi)
        ++ str "> where its plan, recorded " ++ str (phase_name old.phase)
        ++ str ", says <" ++ str (describe old) ++ str ">; generated "
        ++ str (phase_name abi.phase) )
  | None when !frozen ->
    Probe.violation "callable ABI"
      Pp.(
        str "the declaration of " ++ GlobRef.print abi.callee
        ++ str " was generated with no plan: planning the callables missed it" )
  | None -> plans := GlobRef.Map_env.add abi.callee abi !plans

let lookup r = GlobRef.Map_env.find_opt r !plans

let assumed : Param_pos.orig Param_pos.pos list Ref.User.Map.t ref =
  State.cell State.Extraction Ref.User.Map.empty

let assume l = assumed := List.fold_left (fun m (r, ps) -> Ref.User.Map.add r ps m) Ref.User.Map.empty l

let deduces_callable r pos =
  match lookup r with
  | Some abi -> deduces_callable_at abi pos
  | None -> List.exists (Param_pos.equal pos) (Option.default [] (Ref.User.Map.find_opt r !assumed))

let foreign ?(instances = 0) ?(higher_kinded = fun _ -> false) ?(kept = fun _ -> true)
    ?(reachable = max_int) ?(relaxed = fun _ -> false) ?(phantom_prefix = 0) ~callee ~scheme () =
  let dictionaries =
    List.init instances (fun k ->
        (Minicpp.TTtypename, Common.tc_instance_id k, From_instance k) )
  in
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
      (dictionaries @ variables)
  in
  { callee;
    head = mark_phantoms phantom_prefix head;
    deduced_callables = [];
    receiver = None;
    phase = Common.get_phase () }

(* A method's call is still written as its function's would be, against the
   conventions of a callee generated nowhere, and printed on its receiver
   without the variables the receiver carries or the method dropped
   ({!dropped_positions}). *)
let plan ?instances ?higher_kinded ?kept ?reachable ?relaxed ?phantom_prefix callee ~scheme =
  match lookup callee with
  | Some ({receiver = None; _} as abi) -> abi
  | Some {receiver = Some _; _} | None ->
    foreign ?instances ?higher_kinded ?kept ?reachable ?relaxed ?phantom_prefix ~callee ~scheme ()

let dropped_positions r =
  match lookup r with
  | Some {receiver = Some {dropped; _}; _} -> List.map (fun v -> Scheme.Var.ordinal v - 1) dropped
  | _ -> []

let method_params r =
  match lookup r with
  | Some {receiver = Some {params; _}; _} -> Some params
  | _ -> None
