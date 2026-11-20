(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** See [mapping_plan.mli]. *)

open Names
open Mapping_descriptor

type type_expr =
  | Name of string
  | Apply of string * argument list
  | Parameter of int
  | Pointer of type_expr
  | Const of type_expr
  | Verbatim of string

and argument = Type of type_expr | Value of string

type view = {
  requirement : observation_requirement;
  test : string;
  fields : (int * projection) list;
}

type constructor = { source : Names.constructor; build : string; view : view option }

type interface = Abstract | Algebraic of constructor list

type t = {
  instance : GlobRef.t;
  head : GlobRef.t;
  canonical : type_expr;
  components : (string * int) list;
  copy : copy_model;
  access : access_model;
  value_model : value_model;
  lifetime : lifetime_model;
  release : release_plan;
  interface : interface;
  headers : string list;
}

let is_type_head g = Mapping_discovery.has_type_mapping g

let inductive_of = function
  | GlobRef.ConstructRef (ip, _) -> Some (GlobRef.IndRef ip)
  | _ -> None

let is_mapped g =
  is_type_head g || match inductive_of g with Some i -> is_type_head i | None -> false

(** {1 Diagnostics} *)

let fail_head head detail =
  CErrors.user_err
    Pp.(hov 0 (str "Crane: the typed mapping of" ++ spc () ++ Printer.pr_global head ++ str ":" ++ spc () ++ detail))

let fail_plan p detail =
  CErrors.user_err
    Pp.(
      hov 0
        ( str "Crane: the typed mapping" ++ spc () ++ Printer.pr_global p.instance ++ spc () ++ str "of"
        ++ spc () ++ Printer.pr_global p.head ++ str ":" ++ spc () ++ detail ))

(** {1 Compilation} *)

let parameter_id k = Id.of_string (Printf.sprintf "crane_mapped_parameter_%d" k)

(* The head applied to one fresh variable per binder of its arity, in an
   environment declaring them. *)
let generic_query env sigma g =
  let sigma, head = Evd.fresh_global env sigma g in
  let rec go env k ids ty =
    match EConstr.kind sigma (Reductionops.whd_all env sigma ty) with
    | Constr.Prod (na, dom, codom) ->
      let id = parameter_id k in
      let decl = Context.Named.Declaration.LocalAssum (Context.make_annot id na.Context.binder_relevance, dom) in
      go (EConstr.push_named decl env) (k + 1) (id :: ids) (EConstr.Vars.subst1 (EConstr.mkVar id) codom)
    | _ -> (env, List.rev ids)
  in
  let env, ids = go env 0 [] (Retyping.get_type_of env sigma head) in
  (env, sigma, EConstr.mkApp (head, Array.of_list (List.map EConstr.mkVar ids)), ids)

let index_of id ids =
  let rec go k = function [] -> None | x :: r -> if Id.equal x id then Some k else go (k + 1) r in
  go 0 ids

(* The parameter a closed Rocq type names, if it is one. *)
let parameter_of_type ids c = match Constr.kind c with Constr.Var id -> index_of id ids | _ -> None

(* The parameter field [n] of the constructor [d] is declared at, if it is
   declared at one. *)
let parameter_of_field env (d : declaration) n =
  match d.reference with
  | GlobRef.ConstructRef (((mind, _), _) as k) -> (
    let mib = Environ.lookup_mind mind env in
    let nparams = mib.Declarations.mind_nparams in
    let ty, _ = Typeops.type_of_global_in_context env (GlobRef.ConstructRef k) in
    let decls = List.rev (fst (Term.decompose_prod_decls ty)) in
    let p = nparams + n in
    match List.nth_opt decls p with
    | Some decl -> (
      match Constr.kind (Context.Rel.Declaration.get_type decl) with
      | Constr.Rel j when p - j >= 0 && p - j < nparams -> Some (p - j)
      | _ -> None )
    | None -> None )
  | _ -> None

let starts_at text i s =
  let k = String.length s in
  i + k <= String.length text && String.sub text i k = s

(* [%stored(x)] spelled as the [%tN] of the parameter [x] is. *)
let compile_template ~fail ~stored text =
  let n = String.length text in
  let b = Buffer.create n in
  let rec go i =
    if i >= n then ()
    else if starts_at text i "%stored(" then (
      let close = try String.index_from text i ')' with Not_found -> n in
      let start = i + String.length "%stored(" in
      let name = String.trim (String.sub text start (max 0 (close - start))) in
      Buffer.add_string b (Printf.sprintf "%%t%d" (stored name));
      go (close + 1) )
    else if starts_at text i "%tmp" && i + 4 < n && text.[i + 4] >= '0' && text.[i + 4] <= '9' then
      fail
        (Pp.strbrk
           "a template uses a fresh-name hole (%tmpN), which constructor and \
            match templates do not support yet; bind the value with a \
            constructor view instead.")
    else (
      Buffer.add_char b text.[i];
      go (i + 1) )
  in
  go 0;
  Buffer.contents b

let compile env (r : Mapping_discovery.resolved_type_mapping) head ids =
  let m = r.type_mapping in
  let fail detail = fail_head head Pp.(str "the instance" ++ spc () ++ Printer.pr_global r.type_instance ++ spc () ++ detail) in
  let unsupported what c =
    fail
      Pp.(
        strbrk what ++ spc () ++ Printer.pr_constr_env env (Evd.from_env env) c ++ str ","
        ++ spc ()
        ++ strbrk
             "which is not one of the parameters of the mapped type; a \
              component's type must be a parameter, so that its stored C++ \
              type is the one Crane chooses for that type argument.")
  in
  let components =
    List.map
      (fun c ->
        let i =
          match c.component_type with
          | Known_type t -> (
            match parameter_of_type ids t with
            | Some i -> i
            | None -> unsupported ("gives component \"" ^ c.component_name ^ "\" the type") t )
          | Field_type (d, n) -> (
            match parameter_of_field env d n with
            | Some i -> i
            | None ->
              fail
                (Pp.strbrk
                   (Printf.sprintf
                      "gives component \"%s\" the type of field %d of a constructor, which is not one \
                       of the parameters of the mapped type."
                      c.component_name n)) )
        in
        (c.component_name, i))
      m.type_components
  in
  let stored x =
    match List.assoc_opt x components with
    | Some i -> i
    | None -> fail (Pp.strbrk (Printf.sprintf "names the undeclared component \"%s\"." x))
  in
  let rec type_expr = function
    | Cpp.Name s -> Name s
    | Cpp.Apply (s, args) ->
      Apply (s, List.map (function Cpp.Type_arg t -> Type (type_expr t) | Cpp.Value_arg v -> Value v) args)
    | Cpp.Source_type t -> (
      match parameter_of_type ids t with Some i -> Parameter i | None -> unsupported "names the source type" t )
    | Cpp.Stored_component x -> Parameter (stored x)
    | Cpp.Pointer t -> Pointer (type_expr t)
    | Cpp.Const t -> Const (type_expr t)
    | Cpp.Unsafe_verbatim s -> Verbatim s
  in
  let template = compile_template ~fail ~stored in
  let interface =
    match m.type_interface with
    | Abstract_interface -> Abstract
    | Algebraic_interface ctors ->
      Algebraic
        (List.map
           (fun c ->
             let source =
               match c.ctor_source.reference with
               | GlobRef.ConstructRef k -> k
               | _ -> CErrors.anomaly Pp.(str "Crane: a validated constructor mapping names no constructor.")
             in
             let build =
               match c.ctor_build with
               | Expr e -> template e
               | With_body (i, b) -> "%result = " ^ template i ^ "; " ^ template b
             in
             let view =
               Option.map
                 (fun v ->
                   { requirement = v.view_requirement;
                     test = template v.case_test;
                     fields =
                       List.map
                         (fun (n, p) ->
                           ( n,
                             match p with
                             | Owned_projection e -> Owned_projection (template e)
                             | Canonical_borrow_projection e -> Canonical_borrow_projection (template e)
                             | Read_view_projection e -> Read_view_projection (template e) ))
                         v.case_fields })
                 c.ctor_view
             in
             {source; build; view})
           ctors)
  in
  { instance = r.type_instance;
    head;
    canonical = type_expr m.type_cpp;
    components;
    copy = m.type_copy;
    access = m.type_access;
    value_model = m.type_model;
    lifetime = m.type_lifetime;
    release = m.type_release;
    interface;
    headers = m.type_headers }

let plans : t GlobRef.Map.t ref = State.cell State.Extraction GlobRef.Map.empty

let find g =
  let head = match inductive_of g with Some i -> i | None -> g in
  match GlobRef.Map.find_opt head !plans with
  | Some p -> p
  | None ->
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let env, sigma, query, ids = generic_query env sigma head in
    let p =
      match Mapping_discovery.resolve_type_mapping env sigma query with
      | Some r -> compile env r head ids
      | None ->
        fail_head head
          (Pp.strbrk
             "no TypeMapping instance applies to every instantiation of its \
              parameters; an instance for one particular instantiation is not \
              supported yet.")
    in
    plans := GlobRef.Map.add head p !plans;
    p

(** {1 Queries} *)

let cpp_type (type p) plan (tys : p Cpp_ir.Type.t list) : p Cpp_ir.Type.t =
  let rec go : type_expr -> p Cpp_ir.Type.t = function
    | Name s -> External (s, [])
    | Apply (s, args) -> External (s, List.map (function Type t -> go t | Value v -> Cpp_ir.Type.External (v, [])) args)
    | Parameter i -> ( match List.nth_opt tys i with Some t -> t | None -> Any )
    | Pointer t -> Pointer (go t)
    | Const t -> Const (go t)
    | Verbatim s -> External (s, [])
  in
  go plan.canonical

let type_text plan =
  let rec go = function
    | Name s | Verbatim s -> s
    | Apply (s, args) ->
      s ^ "<" ^ String.concat ", " (List.map (function Type t -> go t | Value v -> v) args) ^ ">"
    | Parameter i -> Printf.sprintf "%%t%d" i
    | Pointer t -> go t ^ "*"
    | Const t -> "const " ^ go t
  in
  go plan.canonical

let constructor_count ((mind, i) : inductive) =
  let mib = Global.lookup_mind mind in
  Array.length mib.Declarations.mind_packets.(i).Declarations.mind_consnames

let abstract_use p what =
  fail_plan p
    Pp.(
      strbrk "the type is declared abstract (AbstractInterface), so source code cannot "
      ++ str what ++ str " it;" ++ spc ()
      ++ strbrk "an abstract mapped type is used only through mapped operations.")

let constructor_mapping p k =
  match p.interface with
  | Abstract -> abstract_use p "construct or match on"
  | Algebraic ctors -> (
    match List.find_opt (fun c -> Construct.CanOrd.equal c.source k) ctors with
    | Some c -> c
    | None ->
      fail_plan p
        Pp.(
          str "the constructor" ++ spc ()
          ++ Printer.pr_global (GlobRef.ConstructRef k)
          ++ spc ()
          ++ strbrk "has no constructor mapping in its AlgebraicInterface, but source code uses it." ) )

let constructor_template k =
  let p = find (GlobRef.ConstructRef k) in
  ( match p.interface with Abstract -> abstract_use p "construct" | Algebraic _ -> () );
  (constructor_mapping p k).build

let constructor_templates ip =
  List.init (constructor_count ip) (fun j -> constructor_template (ip, j + 1))

let match_template ip =
  let p = find (GlobRef.IndRef ip) in
  ( match p.interface with Abstract -> abstract_use p "match on" | Algebraic _ -> () );
  let n = constructor_count ip in
  let branch i =
    let k = (ip, i + 1) in
    let c = constructor_mapping p k in
    match c.view with
    | None ->
      fail_plan p
        Pp.(
          str "the constructor" ++ spc ()
          ++ Printer.pr_global (GlobRef.ConstructRef k)
          ++ spc () ++ strbrk "has no constructor view (ctor_view), but source code matches on it.")
    | Some v ->
      let binds =
        List.map
          (fun (j, proj) ->
            match proj with
            | Canonical_borrow_projection e -> Printf.sprintf "const auto& %%b%da%d = %s; " i j e
            | Owned_projection e -> Printf.sprintf "auto %%b%da%d = %s; " i j e
            | Read_view_projection _ ->
              fail_plan p
                (Pp.strbrk
                   "a ReadViewProjection is not supported yet; use \
                    CanonicalBorrowProjection or OwnedProjection."))
          (List.sort (fun (a, _) (b, _) -> compare a b) v.fields)
      in
      (v.test, String.concat "" binds ^ Printf.sprintf "%%br%d" i)
  in
  let branches = List.init n branch in
  match branches with
  | [] -> ""
  | [(_, body)] -> body
  | _ ->
    let rec chain i = function
      | [] -> ""
      | [(_, body)] -> " else { " ^ body ^ " }"
      | (test, body) :: rest ->
        (if i = 0 then "" else " else ") ^ "if (" ^ test ^ ") { " ^ body ^ " }" ^ chain (i + 1) rest
    in
    chain 0 branches

let component_holds p ~argument x =
  match List.assoc_opt x p.components with Some i -> argument i | None -> false

let copies_cheaply p ~argument =
  match p.copy with
  | Bit_copy -> true
  | Copy_components names -> List.for_all (component_holds p ~argument) names
  | Retain_identity | Duplicate_value | Unknown_copy -> false

let read_style_by_value p ~argument = function
  | Read_by_value -> true
  | Read_by_const_reference -> false
  | Read_by_components names -> List.for_all (component_holds p ~argument) names

let read_by_value p ~argument =
  match p.access with
  | Read_only_value s | Mutable_value s -> read_style_by_value p ~argument s
  | Read_only_handle h | Mutable_handle h -> h = Handle_by_value
  | Explicit_access {explicit_read; _} -> explicit_read = Canonical_by_value

let headers g = if is_mapped g then (find g).headers else []

let instantiated : GlobRef.Set.t ref = State.cell State.Extraction GlobRef.Set.empty

let note_instantiated g = instantiated := GlobRef.Set.add g !instantiated

let instantiated_headers () = GlobRef.Set.fold (fun g acc -> headers g @ acc) !instantiated []
