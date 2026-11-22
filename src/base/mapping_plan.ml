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
  field_types : (int * string) list;
  field_heads : (int * GlobRef.t) list;
}

type constructor = { source : Names.constructor; build : string; view : view option }

type interface = Abstract | Algebraic of constructor list

type view_kind = Read_view | Write_view

type escape = Materialise of string | Borrow_only

type view_plan = {
  view_type : type_expr;
  from_canonical : string;
  escape : escape;
  view_headers : string list;
}

type views = {
  read : view_plan option;
  write : view_plan option;
  read_from_write : string option;
}

type numerals = {
  cases : (int * numeral_action) list;
  emitter : numeral_emitter;
  converters : GlobRef.t list;
}

type t = {
  instance : GlobRef.t;
  head : GlobRef.t;
  canonical : type_expr;
  components : (string * int) list;
  component_binders : (string * int) list;
  copy : copy_model;
  access : access_model;
  value_model : value_model;
  lifetime : lifetime_model;
  release : release_plan;
  interface : interface;
  views : views;
  headers : string list;
  numerals : numerals option;
}

let is_type_head g = Mapping_discovery.has_type_mapping g

let mapped_prim_string () =
  let name = "strings.pstring.type" in
  if Rocqlib.has_ref name then
    let g = Rocqlib.lib_ref name in
    if is_type_head g then Some g else None
  else None

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
let rec generic_query env sigma g =
  let sigma, head = Evd.fresh_global env sigma g in
  let rec go env k ids ty =
    match EConstr.kind sigma (Reductionops.whd_all env sigma ty) with
    | Constr.Prod (na, dom, codom) ->
      let id = parameter_id k in
      let decl = Context.Named.Declaration.LocalAssum (Context.make_annot id na.Context.binder_relevance, dom) in
      go (EConstr.push_named decl env) (k + 1) ((id, is_arity env sigma dom) :: ids)
        (EConstr.Vars.subst1 (EConstr.mkVar id) codom)
    | _ -> (env, List.rev ids)
  in
  let env, binders = go env 0 [] (Retyping.get_type_of env sigma head) in
  let ids = List.map fst binders in
  (env, sigma, EConstr.mkApp (head, Array.of_list (List.map EConstr.mkVar ids)), ids, List.map snd binders)

(* Whether a binder of type [t] is a type (or type family) parameter: a
   use's C++ type arguments are those of its type parameters only, an
   instance or a value parameter taking no position among them. *)
and is_arity env sigma t =
  let rec go env t =
    match EConstr.kind sigma (Reductionops.whd_all env sigma t) with
    | Constr.Prod (x, a, c) -> go (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, a)) env) c
    | Constr.Sort _ -> true
    | _ -> false
  in
  go env t

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

(* The inductive the type of field [n] of the constructor [d] is, when it is
   another inductive applied to no argument. *)
let other_inductive_field env (d : declaration) n =
  match d.reference with
  | GlobRef.ConstructRef (((mind, _) as ind, _) as k) -> (
    let mib = Environ.lookup_mind mind env in
    let ty, _ = Typeops.type_of_global_in_context env (GlobRef.ConstructRef k) in
    let decls = List.rev (fst (Term.decompose_prod_decls ty)) in
    match List.nth_opt decls (mib.Declarations.mind_nparams + n) with
    | Some decl -> (
      match Constr.kind (Context.Rel.Declaration.get_type decl) with
      | Constr.Ind (ind', _) when not (Ind.CanOrd.equal ind ind') -> Some (GlobRef.IndRef ind')
      | _ -> None )
    | None -> None )
  | _ -> None

(* Whether field [n] of the constructor [d] is a recursive occurrence of its
   inductive, applied to the inductive's parameters in order. *)
let recursive_field env (d : declaration) n =
  match d.reference with
  | GlobRef.ConstructRef (((mind, _) as ind, _) as k) -> (
    let mib = Environ.lookup_mind mind env in
    let nparams = mib.Declarations.mind_nparams in
    let ty, _ = Typeops.type_of_global_in_context env (GlobRef.ConstructRef k) in
    let decls = List.rev (fst (Term.decompose_prod_decls ty)) in
    let p = nparams + n in
    match List.nth_opt decls p with
    | Some decl -> (
      let head, args = Constr.decompose_app_list (Context.Rel.Declaration.get_type decl) in
      match Constr.kind head with
      | Constr.Ind (ind', _) when Ind.CanOrd.equal ind ind' && List.length args = nparams ->
        List.for_all Fun.id
          (List.mapi (fun i a -> match Constr.kind a with Constr.Rel j -> p - j = i | _ -> false) args)
      | _ -> false )
    | None -> false )
  | _ -> false

let starts_at text i s =
  let k = String.length s in
  i + k <= String.length text && String.sub text i k = s

(* [%stored(x)] spelled as the [%tN] of the parameter [x] is, and each hole
   [%h] of [renamed] as the text [renamed] gives it. *)
let compile_template ?(renamed = []) ~fail ~stored text =
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
    else
      match List.find_opt (fun (h, _) -> starts_at text i h) renamed with
      | Some (h, r) ->
        Buffer.add_string b r;
        go (i + String.length h)
      | None ->
    if starts_at text i "%tmp" && i + 4 < n && text.[i + 4] >= '0' && text.[i + 4] <= '9' then
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

(* A type of the plan in the legacy type-template vocabulary. *)
let rec text_of_type_expr = function
  | Name s | Verbatim s -> s
  | Apply (s, args) ->
    s ^ "<" ^ String.concat ", " (List.map (function Type t -> text_of_type_expr t | Value v -> v) args) ^ ">"
  | Parameter i -> Printf.sprintf "%%t%d" i
  | Pointer t -> text_of_type_expr t ^ "*"
  | Const t -> "const " ^ text_of_type_expr t

let compile env (r : Mapping_discovery.resolved_type_mapping) head ids kinds =
  let m = r.type_mapping in
  (* The position of binder [i] among the type arguments of a use. *)
  let position i = List.length (List.filter Fun.id (List.filteri (fun j _ -> j < i) kinds)) in
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
    | Some i -> position i
    | None -> fail (Pp.strbrk (Printf.sprintf "names the undeclared component \"%s\"." x))
  in
  let rec type_expr = function
    | Cpp.Name s -> Name s
    | Cpp.Apply (s, args) ->
      Apply (s, List.map (function Cpp.Type_arg t -> Type (type_expr t) | Cpp.Value_arg v -> Value v) args)
    | Cpp.Source_type t -> (
      match parameter_of_type ids t with
      | Some i -> Parameter (position i)
      | None -> unsupported "names the source type" t )
    | Cpp.Stored_component x -> Parameter (stored x)
    | Cpp.Pointer t -> Pointer (type_expr t)
    | Cpp.Const t -> Const (type_expr t)
    | Cpp.Unsafe_verbatim s -> Verbatim s
  in
  let template = compile_template ~fail ~stored in
  (* A view's conversions are term templates of one value argument: the
     canonical value ([%value]) or the view ([%view]) is its [%a0]. *)
  let construction ~hole = function
    | Expr e -> compile_template ~renamed:[(hole, "%a0")] ~fail ~stored e
    | With_body _ ->
      fail (Pp.strbrk "materialises a view with a WithBody construction, which is not supported yet; use Expr.")
  in
  let view_plan (v : view_spec) =
    { view_type = type_expr v.view_cpp;
      from_canonical = construction ~hole:"%value" (Expr v.view_from_canonical);
      escape =
        ( match v.view_escape with
        | Materialise_view k -> Materialise (construction ~hole:"%view" k)
        | Borrow_only -> Borrow_only );
      view_headers = v.view_headers }
  in
  let views =
    match m.type_views with
    | No_views -> {read = None; write = None; read_from_write = None}
    | Read_views r -> {read = Some (view_plan r); write = None; read_from_write = None}
    | Read_write_views (r, w, conv) ->
      { read = Some (view_plan r);
        write = Some (view_plan w);
        read_from_write = Some (construction ~hole:"%view" (Expr conv)) }
  in
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
             (* A field declared at a type parameter is spelled as that
                parameter's [%tN]; a recursive field as the matched value's
                type, [%ty], which is the canonical type at the instantiation
                the value is read at (an erased one where it is boxed). *)
             let field_type n =
               match parameter_of_field env c.ctor_source n with
               | Some i -> Some (Printf.sprintf "%%t%d" (position i))
               | None -> if recursive_field env c.ctor_source n then Some "%ty" else None
             in
             let view =
               Option.map
                 (fun v ->
                   { requirement = v.view_requirement;
                     test = template v.case_test;
                     fields =
                       List.map
                         (fun (n, p) ->
                           (* [%ret], the projection's result: the field's
                              type, where the plan spells it. *)
                           let template e =
                             let renamed =
                               match field_type n with
                               | Some t -> [("%ret", t)]
                               | None -> []
                             in
                             compile_template ~renamed ~fail ~stored e
                           in
                           ( n,
                             match p with
                             | Owned_projection e -> Owned_projection (template e)
                             | Canonical_borrow_projection e -> Canonical_borrow_projection (template e)
                             | Read_view_projection e -> Read_view_projection (template e) ))
                         v.case_fields;
                     field_types =
                       List.filter_map (fun (n, _) -> Option.map (fun t -> (n, t)) (field_type n)) v.case_fields;
                     field_heads =
                       List.filter_map
                         (fun (n, _) -> Option.map (fun g -> (n, g)) (other_inductive_field env c.ctor_source n))
                         v.case_fields })
                 c.ctor_view
             in
             {source; build; view})
           ctors)
  in
  let numerals =
    Option.map
      (fun (s : numeral_spec) ->
        { cases =
            List.filter_map
              (fun c ->
                match c.numeral_constructor.reference with
                | GlobRef.ConstructRef (_, j) -> Some (j, c.numeral_action)
                | _ -> None)
              s.numeral_cases;
          emitter = s.numeral_emitter;
          converters = List.map (fun (d : declaration) -> d.reference) s.numeral_converters })
      m.type_numerals
  in
  { instance = r.type_instance;
    numerals;
    head;
    canonical = type_expr m.type_cpp;
    components = List.map (fun (x, i) -> (x, position i)) components;
    component_binders = components;
    copy = m.type_copy;
    access = m.type_access;
    value_model = m.type_model;
    lifetime = m.type_lifetime;
    release = m.type_release;
    interface;
    views;
    headers =
      m.type_headers
      @ (match m.type_views with
        | No_views -> []
        | Read_views r -> r.view_headers
        | Read_write_views (r, w, _) -> r.view_headers @ w.view_headers)
      (* A view conversion may read its component types back from a value
         ({!Cpp_passes.View_args}). *)
      @
      let names_component text =
        let n = String.length text in
        let rec at i = i + 2 < n && ((text.[i] = '%' && text.[i + 1] = 't') || at (i + 1)) in
        at 0
      in
      if List.exists (fun v -> names_component v.from_canonical) (List.filter_map Fun.id [views.read; views.write])
      then ["template_argument.h"]
      else [] }

let plans : t GlobRef.Map.t ref = State.cell State.Extraction GlobRef.Map.empty

let compiled () = GlobRef.Map.fold (fun _ p acc -> p :: acc) !plans []

let duplicates_name s =
  GlobRef.Map.exists
    (fun _ p ->
      (match p.canonical with Name n | Apply (n, _) | Verbatim n -> String.equal n s | _ -> false)
      && match p.copy with Bit_copy | Copy_components _ -> false | Retain_identity | Duplicate_value | Unknown_copy -> true)
    !plans

let numeral_converters head =
  try
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let env, sigma, query, _, _ = generic_query env sigma head in
    match Mapping_discovery.resolve_type_mapping env sigma query with
    | Some {type_mapping = {type_numerals = Some s; _}; _} -> List.map (fun (d : declaration) -> d.reference) s.numeral_converters
    | _ -> []
  with e when CErrors.noncritical e -> []

let find g =
  let head = match inductive_of g with Some i -> i | None -> g in
  match GlobRef.Map.find_opt head !plans with
  | Some p -> p
  | None ->
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let env, sigma, query, ids, kinds = generic_query env sigma head in
    let p =
      match Mapping_discovery.resolve_type_mapping env sigma query with
      | Some r -> compile env r head ids kinds
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

let instantiate (type p) (e : type_expr) (tys : p Cpp_ir.Type.t list) : p Cpp_ir.Type.t =
  let rec go : type_expr -> p Cpp_ir.Type.t = function
    | Name s -> External (s, [])
    | Apply (s, args) -> External (s, List.map (function Type t -> go t | Value v -> Cpp_ir.Type.External (v, [])) args)
    | Parameter i -> ( match List.nth_opt tys i with Some t -> t | None -> Any )
    | Pointer t -> Pointer (go t)
    | Const t -> Const (go t)
    | Verbatim s -> External (s, [])
  in
  go e

let cpp_type plan tys = instantiate plan.canonical tys

let view plan = function Read_view -> plan.views.read | Write_view -> plan.views.write

let has_view plan k = Option.has_some (view plan k)

let view_type plan k tys =
  match view plan k with
  | Some v -> instantiate v.view_type tys
  | None -> CErrors.anomaly Pp.(str "Crane: a view the typed mapping does not declare.")

(* The type arguments [ty], an instantiation of [e], gives the parameters
   [e] names, where it is one. *)
let match_instance (type p) (e : type_expr) (ty : p Cpp_ir.Type.t) : (int * p Cpp_ir.Type.t) list option =
  let rec go (e : type_expr) (t : p Cpp_ir.Type.t) acc =
    match (e, t) with
    | Parameter i, t -> Some ((i, t) :: acc)
    | Name s, External (s', []) | Verbatim s, External (s', []) when s = s' -> Some acc
    | Apply (s, args), External (s', ts) when s = s' && List.length args = List.length ts ->
      List.fold_left2
        (fun acc a t ->
          match (acc, a) with
          | None, _ -> None
          | Some acc, Type a -> go a t acc
          | Some acc, Value _ -> Some acc)
        (Some acc) args ts
    | Pointer e, Pointer t | Const e, Const t -> go e t acc
    | _ -> None
  in
  go e ty []

let view_arguments (type p) plan k (ty : p Cpp_ir.Type.t) : p Cpp_ir.Type.t list option =
  match view plan k with
  | None -> None
  | Some v -> (
    match match_instance v.view_type ty with
    | None -> None
    | Some found ->
      let n = List.fold_left (fun n (i, _) -> max n (i + 1)) 0 found in
      Some (List.init n (fun i -> match List.assoc_opt i found with Some t -> t | None -> Cpp_ir.Type.Any)) )

let type_text plan = text_of_type_expr plan.canonical

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

(* A structured binding of the scrutinee, when that is what the one
   constructor's view says: the canonical type is a [std::pair] (or
   [bsl::pair]) or a [std::tuple] with as many elements as the constructor
   has fields, and field [j] is borrowed as [std::get<j>(%scrut)] (a pair's
   as [%scrut.first], [%scrut.second]) -- what a structured
   binding of a tuple-like type binds its [j]-th name to.  The binding
   form lets an owned scrutinee be taken apart by value
   ({!Cpp_ir.Foreign_template.structured_binding}). *)
let tuple_binding p ((mind, i) as ip) n =
  let arity = (Global.lookup_mind mind).Declarations.mind_packets.(i).Declarations.mind_consnrealdecls.(0) in
  let tuple_like =
    match p.canonical with
    | Apply (("std::pair" | "bsl::pair"), args) -> List.length args = 2 && arity = 2
    | Apply ("std::tuple", args) -> List.length args = arity
    | _ -> false
  in
  if n <> 1 || arity = 0 || not tuple_like then None
  else
    match (constructor_mapping p (ip, 1)).view with
    | Some v
      when List.sort compare (List.map fst v.fields) = List.init arity Fun.id
           && List.for_all
                (fun (j, proj) ->
                  match proj with
                  | Canonical_borrow_projection e ->
                    String.equal e (Printf.sprintf "std::get<%d>(%%scrut)" j)
                    || (j = 0 && String.equal e "%scrut.first")
                    || (j = 1 && String.equal e "%scrut.second")
                  | Owned_projection _ | Read_view_projection _ -> false)
                v.fields ->
      Some
        (Printf.sprintf "const auto& [%s] = %%scrut; %%br0"
           (String.concat ", " (List.init arity (Printf.sprintf "%%b0a%d"))))
    | _ -> None

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
      let binder_type j =
        match List.assoc_opt j v.field_types with
        | Some t -> t
        | None -> (
          match List.assoc_opt j v.field_heads with
          | Some g when is_type_head g ->
            let t = type_text (find g) in
            if String.contains t '%' then "auto" else t
          | _ -> "auto" )
      in
      let binds =
        List.map
          (fun (j, proj) ->
            match proj with
            | Canonical_borrow_projection e -> Printf.sprintf "const %s& %%b%da%d = %s; " (binder_type j) i j e
            | Owned_projection e -> Printf.sprintf "%s %%b%da%d = %s; " (binder_type j) i j e
            | Read_view_projection _ ->
              fail_plan p
                (Pp.strbrk
                   "a ReadViewProjection is not supported yet; use \
                    CanonicalBorrowProjection or OwnedProjection."))
          (List.sort (fun (a, _) (b, _) -> compare a b) v.fields)
      in
      (v.test, String.concat "" binds ^ Printf.sprintf "%%br%d" i)
  in
  match tuple_binding p ip n with
  | Some t -> t
  | None ->
  (* The views are tested in the order the interface lists them, so the
     mapping decides which test needs no condition: the last. *)
  let listed =
    match p.interface with
    | Algebraic ctors ->
      List.filter_map
        (fun (c : constructor) -> if Ind.CanOrd.equal (fst c.source) ip then Some (snd c.source - 1) else None)
        ctors
    | Abstract -> []
  in
  let order = listed @ List.filter (fun i -> not (List.mem i listed)) (List.init n Fun.id) in
  let branches = List.map branch order in
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

type physical =
  | As_read
  | Physical_value
  | Physical_const_reference
  | Physical_mutable_reference
  | Physical_view of view_kind

let explicit_form = function
  | Some Canonical_by_value -> Physical_value
  | Some Canonical_by_const_reference -> Physical_const_reference
  | Some Canonical_by_mutable_reference -> Physical_mutable_reference
  | Some (Exact_parameter _) | None -> As_read

let write_through p =
  match p.access with
  | Mutable_value _ -> Physical_mutable_reference
  | Mutable_handle _ | Read_only_value _ | Read_only_handle _ -> As_read
  | Explicit_access {explicit_write; _} -> explicit_form explicit_write

let replace_form p =
  match p.access with
  | Mutable_value _ | Mutable_handle _ | Read_only_value _ | Read_only_handle _ -> Physical_mutable_reference
  | Explicit_access {explicit_replace = None; _} -> Physical_mutable_reference
  | Explicit_access {explicit_replace; _} -> explicit_form explicit_replace

let headers g = if is_mapped g then (find g).headers else []

let instantiated : GlobRef.Set.t ref = State.cell State.Extraction GlobRef.Set.empty

let note_instantiated g = instantiated := GlobRef.Set.add g !instantiated

let instantiated_headers () = GlobRef.Set.fold (fun g acc -> headers g @ acc) !instantiated []
