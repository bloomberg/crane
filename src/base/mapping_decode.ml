(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** See [mapping_decode.mli]. *)

open Names
open Mapping_descriptor

type ctx = { env : Environ.env; sigma : Evd.evar_map }

let registered name = Rocqlib.lib_ref_opt ("crane.mapping." ^ name)

let inductive_of key =
  match Rocqlib.lib_ref key with
  | GlobRef.IndRef ind -> ind
  | _ -> CErrors.anomaly Pp.(str "Crane: " ++ str key ++ str " is not an inductive.")

let descriptor_inductive name = inductive_of ("crane.mapping." ^ name)

let fail cx ~what c =
  CErrors.user_err
    Pp.(
      str "Crane: cannot read the mapping descriptor: expected "
      ++ str what
      ++ str ", found"
      ++ spc ()
      ++ Printer.pr_econstr_env cx.env cx.sigma c
      ++ str "."
      ++ spc ()
      ++ strbrk
           "A descriptor must reduce to constructors and records of \
            Crane.Mapping.Descriptor; an opaque or axiomatic subterm cannot \
            be read." )

(* [c] in weak head normal form, as a constructor of [ind]: its index (from
   1) and its arguments after the inductive's parameters. *)
let constructor cx ~what ind c =
  let c = Reductionops.whd_all cx.env cx.sigma c in
  let head, args = EConstr.decompose_app_list cx.sigma c in
  match EConstr.kind cx.sigma head with
  | Constr.Construct ((ind', i), _) when Ind.CanOrd.equal ind ind' ->
    let mib = Environ.lookup_mind (fst ind) cx.env in
    (i, CList.skipn mib.Declarations.mind_nparams args)
  | _ -> fail cx ~what c

let constructor_of cx name c = constructor cx ~what:name (descriptor_inductive name) c

let string cx c =
  let c = Reductionops.whd_all cx.env cx.sigma c in
  match EConstr.kind cx.sigma c with
  | Constr.String s -> Pstring.to_string s
  | _ -> fail cx ~what:"a primitive string literal" c

let rec nat cx c =
  match constructor cx ~what:"a nat" (inductive_of "num.nat.type") c with
  | 1, [] -> 0
  | 2, [n] -> 1 + nat cx n
  | _ -> fail cx ~what:"a nat" c

let rec list cx f c =
  match constructor cx ~what:"a list" (inductive_of "core.list.type") c with
  | 1, [] -> []
  | 2, [x; xs] ->
    let x = f cx x in
    x :: list cx f xs
  | _ -> fail cx ~what:"a list" c

let option cx f c =
  match constructor cx ~what:"an option" (inductive_of "core.option.type") c with
  | 1, [x] -> Some (f cx x)
  | 2, [] -> None
  | _ -> fail cx ~what:"an option" c

let pair cx f g c =
  match constructor cx ~what:"a pair" (inductive_of "core.prod.type") c with
  | 1, [a; b] ->
    let a = f cx a in
    (a, g cx b)
  | _ -> fail cx ~what:"a pair" c

let closed cx c = EConstr.to_constr cx.sigma c

(* The argument of [Ref] is read as written: it is not reduced, so a
   declaration keeps its identity even when it has a body. *)
let rec reference_term cx c =
  match EConstr.kind cx.sigma c with
  | Constr.Cast (c, _, _) -> reference_term cx c
  | _ -> (
    let head, args = EConstr.decompose_app_list cx.sigma c in
    let reference =
      match EConstr.kind cx.sigma head with
      | Constr.Const (k, _) -> Some (GlobRef.ConstRef k)
      | Constr.Ind (i, _) -> Some (GlobRef.IndRef i)
      | Constr.Construct (k, _) -> Some (GlobRef.ConstructRef k)
      | Constr.Var id -> Some (GlobRef.VarRef id)
      | _ -> None
    in
    match reference with
    | Some reference -> Some { reference; parameters = List.map (closed cx) args }
    | None -> None )

let declaration_argument cx c =
  match constructor_of cx "Declaration" c with
  | 1, [_ty; d] -> (
    match reference_term cx d with
    | Some decl -> decl
    | None ->
      CErrors.user_err
        Pp.(
          str "Crane: Ref expects a declaration (a constant, inductive or \
               constructor, possibly applied to parameters), found"
          ++ spc ()
          ++ Printer.pr_econstr_env cx.env cx.sigma d
          ++ str "." ) )
  | _ -> fail cx ~what:"a Declaration" c

let declaration = declaration_argument

let rec type_expr cx c : Cpp.type_expr =
  match constructor_of cx "TypeExpr" c with
  | 1, [s] -> Cpp.Name (string cx s)
  | 2, [s; args] ->
    let s = string cx s in
    Cpp.Apply (s, list cx type_argument args)
  | 3, [t] -> Cpp.Source_type (closed cx t)
  | 4, [s] -> Cpp.Stored_component (string cx s)
  | 5, [t] -> Cpp.Pointer (type_expr cx t)
  | 6, [t] -> Cpp.Const (type_expr cx t)
  | 7, [s] -> Cpp.Unsafe_verbatim (string cx s)
  | _ -> fail cx ~what:"a TypeExpr" c

and type_argument cx c : Cpp.type_argument =
  match constructor_of cx "TypeArgument" c with
  | 1, [t] -> Cpp.Type_arg (type_expr cx t)
  | 2, [s] -> Cpp.Value_arg (string cx s)
  | _ -> fail cx ~what:"a TypeArgument" c

let construction cx c =
  match constructor_of cx "Construction" c with
  | 1, [s] -> Expr (string cx s)
  | 2, [i; b] ->
    let i = string cx i in
    With_body (i, string cx b)
  | _ -> fail cx ~what:"a Construction" c

let strings cx c = list cx string c

let copy_model cx c =
  match constructor_of cx "CopyModel" c with
  | 1, [] -> Bit_copy
  | 2, [] -> Retain_identity
  | 3, [] -> Duplicate_value
  | 4, [l] -> Copy_components (strings cx l)
  | 5, [] -> Unknown_copy
  | _ -> fail cx ~what:"a CopyModel" c

let read_style cx c =
  match constructor_of cx "ReadStyle" c with
  | 1, [] -> Read_by_value
  | 2, [] -> Read_by_const_reference
  | 3, [l] -> Read_by_components (strings cx l)
  | _ -> fail cx ~what:"a ReadStyle" c

let handle_pass cx c =
  match constructor_of cx "HandlePass" c with
  | 1, [] -> Handle_by_value
  | 2, [] -> Handle_by_const_reference
  | _ -> fail cx ~what:"a HandlePass" c

let physical_parameter cx c =
  match constructor_of cx "PhysicalParameter" c with
  | 1, [] -> Canonical_by_value
  | 2, [] -> Canonical_by_const_reference
  | 3, [] -> Canonical_by_mutable_reference
  | 4, [s] -> Exact_parameter (string cx s)
  | _ -> fail cx ~what:"a PhysicalParameter" c

let explicit_access_spec cx c =
  match constructor_of cx "ExplicitAccessSpec" c with
  | 1, [r; w; p] ->
    let explicit_read = physical_parameter cx r in
    let explicit_write = option cx physical_parameter w in
    let explicit_replace = option cx physical_parameter p in
    {explicit_read; explicit_write; explicit_replace}
  | _ -> fail cx ~what:"an ExplicitAccessSpec" c

let access_model cx c =
  match constructor_of cx "AccessModel" c with
  | 1, [r] -> Read_only_value (read_style cx r)
  | 2, [r] -> Mutable_value (read_style cx r)
  | 3, [h] -> Read_only_handle (handle_pass cx h)
  | 4, [h] -> Mutable_handle (handle_pass cx h)
  | 5, [s] -> Explicit_access (explicit_access_spec cx s)
  | _ -> fail cx ~what:"an AccessModel" c

let value_model cx c =
  match constructor_of cx "ValueModel" c with
  | 1, [] -> Structural
  | 2, [] -> Identity
  | 3, [] -> Unspecified
  | _ -> fail cx ~what:"a ValueModel" c

let lifetime_model cx c =
  match constructor_of cx "LifetimeModel" c with
  | 1, [] -> Native_raii
  | 2, [d] -> Region_owned (declaration cx d)
  | 3, [] -> Externally_owned
  | 4, [r; l] ->
    let r = declaration cx r in
    Manual_shared (r, declaration cx l)
  | _ -> fail cx ~what:"a LifetimeModel" c

let release_plan cx c =
  match constructor_of cx "ReleasePlan" c with
  | 1, [] -> Ordinary_release
  | 2, [s] -> Drain_with (string cx s)
  | _ -> fail cx ~what:"a ReleasePlan" c

let view_escape cx c =
  match constructor_of cx "ViewEscape" c with
  | 1, [k] -> Materialise_view (construction cx k)
  | 2, [] -> Borrow_only
  | _ -> fail cx ~what:"a ViewEscape" c

let view_spec view_mode cx c =
  match constructor_of cx "ViewSpec" c with
  | 1, [h; t; f; e] ->
    let view_headers = strings cx h in
    let view_cpp = type_expr cx t in
    let view_from_canonical = string cx f in
    let view_escape = view_escape cx e in
    {view_mode; view_headers; view_cpp; view_from_canonical; view_escape}
  | _ -> fail cx ~what:"a ViewSpec" c

let views cx c =
  match constructor_of cx "Views" c with
  | 1, [] -> No_views
  | 2, [r] -> Read_views (view_spec Read_only_view cx r)
  | 3, [r; w; s] ->
    let r = view_spec Read_only_view cx r in
    let w = view_spec Writable_view cx w in
    Read_write_views (r, w, string cx s)
  | _ -> fail cx ~what:"a Views" c

let component_type cx c =
  match constructor_of cx "ComponentType" c with
  | 1, [t] -> Known_type (closed cx t)
  | 2, [d; n] ->
    let d = declaration cx d in
    Field_type (d, nat cx n)
  | _ -> fail cx ~what:"a ComponentType" c

let component cx c =
  match constructor_of cx "Component" c with
  | 1, [n; t] ->
    let component_name = string cx n in
    {component_name; component_type = component_type cx t}
  | _ -> fail cx ~what:"a Component" c

let projection cx c =
  match constructor_of cx "Projection" c with
  | 1, [s] -> Owned_projection (string cx s)
  | 2, [s] -> Canonical_borrow_projection (string cx s)
  | 3, [s] -> Read_view_projection (string cx s)
  | _ -> fail cx ~what:"a Projection" c

let observation_requirement cx c =
  match constructor_of cx "ObservationRequirement" c with
  | 1, [] -> Preferred_observation
  | 2, [] -> Canonical_observation
  | _ -> fail cx ~what:"an ObservationRequirement" c

let constructor_view cx c =
  match constructor_of cx "ConstructorView" c with
  | 1, [r; t; fs] ->
    let view_requirement = observation_requirement cx r in
    let case_test = string cx t in
    let case_fields = list cx (fun cx p -> pair cx nat projection p) fs in
    {view_requirement; case_test; case_fields}
  | _ -> fail cx ~what:"a ConstructorView" c

let constructor_mapping cx c =
  match constructor_of cx "ConstructorMapping" c with
  | 1, [s; b; v] ->
    let ctor_source = declaration cx s in
    let ctor_build = construction cx b in
    let ctor_view = option cx constructor_view v in
    {ctor_source; ctor_build; ctor_view}
  | _ -> fail cx ~what:"a ConstructorMapping" c

let type_interface cx c =
  match constructor_of cx "TypeInterface" c with
  | 1, [] -> Abstract_interface
  | 2, [l] -> Algebraic_interface (list cx constructor_mapping l)
  | _ -> fail cx ~what:"a TypeInterface" c

let numeral_action cx c =
  match constructor_of cx "NumeralAction" c with
  | 1, [] -> Numeral_zero
  | 2, [] -> Numeral_one
  | 3, [n] -> Numeral_successor (nat cx n)
  | 4, [n] -> Numeral_double (nat cx n)
  | 5, [n] -> Numeral_double_plus_one (nat cx n)
  | 6, [n] -> Numeral_identity (nat cx n)
  | 7, [n] -> Numeral_negate (nat cx n)
  | _ -> fail cx ~what:"a NumeralAction" c

let numeral_case cx c =
  match constructor_of cx "NumeralCase" c with
  | 1, [d; a] ->
    let numeral_constructor = declaration cx d in
    {numeral_constructor; numeral_action = numeral_action cx a}
  | _ -> fail cx ~what:"a NumeralCase" c

let numeral_emitter cx c =
  match constructor_of cx "NumeralEmitter" c with
  | 1, [p; s] ->
    let p = string cx p in
    Integer_token (p, string cx s)
  | 2, [s] -> Decimal_constructor (string cx s)
  | _ -> fail cx ~what:"a NumeralEmitter" c

let numeral_spec cx c =
  match constructor_of cx "NumeralSpec" c with
  | 1, [cs; e; cv] ->
    let numeral_cases = list cx numeral_case cs in
    let numeral_emitter = numeral_emitter cx e in
    let numeral_converters = list cx declaration cv in
    {numeral_cases; numeral_emitter; numeral_converters}
  | _ -> fail cx ~what:"a NumeralSpec" c

let type_mapping env sigma c =
  let cx = {env; sigma} in
  match constructor_of cx "TypeMapping" c with
  | 1, [h; t; cs; cp; ac; vs; it; md; lt; rl; nm] ->
    let type_headers = strings cx h in
    let type_cpp = type_expr cx t in
    let type_components = list cx component cs in
    let type_copy = copy_model cx cp in
    let type_access = access_model cx ac in
    let type_views = views cx vs in
    let type_interface = type_interface cx it in
    let type_model = value_model cx md in
    let type_lifetime = lifetime_model cx lt in
    let type_release = release_plan cx rl in
    let type_numerals = option cx numeral_spec nm in
    { type_headers; type_cpp; type_components; type_copy; type_access;
      type_views; type_interface; type_model; type_lifetime; type_release;
      type_numerals }
  | _ -> fail cx ~what:"a TypeMapping" c

let input_use cx c =
  match constructor_of cx "InputUse" c with
  | 1, [] -> Ignore
  | 2, [] -> Read
  | 3, [] -> Read_canonical
  | 4, [] -> Write
  | 5, [] -> Write_canonical
  | 6, [] -> Take
  | 7, [] -> Replace
  | 8, [] -> Opaque_use
  | _ -> fail cx ~what:"an InputUse" c

let argument_spec cx c =
  match constructor_of cx "ArgumentSpec" c with
  | 1, [n; u] ->
    let argument_name = string cx n in
    {argument_name; argument_use = input_use cx u}
  | _ -> fail cx ~what:"an ArgumentSpec" c

let component_path cx c =
  match constructor_of cx "ComponentPath" c with
  | 1, [a; cs] ->
    let path_argument = string cx a in
    {path_argument; path_components = strings cx cs}
  | _ -> fail cx ~what:"a ComponentPath" c

let initial_multiplicity cx c =
  match constructor_of cx "InitialMultiplicity" c with
  | 1, [] -> Initialise_once
  | 2, [] -> Initialise_many
  | _ -> fail cx ~what:"an InitialMultiplicity" c

let component_initialiser cx c =
  match constructor_of cx "ComponentInitialiser" c with
  | 1, [k; s; m] ->
    let initial_component = string cx k in
    let initial_source_argument = option cx string s in
    let initial_multiplicity = initial_multiplicity cx m in
    {initial_component; initial_source_argument; initial_multiplicity}
  | _ -> fail cx ~what:"a ComponentInitialiser" c

let borrow_form cx c =
  match constructor_of cx "BorrowForm" c with
  | 1, [] -> Canonical_borrow
  | 2, [] -> Read_view_borrow
  | 3, [] -> Writable_view_borrow
  | _ -> fail cx ~what:"a BorrowForm" c

let result_spec cx c =
  match constructor_of cx "ResultSpec" c with
  | 1, [] -> Return_value
  | 2, [f; o] ->
    let f = borrow_form cx f in
    Return_borrowed (f, component_path cx o)
  | 3, [a] -> Return_same_identity (string cx a)
  | 4, [is] -> Return_fresh_identity (list cx component_initialiser is)
  | 5, [] -> Return_opaque
  | _ -> fail cx ~what:"a ResultSpec" c

let operation_fact cx c =
  match constructor_of cx "OperationFact" c with
  | 1, [p] -> Reads_component (component_path cx p)
  | 2, [p; s] ->
    let p = component_path cx p in
    Writes_component (p, option cx string s)
  | 3, [p] -> Invalidates_element_borrows (component_path cx p)
  | 4, [p] -> Invalidates_views (component_path cx p)
  | 5, [a; p] ->
    let a = string cx a in
    Retains_argument (a, component_path cx p)
  | 6, [a] -> Releases_identity (string cx a)
  | 7, [n] -> External_effect (string cx n)
  | _ -> fail cx ~what:"an OperationFact" c

let contract_parts cx args result facts =
  let args = list cx argument_spec args in
  let result = result_spec cx result in
  (args, result, list cx operation_fact facts)

let operation_contract cx c =
  match constructor_of cx "OperationContract" c with
  | 1, [a; r; f] ->
    let a, r, f = contract_parts cx a r f in
    Pure_operation (a, r, f)
  | 2, [a; r; f] ->
    let a, r, f = contract_parts cx a r f in
    Effectful_operation (a, r, f)
  | 3, [] -> Opaque_operation
  | _ -> fail cx ~what:"an OperationContract" c

let operation_mapping env sigma c =
  let cx = {env; sigma} in
  match constructor_of cx "OperationMapping" c with
  | 1, [h; k; ct] ->
    let operation_headers = strings cx h in
    let operation_cpp = construction cx k in
    let operation_contract = operation_contract cx ct in
    {operation_headers; operation_cpp; operation_contract}
  | _ -> fail cx ~what:"an OperationMapping" c

let reference_of env sigma c = reference_term {env; sigma} c

(** {1 Printing} *)

open Pp

let pr_string s = qstring s
let pr_list f l = str "[" ++ prlist_with_sep (fun () -> str ";" ++ spc ()) f l ++ str "]"
let pr_strings l = pr_list pr_string l
let pr_option f = function None -> str "None" | Some x -> str "Some " ++ f x
let pr_constr env c = Printer.pr_constr_env env (Evd.from_env env) c

let pr_declaration env {reference; parameters} =
  let r = Printer.pr_global reference in
  if parameters = [] then str "Ref " ++ r
  else
    str "Ref (" ++ r
    ++ prlist (fun p -> spc () ++ pr_constr env p) parameters
    ++ str ")"

let rec pr_type_expr env = function
  | Cpp.Name s -> str "Name " ++ pr_string s
  | Cpp.Apply (s, args) ->
    str "Apply " ++ pr_string s ++ spc () ++ pr_list (pr_type_argument env) args
  | Cpp.Source_type t -> str "SourceType (" ++ pr_constr env t ++ str ")"
  | Cpp.Stored_component s -> str "StoredComponent " ++ pr_string s
  | Cpp.Pointer t -> str "Pointer (" ++ pr_type_expr env t ++ str ")"
  | Cpp.Const t -> str "Const (" ++ pr_type_expr env t ++ str ")"
  | Cpp.Unsafe_verbatim s -> str "UnsafeVerbatim " ++ pr_string s

and pr_type_argument env = function
  | Cpp.Type_arg t -> str "TypeArg (" ++ pr_type_expr env t ++ str ")"
  | Cpp.Value_arg s -> str "ValueArg " ++ pr_string s

let pr_construction = function
  | Expr s -> str "Expr " ++ pr_string s
  | With_body (i, b) -> str "WithBody " ++ pr_string i ++ spc () ++ pr_string b

let pr_copy = function
  | Bit_copy -> str "BitCopy"
  | Retain_identity -> str "RetainIdentity"
  | Duplicate_value -> str "DuplicateValue"
  | Copy_components l -> str "CopyComponents " ++ pr_strings l
  | Unknown_copy -> str "UnknownCopy"

let pr_read_style = function
  | Read_by_value -> str "ReadByValue"
  | Read_by_const_reference -> str "ReadByConstReference"
  | Read_by_components l -> str "ReadByComponents " ++ pr_strings l

let pr_handle = function
  | Handle_by_value -> str "HandleByValue"
  | Handle_by_const_reference -> str "HandleByConstReference"

let pr_physical = function
  | Canonical_by_value -> str "CanonicalByValue"
  | Canonical_by_const_reference -> str "CanonicalByConstReference"
  | Canonical_by_mutable_reference -> str "CanonicalByMutableReference"
  | Exact_parameter s -> str "ExactParameter " ++ pr_string s

let pr_access = function
  | Read_only_value r -> str "ReadOnlyValue " ++ pr_read_style r
  | Mutable_value r -> str "MutableValue " ++ pr_read_style r
  | Read_only_handle h -> str "ReadOnlyHandle " ++ pr_handle h
  | Mutable_handle h -> str "MutableHandle " ++ pr_handle h
  | Explicit_access s ->
    str "ExplicitAccess {read " ++ pr_physical s.explicit_read
    ++ str "; write " ++ pr_option pr_physical s.explicit_write
    ++ str "; replace " ++ pr_option pr_physical s.explicit_replace
    ++ str "}"

let pr_model = function
  | Structural -> str "Structural"
  | Identity -> str "Identity"
  | Unspecified -> str "Unspecified"

let pr_lifetime env = function
  | Native_raii -> str "NativeRAII"
  | Region_owned d -> str "RegionOwned (" ++ pr_declaration env d ++ str ")"
  | Externally_owned -> str "ExternallyOwned"
  | Manual_shared (r, l) ->
    str "ManualShared (" ++ pr_declaration env r ++ str ") ("
    ++ pr_declaration env l ++ str ")"

let pr_release = function
  | Ordinary_release -> str "OrdinaryRelease"
  | Drain_with s -> str "DrainWith " ++ pr_string s

let pr_view env v =
  let escape =
    match v.view_escape with
    | Materialise_view k -> str "MaterialiseView (" ++ pr_construction k ++ str ")"
    | Borrow_only -> str "BorrowOnly"
  in
  hov 2
    ( str "{headers " ++ pr_strings v.view_headers ++ str ";" ++ spc ()
    ++ str "cpp " ++ pr_type_expr env v.view_cpp ++ str ";" ++ spc ()
    ++ str "from_canonical " ++ pr_string v.view_from_canonical ++ str ";"
    ++ spc () ++ str "escape " ++ escape ++ str "}" )

let pr_views env = function
  | No_views -> str "NoViews"
  | Read_views r -> str "ReadViews" ++ spc () ++ pr_view env r
  | Read_write_views (r, w, s) ->
    str "ReadWriteViews" ++ spc () ++ pr_view env r ++ spc () ++ pr_view env w
    ++ spc () ++ pr_string s

let pr_component env {component_name; component_type} =
  pr_string component_name ++ str " : "
  ++
  match component_type with
  | Known_type t -> str "KnownType (" ++ pr_constr env t ++ str ")"
  | Field_type (d, n) ->
    str "FieldType (" ++ pr_declaration env d ++ str ") " ++ int n

let pr_projection = function
  | Owned_projection s -> str "OwnedProjection " ++ pr_string s
  | Canonical_borrow_projection s -> str "CanonicalBorrowProjection " ++ pr_string s
  | Read_view_projection s -> str "ReadViewProjection " ++ pr_string s

let pr_ctor env m =
  let view =
    pr_option
      (fun v ->
        str "{"
        ++ ( match v.view_requirement with
           | Preferred_observation -> str "PreferredObservation"
           | Canonical_observation -> str "CanonicalObservation" )
        ++ str "; test " ++ pr_string v.case_test ++ str "; fields "
        ++ pr_list (fun (n, p) -> int n ++ str " => " ++ pr_projection p) v.case_fields
        ++ str "}" )
      m.ctor_view
  in
  hov 2
    ( pr_declaration env m.ctor_source ++ str ":" ++ spc () ++ str "build "
    ++ pr_construction m.ctor_build ++ str ";" ++ spc () ++ str "view " ++ view )

let pr_interface env = function
  | Abstract_interface -> str "AbstractInterface"
  | Algebraic_interface l ->
    v 2 (str "AlgebraicInterface" ++ prlist (fun m -> cut () ++ pr_ctor env m) l)

let pr_numeral_action = function
  | Numeral_zero -> str "NumeralZero"
  | Numeral_one -> str "NumeralOne"
  | Numeral_successor n -> str "NumeralSuccessor " ++ int n
  | Numeral_double n -> str "NumeralDouble " ++ int n
  | Numeral_double_plus_one n -> str "NumeralDoublePlusOne " ++ int n
  | Numeral_identity n -> str "NumeralIdentity " ++ int n
  | Numeral_negate n -> str "NumeralNegate " ++ int n

let pr_numerals env s =
  str "{cases "
  ++ pr_list
       (fun c ->
         pr_declaration env c.numeral_constructor ++ str " => "
         ++ pr_numeral_action c.numeral_action)
       s.numeral_cases
  ++ str "; emitter "
  ++ ( match s.numeral_emitter with
     | Integer_token (p, q) -> str "IntegerToken " ++ pr_string p ++ spc () ++ pr_string q
     | Decimal_constructor c -> str "DecimalConstructor " ++ pr_string c )
  ++ str "; converters "
  ++ pr_list (pr_declaration env) s.numeral_converters
  ++ str "}"

let field name pp = cut () ++ hov 2 (str name ++ str " :=" ++ spc () ++ pp)

let pr_type_mapping env m =
  v 2
    ( str "TypeMapping"
    ++ field "type_headers" (pr_strings m.type_headers)
    ++ field "type_cpp" (pr_type_expr env m.type_cpp)
    ++ field "type_components" (pr_list (pr_component env) m.type_components)
    ++ field "type_copy" (pr_copy m.type_copy)
    ++ field "type_access" (pr_access m.type_access)
    ++ field "type_views" (pr_views env m.type_views)
    ++ field "type_interface" (pr_interface env m.type_interface)
    ++ field "type_model" (pr_model m.type_model)
    ++ field "type_lifetime" (pr_lifetime env m.type_lifetime)
    ++ field "type_release" (pr_release m.type_release)
    ++ field "type_numerals" (pr_option (pr_numerals env) m.type_numerals) )

let pr_use = function
  | Ignore -> str "Ignore"
  | Read -> str "Read"
  | Read_canonical -> str "ReadCanonical"
  | Write -> str "Write"
  | Write_canonical -> str "WriteCanonical"
  | Take -> str "Take"
  | Replace -> str "Replace"
  | Opaque_use -> str "OpaqueUse"

let pr_path p =
  str "{" ++ pr_string p.path_argument ++ str " " ++ pr_strings p.path_components ++ str "}"

let pr_result = function
  | Return_value -> str "ReturnValue"
  | Return_borrowed (f, o) ->
    str "ReturnBorrowed "
    ++ ( match f with
       | Canonical_borrow -> str "CanonicalBorrow"
       | Read_view_borrow -> str "ReadViewBorrow"
       | Writable_view_borrow -> str "WritableViewBorrow" )
    ++ str " " ++ pr_path o
  | Return_same_identity a -> str "ReturnSameIdentity " ++ pr_string a
  | Return_fresh_identity l ->
    str "ReturnFreshIdentity "
    ++ pr_list
         (fun i ->
           str "{" ++ pr_string i.initial_component ++ str " from "
           ++ pr_option pr_string i.initial_source_argument
           ++ ( match i.initial_multiplicity with
              | Initialise_once -> str " once"
              | Initialise_many -> str " many" )
           ++ str "}")
         l
  | Return_opaque -> str "ReturnOpaque"

let pr_fact = function
  | Reads_component p -> str "ReadsComponent " ++ pr_path p
  | Writes_component (p, s) ->
    str "WritesComponent " ++ pr_path p ++ str " " ++ pr_option pr_string s
  | Invalidates_element_borrows p -> str "InvalidatesElementBorrows " ++ pr_path p
  | Invalidates_views p -> str "InvalidatesViews " ++ pr_path p
  | Retains_argument (a, p) -> str "RetainsArgument " ++ pr_string a ++ str " " ++ pr_path p
  | Releases_identity a -> str "ReleasesIdentity " ++ pr_string a
  | External_effect n -> str "ExternalEffect " ++ pr_string n

let pr_contract = function
  | Opaque_operation -> str "OpaqueOperation"
  | (Pure_operation (args, r, fs) | Effectful_operation (args, r, fs)) as c ->
    v 2
      ( ( match c with
        | Pure_operation _ -> str "PureOperation"
        | _ -> str "EffectfulOperation" )
      ++ field "arguments"
           (pr_list
              (fun a -> pr_string a.argument_name ++ str " : " ++ pr_use a.argument_use)
              args)
      ++ field "result" (pr_result r)
      ++ field "facts" (pr_list pr_fact fs) )

let pr_operation_mapping m =
  v 2
    ( str "OperationMapping"
    ++ field "operation_headers" (pr_strings m.operation_headers)
    ++ field "operation_cpp" (pr_construction m.operation_cpp)
    ++ field "operation_contract" (pr_contract m.operation_contract) )
