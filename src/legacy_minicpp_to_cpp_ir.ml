(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp
module T = Cpp_ir.Type
module E = Cpp_ir.Expr
module S = Cpp_ir.Stmt
module D = Cpp_ir.Decl
module F = Cpp_ir.Field
module Tp = Cpp_ir.Template

type failure =
  | Lowered_only of string
  | Dead of string

(* Raised at the first form with no CppIR counterpart; it aborts the whole
   conversion, which the exported functions turn into an [Error]. *)
exception Unconvertible of failure

let dead form = raise_notrace (Unconvertible (Dead form))

let describe = function
  | Lowered_only form -> form ^ ", which only a lowered declaration may hold, survived resolution"
  | Dead form -> form ^ ", which no pass produces and CppIR does not have, was produced"

type phase = Cpp_ir.Lowered.phase

let list = List.map
let opt = Option.map

let tvar : tvar -> T.Type_variable.t = function
  | Tv_index (i, h) -> Index (i, h)
  | Tv_named x -> Named x

let erased_kind : erased_kind -> T.Erased_kind.t = function
  | Ek_type -> Type
  | Ek_prop -> Proof
  | Ek_implicit -> Implicit

let variant_storage : variant_storage -> T.Variant_storage.t = function
  | Inline_variant -> Inline
  | Shared_variant -> Shared

let ref_kind : ref_kind -> T.Reference_kind.t = function
  | Lvalue -> Lvalue
  | Forwarding -> Forwarding

let written_capture : written_capture -> E.Written_capture.t = function
  | Captures_nothing -> Nothing
  | By_reference -> By_reference
  | By_copy {this; moved} -> By_copy {this; moved}

let capture : capture -> phase E.Capture.t = function
  | Immediate -> Runs_in_place
  | Closure -> Stored
  | Written w -> Written (written_capture w)

let constexpr : constexpr_eligibility -> phase D.Constexpr.t = function
  | Undecided -> Undecided
  | Eligible -> Eligible
  | Ineligible -> Ineligible

let precondition : precondition -> S.Precondition.t = function
  | Pchecked s -> Checked s
  | Pstated s -> Stated s

let binop : cpp_binop -> Cpp_ir.Binary_operator.t = function
  | Beq -> Equal
  | Bneq -> Not_equal
  | Band -> And
  | Bor -> Or
  | Bassign -> Assign

let unop : cpp_unop -> Cpp_ir.Unary_operator.t = function
  | Unot -> Not
  | Uaddr -> Address_of

let alloc_kind : alloc_kind -> E.Allocation.t = function
  | Alloc_heap -> Heap
  | Alloc_arena_scoped -> Arena_scoped
  | Alloc_reusing -> Reusing

let access : obj_access -> E.Access.t = function
  | Adot -> Dot
  | Aarrow -> Arrow

let value_category : value_category -> Tp.Value_category.t = function
  | Mutable_lvalue -> Mutable_lvalue
  | Const_lvalue -> Const_lvalue
  | Xvalue -> Xvalue
  | Prvalue -> Prvalue

let visibility : cpp_visibility -> F.Visibility.t = function
  | VPublic -> Public
  | VPrivate -> Private

let section : section_tag -> F.Section.t = function
  | STypes -> Types
  | SData -> Data
  | SCreators -> Creators
  | SManipulators -> Manipulators
  | SAccessors -> Accessors
  | SNoTag -> Untagged

let ref_qual : ref_qual -> F.Receiver.ref_qualifier = function
  | Rq_any -> Any
  | Rq_lvalue -> Lvalue
  | Rq_rvalue -> Rvalue

let receiver : receiver -> F.Receiver.t = function
  | Static -> Static
  | Instance {this_pos; is_const; ref_qual = q; returns_field} ->
    Instance {this_position = this_pos; is_const; ref_qualifier = ref_qual q; returns_field}

let scrutinee_hold : scrutinee_hold -> S.Custom_match.scrutinee_hold = function
  | Scrut_owned -> Owned
  | Scrut_borrowed -> Borrowed

let match_piece : match_piece -> S.Custom_match.piece = function
  | Mp_text s -> Text s
  | Mp_scrutinee {parenthesised} -> Scrutinee {parenthesised}
  | Mp_matched_type -> Matched_type
  | Mp_type_arg i -> Type_argument i
  | Mp_branch i -> Branch i
  | Mp_binder (i, j) -> Binder (i, j)
  | Mp_binder_type (i, j) -> Binder_type (i, j)

let inline_shape : inline_shape -> Cpp_ir.Foreign.shape = function
  | Inline_identity -> Identity
  | Inline_pair_projection s -> Pair_projection s
  | Inline_other -> Other

let inline_form : inline_form -> Cpp_ir.Foreign.form = function
  | Block_iife -> Block
  | Bare_callee -> Bare_callee
  | Templated -> Templated

let inline_template (t : inline_template) : Cpp_ir.Foreign.template =
  {text = t.it_text; form = inline_form t.it_form; shape = inline_shape t.it_shape; linear = t.it_linear}

let wrapper_piece : wrapper_piece -> Cpp_ir.Foreign.wrapper_piece = function
  | Wp_text s -> Wrapper_text s
  | Wp_element -> Wrapper_element

let foreign_piece : foreign_piece -> Cpp_ir.Foreign.piece = function
  | Fp_text s -> Text s
  | Fp_type i -> Type_argument i
  | Fp_element (i, w) -> Element (i, opt (list wrapper_piece) w)
  | Fp_value i -> Value i
  | Fp_yields -> Yields
  | Fp_result -> Result
  | Fp_statement_end -> Statement_end

let foreign_use : foreign_use -> Cpp_ir.Foreign.use = function
  | Foreign_constant -> Constant
  | Foreign_call -> Call
  | Foreign_block w -> Block_value (written_capture w)
  | Foreign_statements -> Statements

let local_fixpoint_encoding : local_fixpoint_encoding -> E.Local_fixpoint.encoding = function
  | Self_passing xs -> Self_passing xs
  | Knot -> Knot
  | Lowered -> Lowered

let local_fixpoint (f : local_fixpoint) : E.Local_fixpoint.t =
  { binder = f.lf_binder;
    name = f.lf_name;
    member = f.lf_member;
    captured = f.lf_captured;
    encoding = local_fixpoint_encoding f.lf_encoding }

(* The conversion is structural: each MiniCpp constructor maps to its CppIR
   counterpart.  A form only a lowered program may hold raises
   [Lowered_only]; a MiniCpp form no pass produces any more raises
   [Dead]. *)
let rec ty : cpp_type -> phase T.t = function
  | Tvar v -> Variable (tvar v)
  | Tinstance (x, r) -> Instance (x, r)
  | Tpromoted x -> Promoted_member x
  | Tid (x, ts) -> Named (x, list ty ts)
  | Tid_external (s, ts) -> External (s, list ty ts)
  | Tglob (r, ts, es) -> Entity_application (r, list ty ts, list expr es)
  | Tfun (ds, c) -> Function (list ty ds, ty c)
  | Tconst t -> Const (ty t)
  | Tnamespace (r, t) -> In_namespace (r, ty t)
  | Tqualified (t, x) -> Member (ty t, x)
  | Tapply (t, ts) -> Apply (ty t, list ty ts)
  | Tref (k, t) -> Reference (ref_kind k, ty t)
  | Terased k -> Erased (erased_kind k)
  | Tptr t -> Pointer (ty t)
  | Tvariant (s, ts) -> Variant (variant_storage s, list ty ts)
  | Tshared_ptr t -> Shared_pointer (ty t)
  | Tvoid -> Void
  | Tunresolved -> Obligation Unresolved_type
  | Tany -> Any
  | Ttyctor t -> Type_constructor (ty t)
  | Topaque -> Obligation Opaque_type
  | Tauto -> Auto
  | Tdecay t -> Decay (ty t)
  | Tnondeduced t -> Non_deduced (ty t)
  | Trebind (f, x) -> Rebind (ty f, ty x)
  | Thole -> Carrier_parameter
  | Texpr_type e -> Type_of (expr e)
  | Tdecltype_auto -> Decltype_auto
  | Tforeign f -> Foreign (foreign f)

and type_test : type_test -> phase T.Type_test.t = function
  | Tt_convertible (a, b) -> Convertible (ty a, ty b)

and foreign (f : Minicpp.foreign) : phase Cpp_ir.Foreign.t =
  { custom = f.fr_custom;
    types = list ty f.fr_types;
    values = list expr f.fr_values;
    yields = opt ty f.fr_yields;
    pieces = list foreign_piece f.fr_pieces }

and custom_info (c : custom_info) : phase Cpp_ir.Foreign.custom =
  {inline = opt inline_template c.ci_inline; custom_yields = opt ty c.ci_yields}

and call_sig (c : call_sig) : phase E.Call.signature =
  { yields = (match c.cs_yields with Ryields t -> Yields (ty t) | Ropaque -> Untyped);
    params = (match c.cs_params with Ptypes ts -> Types (list ty ts) | Punknown -> Unknown);
    constructs = c.cs_constructs;
    occurrence = c.cs_occurrence }

and erase_shape : erase_shape -> phase E.Erase_shape.t = function
  | Boxed_whole -> Boxed_whole
  | At_signature t -> At_signature (ty t)

and unbox : unbox -> phase E.Unbox.t = function
  | Unbox_to t -> To (ty t)
  | Unbox_or_keep t -> Or_keep (ty t)
  | Unbox_list (l, f) -> List (ty l, ty f)

and lambda (l : cpp_lambda) : phase E.Lambda.t =
  { params = list (fun (t, x) -> (ty t, x)) (lambda_params l.cl_params);
    type_params = l.cl_tparams;
    return_type = opt ty l.cl_ret;
    body = list stmt l.cl_body;
    capture = capture l.cl_capture;
    moved = l.cl_moved;
    binders = l.cl_binders;
    fixpoint = opt local_fixpoint l.cl_fixpoint }

and aggregate : 'n. 'n -> cpp_type list -> cpp_expr list -> ('n, phase) E.Aggregate.t =
 fun struct_ ts es -> {struct_; type_args = list ty ts; values = list expr es}

and expr : cpp_expr -> phase E.t = function
  | CPPvar x -> Local x
  | CPPglob (r, ts, ci) -> Entity (r, list ty ts, opt custom_info ci)
  | CPPnamespace _ -> dead "CPPnamespace"
  | CPPfun_call (c, f, args) -> Call (call_sig c, expr f, list expr (call_args args))
  | CPPconverting_ctor (t, es) -> Converting_construct (ty t, list expr es)
  | CPPbox (t, e) -> Box (ty t, expr e)
  | CPPderef e -> Dereference (expr e)
  | CPPmove e -> Move (expr e)
  | CPPforward (t, e) -> Forward (ty t, expr e)
  | CPPlambda l -> Lambda (lambda l)
  | CPPsuspend (t, e) -> Suspend (ty t, expr e)
  | CPPalloc (k, t) -> Allocate (alloc_kind k, ty t)
  | CPPstructmk _ -> dead "CPPstructmk"
  | CPPstruct (r, ts, es) -> Aggregate (aggregate r ts es)
  | CPPstruct_id (x, ts, es) -> Local_aggregate (aggregate x ts es)
  | CPPget (e, x) -> Member (expr e, x)
  | CPPget' (e, r, t) -> Project (expr e, r, opt ty t)
  | CPPstring s -> Literal (String s)
  | CPPuint u -> Literal (Uint63 u)
  | CPPfloat f -> Literal (Float f)
  | CPPparray (es, d) -> Persistent_array (Array.map expr es, expr d)
  | CPPrequires (ps, cs, ts) ->
    Requires
      { params = list (fun (t, x) -> (ty t, x)) ps;
        constraints = list (fun (e, c) -> (expr e, expr c)) cs;
        type_requirements = list ty ts }
  | CPPconcept_app (c, s, ts) -> Concept_application (c, s, list ty ts)
  | CPPnew _ -> dead "CPPnew"
  | CPPshared_ptr_ctor _ -> dead "CPPshared_ptr_ctor"
  | CPPthis -> This
  | CPPshared_from_this t -> Shared_from_this (ty t)
  | CPPaccess (a, e, x) -> Access (access a, expr e, x)
  | CPPaccess_call (a, e, x, es) -> Access_call (access a, expr e, x, list expr es)
  | CPPmethod_call m ->
    Method_call
      { method_ = m.mc_method;
        access = access m.mc_access;
        receiver = expr m.mc_receiver;
        type_args = list ty m.mc_type_args;
        args = list expr m.mc_args }
  | CPPmethod_value m ->
    Method_value
      { method_ = m.mv_method;
        access = access m.mv_access;
        receiver = m.mv_receiver;
        params = list (opt ty) m.mv_params;
        type_args = list ty m.mv_type_args }
  | CPPprojection p ->
    Projection {projection = p.pj_projection; record = expr p.pj_record; args = list expr p.pj_args}
  | CPPprojection_value r -> Projection_value r
  | CPPscope (e, x, ts) -> Scope (expr e, x, list ty ts)
  | CPPqualified_t (t, x) -> Type_member (ty t, x)
  | CPPconvertible_to t -> Convertible_to (ty t)
  | CPPabort (s, t) -> Abort (s, ty t)
  | CPPenum_val (r, x) -> Enum_value (r, x)
  | CPPnullptr -> Literal Null_pointer
  | CPPin_place -> In_place
  | CPPin_place_index i -> In_place_index i
  | CPPbraced es -> Braced (list expr es)
  | CPPstd_get (t, e) -> Variant_get (ty t, opt expr e)
  | CPPstd_holds_alternative t -> Holds_alternative (ty t)
  | CPPdeclval t -> Declval (ty t)
  | CPPtype_name t -> Type_name (ty t)
  | CPPnumeral (r, n) -> Numeral (r, {value = n.nl_value; text = n.nl_text})
  | CPPraw s -> Foreign_text s
  | CPPrt h -> Runtime h
  | CPPbinop (o, a, b) -> Binary (binop o, expr a, expr b)
  | CPPcond (c, a, b) -> Conditional (expr c, expr a, expr b)
  | CPPbool b -> Literal (Bool b)
  | CPPint i -> Literal (Int i)
  | CPPunop (o, e) -> Unary (unop o, expr e)
  | CPPany_cast (t, e) -> Any_cast (ty t, expr e)
  | CPPany_cast_tolerant (t, e) -> Tolerant_any_cast (ty t, expr e)
  | CPPunbox (u, e) -> Unbox (unbox u, expr e)
  | CPPconvert (t, e) -> Convert (ty t, expr e)
  | CPPerase_fn (s, e) -> Erase_callable (erase_shape s, expr e)
  | CPPerased_call (f, a) -> Erased_call (expr f, expr a)
  | CPPtolerant_call (f, es) -> Tolerant_call (expr f, list expr es)
  | CPPfn_value e -> Function_value (expr e)
  | CPPcontainer_cast (t, e, b) -> Container_cast (ty t, expr e, b)
  | CPPstd_get_if (t, e) -> Variant_get_if (ty t, expr e)
  | CPPforeign (u, f) -> Foreign (foreign_use u, foreign f)

and binding : asgn_target -> phase S.Binding.t = function
  | Declare (t, b) -> Declare (ty t, b)
  | Existing -> Existing
  | Declare_static t -> Declare_static (ty t)

and custom_match ret scrut targs branches (cm : custom_match) : phase S.Custom_match.t =
  let param (p : custom_param) : phase S.Custom_match.param =
    {name = p.cp_name; type_ = ty p.cp_type; binder = p.cp_binder}
  in
  { return_type = ty ret;
    scrutinee = expr scrut;
    type_args = list ty targs;
    branches = list (fun (ps, t, body) : phase S.Custom_match.branch ->
      {params = list param ps; type_ = ty t; body = list stmt body}) branches;
    template = cm.cm_template;
    inductive = cm.cm_inductive;
    hold = scrutinee_hold cm.cm_scrutinee;
    pieces =
      ( match cm.cm_pieces with
      | Some ps -> Instantiated (list match_piece ps)
      | None -> Uninstantiated ) }

and match_scrutinee (sc : smatch_scrutinee) : phase S.Match.scrutinee =
  {expr = expr sc.sc_expr; access = access sc.sc_access; owned = sc.sc_owned; flat = sc.sc_flat}

and match_branch (b : smatch_branch) : phase S.Match.branch =
  let field (f : field_binding) : phase S.Match.field_binding =
    {name = f.fb_name; type_ = ty f.fb_type; used = f.fb_used; binder = f.fb_binder}
  in
  { ctor_type = ty b.smb_ctor_type;
    var = b.smb_var;
    field_bindings = list field b.smb_field_bindings;
    extra_conditions = list expr b.smb_extra_conds;
    body = list stmt b.smb_body }

and stmts ss = list stmt ss

and stmt : cpp_stmt -> phase S.t = function
  | Sreturn e -> Return (opt expr e)
  | Sdecl (x, t, b) -> Declare (x, ty t, b)
  | Sasgn (x, target, e) -> Bind_variable (x, binding target, expr e)
  | Sexpr e -> Expression (expr e)
  | Scustom_case (ret, scrut, targs, branches, cm) -> Custom_match (custom_match ret scrut targs branches cm)
  | Sthrow s -> Throw s
  | Sswitch (e, r, branches, default) ->
    Switch
      { scrutinee = expr e;
        enum = r;
        branches = list (fun (x, ss) -> (x, stmts ss)) branches;
        default = opt stmts default }
  | Sassert p -> Assert (precondition p)
  | Sif (c, a, b) -> If {condition = expr c; then_ = stmts a; else_ = stmts b}
  | Sif_constexpr (t, a, b) -> If_constexpr {test = type_test t; then_ = stmts a; else_ = stmts b}
  | Sif_decl (x, t, e, a, b) ->
    If_declaration {name = x; type_ = ty t; init = expr e; then_ = stmts a; else_ = stmts b}
  | Sraw s -> Foreign_text s
  | Scomment s -> Comment s
  | Sstruct_def (x, fs) -> Local_struct (x, list (fun (f, t) -> (f, ty t)) fs)
  | Susing (x, t) -> Local_type_alias (x, ty t)
  | Sbind (xs, e) -> Structured_binding (xs, expr e)
  | Sdecl_init (x, t) -> Declare_value_initialized (x, ty t)
  | Sassign_expr (l, r) -> Assign (expr l, expr r)
  | Sfor_range (x, e, ss) -> For_range (x, expr e, stmts ss)
  | Swhile (c, ss) -> While (expr c, stmts ss)
  | Sblock ss -> Block (stmts ss)
  | Scontinue -> Continue
  | Sbreak -> Break
  | Sblock_custom (custom, template, result, t, values, type_args, binder) ->
    Foreign_block
      {custom; template; result; result_type = ty t; values = list expr values; type_args = list ty type_args; binder}
  | Smatch (sc, bs, default) -> Match (match_scrutinee sc, list match_branch bs, opt stmts default)

let invocation (i : invocation) : phase Tp.Invocation.t =
  {callable = value_category i.inv_callable; args = list (fun (c, t) -> (value_category c, ty t)) i.inv_args}

let parameter_kind : template_type -> phase Tp.Parameter_kind.t = function
  | TTtypename -> Typename
  | TTtypename_default t -> Typename_default (ty t)
  | TTtemplate n -> Template n
  | TTfun (ds, c) -> Callable_declared (list ty ds, ty c)
  | TTinvocable (is, r) -> Invocable (list invocation is, ty r)
  | TTconcept (r, ts) -> Concept (r, list ty ts)

let tparams ps : phase Tp.parameters = list (fun (k, x) -> (parameter_kind k, x)) ps

let method_field (m : method_field) : phase F.Method.t =
  { name = m.mf_name;
    globref = m.mf_globref;
    type_params = tparams m.mf_tparams;
    return_type = ty m.mf_ret_type;
    params = list (fun (x, t) -> (x, ty t)) m.mf_params;
    body = stmts m.mf_body;
    receiver = receiver m.mf_receiver;
    is_inline = m.mf_is_inline;
    no_pure = m.mf_no_pure;
    constexpr = constexpr m.mf_constexpr;
    is_noexcept = m.mf_is_noexcept;
    is_conversion = m.mf_is_conversion;
    binders = m.mf_binders;
    receiver_binder = m.mf_receiver_binder;
    loop = m.mf_loop }

let out_of_line : out_of_line_member -> phase F.Out_of_line.t = function
  | OLmethod m -> Method (method_field m)
  | OLdestructor ss -> Destructor (stmts ss)

let fields_of ts = list (fun (x, t) -> (x, ty t)) ts

let rec field : cpp_field -> phase F.t = function
  | Fvar (x, t) -> Data (x, ty t)
  | Fvar' (r, t) -> Entity_data (r, ty t)
  | Fmethod m -> Method (method_field m)
  | Fconstructor c ->
    Constructor
      { type_params = tparams c.fc_tparams;
        params = fields_of c.fc_params;
        inits = list (fun (x, e) -> (x, expr e)) c.fc_inits;
        body = stmts c.fc_body;
        explicit = c.fc_explicit;
        noexcept = c.fc_noexcept }
  | Fdestructor ss -> Destructor (stmts ss)
  | Fnested_struct (x, ms) -> Nested_struct (x, list member ms)
  | Fdeferred_struct d -> Deferred_struct {name = d.dfs_name; selves = fields_of d.dfs_selves; fields = fields_of d.dfs_fields}
  | Fnested_using (ps, x, t) -> Nested_type_alias (tparams ps, x, ty t)
  | Fmember_decl m -> Out_of_line_declaration (out_of_line m)
  | Fdeleted_ctor -> Deleted_default_constructor
  | Fdefaulted_special_members -> Defaulted_special_members

and member (f, v, s) : phase F.member = (field f, visibility v, section s)

let wrapper (w : nspace_wrapper) : D.Namespace.wrapper = {ref_ = w.nw_ref; merges = w.nw_merges}

let dstruct (s : dstruct) : phase Cpp_ir.Struct.t =
  { ref_ = s.ds_ref;
    fields = list member s.ds_fields;
    type_params = tparams s.ds_tparams;
    constraint_ = opt expr s.ds_constraint;
    needs_shared_from_this = s.ds_needs_shared_from_this }

let path_entry (r, ts) = (r, list ty ts)

let dfun (f : dfun) : phase Cpp_ir.Function.t =
  { path = {outer = path_entry f.df_path.dp_outer; inner = list path_entry f.df_path.dp_inner};
    return_type = ty f.df_ret;
    no_pure = f.df_no_pure;
    constexpr = constexpr f.df_constexpr;
    shape =
      ( match f.df_shape with
      | Ddef (ps, body) -> Definition (fields_of ps, stmts body)
      | Ddecl ps -> Declaration (list (fun (x, t) -> (x, ty t)) ps) );
    binders = f.df_binders;
    loop = f.df_loop }

let rec decl : cpp_decl -> phase D.t = function
  | Dtemplate (ps, c, d) -> Template (tparams ps, opt expr c, decl d)
  | Dnspace (w, ds) -> Namespace (opt wrapper w, list decl ds)
  | Dfun f -> Function (dfun f)
  | Dstruct s -> Struct (dstruct s)
  | Dasgn a -> Variable {ref_ = a.da_ref; type_ = ty a.da_type; init = expr a.da_init; constexpr = constexpr a.da_constexpr}
  | Dconcept (r, e) -> Concept (r, expr e)
  | Dstatic_assert (e, m) -> Static_assert (expr e, m)
  | Dusing u -> Type_alias {type_params = tparams u.du_tparams; name = u.du_name; rhs = opt ty u.du_rhs; note = u.du_note}
  | Dstruct_fwd (ps, r) -> Struct_forward_declaration (tparams ps, r)
  | Dfields s -> Merged_struct_members (dstruct s)
  | Dmember_def m ->
    Member_definition
      { owner = m.dm_owner;
        enclosing = opt wrapper m.dm_enclosing;
        type_params = tparams m.dm_tparams;
        member = out_of_line m.dm_field }
  | Denum e -> Enum {ref_ = e.de_ref; ctors = e.de_ctors; rocq_names = e.de_ctor_rocq_names; type_params = tparams e.de_tparams}

(* The exported conversions catch [Unconvertible]: [lower] treats it as an
   anomaly, [resolved] reports it. *)
let lowered convert x =
  match convert x with
  | x -> x
  | exception Unconvertible f -> CErrors.anomaly Pp.(str "Crane: a declaration did not lower: " ++ str (describe f))

let lower d = lowered decl d
let lower_stmt s = lowered stmt s

let resolved resolve convert x =
  match resolve (convert x) with
  | x -> Ok x
  | exception Unconvertible f -> Error f
  | exception Cpp_ir.Resolve.Owed form -> Error (Lowered_only form)

let lower_type t = lowered ty t
let lower_expr e = lowered expr e
let lower_template_parameters ps = lowered tparams ps
let lower_member m = lowered member m
let type_ t = resolved Cpp_ir.Resolve.type_ ty t
let expr e = resolved Cpp_ir.Resolve.expr expr e

let type_exn t =
  match type_ t with
  | Ok t -> t
  | Error f -> CErrors.anomaly Pp.(str "Crane: a type written outside every finished declaration: " ++ str (describe f))

let instantiated_type_exn instantiate t =
  match Cpp_ir.Resolve.type_ (instantiate (lowered ty t)) with
  | t -> t
  | exception Cpp_ir.Resolve.Owed form ->
    CErrors.anomaly
      Pp.(str "Crane: a type written outside every finished declaration: " ++ str (describe (Lowered_only form)))
