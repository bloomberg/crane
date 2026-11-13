(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Lowered CppIR back into MiniCpp.  See [cpp_ir_to_legacy_minicpp.mli]. *)

open Minicpp
open Cpp_ir.Grammar

type l = lowered

let list = List.map
let opt = Option.map

let tvar : Type_variable.t -> tvar = function
  | Index (i, h) -> Tv_index (i, h)
  | Named x -> Tv_named x

let erased_kind : Erased_kind.t -> erased_kind = function
  | Type -> Ek_type
  | Proof -> Ek_prop
  | Implicit -> Ek_implicit

let variant_storage : Variant_storage.t -> variant_storage = function
  | Inline -> Inline_variant
  | Shared -> Shared_variant

let ref_kind : Reference_kind.t -> ref_kind = function
  | Lvalue -> Lvalue
  | Forwarding -> Forwarding

let written_capture : Written_capture.t -> written_capture = function
  | Nothing -> Captures_nothing
  | By_reference -> By_reference
  | By_copy {this; moved} -> By_copy {this; moved}

let capture : l Capture.t -> capture = function
  | Runs_in_place -> Immediate
  | Stored -> Closure
  | Written w -> Written (written_capture w)

let constexpr : l Constexpr.t -> constexpr_eligibility = function
  | Undecided -> Undecided
  | Eligible -> Eligible
  | Ineligible -> Ineligible

let precondition : Precondition.t -> precondition = function
  | Checked s -> Pchecked s
  | Stated s -> Pstated s

let binop : Binary_operator.t -> cpp_binop = function
  | Equal -> Beq
  | Not_equal -> Bneq
  | And -> Band
  | Or -> Bor
  | Assign -> Bassign

let unop : Unary_operator.t -> cpp_unop = function
  | Not -> Unot
  | Address_of -> Uaddr

let alloc_kind : Allocation.t -> alloc_kind = function
  | Heap -> Alloc_heap
  | Arena_scoped -> Alloc_arena_scoped
  | Reusing -> Alloc_reusing

let access : Access.t -> obj_access = function
  | Dot -> Adot
  | Arrow -> Aarrow

let value_category : Value_category.t -> value_category = function
  | Mutable_lvalue -> Mutable_lvalue
  | Const_lvalue -> Const_lvalue
  | Xvalue -> Xvalue
  | Prvalue -> Prvalue

let visibility : Visibility.t -> cpp_visibility = function
  | Public -> VPublic
  | Private -> VPrivate

let section : Section.t -> section_tag = function
  | Types -> STypes
  | Data -> SData
  | Creators -> SCreators
  | Manipulators -> SManipulators
  | Accessors -> SAccessors
  | Untagged -> SNoTag

let ref_qual : Receiver.ref_qualifier -> ref_qual = function
  | Any -> Rq_any
  | Lvalue -> Rq_lvalue
  | Rvalue -> Rq_rvalue

let receiver : Receiver.t -> receiver = function
  | Static -> Static
  | Instance {this_position; is_const; ref_qualifier; returns_field} ->
    Instance {this_pos = this_position; is_const; ref_qual = ref_qual ref_qualifier; returns_field}

let scrutinee_hold : Custom_match.scrutinee_hold -> scrutinee_hold = function
  | Owned -> Scrut_owned
  | Borrowed -> Scrut_borrowed

let match_piece : Custom_match.piece -> match_piece = function
  | Text s -> Mp_text s
  | Scrutinee {parenthesised} -> Mp_scrutinee {parenthesised}
  | Matched_type -> Mp_matched_type
  | Type_argument i -> Mp_type_arg i
  | Branch i -> Mp_branch i
  | Binder (i, j) -> Mp_binder (i, j)
  | Binder_type (i, j) -> Mp_binder_type (i, j)

let inline_shape : Foreign.shape -> inline_shape = function
  | Identity -> Inline_identity
  | Pair_projection s -> Inline_pair_projection s
  | Other -> Inline_other

let inline_form : Foreign.form -> inline_form = function
  | Block -> Block_iife
  | Bare_callee -> Bare_callee
  | Templated -> Templated

let inline_template (t : Foreign.template) : inline_template =
  {it_text = t.text; it_form = inline_form t.form; it_shape = inline_shape t.shape; it_linear = t.linear}

let wrapper_piece : Foreign.wrapper_piece -> wrapper_piece = function
  | Wrapper_text s -> Wp_text s
  | Wrapper_element -> Wp_element

let foreign_piece : Foreign.piece -> foreign_piece = function
  | Text s -> Fp_text s
  | Type_argument i -> Fp_type i
  | Element (i, w) -> Fp_element (i, opt (list wrapper_piece) w)
  | Value i -> Fp_value i
  | Yields -> Fp_yields
  | Result -> Fp_result
  | Statement_end -> Fp_statement_end

let foreign_use : Foreign.use -> foreign_use = function
  | Constant -> Foreign_constant
  | Call -> Foreign_call
  | Block_value w -> Foreign_block (written_capture w)
  | Statements -> Foreign_statements

let local_fixpoint_encoding : Local_fixpoint.encoding -> local_fixpoint_encoding = function
  | Self_passing xs -> Self_passing xs
  | Knot -> Knot
  | Lowered -> Lowered

let local_fixpoint (f : Local_fixpoint.t) : local_fixpoint =
  { lf_binder = f.binder;
    lf_name = f.name;
    lf_member = f.member;
    lf_captured = f.captured;
    lf_encoding = local_fixpoint_encoding f.encoding }

(* A list in source order, stored reversed. *)
let reversed f xs = of_reversed (List.rev_map f xs)

let rec ty : l Type.t -> cpp_type = function
  | Variable v -> Tvar (tvar v)
  | Instance (x, r) -> Tinstance (x, r)
  | Promoted_member x -> Tpromoted x
  | Named (x, ts) -> Tid (x, list ty ts)
  | External (s, ts) -> Tid_external (s, list ty ts)
  | Entity_application (r, ts, es) -> Tglob (r, list ty ts, list expr es)
  | Function (ds, c) -> Tfun (list ty ds, ty c)
  | Const t -> Tconst (ty t)
  | In_namespace (r, t) -> Tnamespace (r, ty t)
  | Member (t, x) -> Tqualified (ty t, x)
  | Apply (t, ts) -> Tapply (ty t, list ty ts)
  | Reference (k, t) -> Tref (ref_kind k, ty t)
  | Erased k -> Terased (erased_kind k)
  | Pointer t -> Tptr (ty t)
  | Variant (s, ts) -> Tvariant (variant_storage s, list ty ts)
  | Shared_pointer t -> Tshared_ptr (ty t)
  | Void -> Tvoid
  | Any -> Tany
  | Type_constructor t -> Ttyctor (ty t)
  | Auto -> Tauto
  | Decay t -> Tdecay (ty t)
  | Non_deduced t -> Tnondeduced (ty t)
  | Rebind (f, x) -> Trebind (ty f, ty x)
  | Carrier_parameter -> Thole
  | Type_of e -> Texpr_type (expr e)
  | Decltype_auto -> Tdecltype_auto
  | Foreign f -> Tforeign (foreign f)
  | Obligation Unresolved_type -> Tunresolved
  | Obligation Opaque_type -> Topaque
  | Obligation _ -> CErrors.anomaly Pp.(str "Crane: a type obligation other than an unresolved or opaque type")

and type_test : l Type_test.t -> type_test = function
  | Convertible (a, b) -> Tt_convertible (ty a, ty b)

and foreign (f : l Foreign.t) : Minicpp.foreign =
  { fr_custom = f.custom;
    fr_types = list ty f.types;
    fr_values = list expr f.values;
    fr_yields = opt ty f.yields;
    fr_pieces = list foreign_piece f.pieces }

and custom_info (c : l Foreign.custom) : custom_info =
  {ci_inline = opt inline_template c.inline; ci_yields = opt ty c.custom_yields}

and call_sig (c : l Call.signature) : call_sig =
  { cs_yields = (match c.yields with Yields t -> Ryields (ty t) | Untyped -> Ropaque);
    cs_params = (match c.params with Types ts -> Ptypes (list ty ts) | Unknown -> Punknown);
    cs_constructs = c.constructs;
    cs_occurrence = c.occurrence }

and erase_shape : l Erase_shape.t -> erase_shape = function
  | Boxed_whole -> Boxed_whole
  | At_signature t -> At_signature (ty t)

and unbox : l Unbox.t -> unbox = function
  | To t -> Unbox_to (ty t)
  | Or_keep t -> Unbox_or_keep (ty t)
  | List (a, b) -> Unbox_list (ty a, ty b)

and lambda (l : l Lambda.t) : cpp_lambda =
  { cl_params = reversed (fun (t, x) -> (ty t, x)) l.params;
    cl_tparams = l.type_params;
    cl_ret = opt ty l.return_type;
    cl_body = list stmt l.body;
    cl_capture = capture l.capture;
    cl_moved = l.moved;
    cl_binders = l.binders;
    cl_fixpoint = opt local_fixpoint l.fixpoint }

and expr : l Expr.t -> cpp_expr = function
  | Local x -> CPPvar x
  | Entity (r, ts, ci) -> CPPglob (r, list ty ts, opt custom_info ci)
  | Call (c, f, args) -> CPPfun_call (call_sig c, expr f, reversed expr args)
  | Converting_construct (t, es) -> CPPconverting_ctor (ty t, list expr es)
  | Box (t, e) -> CPPbox (ty t, expr e)
  | Dereference e -> CPPderef (expr e)
  | Move e -> CPPmove (expr e)
  | Forward (t, e) -> CPPforward (ty t, expr e)
  | Lambda l -> CPPlambda (lambda l)
  | Suspend (t, e) -> CPPsuspend (ty t, expr e)
  | Allocate (k, t) -> CPPalloc (alloc_kind k, ty t)
  | Aggregate a -> CPPstruct (a.struct_, list ty a.type_args, list expr a.values)
  | Local_aggregate a -> CPPstruct_id (a.struct_, list ty a.type_args, list expr a.values)
  | Member (e, x) -> CPPget (expr e, x)
  | Project (e, r, t) -> CPPget' (expr e, r, opt ty t)
  | Literal (String s) -> CPPstring s
  | Literal (Uint63 u) -> CPPuint u
  | Literal (Float f) -> CPPfloat f
  | Literal (Bool b) -> CPPbool b
  | Literal (Int i) -> CPPint i
  | Literal Null_pointer -> CPPnullptr
  | Persistent_array (es, d) -> CPPparray (Array.map expr es, expr d)
  | Requires q ->
    CPPrequires
      ( list (fun (t, x) -> (ty t, x)) q.params,
        list (fun (e, c) -> (expr e, expr c)) q.constraints,
        list ty q.type_requirements )
  | Concept_application (c, s, ts) -> CPPconcept_app (c, s, list ty ts)
  | This -> CPPthis
  | Shared_from_this t -> CPPshared_from_this (ty t)
  | Access (a, e, x) -> CPPaccess (access a, expr e, x)
  | Access_call (a, e, x, es) -> CPPaccess_call (access a, expr e, x, list expr es)
  | Method_call m ->
    CPPmethod_call
      { mc_method = m.method_;
        mc_access = access m.access;
        mc_receiver = expr m.receiver;
        mc_type_args = list ty m.type_args;
        mc_args = list expr m.args }
  | Method_value m ->
    CPPmethod_value
      { mv_method = m.method_;
        mv_access = access m.access;
        mv_receiver = m.receiver;
        mv_params = list (opt ty) m.params;
        mv_type_args = list ty m.type_args }
  | Projection p -> CPPprojection {pj_projection = p.projection; pj_record = expr p.record; pj_args = list expr p.args}
  | Projection_value r -> CPPprojection_value r
  | Scope (e, x, ts) -> CPPscope (expr e, x, list ty ts)
  | Type_member (t, x) -> CPPqualified_t (ty t, x)
  | Convertible_to t -> CPPconvertible_to (ty t)
  | Abort (s, t) -> CPPabort (s, ty t)
  | Enum_value (r, x) -> CPPenum_val (r, x)
  | In_place -> CPPin_place
  | In_place_index i -> CPPin_place_index i
  | Braced es -> CPPbraced (list expr es)
  | Variant_get (t, e) -> CPPstd_get (ty t, opt expr e)
  | Holds_alternative t -> CPPstd_holds_alternative (ty t)
  | Declval t -> CPPdeclval (ty t)
  | Type_name t -> CPPtype_name (ty t)
  | Numeral (r, n) -> CPPnumeral (r, {nl_value = n.value; nl_text = n.text})
  | Foreign_text s -> CPPraw s
  | Runtime h -> CPPrt h
  | Binary (o, a, b) -> CPPbinop (binop o, expr a, expr b)
  | Conditional (c, a, b) -> CPPcond (expr c, expr a, expr b)
  | Unary (o, e) -> CPPunop (unop o, expr e)
  | Any_cast (t, e) -> CPPany_cast (ty t, expr e)
  | Tolerant_any_cast (t, e) -> CPPany_cast_tolerant (ty t, expr e)
  | Unbox (u, e) -> CPPunbox (unbox u, expr e)
  | Convert (t, e) -> CPPconvert (ty t, expr e)
  | Erase_callable (s, e) -> CPPerase_fn (erase_shape s, expr e)
  | Erased_call (f, a) -> CPPerased_call (expr f, expr a)
  | Tolerant_call (f, es) -> CPPtolerant_call (expr f, list expr es)
  | Function_value e -> CPPfn_value (expr e)
  | Container_cast (t, e, b) -> CPPcontainer_cast (ty t, expr e, b)
  | Variant_get_if (t, e) -> CPPstd_get_if (ty t, expr e)
  | Foreign (u, f) -> CPPforeign (foreign_use u, foreign f)

and binding : l Binding.t -> asgn_target = function
  | Declare (t, b) -> Declare (ty t, b)
  | Existing -> Existing
  | Declare_static t -> Declare_static (ty t)

and stmts ss = list stmt ss

and stmt : l Stmt.t -> cpp_stmt = function
  | Return e -> Sreturn (opt expr e)
  | Declare (x, t, b) -> Sdecl (x, ty t, b)
  | Bind_variable (x, b, e) -> Sasgn (x, binding b, expr e)
  | Expression e -> Sexpr (expr e)
  | Custom_match m ->
    let param (p : l Custom_match.param) = {cp_name = p.name; cp_type = ty p.type_; cp_binder = p.binder} in
    Scustom_case
      ( ty m.return_type,
        expr m.scrutinee,
        list ty m.type_args,
        list (fun (b : l Custom_match.branch) -> (list param b.params, ty b.type_, stmts b.body)) m.branches,
        { cm_template = m.template;
          cm_inductive = m.inductive;
          cm_scrutinee = scrutinee_hold m.hold;
          cm_pieces = (match m.pieces with Instantiated ps -> Some (list match_piece ps) | Uninstantiated -> None) } )
  | Throw s -> Sthrow s
  | Switch s -> Sswitch (expr s.scrutinee, s.enum, list (fun (x, ss) -> (x, stmts ss)) s.branches, opt stmts s.default)
  | Assert p -> Sassert (precondition p)
  | If s -> Sif (expr s.condition, stmts s.then_, stmts s.else_)
  | If_constexpr s -> Sif_constexpr (type_test s.test, stmts s.then_, stmts s.else_)
  | If_declaration s -> Sif_decl (s.name, ty s.type_, expr s.init, stmts s.then_, stmts s.else_)
  | Foreign_text s -> Sraw s
  | Comment s -> Scomment s
  | Local_struct (x, fs) -> Sstruct_def (x, list (fun (f, t) -> (f, ty t)) fs)
  | Local_type_alias (x, t) -> Susing (x, ty t)
  | Structured_binding (xs, e) -> Sbind (xs, expr e)
  | Declare_value_initialized (x, t) -> Sdecl_init (x, ty t)
  | Assign (a, b) -> Sassign_expr (expr a, expr b)
  | For_range (x, e, ss) -> Sfor_range (x, expr e, stmts ss)
  | While (c, ss) -> Swhile (expr c, stmts ss)
  | Block ss -> Sblock (stmts ss)
  | Continue -> Scontinue
  | Break -> Sbreak
  | Match (sc, bs, d) ->
    let field (f : l Match.field_binding) =
      {fb_name = f.name; fb_type = ty f.type_; fb_used = f.used; fb_binder = f.binder}
    in
    let branch (b : l Match.branch) =
      { smb_ctor_type = ty b.ctor_type;
        smb_var = b.var;
        smb_field_bindings = list field b.field_bindings;
        smb_extra_conds = list expr b.extra_conditions;
        smb_body = stmts b.body }
    in
    Smatch
      ( {sc_expr = expr sc.expr; sc_access = access sc.access; sc_owned = sc.owned; sc_flat = sc.flat},
        list branch bs,
        opt stmts d )
  | Foreign_block b ->
    Sblock_custom (b.custom, b.template, b.result, ty b.result_type, list expr b.values, list ty b.type_args, b.binder)

let invocation (i : l Invocation.t) : invocation =
  {inv_callable = value_category i.callable; inv_args = list (fun (c, t) -> (value_category c, ty t)) i.args}

let parameter_kind : l Parameter_kind.t -> template_type = function
  | Typename -> TTtypename
  | Typename_default t -> TTtypename_default (ty t)
  | Template n -> TTtemplate n
  | Callable_declared (ds, c) -> TTfun (list ty ds, ty c)
  | Invocable (is, r) -> TTinvocable (list invocation is, ty r)
  | Concept (r, ts) -> TTconcept (r, list ty ts)

let tparams ps = list (fun (k, x) -> (parameter_kind k, x)) ps
let typed ps = list (fun (x, t) -> (x, ty t)) ps

let method_field (m : l Method.t) : method_field =
  { mf_name = m.name;
    mf_globref = m.globref;
    mf_tparams = tparams m.type_params;
    mf_ret_type = ty m.return_type;
    mf_params = typed m.params;
    mf_body = stmts m.body;
    mf_receiver = receiver m.receiver;
    mf_is_inline = m.is_inline;
    mf_no_pure = m.no_pure;
    mf_constexpr = constexpr m.constexpr;
    mf_is_noexcept = m.is_noexcept;
    mf_is_conversion = m.is_conversion;
    mf_binders = m.binders;
    mf_receiver_binder = m.receiver_binder;
    mf_loop = m.loop }

let out_of_line : l Out_of_line.t -> out_of_line_member = function
  | Method m -> OLmethod (method_field m)
  | Destructor ss -> OLdestructor (stmts ss)

let rec field : l Field.t -> cpp_field = function
  | Data (x, t) -> Fvar (x, ty t)
  | Entity_data (r, t) -> Fvar' (r, ty t)
  | Method m -> Fmethod (method_field m)
  | Constructor c ->
    Fconstructor
      { fc_tparams = tparams c.type_params;
        fc_params = typed c.params;
        fc_inits = list (fun (x, e) -> (x, expr e)) c.inits;
        fc_body = stmts c.body;
        fc_explicit = c.explicit;
        fc_noexcept = c.noexcept }
  | Destructor ss -> Fdestructor (stmts ss)
  | Nested_struct (x, ms) -> Fnested_struct (x, list member ms)
  | Deferred_struct d -> Fdeferred_struct {dfs_name = d.name; dfs_selves = typed d.selves; dfs_fields = typed d.fields}
  | Nested_type_alias (ps, x, t) -> Fnested_using (tparams ps, x, ty t)
  | Out_of_line_declaration m -> Fmember_decl (out_of_line m)
  | Deleted_default_constructor -> Fdeleted_ctor
  | Defaulted_special_members -> Fdefaulted_special_members

and member (f, v, s) = (field f, visibility v, section s)

let wrapper (w : Namespace.wrapper) : nspace_wrapper = {nw_ref = w.ref_; nw_merges = w.merges}

let dstruct (s : l Struct.t) : dstruct =
  { ds_ref = s.ref_;
    ds_fields = list member s.fields;
    ds_tparams = tparams s.type_params;
    ds_constraint = opt expr s.constraint_;
    ds_needs_shared_from_this = s.needs_shared_from_this }

let path_entry (r, ts) = (r, list ty ts)

let dfun (f : l Function.t) : dfun =
  { df_path = {dp_outer = path_entry f.path.outer; dp_inner = list path_entry f.path.inner};
    df_ret = ty f.return_type;
    df_no_pure = f.no_pure;
    df_constexpr = constexpr f.constexpr;
    df_shape =
      ( match f.shape with
      | Definition (ps, body) -> Ddef (typed ps, stmts body)
      | Declaration ps -> Ddecl (list (fun (x, t) -> (x, ty t)) ps) );
    df_binders = f.binders;
    df_loop = f.loop }

let rec decl : l Decl.t -> cpp_decl = function
  | Template (ps, c, d) -> Dtemplate (tparams ps, opt expr c, decl d)
  | Namespace (w, ds) -> Dnspace (opt wrapper w, list decl ds)
  | Function f -> Dfun (dfun f)
  | Struct s -> Dstruct (dstruct s)
  | Variable v -> Dasgn {da_ref = v.ref_; da_type = ty v.type_; da_init = expr v.init; da_constexpr = constexpr v.constexpr}
  | Concept (r, e) -> Dconcept (r, expr e)
  | Static_assert (e, m) -> Dstatic_assert (expr e, m)
  | Type_alias a -> Dusing {du_tparams = tparams a.type_params; du_name = a.name; du_rhs = opt ty a.rhs; du_note = a.note}
  | Struct_forward_declaration (ps, r) -> Dstruct_fwd (tparams ps, r)
  | Merged_struct_members s -> Dfields (dstruct s)
  | Member_definition m ->
    Dmember_def
      { dm_owner = m.owner;
        dm_enclosing = opt wrapper m.enclosing;
        dm_tparams = tparams m.type_params;
        dm_field = out_of_line m.member }
  | Enum e -> Denum {de_ref = e.ref_; de_ctors = e.ctors; de_ctor_rocq_names = e.rocq_names; de_tparams = tparams e.type_params}

let template_parameters = tparams
