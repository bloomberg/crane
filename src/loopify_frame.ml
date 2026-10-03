(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Frame-based loopification of non-tail recursion for {!Loopify}: explicit
    frame stacks, continuations, multi-call decomposition, and the bodies the
    machine adopts as extra entry points. *)

open Names
open Minicpp
open Loopify_analysis
open Loopify_tail
open Loopify_tmc

(** {3 Frame-based non-tail recursion helpers} *)

(** Derive field names from saved expressions. If an expression is [CPPvar id],
    use that variable name; otherwise fall back to ["_s{j}"]. Deduplicates by
    appending numeric suffixes when the same name appears more than once. *)
let derive_field_names (exprs : cpp_expr list) : Id.t list =
  let raw_names =
    List.mapi (fun j e ->
      match e with
      | CPPvar id -> Id.to_string id
      | CPPmove (CPPvar id) -> Id.to_string id
      | CPPaccess_call (_, CPPvar id, _, []) -> Id.to_string id
      | CPPaccess (_, _, field_id) -> Id.to_string field_id
      | CPPderef (CPPvar id) -> Id.to_string id
      | CPPfun_call (_, _, {rev = [CPPvar id]}) -> Id.to_string id
      | CPPfun_call (_, _, {rev = [CPPmove (CPPvar id)]}) -> Id.to_string id
      | _ -> "_s" ^ string_of_int j)
    exprs
  in
  (* Count occurrences of each name *)
  let counts = Hashtbl.create 8 in
  List.iter (fun name ->
    let c = try Hashtbl.find counts name with Not_found -> 0 in
    Hashtbl.replace counts name (c + 1))
    raw_names;
  (* Assign unique names: if a name appears once, use it as-is;
     if it appears multiple times, append _0, _1, ... *)
  let next_idx = Hashtbl.create 8 in
  List.map (fun name ->
    if Hashtbl.find counts name = 1 then
      Id.of_string name
    else begin
      let idx = try Hashtbl.find next_idx name with Not_found -> 0 in
      Hashtbl.replace next_idx name (idx + 1);
      Id.of_string (name ^ "_" ^ string_of_int idx)
    end)
    raw_names

(** One value a frame saves across the recursive call.

    The three facts about a saved value — what it is called in the frame
    struct, what its type is, and which expression produced it — used to be
    three lists that every reader indexed in parallel with [List.nth].  They
    are one record per value now, so a frame whose names and types have
    drifted out of step is not a thing that can be built. *)
type saved_slot = {
  ss_field : Id.t;
      (** field name in the frame struct (see {!derive_field_names}) *)
  ss_ty : cpp_type;
      (** the declared type, or [Tunresolved] when the frame was built before
          the type was known, in which case {!ss_expr} recovers it *)
  ss_expr : cpp_expr;  (** the saved expression *)
}

(** A collected call frame — saved values + handler body. *)
type call_frame_info = {
  cf_name : string;
      (** e.g. "_Resume0" — assigned when the push statement is generated *)
  cf_slots : saved_slot list;
  cf_env : (Id.t * cpp_type) list;
      (** type env at frame creation, for decltype resolution *)
  cf_handler : cpp_stmt list;
}

(** [make_slots ~types ~exprs] pairs a frame's saved types with the
    expressions that produced them and names each one.

    Naming is {!derive_field_names} over the whole list, so it has to happen
    here rather than per slot: the names are deduplicated against each other.
    This is the only way to build a slot list, which is what makes the three
    lists impossible to desynchronise. *)
let make_slots ~types ~exprs =
  let names = derive_field_names exprs in
  map3_exn ~what:"make_slots"
    (fun ss_field ss_ty ss_expr -> {ss_field; ss_ty; ss_expr})
    names types exprs

let cf_field_names cf = List.map (fun s -> s.ss_field) cf.cf_slots
let cf_saved_types cf = List.map (fun s -> s.ss_ty) cf.cf_slots
let cf_saved_exprs cf = List.map (fun s -> s.ss_expr) cf.cf_slots

(** Type environment for inferring saved expression types. *)

(** Collect type bindings from a list of statements. Handles
    [Sasgn(id, Declare ty, _)] and [Sdecl(id, ty)]. Also recurses into
    Scustom_case
    branches to pick up pattern-bound variables. *)
let rec collect_type_env (stmts : cpp_stmt list) : (Id.t * cpp_type) list =
  List.concat_map
    (fun s ->
      match s with
      | Sasgn (id, Declare Tauto, CPPlambda
        { cl_params = params;
          cl_ret = ret_ty_opt;
          _ }) ->
        let param_types =
          List.rev_map (fun (t, _) -> strip_ref_and_const_type t) (to_reversed params)
        in
        let ret_ty = match ret_ty_opt with
          | Some t when t <> Tvoid -> t
          | _ -> Tvoid
        in
        [(id, Tfun (param_types, ret_ty))]
      | Sasgn (id, Declare ty, _) -> [(id, ty)]
      | Sdecl (id, ty) -> [(id, ty)]
      | Scustom_case (_, _, _, branches, _) ->
        List.concat_map
          (fun (ps, _, body) -> ps @ collect_type_env body)
          branches
      | Sif (_, then_br, else_br) ->
        collect_type_env then_br @ collect_type_env else_br
      | Smatch (scrut, branches, default) ->
        List.concat_map
          (fun br ->
            (* Register structured-binding field types so that
               [infer_saved_type] can resolve them for frame structs. *)
            let field_type_bindings =
              List.map
                (fun (bname, ty, _) -> (bname, ty))
                br.smb_field_bindings
            in
            (* Also register the aggregate binding for frame-dispatch
               branches (which use [smb_var] without structured bindings). *)
            let var_binding =
              match br.smb_var with
              | Some id when br.smb_field_bindings = [] ->
                [(id, Tconst (br.smb_ctor_type))]
              | _ -> []
            in
            field_type_bindings @ var_binding
            @ collect_type_env br.smb_body )
          branches
        @ (match default with Some ss -> collect_type_env ss | None -> [])
      | Sblock ss -> collect_type_env ss
      | _ -> [] )
    stmts

(** Collect expression bindings: maps id to its RHS for [Sasgn(id, _, rhs)] entries.
    Recurses into [Smatch] branches, [Sif] branches, and [Sblock] to find all
    bindings.  Used to look through intermediate bindings in pointer-safe analysis
    (e.g., to detect [x = *(sp)] and treat a recursive call passing [CPPvar x] as
    equivalent to passing [CPPderef sp]). *)
let rec collect_binding_env (stmts : cpp_stmt list) : (Id.t * cpp_expr) list =
  List.concat_map
    (fun s ->
      match s with
      | Sasgn (id, _, expr) -> [(id, expr)]
      | Smatch (scrut, branches, default) ->
        List.concat_map (fun br -> collect_binding_env br.smb_body) branches
        @ (match default with Some ss -> collect_binding_env ss | None -> [])
      | Sif (_, then_br, else_br) ->
        collect_binding_env then_br @ collect_binding_env else_br
      | Sblock ss -> collect_binding_env ss
      | _ -> [])
    stmts

(** Look up a variable's type in the environment. *)
let lookup_var_type env id = List.assoc_opt id env

(** Given template parameters and a type variable id, find the return type of a
    TTfun constraint if the template param is function-typed. *)
let lookup_tparam_return_type tparams id =
  match lookup_tparam_fun_type tparams id with
  | Some (Tfun (_, cod)) -> Some cod
  | _ -> None

(** The C++ [bool] type, as the printer spells it. *)
let ty_bool = Tid_external ("bool", [])

(** Whether a binary operator's result is [bool] whatever its operands are.
    Comparisons and the short-circuiting connectives are the ones that do not
    hand their operand's type back. *)
let binop_yields_bool = function
  | Beq | Bneq | Band | Bor -> true
  | Bassign -> false

(** The raw-pointer type an owning or raw pointer decays to.  Both
    [crane_raw(x)] and [x.get()] answer this way.  [None] for anything that is
    not a pointer, which has no raw form to decay to. *)
let as_raw_ptr = function
  | Tptr t | Tshared_ptr t -> Some (Tptr t)
  | _ -> None

(** Infer the C++ type of a saved CPP expression bottom-up, or [None] when
    there is nothing to go on.

    Not knowing is an ordinary answer here, so it is one the type admits: this
    walks expressions the loopifier saved into a frame, and a variable it never
    saw bound, or a call through a global, simply cannot be typed from what is
    in hand.  Callers that need a type anyway fall back at their own boundary
    -- see {!infer_saved_types}.

    Handles the common cases: variable lookups, smart-pointer derefs,
    arithmetic inlined operators (detected by their format-string pattern),
    and lambdas (return type inferred from body [Sreturn] statements).
    Used by [compute_frame_field_types] to emit [std::function<R(Args...)>]
    instead of [decltype(lambda)] for closures in loopification frame structs. *)
let rec infer_saved_type tparams (env : (Id.t * cpp_type) list) (e : cpp_expr) :
    cpp_type option =
  match e with
  | CPPvar id ->
    (* A forwarding parameter's value is held at [std::decay_t<F>]: its [F]
       may be deduced as a reference. *)
    Option.map
      (function Tref (Forwarding, t) -> Tdecay (strip_ref_type t) | t -> strip_ref_type t)
      (lookup_var_type env id)
  | CPPmove inner -> infer_saved_type tparams env inner
  | CPPderef inner ->
    (* Peel the qualifiers off the pointer before taking its pointee: the
       loopified receiver [_self] has type [const T *], and
       [strip_ref_and_const_type] deliberately keeps the [const] on such a
       type.  Missing the pointee would give the saved frame field the
       pointer's type while the push and the handler both use it as a
       value. *)
    let rec pointee = function
      | Tref (_, t) | Tconst t -> pointee t
      | Tshared_ptr t | Tptr t -> t
      | t -> t
    in
    Option.map pointee (infer_saved_type tparams env inner)
  | CPPbinop (op, _, _) when binop_yields_bool op -> Some ty_bool
  (* [&x] points at whatever [x] is, its [const] kept. *)
  | CPPunop (Uaddr, inner) ->
    Option.map (fun t -> Tptr t) (infer_saved_type tparams env inner)
  | CPPbinop (_, lhs, rhs) ->
    (* An arithmetic or assignment operator hands back an operand's type.
       Try left first, fall back to right: this handles the common pattern
       [(d_a1 + n)] where [d_a1] is not in env but [n] (a lambda param) is,
       and the result type matches the param type. *)
    ( match infer_saved_type tparams env lhs with
    | Some _ as ty -> ty
    | None -> infer_saved_type tparams env rhs )
  | CPPlit (ty, _) -> Some (strip_ref_and_const_type ty)
  (* A primitive string literal is a [std::string], as its ML type [Tstring]
     converts. *)
  | CPPstring _ -> Some (Tid_external ("std::string", []))
  | CPPbool _ -> Some ty_bool
  | CPPglob (_, _, Some {ci_yields = Some ty; _}) ->
    (* Translation recorded what the reference evaluates to while the
       global's ML type was in hand; nothing here can improve on it. *)
    Some (strip_ref_and_const_type ty)
  | CPPfun_call ({cs_yields = Ryields ty; _}, _, _) ->
    (* The call says what it yields; nothing below can improve on that, and
       a guess that disagreed with it would be a bug. *)
    Some (strip_ref_and_const_type ty)
  | CPPfun_call (_, CPPrt Crane_rt.Raw, {rev = [ inner ]}) ->
    (* crane_raw(x) returns a raw pointer, whether [x] was a shared_ptr or
       already raw (arena mode).  Infer from the inner expression. *)
    Option.bind (infer_saved_type tparams env inner) as_raw_ptr
  | CPPfun_call (_, CPPvar f, _) ->
    ( match lookup_var_type env f with
    | Some (Tfun (_, cod)) -> Some cod
    | Some ty ->
      (* f might be a template param with forwarding ref type *)
      Option.bind (extract_fwd_ref_tvar ty) (lookup_tparam_return_type tparams)
    | None -> None )
  | CPPfun_call (_, CPPnamespace (_, CPPvar f), _) ->
    ( match lookup_var_type env f with
    | Some (Tfun (_, cod)) -> Some cod
    | _ -> None )
  | CPPfun_call (_, CPPlambda {cl_ret = Some ret_ty; _}, _) -> Some ret_ty
  (* A lambda applied in place yields what its body returns. *)
  | CPPfun_call (_, (CPPlambda _ as l), _) -> (
    match infer_saved_type tparams env l with
    | Some (Tfun (_, cod)) -> Some cod
    | _ -> None )
  | CPPfun_call (_, CPPaccess (Adot, inner, id), {rev = []})
    when String.equal (Id.to_string id) "get" ->
    (* shared_ptr::get() returns a raw pointer.
       Infer from the inner expression. *)
    Option.bind (infer_saved_type tparams env inner) as_raw_ptr
  | CPPfun_call _ -> None
  | CPPconverting_ctor (ty, _) | CPPbox (ty, _) ->
    Some (strip_ref_and_const_type ty)
  (* A record field read says what the field is. *)
  | CPPget' (_, _, Some ty) -> Some (strip_ref_and_const_type ty)
  | CPPlambda {cl_params = params; cl_ret = ret_ty_opt; cl_body = body; _} ->
    let param_types = List.rev_map fst (to_reversed params) in
    let ret_ty =
      match ret_ty_opt with
      | Some ty when ty <> Tvoid -> Some ty
      | _ ->
        (* No recorded return type.  Ten construction sites in
           [translation.ml] still build a lambda without one, so the body's
           [Sreturn] statements remain the only answer available here; each
           site that learns to record its type retires a little more of
           this. *)
        let lam_env =
          collect_type_env body
          @ List.fold_left
              (fun acc (ty, id_opt) ->
                match id_opt with
                | Some id -> (id, ty) :: acc
                | None -> acc)
              env (to_reversed params)
        in
        (* The first [return] that can be typed answers for the whole body --
           in any branch, a match's included: a lambda over a pair opens with
           the structured binding that destructures it.  A branch's own
           bindings are not in [lam_env], so a [return] reading one of them
           may go untyped and leave the answer to another. *)
        let rec of_stmt = function
          | Sreturn (Some e) -> infer_saved_type tparams lam_env e
          | Sif (_, then_body, else_body)
          | Sif_decl (_, _, _, then_body, else_body) ->
            List.find_map of_stmt (then_body @ else_body)
          | Sblock stmts -> List.find_map of_stmt stmts
          | Smatch (_, branches, default) ->
            List.find_map of_stmt
              (List.concat_map (fun b -> b.smb_body) branches
              @ Option.default [] default)
          | Scustom_case (_, _, _, branches, _) ->
            List.find_map of_stmt
              (List.concat_map (fun (_, _, body) -> body) branches)
          | Sswitch (_, _, branches, default) ->
            List.find_map of_stmt
              (List.concat_map snd branches @ Option.default [] default)
          | _ -> None
        in
        List.find_map of_stmt body
    in
    Option.map
      (fun r ->
        Tfun
          ( List.map strip_ref_and_const_type param_types,
            strip_ref_and_const_type r ) )
      ret_ty
  | _ -> None

let free_vars_expr = Minicpp.free_vars_expr
let free_vars_stmt = Minicpp.free_vars_stmt
let free_vars_body = Minicpp.free_vars_body

let subst_var_stmts old_id new_id stmts =
  List.map (subst_stmt [(old_id, new_id)]) stmts

(** Substitute [CPPderef (CPPvar target_id)] with [CPPvar target_id] throughout
    an expression, statement, or statement list.

    When {!Translation.gen_local_fix_shared_ptr} generates a
    shared_ptr fixpoint, all call sites use dereferenced calls
    (i.e. [CPPfun_call(CPPderef(CPPvar f), args)]).  After
    {!loopify_inner_lambdas} converts the recursion into a loop, the
    indirection is no longer needed.  This function strips the [CPPderef]
    wrapper so subsequent code sees plain [CPPvar f] calls and the emitted
    C++ uses direct calls instead of dereferenced ones. *)
let rec un_deref_var_expr target_id e =
  let fe e = un_deref_var_expr target_id e in
  match e with
  | CPPderef (CPPvar id) when Id.equal id target_id -> CPPvar id
  | _ -> Minicpp.map_expr fe (un_deref_var_stmt target_id) (fun t -> t) e

and un_deref_var_stmt target_id s =
  let fe e = un_deref_var_expr target_id e in
  let fs s = un_deref_var_stmt target_id s in
  Minicpp.map_stmt fe fs (fun t -> t) s

let un_deref_var_stmts target_id stmts =
  List.map (un_deref_var_stmt target_id) stmts

(** {3 Continuation variable helpers}

    When a recursive call occurs mid-statement-sequence (e.g., [let x = f(n) in
    rest]), the "rest" statements form a continuation. Variables that are free in
    [rest] but defined before it must be saved in the call frame and restored in
    the handler. These helpers factor out the repeated pattern of computing,
    filtering, binding, and registering continuation variables. *)

(** Compute the free variables of a continuation (the "rest" of a statement
    sequence). Excludes variables that are defined within [rest] itself and
    the special [_result] accumulator.

    @param rest The remaining statements (the continuation)
    @return Sorted, unique list of free variable [Id.t] values *)
let compute_rest_free_vars rest =
  let rest_defined =
    List.filter_map
      (function
        | Sasgn (vid, _, _) -> Some vid
        | Sdecl (vid, _) -> Some vid
        | _ -> None)
      rest
  in
  List.concat_map free_vars_stmt rest
  |> List.filter (fun v -> not (List.exists (Id.equal v) rest_defined))
  |> List.sort_uniq (fun a b -> Id.compare a b)

(** Filter continuation free variables, removing the assigned variable and
    the [_result] accumulator.

    @param exclude_id The variable being assigned (not needed in continuation)
    @param rest_free The free variables of the continuation
    @return Filtered list of continuation variables *)
let filter_cont_vars ~exclude_id rest_free =
  List.filter
    (fun fv ->
      (not (Id.equal fv exclude_id))
      && not (Id.equal fv (id_result)))
    rest_free

(** Generate statements that bind continuation variables from frame fields.
    Produces [<type> <name> = _f._s<offset+i>;] for each continuation variable.

    @param offset Starting field index in the frame
    @param cont_vars The continuation variable names
    @param cont_types Their types (parallel to [cont_vars])
    @return List of raw C++ binding statements *)
let make_cont_bindings ~offset ~field_names cont_vars cont_types =
  List.mapi
    (fun i id ->
      let ty = List.nth cont_types i in
      let field_expr =
        CPPaccess (Adot, CPPvar (id_f),
                   List.nth field_names (offset + i))
      in
      match ty with
      | Tshared_ptr _ -> Sasgn (id, Declare ty, CPPmove field_expr)
      | Tunresolved -> Sasgn (id, Existing, field_expr)
      | Tconst inner when not (is_trivially_copyable_type inner) ->
        Sasgn (id, Declare (Tref (Lvalue, Tconst inner)), field_expr)
      | t when not (is_trivially_copyable_type t) ->
        (* Move from frame field to avoid O(n) deep copy of owned value types
           (e.g. [List<T>]).  Safe because [_f] was obtained via
           [std::move(std::get<...>(_frame))] and this field is not used again. *)
        Sasgn (id, Declare ty, CPPmove field_expr)
      | Tvar _ ->
        (* Template type parameter (e.g. [F0] from [F0 &&f]).  When [F0] is
           deduced as a reference type, [F0 f = std::move(_f.f)] would be
           ill-formed — a non-const lvalue reference cannot bind to an rvalue.
           Use [auto] so the declared type is always deduced as a value type,
           regardless of whether [F0] was a reference or function type. *)
        Sasgn (id, Declare Tauto, CPPmove field_expr)
      | _ -> Sasgn (id, Declare ty, field_expr))
    cont_vars

(** Build a type environment from continuation variables and their types,
    prepended to an existing environment.

    @param cont_vars Continuation variable names
    @param cont_types Their types (parallel to [cont_vars])
    @param env The existing type environment
    @return Extended type environment *)
let make_cont_env cont_vars cont_types env =
  map2_exn ~what:"make_cont_env" (fun id ty -> (id, ty)) cont_vars cont_types @ env

(** Register a call frame in the mutable [frames_ref] accumulator.

    @param frames_ref Mutable reference to the list of collected frames
    @param name Frame struct name (e.g., ["_Resume0"])
    @param saved_types Types of saved expressions
    @param saved_exprs The saved expressions (for decltype fallback)
    @param env Type environment at frame creation point
    @param handler The handler body statements *)
let register_frame frames_ref ~name ~saved_types ~saved_exprs ~env ~handler =
  frames_ref :=
    !frames_ref
    @ [{cf_name = name;
        cf_slots = make_slots ~types:saved_types ~exprs:saved_exprs;
        cf_env = env; cf_handler = handler}]

(** {3 Frame-based non-tail rewrite}

    Rewrite the body for the Enter handler, replacing recursive returns with
    frame pushes. Collects [call_frame_info] for each call site so that the
    caller can generate the corresponding handler lambdas.

    The [call_counter] ref assigns sequential IDs (starting from 1). The
    [frames_ref] accumulates call frame info in order. *)

(** Build a stack push expression. Uses
    [CPPfun_call (CPPaccess (Adot, ...))] so that
    [CPPvar "_stack"] is visible to capture detection (ensuring [[&]] capture),
    and renders with [.] not [->]. *)
let make_stack_push arg =
  Sexpr
    (CPPfun_call
       (call_opaque, CPPaccess (Adot, CPPvar (id_stack), id_emplace_back),
         of_reversed [arg] ) )

(** Read the [i]-th saved field from frame variable [_f] using the given
    [names] list. Generates [_f.<name>] where [<name>] is [List.nth names i]. *)
let frame_field_named names i =
  CPPaccess (Adot, CPPvar (id_f), List.nth names i)

(** Read [n] consecutive saved fields from frame [_f] using [names],
    starting at [offset]. *)
let frame_fields_named ?(offset = 0) names n =
  List.init n (fun i -> frame_field_named names (offset + i))

(** Prepare an expression for saving in a continuation frame.
    [shared_ptr] values are ref-counted and can be copied directly.
    Other non-trivially-copyable lvalues (e.g. [std::function], value-type
    inductives) are std::moved into the frame, except bare variables.
    Trivially-copyable types are copied cheaply. *)
let move_for_frame ty expr =
  (* [std::move] is only meaningful on an lvalue.  Wrapping a prvalue -- a call
     result, a constructor call, a lambda -- cannot save a copy and actively
     blocks copy elision, which clang reports as -Wpessimizing-move (an error
     under the test suite's -Werror).  Moves of such expressions used to slip
     through unnoticed on types whose drain destructor had suppressed the move
     constructor, because the "move" silently resolved to the copy. *)
  let is_lvalue = function
    | CPPvar _ | CPPderef _ | CPPaccess (Adot, _, _) -> true
    | _ -> false
  in
  match ty with
  | Tshared_ptr _ -> expr
  | Tconst _ -> expr
  | t when not (is_trivially_copyable_type t) ->
    (match expr with
    (* A bare variable is left alone: a later push may still read it, and
       [optimize_frame_push_args] moves it at its last push.  A dereferenced
       pointer is a borrow of someone else's cell. *)
    | CPPvar _ | CPPderef _ -> expr
    | e when is_lvalue e -> CPPmove e
    | _ -> expr)
  | _ -> expr

(** Apply [move_for_frame] to parallel type and expression lists. *)
let move_for_frame_list types exprs =
  List.map2 move_for_frame types exprs

(** {4 Frame construction helpers}

    These helpers reduce code duplication when constructing frame instances and
    managing the frame counter. *)

(** Extract a short constructor name from a [cpp_type], for use in frame
    name suffixes. Returns [None] for types that don't have a clear short name. *)
let ctor_type_short_name : cpp_type -> string option = function
  | Tid (id, _) -> Some (Id.to_string id)
  | Tqualified (_, id) -> Some (Id.to_string id)
  | _ -> None

(** Generate a unique call frame name from a role prefix (e.g. ["_Resume"],
    ["_After"], ["_Combine"]) and optional branch context.

    When [branch_ctx] is [Some "Node"], produces ["_Resume_Node"] instead of
    ["_Resume0"].  Falls back to a numeric suffix when no context is available.
    The [seen] table tracks used names for deduplication: if a context-derived
    name collides, a numeric suffix is appended (["_Resume_Node_1"]). *)
let make_call_frame_name (prefix : string) (counter : int ref)
    (seen : (string, int) Hashtbl.t) ?(branch_ctx : string option) () : string =
  let id = !counter in
  counter := id + 1;
  let candidate = match branch_ctx with
    | Some s -> prefix ^ "_" ^ s
    | None -> prefix ^ string_of_int id
  in
  let n = try Hashtbl.find seen candidate with Not_found -> 0 in
  Hashtbl.replace seen candidate (n + 1);
  if n = 0 then candidate
  else candidate ^ "_" ^ string_of_int n

(** Construct an [_Enter] frame expression with the given arguments.

    Generates [_Enter\{arg1, arg2, ...\}] as a [CPPstruct_id] expression.

    @param args The arguments to save in the Enter frame (typically function parameters)
    @return A [CPPstruct_id] expression representing the frame instance *)

(** Batch-infer types for a list of saved expressions.

    @param tparams Template parameters context
    @param env Type environment for variable lookups
    @param exprs The expressions whose types to infer
    @return A list of inferred [cpp_type] values, parallel to [exprs]

    This is the boundary where not knowing becomes {!Minicpp.Tunresolved}: a
    frame field's declared type is a slot that has to hold something, and
    [Tunresolved] is what the rest of the frame machinery reads as "not settled
    yet". *)
let infer_saved_types tparams env exprs =
  List.map
    (fun e -> Option.default Tunresolved (infer_saved_type tparams env e))
    exprs

(** Search through an argument list for an element matching [search_fn].

    Iterates left-to-right through [args] applying [search_fn] to each element.
    On the first match, returns [Some (result, rebuild)] where [result] is the
    value produced by [search_fn] and [rebuild] is a function that reconstructs
    the full argument list with a replacement element at the matched position.
    Returns [None] if no element matches.

    This enables "find and replace in context" patterns: locate a subexpression
    within a function's arguments, transform it, and rebuild the outer call.

    @param search_fn Predicate/extractor applied to each argument
    @param args      The argument list to search
    @return [Some (result, rebuild)] on match, [None] otherwise. [rebuild] takes
            a replacement expression and returns the full argument list with that
            element substituted at the matched position. *)
let search_in_args search_fn args =
  let rec try_args rev_pre = function
    | [] -> None
    | arg :: post ->
    match search_fn arg with
    | Some result -> Some (result, fun x -> List.rev rev_pre @ [x] @ post)
    | None -> try_args (arg :: rev_pre) post
  in
  try_args [] args

(** Find an immediately-invoked lambda expression (IIFE) containing recursive
    calls. Returns [(body, ret_ty, rebuild)] where [rebuild] wraps a result
    expression back into the surrounding context. *)
let rec find_inner_iife check = function
  | CPPfun_call (_, CPPlambda
    { cl_params = {rev = []};
      cl_ret = ret_ty;
      cl_body = body;
      cl_capture = _cap }, {rev = []})
    when collect_stmts check ~in_visitor:false body <> [] ->
    Some (body, ret_ty, Fun.id)
  | CPPfun_call (res, f, args) ->
    ( match search_in_args (find_inner_iife check) (to_reversed args) with
    | Some ((body, ret_ty, rebuild), mk_args) ->
      Some (body, ret_ty, fun x -> CPPfun_call (res, f, of_reversed (mk_args (rebuild x))))
    | None -> None )
  | CPPmove e ->
    ( match find_inner_iife check e with
    | Some (body, ret_ty, rebuild) ->
      Some (body, ret_ty, fun x -> CPPmove (rebuild x))
    | None -> None )
  | CPPstruct_id (name, tys, args) ->
    ( match search_in_args (find_inner_iife check) args with
    | Some ((body, ret_ty, rebuild), mk_args) ->
      Some (body, ret_ty, fun x -> CPPstruct_id (name, tys, mk_args (rebuild x)))
    | None -> None )
  | CPPstructmk (name, tys, args) ->
    ( match search_in_args (find_inner_iife check) args with
    | Some ((body, ret_ty, rebuild), mk_args) ->
      Some (body, ret_ty, fun x -> CPPstructmk (name, tys, mk_args (rebuild x)))
    | None -> None )
  | _ -> None

(** Handle a base-case expression (0 direct recursive calls) that may contain
    recursive calls hidden inside a nested IIFE.

    When {!find_inner_iife} finds an immediately-invoked lambda, each of its
    [Sreturn (Some result)] statements is wrapped with [rebuild] so the
    surrounding expression context is preserved, then the body is rewritten via
    [rewrite_iife_body].  Otherwise this falls back to [base_case e].

    @param check              Call checker identifying recursive calls
    @param e                  Expression with 0 direct calls to check
    @param rewrite_iife_body  Rewriter for IIFE bodies:
                              [extended_body -> rewritten_body]
    @param base_case          Fallback for true base cases (no inner calls) *)
let rewrite_base_with_inner_calls check e ~rewrite_iife_body ~base_case =
  let rec wrap_returns_with rebuild body =
    List.map
      (fun stmt ->
        match stmt with
        | Sreturn (Some result) -> Sreturn (Some (rebuild result))
        | Sif (cond, t, e) ->
          Sif (cond, wrap_returns_with rebuild t, wrap_returns_with rebuild e)
        | Sif_decl (id, ty, init, t, e) ->
          Sif_decl (id, ty, init, wrap_returns_with rebuild t, wrap_returns_with rebuild e)
        | Sblock stmts -> Sblock (wrap_returns_with rebuild stmts)
        | Sswitch (scrut, r, branches, default) ->
          Sswitch (scrut, r,
            List.map (fun (lbl, b) -> (lbl, wrap_returns_with rebuild b)) branches,
            Option.map (wrap_returns_with rebuild) default)
        | Smatch (scrut, branches, default) ->
          Smatch (
            scrut,
            List.map (fun br -> { br with smb_body = wrap_returns_with rebuild br.smb_body }) branches,
            Option.map (wrap_returns_with rebuild) default)
        | Scustom_case (ty, scrut, tyargs, branches, err) ->
          Scustom_case (ty, scrut, tyargs,
            List.map (fun (pats, ret_ty, b) -> (pats, ret_ty, wrap_returns_with rebuild b)) branches,
            err)
        | s -> s )
      body
  in
  match find_inner_iife check e with
  | Some (iife_body, _iife_ret_ty, rebuild) ->
    let extended_body = wrap_returns_with rebuild iife_body in
    rewrite_iife_body extended_body
  | None ->
    base_case e

(** {3 Enter-rewrite context} *)

(** One parameter a frame carries, and how the frame holds it: [fp_pointer_safe]
    says the caller's value outlives the frame, so the field is a pointer to it
    rather than a copy.

    The flag lives in the parameter because every reader needs the two
    together -- the field's type, the push argument and the handler's binding
    each depend on both -- and a mask beside the list is one more thing to keep
    in step. *)
type frame_param = {
  fp_name : Id.t;
  fp_ty : cpp_type;
  fp_pointer_safe : bool;
}

(** One entry point of a frame machine.

    An entry is what a call needs in order to become a stack push: the
    [_Enter]-style frame struct that entering it goes through, the parameters
    that entry binds, and the mask saying which of them vary across calls and
    so have to be carried in the frame. A function loopified on its own has a
    single entry; the representation is a table so that an enclosing function
    and a body adopted from it can share one stack, each entering through its
    own frame.

    The parameters live here rather than beside the entry because everything
    the machine derives per entry -- which arguments a frame carries, and at
    which types -- is a function of the two together. Build one with
    {!machine_entry}, which checks that the mask describes those parameters. *)
type machine_entry = {
  en_enter_id : Id.t;  (** Frame struct entering this point goes through *)
  en_params : (Id.t * cpp_type) list;  (** The parameters this entry binds *)
  en_varying : bool list;  (** Mask over {!en_params} *)
}

(** An entry binding [params], entered through [enter_id], carrying the
    positions [varying] selects. *)
let machine_entry ~enter_id ~params ~varying =
  ignore
    (map2_exn ~what:"a machine entry's varying mask" (fun _ _ -> ()) varying
       params );
  {en_enter_id = enter_id; en_params = params; en_varying = varying}

(** The parameters [en] carries in its frame: those that vary across calls.
    The invariant ones are in scope at the handler already. *)
let entry_varying_params en = filter_by_mask en.en_varying en.en_params

(** The types of {!entry_varying_params}, the layout of [en]'s frame. *)
let entry_varying_types en = List.map snd (entry_varying_params en)

(** Everything one entry point contributes to the emitted machine: the frame
    struct its callers push, the parameters it carries and how it holds each
    of them, and the handler the dispatch loop runs on popping one.

    These four travel together -- a struct's fields, their types, their mask
    and the handler that binds them all have to describe the same frame -- so
    they are one record rather than parallel lists indexed by position. *)
type entry_emission = {
  ee_id : Id.t;
  ee_params : frame_param list;
  ee_body : cpp_stmt list;
}

(** What [en] contributes to the machine, given the [body] its handler runs.
    The parameters are read off the entry, so the struct and the frames pushed
    at it cannot disagree about what it carries.  [pointer_safe] defaults to
    all-false: only an entry whose parameters come from the enclosing
    function's own can borrow rather than own them. *)
let entry_emission ?pointer_safe en body =
  let params = entry_varying_params en in
  let params =
    match pointer_safe with
    | None ->
      List.map
        (fun (id, ty) -> {fp_name = id; fp_ty = ty; fp_pointer_safe = false})
        params
    | Some ps ->
      map2_exn ~what:"an entry emission's pointer-safe mask"
        (fun safe (id, ty) ->
          {fp_name = id; fp_ty = ty; fp_pointer_safe = safe} )
        ps params
  in
  {ee_id = en.en_enter_id; ee_params = params; ee_body = body}

(** {3 Bodies the machine adopts as extra entry points} *)

(** A local fixpoint's own name, recovered from its self-parameter [_self_f]. *)
let name_of_self_id self_id =
  let s = Id.to_string self_id in
  String.sub s
    (String.length self_param_prefix)
    (String.length s - String.length self_param_prefix)

(** The statement lists that run as part of evaluating [e]: the bodies of
    immediately-invoked zero-parameter lambdas, collected recursively.

    Translation wraps a Coq [let fix] that appears in argument position in one
    of these, so a fixpoint bound there is part of the enclosing function's
    flow just as much as one bound by a statement.  The body of a lambda that
    is merely {i passed} somewhere is not collected: it runs later, under a
    scope this machine does not control. *)
let invoked_body e =
  match e with
  | CPPfun_call
      (res, CPPlambda ({cl_params = {rev = []}; _} as l), ({rev = []} as noargs))
    ->
    Some
      ( l.cl_body,
        fun body -> CPPfun_call (res, CPPlambda {l with cl_body = body}, noargs)
      )
  | _ -> None

let rec invoked_bodies_expr e =
  let acc = ref (match invoked_body e with Some (b, _) -> [b] | None -> []) in
  Minicpp.iter_expr_children
    ~on_expr:(fun c -> acc := !acc @ invoked_bodies_expr c)
    ~on_stmts:(fun _ -> ())
    e;
  !acc

(** Apply [f] to every expression in [stmts], innermost first.  Unlike the
    searches above this does descend into every lambda: an adopted entry is
    reached by name once installed, and a name has to be rewritten wherever it
    is written. *)
let rec rewrite_exprs f stmts = List.map (rewrite_exprs_stmt f) stmts

and rewrite_exprs_stmt f s =
  map_stmt (rewrite_exprs_expr f) (rewrite_exprs_stmt f) Fun.id s

and rewrite_exprs_expr f e =
  f (map_expr (rewrite_exprs_expr f) (rewrite_exprs_stmt f) Fun.id e)

(** The first hit of [on_stmt] or [on_expr] among the statements that run as
    part of this function's flow.

    Statements are searched throughout -- what is looked for is often bound
    inside a match branch rather than at the body's top level.  Expressions are
    searched only when [on_expr] is given, and then recursively; without it the
    traversal still enters {!invoked_body} lambdas, since translation wraps a
    Coq [let fix] appearing in argument position in one of those.  The body of
    a lambda this function merely {i builds} is never searched: it runs later,
    under a scope this machine does not control. *)
let find_in_flow ?on_stmt ?on_expr stmts =
  let found = ref None in
  let pending () = Option.is_empty !found in
  let try_hit f x = if pending () then found := f x in
  let rec visit stmt =
    if pending () then (
      Option.iter (fun f -> try_hit f stmt) on_stmt;
      if pending () then ignore (map_stmt visit_expr visit Fun.id stmt) );
    stmt
  and visit_expr e =
    if pending () then (
      match on_expr with
      | Some f ->
        try_hit f e;
        if pending () then
          Minicpp.iter_expr_children
            ~on_expr:(fun c -> ignore (visit_expr c))
            ~on_stmts:(fun _ -> ()) e
      | None ->
        List.iter
          (fun body -> List.iter (fun s -> ignore (visit s)) body)
          (invoked_bodies_expr e) );
    e
  in
  List.iter (fun s -> ignore (visit s)) stmts;
  !found

(** Drop the bindings of [ids] wherever they occur in [stmts].

    Once a local fixpoint becomes an entry point of the enclosing machine, the
    lambdas that used to implement it are dead -- and not merely untidy: they
    still hold a call the loopification postcondition would see, so leaving
    them in gets the function reported as declined even though its machine is
    correct. *)
let rec drop_bindings ids stmts =
  let dropped id = List.exists (Id.equal id) ids in
  List.filter_map
    (fun st ->
      match st with
      | Sasgn (id, Declare _, _) when dropped id -> None
      | Sdecl (id, _) when dropped id -> None
      | _ -> Some (map_stmt (drop_bindings_expr ids) (drop_bindings_stmt ids)
                     Fun.id st) )
    stmts

(** [drop_bindings] on a single statement, collapsing a list result into a
    block so that it fits where one statement is expected. *)
and drop_bindings_stmt ids s =
  match drop_bindings ids [s] with
  | [] -> Sblock []
  | [one] -> one
  | many -> Sblock many

(** [drop_bindings] reaching through expressions into the bodies of
    {!invoked_body} lambdas -- the statements the searches above look in, so
    the same ones a dropped binding can hide in. *)
and drop_bindings_expr ids e =
  match invoked_body e with
  | Some (body, rebuild) -> rebuild (drop_bindings ids body)
  | None -> map_expr (drop_bindings_expr ids) Fun.id Fun.id e

(** The binder of the wrapper lambda for the fixpoint bound to [impl_id]: the
    one whose body passes [impl_id] to itself.  Searched over the same flow the
    fixpoint itself is, since translation emits the pair together. *)
let find_fix_wrapper impl_id stmts =
  find_in_flow stmts
    ~on_stmt:(function
      | Sasgn (wid, Declare Tauto, (CPPlambda _ as w))
        when (not (Id.equal wid impl_id))
             && List.exists (Id.equal impl_id) (free_vars_expr w) ->
        Some wid
      | _ -> None )

(** A body this machine adopts as an extra entry point.

    Two shapes reach here: a fixpoint local to the function, and the body of a
    mutual-recursion partner that {!generic_inline_expr} left as an
    immediately-invoked lambda.  Both hold calls that belong to this machine's
    recursion but sit where the [_Enter] rewriter does not go, so neither can
    be linearised by a single-entry machine.

    The machine treats them alike because {!ad_install} makes them alike: it
    rewrites the enclosing body so that, whichever shape the source had, the
    calls that enter the adopted body are calls on the one name
    {!ad_entry_id}.  Everything downstream keys on that name, so there is a
    single way to denote "enter this entry" rather than one per shape. *)
type adopted = {
  ad_name : string;  (** Names the entry's frame, [_Enter_<name>] *)
  ad_entry_id : Id.t;
      (** The synthetic name {!ad_install} routes this entry's calls through *)
  ad_params : (Id.t * cpp_type) list;  (** Parameters, in call-argument order *)
  ad_ret : cpp_type option;
      (** The body's result type, where its lambda records one.  The entry
          shares the machine's one [_result], so it must be the function's. *)
  ad_captures : Id.t list;
      (** Free variables the body takes from the enclosing scope.  The entry's
          frame carries these alongside {!ad_params}: they are in scope for a
          lambda but not for a dispatch loop re-entering it from a popped
          frame. *)
  ad_body : cpp_stmt list;
      (** The entry's handler, already installed: its own recursive calls go
          through {!ad_entry_id} like every other call into this entry. *)
  ad_install : cpp_stmt list -> cpp_stmt list;
      (** Prepare the enclosing body for the adoption: route every call that
          enters this body through {!ad_entry_id}, and drop the bindings the
          adoption makes dead.  Those are not merely untidy -- they still hold
          a call the loopification postcondition would see, so leaving them in
          gets the function reported as declined even though its machine is
          correct. *)
  ad_what : string;  (** The body, named concretely enough to act on *)
}

(** The synthetic name calls entering an entry called [name] are routed
    through.  Lowercase and prefixed, so it cannot collide with the [_Enter_]
    frame struct nor with a binder translation emits. *)
let adopted_entry_id name = Id.of_string ("_adopted_" ^ name)

(** The calls reaching [ad], reported as targeting machine entry [entry].

    The captured variables are arguments of the entry even though no call site
    writes them: they reach the body through a closure, and a frame re-entering
    it has to carry them.  They are in scope wherever a call to the body is, so
    appending them here -- in the order the entry's parameter list is built --
    is what makes the two agree. *)
let adopted_checker ~entry ad : call_checker =
  let captured = List.map (fun id -> CPPvar id) ad.ad_captures in
  function
  | CPPfun_call (_, CPPvar id, args) when Id.equal id ad.ad_entry_id ->
    Some (mk_call_site ~entry (to_reversed args @ captured))
  | _ -> None

(** Why a single-entry machine cannot linearise the function [ad] was found
    in. *)
let decline_reason ad =
  Printf.sprintf
    "a self-call survived the transform: it is inside %s (%d parameter(s)%s), \
     which needs a second machine entry"
    ad.ad_what
    (List.length ad.ad_params)
    ( match ad.ad_captures with
    | [] -> ""
    | ids -> ", capturing " ^ String.concat ", " (List.map Id.to_string ids) )

(** Adopt the local fixpoint [stmt] binds, if it is one that calls back into
    the enclosing function.

    The shape is the Y-combinator pair {!Translation.gen_local_fix_by_ref}
    emits (see {!ycomb_self_id}).  A fixpoint whose body calls none of the
    enclosing function is left for {!loopify_inner_lambdas}, which handles it
    correctly on its own; one that does call back cannot be loopified alone,
    because two machines leave each other's stack to unwind.

    Calls reach the fixpoint two ways -- from inside through its
    self-reference parameter, from outside through the [wrapper] lambda that
    ties the knot -- and installation rewrites both into calls on
    {!ad_entry_id}.  The self-call forwards the fixpoint as a leading argument
    that the entry does not need, so installation drops it. *)
let adopt_local_fix ~stmts check = function
  | Sasgn (impl_id, Declare Tauto, CPPlambda {cl_params; cl_body; cl_ret; _}) -> (
    let lparams = to_reversed cl_params in
    match ycomb_self_id lparams with
    | None -> None
    | Some self_id ->
      if collect_stmts check ~in_visitor:false cl_body = [] then None
      else
        (* Drop the self-parameter, and any unnamed one: a frame can only
           carry a binder it can name. *)
        let params =
          match List.rev lparams with
          | _self :: rest_rev ->
            List.filter_map
              (fun (ty, id_opt) ->
                match id_opt with Some id -> Some (id, ty) | None -> None )
              (List.rev rest_rev)
          | [] -> []
        in
        let bound = self_id :: List.map fst params in
        let captures =
          free_vars_body cl_body
          |> List.filter (fun v -> not (List.exists (Id.equal v) bound))
          |> List.sort_uniq Id.compare
        in
        let name = name_of_self_id self_id in
        let entry_id = adopted_entry_id name in
        let wrapper = find_fix_wrapper impl_id stmts in
        let reroute e =
          match e with
          | CPPfun_call (res, CPPvar id, args) when Id.equal id self_id -> (
            match call_args args with
            | _self_arg :: rest ->
              CPPfun_call (res, CPPvar entry_id, of_reversed (List.rev rest))
            | [] -> e )
          | CPPfun_call (res, CPPvar id, args)
            when Option.equal Id.equal (Some id) wrapper ->
            CPPfun_call (res, CPPvar entry_id, args)
          | _ -> e
        in
        let install_calls = rewrite_exprs reroute in
        let bindings =
          impl_id :: (match wrapper with Some w -> [w] | None -> [])
        in
        let install ss = install_calls (drop_bindings bindings ss) in
        (* [reroute] only knows how to redirect a *call* on the fixpoint.  A
           program that passes it around as a value -- Coq's [FMapList.map2]
           returns it from a branch and applies it outside -- keeps a mention
           that installation cannot rewrite, and dropping the binding under it
           would leave the name undefined.  Decline instead, and let the
           postcondition check report the function as not linearisable. *)
        let survives =
          let free = free_vars_body (install stmts) in
          List.exists
            (fun id -> List.exists (Id.equal id) free)
            bindings
        in
        (* [reroute] goes by name, which is only sound while the names denote
           this fixpoint alone.  Two local fixpoints both called [loop] -- one
           of them inside a lambda -- share [loop_impl], [loop] and
           [_self_loop], and rerouting would send the other one's calls to an
           entry that never handles them. *)
        let shared_name =
          let rec count_stmt n st =
            let n =
              match st with
              | Sasgn (id, Declare _, _) when Id.equal id impl_id -> n + 1
              | _ -> n
            in
            fold_stmt_children ~on_expr:count_expr ~on_stmts:count_stmts n st
          and count_expr n e =
            fold_expr_children ~on_expr:count_expr ~on_stmts:count_stmts n e
          and count_stmts n l = List.fold_left count_stmt n l in
          count_stmts 0 stmts > 1
        in
        if survives || shared_name then None
        else
        Some
          { ad_name = name;
            ad_entry_id = entry_id;
            ad_params = params;
            ad_ret = cl_ret;
            ad_captures = captures;
            ad_body = install_calls cl_body;
            ad_install = install;
            ad_what = "the local fixpoint " ^ name } )
  | _ -> None

(** Adopt the body of an immediately-invoked lambda that still calls this
    function -- what {!generic_inline_expr} leaves behind when a mutual
    recursion partner is inlined in a non-tail position.

    Unlike a fixpoint the lambda has no name to key calls on, so installation
    recognises the invocation by its body and replaces it with a call on
    {!ad_entry_id}, which the body itself then no longer appears in. *)
let adopt_invocation check e =
  match e with
  | CPPfun_call (_, CPPlambda {cl_params; cl_body; cl_ret; _}, args)
    when collect_stmts check ~in_visitor:false cl_body <> [] ->
    let params =
      List.filter_map
        (fun (ty, id_opt) ->
          match id_opt with Some id -> Some (id, ty) | None -> None )
        (to_reversed cl_params)
    in
    if params = [] || List.length params <> List.length (call_args args) then
      None
    else
      let invoked = cl_body in
      let bound = List.map fst params in
      let captures =
        free_vars_body cl_body
        |> List.filter (fun v -> not (List.exists (Id.equal v) bound))
        |> List.sort_uniq Id.compare
      in
      let entry_id = adopted_entry_id "inl" in
      let reroute e' =
        match e' with
        | CPPfun_call (res, CPPlambda l', args') when l'.cl_body = invoked ->
          CPPfun_call (res, CPPvar entry_id, args')
        | _ -> e'
      in
      Some
        { ad_name = "inl";
          ad_entry_id = entry_id;
          ad_params = params;
          ad_ret = cl_ret;
          ad_captures = captures;
          ad_body = rewrite_exprs reroute cl_body;
          ad_install = rewrite_exprs reroute;
          ad_what = "an inlined body" }
  | _ -> None

(** The body this machine should adopt, if any.

    A local fixpoint is preferred: it is the shape translation emits for Coq's
    [let fix], and it names itself.  Failing that, an invoked lambda in the
    function's flow -- the residue of inlining a mutual-recursion partner. *)
let find_adopted check stmts =
  match find_in_flow stmts ~on_stmt:(adopt_local_fix ~stmts check) with
  | Some _ as found -> found
  | None -> find_in_flow stmts ~on_expr:(adopt_invocation check)

(** [only_entry n check] reports just the calls [check] finds against entry
    [n].

    Per-parameter analyses -- which parameters vary across calls, which are
    safe to park as pointers -- are about one entry's parameter list, so they
    must not be shown an argument list belonging to another entry: the two
    have no positional correspondence, and generally not even the same
    length. *)
let only_entry entry (check : call_checker) : call_checker =
 fun e ->
  match check e with Some cs when cs.cs_entry = entry -> Some cs | _ -> None

(** A checker that tries each of [checkers] in turn, so one machine can be
    driven by the calls that reach any of its entry points. *)
let any_checker (checkers : call_checker list) : call_checker =
 fun e -> List.find_map (fun c -> c e) checkers

(** The parameters the nontail frame-based transformation threads through its
    three mutually-recursive rewrite functions
    ({!rewrite_enter_lambda_return}, {!rewrite_enter_stmts},
    {!rewrite_enter_stmt}), bundled
    into a single value so that call sites read [ctx] rather than a dozen
    positional arguments.

    All fields are constant within a single invocation of the outer
    transformation ({!transform_nontail}) except {!er_env}, which is narrowed
    when entering lambda bodies, match branches, or continuations. *)
type enter_rewrite_ctx = {
  er_check : call_checker;
      (** Identifies recursive calls in expressions *)
  er_entries : machine_entry list;
      (** The machine's entry points, indexed by {!call_site.cs_entry} *)
  er_tparams : (template_type * Id.t) list;
      (** Template parameters of the enclosing function *)
  er_env : (Id.t * cpp_type) list;
      (** Type environment — changes when entering sub-scopes *)
  er_call_counter : int ref;
      (** Mutable counter for generating unique frame names *)
  er_frames_ref : call_frame_info list ref;
      (** Mutable accumulator for generated {!call_frame_info} records *)
  er_branch_ctx : string option;
      (** Constructor name when inside a match branch, for frame naming *)
  er_seen_frame_names : (string, int) Hashtbl.t;
      (** Deduplication table for context-derived frame names *)
  er_invariant_params : Id.Set.t;
      (** Invariant parameter ids — referenced directly from function scope,
          not stored in continuation frames *)
  er_rematerialized : (Id.t * cpp_stmt) list;
      (** Locals in scope bound to a value that mentions no local and calls
          nothing -- an alias of a static member, say.  A continuation binds
          them again rather than saving them in its frame, where a type the
          binding left to [auto] has no spelling. *)
}

(** The entry point a call site targets. *)
let entry_of ctx cs = List.nth ctx.er_entries cs.cs_entry

(** The frame that re-enters machine entry [entry] with [args], narrowed to
    that entry's varying positions.  The invariant ones are in scope at the
    handler already, so parking them would be dead weight.

    Which frame struct that is, and which arguments it carries, both follow
    from the entry -- so the two must be read together, and this is the only
    place that pairs them.  {!make_enter_for} is this for a call site still to
    hand; a decomposition that has kept only its arguments reaches the same
    frame through {!decomposed.d_entry}. *)
let enter_frame en fields = CPPstruct_id (en.en_enter_id, [], fields)

let make_enter_at ctx entry args =
  let en = List.nth ctx.er_entries entry in
  enter_frame en (filter_by_mask en.en_varying args)

(** The [_Enter]-style frame expression that enters [cs]'s target. *)
let make_enter_for ctx cs = make_enter_at ctx cs.cs_entry cs.cs_args

(** The frame entering [cs]'s target with [fields], which a caller has already
    narrowed -- typically a frame's stored copies of the call's arguments. *)
let make_enter_with ctx cs fields = enter_frame (entry_of ctx cs) fields

(** The frame layout a call site's target expects: the types of the arguments
    {!make_enter_for} keeps. *)
let enter_types_for ctx cs = entry_varying_types (entry_of ctx cs)

let partition_saved_invariant invariant_params saved_exprs saved_types =
  let analysis = map2_exn ~what:"partition_saved_invariant" (fun e ty ->
    match e with
    | CPPvar id when Id.Set.mem id invariant_params -> `Inv (id, ty)
    | CPPmove (CPPvar id) when Id.Set.mem id invariant_params -> `Inv (id, ty)
    | _ -> `Store (e, ty)
  ) saved_exprs saved_types in
  let must_store_exprs = List.filter_map (function
    | `Store (e, _) -> Some e | `Inv _ -> None) analysis in
  let must_store_types = List.filter_map (function
    | `Store (_, ty) -> Some ty | `Inv _ -> None) analysis in
  let rebuild stored_fields =
    let si = ref 0 in
    List.map (function
      | `Inv (id, _) -> CPPvar id
      | `Store _ ->
        let r = List.nth stored_fields !si in
        incr si; r
    ) analysis
  in
  (must_store_exprs, must_store_types, rebuild)

(** Emit a single [_ResumeN] frame for a decomposed single-call expression.

    Given a {!decomposed} record [d] (from {!decompose_single_call}), this
    function:
    + Infers types for all saved sub-expressions.
    + Registers a new [_CallN] frame whose handler binds frame fields back to
      the saved expression positions and applies [make_handler] to produce the
      handler body.
    + Moves/copies saved expressions for safe frame storage.
    + Returns push statements for [_CallN\{saved...\}] followed by
      [_Enter\{rec_args\}].

    {b Usage.}  The [make_handler] callback receives [(saved_field_vars,
    result_var)] — the frame-field accessors for saved expressions and the
    [_result] variable — and returns the handler body.  For [Sreturn] contexts
    this is [assign_result (d.d_rebuild svs r)]; for [Sasgn] contexts this is
    [[Sasgn (id, ty, d.d_rebuild svs r)]].

    @param ctx          Enter-rewrite context (see {!enter_rewrite_ctx})
    @param d            Single-call decomposition from {!decompose_single_call}
    @param make_handler Callback: [(saved_vars, result_var) -> handler_stmts]
    @return Push statements for [_CallN] + [_Enter] *)
let emit_single_call_frame ctx (d : decomposed) ~make_handler =
  let { er_tparams = tparams; er_env = env; er_call_counter = call_counter;
        er_frames_ref = frames_ref;
        er_branch_ctx = branch_ctx; er_seen_frame_names = seen;
        er_invariant_params = invariant_params; _ } = ctx
  in
  let call_name = make_call_frame_name "_Resume" call_counter seen ?branch_ctx () in
  let all_saved_types = infer_saved_types tparams env d.d_saved in
  let (must_store, must_store_types, rebuild) =
    partition_saved_invariant invariant_params d.d_saved all_saved_types in
  let n_must_store = List.length must_store in
  let saved_exprs_conv = move_for_frame_list must_store_types must_store in
  let field_names = derive_field_names saved_exprs_conv in
  let handler =
    let stored_fields = frame_fields_named field_names n_must_store in
    let saved_vars = rebuild stored_fields in
    make_handler saved_vars (CPPvar (id_result))
  in
  register_frame frames_ref ~name:call_name ~saved_types:must_store_types
    ~saved_exprs:saved_exprs_conv ~env ~handler;
  [
    make_stack_push (CPPstruct_id (Id.of_string call_name, [], saved_exprs_conv));
    make_stack_push (make_enter_at ctx d.d_entry d.d_rec_args);
  ]

(** [with_rematerialized ctx stmt] -- [ctx] once [stmt] has run: a binding
    whose value mentions only template parameters, invariant parameters and
    locals already bound again, and whose evaluation calls nothing, joins
    {!enter_rewrite_ctx.er_rematerialized}.  A call inside a lambda's body
    runs when the lambda does, not when it is made, so a closure qualifies:
    rebuilding it in a continuation is cheaper than storing it, and safe where
    storing it would keep references to locals of a scope already left. *)
let with_rematerialized ctx stmt =
  let rebindable v =
    List.exists (fun (_, tp) -> Id.equal tp v) ctx.er_tparams
    || Id.Set.mem v ctx.er_invariant_params
    || List.mem_assoc v ctx.er_rematerialized
  in
  let rec calls_nothing e =
    match e with
    | CPPfun_call _ -> false
    | CPPlambda _ -> true
    | _ ->
      let ok = ref true in
      iter_expr_children
        ~on_expr:(fun c -> if not (calls_nothing c) then ok := false)
        ~on_stmts:(fun _ -> ok := false)
        e;
      !ok
  in
  let rec is_reference = function
    | Tref _ -> true
    | Tconst t -> is_reference t
    | _ -> false
  in
  match stmt with
  (* A reference names someone else's value: saving it would copy the value
     and leave a pointer taken from it dangling with the frame.  The
     continuation rebuilds it from its source, which is saved instead. *)
  | Sasgn (id, Declare ty, e)
    when calls_nothing e
         && (is_reference ty || List.for_all rebindable (free_vars_expr e)) ->
    {ctx with er_rematerialized = ctx.er_rematerialized @ [(id, stmt)]}
  | _ -> ctx

(** Rewrite a single return statement for the [_Enter] handler in frame-based
    non-tail recursion transformation.

    {!Normalize} has bound every recursive call that is not a tail call, the
    last recursive argument of a constructor, or under a conditional or a
    custom replacement, so a returned expression holds at most one:

    - {b 0 calls}: assign to [_result], descending into IIFEs that hold calls
    - {b a tail call}: push [_Enter]
    - {b 1 call inside an expression}: decompose via {!decompose_single_call},
      push a [_Resume] frame that rebuilds the expression, then [_Enter]

    @param ctx  Enter-rewrite context (see {!enter_rewrite_ctx})
    @param stmt The statement to rewrite (typically a [Sreturn] statement)
    @return A list of rewritten statements (frame pushes or result assignments) *)
let rec rewrite_enter_lambda_return ctx stmt =
  let { er_check = check; er_env = env; _ } = ctx in
  match stmt with
  | Sreturn (Some e) ->
    let n_calls = count_calls_expr check e in
    if n_calls = 0 then
      rewrite_base_with_inner_calls check e
        ~rewrite_iife_body:(fun extended_body ->
          let lenv = collect_type_env extended_body @ env in
          rewrite_enter_stmts { ctx with er_env = lenv } extended_body)
        ~base_case:assign_result
    else if n_calls = 1 then
      match decompose_single_call check e with
      | Some d ->
        emit_single_call_frame ctx d
          ~make_handler:(fun svs r -> assign_result (d.d_rebuild svs r))
      | None -> (
        match check e with
        | Some cs when List.for_all (fun a -> count_calls_expr check a = 0) cs.cs_args ->
          (* Tail call: re-enter. *)
          [make_stack_push (make_enter_for ctx cs)]
        | _ ->
          (* A call {!Normalize} left in place that no frame can hold: it
             runs inline, and the postcondition reports the function. *)
          assign_result e )
    else
      (* {!Normalize} binds all but one call of a returned expression. *)
      assign_result e
  | Sif (cond, then_br, else_br) ->
    let rw_stmts = rewrite_enter_stmts ctx in
    let rw_then = rw_stmts then_br in
    let rw_else = rw_stmts else_br in
    [Sif (cond, rw_then, rw_else)]
  | Scustom_case (ty, scrut, tyargs, branches, err) ->
    (* A recursive call in the scrutinee is bound before the match by
       {!Normalize}; only the branches are left to rewrite. *)
    [
      Scustom_case
        ( ty,
          scrut,
          tyargs,
          List.map
            (fun (ps, ret_ty2, body) ->
              let lenv = collect_type_env body @ ps @ env in
              let br_ctx = match ps with
                | (id, _) :: _ -> Some (Id.to_string id)
                | [] -> None
              in
              ( ps, ret_ty2,
                rewrite_enter_stmts { ctx with er_env = lenv;
                                               er_branch_ctx = br_ctx } body ) )
            branches,
          err );
    ]
  | Smatch (scrut, branches, default) ->
    (* Augment the env with each branch's binding variable types so that
       [infer_saved_types] resolves field types correctly per-branch. *)
    let rw_branch br =
      let branch_env =
        (* Register structured-binding field types. *)
        let fb_env =
          List.map (fun (bname, ty, _) -> (bname, ty)) br.smb_field_bindings
        in
        (* Also register aggregate binding for frame-dispatch branches. *)
        let var_env =
          match br.smb_var with
          | Some id when br.smb_field_bindings = [] ->
            [(id, Tconst (br.smb_ctor_type))]
          | _ -> []
        in
        fb_env @ var_env @ env
      in
      let br_ctx = ctor_type_short_name br.smb_ctor_type in
      let rw = rewrite_enter_stmts { ctx with er_env = branch_env;
                                              er_branch_ctx = br_ctx } in
      { br with smb_body = rw br.smb_body }
    in
    let rw_default = rewrite_enter_stmts { ctx with er_branch_ctx = None } in
    [Smatch (scrut, List.map rw_branch branches, Option.map rw_default default)]
  | Sblock stmts ->
    [Sblock (rewrite_enter_stmts ctx stmts)]
  | Sswitch (scrut, r, branches, default) ->
    let rw_branches =
      List.map
        (fun (id, body) ->
          let lenv = collect_type_env body @ env in
          (id, rewrite_enter_stmts { ctx with er_env = lenv } body))
        branches
    in
    let rw_default = Option.map (rewrite_enter_stmts ctx) default in
    [Sswitch (scrut, r, rw_branches, rw_default)]
  | s -> [s]

(** Process a sequence of statements using continuation-passing to handle
    recursive calls in assignment positions.

    This is the core of the nontail frame-based transformation for statement
    sequences. When it encounters [Sasgn(id, ty, e)] where [e] contains one or
    more recursive calls, it captures the remaining statements ([rest]) as a
    "continuation" that is embedded in the Call frame's handler.

    {b Stack frame chaining strategy.}  For [let x = f(a) in rest]:
    + Push [_CallN\{saved_fields\}] — saves continuation variables live across
      the call.
    + Push [_Enter\{args\}] — provides the recursive call's arguments.
    + The loop pops [_Enter], executes the call, stores the result in
      [_result], then pops [_CallN] whose handler binds [x = _result],
      restores saved fields, and processes [rest].

    For nested calls like [let x = f(a) in let y = f(b) in rest], frames
    chain: [_Call1]'s handler processes the [let y = ...] assignment, which
    pushes [_Call2] + [_Enter] for the second call.  The final handler in
    [_Call2] processes [rest].

    The function handles several cases:
    - {b Single direct call}: [let x = f(args) in rest] -- creates one Call
      frame whose handler assigns [_result] to [x] then processes [rest].
    - {b Single decomposed call}: [let x = g(saved, f(args)) in rest] --
      decomposes [e] to extract saved expressions and the recursive call,
      creates a Call frame that reconstructs the expression from frame fields.
    - {b Non-assignment statements}: delegates to {!rewrite_enter_lambda_return}.

    Continuation variables (free in [rest] but defined before it) are saved in
    each Call frame and restored via [make_cont_bindings] in the handler.

    @param ctx    Enter-rewrite context (see {!enter_rewrite_ctx})
    @param stmts  The statement sequence to process
    @return Rewritten statement list (typically stack push operations) *)
and rewrite_enter_stmts ctx stmts =
  let { er_check = check; er_tparams = tparams;
        er_env = env;
        er_call_counter = call_counter; er_frames_ref = frames_ref;
        er_branch_ctx = branch_ctx;
        er_seen_frame_names = seen; _ } = ctx
  in
  match stmts with
  | [] -> []
  | Sasgn (id, tgt, e) :: rest when count_calls_expr check e >= 1 ->
    let n_calls = count_calls_expr check e in
    let rest_free = compute_rest_free_vars rest in
    (* Helper: build continuation handler and register the call frame.
       [~offset] is the field offset where continuation vars start in the
       frame. [assign_expr] is the expression to assign to [id].
       [saved/types] are the frame's saved values (decomposed + continuation).
       [enter] is the frame the recursive call re-enters through. *)
    let make_cont_handler ~offset ~make_assign_expr ~saved ~types ~enter =
      (* The bindings the rest reads, with the ones they read in turn, in
         the order they were made. *)
      let remat =
        let needed =
          List.fold_right
            (fun (cid, st) needed ->
              if List.exists (Id.equal cid) needed then
                needed @ (match st with Sasgn (_, _, e) -> free_vars_expr e | _ -> [])
              else needed )
            ctx.er_rematerialized rest_free
        in
        List.filter (fun (cid, _) -> List.exists (Id.equal cid) needed) ctx.er_rematerialized
      in
      (* A name heading a recursive call is the machine's entry, not a value
         the continuation needs: the call becomes a frame push. *)
      let entry_heads =
        let heads = ref [] in
        let rec fe e =
          ( match e with
          | CPPfun_call (_, CPPvar h, _) when check e <> None -> heads := h :: !heads
          | _ -> () );
          iter_expr_children ~on_expr:fe ~on_stmts:(List.iter fs) e
        and fs st = iter_stmt_children ~on_expr:fe ~on_stmts:(List.iter fs) st in
        List.iter fs rest;
        !heads
      in
      (* What the rest reads, with what its rebuilt bindings read in place
         of those bindings. *)
      let remat_free =
        List.concat_map
          (fun (_, st) -> match st with Sasgn (_, _, e) -> free_vars_expr e | _ -> [])
          remat
        |> List.filter (fun v -> not (List.exists (fun (_, tp) -> Id.equal tp v) tparams))
      in
      let cont_vars =
        filter_cont_vars ~exclude_id:id
          (List.fold_left
             (fun acc v -> if List.exists (Id.equal v) acc then acc else acc @ [v])
             rest_free remat_free)
        |> List.filter (fun cid -> not (Id.Set.mem cid ctx.er_invariant_params))
        |> List.filter (fun cid -> not (List.mem_assoc cid remat))
        |> List.filter (fun cid -> not (List.exists (Id.equal cid) entry_heads)) in
      let cont_saved = List.map (fun cid -> CPPvar cid) cont_vars in
      let cont_types = infer_saved_types tparams env cont_saved in
      let call_name = make_call_frame_name "_Cont" call_counter seen ?branch_ctx () in
      let all_saved = saved @ cont_saved in
      let all_field_names = derive_field_names all_saved in
      let assign_expr = make_assign_expr all_field_names in
      let bindings = make_cont_bindings ~offset ~field_names:all_field_names cont_vars cont_types in
      (* The rest sees the result binding too: a later frame saving it needs
         its type, and the body it came from may only say [auto]. *)
      let rest_env =
        let bound = match tgt with Declare ty when ty <> Tauto -> [(id, ty)] | _ -> [] in
        bound @ make_cont_env cont_vars cont_types env
      in
      let rest_processed =
        List.map snd remat @ rewrite_enter_stmts { ctx with er_env = rest_env } rest
      in
      (* When tgt is Existing (a bare assignment), the variable was declared
         in the _Enter handler scope and does not exist in the _Cont handler
         scope.  Promote to [auto] so the handler declares it. *)
      let handler_ty = match tgt with Existing -> Declare Tauto | t -> t in
      let handler =
        match assign_expr with
        | CPPvar v when Common.is_scrutinee_cache_id id ->
          (* assign_expr is a plain variable (e.g. _result) and id is a
             scrutinee cache variable (_cs, _cs1, ...) — skip the
             redundant alias [auto _cs = v;] and substitute v for id. *)
          bindings @ subst_var_stmts id v rest_processed
        | _ ->
          bindings @ [Sasgn (id, handler_ty, assign_expr)] @ rest_processed
      in
      let all_saved = saved @ cont_saved in
      let all_types = types @ cont_types in
      let all_saved_conv = move_for_frame_list all_types all_saved in
      register_frame frames_ref ~name:call_name ~saved_types:all_types
        ~saved_exprs:all_saved_conv ~env ~handler;
      [
        make_stack_push (CPPstruct_id (Id.of_string call_name, [], all_saved_conv));
        make_stack_push enter;
      ]
    in
    if n_calls = 1 then
      match check e with
      | Some cs ->
        (* Direct call: id = f(args) — no decomposition needed *)
        make_cont_handler
          ~offset:0
          ~make_assign_expr:(fun _fnames -> CPPmove (CPPvar (id_result)))
          ~saved:[] ~types:[]
          ~enter:(make_enter_for ctx cs)
      | None ->
      match decompose_single_call check e with
      | Some d ->
        (* Decomposed call: id = rebuild(saved, f(rec_args)) *)
        let n_d = List.length d.d_saved in
        let d_types = infer_saved_types tparams env d.d_saved in
        make_cont_handler
          ~offset:n_d
          ~make_assign_expr:(fun fnames ->
            d.d_rebuild (frame_fields_named fnames n_d) (CPPmove (CPPvar (id_result))))
          ~saved:d.d_saved ~types:d_types
          ~enter:(make_enter_at ctx d.d_entry d.d_rec_args)
      | None ->
        [Sasgn (id, tgt, e)] @ rewrite_enter_stmts ctx rest
    else
      (* {!Normalize} binds each call on its own; a right-hand side holding
         several is not one it produces. *)
      [Sasgn (id, tgt, e)] @ rewrite_enter_stmts ctx rest
  (* Conditional recursion: at least one branch has a recursive call and there
     are continuation statements after.  Merge the continuation into each branch
     so the recursive branch captures it via the Sasgn::rest _Cont pattern while
     the non-recursive branch processes it inline.
     Non-recursive branches wrap [rest] in Sblock to prevent name collisions
     with bindings generated by Scustom_case destructuring in the branch. *)
  | Sif (cond, then_br, else_br) :: rest
      when rest <> []
        && count_calls_expr check cond = 0
        && (count_calls_stmts check then_br > 0
            || count_calls_stmts check else_br > 0) ->
    let merge_rest br =
      if count_calls_stmts check br > 0 then br @ rest
      else br @ [Sblock rest]
    in
    rewrite_enter_lambda_return ctx
      (Sif (cond, merge_rest then_br, merge_rest else_br))

  | Scustom_case (ty, scrut, tyargs, branches, err) :: rest
      when rest <> []
        && count_calls_expr check scrut = 0
        && List.exists (fun (_, _, body) -> count_calls_stmts check body > 0)
             branches ->
    let merged =
      List.map (fun (ps, rty, body) ->
        if count_calls_stmts check body > 0 then (ps, rty, body @ rest)
        else (ps, rty, body @ [Sblock rest]))
        branches
    in
    rewrite_enter_lambda_return ctx
      (Scustom_case (ty, scrut, tyargs, merged, err))

  | Smatch (scrut, branches, default) :: rest
      when rest <> []
        && List.exists
             (fun br -> count_calls_stmts check br.smb_body > 0)
             branches ->
    let merged_brs =
      List.map (fun br ->
        if count_calls_stmts check br.smb_body > 0
        then { br with smb_body = br.smb_body @ rest }
        else { br with smb_body = br.smb_body @ [Sblock rest] })
        branches
    in
    let merged_default = Option.map (fun d -> d @ rest) default in
    rewrite_enter_lambda_return ctx
      (Smatch (scrut, merged_brs, merged_default))

  | stmt :: rest ->
    (* Extend the environment with any variable bound by this statement so
       that [infer_saved_type] can resolve its type when processing [rest].
       This is important when a local [std::function] (e.g. from [let fix])
       is defined here and then used as the callee in a continuation. *)
    let updated_env =
      match stmt with
      | Sasgn (id, Declare Tauto, CPPlambda
        { cl_params = params;
          cl_ret = ret_ty_opt;
          _ }) ->
        let param_types =
          List.rev_map (fun (t, _) -> strip_ref_and_const_type t) (to_reversed params)
        in
        let ret_ty = match ret_ty_opt with
          | Some t when t <> Tvoid -> t
          | _ -> Tvoid
        in
        (id, Tfun (param_types, ret_ty)) :: ctx.er_env
      | Sasgn (id, Declare ty, _) -> (id, ty) :: ctx.er_env
      | Sdecl (id, ty) -> (id, ty) :: ctx.er_env
      | _ -> ctx.er_env
    in
    rewrite_enter_lambda_return ctx stmt
    @ rewrite_enter_stmts
        { (with_rematerialized ctx stmt) with er_env = updated_env } rest

(** Rewrite a single non-tail recursive statement for the Enter handler.

    Thin wrapper around {!rewrite_enter_lambda_return} that collapses a
    multi-statement result into a single [Sblock]. This is the entry point used
    by {!transform_nontail} when rewriting each top-level body statement for the
    Enter handler of the frame-based loop.

    @param ctx  Enter-rewrite context (see {!enter_rewrite_ctx})
    @param stmt The single statement to rewrite
    @return A single statement (possibly [Sblock] wrapping multiple results) *)
let rewrite_enter_stmt ctx stmt =
  match rewrite_enter_lambda_return ctx stmt with
  | [s] -> s
  | ss -> Sblock ss

(** {3 Shared helpers for transform_nontail}

    The non-tail recursion transform generates boilerplate: struct definitions,
    stack initialization, parameter copies from frame, frame lambdas, and the
    while-loop dispatch. These helpers factor out the common patterns. *)

(** Generate the initial [_stack.emplace_back(_Enter\{...\})] statement.

    @param varying_params The parameters to include in the Enter frame
    @return A raw C++ statement pushing the initial Enter frame *)
let make_stack_init varying_params =
  let move_if_needed ty v =
    match ty with
    | Tconst _ | Tref _ -> v
    | t when not (is_trivially_copyable_type t) -> CPPmove v
    | _ -> v
  in
  make_stack_push
    (CPPstruct_id
       ( id_enter,
         [],
         List.map
           (fun p ->
             let v = CPPvar p.fp_name in
             if p.fp_pointer_safe then CPPunop (Uaddr, v)
             else move_if_needed p.fp_ty v )
           varying_params ))

(** Generate parameter bindings that read frame fields into locals.
    For trivially copyable types (scalars, pointers, enums), produces a copy.
    For non-trivially-copyable const-ref types (invariant borrowed params stored by
    pointer), produces a [const T&] reference to the frame field.
    For non-trivially-copyable owned types (e.g. [List<T>]), produces a move to
    avoid an O(n) deep copy — safe because [_f] was moved off the stack.
    For trivially-copyable scalars, produces a plain copy.

    @param varying_params The parameters to bind from the frame
    @return List of assignment statements *)
let make_param_copies varying_params =
  (* Helper: choose the right binding expression for a frame field access. *)
  let bind_field id ty =
    let stripped = strip_ref_type ty in
    let f = CPPaccess (Adot, CPPvar (id_f), id) in
    match stripped with
    | Tconst inner when not (is_trivially_copyable_type inner) ->
      (* Const-ref param stored in frame: bind by [const T&] reference, cheaper
         than cloning. *)
      Sasgn (id, Declare (Tref (Lvalue, Tconst inner)), f)
    | t when not (is_trivially_copyable_type t) ->
      (* Owned non-trivial type (e.g. [List<T>]): move from frame field to avoid
         an O(n) deep-copy.  [_f] was obtained via [std::move(std::get<...>(_frame))]
         so the field is safe to consume. *)
      Sasgn (id, Declare t, CPPmove f)
    | Tvar _ ->
      (* Template type parameter (e.g. [F0] from [F0 &&f]).  When [F0] is
         deduced as a reference type, [F0 f = std::move(_f.f)] would be
         ill-formed — a non-const lvalue reference cannot bind to an rvalue.
         Use [auto] so the declared type is always deduced as a value type,
         regardless of whether [F0] was a reference or function type. *)
      Sasgn (id, Declare Tauto, CPPmove f)
    | _ ->
      (* Trivially copyable (scalar, pointer, enum): plain copy is fine. *)
      Sasgn (id, Declare stripped, f)
  in
  List.map
    (fun {fp_name = id; fp_ty = ty; fp_pointer_safe} ->
      if not fp_pointer_safe then bind_field id ty
      else
        match borrowed_value_param_pointee ty with
        | Some t ->
          Sasgn (id, Declare (Tref (Lvalue, Tconst t)),
                 CPPderef (CPPaccess (Adot, CPPvar (id_f), id)))
        | None ->
          let stripped = strip_ref_type ty in
          Sasgn (id, Declare stripped,
                 CPPaccess (Adot, CPPvar (id_f), id)) )
    varying_params

(** Compute pointer-safe flags for each Call frame by analyzing which
    frame fields appear as [_Enter] push args at pointer-safe positions.
    Propagates transitively through Call-to-Call chains (e.g. when
    [_Call1] handler pushes [_Call2\{_f._s1\}] and [_Call2._s1] is used
    at a pointer-safe position in [_Enter]).
    Returns [(frame_name, bool list)] for frames with any pointer-safe
    field. *)
let compute_frame_pointer_safe pointer_safe_varying frames =
  if not (List.exists Fun.id pointer_safe_varying) then []
  else
  let n_enter = List.length pointer_safe_varying in
  (* Build a map from local variable id to field index in [(cf_field_names cf)].
     Scans top-level [Sasgn(id, _, _f.field)] and [Sasgn(id, _, move(_f.field))]
     statements so that [_Enter{local_var}] pushes can be traced back to the
     frame field that [local_var] was loaded from. *)
  let build_local_to_field_map field_names stmts =
    let field_idx expr =
      let base = match expr with CPPmove e -> e | e -> e in
      match base with
      | CPPaccess (Adot, CPPvar f, field_id) when Id.equal f id_f ->
        let rec find i = function
          | [] -> None
          | fn :: rest -> if Id.equal fn field_id then Some i else find (i + 1) rest
        in
        find 0 field_names
      | _ -> None
    in
    List.filter_map
      (fun stmt ->
        match stmt with
        | Sasgn (id, _, expr) ->
          (match field_idx expr with
          | Some j -> Some (id, j)
          | None -> None)
        | _ -> None)
      stmts
  in
  let is_field_access_or_alias local_map field_names j expr =
    (* Strip CPPmove wrappers before pattern matching, since push arguments
       are commonly [CPPmove (CPPvar x)] or
       [CPPmove (CPPaccess (Adot, CPPvar _f, fld))]. *)
    let expr = match expr with CPPmove e -> e | e -> e in
    match expr with
    | CPPaccess (Adot, CPPvar f, field_id) ->
      Id.equal f id_f
      && j < List.length field_names
      && Id.equal field_id (List.nth field_names j)
    | CPPvar x ->
      (match List.assoc_opt x local_map with
       | Some k -> k = j
       | None -> false)
    | CPPderef (CPPvar x) ->
      (match List.assoc_opt x local_map with
       | Some k -> k = j
       | None -> false)
    | CPPderef (CPPaccess (Adot, CPPvar f, field_id)) ->
      Id.equal f id_f
      && j < List.length field_names
      && Id.equal field_id (List.nth field_names j)
    | _ -> false
  in
  (* Find all struct pushes in handler body: returns (name, args) list *)
  let find_struct_pushes stmts =
    let result = ref [] in
    let rec scan = function
      | Sexpr (CPPfun_call (_, _callee, {rev = [CPPstruct_id (name, _, args)]})) ->
        result := (Id.to_string name, args) :: !result
      | s ->
        iter_stmt_children ~on_expr:(fun _ -> ())
          ~on_stmts:(List.iter scan) s
    in
    List.iter scan stmts;
    !result
  in
  (* Mutable flags per frame *)
  let flag_arrays =
    List.map
      (fun cf ->
        (cf.cf_name, Array.make (List.length (cf_saved_types cf)) false))
      frames
  in
  let get_flags name =
    match List.assoc_opt name flag_arrays with
    | Some arr -> Some arr
    | None -> None
  in
  (* Step 1: seed from _Enter push args, looking through local variable bindings *)
  List.iter
    (fun cf ->
      let fnames = cf_field_names cf in
      let local_map = build_local_to_field_map fnames cf.cf_handler in
      let pushes = find_struct_pushes cf.cf_handler in
      List.iter
        (fun (push_name, args) ->
          if push_name = "_Enter" && List.length args = n_enter then
            match get_flags cf.cf_name with
            | Some arr ->
              for j = 0 to Array.length arr - 1 do
                if not arr.(j) then
                  let is_used =
                    List.exists2
                      (fun safe arg ->
                        safe
                        && is_field_access_or_alias local_map fnames j arg)
                      pointer_safe_varying args
                  in
                  if is_used then arr.(j) <- true
              done
            | None -> ())
        pushes)
    frames;
  (* Step 2: propagate through Call-to-Call chains until fixpoint.
     Two directions:
     (a) BACKWARD: if target frame's position k is pointer-safe and cf pushes
         target with its field j (or local from field j) at position k, then
         cf's field j must also be pointer-safe (it will be forwarded as a raw ptr).
     (b) FORWARD: if cf's field j is pointer-safe and cf pushes target with
         that field at position k, then target's position k must also be
         pointer-safe (it receives a raw pointer and must store/forward it as such). *)
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter
      (fun cf ->
        let fnames = cf_field_names cf in
      let local_map = build_local_to_field_map fnames cf.cf_handler in
        let pushes = find_struct_pushes cf.cf_handler in
        List.iter
          (fun (push_name, args) ->
            match get_flags push_name with
            | Some target_arr when List.length args = Array.length target_arr ->
              List.iteri
                (fun k arg ->
                  (* (a) BACKWARD: target[k] true → src[j] true *)
                  (if target_arr.(k) then
                    match get_flags cf.cf_name with
                    | Some src_arr ->
                      for j = 0 to Array.length src_arr - 1 do
                        if (not src_arr.(j))
                           && is_field_access_or_alias local_map fnames j arg
                        then (
                          src_arr.(j) <- true;
                          changed := true)
                      done
                    | None -> ());
                  (* (b) FORWARD: src[j] true → target[k] true.
                     If the argument at position k comes from a pointer-safe
                     field of cf, then target position k must also be pointer-safe
                     so its type stays consistent (raw pointer throughout). *)
                  if not target_arr.(k) then
                    (match get_flags cf.cf_name with
                    | Some src_arr ->
                      let src_is_safe =
                        Array.exists Fun.id
                          (Array.mapi (fun j flag ->
                            flag
                            && is_field_access_or_alias local_map fnames j
                                 arg)
                          src_arr)
                      in
                      if src_is_safe then (
                        target_arr.(k) <- true;
                        changed := true)
                    | None -> ()))
                args
            | _ -> ())
          pushes)
      frames
  done;
  (* Collect results *)
  List.filter_map
    (fun (name, arr) ->
      let flags = Array.to_list arr in
      if List.exists Fun.id flags then Some (name, flags) else None)
    flag_arrays

(** Rewrite frame push expressions so that pointer-safe positions use
    [&x] (for variables) or [crane_raw(x)] (for dereferences) instead of
    deep-copying.  Handles both [_Enter] and [_CallN] pushes.

    When [binding_env] is supplied, a [CPPvar x] at a pointer-safe position is
    looked up: if [x = *(sp)] in the environment, emit [crane_raw(sp)] rather
    than [&x] (which would be a dangling pointer to a local).

    @param frame_pointer_safe [(frame_name, bool list)] mapping
    @param frame_sptr  [(frame_name, bool list)] — positions where the
           original saved type is [Tshared_ptr _]. At these positions, emit
           [crane_raw(...)] instead of [&] to extract the raw pointer. *)
let adjust_frame_push_args ?(binding_env = []) ?(frame_sptr = []) frame_pointer_safe stmts =
  if frame_pointer_safe = [] then stmts
  else
    let lookup name_s = List.assoc_opt name_s frame_pointer_safe in
    let lookup_uptr name_s = List.assoc_opt name_s frame_sptr in
    let adjust_arg safe is_uptr arg =
      if not safe then arg
      else
      let arg = match arg with CPPmove a -> a | a -> a in
      let raw_of e =
        CPPfun_call (call_opaque, CPPrt Crane_rt.Raw, of_reversed ([e]))
      in
      if is_uptr then
        (* If the argument is a local variable loaded as a const-reference from a
           pointer-safe frame field (const T &x = *_f.field after fix_handler_bindings),
           take its address (&x) rather than extracting a raw pointer from a
           non-pointer local. *)
        (match arg with
         | CPPvar x ->
           (match List.assoc_opt x binding_env with
            | Some (CPPderef (CPPaccess (Adot, CPPvar f, _)))
              when Id.equal f id_f ->
              CPPunop (Uaddr, arg)
            | _ ->
              raw_of arg)
         | _ -> raw_of arg)
      else
        match arg with
        | CPPderef (CPPvar x) ->
          (match List.assoc_opt x binding_env with
           | Some (CPPderef (CPPaccess (Adot, CPPvar f, _)))
             when Id.equal f id_f ->
             CPPunop (Uaddr, CPPvar x)
           | Some (CPPderef sp) ->
             raw_of sp
           | _ ->
             raw_of (CPPvar x))
        | CPPderef inner ->
          raw_of inner
        | CPPvar x ->
          (match List.assoc_opt x binding_env with
           | Some (CPPderef (CPPaccess (Adot, CPPvar f, _)))
             when Id.equal f id_f ->
             CPPunop (Uaddr, arg)
           | Some (CPPderef sp) ->
             raw_of sp
           | _ -> CPPunop (Uaddr, arg))
        | _ -> arg
    in
    let rec on_stmt = function
      | Sexpr (CPPfun_call (_, callee, {rev = [CPPstruct_id (name, targs, args)]})) -> (
        match lookup (Id.to_string name) with
        | Some flags when List.length args = List.length flags ->
          let uptr_flags = match lookup_uptr (Id.to_string name) with
            | Some f -> f
            | None -> List.map (fun _ -> false) flags
          in
          let args' = List.map2 (fun (safe, is_uptr) arg -> adjust_arg safe is_uptr arg)
            (List.combine flags uptr_flags) args in
          Sexpr (CPPfun_call (call_opaque, callee, of_reversed ([CPPstruct_id (name, targs, args')])))
        | _ -> map_stmt Fun.id on_stmt Fun.id
                 (Sexpr (CPPfun_call (call_opaque, callee, of_reversed ([CPPstruct_id (name, targs, args)])))))
      | s -> map_stmt Fun.id on_stmt Fun.id s
    in
    List.map on_stmt stmts

(** Rewrite [Smatch] nodes in [stmts] whose scrutinee is a value-type accessor
    [param.v()] for any [param] in [owned_names], marking the scrutinee owned
    so that the printer emits [param.v_mut()] and [auto& [...]] structured
    bindings.  This enables [std::move] of child [shared_ptr] fields when the
    parameter was moved into the handler (not borrowed).

    Does not recurse into lambda bodies — only into statement-level nesting
    ([Sblock], [Sif], [Swhile], [Smatch] branch bodies, etc.). *)
let make_owned_param_matches owned_names stmts =
  let rec rewrite_stmts ss = List.map rewrite_stmt ss
  and rewrite_stmt s =
    match s with
    | Smatch (scrut, branches, default) ->
      let is_owned_param =
        (* Value-type inductives:
           scrutinee = CPPfun_call (CPPaccess (Adot, id, "v"), []) *)
        match scrut.sc_expr with
        | CPPfun_call (_, CPPaccess (Adot, CPPvar id, v_id), {rev = []})
          when Id.equal v_id id_v ->
          List.exists (Id.equal id) owned_names
        | _ -> false
      in
      Smatch
        ( { scrut with sc_owned = scrut.sc_owned || is_owned_param },
          List.map
            (fun br -> { br with smb_body = rewrite_stmts br.smb_body })
            branches,
          Option.map rewrite_stmts default )
    | s ->
      (* Recurse into statement-level nesting.  [Fun.id] for the expression
         mapper ensures we never descend into [CPPlambda] bodies. *)
      map_stmt Fun.id rewrite_stmt Fun.id s
  in
  rewrite_stmts stmts

(** Move non-trivial values into explicit continuation frames when ownership is
    already local to the loop dispatcher.

    Frame handlers bind [_f] by moving the active variant alternative out of
    [_frame].  Any non-trivial [_f.field] subsequently saved into another frame
    can therefore be moved instead of cloned.  Likewise, [_result] is used as a
    scratch accumulator and is overwritten by the recursive call whose [_Enter]
    frame is pushed immediately after the continuation frame, so saving it by
    move avoids a deep copy.

    For [_Enter] frame pushes the rule is extended: child pointers dereferenced
    by [CPPderef] (e.g. [*(d_a1)]) are also moved.  These arise from
    [shared_ptr] fields of a value-type variant that has been matched with
    [v_mut()] (after [make_owned_param_matches]), so the pointed-to value is
    mutable and the current iteration is the only owner — moving is safe.

    Value fields bound from owned [v_mut()] matches (e.g. [auto &[a0, a1] =
    std::get<...>(l.v_mut())]) are also moveable: the scrutinee is owned and
    dead after the frame push, so moving the field avoids a deep copy. *)
let optimize_frame_push_args frame_field_types stmts =
  if frame_field_types = [] then stmts
  else
    let lookup name_s = List.assoc_opt name_s frame_field_types in
    let should_move ~is_enter ~owned_vars ty arg =
      let stripped = strip_ref_and_const_type ty in
      worthwhile_move_type stripped
      &&
      match arg with
      | CPPmove _ -> false
      | CPPaccess (Adot, CPPvar id, _) when Id.equal id id_f -> true
      | CPPvar id when Id.equal id id_result -> true
      | CPPvar id when List.exists (Id.equal id) owned_vars -> true
      | _ -> false
    in
    let adjust_args ~is_enter ~owned_vars types args =
      if List.length types = List.length args then
        List.map2
          (fun ty arg ->
            if should_move ~is_enter ~owned_vars ty arg then CPPmove arg else arg)
          types args
      else
        args
    in
    let owned_bindings_of_branch ~owned br =
      if owned then
        List.filter_map
          (fun (id, ty, _used) ->
            match ty with
            | Tshared_ptr _ -> None
            | _ -> Some id)
          br.smb_field_bindings
      else []
    in
    let is_owned_decl_type ty =
      let rec has_ref = function
        | Tref _ -> true
        | Tconst t -> has_ref t
        | _ -> false
      in
      not (has_ref ty) && worthwhile_move_type (strip_ref_and_const_type ty)
    in
    let is_frame_push = function
      | Sexpr (CPPfun_call (_, _, {rev = [CPPstruct_id (name, _, _)]})) ->
        lookup (Id.to_string name) <> None
      | _ -> false
    in
    let rec take_while pred = function
      | x :: rest when pred x ->
        let taken, remaining = take_while pred rest in
        (x :: taken, remaining)
      | rest -> ([], rest)
    in
    let process_push_group ~decl_owned match_owned pushes =
      let owned_vars = decl_owned @ match_owned in
      let push_data = List.map (function
        | Sexpr (CPPfun_call (_, callee, {rev = [CPPstruct_id (name, targs, args)]})) ->
          (callee, name, targs, args)
        | _ -> CErrors.anomaly (Pp.str "loopify: unexpected push statement shape")
      ) pushes in
      let last_push_of = Hashtbl.create 8 in
      (* A read nested in a later push (the re-entry frame's [f(0)]) counts:
         moving earlier would leave that read with a moved-from value. *)
      List.iteri (fun idx (_, _, _, args) ->
        List.iter (fun arg ->
          List.iter (fun id ->
            if List.exists (Id.equal id) owned_vars then
              Hashtbl.replace last_push_of (Id.to_string id) idx)
            (free_vars_expr arg)
        ) args
      ) push_data;
      let should_move_in_group ~is_enter idx ty arg =
        let stripped = strip_ref_and_const_type ty in
        worthwhile_move_type stripped
        &&
        match arg with
        | CPPmove _ -> false
        | CPPaccess (Adot, CPPvar id, _) when Id.equal id id_f -> true
        | CPPvar id when Id.equal id id_result -> true
        | CPPvar id when List.exists (Id.equal id) owned_vars ->
          Hashtbl.find_opt last_push_of (Id.to_string id) = Some idx
        | _ -> false
      in
      List.mapi (fun idx (callee, name, targs, args) ->
        match lookup (Id.to_string name) with
        | Some types when List.length types = List.length args ->
          let is_enter = Id.equal name id_enter in
          let args' = List.map2 (fun ty arg ->
            if should_move_in_group ~is_enter idx ty arg
            then CPPmove arg else arg
          ) types args in
          Sexpr (CPPfun_call (call_opaque, callee, of_reversed ([CPPstruct_id (name, targs, args')])))
        | _ -> List.nth pushes idx
      ) push_data
    in
    let rec on_stmts ~decl_owned match_owned = function
      | [] -> []
      | (Sasgn (id, (Declare ty), _) as s) :: rest
        when is_owned_decl_type ty ->
        on_stmt ~decl_owned match_owned s
        :: on_stmts ~decl_owned:(id :: decl_owned) match_owned rest
      | s :: rest when is_frame_push s ->
        let more, after = take_while is_frame_push rest in
        let group = s :: more in
        if List.length group >= 2 then
          process_push_group ~decl_owned match_owned group
          @ on_stmts ~decl_owned match_owned after
        else
          on_stmt ~decl_owned match_owned s
          :: on_stmts ~decl_owned match_owned rest
      | s :: rest ->
        on_stmt ~decl_owned match_owned s
        :: on_stmts ~decl_owned match_owned rest
    and on_stmt ~decl_owned match_owned = function
      | Sexpr (CPPfun_call (_, callee, {rev = [CPPstruct_id (name, targs, args)]})) as s -> (
        let owned_vars = decl_owned @ match_owned in
        match lookup (Id.to_string name) with
        | Some types ->
          let is_enter = Id.equal name id_enter in
          Sexpr
            (CPPfun_call
               (call_opaque, callee,
                of_reversed
                  [CPPstruct_id (name, targs,
                    adjust_args ~is_enter ~owned_vars types args)]))
        | None -> map_stmt Fun.id (on_stmt ~decl_owned match_owned) Fun.id s )
      | Smatch (scrut, branches, default) ->
        let branches' =
          List.map
            (fun br ->
              let new_owned =
                owned_bindings_of_branch ~owned:scrut.sc_owned br
              in
              { br with smb_body =
                on_stmts ~decl_owned:[] (new_owned @ match_owned) br.smb_body })
            branches
        in
        let default' =
          Option.map (on_stmts ~decl_owned:[] match_owned) default
        in
        Smatch (scrut, branches', default')
      | Sif (cond, then_body, else_body) ->
        Sif (cond,
          on_stmts ~decl_owned match_owned then_body,
          on_stmts ~decl_owned match_owned else_body)
      | Sblock body ->
        Sblock (on_stmts ~decl_owned match_owned body)
      | Scustom_case (ty, scrut, tyargs, branches, err) ->
        Scustom_case (ty, scrut, tyargs,
          List.map (fun (ps, rty, body) ->
            (ps, rty, on_stmts ~decl_owned match_owned body))
            branches,
          err)
      | s -> map_stmt Fun.id (on_stmt ~decl_owned match_owned) Fun.id s
    in
    on_stmts ~decl_owned:[] [] stmts

(** Build one branch of the frame-dispatch [Smatch].

    The loop variable [_frame] is the scrutinee; the frame struct type is
    represented as [Tvar(0, Some name)] (avoids the struct-name qualification
    that [Tid] would add); [_f] is the [const auto&] binding that gives the
    handler body access to the saved frame fields.

    @param frame_name Name of the frame struct (e.g. ["_Enter"], ["_Call1"])
    @param body       Handler body statements
    @return An [smatch_branch] for use under {!frame_scrutinee} *)
let make_frame_branch frame_name body =
  { smb_ctor_type = Tid_external (frame_name, []);
    smb_var = Some (id_f);
    smb_field_bindings = [];
    smb_extra_conds = [];
    smb_body = body }

(** The scrutinee of the frame-dispatch match: the loop variable [_frame],
    owned (it was moved off the stack) and held as a variant. *)
let frame_scrutinee =
  { sc_expr = CPPvar id_frame;
    sc_access = Aarrow;
    sc_owned = true;
    sc_flat = false }

(** Generate the while-loop body and surrounding boilerplate for the
    frame-dispatch loop.  Each iteration moves the top frame into a local,
    pops the stack, then dispatches via an [Smatch] if/else-if chain.

    @param struct_defs The struct definitions ([_Enter], [_CallN], etc.)
    @param ret_ty      Return type for the [_result] declaration
    @param init_push   The initial stack-push statement
    @param branches    One [smatch_branch] per frame type, in dispatch order
    @return Complete statement list for the loopified function body *)
let make_loop_and_return ?(fn_name : string option) struct_defs ret_ty init_push branches ~frame_names =
  let result_decl = Sdecl_init (id_result, ret_ty) in
  let frame_ty = Tid_external (Id.to_string id_Frame, []) in
  (* [crane::small_vector] rather than [std::vector]: the frame stack is only
     as deep as the recursion it replaced, so for the overwhelming majority of
     calls it never exceeds the inline capacity.  A [std::vector] with
     [reserve(8)] paid one heap allocation on *every* call regardless -- and
     loopified comparison functions are called once per key comparison, so
     that allocation showed up as a third of all allocations in a
     comparison-heavy workload. *)
  Table.mark_needs_small_vector ();
  let vector_ty =
    Tid_external (Crane_rt.small_vector, [frame_ty])
  in
  let stack_id = id_stack in
  let stack_decl = Sdecl (stack_id, vector_ty) in
  (* An exhaustive if/else-if chain; no wildcard needed, since the variant can
     only hold the listed frame types. *)
  let dispatch_stmt = Smatch (frame_scrutinee, branches, None) in
  let loop_body =
    [
      Sasgn (id_frame, Declare frame_ty,
             CPPmove
               (CPPfun_call
                  (call_opaque, CPPaccess (Adot, CPPvar (id_stack),
                              id_back), of_reversed [])));
      Sexpr
        (CPPfun_call
           (call_opaque, CPPaccess (Adot, CPPvar (id_stack),
                       id_pop_back), of_reversed []));
      dispatch_stmt;
    ]
  in
  let loop_comment =
    let all_names = "_Enter" :: frame_names in
    let prefix = match fn_name with
      | Some name -> "Loopified " ^ name ^ ": "
      | None -> "Frame dispatch: "
    in
    prefix ^ String.concat " -> " all_names ^ "."
  in
  struct_defs
  @ [
      result_decl;
      stack_decl;
      init_push;
      Scomment loop_comment;
      Swhile
        (CPPunop (Unot,
                  CPPfun_call
                    (call_opaque, CPPaccess (Adot, CPPvar (id_stack),
                                id_empty), of_reversed [])),
         loop_body);
      Sreturn (Some (CPPvar (id_result)));
    ]

(** Rewrite variable references and field accesses on lambda-scoped variables
    to use std::declval, so that decltype expressions are valid at struct
    definition scope.  E.g., [_args.d_a0] becomes
    [std::declval<CtorType&>().d_a0] and plain [b] becomes
    [std::declval<unsigned int&>()].

    @param env      Type environment mapping variable [Id.t]s to their types,
                    used to resolve the concrete type for [std::declval]
    @param expr     Expression to rewrite
    @return [expr] with in-scope variable and field-access references replaced
            by [std::declval]-based equivalents safe at struct scope *)
(* Enclosing-scope variables referenced anywhere inside [body], in order of
   first occurrence.  A name is "enclosing" exactly when [env] knows its type;
   anything declared inside the lambda itself (its parameters, its locals) is
   absent from [env] and so is correctly left alone. *)
let collect_env_vars env body =
  let acc = ref [] in
  let add id =
    if not (List.exists (Id.equal id) !acc) && lookup_var_type env id <> None
    then acc := !acc @ [id]
  in
  let rec fe e =
    (match e with
     | CPPvar id -> add id
     | CPPlambda
       { cl_body = lbody;
         _ } -> List.iter (fun s -> ignore (fs s)) lbody
     | _ -> ());
    map_expr fe Fun.id Fun.id e
  and fs s = map_stmt fe fs Fun.id s in
  List.iter (fun s -> ignore (fs s)) body;
  !acc

let rec rewrite_field_access_for_decltype env expr =
  match expr with
  | CPPfun_call (_, CPPlambda
    { cl_params = params;
      cl_ret = rt;
      cl_body = body;
      _ }, args)
    when body <> [] && collect_env_vars env body <> [] ->
    (* An immediately-invoked lambda -- Crane's encoding of a local [fix] used
       in expression position.  Substituting [std::declval] for the captured
       variables *inside* the body would put it in evaluated context, where its
       [static_assert] fires ("declval can only be used in an unevaluated
       context").  The body is a real function body even though the surrounding
       [decltype] is not evaluated.

       So lift the captures to parameters instead and pass the [declval]s as
       call arguments, which is the position [decltype] makes unevaluated:

         decltype([](lst& _c0, uint64_t& _c1) { ...uses _c0, _c1... }
                    (std::declval<lst&>(), std::declval<uint64_t&>()))

       The capture-default is dropped for the same reason it is dropped on
       plain lambdas below: a lambda in an unevaluated operand may not capture.
       The body is left untouched -- with the captures now parameters, it needs
       no rewriting. *)
    let free = collect_env_vars env body in
    let extra =
      List.map
        (fun id ->
          (Tref (Lvalue, strip_ref_type (Option.get (lookup_var_type env id))), Some id))
        free
    in
    (* Both lambda parameters and call arguments are stored reversed relative
       to their printed order, so the new trailing entries go at the head of
       each list -- and in the same orientation, so the two line up. *)
    let extra_args = List.map (fun (ty, _) -> CPPdeclval ty) extra in
    CPPfun_call
      (call_opaque, CPPlambda
        { cl_params = of_reversed (extra @ to_reversed params);
          cl_tparams = [];
          cl_ret = rt;
          cl_body = body;
          cl_capture = Immediate },
        of_reversed
          ( extra_args
          @ List.map (rewrite_field_access_for_decltype env) (to_reversed args)
          ) )
  | CPPvar id ->
    ( match lookup_var_type env id with
    | Some ty ->
      let base_ty = strip_ref_type ty in
      CPPdeclval (Tref (Lvalue, base_ty))
    | None -> expr )
  | CPPget (CPPvar id, field) ->
    (* Dot access on a variable.  Strip const to get the struct type for
       std::declval. *)
    ( match lookup_var_type env id with
    | Some ty ->
      let base_ty = strip_ref_type ty in
      let struct_ty =
        match base_ty with
        | Tconst t -> t
        | t -> t
      in
      CPPaccess (Adot, CPPdeclval (Tref (Lvalue, struct_ty)), field)
    | None -> expr )
  | CPPaccess (Aarrow, CPPvar id, field) ->
    (* Arrow access on a pointer variable — used by Smatch bindings
       ([_m->d_field] from [std::get_if]) and loopify frame dispatch. *)
    ( match lookup_var_type env id with
    | Some ty ->
      let base_ty = strip_ref_type ty in
      let pointee_ty =
        match base_ty with
        | Tptr (Tconst t) | Tptr t -> t
        | t -> t
      in
      CPPaccess (Adot, CPPdeclval (Tref (Lvalue, pointee_ty)), field)
    | None -> expr )
  | CPPlambda ({cl_body = body; _} as l) ->
    (* Rewrite variables inside the lambda body to use std::declval, and remove
       any capture-default so the lambda is valid inside decltype (which is an
       unevaluated context where capture-defaults are not allowed in C++23). *)
    let fe = rewrite_field_access_for_decltype env in
    let rec fs stmt = map_stmt fe fs Fun.id stmt in
    CPPlambda {l with cl_body = List.map fs body; cl_capture = Immediate}
  | _ ->
    map_expr (rewrite_field_access_for_decltype env) Fun.id Fun.id expr

(** Build a [std::decay_t<decltype(expr)>] type, suitable for struct field type annotations
    when the actual type is unknown. Rewrites variable references to use
    std::declval so that decltype is valid at struct definition scope.

    @param env      Type environment for resolving variable types in the
                    [decltype] expression
    @param expr     The expression whose type to capture via [decltype]
    @return [std::decay_t<decltype(rewritten_expr)>] where [rewritten_expr] uses
            [std::declval] for any in-scope variables *)
let make_decltype_ty env expr =
  let expr = rewrite_field_access_for_decltype env expr in
  Tdecay (Texpr_type expr)

(** Fix bindings in a continuation frame handler for fields that became
    pointer-safe after [compute_frame_pointer_safe].

    When a frame field is pointer-safe, its C++ type changes from [T] to
    [const T*].  The handler body (generated by [make_cont_bindings] before
    pointer-safe computation) has bindings of the form:
      [T id = std::move(_f.field)]  — invalid: field is [const T*], not [T]
    This function replaces those with a const-reference binding:
      [const T& id = *(_f.field)]   — dereference the pointer (zero copy)

    A reference binding is preferred over a plain pointer copy because:
    - Lambda captures ([=]) copy the referenced value by value (semantics preserved)
    - Method calls ([id.foo()]) work directly without an extra dereference
    - [&id] in pointer-safe push args gives back the original raw pointer

    The subsequent [adjust_frame_push_args] pass then rewrites [_Enter{id}] and
    [_CallN{..., id, ...}] push arguments at pointer-safe positions to [&id],
    recovering the [const T*] that those frames expect.

    Only processes top-level [Sasgn] statements in the handler body, which is
    all that [make_cont_bindings] generates.  Does not recurse into nested
    statement structures (inner lambdas, visitor branches, etc.).

    @param field_names  Field names of the frame struct (from [cf_field_names])
    @param cf_ps        Pointer-safe flags for each field (from [frame_ps_for])
    @param handler      The handler body to fix
    @return Fixed handler body with pointer-safe bindings adjusted *)
let fix_handler_bindings field_names cf_ps handler =
  let ps_field_ids =
    List.filter_map
      (fun (safe, name) -> if safe then Some name else None)
      (List.combine cf_ps field_names)
  in
  if ps_field_ids = [] then handler
  else
    let is_ps_field_access = function
      | CPPaccess (Adot, CPPvar f, field_id)
        when Id.equal f id_f ->
        List.exists (Id.equal field_id) ps_field_ids
      | _ -> false
    in
    let remapped = ref [] in
    let fixed =
      List.map
        (fun stmt ->
          match stmt with
          | Sasgn (id, Declare orig_ty, CPPmove e) when is_ps_field_access e ->
            let base_ty = match orig_ty with
              | Tshared_ptr inner -> inner
              | _ -> strip_ref_and_const_type orig_ty
            in
            remapped := id :: !remapped;
            Sasgn (id, Declare (Tref (Lvalue, Tconst base_ty)), CPPderef e)
          | Sasgn (id, Declare orig_ty, e) when is_ps_field_access e ->
            let base_ty = match orig_ty with
              | Tshared_ptr inner -> inner
              | _ -> strip_ref_and_const_type orig_ty
            in
            remapped := id :: !remapped;
            Sasgn (id, Declare (Tref (Lvalue, Tconst base_ty)), CPPderef e)
          | s -> s)
        handler
    in
    (* Rewrite CPPderef(CPPvar x) → CPPvar x for remapped IDs.
       After rebinding as [const T &x = *_f.field], any [*x] expression that
       previously dereferenced the shared_ptr is now a double-dereference of a
       reference, which is invalid.  Replace with [x] directly. *)
    if !remapped = [] then fixed
    else
      let rids = !remapped in
      let rec fe e = match e with
        | CPPderef (CPPvar x) when List.exists (Id.equal x) rids -> CPPvar x
        | e -> map_expr fe Fun.id Fun.id e
      in
      let rec fs s = map_stmt fe fs Fun.id s in
      List.map fs fixed

(** Transform a non-tail recursive function body using an explicit frame-based stack.

    Non-tail recursion requires saving continuation context. We use typed frames
    stored in a [std::variant] stack. Each frame captures the state needed to
    resume after a recursive call returns.

    {v
    let rec f x = if base(x) then result else combine(x, f(next(x)))

    becomes:

    struct _Enter { T x; };
    struct _Call1 { T _s0; };  // saves 'x' for combine step
    using _Frame = std::variant<_Enter, _Call1>;

    let f x_init =
      std::vector<_Frame> _stack;
      _stack.emplace_back(_Enter{x_init});
      T _result;
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          if (base(_f.x)) { _result = result; }
          else {
            _stack.emplace_back(_Call1{_f.x});        // save x
            _stack.emplace_back(_Enter{next(_f.x)});  // recurse
          }
        } else {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = combine(_f._s0, _result);
        }
      }
      return _result;
    v}

    Frame types:
    - [_Enter]: Captures function arguments (the "call" part of a recursive call)
    - [_CallN]: Captures continuation context (values needed after a call returns)

    The transformation:
    1. Identifies varying vs invariant parameters
    2. Rewrites [_Enter] handler: returns → frame pushes
    3. Collects [_CallN] frame info during rewriting
    4. Generates frame struct definitions
    5. Generates the dispatch loop as an if/else-if chain over the frame

    @param fn_name  Optional function name used to annotate the generated
                    [while] loop comment (aids readability of the emitted C++)
    @param check    Call checker for identifying recursive calls
    @param tparams  Template parameter context of the enclosing function
    @param params   Function parameters [(id, type)]
    @param ret_ty   Return type of the function
    @param body     Function body statements
    @return Transformed body with frame-based stack structure, or the original
            [body] unchanged when the transformation is unsafe (branch
            dependencies on recursive calls) *)
let transform_nontail ?(fn_name : string option) ?adopted ?(outer_env = [])
    check tparams params ret_ty body =
  (* An adopted body becomes a second entry point of this machine rather than
     a machine of its own: two machines cannot unwind each other's stack, so
     loopifying them separately leaves the recursion in place.  The calls that
     enter it are recursive calls of this machine targeting entry 1, and the
     bindings it leaves dead are dropped.

     It is entered with its own parameters {e and} the variables it captures
     from this function's scope, which are in scope for a lambda but not for a
     dispatch loop re-entering it from a popped frame.  A capture whose type
     this function cannot name is not something a frame can carry, so the
     adoption is abandoned rather than guessed at -- and that is settled
     before anything routes a call to entry 1, which an abandoned adoption
     never registers.

     A template parameter is no capture: it is named wherever the function
     is, the dispatch loop included, and [_tcI0::size(n)] mentions a
     dictionary's type, not a value a frame could carry. *)
  let adopted =
    Option.bind adopted (fun ad ->
        let is_tparam id = List.exists (fun (_, t) -> Id.equal t id) tparams in
        let ad =
          { ad with
            ad_captures = List.filter (fun id -> not (is_tparam id)) ad.ad_captures }
        in
        (* A body yielding another type -- the inlined partner of a mutual
           recursion over two types, [dbl_md] inside [dbl_e] -- cannot share
           the one [_result]. *)
        let yields_other =
          match ad.ad_ret with
          | Some t -> (
            let t = strip_ref_and_const_type t
            and r = strip_ref_and_const_type ret_ty in
            match (t, r) with
            | Tdecay (Texpr_type _), _ | _, Tdecay (Texpr_type _) -> false
            | _ -> ( try t <> r with Invalid_argument _ -> false ) )
          | None -> false
        in
        (* A parameter only a generic lambda can declare ([auto &&]) is not a
           type a frame can store it at. *)
        let unnameable_param =
          List.exists
            (fun (_, ty) -> strip_ref_and_const_type ty = Tauto)
            ad.ad_params
        in
        if yields_other || unnameable_param then None
        else
        let env = collect_type_env body @ params in
        let capture_params =
          List.filter_map
            (fun id -> Option.map (fun ty -> (id, ty)) (List.assoc_opt id env))
            ad.ad_captures
        in
        if List.length capture_params <> List.length ad.ad_captures then None
        else Some (ad, capture_params) )
  in
  let check =
    match adopted with
    | None -> check
    | Some (ad, _) -> any_checker [check; adopted_checker ~entry:1 ad]
  in
  let body =
    match adopted with
    | None -> body
    | Some (ad, _) -> ad.ad_install body
  in
  (* This function's own parameters are described by the calls that re-enter
     it, not by those targeting an adopted fixpoint. *)
  let own = only_entry 0 check in
  let varying = find_varying_params own params body in
  let binding_env = collect_binding_env body in
  let pointer_safe = tail_pointer_safe_flags own params body ~binding_env () in
  (* Loopifying a function on its own gives a machine with one entry: the
     function itself, entered through [_Enter]. *)
  let own_entry = machine_entry ~enter_id:id_enter ~params ~varying in
  let pointer_safe_varying = filter_by_mask varying pointer_safe in
  (* Build initial type env from params and body declarations, then what the
     enclosing scope binds: a local fixpoint's frame saves the variables it
     captures as well as its own. *)
  let env =
    collect_type_env body @ List.map (fun (id, ty) -> (id, ty)) params
    @ outer_env
  in
  (
  (* Rewrite body for Enter handler and collect call frame info *)
  let call_counter = ref 1 in
  let frames_ref = ref [] in
  let invariant_params =
    List.fold_left2 (fun acc (id, _) v ->
      if not v then Id.Set.add id acc else acc)
      Id.Set.empty params varying
  in
  (* Entry 1, when a body was adopted.  Every one of its parameters varies --
     each re-entry rebinds them -- so the mask is all-true. *)
  let adopted_entry =
    Option.map
      (fun (ad, capture_params) ->
        let params = ad.ad_params @ capture_params in
        ( ad,
          machine_entry
            ~enter_id:(Id.of_string ("_Enter_" ^ ad.ad_name))
            ~params
            ~varying:(List.map (fun _ -> true) params) ) )
      adopted
  in
  let entries =
    own_entry
    :: (match adopted_entry with Some (_, en) -> [en] | None -> [])
  in
  let ctx = { er_check = check; er_entries = entries;
               er_tparams = tparams;
               er_env = env;
               er_call_counter = call_counter; er_frames_ref = frames_ref;
               er_branch_ctx = None;
               er_seen_frame_names = Hashtbl.create 16;
               er_invariant_params = invariant_params;
               er_rematerialized = [] }
  in
  (* Each top-level statement is rewritten on its own, but a binding it makes
     is still one a later statement's continuation may rebuild. *)
  let rewritten_body =
    List.rev
      (fst
         (List.fold_left
            (fun (acc, ctx) st -> (rewrite_enter_stmt ctx st :: acc, with_rematerialized ctx st))
            ([], ctx) body ))
  in
  (* The adopted entry's handler is that body, rewritten under a context
     describing its parameters rather than this function's.  Both handlers
     share the frame accumulator and the call counter, so the resume frames
     either of them needs land in this one machine -- which is why this runs
     before the frames are collected below. *)
  let adopted_emission =
    match adopted_entry with
    | None -> []
    | Some (ad, en) ->
      let ctx1 =
        { ctx with
          er_env = env @ en.en_params;
          er_invariant_params = Id.Set.empty }
      in
      [entry_emission en (rewrite_enter_stmts ctx1 ad.ad_body)]
  in
  (* Sort frames by name to ensure consistent ordering *)
  let frames =
    List.sort (fun a b -> String.compare a.cf_name b.cf_name) !frames_ref
  in
  (* Compute pointer-safe flags for Call frames *)
  let frame_ps_map =
    compute_frame_pointer_safe pointer_safe_varying frames
  in
  (* One emission per entry point, in {!entries} order. *)
  let emissions =
    entry_emission ~pointer_safe:pointer_safe_varying own_entry rewritten_body
    :: adopted_emission
  in
  let ee_name ee = Id.to_string ee.ee_id in
  let all_frame_ps =
    List.map
      (fun ee ->
        (ee_name ee, List.map (fun p -> p.fp_pointer_safe) ee.ee_params) )
      emissions
    @ frame_ps_map
  in
  let frame_sptr =
    List.filter_map (fun cf ->
      let flags = List.map contains_shared_ptr (cf_saved_types cf) in
      if List.exists Fun.id flags then Some (cf.cf_name, flags) else None)
      frames
  in
  (* Build struct definitions *)
  (* The type a frame struct stores a value of type [ty] at.
     [strip_ref_and_const_type] removes the [const T&] wrapper that e.g. a
     [const unsigned int &fuel] param carries: keeping [const] in the field
     would prevent the struct from being move-assignable (breaks
     [std::variant] in some compilers).  A forwarding parameter is the one
     case that needs [std::decay_t]: its [F1] is deduced as [L &] for an
     lvalue argument, and a field of that type is a reference the frame
     cannot rebind to what it moves in.  Any other template parameter is
     deduced from a [const T &] or a value and is never a reference. *)
  let frame_field_type ty =
    match ty with
    | Tref (Forwarding, t) -> Tdecay (strip_ref_and_const_type t)
    | ty -> strip_ref_and_const_type ty
  in
  let entry_fields ee =
    List.map
      (fun p ->
        match p.fp_pointer_safe, borrowed_value_param_pointee p.fp_ty with
        | true, Some t -> (p.fp_name, Tptr (Tconst t))
        | _ -> (p.fp_name, frame_field_type p.fp_ty) )
      ee.ee_params
  in
  let frame_description cf =
    let field_names_str =
      if (cf_field_names cf) = [] then ""
      else
        let names = List.map Id.to_string (cf_field_names cf) in
        " saves [" ^ String.concat ", " names ^ "],"
    in
    let name = cf.cf_name in
    if Common.contains_substring name "_Resume" then
      name ^ ":" ^ field_names_str ^ " resumes after recursive call with _result."
    else if Common.contains_substring name "_Combine" then
      name ^ ": receives partial results, combines with _result from final call."
    else if Common.contains_substring name "_After" then
      name ^ ":" ^ field_names_str ^ " dispatches next recursive call."
    else if Common.contains_substring name "_Final" then
      name ^ ": rebuilds expression after inner recursive call resolves."
    else if Common.contains_substring name "_Inter" then
      name ^ ": dispatches main recursive call after inner call resolves."
    else if Common.contains_substring name "_Cont" then
      name ^ ":" ^ field_names_str ^ " resumes after recursive call, then processes rest."
    else
      "Frame: saves" ^ field_names_str ^ " across recursive call."
  in
  (* Find the first Sreturn expression in a lambda body, for return-type inference. *)
  let rec extract_lambda_return_expr = function
    | [] -> None
    | Sreturn (Some e) :: _ -> Some e
    | Sif (_, then_body, else_body) :: rest ->
      (match extract_lambda_return_expr then_body with
       | Some e -> Some e
       | None ->
         match extract_lambda_return_expr else_body with
         | Some e -> Some e
         | None -> extract_lambda_return_expr rest)
    | Sblock stmts :: rest ->
      (match extract_lambda_return_expr stmts with
       | Some e -> Some e
       | None -> extract_lambda_return_expr rest)
    | _ :: rest -> extract_lambda_return_expr rest
  in
  let compute_frame_field_types cf cf_ps =
    map2_exn ~what:"compute_frame_field_types"
      (fun ps {ss_ty = ty; ss_expr = expr; _} ->
        if ps then
          match ty with
          | Tshared_ptr inner -> Tptr (Tconst inner)
          | _ -> Tptr (Tconst (strip_ref_and_const_type ty))
        else
          match ty with
          | Tunresolved | Tauto ->
            let inferred = infer_saved_type tparams cf.cf_env expr in
            (match inferred with
            | None | Some Tauto ->
              (* For lambda expressions whose return type can't be inferred
                 (e.g., a method call like a1_value.length()), generate
                 std::function<decltype(body_ret_expr)(params)> instead of
                 std::decay_t<decltype(lambda)>.  The lambda in decltype at
                 struct definition scope and the actual stored lambda are
                 different C++ types, so std::decay_t<decltype(lambda)> does
                 not work.  std::function accepts any callable with a
                 matching signature. *)
              let base_expr = match expr with CPPmove e -> e | e -> e in
              (match base_expr with
               | CPPlambda {cl_params = params; cl_body = body; _} ->
                 let param_types =
                   List.map (fun (ty, _) -> strip_ref_and_const_type ty)
                     (to_reversed params)
                 in
                 (match extract_lambda_return_expr body with
                  | Some ret_expr ->
                    let rewritten = rewrite_field_access_for_decltype cf.cf_env ret_expr in
                    Tfun (param_types, Tdecay (Texpr_type rewritten))
                  | None -> make_decltype_ty cf.cf_env expr)
               | _ -> make_decltype_ty cf.cf_env expr)
            | Some ty -> ty)
          | _ -> frame_field_type ty)
      cf_ps cf.cf_slots
  in
  let frame_ps_for cf =
    match List.assoc_opt cf.cf_name frame_ps_map with
    | Some flags -> flags
    | None -> List.map (fun _ -> false) (cf_saved_types cf)
  in
  let call_structs =
    List.concat_map
      (fun cf ->
        let cf_ps = frame_ps_for cf in
        let field_tys = compute_frame_field_types cf cf_ps in
        let fields =
          map2_exn ~what:"call_struct_fields"
            (fun s ty -> (s.ss_field, ty))
            cf.cf_slots field_tys
        in
        [Scomment (frame_description cf);
         Sstruct_def (Id.of_string cf.cf_name, fields)])
      frames
  in
  let call_names = List.map (fun cf -> cf.cf_name) frames in
  let variant_tys =
    List.map (fun ee -> Tid_external (ee_name ee, [])) emissions
    @ List.map (fun name -> Tid_external (name, [])) call_names
  in
  let struct_defs =
    List.concat_map
      (fun ee ->
        [Scomment
           (ee_name ee
           ^ ": captures varying parameters for each recursive call.");
         Sstruct_def (ee.ee_id, entry_fields ee)])
      emissions
    @ call_structs
    @ [Susing (id_Frame, Tvariant variant_tys)]
  in
  let frame_field_types =
    List.map (fun ee -> (ee_name ee, List.map snd (entry_fields ee))) emissions
    @ List.map
         (fun cf -> (cf.cf_name, compute_frame_field_types cf (frame_ps_for cf)))
         frames
  in
  (* The machine is entered at its first entry point: that is the call the
     caller made. *)
  let init_push =
    match emissions with
    | ee :: _ -> make_stack_init ee.ee_params
    | [] -> CErrors.anomaly (Pp.str "loopify: frame machine with no entry point")
  in
  (* Identify varying params that are moved into the Enter handler (not passed
     as pointers).  For these, the Smatch scrutinee should use [v_mut()] so
     that [shared_ptr] child fields are mutable and can be moved into the next
     [_Enter] frame (avoiding an unnecessary refcount bump).

     Mirrors [make_param_copies.bind_field] exactly: use [strip_ref_type]
     (not [strip_ref_and_const_type]) so that [const T&] params (which are
     bound as [const T& id = _f.id], not moved) are excluded. *)
  let owned_varying_names ee =
    List.filter_map
      (fun p ->
        if p.fp_pointer_safe then None
        else
          match strip_ref_type p.fp_ty with
          | Tconst _ -> None  (* const-ref bind: not owned *)
          | Tglob (r, _, _) when Table.is_coinductive r -> None
          | t when not (is_trivially_copyable_type t) -> Some p.fp_name
          | _ -> None )
      ee.ee_params
  in
  (* Enter handler: copy frame fields to locals (only varying params; invariant
     params are captured directly from function scope) *)
  let entry_branch ee =
    let owned = owned_varying_names ee in
    let body =
      if owned = [] then ee.ee_body
      else make_owned_param_matches owned ee.ee_body
    in
    let field_keys =
      List.filter_map (fun (id, ty) ->
        if worthwhile_move_type (strip_ref_and_const_type ty)
        then Some (frame_field_key id) else None)
      (entry_fields ee)
    in
    let is_cand key =
      key = Id.to_string id_result || List.mem key field_keys
    in
    let handler =
      make_param_copies ee.ee_params
      @ adjust_frame_push_args ~binding_env ~frame_sptr all_frame_ps body
      |> optimize_frame_push_args frame_field_types
      |> optimize_last_use_moves
           ~self_ref_candidate:is_cand
           ~last_use_candidate:is_cand
    in
    make_frame_branch (ee_name ee) handler
  in
  let enter_branches = List.map entry_branch emissions in
  (* Call handlers — fix pointer-safe field bindings, then adjust push args *)
  let call_branches =
    List.map
      (fun cf ->
        let cf_ps = frame_ps_for cf in
        (* Step 1: fix [T id = std::move(_f.field)] → [const T& id = *(_f.field)]
           for pointer-safe fields so that downstream lambda captures and method
           calls still work on value-typed [id]. *)
        let handler =
          if List.exists Fun.id cf_ps then
            fix_handler_bindings (cf_field_names cf) cf_ps cf.cf_handler
          else cf.cf_handler
        in
        (* Step 2: adjust push arguments at pointer-safe positions.  After
           fix_handler_bindings, pointer-safe locals are [const T&] references;
           [adjust_frame_push_args] converts [_Enter{id}] → [_Enter{&id}] so
           that [const T&] is passed as [const T*] as the frame struct expects. *)
        (* Guard on [all_frame_ps], not [frame_ps_map]: a handler that has no
           pointer-safe fields of its own can still push an [_Enter] frame whose
           fields are pointer-safe, and that push needs adjusting too. *)
        let handler =
          if all_frame_ps <> [] then
            let cf_binding_env = collect_binding_env handler in
            adjust_frame_push_args ~binding_env:cf_binding_env ~frame_sptr all_frame_ps handler
          else handler
        in
        let cf_types = compute_frame_field_types cf (frame_ps_for cf) in
        let cf_field_keys =
          List.filter_map (fun (id, ty) ->
            if worthwhile_move_type (strip_ref_and_const_type ty)
            then Some (frame_field_key id) else None)
          (List.combine (cf_field_names cf) cf_types)
        in
        let is_cf_cand key =
          key = Id.to_string id_result || List.mem key cf_field_keys
        in
        make_frame_branch cf.cf_name
          (handler
           |> optimize_frame_push_args frame_field_types
           |> optimize_last_use_moves
                ~self_ref_candidate:is_cf_cand
                ~last_use_candidate:is_cf_cand))
      frames
  in
  let result =
    make_loop_and_return ?fn_name struct_defs ret_ty init_push
      (enter_branches @ call_branches) ~frame_names:call_names
    |> unmove_invariant_params invariant_params
  in
  if Table.reuse () then borrow_frame_bound_matches result else result
  )
