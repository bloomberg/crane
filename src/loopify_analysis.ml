(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Recursive-call analysis for {!Loopify}: the named constants and utilities the
    strategies share, the mutual-recursion table, outcome diagnostics, call
    checkers and call collection, invariant-parameter detection, and the
    substitutions the rewrites use. *)

open Names
open Minicpp

(** {2 Named Constants}

    Frequently used [Id.t] values, defined once to avoid repeated
    [Id.of_string] allocations across ~95 call sites. *)

let id_result       = Id.of_string "_result"
let id_enter        = Generated_name.id "Enter"
let id_f            = Id.of_string "_f"
let id_stack        = Id.of_string "_stack"
let id_head         = Id.of_string "_head"
let id_write        = Id.of_string "_write"
let id_frame        = Id.of_string "_frame"
let id_Frame        = Generated_name.id "Frame"
let id_self         = Id.of_string "_self"

(** The move-analysis key for a read of the frame field [_f.x].  Reads of a
    frame field and reads of a plain local share one table, so the field's
    key is spelled once here rather than at each of the four sites that
    builds or tests one. *)
let frame_field_key field = Id.to_string id_f ^ "." ^ Id.to_string field

(* Perceus reuse cursor (see {!section:reuse-cursor}). *)
let id_own          = Id.of_string "_own"

(* A value-type result assembled in place (see {!Loopify_tmc.result_storage}). *)
let id_root         = Id.of_string "_root"
let id_node         = Id.of_string "_node"
let id_value        = Id.of_string "_value"
let id_emplace      = Id.of_string "emplace"
let id_uniq         = Id.of_string "_uniq"
let id_rstep        = Id.of_string "_rs"

(* Method names used with CPPaccess / CPPaccess_call *)
let id_get          = Id.of_string "get"

(* [lazy_]: the factory a coinductive type's cofixpoint body returns.  Its
   presence is how a cofixpoint is told from a fixpoint here. *)
let id_lazy         = Id.of_string "lazy_"

(* [crane_raw] (crane_fn.h): extracts a raw pointer from either a
   [std::shared_ptr<T>] or an already-raw [T*] (arena mode), by overload
   resolution.  Used in place of a bare [.get()] call wherever the extraction
   target may be either representation. *)
let id_v            = Id.of_string "v"
let id_v_mut        = Id.of_string "v_mut"
let id_empty        = Id.of_string "empty"
let id_emplace_back = Id.of_string "emplace_back"
let id_pop_back     = Id.of_string "pop_back"
let id_back         = Id.of_string "back"

(** Raised when a function's shape defeats a linearising transform -- for
    instance a self-call whose arity differs from the enclosing definition's, so
    that no per-parameter correspondence exists.  This is a limitation of the
    transform, not a broken invariant, so the caller turns it into a decline
    (original body preserved) rather than letting it abort the extraction. *)
exception Not_linearisable of string

(** {2 List utility helpers} *)

let rec list_take n = function
  | _ when n <= 0 -> []
  | [] -> []
  | x :: xs -> x :: list_take (n - 1) xs

let rec list_drop n = function
  | xs when n <= 0 -> xs
  | [] -> []
  | _ :: xs -> list_drop (n - 1) xs
let list_remove_at idx xs = List.filteri (fun i _ -> i <> idx) xs

(** [map2_exn ~what f l1 l2] is [List.map2] with the same descriptive-error
    contract as {!combine_exn}. *)
let map2_exn ~what f l1 l2 =
  let n1 = List.length l1 and n2 = List.length l2 in
  if n1 <> n2 then
    CErrors.anomaly
      (Pp.str
         (Printf.sprintf "loopify: %s expects equal-length lists (%d vs %d)"
            what n1 n2));
  List.map2 f l1 l2

(** [map3_exn ~what f l1 l2 l3] is [map2_exn] at three lists. *)
let map3_exn ~what f l1 l2 l3 =
  let pairs = map2_exn ~what (fun x y -> (x, y)) l1 l2 in
  map2_exn ~what (fun (x, y) z -> f x y z) pairs l3

(** {2 Generic AST predicate search}

    A single pair of mutually recursive functions that answer the question
    "does any expression in this AST satisfy [pred]?"  Used throughout the
    loopify pass to detect recursive calls, [CPPthis] references, [lazy_]
    factories, pointer-shadow variables, and more.

    Earlier versions of this file had three independent implementations of the
    same traversal.  This unified version delegates structural recursion to
    {!iter_expr_children} and {!iter_stmt_children} from {!Minicpp}, which
    already enumerate every constructor — so adding a new AST node to MiniCpp
    automatically makes it visible to every predicate here. *)

(** Return [true] when [pred] holds for [e] or any sub-expression reachable
    from [e], including inside lambda bodies.

    Short-circuits on the first match via an exception to avoid traversing
    the entire tree when only an existence check is needed.

    @param pred  Predicate to test on each expression node
    @param e     Root expression to search *)
let rec expr_exists (pred : cpp_expr -> bool) (e : cpp_expr) : bool =
  if pred e then true
  else
    try
      iter_expr_children
        ~on_expr:(fun e' -> if expr_exists pred e' then raise Exit)
        ~on_stmts:(fun ss -> if List.exists (stmt_exists pred) ss then raise Exit)
        e;
      false
    with Exit -> true

(** Return [true] when any expression within statement [s] satisfies [pred].
    Descends into all branches, conditions, scrutinees, reuse paths, and
    nested blocks.

    @param pred  Predicate to test on each expression node
    @param s     Statement to search *)
and stmt_exists (pred : cpp_expr -> bool) (s : cpp_stmt) : bool =
  try
    iter_stmt_children
      ~on_expr:(fun e -> if expr_exists pred e then raise Exit)
      ~on_stmts:(fun ss -> if List.exists (stmt_exists pred) ss then raise Exit)
      s;
    false
  with Exit -> true

(** Return [true] when any expression within a statement list satisfies [pred].
    Convenience wrapper around {!stmt_exists}.

    @param pred   Predicate to test on each expression node
    @param stmts  Statement list (function body) to search *)
let body_exists (pred : cpp_expr -> bool) (stmts : cpp_stmt list) : bool =
  List.exists (stmt_exists pred) stmts

(** Check whether a C++ return type is a value-type inductive (non-coinductive,
    non-enum bare [Tglob]).  When true, TMC must wrap [_head]/_write in
    [shared_ptr] because the constructor's recursive field is [shared_ptr].
    Handles [Tnamespace] wrapping for out-of-line (.cpp) method definitions. *)
let rec is_value_type_ret = function
  | Tglob (r, _, _) -> not (Table.is_coinductive r) && not (Table.is_custom r)
  | Tnamespace (_, t) -> is_value_type_ret t
  | _ -> false

(** Whether a C++ type is trivially copyable (scalars, pointers, enums).
    For these types, copying is cheaper than indirecting through a reference,
    so frame-field bindings should remain copies rather than [const T&]. *)
let rec is_trivially_copyable_type = function
  | Tvoid | Tauto | Tunresolved | Tany -> true
  | Tptr _ | Tref _ -> true
  | Tconst t | Tnamespace (_, t) | Tqualified (t, _) ->
    is_trivially_copyable_type t
  | Tdecay (Texpr_type _) -> true
  | Tvar _ -> true
  | Tid (id, ts) -> is_trivially_copyable_named (Id.to_string id) ts
  | Tid_external (s, ts) -> is_trivially_copyable_named s ts
  | Tglob (r, ts, _) ->
    Table.is_enum_inductive r || Table.is_custom_scalar_ref r
    || Table.is_trivially_copyable_ref r
       && List.for_all is_trivially_copyable_type ts
  | _ -> false

(** Whether the named type [s] applied to [ts] is trivially copyable: its head
    is, and so is every argument.

    A scalar takes no arguments, so the second half is vacuous for the builtin
    names.  It is the whole question for a mapped type like [std::pair], which
    the user declares with [Crane TriviallyCopyable]. *)
and is_trivially_copyable_named s ts =
  Table.is_trivially_copyable_cpp_name s
  && List.for_all is_trivially_copyable_type ts

(** Returns [true] for types that are expensive to copy and benefit from
    [std::move]: [shared_ptr], value-type inductives, type variables, and
    types parameterized by such types.  A mapped type is one of them unless
    it is known to copy for free -- a scalar, or a type declared
    [Crane TriviallyCopyable] -- since its replacement text says nothing about
    what a copy costs: [Big] may be a class that owns a buffer. *)
let rec worthwhile_move_type = function
  | Tglob (r, tparams, _) -> not (Table.is_enum_inductive r)
                         && not (Table.is_coinductive r)
                         && (not (Table.is_custom r)
                             || List.exists worthwhile_move_type tparams
                             || not (Table.is_custom_scalar_ref r
                                     || Table.is_trivially_copyable_ref r))
  | Tshared_ptr _ | Tfun _ | Terased _ -> true
  | Tvariant ts -> List.exists worthwhile_move_type ts
  | Tid (_, ts) | Tid_external (_, ts) ->
    List.exists worthwhile_move_type ts
  | Tnondeduced t -> worthwhile_move_type t
  | Trebind (h, x) -> worthwhile_move_type h || worthwhile_move_type x
  | Thole -> false
  | Tref (Forwarding, t) -> worthwhile_move_type t
  | Texpr_type _ | Tdecltype_auto -> false
  | Tconst t | Tnamespace (_, t) | Tqualified (t, _) | Tapply (t, _)
  | Tref (Lvalue, t) ->
    worthwhile_move_type t
  | Tvar _ | Tinstance _ | Tpromoted _ -> true
  | Tdecay t -> worthwhile_move_type t
  | Ttyctor _ | Tptr _ | Tvoid | Tauto | Tunresolved | Tany | Topaque ->
    false

(* Global mutable state in this file and their reset granularity:
   - mutual_fn_table, outcomes : reset per generated file (State.Unit)
   - ctor_ptr_fields : accumulates across the full session; never cleared because
     struct shapes don't change within a Rocq session *)

(** {2 Mutual recursion table}

    Functions register their bodies here so mutual pairs can be detected and
    inlined during the loopify pass. Keyed by GlobRef. *)

(** A registered function definition, as an inlining site needs it.  The
    return type is carried because inlining a non-tail call builds a lambda
    around the body, and that lambda's return type is this one -- there is no
    reason for a later pass to go looking for it in the statements. *)
type registered_fn = {
  rf_ret_ty : cpp_type;  (** the function's declared return type *)
  rf_params : (Id.t * cpp_type) list;  (** its formal parameters *)
  rf_body : cpp_stmt list;  (** its body *)
}

(** Table mapping GlobRef → definition, for function definitions. *)
let mutual_fn_table : (GlobRef.t, registered_fn) Hashtbl.t = Hashtbl.create 32

(** Register a function definition for mutual recursion detection. Each
    [GlobRef.t] in [refs] maps to the function's definition. *)
let register_fundef
    (refs : (GlobRef.t * cpp_type list) list)
    (ret_ty : cpp_type)
    (params : (Id.t * cpp_type) list)
    (body : cpp_stmt list) =
  List.iter
    (fun (r, _) -> Hashtbl.replace mutual_fn_table r {rf_ret_ty = ret_ty; rf_params = params; rf_body = body})
    refs

(** [register_decl d] registers [d] with {!register_fundef} if it is a
    function definition, and does nothing otherwise.

    Callers pre-register a whole group of declarations before rendering any of
    them, so that the first one rendered can already see the last one in the
    mutual table. *)
let register_decl = function
  | Dfun {df_path; df_ret; df_shape = Ddef (params, body)}
  | Dtemplate (_, _, Dfun {df_path; df_ret; df_shape = Ddef (params, body)}) ->
    register_fundef (dfun_path_list df_path) df_ret params body
  | _ -> ()

(** Clear the mutual recursion table. Called between extraction units. *)
let clear_mutual_table () = Hashtbl.clear mutual_fn_table

let () = State.on_reset State.Unit clear_mutual_table

(** Table mapping constructor struct names to their shared_ptr field indices.
    Populated from [Dstruct] definitions in {!transform_decl} and queried by
    {!try_tmc_decompose} to determine which fields need [make_shared] wrapping
    in the direct-struct-construction path.

    The key pairs {!Common.ctor_owner_key} of the owning inductive with the
    capitalized constructor name (e.g., ["App"], ["Cons"]); the owner is part
    of it because a constructor name alone does not identify a struct -- two
    inductives may each have a [Cons], with different fields.  The value is a
    list of the constructor's pointer fields, by 0-based index. *)

(** A constructor field stored behind the smart pointer: a recursive one, which
    holds the inductive itself, or one [Crane BoxedFields] boxed for holding
    some other inductive. *)
type ptr_field = Recursive of int | Boxed of int

let ptr_field_index = function Recursive i | Boxed i -> i

let ctor_ptr_fields : (string * string, ptr_field list) Hashtbl.t = Hashtbl.create 32

(** The inductive a TMC cell belongs to, read off the cell's own type.  A
    factory call is always qualified by that type ([Type<...>::cons]), which
    is what makes the owner recoverable from the C++ AST alone. *)
let cell_owner = function Tglob (g, _, _) -> Some g | _ -> None

(** The registered name of field [field_idx] of a cell's constructor struct,
    or the positional fallback when the owner cannot be recovered. *)
let cell_field_name ~cell_ty ~ctor_name field_idx =
  match cell_owner cell_ty with
  | Some owner -> Common.lookup_ctor_field_name ~owner ctor_name field_idx
  | None -> Common.field_param_id field_idx

(** {2 Recursion classification} *)

(** Information about a single recursive call site. *)
type call_site = {
  cs_args : cpp_expr list;  (** Arguments to the recursive call *)
  cs_is_tail : bool;  (** Whether this call appears in tail position *)
  cs_entry : int;
      (** Which entry point of the frame machine this call targets, as an index
          into the machine's entry table. A function loopified on its own has
          exactly one entry, so this is [0]; it becomes meaningful once an
          enclosing function and a fixpoint local to it share a single stack,
          where a call selects which [CraneEnter]-style frame to push and hence
          which parameter analysis applies. *)
  cs_recv : cpp_expr option;
      (** For a method call, the receiver expression {e as written}, before
          {!method_checker} converts it to the raw pointer stored in frames.
          Callers that need to reason about the receiver's storage duration
          must consult this rather than the head of {!cs_args}, which is always
          a synthesised [&recv] or [crane_raw(recv)] and therefore says nothing
          about the original expression. [None] for non-method calls. *)
}

(** [mk_call_site args] is the call site a {!call_checker} reports for a
    recursive call taking [args].

    Tail position is not something a checker can see -- it is a property of
    where the call sits, which {!classify} determines -- so [cs_is_tail] starts
    [false] and is set by whoever has that context. [entry] defaults to the
    machine's first entry point, which is the only one a singly-loopified
    function has. *)
let mk_call_site ?(entry = 0) ?recv args =
  {cs_args = args; cs_is_tail = false; cs_entry = entry; cs_recv = recv}

(** Classification of a function body's recursion pattern. *)
type recursion_kind =
  | No_recursion  (** No recursive calls found *)
  | Tail_recursion  (** All recursive calls are in tail position *)
  | Nontail_recursion  (** At least one non-tail recursive call *)

(** {2 Diagnostics}

    Historically every bail-out in this pass silently returned the original
    recursive body, so a function that loopify could not handle was
    indistinguishable from one it chose not to touch.  That made the pass's
    coverage unmeasurable.  The machinery below records, for every recursive
    function the pass sees, which strategy fired or why it declined.

    A transform therefore returns {e what it did} alongside the body, rather
    than only the body: a bail-out hands back the body it was given, so
    "declined" is distinguishable from "transformed" only if the transform
    says which.  {!report_outcome} then re-classifies the {e transformed}
    body, so a strategy that silently left a self-call behind is reported as a
    decline too.  This postcondition is what makes the report trustworthy: it
    does not depend on every bail site remembering to announce itself. *)

(** What the pass did with one recursive function. *)
type loopify_outcome =
  | Lp_tail  (** Rewritten to a flat [while] loop by {!transform_tail}. *)
  | Lp_tmc  (** Rewritten by the tail-modulo-cons transform. *)
  | Lp_frame  (** Rewritten to an explicit frame stack. *)
  | Lp_deferred of string
      (** Intentionally not rewritten because the shape already runs in O(1)
          stack (e.g. a [lazy_]-wrapped cofixpoint body). Not a failure. *)
  | Lp_declined of string  (** Left as C++ recursion; the string is the reason. *)

let string_of_outcome = function
  | Lp_tail -> "tail loop"
  | Lp_tmc -> "tail-modulo-cons"
  | Lp_frame -> "frame stack"
  | Lp_deferred why -> "deferred (" ^ why ^ ")"
  | Lp_declined why -> "DECLINED: " ^ why

(** Outcomes recorded during the current extraction, most recent first. *)
let outcomes : (string * loopify_outcome) list ref = ref []

let clear_outcomes () = outcomes := []

let () = State.on_reset State.Unit clear_outcomes

(** How good an outcome is.  A function can be transformed more than once —
    {!transform_decl} is invoked independently from [Cpp_ind] and [Cpp_print],
    and only one of those results is emitted — so the same name can produce
    several outcomes per unit.  Only the best one describes the emitted code:
    if any attempt linearised the function, the C++ holds no self-call. *)
let outcome_rank = function
  | Lp_declined _ -> 0
  | Lp_deferred _ -> 1
  | Lp_tail | Lp_tmc | Lp_frame -> 2

let get_outcomes () =
  (* Keep first-seen order, but collapse each name to its best outcome. *)
  let best = Hashtbl.create 64 in
  let order = ref [] in
  List.iter
    (fun (name, outcome) ->
      match Hashtbl.find_opt best name with
      | Some prev when outcome_rank prev >= outcome_rank outcome -> ()
      | Some _ -> Hashtbl.replace best name outcome
      | None ->
        Hashtbl.add best name outcome;
        order := name :: !order)
    (List.rev !outcomes);
  List.rev_map (fun name -> (name, Hashtbl.find best name)) !order

(** Record one outcome.  Nothing is printed here: an outcome is only meaningful
    once every attempt at the same function has been seen, so reporting waits
    for {!report_outcomes} at the end of the unit. *)
let record_outcome name outcome =
  outcomes := (name, outcome) :: !outcomes

(** Print the collapsed outcomes when [Crane Loopify Diagnostics] is set, and
    raise when [Crane Loopify Strict] is set and any function was declined.
    Called once per compilation unit, after all decls have been transformed. *)
let report_outcomes ?(unit_name = "") () =
  let final = get_outcomes () in
  let where = if unit_name = "" then "" else unit_name ^ " " in
  if Table.loopify_diagnostics () then
    List.iter
      (fun (name, outcome) ->
        Feedback.msg_notice
          (Pp.str ("[loopify] " ^ where ^ name ^ ": " ^ string_of_outcome outcome)))
      final;
  if Table.loopify_strict () then
    List.iter
      (function
        | (name, Lp_declined why) ->
          CErrors.user_err
            (Pp.str ("loopify: cannot linearise " ^ name ^ " (" ^ why ^ ")"))
        | _ -> ())
      final

(** What {!apply_nontail_loopification} did with a body.  It chooses between
    the TMC and frame transforms internally, so it reports the choice here
    rather than leaving the caller to guess. *)
type nontail_result = {
  nt_body : cpp_stmt list;  (** The body to emit, transformed or original. *)
  nt_outcome : loopify_outcome;  (** Which transform fired, or why none did. *)
  nt_used_param_inits : bool;
      (** [true] when [param_inits] were consumed by the transform (TMC uses
          them for method-self initialisation), meaning the caller does not
          need a separate initialiser statement. *)
}

(** {2 Call checker abstraction}

    A [call_checker] is a function that recognises recursive calls in
    expressions. It returns [Some call_site] when the expression is a direct
    recursive call, and [None] otherwise. Different checkers are used for
    top-level functions ({!fn_checker}) vs methods ({!method_checker}) vs inner
    lambdas ({!lambda_checker}). *)

(** Type alias for recursive call detection functions. Given a [cpp_expr],
    returns [Some call_site] if it is a direct recursive call, [None] otherwise. *)
type call_checker = cpp_expr -> call_site option

(** Check whether a [GlobRef.t] matches any of the given function refs. *)
let ref_matches fn_refs r =
  List.exists
    (fun (fn_r, _) -> Common.globref_equal r fn_r)
    fn_refs

(** Build a call checker for top-level function definitions: a call is
    recursive when it names one of the function's global references.  A local
    variable that happens to share the function's name -- a class method's
    field read in its own projection -- is not the function.

    @param fn_refs List of [(GlobRef.t, type_args)] pairs identifying the
                   function being loopified. Multiple refs arise when a single
                   Rocq definition is known by several global references (e.g.
                   mutual fixpoints registered together).
    @return A {!call_checker} that returns [Some cs] when [e] is a direct call
            to any function in [fn_refs], [None] otherwise. *)
let fn_checker (fn_refs : (GlobRef.t * cpp_type list) list) : call_checker =
 fun e ->
   match e with
   | CPPfun_call (_, CPPglob (r, _, _), args) when ref_matches fn_refs r ->
     Some (mk_call_site (to_reversed args))
   | _ -> None

(** Locals whose storage does not outlive one iteration of a loopified body.

    A match whose scrutinee is a value temporary -- typically the [_cs] cache
    of a scrutinee that is a function call, as in [auto _cs = _self->next();]
    -- binds names into an object that dies with the branch that created it.
    Parking the address of such a binder in an [CraneEnter] frame leaves the frame
    pointing at freed memory once the branch is left, so a recursive call on
    one of these receivers must not be linearised.

    [stable] seeds the traversal with the storage that does outlive the loop:
    the method parameters and [_self]. *)
let unstable_locals ~(stable : Id.Set.t) (body : cpp_stmt list) : Id.Set.t =
  let stable = ref stable in
  let unstable = ref Id.Set.empty in
  (* Storage outlives the frame when it is rooted in [this] or in a variable
     already known to be stable.  An accessor call is treated as reaching into
     its receiver ([_self->v()] denotes part of [*_self]); when such a call in
     fact returns by value, the copy it makes is caught below, at the local it
     is bound to. *)
  let rec denotes_stable e =
    match e with
    | CPPthis -> true
    | CPPvar v -> Id.Set.mem v !stable
    | CPPderef e | CPPmove e | CPPaccess (_, e, _)
    | CPPget (e, _) | CPPget' (e, _, _)
    | CPPaccess_call (_, e, _, _) ->
      denotes_stable e
    | CPPfun_call (_, f, args) -> List.exists denotes_stable (f :: to_reversed args)
    | _ -> false
  in
  (* A local initialised from a call keeps a copy of whatever the call
     returned, unless it is declared as a reference; that copy dies with its
     enclosing block.  Locals bound from a dereference or a field are plain
     aliases and live as long as what they name. *)
  let rec is_alias_ty = function
    | Tref _ -> true
    | Tconst t -> is_alias_ty t
    | _ -> false
  in
  let copies_its_initialiser e ty =
    ( match e with
    | CPPaccess_call _ | CPPfun_call _ -> true
    | _ -> false )
    && match ty with Declare t -> not (is_alias_ty t) | Existing -> true
  in
  let classify ok id =
    if ok then stable := Id.Set.add id !stable
    else unstable := Id.Set.add id !unstable
  in
  let rec walk s =
    ( match s with
    | Sasgn (id, ty, e) ->
      classify (denotes_stable e && not (copies_its_initialiser e ty)) id
    | Scustom_case (_, scrut, _, branches, _) ->
      let ok = denotes_stable scrut in
      List.iter
        (fun (binders, _, _) -> List.iter (fun (id, _) -> classify ok id) binders)
        branches
    | Smatch (scrut, branches, _) ->
      (* Structured bindings alias the matched object. *)
      let ok = denotes_stable scrut.sc_expr in
      List.iter
        (fun br ->
          Option.iter (classify ok) br.smb_var;
          List.iter (fun (id, _, _) -> classify ok id) br.smb_field_bindings)
        branches
    | _ -> () );
    iter_stmt_children ~on_expr:(fun _ -> ()) ~on_stmts:(List.iter walk) s
  in
  List.iter walk body;
  !unstable

(** {3 The Y-combinator idiom for local fixpoints}

    {!Translation.gen_local_fix_by_ref} emits Coq's [let fix] as a pair of
    lambdas: an [f_impl] taking its own self-reference as a trailing parameter,
    and an [f] that ties the knot by passing [f_impl] to itself. These
    recognise that shape. They sit here, beside the other checkers, because
    both {!transform_nontail} and {!loopify_inner_lambdas} need them. *)

(** The prefix {!Translation.gen_local_fix_by_ref} gives a local fixpoint's
    self-reference parameter. *)
let self_param_prefix = "_self_"

(** Whether [id] is such a self-reference parameter. *)
let is_self_param_id id =
  let s = Id.to_string id in
  let p = self_param_prefix in
  String.length s > String.length p && String.sub s 0 (String.length p) = p

(** The self-reference parameter of a lambda written in the idiom, if it is one.

    Only a single (non-mutual) fixpoint qualifies: a mutual group forwards one
    self-reference per partner, and those the callers here cannot linearise. *)
let ycomb_self_id lparams =
  let self_count =
    List.length
      (List.filter
         (fun (_, io) ->
           match io with Some id -> is_self_param_id id | None -> false )
         lparams)
  in
  match List.rev lparams with
  | (_, Some sid) :: _ when is_self_param_id sid && self_count = 1 -> Some sid
  | _ -> None

(** A checker matching the fixpoint's calls to itself through [self_id]. *)
let self_checker self_id : call_checker =
 fun e ->
  match e with
  | CPPfun_call (_, CPPvar id, args) when Id.equal id self_id -> (
    (* Drop the trailing self-forward argument. *)
    match call_args args with
    | _self_arg :: rest_rev ->
      Some (mk_call_site (List.rev rest_rev))
    | [] -> None )
  | _ -> None


(** The receiver of a recursive call, with the wrappers that only re-spell an
    object stripped off.  [std::move] is one: it is a cast, so moving out of
    [this] still names the storage of [this] rather than making a temporary of
    its own. *)
let rec receiver_storage = function CPPmove e -> receiver_storage e | e -> e

(** Whether a recursive call's receiver is a value temporary, whose address
    would dangle once parked in an [CraneEnter] frame.  A receiver that names
    existing storage -- a variable, [this], or a smart pointer it dereferences
    -- is not. *)
let receiver_is_value = function
  | CPPderef _ | CPPvar _ | CPPthis -> false
  | _ -> true

(** Whether a [CPPglob] callee is the method itself.

    The method's own global decides it where there is one.  Matching on the
    bare label instead is not a weaker test but a wrong one: [T1.cmp] called
    from [T2.cmp] shares its label and nothing else, and reading that call as
    recursion parks a delegation as a self-call, discards the real callee and
    leaves a [while (true)] with no exit -- a miscompilation that compiles.
    The label is still the answer where the method has no global to compare
    against, which is the generated members ([clone], [v]) that no body calls
    by name. *)
let calls_self_glob ~(self_ref : GlobRef.t option) (name : Id.t) (r : GlobRef.t)
    =
  match self_ref with
  | Some sr -> Common.globref_equal r sr
  | None -> Id.equal (Label.to_id (Common.label_of_r r)) name

(** Build a call checker for struct methods. Matches [CPPaccess_call] on
    [method_name] and, when [has_self_param] is true, includes the receiver
    pointer as the first argument. Also matches [CPPglob] calls that resolve to
    the same method name.

    @param n_params     Number of formal parameters of the method (excluding
                        the implicit [this] pointer). Used to detect when an
                        argument list is longer than expected (curried / extra
                        receiver argument) so the receiver can be stripped.
    @param has_self_param [true] when the [_self] receiver has been added as
                        an explicit first parameter (nontail / method
                        loopification context). Causes the receiver expression
                        to be prepended as the first call argument.
    @param this_pos     Index of the [this]/receiver argument in the argument
                        list of [CPPfun_call] forms. Used to extract and remove
                        the receiver from over-long argument lists.
    @param self_ref     The global the method was made from, when known.  See
                        {!calls_self_glob}.
    @param method_name  The method name to match on. *)

let method_checker
    ~(n_params : int)
    ~(has_self_param : bool)
    ~(this_pos : int)
    ?(self_ref : GlobRef.t option)
    (method_name : Id.t) : call_checker =
 (* Convert a receiver expression to a raw pointer for the CraneEnter struct.
    CPPderef(shared_ptr): use shared_ptr.get() to extract the raw pointer.
    CPPvar: take the address (&var) to get a pointer.
    Other: take the address. *)
 let recv_to_self recv =
   match receiver_storage recv with
   | CPPderef inner ->
     CPPfun_call (call_opaque, CPPrt Crane_rt.Raw, of_reversed ([inner]))
   | _ ->
     CPPunop (Uaddr, recv)
 in
 let extract_at pos lst =
   let rec aux i acc = function
     | [] -> (None, List.rev acc)
     | x :: rest ->
       if i = pos then (Some x, List.rev_append acc rest)
       else aux (i + 1) (x :: acc) rest
   in
   aux 0 [] lst
 in
 fun e ->
   match e with
   | CPPaccess_call (Aarrow, recv, id, args) when Id.equal id method_name ->
     if has_self_param then
       Some (mk_call_site ~recv (recv_to_self recv :: args))
     else
       Some (mk_call_site args)
   | CPPfun_call (_, CPPvar id, args) when Id.equal id method_name ->
     let args_normal = call_args args in
     if has_self_param && List.length args_normal > n_params then
       let self_arg, rest = extract_at this_pos args_normal in
       ( match self_arg with
       | Some recv ->
         Some (mk_call_site ~recv (recv_to_self recv :: rest))
       | None -> Some (mk_call_site args_normal) )
     else if (not has_self_param) && List.length args_normal > n_params then
       Some (mk_call_site (list_remove_at this_pos args_normal))
     else
       Some (mk_call_site args_normal)
   | CPPfun_call (_, CPPglob (r, _, _), args) ->
     if calls_self_glob ~self_ref method_name r then
       let args_normal = call_args args in
       if has_self_param then
         let self_arg, rest = extract_at this_pos args_normal in
         ( match self_arg with
         | Some recv ->
           Some (mk_call_site ~recv (recv_to_self recv :: rest))
         | None -> Some (mk_call_site args_normal) )
       else
         let args_stripped =
           if List.length args_normal > n_params then
             list_remove_at this_pos args_normal
           else
             args_normal
         in
         Some (mk_call_site args_stripped)
     else
       None
   | _ -> None

(** {2 Call collection} *)

(** Collect all recursive call sites from an expression. Returns a list of
    {!call_site} values, one per recursive call found. Does NOT descend into
    inner lambda bodies for counting (those are handled separately via
    {!collect_stmts}). *)
let rec collect_expr (check : call_checker) expr =
  match check expr with
  | Some cs ->
    (* Also look for nested calls in the arguments (e.g., f(m', f(m, n'))) *)
    let nested =
      match expr with
      | CPPfun_call (_, _, args) ->
        List.concat_map (collect_expr check) (to_reversed args)
      | CPPaccess_call (_, _, _, args) ->
        List.concat_map (collect_expr check) args
      | _ -> []
    in
    cs :: nested
  | None ->
  match expr with
  | CPPfun_call (_, f, args) ->
    collect_expr check f
    @ List.concat_map (collect_expr check) (to_reversed args)
  | CPPerased_call (f, a) -> collect_expr check f @ collect_expr check a
  | CPPtolerant_call (f, args) ->
    collect_expr check f @ List.concat_map (collect_expr check) args
  | CPPaccess_call (Aarrow, obj, _id, args) ->
    collect_expr check obj @ List.concat_map (collect_expr check) args
  | CPPaccess_call (Adot, obj, _id, args) ->
    collect_expr check obj @ List.concat_map (collect_expr check) args
  | CPPmove e | CPPderef e | CPPforward (_, e) | CPPnamespace (_, e) ->
    collect_expr check e
  | CPPlambda {cl_body = stmts; _} ->
    (* Calls inside lambdas found via collect_expr are NOT tail calls of the
       outer function — they're returns from the lambda, whose result is used in
       a larger expression (e.g., Cons_(x, visit(l, {... => f(args)}))). The
       direct visit-in-return case goes through collect_stmt's special case for
       Sreturn(Some(visit(...))), not through here. *)
    List.map
      (fun cs -> {cs with cs_is_tail = false; cs_recv = None})
      (collect_stmts check ~in_visitor:false stmts)
  | CPPget (e, _)
   |CPPget' (e, _, _)
   |CPPaccess (_, e, _)
   |CPPscope (e, _, _) -> collect_expr check e
  | CPPstructmk (_, _, args)
   |CPPstruct (_, _, args)
   |CPPstruct_id (_, _, args)
   |CPPnew (_, args) -> List.concat_map (collect_expr check) args
  | CPPshared_ptr_ctor (_, e) ->
    collect_expr check e
  | CPPbinop (_, e1, e2) -> collect_expr check e1 @ collect_expr check e2
  | CPPcond (c, t, f) ->
    collect_expr check c @ collect_expr check t @ collect_expr check f
  | CPPparray (arr, def) ->
    Array.fold_left
      (fun acc e -> acc @ collect_expr check e)
      (collect_expr check def)
      arr
  | CPPbraced args -> List.concat_map (collect_expr check) args
  | CPPstd_get (_, Some e) -> collect_expr check e
  | CPPstd_get_if (_, e) -> collect_expr check e
  | CPPvar _
   |CPPglob _
   |CPPalloc _
   |CPPthis
   |CPPshared_from_this _
   |CPPconvertible_to _
   |CPPabort _
   |CPPenum_val _
   |CPPnullptr | CPPin_place | CPPin_place_index _
   |CPPstd_get (_, None)
   |CPPstd_holds_alternative _
   |CPPdeclval _
   |CPPtype_name _
   |CPPlit _
   |CPPraw _
   |CPPrt _
   |CPPbool _
   |CPPint _
   |CPPunop _
   |CPPany_cast _
   |CPPany_cast_tolerant _
   |CPPconvert _
   |CPPunbox _
   |CPPerase_fn _
   |CPPfn_value _
   |CPPcontainer_cast _
   |CPPconverting_ctor _
   |CPPbox _
   |CPPqualified_t _
   |CPPstring _
   |CPPuint _
   |CPPfloat _
   |CPPconcept_app _
   |CPPrequires _ -> []

(** Collect recursive call sites from a list of statements.
    Delegates to {!collect_stmt} for each statement. *)
and collect_stmts check ~in_visitor stmts =
  (* Detect void tail-call patterns at the end of a statement list.

     Pattern A — [Sexpr call; Sreturn None]:
     In C++, a void function can end with [f(); return;] which is
     semantically [return f();] — the call is in tail position.
     Generated by cofix_wrap and gen_stmts when current_cpp_return_type
     is Tvoid.

     Pattern B — [Sexpr call; Sreturn (Some val)]:
     Same situation but generated when current_cpp_return_type is a unit
     type (not Tvoid), e.g. for ITree-unit-returning fixpoints whose
     return is threaded through the nat-match continuation [k].  The
     generated code is [f(); return Unit::e_TT;] which is semantically
     equivalent — [f()] is still the last meaningful call before the
     function exits.  Without this pattern the call would be found only
     via collect_expr (cs_is_tail = false), misclassifying the function
     as Nontail_recursion and producing an unnecessary explicit stack. *)
  let rec go = function
    | Sexpr e :: Sreturn None :: rest when Option.has_some (check e) ->
      collect_stmt check ~in_visitor (Sreturn (Some e)) @ go rest
    | Sexpr e :: Sreturn (Some _) :: rest when Option.has_some (check e) ->
      (* Void/unit tail-call pattern [f(); return (val)] where [f()] is itself
         the recursive call — treat it as [return f()].  Guard on [check e] so
         we only fire when the [Sexpr] is genuinely the recursive tail call; a
         bare side-effect followed by [return g()] (e.g. [writeSTRef(...);
         return _self_go(...)]) must fall through so the recursive call in the
         [Sreturn] is not discarded. *)
      collect_stmt check ~in_visitor (Sreturn (Some e)) @ go rest
    | s :: rest ->
      collect_stmt check ~in_visitor s @ go rest
    | [] -> []
  in
  go stmts

(** Collect recursive call sites from a single statement. Handles
    [Sreturn], [Sif], [Scustom_case], [Sswitch], and nested visit lambdas.
    When [~in_visitor:true], return-position calls are treated as tail calls. *)
and collect_stmt check ~in_visitor = function
  | Sreturn (Some e) ->
    ( match check e with
    | Some cs ->
      (* Also look for nested calls in arguments (e.g., f(m', f(m, n'))) *)
      let nested =
        match e with
        | CPPfun_call (_, _, args) ->
        List.concat_map (collect_expr check) (to_reversed args)
        | CPPaccess_call (Aarrow, _, _, args) ->
          List.concat_map (collect_expr check) args
        | _ -> []
      in
      {cs with cs_is_tail = true} :: nested
    | None ->
    collect_expr check e )
  | Sreturn None -> []
  | Sexpr e | Sbind (_, e) -> collect_expr check e
  | Sasgn (_, _, e) -> collect_expr check e
  | Sassign_expr (lhs, e) -> collect_expr check lhs @ collect_expr check e
  | Sif_constexpr (_, then_br, else_br) ->
    collect_stmts check ~in_visitor then_br
    @ collect_stmts check ~in_visitor else_br
  | Sif (cond, then_br, else_br) ->
    collect_expr check cond
    @ collect_stmts check ~in_visitor then_br
    @ collect_stmts check ~in_visitor else_br
  | Sif_decl (_, _, init, then_br, else_br) ->
    collect_expr check init
    @ collect_stmts check ~in_visitor then_br
    @ collect_stmts check ~in_visitor else_br
  | Swhile (cond, body) | Sfor_range (_, cond, body) ->
    collect_expr check cond @ collect_stmts check ~in_visitor body
  | Sblock stmts -> collect_stmts check ~in_visitor stmts
  | Sswitch (scrut, _, branches, _) ->
    collect_expr check scrut
    @ List.concat_map
        (fun (_, body) -> collect_stmts check ~in_visitor body)
        branches
  | Scustom_case (_, scrut, _, branches, _) ->
    collect_expr check scrut
    @ List.concat_map
        (fun (_, _, body) -> collect_stmts check ~in_visitor body)
        branches
  | Sblock_custom (_, _, _, _, args, _) ->
    List.concat_map (collect_expr check) args
  | Smatch (scrut, branches, default) ->
    collect_expr check scrut.sc_expr
    @ List.concat_map
      (fun br ->
        List.concat_map (collect_expr check) br.smb_extra_conds
        @ collect_stmts check ~in_visitor:true br.smb_body)
      branches
    @ ( match default with
      | Some stmts -> collect_stmts check ~in_visitor stmts
      | None -> [] )
  | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ | Scomment _ | Sstruct_def _
  | Susing _ | Sdecl_init _ | Scontinue | Sbreak -> []

(** Count recursive calls in an expression (not descending into lambdas). *)
let rec count_calls_expr (check : call_checker) expr =
  match check expr with
  | Some _ -> 1
  | None ->
  match expr with
  | CPPfun_call (_, f, args) ->
    count_calls_expr check f
    + List.fold_left
        (fun acc a -> acc + count_calls_expr check a) 0 (to_reversed args)
  | CPPaccess_call (Aarrow, obj, _, args) ->
    count_calls_expr check obj
    + List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 args
  | CPPmove e | CPPderef e | CPPforward (_, e) | CPPnamespace (_, e) ->
    count_calls_expr check e
  | CPPbinop (_, e1, e2) ->
    count_calls_expr check e1 + count_calls_expr check e2
  | CPPget (e, _)
   |CPPget' (e, _, _)
   |CPPaccess (_, e, _)
   |CPPscope (e, _, _) -> count_calls_expr check e
  | CPPstructmk (_, _, args)
   |CPPstruct (_, _, args)
   |CPPstruct_id (_, _, args)
   |CPPnew (_, args) ->
    List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 args
  | CPPshared_ptr_ctor (_, e) ->
    count_calls_expr check e
  | _ -> 0

(** Count recursive calls in a statement list. *)
let rec count_calls_stmts (check : call_checker) stmts =
  List.fold_left
    (fun acc stmt ->
      acc
      +
      match stmt with
      | Sreturn (Some e) | Sexpr e | Sasgn (_, _, e) ->
        count_calls_expr check e
      | Sif (cond, then_br, else_br) ->
        count_calls_expr check cond
        + count_calls_stmts check then_br
        + count_calls_stmts check else_br
      | Sblock ss -> count_calls_stmts check ss
      | Sswitch (e, _, branches, _) ->
        count_calls_expr check e
        + List.fold_left
            (fun acc (_, body) -> acc + count_calls_stmts check body)
            0
            branches
      | Scustom_case (_, scrut, _, branches, _) ->
        count_calls_expr check scrut
        + List.fold_left
            (fun acc (_, _, body) -> acc + count_calls_stmts check body)
            0
            branches
      | Smatch (scrut, branches, default) ->
        count_calls_expr check scrut.sc_expr
        + List.fold_left
          (fun acc br ->
            acc
            + List.fold_left (fun a c -> a + count_calls_expr check c) 0 br.smb_extra_conds
            + count_calls_stmts check br.smb_body )
          0 branches
        + (match default with Some ss -> count_calls_stmts check ss | None -> 0)
      | _ -> 0 )
    0
    stmts

(** Detect a non-tail shape that is currently unsafe for the frame-based
    transform with move-only recursive fields.

    If a recursive call is used to compute a branch condition or scrutinee, the
    current rewrite may need to keep an owned cloned subtree alive while
    evaluating the selected continuation.  Popping the continuation frame before
    pushing [CraneEnter] can leave a dangling raw pointer from a shared_ptr that
    was std::moved.  Until the explicit stack has an owning-enter frame, leave
    these functions recursive. *)
let rec expr_has_recursive_branch_dependency check expr =
  try
    iter_expr_children
      ~on_expr:(fun e' ->
        if expr_has_recursive_branch_dependency check e' then raise Exit)
      ~on_stmts:(fun body ->
        if has_recursive_branch_dependency check body then raise Exit)
      expr;
    false
  with Exit -> true

(** True when [expr] contains a recursive call (counted by
    {!count_calls_expr}) or a branch-dependency on one (detected by
    {!expr_has_recursive_branch_dependency}).  Factored out because this
    combined check appears in every scrutinee/condition position of
    {!has_recursive_branch_dependency}. *)
and expr_has_call_or_branch_dep check expr =
  count_calls_expr check expr > 0
  || expr_has_recursive_branch_dependency check expr

and has_recursive_branch_dependency check stmts =
  List.exists
    (function
      | Sreturn (Some e) | Sexpr e | Sasgn (_, _, e) ->
        expr_has_recursive_branch_dependency check e
      | Sif (cond, then_br, else_br) ->
        expr_has_call_or_branch_dep check cond
        || has_recursive_branch_dependency check then_br
        || has_recursive_branch_dependency check else_br
      | Sswitch (scrut, _, branches, default) ->
        let branch_bodies = List.map snd branches in
        expr_has_call_or_branch_dep check scrut
        || List.exists (has_recursive_branch_dependency check) branch_bodies
        ||
        (match default with
        | Some body -> has_recursive_branch_dependency check body
        | None -> false)
      | Scustom_case (_, scrut, _, branches, _) ->
        let branch_bodies = List.map (fun (_, _, body) -> body) branches in
        (* An irrefutable single-branch destructure (e.g. [let (a, b) := f x in
           ...], or a tuple/record pattern on a recursive call's result) selects
           no continuation: its one branch always runs after the scrutinee is
           fully evaluated.  A recursive call in that scrutinee is therefore
           safe — {!transform_nontail} lifts it into a resume frame (see the
           [Scustom_case]/[check scrut] handling there) — so it must not count
           as a disqualifying branch dependency.  Only treat the scrutinee as a
           dependency for genuine multi-way dispatch ([List.length > 1]). *)
        (List.length branches > 1
         && expr_has_call_or_branch_dep check scrut)
        || List.exists (has_recursive_branch_dependency check) branch_bodies
      | Smatch (scrut, branches, default) ->
        (* Same reasoning as {!Scustom_case}: a single-branch [Smatch] with no
           default is an irrefutable destructure (no branch selection), so a
           recursive call in its scrutinee is safe.  Genuine dispatch — more
           than one branch, or a fall-through [default] — keeps the guard. *)
        let is_irrefutable_destructure =
          List.length branches = 1 && default = None
        in
        ( (not is_irrefutable_destructure)
          && expr_has_call_or_branch_dep check scrut.sc_expr )
        || List.exists
             (fun br ->
               List.exists (expr_has_call_or_branch_dep check) br.smb_extra_conds)
             branches
        || List.exists
             (fun br -> has_recursive_branch_dependency check br.smb_body)
             branches
        ||
        (match default with
        | Some body -> has_recursive_branch_dependency check body
        | None -> false)
      | Sblock body | Swhile (_, body) | Sfor_range (_, _, body) ->
    has_recursive_branch_dependency check body
      | Sblock_custom (_, _, _, _, args, _) ->
        List.exists (expr_has_recursive_branch_dependency check) args
      | _ -> false)
    stmts

(** [expose_tail_calls check body] is [body] with each returned conditional or
    short-circuit expression whose conditionally evaluated operand holds a
    recursive call written as the [if] it stands for: [return c ? a : b] as
    [if (c) return a; else return b;], [return a || b] as
    [if (a) return true; else return b;], [return a && b] as
    [if (a) return b; else return false;].  A call there is a tail call, and
    in statement form the transforms see it as one rather than as a call
    nested in an expression.  Lambdas are left to their own transform. *)
let rec expose_tail_calls check stmts = List.map (expose_stmt check) stmts

and expose_stmt check = function
  | Sreturn (Some e) -> expose_return check e
  | s -> map_stmt ~fl:(expose_tail_calls check) Fun.id (expose_stmt check) Fun.id s

and expose_return check e =
  let holds e = count_calls_expr check e > 0 in
  let return e = expose_return check e in
  match e with
  | CPPcond (c, a, b) when holds a || holds b -> Sif (c, [return a], [return b])
  | CPPbinop (Bor, a, b) when holds b -> Sif (a, [Sreturn (Some (CPPbool true))], [return b])
  | CPPbinop (Band, a, b) when holds b -> Sif (a, [return b], [Sreturn (Some (CPPbool false))])
  | _ -> Sreturn (Some e)

(** Classify a function body's recursion pattern. Collects all recursive call
    sites and checks whether they are all in tail position, some non-tail, or
    none at all.

    @param check Call checker identifying recursive calls
    @param body  Function body statements to classify
    @return {!No_recursion}, {!Tail_recursion}, or {!Nontail_recursion} *)
let classify check body =
  let calls = collect_stmts check ~in_visitor:false body in
  match calls with
  | [] -> No_recursion
  | _ ->
    if List.for_all (fun cs -> cs.cs_is_tail) calls then
      Tail_recursion
    else
      Nontail_recursion

(** Record what happened to one recursive function, checking the postcondition.

    [strategy] is the outcome the pass {e believes} it achieved.  Before
    accepting it we re-run {!classify} on the transformed body: if a recursive
    call survived, the strategy did not actually linearise the function and the
    outcome is downgraded to {!Lp_declined}.  A decline the transform reported
    itself stands, since its reason is more specific than "a self-call
    remains".

    @param survived Reason to record if a call did survive, when the caller
                    knows something sharper than "a self-call remains"
    @param name     Display name of the function, for the report
    @param check    The same call checker the transform was driven by
    @param strategy What the transform says it did
    @param body     The {e transformed} body
    @return [body], unchanged *)
let report_outcome ?survived ~name ~check ~strategy body =
  let outcome =
    match strategy with
    | Lp_declined _ -> strategy
    | _ when classify check body <> No_recursion ->
      Lp_declined
        (Option.default "a self-call survived the transform" survived)
    | _ -> strategy
  in
  record_outcome name outcome;
  body

(** {2 Invariant parameter detection}

    A parameter is invariant if every recursive call site passes it unchanged
    (i.e., the argument at that position is [CPPvar id] where [id] is the
    parameter name). Invariant parameters need not appear in frame structs or
    shadow variables — they can be referenced directly from function scope. *)

(** Determine which parameters vary across recursive calls.

    A parameter is considered invariant when every recursive call site passes
    exactly the same variable back (i.e. the argument at that position is
    [CPPvar id] where [id] is the parameter name). Invariant parameters can be
    referenced directly from function scope and need not appear in shadow
    variables or frame structs.

    @param check  Call checker identifying recursive calls
    @param params Function parameters [(id, type)]
    @param body   Function body statements
    @return A bool list parallel to [params]: [true] = varying (changes across
            calls), [false] = invariant (always passed unchanged) *)
let find_varying_params check params body =
  let calls = collect_stmts check ~in_visitor:false body in
  if calls = [] then
    List.map (fun _ -> true) params
  else
    List.mapi
      (fun i (id, _ty) ->
        not
          (List.for_all
             (fun cs ->
               match List.nth_opt cs.cs_args i with
               | Some (CPPvar arg_id) -> Id.equal arg_id id
               | _ -> false )
             calls ) )
      params

(** Filter a list keeping only elements at positions where [mask] is [true].

    [mask] is indexed by the function's parameters, so [lst] is expected to be
    a call site's argument list of the same length.  A self-call can legitimately
    carry a different arity than the definition it sits in -- a partially applied
    call, or a knot-tying wrapper whose functional takes an extra [rec] parameter
    -- and then no per-parameter mask applies.  That is a shape this transform
    does not handle rather than a broken invariant, so raise {!Not_linearisable}
    and let the caller decline, instead of failing the whole extraction. *)
let filter_by_mask mask lst =
  let n1 = List.length mask and n2 = List.length lst in
  if n1 <> n2 then
    raise
      (Not_linearisable
         (Printf.sprintf
            "a recursive call passes %d argument%s where the definition has %d \
             parameter%s"
            n2 (if n2 = 1 then "" else "s") n1 (if n1 = 1 then "" else "s") ));
  List.combine mask lst
  |> List.filter_map (fun (keep, x) -> if keep then Some x else None)

(** {2 This→_self substitution for method loopification} *)

(** True when an expression refers to the method receiver ([CPPthis]).
    Uses the generic {!expr_exists} traversal. *)
let expr_contains_this e =
  expr_exists (function CPPthis -> true | _ -> false) e

(** Replace [CPPthis] with [CPPvar self_id] throughout an expression. *)
let rec this_to_self_expr (self_id : Id.t) (e : cpp_expr) : cpp_expr =
  match e with
  | CPPthis -> CPPvar self_id
  | _ ->
    map_expr (this_to_self_expr self_id) (this_to_self_stmt self_id) Fun.id e

(** Replace [CPPthis] with [CPPvar self_id] throughout a statement. *)
and this_to_self_stmt (self_id : Id.t) (s : cpp_stmt) : cpp_stmt =
  match s with
  | Smatch (scrut, branches, default) ->
    (* Matching on the receiver: [self] is a borrowed reference, so the
       payload must not be taken by [auto&] out of [v_mut()]. *)
    let receiver_match = expr_contains_this scrut.sc_expr in
    Smatch
      ( { scrut with
          sc_expr = this_to_self_expr self_id scrut.sc_expr;
          sc_owned = (not receiver_match) && scrut.sc_owned },
        List.map
          (fun br ->
            { br with
              smb_extra_conds =
                List.map (this_to_self_expr self_id) br.smb_extra_conds;
              smb_body = List.map (this_to_self_stmt self_id) br.smb_body })
          branches,
        Option.map (List.map (this_to_self_stmt self_id)) default )
  | _ ->
    map_stmt (this_to_self_expr self_id) (this_to_self_stmt self_id) Fun.id s

(** {2 Variable substitution} *)

(** Substitute variable names in an expression using a mapping
    [(old_id, new_id)]. *)
let rec subst_expr (subs : (Id.t * Id.t) list) e =
  let e' =
    List.fold_left
      (fun acc (old_id, new_id) ->
        match acc with
        | CPPvar id when Id.equal id old_id -> CPPvar new_id
        | _ -> acc )
      e
      subs
  in
  map_expr (subst_expr subs) (subst_stmt subs) (fun t -> t) e'

(** Substitute variable names in a statement using a mapping
    [(old_id, new_id)]. Statement-level companion of {!subst_expr}. *)
and subst_stmt subs s =
  map_stmt (subst_expr subs) (subst_stmt subs) (fun t -> t) s
