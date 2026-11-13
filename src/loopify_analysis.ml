(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Recursive-call analysis for {!Loopify}: the CppIR vocabulary and
    traversals the strategies share, named constants, the constructor
    pointer-field table, outcome diagnostics, call checkers and call
    collection, and the substitutions the rewrites use.  Everything here
    reads and builds {!Cpp_ir.Lowered} code, the form Loopify and ControlIR
    lowering ({!Control_to_cpp_ir}) rewrite between translation and the
    finish pipeline. *)

open Names
open Cpp_ir.Type
open Cpp_ir.Stmt
open Cpp_ir.Expr

(** {2 CppIR}

    The stack rewrites {!Cpp_ir.Lowered} code.  The names below are the
    families it reads and builds, and the one-level traversals it is written
    over: each visits a node's children in {!Cpp_ir.Map}'s and
    {!Cpp_ir.Subterms}' order, which the names the transforms mint by counter
    depend on. *)

type phase = Cpp_ir.Lowered.phase
type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type decl = Cpp_ir.Lowered.Decl.t
type lambda = phase Cpp_ir.Expr.Lambda.t
type signature = phase Cpp_ir.Expr.Call.signature
type meth = phase Cpp_ir.Field.Method.t
type func = phase Cpp_ir.Function.t
type param_kind = phase Cpp_ir.Template.Parameter_kind.t
type scrutinee = phase Cpp_ir.Stmt.Match.scrutinee
type branch = phase Cpp_ir.Stmt.Match.branch
type field_binding = phase Cpp_ir.Stmt.Match.field_binding
type custom_branch = phase Cpp_ir.Stmt.Custom_match.branch
type custom_param = phase Cpp_ir.Stmt.Custom_match.param
type binding = phase Cpp_ir.Stmt.Binding.t
type field = phase Cpp_ir.Field.t
type local_fixpoint = Cpp_ir.Expr.Local_fixpoint.t

(** The signature of a call nothing is known about. *)
let call_opaque : signature = {yields = Untyped; params = Unknown; constructs = None; occurrence = None}

(** [signature ?yields ?params ?constructs ~nargs ()] is what a builder knows
    about a call on [nargs] arguments; [params] is kept only where it is one
    type per argument. *)
let signature ?yields ?params ?constructs ~nargs () : signature =
  { yields = (match yields with Some t -> Yields t | None -> Untyped);
    params = (match params with Some ts when List.length ts = nargs -> Types ts | _ -> Unknown);
    constructs;
    occurrence = None }

(** [call_made_of occurrence e] is the call [e] recording the Core call it is
    made of; any other expression unchanged. *)
let call_made_of occurrence : expr -> expr = function
  | Call (s, f, args) -> Call ({s with occurrence = Some occurrence}, f, args)
  | e -> e

(** [map_args f args] rewrites a call's arguments, the last first. *)
let map_args f (args : expr list) = List.rev (List.map f (List.rev args))

(** [map_expr ?fl fe fs ft e] is [e] with its children rewritten: [fe] its
    expressions, [fs] its statements -- or [fl] each statement list -- and
    [ft] its types. *)
let map_expr ?fl fe fs ft (e : expr) : expr =
  Cpp_ir.Map.expr (Cpp_ir.Map.make ?stmts:fl ~expr:fe ~stmt:fs ~type_:ft ()) e

(** [map_stmt ?fl fe fs ft s] is {!map_expr} of a statement. *)
let map_stmt ?fl fe fs ft (s : stmt) : stmt =
  Cpp_ir.Map.stmt (Cpp_ir.Map.make ?stmts:fl ~expr:fe ~stmt:fs ~type_:ft ()) s

(** [iter_expr_children ~on_expr ~on_stmts e] visits the expressions and
    statement lists [e] holds directly ({!Cpp_ir.Subterms}). *)
let iter_expr_children ~on_expr ~on_stmts (e : expr) = Cpp_ir.Subterms.expr ~expr:on_expr ~stmts:on_stmts e

(** [iter_stmt_children ~on_expr ~on_stmts s] is {!iter_expr_children} of a
    statement. *)
let iter_stmt_children ~on_expr ~on_stmts (s : stmt) = Cpp_ir.Subterms.stmt ~expr:on_expr ~stmts:on_stmts s

(** [fold_expr_children ~on_expr ~on_stmts acc e] folds over what
    {!iter_expr_children} visits. *)
let fold_expr_children ~on_expr ~on_stmts acc (e : expr) =
  let acc = ref acc in
  iter_expr_children ~on_expr:(fun e -> acc := on_expr !acc e) ~on_stmts:(fun ss -> acc := on_stmts !acc ss) e;
  !acc

(** [fold_stmt_children ~on_expr ~on_stmts acc s] folds over what
    {!iter_stmt_children} visits. *)
let fold_stmt_children ~on_expr ~on_stmts acc (s : stmt) =
  let acc = ref acc in
  iter_stmt_children ~on_expr:(fun e -> acc := on_expr !acc e) ~on_stmts:(fun ss -> acc := on_stmts !acc ss) s;
  !acc

(** The variables an expression, a statement or a statement list reads
    without binding them ({!Cpp_ir.Variables}). *)
let free_vars_expr (e : expr) = Cpp_ir.Variables.free_in_expr e

let free_vars_stmt (s : stmt) = Cpp_ir.Variables.free_in_stmt s
let free_vars_body (ss : stmt list) = Cpp_ir.Variables.free_in_body ss

(** Whether a declaration of type [ty] binds a reference rather than a value. *)
let rec is_reference_type : ty -> bool = function
  | Reference _ -> true
  | Const t -> is_reference_type t
  | _ -> false

(** Whether a parameter declared at [ty] is a reference the body does not
    own: a [const T &], or the [F &&] a deduced callable is. *)
let rec declared_by_reference : ty -> bool = function
  | Reference _ | Const _ -> true
  | In_namespace (_, t) -> declared_by_reference t
  | _ -> false

(** Whether [ty] mentions a [std::shared_ptr] anywhere. *)
let contains_shared_ptr (t : ty) = Cpp_ir.Children.exists_type (function Shared_pointer _ -> true | _ -> false) t

(** The Core binder each local a lambda's body reads as its own stands for,
    by name: its parameters, and the locals its local fixpoint captures. *)
let lambda_binders (l : lambda) =
  l.binders @ Option.cata (fun (f : Cpp_ir.Expr.Local_fixpoint.t) -> f.captured) [] l.fixpoint

(** The type variable a template header declares under the name [x]. *)
let named_tvar x : ty = Variable (Named x)

(** [converting_ctor ty args]: [ty(args)], a box where [ty] is written
    [std::any] -- of what a box holds, where [args] is one. *)
let converting_ctor (ty : ty) (args : expr list) : expr =
  match args with
  | [inner] when Cpp_ir.Types.prints_as_any ty ->
    let inner = match inner with Box (_, x) -> x | x -> x in
    Box (ty, inner)
  | _ -> Converting_construct (ty, args)

(** {2 Named Constants}

    Frequently used [Id.t] values, defined once to avoid repeated
    [Id.of_string] allocations across the loopify modules. *)

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

(* Perceus reuse cursor (see the reuse-cursor section of {!Loopify_tmc}). *)
let id_own          = Id.of_string "_own"

(* A value-type result assembled in place (see {!Loopify_tmc.result_storage}). *)
let id_root         = Id.of_string "_root"
let id_node         = Id.of_string "_node"
let id_value        = Id.of_string "_value"
let id_emplace      = Id.of_string "emplace"
let id_uniq         = Id.of_string "_uniq"
let id_rstep        = Id.of_string "_rs"

(* Method names used with Access / Access_call: [get] and the variant
   accessors [v] / [v_mut] on a value, and the [std::vector] members an
   explicit frame stack is driven by. *)
let id_get          = Id.of_string "get"
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

(** [map2_exn ~what f l1 l2] is [List.map2], raising an anomaly that names
    [what] and both lengths when the lists differ in length. *)
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
    loopify pass to detect recursive calls, [This] references, [lazy_]
    factories, pointer-shadow variables, and more.

    The traversal delegates structural recursion to
    {!Cpp_ir.Subterms.expr} and {!Cpp_ir.Subterms.stmt}, which
    already enumerate every constructor, so a new CppIR node is
    automatically visible to every predicate here. *)

(** Return [true] when [pred] holds for [e] or any sub-expression reachable
    from [e], including inside lambda bodies.

    Short-circuits on the first match via an exception to avoid traversing
    the entire tree when only an existence check is needed.

    @param pred  Predicate to test on each expression node
    @param e     Root expression to search *)
let rec expr_exists (pred : expr -> bool) (e : expr) : bool =
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
and stmt_exists (pred : expr -> bool) (s : stmt) : bool =
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
let body_exists (pred : expr -> bool) (stmts : stmt list) : bool =
  List.exists (stmt_exists pred) stmts

(** Check whether a C++ return type is a value-type inductive (a bare [Entity_application]
    that is neither coinductive nor custom-extracted).  When true, TMC must wrap [_head]/_write in
    [shared_ptr] because the constructor's recursive field is [shared_ptr].
    Handles [In_namespace] wrapping for out-of-line (.cpp) method definitions. *)
let rec is_value_type_ret = function
  | Entity_application (r, _, _) -> not (Table.is_coinductive r) && not (Table.is_custom r)
  | In_namespace (_, t) -> is_value_type_ret t
  | _ -> false

(** Whether a C++ type is trivially copyable (scalars, pointers, enums).
    For these types, copying is cheaper than indirecting through a reference,
    so frame-field bindings should remain copies rather than [const T&]. *)
let rec is_trivially_copyable_type = function
  | Void | Auto | (Obligation Unresolved_type) | Any -> true
  | Pointer _ | Reference _ -> true
  | Const t | In_namespace (_, t) | Member (t, _) ->
    is_trivially_copyable_type t
  | Decay (Type_of _) -> true
  | Variable _ -> true
  | Named (id, ts) -> is_trivially_copyable_named (Id.to_string id) ts
  | External (s, ts) -> is_trivially_copyable_named s ts
  | Entity_application (r, ts, _) ->
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

(** Whether a value of type [t] is worth a [std::move]
    ({!Ownership_ir.worth_moving_ir}). *)
let worthwhile_move_type (t : ty) = Ownership_ir.worth_moving_ir t

(** Whether a value of the C++ type [t] is copied as cheaply as it is moved:
    trivially copyable, and not worth a move -- a template type variable is
    trivially copyable here, and may stand for any type. *)
let copies_cheaply t = is_trivially_copyable_type t && not (worthwhile_move_type t)

(** Whether a local declared at [ty] names a value it does not own: a
    [const T] moved from is silently copied, and a [const T &] names what
    another holds. *)
let rec is_borrowed = function
  | Reference _ | Const _ -> true
  | In_namespace (_, t) -> is_borrowed t
  | _ -> false

(** Whether a local declared at [ty] is one to move from at its last read:
    held by value, at a type worth moving.  [auto] never deduces a
    reference, and is how most temporaries are declared, so it is worth
    moving though its type is not written down. *)
let movable ty = (not (is_borrowed ty)) && (ty = Auto || worthwhile_move_type ty)

(* Global mutable state in this file and their reset granularity:
   - outcomes : reset per generated file (State.Unit)
   - ctor_ptr_fields : accumulates across the full session; never cleared because
     struct shapes don't change within a Rocq session *)

(** A constructor field stored behind the smart pointer: a recursive one, which
    holds the inductive itself, or one [Crane BoxedFields] boxed for holding
    some other inductive. *)
type ptr_field = Recursive of int | Boxed of int

let ptr_field_index = function Recursive i | Boxed i -> i

(** Table mapping constructor struct names to their shared_ptr field indices.
    Installed before rendering ({!install_ctor_ptr_fields}) and queried by
    {!Loopify_tmc.make_cell} to determine which fields need [make_shared] wrapping
    in the direct-struct-construction path.

    The key pairs {!Common.ctor_owner_key} of the owning inductive with the
    capitalized constructor name (e.g., ["App"], ["Cons"]); the owner is part
    of it because a constructor name alone does not identify a struct -- two
    inductives may each have a [Cons], with different fields.  The value is a
    list of the constructor's pointer fields, by 0-based index. *)
let ctor_ptr_fields : (string * string, ptr_field list) Hashtbl.t = Hashtbl.create 32

(** Install the pointer fields of each constructor struct planned before
    rendering, the inductive, the constructor's struct name and each field's
    index with whether it holds the inductive itself
    ({!Gen_inductives.constructor_pointer_fields}); the struct read later
    must agree ({!agree_ptr_fields}). *)
let install_ctor_ptr_fields planned =
  List.iter
    (fun (owner, ctor_name, fields) ->
      Hashtbl.replace ctor_ptr_fields
        (Common.ctor_owner_key owner, ctor_name)
        (List.map (fun (i, recursive) -> if recursive then Recursive i else Boxed i) fields) )
    planned

(** The arguments of the constructor [c] its struct stores behind the pointer,
    as planned, or [None] where it stores none. *)
let constructor_pointer_fields c =
  Option.map (List.map ptr_field_index)
    (Hashtbl.find_opt ctor_ptr_fields
       (Common.ctor_owner_key c, Ml_type_util.ctor_struct_name_of_ref c))

(** Check the pointer fields read off a generated constructor struct against
    the ones planned before rendering, under [CRANE_CHECK_IR]. *)
let agree_ptr_fields owner ctor_name fields =
  let key = (Common.ctor_owner_key owner, ctor_name) in
  if Hashtbl.find_opt ctor_ptr_fields key <> Some fields then
    Probe.violation "constructor pointer fields"
      Pp.(
        str "the struct " ++ str ctor_name ++ str " of " ++ GlobRef.print owner
        ++ str " stores other fields behind the pointer than planned" )

(** {2 Recursion classification} *)

(** Information about a single recursive call site. *)
type call_site = {
  cs_args : expr list;
      (** Arguments to the recursive call, parallel to the parameters of the
          loop the checker that found it serves ({!filter_by_mask}): the
          last first where the checker reverses the call's source-order
          arguments, as those of a function's or a local fixpoint's loop do
          ({!calls_checker}, {!planned_self_checker},
          {!Control_to_cpp_ir.jump}); in source order for a method's loop,
          which takes the receiver and then the parameters as written
          ({!method_checker}) *)
  cs_is_tail : bool;  (** Whether this call appears in tail position *)
  cs_entry : int;
      (** Which entry point of the frame machine this call targets, as an index
          into the machine's entry table. A function loopified on its own has
          exactly one entry, so this is [0]; it becomes meaningful once an
          enclosing function and a fixpoint local to it share a single stack,
          where a call selects which [CraneEnter]-style frame to push and hence
          which parameter analysis applies. *)
  cs_recv : expr option;
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

    A bail-out returns the original recursive body, so without a record a
    function that loopify could not handle would be indistinguishable from
    one it chose not to touch, and the pass's coverage unmeasurable.  The
    machinery below records, for every recursive function the pass sees,
    which strategy fired or why it declined.

    A transform therefore returns {e what it did} alongside the body, rather
    than only the body: a bail-out hands back the body it was given, so
    "declined" is distinguishable from "transformed" only if the transform
    says which.  {!report_outcome} then re-classifies the {e transformed}
    body, so a strategy that silently left a self-call behind is reported as a
    decline too.  This postcondition is what makes the report trustworthy: it
    does not depend on every bail site remembering to announce itself. *)

(** What the pass did with one recursive function. *)
type loopify_outcome =
  | Lp_tail  (** Rewritten to a flat [while] loop by {!Loopify_tail.transform_tail}. *)
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

(* A function generated again is lowered again, alike, and one lowered and
   then left -- a member of a recursive group whose partners were not all
   lowered -- is recorded as left after it was recorded lowered: the last
   outcome recorded describes the emitted code. *)
let get_outcomes () =
  (* Keep first-seen order, but collapse each name to its last outcome. *)
  let last = Hashtbl.create 64 in
  let order = ref [] in
  List.iter
    (fun (name, outcome) ->
      if not (Hashtbl.mem last name) then order := name :: !order;
      Hashtbl.replace last name outcome )
    (List.rev !outcomes);
  List.rev_map (fun name -> (name, Hashtbl.find last name)) !order

(** What a suspended cofixpoint's function is: its calls run when a thunk is
    forced, and need no loop. *)
let deferred_cofixpoint = Lp_deferred "cofixpoint body is lazy_-wrapped"

(** Why a function a self-call is left in was declined, where nothing
    sharper is known. *)
let survived_generically = "a self-call survived the transform"

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

(** What [Loopify.apply_nontail_loopification] did with a body.  It chooses between
    the TMC and frame transforms internally, so it reports the choice here
    rather than leaving the caller to guess. *)
type nontail_result = {
  nt_body : stmt list;  (** The body to emit, transformed or original. *)
  nt_outcome : loopify_outcome;  (** Which transform fired, or why none did. *)
  nt_machine : bool;
      (** Whether a call enters the loop or machine the transform made: one
          none enters is not made, and the body is the one given. *)
}

(** {2 Call checker abstraction}

    A [call_checker] is a function that recognises recursive calls in
    expressions. It returns [Some call_site] when the expression is a direct
    recursive call, and [None] otherwise.  A loop's are the calls made of
    its Continues; a method's also convert the receiver ({!method_checker});
    a local fixpoint's drop the self-parameter it recurses through
    ({!planned_self_checker}); and those a body is left with are told by
    the Core use they are made of ({!calls_checker}). *)

(** Type alias for recursive call detection functions. Given a [expr],
    returns [Some call_site] if it is a direct recursive call, [None] otherwise. *)
type call_checker = expr -> call_site option

(** {3 The Y-combinator idiom for local fixpoints}

    {!Translation.gen_local_fix_by_ref} emits Coq's [let fix] as a pair of
    lambdas: an [f_impl] taking its own self-reference as its first
    parameter, and an [f] that ties the knot by passing [f_impl] to itself
    ([f_impl(f_impl, args...)]). These
    recognise that shape. They sit here, beside the other checkers, because
    both {!Loopify_frame} and {!Loopify.loopify_inner_lambdas} need them. *)

(** Whether [w] is the wrapper tying the knot of the local fixpoint
    [fixpoint] for its callers: a lambda lowering the same function of the
    same Core fixpoint through no self-parameter. *)
let wraps (fixpoint : local_fixpoint option) (w : lambda) =
  match (fixpoint, w.fixpoint) with
  | Some {member = occ, j; _}, Some {member = occ', j'; encoding = Knot; _} ->
    Miniml.Occurrence.equal occ occ' && Int.equal j j'
  | _ -> false

(** The self-reference parameter of the lambda a single local fixpoint's
    body is, as its encoding recorded it ({!Cpp_ir.Expr.Local_fixpoint}): the
    one self-parameter of [fixpoint], where it is the first of [params], the
    lambda's parameters in source order.  A mutual group's lambda takes one per
    member, which the callers here cannot linearise.  Its name is no
    evidence: the encoding spells it [_self_f], and Crane spells other
    locals of its own in that space too ([_self_val]). *)
let fixpoint_self (fixpoint : local_fixpoint option) params =
  match (fixpoint, params) with
  | Some {encoding = Self_passing [self]; _}, (_, Some first) :: _ when Id.equal self first -> Some self
  | _ -> None

(** A checker matching the calls of the function [member] of a local
    fixpoint to itself, as the recursion plan has them
    ({!Recursion_plan.member_calls}), each forwarding the self-parameter as
    its first argument, which the call site drops.  The other arguments are
    reported the last first, parallel to the parameters a local fixpoint's
    loop is lowered over. *)
let planned_self_checker member : call_checker =
  let calls = Recursion_plan.member_calls member in
  fun e ->
    let planned =
      match e with
      | Call ({occurrence = Some o; _}, _, _) -> List.exists (Miniml.Occurrence.equal o) calls
      | _ -> false
    in
    match e with
    | Call (_, _, args) when planned -> (
      match args with
      | _self_arg :: rest_rev -> Some (mk_call_site (List.rev rest_rev))
      | [] -> None )
    | _ -> None

(** The calls [calls] as a checker: a C++ call made of one of them, by the
    occurrence it records, whatever heads it, its arguments reported the last
    first. *)
let calls_checker calls : call_checker = function
  | Call ({occurrence = Some o; _}, _, args) when List.exists (Miniml.Occurrence.equal o) calls ->
    Some (mk_call_site (List.rev args))
  | _ -> None

(** The receiver of a recursive call, with the wrappers that only re-spell an
    object stripped off.  [std::move] is one: it is a cast, so moving out of
    [this] still names the storage of [this] rather than making a temporary of
    its own. *)
let rec receiver_storage = function Move e -> receiver_storage e | e -> e

(** Build a call checker for struct methods: a recursive call is a call of
    the global the method was made from, [self_ref], and when
    [has_self_param] is true the receiver pointer becomes its first
    argument.

    The method's own global decides it, never its name: [T1.cmp] called from
    [T2.cmp] shares its label and nothing else, and reading that call as
    recursion parks a delegation as a self-call, discards the real callee and
    leaves a [while (true)] with no exit -- a miscompilation that compiles.
    A method with no global is a member the backend generates ([clone],
    [v]), which no body calls; it does not recurse here.

    @param n_params     Number of formal parameters of the method (excluding
                        the implicit [this] pointer). Used to detect when an
                        argument list is longer than expected (curried / extra
                        receiver argument) so the receiver can be stripped.
    @param has_self_param [true] when the [_self] receiver has been added as
                        an explicit first parameter (nontail / method
                        loopification context). Causes the receiver expression
                        to be prepended as the first call argument.
    @param this_position     Index of the [this]/receiver argument among a
                        [Call]'s arguments, in source order. Used to
                        extract and remove the receiver from over-long
                        argument lists; the arguments are reported in
                        source order.
    @param self_ref     The global the method was made from, when known. *)
let method_checker
    ~(n_params : int)
    ~(has_self_param : bool)
    ~(this_position : int)
    (self_ref : GlobRef.t option) : call_checker =
 (* Convert a receiver expression to the raw pointer an [Enter] frame stores.
    Dereference(p): [crane_raw(p)], which extracts a raw pointer from either a
    [std::shared_ptr<T>] or an already-raw [T*] (arena mode) by overload
    resolution, where a bare [.get()] would assume one representation.
    Other: take the address. *)
 let recv_to_self recv =
   match receiver_storage recv with
   | Dereference inner ->
     Call (call_opaque, Runtime Crane_rt.Raw, [inner])
   | _ ->
     Unary (Address_of, recv)
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
   match (e, self_ref) with
   | Call (_, Entity (r, _, _), args), Some self_ref ->
     if Common.globref_equal r self_ref then
       let args_normal = args in
       if has_self_param then
         let self_arg, rest = extract_at this_position args_normal in
         ( match self_arg with
         | Some recv ->
           Some (mk_call_site ~recv (recv_to_self recv :: rest))
         | None -> Some (mk_call_site args_normal) )
       else
         let args_stripped =
           if List.length args_normal > n_params then
             list_remove_at this_position args_normal
           else
             args_normal
         in
         Some (mk_call_site args_stripped)
     else
       None
   | _ -> None

(** The occurrence of the Core call a C++ call is made of. *)
let made_of = function Call (cs, _, _) -> cs.occurrence | _ -> None

(** Whether the calls [made], each by the occurrence it is made of
    ({!made_of}), are the calls [planned], as many times each. *)
let made_as_planned planned made =
  let made_occs = List.filter_map Fun.id made in
  let count o l = List.length (List.filter (Miniml.Occurrence.equal o) l) in
  List.length made_occs = List.length made
  && List.length planned = List.length made_occs
  && List.for_all (fun o -> count o planned = count o made_occs) planned

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
      | Call (_, _, args) ->
        List.concat_map (collect_expr check) (List.rev args)
      | Access_call (_, _, _, args) ->
        List.concat_map (collect_expr check) args
      | _ -> []
    in
    cs :: nested
  | None ->
  match expr with
  | Persistent_array (arr, def) ->
    Array.fold_left
      (fun acc e -> acc @ collect_expr check e)
      (collect_expr check def)
      arr
  (* A requires-expression is never evaluated. *)
  | Requires _ -> []
  | _ ->
    (* A call below an expression is not in tail position, but it is a call.
       A statement list there is a lambda's body: a call in it returns from
       the lambda, whose result the larger expression uses (e.g.
       Cons_(x, visit(l, {... => f(args)}))); collect_stmt sees the direct
       Return(Some(visit(...))) case, not this. *)
    let in_body stmts =
      List.map
        (fun cs -> {cs with cs_is_tail = false; cs_recv = None})
        (collect_stmts check ~in_visitor:false stmts)
    in
    fold_expr_children
      ~on_expr:(fun acc e -> acc @ collect_expr check e)
      ~on_stmts:(fun acc stmts -> acc @ in_body stmts)
      [] expr

(** Collect recursive call sites from a list of statements.
    Delegates to {!collect_stmt} for each statement. *)
and collect_stmts check ~in_visitor stmts =
  (* Detect void tail-call patterns at the end of a statement list.

     Pattern A — [Expression call; Return None]:
     In C++, a void function can end with [f(); return;] which is
     semantically [return f();] — the call is in tail position.
     Translation ({!Translation.gen_stmts}) emits it when
     current_cpp_return_type is Void.

     Pattern B — [Expression call; Return (Some val)]:
     Same situation but generated when current_cpp_return_type is a unit
     type (not Void), e.g. for ITree-unit-returning fixpoints whose
     return is threaded through the nat-match continuation [k].  The
     generated code is [f(); return Unit::e_TT;] which is semantically
     equivalent — [f()] is still the last meaningful call before the
     function exits.  Without this pattern the call would be found only
     via collect_expr (cs_is_tail = false), misclassifying the function
     as Nontail_recursion and producing an unnecessary explicit stack. *)
  let rec go = function
    | Expression e :: Return None :: rest when Option.has_some (check e) ->
      collect_stmt check ~in_visitor (Return (Some e)) @ go rest
    | Expression e :: Return (Some _) :: rest when Option.has_some (check e) ->
      (* Void/unit tail-call pattern [f(); return (val)] where [f()] is itself
         the recursive call — treat it as [return f()].  Guard on [check e] so
         we only fire when the [Expression] is genuinely the recursive tail call; a
         bare side-effect followed by [return g()] (e.g. [writeSTRef(...);
         return _self_go(...)]) must fall through so the recursive call in the
         [Return] is not discarded. *)
      collect_stmt check ~in_visitor (Return (Some e)) @ go rest
    | s :: rest ->
      collect_stmt check ~in_visitor s @ go rest
    | [] -> []
  in
  go stmts

(** Collect recursive call sites from a single statement. Handles
    [Return], [If], [Custom_match], [Switch], [Match] and nested blocks; a
    call in a match branch's return position is a tail call.
    When [~in_visitor:true], return-position calls are treated as tail calls. *)
and collect_stmt check ~in_visitor = function
  | Return (Some e) ->
    ( match check e with
    | Some cs ->
      (* Also look for nested calls in arguments (e.g., f(m', f(m, n'))) *)
      let nested =
        match e with
        | Call (_, _, args) ->
        List.concat_map (collect_expr check) (List.rev args)
        | Access_call (Arrow, _, _, args) ->
          List.concat_map (collect_expr check) args
        | _ -> []
      in
      {cs with cs_is_tail = true} :: nested
    | None ->
    collect_expr check e )
  | Return None -> []
  | Expression e | Structured_binding (_, e) -> collect_expr check e
  | Bind_variable (_, _, e) -> collect_expr check e
  | Assign (lhs, e) -> collect_expr check lhs @ collect_expr check e
  | If_constexpr {test = _; then_ = then_br; else_ = else_br} ->
    collect_stmts check ~in_visitor then_br
    @ collect_stmts check ~in_visitor else_br
  | If {condition = cond; then_ = then_br; else_ = else_br} ->
    collect_expr check cond
    @ collect_stmts check ~in_visitor then_br
    @ collect_stmts check ~in_visitor else_br
  | If_declaration {name = _; type_ = _; init = init; then_ = then_br; else_ = else_br} ->
    collect_expr check init
    @ collect_stmts check ~in_visitor then_br
    @ collect_stmts check ~in_visitor else_br
  | While (cond, body) | For_range (_, cond, body) ->
    collect_expr check cond @ collect_stmts check ~in_visitor body
  | Block stmts -> collect_stmts check ~in_visitor stmts
  | Switch {scrutinee = scrut; enum = _; branches = branches; default = default} ->
    collect_expr check scrut
    @ List.concat_map
        (fun (_, body) -> collect_stmts check ~in_visitor body)
        branches
    @ (match default with
       | Some ss -> collect_stmts check ~in_visitor ss
       | None -> [])
  | Custom_match {scrutinee = scrut; branches; _} ->
    collect_expr check scrut
    @ List.concat_map
        (fun (b : custom_branch) -> collect_stmts check ~in_visitor b.body)
        branches
  | Foreign_block {custom = _; template = _; result = _; result_type = _; values = args; type_args = _; binder = _} ->
    List.concat_map (collect_expr check) args
  | Match (scrut, branches, default) ->
    collect_expr check scrut.expr
    @ List.concat_map
      (fun (br : branch) ->
        List.concat_map (collect_expr check) br.extra_conditions
        @ collect_stmts check ~in_visitor:true br.body)
      branches
    @ ( match default with
      | Some stmts -> collect_stmts check ~in_visitor stmts
      | None -> [] )
  | Declare _ | Throw _ | Assert _ | Foreign_text _ | Comment _ | Local_struct _
  | Local_type_alias _ | Declare_value_initialized _ | Continue | Break -> []

(** Count recursive calls in an expression (not descending into lambdas). *)
let rec count_calls_expr (check : call_checker) expr =
  match check expr with
  | Some _ -> 1
  | None ->
  match expr with
  | Call (_, f, args) ->
    count_calls_expr check f
    + List.fold_left
        (fun acc a -> acc + count_calls_expr check a) 0 (List.rev args)
  | Access_call (Arrow, obj, _, args) ->
    count_calls_expr check obj
    + List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 args
  | Move e | Dereference e | Forward (_, e) ->
    count_calls_expr check e
  (* A cast evaluates the call it reads, as {!collect_expr} counts it. *)
  | Any_cast (_, e) | Tolerant_any_cast (_, e) | Unbox (_, e) | Convert (_, e) ->
    count_calls_expr check e
  | Binary (_, e1, e2) ->
    count_calls_expr check e1 + count_calls_expr check e2
  | Member (e, _)
   |Project (e, _, _)
   |Access (_, e, _)
   |Scope (e, _, _) -> count_calls_expr check e
  | Aggregate {values = args; _}
   |Local_aggregate {values = args; _} ->
    List.fold_left (fun acc a -> acc + count_calls_expr check a) 0 args
  | _ -> 0

(** Count recursive calls in a statement list. *)
let rec count_calls_stmts (check : call_checker) stmts =
  List.fold_left
    (fun acc stmt ->
      acc
      +
      match stmt with
      | Return (Some e) | Expression e | Bind_variable (_, _, e) ->
        count_calls_expr check e
      | If {condition = cond; then_ = then_br; else_ = else_br} ->
        count_calls_expr check cond
        + count_calls_stmts check then_br
        + count_calls_stmts check else_br
      | Block ss -> count_calls_stmts check ss
      | Switch {scrutinee = e; enum = _; branches = branches; default = default} ->
        count_calls_expr check e
        + List.fold_left
            (fun acc (_, body) -> acc + count_calls_stmts check body)
            0
            branches
        + (match default with
           | Some ss -> count_calls_stmts check ss
           | None -> 0)
      | Custom_match {scrutinee = scrut; branches; _} ->
        count_calls_expr check scrut
        + List.fold_left
            (fun acc (b : custom_branch) -> acc + count_calls_stmts check b.body)
            0
            branches
      | Match (scrut, branches, default) ->
        count_calls_expr check scrut.expr
        + List.fold_left
          (fun acc (br : branch) ->
            acc
            + List.fold_left (fun a c -> a + count_calls_expr check c) 0 br.extra_conditions
            + count_calls_stmts check br.body )
          0 branches
        + (match default with Some ss -> count_calls_stmts check ss | None -> 0)
      | _ -> 0 )
    0
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
  | Return (Some e) -> expose_return check e
  | s -> map_stmt ~fl:(expose_tail_calls check) Fun.id (expose_stmt check) Fun.id s

and expose_return check e =
  let holds e = count_calls_expr check e > 0 in
  let return e = expose_return check e in
  match e with
  | Conditional (c, a, b) when holds a || holds b -> If {condition = c; then_ = [return a]; else_ = [return b]}
  | Binary (Or, a, b) when holds b -> If {condition = a; then_ = [Return (Some (Literal (Bool true)))]; else_ = [return b]}
  | Binary (And, a, b) when holds b -> If {condition = a; then_ = [return b]; else_ = [Return (Some (Literal (Bool false)))]}
  | _ -> Return (Some e)

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
        (Option.default survived_generically survived)
    | _ -> strategy
  in
  record_outcome name outcome;
  body

(** A recursive call a transform takes passing [args] arguments to a loop of
    [params] parameters.  A call taken is made of one of the loop's
    Continues, which passes each parameter one argument, so this is the C++
    call disagreeing with the loop's ControlIR: a violation under
    [CRANE_CHECK_IR], and the transform declines ({!Not_linearisable}). *)
let arity_mismatch ~args ~params =
  let plural n = if n = 1 then "" else "s" in
  let why =
    Printf.sprintf "a recursive call passes %d argument%s where its loop has %d parameter%s" args (plural args) params
      (plural params)
  in
  Probe.violation "control lowering" (Pp.str why);
  raise (Not_linearisable why)

(** Filter a list keeping only elements at positions where [mask] is [true].
    [mask] is indexed by the loop's parameters and [lst] is a call's
    arguments, one per parameter ({!arity_mismatch}). *)
let filter_by_mask mask lst =
  if List.compare_lengths mask lst <> 0 then arity_mismatch ~args:(List.length lst) ~params:(List.length mask);
  List.combine mask lst
  |> List.filter_map (fun (keep, x) -> if keep then Some x else None)

(** {2 This→_self substitution for method loopification} *)

(** True when an expression refers to the method receiver ([This]).
    Uses the generic {!expr_exists} traversal. *)
let expr_contains_this e =
  expr_exists (function This -> true | _ -> false) e

(** Replace [This] with [Local self_id] throughout an expression. *)
let rec this_to_self_expr (self_id : Id.t) (e : expr) : expr =
  match e with
  | This -> Local self_id
  | _ ->
    map_expr (this_to_self_expr self_id) (this_to_self_stmt self_id) Fun.id e

(** Replace [This] with [Local self_id] throughout a statement. *)
and this_to_self_stmt (self_id : Id.t) (s : stmt) : stmt =
  match s with
  | Match (scrut, branches, default) ->
    (* Matching on the receiver: [self] is a borrowed reference, so the
       payload must not be taken by [auto&] out of [v_mut()]. *)
    let receiver_match = expr_contains_this scrut.expr in
    Match
      ( { scrut with
          expr = this_to_self_expr self_id scrut.expr;
          owned = (not receiver_match) && scrut.owned },
        List.map
          (fun (br : branch) ->
            { br with
              extra_conditions =
                List.map (this_to_self_expr self_id) br.extra_conditions;
              body = List.map (this_to_self_stmt self_id) br.body })
          branches,
        Option.map (List.map (this_to_self_stmt self_id)) default )
  | _ ->
    map_stmt (this_to_self_expr self_id) (this_to_self_stmt self_id) Fun.id s

(** {2 Variable substitution} *)

(** Substitute variable names in an expression using a mapping
    [(old_id, new_id)].  A closure taking a renamed variable by move takes
    the variable by its new name: the move was planned of the variable, not
    of the name it had. *)
let rec subst_expr (subs : (Id.t * Id.t) list) e =
  let rename id =
    List.fold_left (fun id (old_id, new_id) -> if Id.equal id old_id then new_id else id) id subs
  in
  let e' =
    match e with
    | Local id -> Local (rename id)
    | Lambda l when l.moved <> [] -> Lambda {l with moved = List.map rename l.moved}
    | _ -> e
  in
  map_expr (subst_expr subs) (subst_stmt subs) (fun t -> t) e'

(** Substitute variable names in a statement using a mapping
    [(old_id, new_id)]. Statement-level companion of {!subst_expr}. *)
and subst_stmt subs s =
  map_stmt (subst_expr subs) (subst_stmt subs) (fun t -> t) s
