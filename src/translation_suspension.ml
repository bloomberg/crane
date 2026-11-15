(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** When naming or building something runs code: why a global is emitted as
    a function of no parameters, whether a definition or a coinductive
    constructor application is suspended, and whether evaluating a term may
    throw.  Read by lowering, {!Recursion_plan} and the function
    generators. *)

open Common
open Util
open Translation_state
open Type_util
open Core_query

(** Why a global is emitted as a function of no parameters, so that naming it
    calls it: a cofixpoint, whose value is built when asked for; a definition
    whose body only throws ({!Structure_analysis.throwing_values}),
    which must throw when asked for rather than during static
    initialisation; a monadic action, run when performed. *)
type thunk_reason = Cofixpoint | Throws | Monadic

(** The {!thunk_reason} of the global [r], if it has one: the one place that
    decides it, which the declaration of [r] and every reference to it read. *)
let thunk_reason r =
  if Table.is_cofixpoint r then Some Cofixpoint
  else if is_throwing_value r then Some Throws
  else
    match find_type_opt r with
    | Some t when is_monadic_core_type t -> Some Monadic
    | _ -> None

(** Whether naming the global [r] calls it.  A definition that only throws is
    emitted as a zero-parameter function unless it has C++ parameters of its
    own -- [cpp_of] spells its type -- in which case naming it names the
    function. *)
let naming_calls ~cpp_of r =
  match thunk_reason r with
  | None -> false
  | Some (Cofixpoint | Monadic) -> true
  | Some Throws -> (
    match Option.map cpp_of (callee_core_type r) with Some (Cpp_ir.Type.Function _) -> false | _ -> true )

(** Whether evaluating [e] is only building a value: no call is made, so it
    cannot fail to terminate.  A lambda is a value; so is a constructor of
    values.  A global is a value unless naming it calls it ({!thunk_reason}). *)
let rec core_is_value = function
  | Core.Expr.Bound_variable _
  | Core.Expr.Lambda _
  | Core.Expr.Erased_value _
  | Core.Expr.UInt63 _
  | Core.Expr.Numeral _
  | Core.Expr.Float64 _
  | Core.Expr.String _ -> true
  | Core.Expr.Global {callee = r; _} -> thunk_reason r = None
  | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.for_all core_is_value args
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    core_is_value e
  | _ -> false

(** Whether [body] calls [r] somewhere a suspension does not reach: outside
    every lambda and every coinductive constructor.  Rocq's guard condition
    rules this out syntactically, but it checks guardedness up to unfolding
    definitions, so a corecursive call may sit under a function that only
    builds the constructor once unfolded.  A body like that is suspended
    whole rather than at its constructors. *)
let calls_eagerly r body =
  let exception Found in
  let rec walk e =
    match e with
    | Core.Expr.Global {callee = r'; _} when globref_equal r r' -> raise Found
    | Core.Expr.Lambda _ -> ()
    | Core.Expr.Construct {result_type = ty; _} when Table.is_coinductive_type ty -> ()
    | _ -> Core_util.ast_iter walk e
  in
  try walk body; false with Found -> true

(** Whether the definition [r], whose Core result type is [core_ret], is suspended
    whole: a coinductive result, and a body [b] that calls [r] outside every
    constructor -- Rocq's guard condition holds only up to unfolding.  Any
    other coinductive body is suspended at its constructors
    ({!suspend_ctor}). *)
let suspends_whole r core_ret b = Table.is_coinductive_type core_ret && calls_eagerly r b

(** Whether the arguments [ts] of a coinductive constructor may run the
    corecursion the constructor guards, so that only a suspension keeps them
    from unfolding without end: they name the declaration being generated,
    [self], a global or a binder that yields a coinductive value -- a sibling
    in a mutual block, a local cofixpoint -- or a fixpoint of their own.
    Anything else is an ordinary call, which ends: every body suspends its
    own corecursive calls at its constructors.  [binder_type i] is the type
    of the binder at de Bruijn index [i] where the constructor stands; a
    binder whose type is not known counts as corecursive. *)
let args_may_corecurse ~self ~binder_type ts =
  let yields_coinductive ty = Table.is_coinductive_type (core_codomain ty) in
  let rec corec depth t =
    match t with
    | Core.Expr.Global {callee = g; _} -> (
      (match self with
       | Some self -> globref_equal g self
       | None -> false)
      || match find_type_opt g with Some ty -> yields_coinductive ty | None -> false )
    | Core.Expr.Bound_variable {index = i; _} when i > depth -> (
      match binder_type (i - depth) with
      | Some (Core.Type.Unknown | Core.Type.Axiom) | None -> true
      | Some ty -> yields_coinductive ty )
    | Core.Expr.Bound_variable _ -> false
    | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ -> true
    | Core.Expr.Lambda {body = b; _} -> corec (depth + 1) b
    | Core.Expr.Let {value = a; body = b; _} -> corec depth a || corec (depth + 1) b
    | Core.Expr.Match {scrutinee = s; branches = brs; _} ->
      corec depth s
      || Array.exists (fun {Core.Match.Branch.binders = ids; body = b; _} -> corec (depth + List.length ids) b) brs
    | e ->
      let exception Found in
      (try Core_util.ast_iter (fun c -> if corec depth c then raise Found) e; false
       with Found -> true)
  in
  List.exists (corec 0) ts

(** Whether a constructor of the inductive [n] applied to [ts] is suspended
    ({!suspend_ctor}): [n] is coinductive, and its arguments are not all
    values and may run the corecursion ({!args_may_corecurse}, which [self]
    and [binder_type] are passed to). *)
let suspends_constructor ~self ~binder_type n ts =
  Table.is_coinductive n
  && (not (List.for_all core_is_value ts))
  && args_may_corecurse ~self ~binder_type ts

(** [suspend_ctor ty ctor args] is the coinductive constructor [ctor] of
    type [ty] applied to [args], suspended:
    [ty::lazy_([=]() -> typename ty::ctor { return {args}; })].  The thunk
    yields the constructor's fields rather than a [ty] built by its factory,
    so forcing builds the value in the suspended cell itself, not in a cell
    of its own that is then emptied into it.

    The only suspension point a coinductive value has, as in OCaml's
    extraction: everything else in a body runs where it is written.  It is
    taken only where the constructor's arguments may run the corecursion
    ({!args_may_corecurse}).  Rocq's guard condition puts every corecursive
    call under a constructor, so a constructor whose arguments only compute
    -- [Ret (f x)] -- holds no call to delay, and is built directly: a lazy
    cell already holding its value, where a suspension would be a closure
    to allocate, run and free.  The thunk takes the variables [moved] by
    move where it is made. *)
let suspend_ctor ~moved (ty : Cpp_ir.Lowered.Type.t) ctor (args : Cpp_ir.Lowered.Expr.t list) : Cpp_ir.Lowered.Expr.t =
  let thunk : Cpp_ir.Lowered.Expr.t =
    match Cpp_ir.Build.lambda [] (Some (Member (ty, ctor))) [Return (Some (Braced args))] ~capture:Stored with
    | Lambda l -> Lambda {l with moved}
    | e -> e
  in
  Suspend (ty, thunk)

(** True when evaluating a Core term may throw through an extracted axiom or
    exception. Functions whose bodies can throw must not be marked
    [__attribute__((pure))]: Clang may otherwise move calls across local
    exception handlers or discard them when their result is unused. *)
let rec ast_may_throw = function
  | Core.Expr.Axiom_value _ | Core.Expr.Runtime_error _ -> true
  | Core.Expr.Global {callee = r; _} -> is_throwing_value r
  | Core.Expr.Lambda {body; _} -> ast_may_throw body
  | Core.Expr.Let {value = a; body = b; _} -> ast_may_throw a || ast_may_throw b
  | Core.Expr.Construct {arguments = args; _} -> List.exists ast_may_throw args
  | Core.Expr.Match {scrutinee = e; branches = brs; _} ->
    ast_may_throw e
    || Array.exists (fun {Core.Match.Branch.body = body; _} -> ast_may_throw body) brs
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let funs = Core.Recursion.Group.bodies rec_group in
    Array.exists ast_may_throw funs
  | Core.Expr.Apply {callee = f; arguments = args} -> ast_may_throw f || List.exists ast_may_throw args
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    ast_may_throw a
  | Core.Expr.Persistent_array {elements = arr; default = def} -> Array.exists ast_may_throw arr || ast_may_throw def
  | Core.Expr.Tuple args -> List.exists ast_may_throw args
  | Core.Expr.Bound_variable _
  | Core.Expr.Erased_value _
  | Core.Expr.UInt63 _
  | Core.Expr.Numeral _
  | Core.Expr.Float64 _
  | Core.Expr.String _ -> false
