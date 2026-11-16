(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Smart pointer optimization for Core AST.

    This module performs escape analysis on Core terms to determine ownership
    of values, enabling two optimizations:

    1. Owned/borrowed inference: Function parameters are classified as "owned"
    (caller transfers ownership) or "borrowed" (caller retains ownership, callee
    receives const&), reducing unnecessary copies and reference-count bumps.

    2. Memory reuse optimization: Destructive pattern matches on values with
    use_count() == 1 can reuse the existing allocation by mutating fields
    in-place rather than allocating a new object.

    The analysis runs on the Core AST before translation to CppIR.  It
    attaches nothing to the tree: it answers per-parameter queries, which
    {!Ownership} settles for the whole program and translation reads back
    when it chooses parameter passing and the reuse path of a match. *)

open Base.Table

(** {2 Utility: occurrence counting} *)

(** Count occurrences of de Bruijn index [k] in [t]. For case expressions, use
    max over branches (conservative estimate).  A fixpoint's bodies are summed,
    not maximised.  An argument of an inline custom
    counts as many times as its template splices it: [sum_twice(%a0, %a0)]
    evaluates its argument twice, so a variable passed to it is read twice. *)
let nb_occur_match =
  let rec nb k = function
    | Core.Expr.Bound_variable {index = i; _} -> if i = k then 1 else 0
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      nb k scrut
      + Array.fold_left
          (fun max_count {Core.Match.Branch.binders = ids; body = body; _} ->
            max max_count (nb (k + List.length ids) body) )
          0
          branches
    | Core.Expr.Let {value = rhs; body = cont; _} -> nb k rhs + nb (k + 1) cont
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      let k' = k + Array.length ids in
      Array.fold_left (fun total body -> total + nb k' body) 0 bodies
    | Core.Expr.Lambda {body; _} -> nb (k + 1) body
    | Core.Expr.Apply {callee = (Core.Expr.Global {callee = r; _} as head);
                       arguments = args} when Base.Table.is_inline_custom r ->
      let mentions =
        match Base.Table.inline_custom_text r with
        | Some s -> Cpp_ir.Foreign_template.arg_mentions s
        | None -> fun _ -> 1
      in
      fst
        (List.fold_left
           (fun (total, i) arg -> (total + (mentions i * nb k arg), i + 1))
           (nb k head, 0) args)
    | Core.Expr.Apply {callee = head; arguments = args} ->
      List.fold_left (fun total arg -> total + nb k arg) (nb k head) args
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args ->
      List.fold_left (fun total arg -> total + nb k arg) 0 args
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> nb k a
    | Core.Expr.Persistent_array {elements = elts; default = def} ->
      Array.fold_left (fun total elt -> total + nb k elt) 0 elts + nb k def
    | Core.Expr.Global _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _ -> 0
  in
  nb

(** Simple occurrence check: does [Core.Expr.Bound_variable k] appear anywhere in [t]?  {!escapes}
    uses it for positions where any occurrence is a capture (lambda and
    fixpoint bodies, partial applications, primitive arrays). *)
let rec occurs k = function
  | Core.Expr.Bound_variable {index = i; _} -> i = k
  | Core.Expr.Match {scrutinee = scrut; branches; _} ->
    occurs k scrut
    || Array.exists
         (fun {Core.Match.Branch.binders = ids; body = body; _} -> occurs (k + List.length ids) body)
         branches
  | Core.Expr.Let {value = rhs; body = cont; _} -> occurs k rhs || occurs (k + 1) cont
  | Core.Expr.Lambda {body; _} -> occurs (k + 1) body
  | Core.Expr.Apply {callee = head; arguments = args} -> occurs k head || List.exists (occurs k) args
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
    let k' = k + Array.length ids in
    Array.exists (occurs k') bodies
  | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.exists (occurs k) args
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    occurs k a
  | Core.Expr.Persistent_array {elements = elts; default = def} -> Array.exists (occurs k) elts || occurs k def
  | Core.Expr.Global _
   |Core.Expr.Runtime_error _
   |Core.Expr.Erased_value _
   |Core.Expr.Axiom_value _
   |Core.Expr.UInt63 _ | Core.Expr.Numeral _
   |Core.Expr.Float64 _
   |Core.Expr.String _ -> false

(** Return the remaining arity of a partial application, or [None] if fully
    applied. A partial application creates a closure that captures the provided
    args, so those args effectively escape. Returns [Some remaining] when
    the function's value-level arity exceeds the number of non-dummy
    arguments. *)
let partial_app_remaining head args =
  let find_type_opt r =
    try Some (find_type r) with Not_found -> None
  in
  match head with
  | Core.Expr.Global {callee = r; _} ->
    ( match find_type_opt r with
    | Some ty ->
      let rec count_value_dom = function
        | Core.Type.Arrow {parameter = Core.Type.Erased _; result = rest} -> count_value_dom rest
        | Core.Type.Arrow {result = rest; _} -> 1 + count_value_dom rest
        | Core.Type.Meta {contents = Some t} -> count_value_dom t
        | _ -> 0
      in
      let n_dom = count_value_dom ty in
      let n_args =
        List.length
          (List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args)
      in
      if n_args < n_dom then Some (n_dom - n_args) else None
    | None -> None )
  | _ -> None

(** Check if [Core.Expr.Apply(head, args)] is a partial application. Delegates to
    [partial_app_remaining]. *)
let is_partial_app head args =
  partial_app_remaining head args <> None

(** {2 Escape analysis} *)

(** Check if de Bruijn index [k] escapes in [t].

    Escaping positions (value outlives its scope):
    - Lambda body (Core.Expr.Lambda) → captured by closure
    - Tail position → returned to caller (caller owns it)
    - Fixpoint body (Core.Expr.Fixpoint, Core.Expr.Cofixpoint) → captured by recursive closure
    - Constructor argument (Core.Expr.Construct/Core.Expr.Tuple), unless the query is
      [Of_param] → stored in a data structure

    Non-escaping positions:
    - Case scrutinee (Core.Expr.Match) → destructured immediately
    - Under Core.Expr.Coerce/Core.Expr.Boxed_value/Core.Expr.Lambda_group_barrier → transparent wrapper
    - Function arguments (Core.Expr.Apply) → callee's responsibility
    - Constructor argument (Core.Expr.Construct/Core.Expr.Tuple), for an [Of_param] query →
      callee's responsibility too: building [(s, a)] or [Ctor s] reads [s]
      once to copy it into the new value's field, exactly as calling a
      function with [s] does.  The field needs a copy either way; a
      borrowed [s] pays for it at the construction site instead of at
      every borrowed link further up the call chain that only ever passed
      [s] along: [fun s => ret (s, a)] (a monad's [ret], reading [s] to
      pair it with [a]) has the same shape as [fun s => k (t s)] (a
      monad's [bind], reading [s] to call [t]), so both are borrowable.

      Every other query treats it as an escape -- {!sub_bindings_escape}'s
      scan of a match branch's body among them -- because a
      sub-binding destructured out of an owned scrutinee and rebuilt into a
      new constructor ([match t with Node l x r -> Node (f l) x (f r)])
      needs the scrutinee owned so [x] can move out of it; relaxing that
      occurrence too would silently turn the move back into a copy.  Only
      {!infer_owned_params}'s direct query -- is this *parameter itself*,
      not something extracted from it, merely read to build a new value --
      asks [Of_param].

    An [Of_param] query also counts as an escape passing [Core.Expr.Bound_variable k] directly
    to a parameter its callee owns ([callee_flags]): the callee keeps it.

    [Of_sub_binding] and [Of_param] both look inside a lambda passed directly
    as a call argument instead of treating every capture as an escape, and
    do not count a partial application passed directly as a call argument
    as capturing its arguments. *)
type escape_query = Conservative | Of_sub_binding | Of_param

(* Whether [args], applied to the global [g], pass [Core.Expr.Bound_variable k] itself to one of
   [g]'s owned parameters, as [callee_flags] settles them: the callee keeps
   it, so a borrowed [k] would be copied there, where an owned one is
   moved. *)
let passed_to_owned callee_flags g k args =
  match callee_flags g with
  | None -> false
  | Some flags ->
    let n = List.length flags in
    let rec direct = function
      | Core.Expr.Bound_variable {index = i; _} -> i = k
      | Core.Expr.Coerce {value = a; _}
      | Core.Expr.Boxed_value {value = a; _}
      | Core.Expr.Lambda_group_barrier {value = a; _} -> direct a
      | _ -> false
    in
    List.exists
      (fun (j, a) -> j < n && direct a && List.nth flags (n - 1 - j))
      (List.mapi (fun j a -> (j, a)) args)

let escapes ?(query = Conservative) ?(callee_flags = fun _ -> None) ?(return_escapes = true) k t =
  let refined = query <> Conservative in
  let cons_escapes = query <> Of_param in
  let rec check k in_tail in_fn_arg = function
    | Core.Expr.Bound_variable {index = i; _} -> i = k && in_tail && return_escapes
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      ( match scrut with
      | Core.Expr.Bound_variable {index = i; _} when i = k -> false
      | _ -> check k false false scrut )
      || Array.exists
           (fun {Core.Match.Branch.binders = ids; body = body; _} ->
             check (k + List.length ids) in_tail false body )
           branches
    | Core.Expr.Let {value = rhs; body = cont; _} ->
      check k false false rhs || check (k + 1) in_tail false cont
    | Core.Expr.Lambda {body; _} ->
      if refined && in_fn_arg then
        check (k + 1) false false body
      else
        occurs (k + 1) body
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = g; _};
                       arguments = args} when query = Of_param && passed_to_owned callee_flags g k args -> true
    | Core.Expr.Apply {callee = head; arguments = args} ->
      check k false false head
      || List.exists (check k false (refined)) args
      || (not in_fn_arg && is_partial_app head args
         && List.exists (occurs k) args)
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      let k' = k + Array.length ids in
      Array.exists (occurs k') bodies
    | Core.Expr.Construct {arguments = args; _} ->
      List.exists (check k cons_escapes false) args
    | Core.Expr.Tuple args -> List.exists (check k cons_escapes false) args
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} ->
      check k in_tail false a
    | Core.Expr.Persistent_array {elements = elts; default = def} -> Array.exists (occurs k) elts || occurs k def
    | Core.Expr.Global _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _ -> false
  in
  check k true false t

(** {2 Owned/borrowed parameter inference} *)

(** Determine if parameters need ownership (pass by value) or can borrow (pass
    by const ref).

    A parameter needs ownership when:
    - Returned in tail position (caller needs ownership)
    - Stored in constructor (outlives the call)
    - Captured by lambda or fixpoint (outlives the call)

    A parameter can be borrowed when it only appears in:
    - Case scrutinee (destructured immediately)
    - Under Core.Expr.Coerce/Core.Expr.Boxed_value/Core.Expr.Lambda_group_barrier (transparent wrapper)
    - Call arguments, other than one the callee owns
    - Constructor arguments (read once to copy into the new field)

    This is escape analysis with an [Of_param] query (a parameter "escapes"
    when the caller needs to pass ownership rather than just lend a
    reference), with two adjustments in {!infer_owned_params}: a parameter
    only matched on and returned as it is stays borrowed
    ({!returned_or_matched}), and a reuse scrutinee is owned
    ({!is_reuse_scrutinee}). *)

(** Check if sub-bindings of a parameter used as scrutinee escape.
    When param [k] appears only in scrutinee position but the extracted
    pattern variables are consumed (returned, stored in constructors),
    the parameter should be owned so sub-bindings can be moved. *)
let sub_bindings_escape k body =
  let rec check k = function
    | Core.Expr.Match {scrutinee = Core.Expr.Bound_variable {index = i; _}; branches; _} when i = k ->
      Array.exists (fun {Core.Match.Branch.binders = ids; body = branch_body; _} ->
        let n = List.length ids in
        List.exists (fun j ->
          escapes ~query:Of_sub_binding (j + 1) branch_body
        ) (List.init n Fun.id)
      ) branches
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      check k scrut
      || Array.exists (fun {Core.Match.Branch.binders = ids; body = body; _} ->
           check (k + List.length ids) body
         ) branches
    | Core.Expr.Let {value = rhs; body = cont; _} ->
      check k rhs || check (k + 1) cont
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> check k a
    | _ -> false
  in
  check k body

(** {2 Phase 2: reuse candidate discovery} *)

(* The constructions [body] returns, wherever it returns one: under its
   [let]s, and in each branch of a match it ends in -- a map's update
   rebuilds its node in whichever branch the key comparison picks. *)
let rec tail_constructions = function
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    tail_constructions a
  | Core.Expr.Let {body = b; _} -> tail_constructions b
  | Core.Expr.Construct _ as c -> [c]
  | Core.Expr.Match {branches = brs; _} ->
    List.concat_map (fun {Core.Match.Branch.body = b; _} -> tail_constructions b) (Array.to_list brs)
  | _ -> []

(** [find_reuse_candidates pv]: match branches whose body builds an [Core.Expr.Construct]
    of the same inductive type as the matched constructor, as
    [(branch_idx, matched_ctor, matched_arity, tail_ctor, tail_args)]. *)
let find_reuse_candidates (pv : Core.Match.Branch.t array) =
  let ctor_ind = function
    | Names.GlobRef.ConstructRef (ind, _) -> Some ind
    | _ -> None
  in
  let same_inductive a b =
    match (ctor_ind a, ctor_ind b) with
    | Some (m1, i1), Some (m2, i2) ->
      Names.MutInd.CanOrd.equal m1 m2 && Int.equal i1 i2
    | _ -> false
  in
  let tail_conses body =
    List.filter_map (function Core.Expr.Construct {constructor = r; arguments = args; _} -> Some (r, args) | _ -> None)
      (tail_constructions body)
  in
  let cands = ref [] in
  Array.iteri
    (fun idx {Core.Match.Branch.binders = ids; pattern = pat; body = body; _} ->
      match pat with
      | Core.Pattern.Constructor {constructor = mr; _} ->
        (* One candidate per constructor the arm may rebuild: a nullary one
           among them ([take]'s [nil]) has no cell to recycle into, so the
           caller picks among them. *)
        let tails =
          List.sort_uniq
            (fun (a, _) (b, _) -> Names.GlobRef.CanOrd.compare a b)
            (List.filter (fun (tr, _) -> same_inductive mr tr) (tail_conses body))
        in
        List.iter
          (fun (tr, targs) -> cands := (idx, mr, List.length ids, tr, targs) :: !cands)
          tails
      | Core.Pattern.Wildcard | Core.Pattern.Bound_variable _ | Core.Pattern.Tuple _ -> () )
    pv;
  List.rev !cands

(** [is_reuse_scrutinee k body]: does [body] match on parameter [k] (de Bruijn,
    1 = innermost) with at least one reuse candidate arm, on a type whose cells
    can be recycled?  Such a scrutinee must be passed OWNED (by value) so the
    reuse path can consume it; escape analysis would otherwise borrow a
    match-only param.  A shared variant's block is recycled whatever the
    counts; another type's child cell only under non-atomic counts (the
    recycling helpers in rc.h are single-threaded, matching the rest of
    Crane's clone-at-boundary model).

    Non-atomic counts as requested, not as a unit is granted them: ownership
    is settled for the whole program ({!Ownership.summarize}) before any
    unit's concurrency is decided, and a function's parameters are owned the
    same way in every unit that calls it.  A unit refused the request
    because it starts a thread ({!Base.Table.non_atomic_rc_for}) owns such a
    parameter and recycles nothing through it: the rewrite itself is gated
    on the granted answer. *)
let is_reuse_scrutinee k body =
  let recyclable = function
    | Core.Type.Global_app {head = r; _} when Base.Table.is_shared_variant r -> true
    | _ -> non_atomic_rc_requested ()
  in
  let found = ref false in
  let rec scan d = function
    | Core.Expr.Match {scrutinee_type = typ; scrutinee = scrut; branches; _} ->
      ( match scrut with
      | Core.Expr.Bound_variable {index = j; _}
      | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = j; _}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = j; _}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = j; _}; _} ->
        if j > d && j - d = k && recyclable typ
           && find_reuse_candidates branches <> []
        then found := true
      | _ -> () );
      scan d scrut;
      Array.iter
        (fun {Core.Match.Branch.binders = ids; body = b; _} -> scan (d + List.length ids) b)
        branches
    | Core.Expr.Let {value = rhs; body = cont; _} -> scan d rhs; scan (d + 1) cont
    | Core.Expr.Lambda {body = b; _} -> scan (d + 1) b
    | Core.Expr.Apply {callee = f; arguments = args} -> scan d f; List.iter (scan d) args
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      Array.iter (scan (d + Array.length ids)) bodies
    | Core.Expr.Construct {arguments = ts; _} | Core.Expr.Tuple ts -> List.iter (scan d) ts
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> scan d a
    | Core.Expr.Persistent_array {elements = arr; default = def} -> Array.iter (scan d) arr; scan d def
    | _ -> ()
  in
  scan 0 body;
  !found

(* Whether [Core.Expr.Bound_variable k] is matched on in [t]. *)
let rec matched k = function
  | Core.Expr.Match {scrutinee = scrut; branches; _} ->
    (match scrut with
     | Core.Expr.Bound_variable {index = i; _}
     | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
     | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
     | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} -> i = k
     | _ -> false)
    || matched k scrut
    || Array.exists (fun {Core.Match.Branch.binders = ids; body = b; _} -> matched (k + List.length ids) b) branches
  | Core.Expr.Let {value = rhs; body = cont; _} -> matched k rhs || matched (k + 1) cont
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    matched k a
  | _ -> false

(* A parameter that is matched on, and otherwise only ever returned as it is
   -- the tree an update returns unchanged when the key is absent -- is
   borrowed.  Owning it would let the return move instead of copy, but every
   call that passes it a part of a matched value, which is how a structural
   recursion calls itself, would copy that part in: at every level, against
   one copy at the end. *)
let returned_or_matched ~callee_flags k body =
  matched k body
  && not (escapes ~query:Of_param ~callee_flags ~return_escapes:false k body)

let infer_owned_params ~callee_flags n_params body =
  (* Reuse and loopify both rewrite tail-recursive-modulo-cons matches (the
     [Cons x (rec xs)] shape).  Only one of them may rewrite a given match --
     loopify owns the shape wherever it applies -- but BOTH need the scrutinee
     passed owned, because both recycle its cells: loopify does so through the
     owning cursor its TMC loop carries (see {!Control_to_cpp.Reuse_cursor}).  So this
     inference does not defer to loopify; it asks only whether reuse can be
     performed at all.  The consumer that actually emits a reuse rewrite,
     translation's dual-path match, defers to loopify via
     [Base.Table.reuse_loopify_ok]. *)
  List.init n_params (fun i ->
    let k = i + 1 in
    ( escapes ~query:Of_param ~callee_flags k body
      && not (returned_or_matched ~callee_flags k body) )
    || (reuse_here () && is_reuse_scrutinee k body))

(** Like [infer_owned_params] but returns only the [sub_bindings_escape]
    contribution.  Callers can OR this into the base owned flags selectively
    (e.g., only for value-typed parameters, not shared_ptr-backed lists). *)
let infer_sub_bindings_escape_params n_params body =
  List.init n_params (fun i ->
    sub_bindings_escape (i + 1) body)

(** {2 Projections} *)

let returns_receiver_field ~this_pos fn =
  let params, body = Base.Core_util.collect_lams fn in
  let receiver = List.length params - this_pos in
  let bare = Core.Expr.strip_crossings in
  List.length params = 1
  &&
  match bare body with
  | Core.Expr.Match {scrutinee = scrut;
                     branches = [| {Core.Match.Branch.binders = ids;
                                    pattern = Core.Pattern.Constructor _;
                                    body = result; _} |]; _} -> (
    (match bare scrut with Core.Expr.Bound_variable {index = i; _} -> i = receiver | _ -> false)
    && match bare result with Core.Expr.Bound_variable {index = j; _} -> j <= List.length ids | _ -> false )
  | _ -> false

(** {2 Utility functions} *)

(** Set of integers for tracking de Bruijn indices. *)
module IntSet = Base.Core_util.IntSet

(** Compute free de Bruijn indices in [t], shifted by [depth]. An index
    [i > depth] in [t] contributes [i - depth] to the result. *)
let free_rels depth t =
  let free = ref IntSet.empty in
  let rec collect d = function
    | Core.Expr.Bound_variable {index = i; _} when i > d -> free := IntSet.add (i - d) !free
    | Core.Expr.Bound_variable _ -> ()
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      collect d scrut;
      Array.iter
        (fun {Core.Match.Branch.binders = ids; body = body; _} -> collect (d + List.length ids) body)
        branches
    | Core.Expr.Let {value = rhs; body = cont; _} ->
      collect d rhs;
      collect (d + 1) cont
    | Core.Expr.Lambda {body; _} -> collect (d + 1) body
    | Core.Expr.Apply {callee = head; arguments = args} ->
      collect d head;
      List.iter (collect d) args
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      let d' = d + Array.length ids in
      Array.iter (collect d') bodies
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.iter (collect d) args
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} ->
      collect d a
    | Core.Expr.Persistent_array {elements = elts; default = def} ->
      Array.iter (collect d) elts;
      collect d def
    | Core.Expr.Global _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _ -> ()
  in
  collect depth t;
  !free

(** Find the single use of [Core.Expr.Bound_variable k] in [t] and return how many non-dummy
    args it is applied to (0 if it appears bare, not as head of Core.Expr.Apply).
    Precondition: [k] occurs at most once in [t]. *)
let single_use_nargs k t =
  let result = ref 0 in
  let rec search k = function
    | Core.Expr.Apply {callee = ( Core.Expr.Bound_variable {index = i; _}
          | Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
          | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
          | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _} ); arguments = args}
      when i = k ->
      result :=
        List.length
          (List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args)
    | Core.Expr.Bound_variable _ -> ()
    | Core.Expr.Let {value = rhs; body = cont; _} ->
      search k rhs;
      search (k + 1) cont
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      search k scrut;
      Array.iter
        (fun {Core.Match.Branch.binders = ids; body = body; _} -> search (k + List.length ids) body)
        branches
    | Core.Expr.Lambda {body; _} -> search (k + 1) body
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      Array.iter (search (k + Array.length ids)) bodies
    | Core.Expr.Apply {callee = head; arguments = args} ->
      search k head;
      List.iter (search k) args
    | Core.Expr.Construct {arguments = args; _} -> List.iter (search k) args
    | Core.Expr.Tuple args -> List.iter (search k) args
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} ->
      search k a
    | Core.Expr.Persistent_array {elements = elts; default = def} ->
      Array.iter (search k) elts;
      search k def
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ ->
      ()
  in
  search k t;
  !result

(** Check if [ty] is a non-enum, non-coinductive, non-custom inductive.  The
    name predates value-type inductives: most such inductives are value
    types in C++, with only their recursive fields behind a shared pointer.
    The predicate separates Crane's own inductive layouts from enums, lazy
    coinductives and custom mappings.  Custom-extracted inductives (e.g., prod mapped to
    std::pair) are excluded.  Resolves Core.Type.Meta chains. *)
let rec is_shared_ptr_type = function
  | Core.Type.Global_app {head = r; _} ->
    ( match r with
    | Names.GlobRef.IndRef _ ->
      (not (is_enum_inductive r))
      && not (is_coinductive_type (Core.Type.Global_app {head = r; type_arguments = []; index_arguments = []}))
      && not (is_custom r)
    | _ -> false )
  | Core.Type.Meta {contents = Some ty} -> is_shared_ptr_type ty
  | _ -> false

