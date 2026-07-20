(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Smart pointer optimization for MiniML AST.

    This module performs escape analysis on MiniML terms to determine ownership
    of values, enabling two optimizations:

    1. Owned/borrowed inference: Function parameters are classified as "owned"
    (caller transfers ownership) or "borrowed" (caller retains ownership, callee
    receives const&), reducing unnecessary copies and reference-count bumps.

    2. Memory reuse optimization: Destructive pattern matches on values with
    use_count() == 1 can reuse the existing allocation by mutating fields
    in-place rather than allocating a new object.

    The analysis runs on the MiniML AST before translation to MiniCpp, attaching
    ownership annotations that translation.ml and cpp.ml use during code
    generation. *)

open Miniml
open Table

(** {2 Utility: occurrence counting} *)

(** Count occurrences of de Bruijn index [k] in [t]. For case expressions, use
    max over branches (conservative estimate). *)
let nb_occur_match =
  let rec nb k = function
    | MLrel i -> if i = k then 1 else 0
    | MLcase (_, scrut, branches) ->
      nb k scrut
      + Array.fold_left
          (fun max_count (ids, _, _, body) ->
            max max_count (nb (k + List.length ids) body) )
          0
          branches
    | MLletin (_, _, rhs, cont) -> nb k rhs + nb (k + 1) cont
    | MLfix (_, ids, bodies, _) ->
      let k' = k + Array.length ids in
      Array.fold_left (fun total body -> total + nb k' body) 0 bodies
    | MLlam (_, _, body) -> nb (k + 1) body
    | MLapp (head, args) ->
      List.fold_left (fun total arg -> total + nb k arg) (nb k head) args
    | MLcons (_, _, args) | MLtuple args ->
      List.fold_left (fun total arg -> total + nb k arg) 0 args
    | MLmagic a -> nb k a
    | MLparray (elts, def) ->
      Array.fold_left (fun total elt -> total + nb k elt) 0 elts + nb k def
    | MLglob _
     |MLexn _
     |MLdummy _
     |MLaxiom _
     |MLuint _
     |MLfloat _
     |MLstring _ -> 0
  in
  nb

(** Simple occurrence check: does [MLrel k] appear anywhere in [t]? Used by both
    escape analysis and the combined analysis below. *)
let rec occurs k = function
  | MLrel i -> i = k
  | MLcase (_, scrut, branches) ->
    occurs k scrut
    || Array.exists
         (fun (ids, _, _, body) -> occurs (k + List.length ids) body)
         branches
  | MLletin (_, _, rhs, cont) -> occurs k rhs || occurs (k + 1) cont
  | MLlam (_, _, body) -> occurs (k + 1) body
  | MLapp (head, args) -> occurs k head || List.exists (occurs k) args
  | MLfix (_, ids, bodies, _) ->
    let k' = k + Array.length ids in
    Array.exists (occurs k') bodies
  | MLcons (_, _, args) | MLtuple args -> List.exists (occurs k) args
  | MLmagic a -> occurs k a
  | MLparray (elts, def) -> Array.exists (occurs k) elts || occurs k def
  | MLglob _
   |MLexn _
   |MLdummy _
   |MLaxiom _
   |MLuint _
   |MLfloat _
   |MLstring _ -> false

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
  | MLglob (r, _) ->
    ( match find_type_opt r with
    | Some ty ->
      let rec count_value_dom = function
        | Tarr (Tdummy _, rest) -> count_value_dom rest
        | Tarr (_, rest) -> 1 + count_value_dom rest
        | Tmeta {contents = Some t} -> count_value_dom t
        | _ -> 0
      in
      let n_dom = count_value_dom ty in
      let n_args =
        List.length
          (List.filter (function MLdummy _ -> false | _ -> true) args)
      in
      if n_args < n_dom then Some (n_dom - n_args) else None
    | None -> None )
  | _ -> None

(** Check if [MLapp(head, args)] is a partial application. Delegates to
    [partial_app_remaining]. *)
let is_partial_app head args =
  partial_app_remaining head args <> None

(** {2 Escape analysis} *)

(** Check if de Bruijn index [k] escapes in [t].

    Escaping positions (value outlives its scope):
    - Constructor argument (MLcons) → stored in data structure
    - Lambda body (MLlam) → captured by closure
    - Tail position → returned to caller (caller owns it)
    - Fixpoint body (MLfix) → captured by recursive closure

    Non-escaping positions:
    - Case scrutinee (MLcase) → destructured immediately
    - Under MLmagic → transparent wrapper
    - Function arguments (MLapp) → callee's responsibility *)
let escapes ?(refined = false) k t =
  let rec check k in_tail in_fn_arg = function
    | MLrel i -> i = k && in_tail
    | MLcase (_, scrut, branches) ->
      ( match scrut with
      | MLrel i when i = k -> false
      | _ -> check k false false scrut )
      || Array.exists
           (fun (ids, _, _, body) ->
             check (k + List.length ids) in_tail false body )
           branches
    | MLletin (_, _, rhs, cont) ->
      check k false false rhs || check (k + 1) in_tail false cont
    | MLlam (_, _, body) ->
      if refined && in_fn_arg then
        check (k + 1) false false body
      else
        occurs (k + 1) body
    | MLapp (head, args) ->
      check k false false head
      || List.exists (check k false (refined)) args
      || (not in_fn_arg && is_partial_app head args
         && List.exists (occurs k) args)
    | MLfix (_, ids, bodies, _) ->
      let k' = k + Array.length ids in
      Array.exists (occurs k') bodies
    | MLcons (_, _, args) ->
      List.exists (check k true false) args
    | MLtuple args -> List.exists (check k true false) args
    | MLmagic a -> check k in_tail false a
    | MLparray (elts, def) -> Array.exists (occurs k) elts || occurs k def
    | MLglob _
     |MLexn _
     |MLdummy _
     |MLaxiom _
     |MLuint _
     |MLfloat _
     |MLstring _ -> false
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
    - Under MLmagic (transparent wrapper)

    This is identical to escape analysis — a parameter "escapes" when the caller
    needs to pass ownership rather than just lend a reference. *)

(** Check if sub-bindings of a parameter used as scrutinee escape.
    When param [k] appears only in scrutinee position but the extracted
    pattern variables are consumed (returned, stored in constructors),
    the parameter should be owned so sub-bindings can be moved. *)
let sub_bindings_escape k body =
  let rec check k = function
    | MLcase (_, MLrel i, branches) when i = k ->
      Array.exists (fun (ids, _, _, branch_body) ->
        let n = List.length ids in
        List.exists (fun j ->
          escapes ~refined:true (j + 1) branch_body
        ) (List.init n Fun.id)
      ) branches
    | MLcase (_, scrut, branches) ->
      check k scrut
      || Array.exists (fun (ids, _, _, body) ->
           check (k + List.length ids) body
         ) branches
    | MLletin (_, _, rhs, cont) ->
      check k rhs || check (k + 1) cont
    | MLmagic a -> check k a
    | _ -> false
  in
  check k body

let infer_owned_params n_params body =
  List.init n_params (fun i ->
    let k = i + 1 in
    escapes ~refined:true k body)

(** Like [infer_owned_params] but returns only the [sub_bindings_escape]
    contribution.  Callers can OR this into the base owned flags selectively
    (e.g., only for value-typed parameters, not shared_ptr-backed lists). *)
let infer_sub_bindings_escape_params n_params body =
  List.init n_params (fun i ->
    sub_bindings_escape (i + 1) body)

(** {2 Utility functions} *)

(** Set of integers for tracking de Bruijn indices. *)
module IntSet = Set.Make (Int)

(** Compute free de Bruijn indices in [t], shifted by [depth]. An index
    [i > depth] in [t] contributes [i - depth] to the result. *)
let free_rels depth t =
  let free = ref IntSet.empty in
  let rec collect d = function
    | MLrel i when i > d -> free := IntSet.add (i - d) !free
    | MLrel _ -> ()
    | MLcase (_, scrut, branches) ->
      collect d scrut;
      Array.iter
        (fun (ids, _, _, body) -> collect (d + List.length ids) body)
        branches
    | MLletin (_, _, rhs, cont) ->
      collect d rhs;
      collect (d + 1) cont
    | MLlam (_, _, body) -> collect (d + 1) body
    | MLapp (head, args) ->
      collect d head;
      List.iter (collect d) args
    | MLfix (_, ids, bodies, _) ->
      let d' = d + Array.length ids in
      Array.iter (collect d') bodies
    | MLcons (_, _, args) | MLtuple args -> List.iter (collect d) args
    | MLmagic a -> collect d a
    | MLparray (elts, def) ->
      Array.iter (collect d) elts;
      collect d def
    | MLglob _
     |MLexn _
     |MLdummy _
     |MLaxiom _
     |MLuint _
     |MLfloat _
     |MLstring _ -> ()
  in
  collect depth t;
  !free

(** Find the single use of [MLrel k] in [t] and return how many non-dummy
    args it is applied to (0 if it appears bare, not as head of MLapp).
    Precondition: [k] occurs at most once in [t]. *)
let single_use_nargs k t =
  let result = ref 0 in
  let rec search k = function
    | MLapp ((MLrel i | MLmagic (MLrel i)), args) when i = k ->
      result :=
        List.length
          (List.filter (function MLdummy _ -> false | _ -> true) args)
    | MLrel _ -> ()
    | MLletin (_, _, rhs, cont) ->
      search k rhs;
      search (k + 1) cont
    | MLcase (_, scrut, branches) ->
      search k scrut;
      Array.iter
        (fun (ids, _, _, body) -> search (k + List.length ids) body)
        branches
    | MLlam (_, _, body) -> search (k + 1) body
    | MLfix (_, ids, bodies, _) ->
      Array.iter (search (k + Array.length ids)) bodies
    | MLapp (head, args) ->
      search k head;
      List.iter (search k) args
    | MLcons (_, _, args) -> List.iter (search k) args
    | MLtuple args -> List.iter (search k) args
    | MLmagic a -> search k a
    | MLparray (elts, def) ->
      Array.iter (search k) elts;
      search k def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _
    | MLstring _ ->
      ()
  in
  search k t;
  !result

(** Check if [ty] is a non-enum, non-coinductive, non-custom inductive
    (wrapped in shared_ptr in C++). Custom-extracted inductives (e.g., prod
    mapped to std::pair) are value types, not wrapped in shared_ptr.
    Resolves Tmeta chains. *)
let rec is_shared_ptr_type = function
  | Tglob (r, _, _) ->
    ( match r with
    | Names.GlobRef.IndRef _ ->
      (not (is_enum_inductive r))
      && not (is_coinductive_type (Tglob (r, [], [])))
      && not (is_custom r)
    | _ -> false )
  | Tmeta {contents = Some ty} -> is_shared_ptr_type ty
  | _ -> false

