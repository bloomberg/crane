(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*s Smart pointer optimization for MiniML AST. *)

open Miniml
open Table

(* ========================================================================== *)
(*  Utility: occurrence counting                                             *)
(* ========================================================================== *)

(* Count occurrences of de Bruijn index [k] in [t].
   For case expressions, use max over branches (conservative estimate). *)
let nb_occur_match =
  let rec nb k = function
    | MLrel i -> if i = k then 1 else 0
    | MLcase (_, scrut, branches) ->
        nb k scrut +
        Array.fold_left (fun max_count (ids, _, _, body) ->
          max max_count (nb (k + List.length ids) body)
        ) 0 branches
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
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> 0
  in nb

(* ========================================================================== *)
(*  Phase 1: Escape analysis for unique_ptr promotion                        *)
(* ========================================================================== *)

(* Check if de Bruijn index [k] escapes in [t].

   Escaping positions (value outlives its scope):
     - Constructor argument (MLcons) → stored in data structure
     - Lambda body (MLlam) → captured by closure
     - Tail position → returned to caller (caller owns it)
     - Fixpoint body (MLfix) → captured by recursive closure

   Non-escaping positions (safe for unique_ptr):
     - Case scrutinee (MLcase) → destructured immediately
     - Under MLmagic → transparent wrapper
     - Function arguments (MLapp) → callee's responsibility *)
let escapes k t =
  (* [check k in_tail t]: does [MLrel k] escape in [t]?
     [in_tail]: are we in tail position (return value)? *)
  let rec check k in_tail = function
    | MLrel i -> i = k && in_tail

    | MLcase (_, scrut, branches) ->
        (* Scrutinee is safe (destructured). Branches inherit tail position. *)
        (match scrut with
         | MLrel i when i = k -> false  (* Safe: scrutinee position *)
         | _ -> check k false scrut) ||
        Array.exists (fun (ids, _, _, body) ->
          check (k + List.length ids) in_tail body
        ) branches

    | MLletin (_, _, rhs, cont) ->
        check k false rhs || check (k + 1) in_tail cont

    | MLlam (_, _, body) ->
        occurs (k + 1) body  (* Lambda capture → escape *)

    | MLapp (head, args) ->
        (* Arguments don't escape (callee borrows or copies).
           Only escape if variable appears within argument expression. *)
        check k false head || List.exists (check k false) args

    | MLfix (_, ids, bodies, _) ->
        let k' = k + Array.length ids in
        Array.exists (occurs k') bodies  (* Fixpoint capture → escape *)

    | MLcons (_, _, args) ->
        List.exists (occurs k) args  (* Constructor storage → escape *)

    | MLtuple args ->
        List.exists (occurs k) args

    | MLmagic a -> check k in_tail a

    | MLparray (elts, def) ->
        Array.exists (occurs k) elts || occurs k def

    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> false

  (* Simple occurrence check: does [MLrel k] appear anywhere in [t]? *)
  and occurs k = function
    | MLrel i -> i = k
    | MLcase (_, scrut, branches) ->
        occurs k scrut ||
        Array.exists (fun (ids, _, _, body) ->
          occurs (k + List.length ids) body
        ) branches
    | MLletin (_, _, rhs, cont) ->
        occurs k rhs || occurs (k + 1) cont
    | MLlam (_, _, body) -> occurs (k + 1) body
    | MLapp (head, args) ->
        occurs k head || List.exists (occurs k) args
    | MLfix (_, ids, bodies, _) ->
        let k' = k + Array.length ids in
        Array.exists (occurs k') bodies
    | MLcons (_, _, args) | MLtuple args ->
        List.exists (occurs k) args
    | MLmagic a -> occurs k a
    | MLparray (elts, def) ->
        Array.exists (occurs k) elts || occurs k def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> false

  in check k true t

(* ========================================================================== *)
(*  Phase 2: Owned/borrowed parameter inference                              *)
(* ========================================================================== *)

(* Determine if parameters need ownership (pass by value) or can borrow
   (pass by const ref).

   A parameter needs ownership when:
     - Returned in tail position (caller needs ownership)
     - Stored in constructor (outlives the call)
     - Captured by lambda or fixpoint (outlives the call)

   A parameter can be borrowed when it only appears in:
     - Case scrutinee (destructured immediately)
     - Under MLmagic (transparent wrapper)

   This is identical to escape analysis — a parameter "escapes" when
   the caller needs to pass ownership rather than just lend a reference. *)

let infer_owned_params n_params body =
  List.init n_params (fun i -> escapes (i + 1) body)

(* ========================================================================== *)
(*  Utility functions                                                        *)
(* ========================================================================== *)

module IntSet = Set.Make(Int)

(* Compute free de Bruijn indices in [t], shifted by [depth].
   An index [i > depth] in [t] contributes [i - depth] to the result. *)
let free_rels depth t =
  let free = ref IntSet.empty in
  let rec collect d = function
    | MLrel i when i > d -> free := IntSet.add (i - d) !free
    | MLrel _ -> ()
    | MLcase (_, scrut, branches) ->
        collect d scrut;
        Array.iter (fun (ids, _, _, body) ->
          collect (d + List.length ids) body
        ) branches
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
    | MLcons (_, _, args) | MLtuple args ->
        List.iter (collect d) args
    | MLmagic a -> collect d a
    | MLparray (elts, def) ->
        Array.iter (collect d) elts;
        collect d def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> ()
  in
  collect depth t;
  !free

(* Check if [ty] is a non-enum, non-coinductive inductive
   (wrapped in shared_ptr in C++). Resolves Tmeta chains. *)
let rec is_shared_ptr_type = function
  | Tglob (r, _, _) ->
      (match r with
       | Names.GlobRef.IndRef _ ->
           not (is_enum_inductive r) &&
           not (is_coinductive_type (Tglob (r, [], [])))
       | _ -> false)
  | Tmeta { contents = Some ty } -> is_shared_ptr_type ty
  | _ -> false

(* Analyze [body] to find MLletin bindings safe for unique_ptr.

   Returns list of letin depth indices (0-based) where binding satisfies:
     1. Non-enum, non-coinductive inductive type (shared_ptr candidate)
     2. Not Dummy
     3. RHS is constructor application (not function call)
     4. Occurs ≤ 1 time in continuation (max over branches)
     5. Does not escape in continuation *)
let analyze body =
  let safe = ref [] in

  let rec walk depth = function
    | MLletin (id, ty, rhs, cont) ->
        (* Check if safe for unique_ptr *)
        if id <> Dummy && is_shared_ptr_type ty then begin
          let is_ctor = match rhs with
            | MLcons _ | MLmagic (MLcons _) -> true
            | _ -> false
          in
          if is_ctor && nb_occur_match 1 cont <= 1 && not (escapes 1 cont) then
            safe := depth :: !safe
        end;
        walk_subterm depth rhs;
        walk (depth + 1) cont
    | t -> walk_subterm depth t

  (* Walk subterms without incrementing depth *)
  and walk_subterm depth = function
    | MLletin _ as t -> walk depth t
    | MLcase (_, scrut, branches) ->
        walk_subterm depth scrut;
        Array.iter (fun (_, _, _, body) -> walk_subterm depth body) branches
    | MLlam (_, _, body) -> walk_subterm depth body
    | MLapp (head, args) ->
        walk_subterm depth head;
        List.iter (walk_subterm depth) args
    | MLfix (_, _, bodies, _) ->
        Array.iter (walk_subterm depth) bodies
    | MLcons (_, _, args) | MLtuple args ->
        List.iter (walk_subterm depth) args
    | MLmagic a -> walk_subterm depth a
    | MLparray (elts, def) ->
        Array.iter (walk_subterm depth) elts;
        walk_subterm depth def
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> ()
  in

  walk 0 body;
  List.rev !safe

(* ========================================================================== *)
(*  Phase 3: Reset/reuse optimization                                        *)
(* ========================================================================== *)

(* For case expressions, identify branches where we can reuse the scrutinee's
   memory cell when use_count() == 1 at runtime.

   Reuse is safe when:
     1. Branch tail constructs same inductive type as scrutinee
     2. Constructor arity matches matched pattern arity
     3. Type arguments match exactly (conservative check) *)

(* Extract constructor at tail position, if any *)
let rec tail_constructor = function
  | MLcons (ty, ctor, args) -> Some (ty, ctor, args)
  | MLletin (_, _, _, cont) -> tail_constructor cont
  | MLmagic body -> tail_constructor body
  | _ -> None

(* Check if two types refer to the same inductive with same type arguments *)
let same_inductive t1 t2 =
  match t1, t2 with
  | Tglob (r1, args1, _), Tglob (r2, args2, _) ->
      Names.GlobRef.CanOrd.equal r1 r2 &&
      List.length args1 = List.length args2
  | _ -> false

(* Find branches suitable for memory reuse *)
let find_reuse_candidates scrutinee_type branches =
  Array.to_list (Array.mapi (fun idx (ids, _, pat, body) ->
    match pat with
    | Pusual matched_ctor ->
        let matched_arity = List.length ids in
        (match tail_constructor body with
         | Some (cons_ty, tail_ctor, tail_args)
           when same_inductive scrutinee_type cons_ty &&
                List.length tail_args = matched_arity ->
             Some (idx, matched_ctor, matched_arity, tail_ctor, tail_args)
         | _ -> None)
    | _ -> None
  ) branches)
  |> List.filter_map Fun.id
