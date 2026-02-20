(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*s Escape analysis for MiniML AST. *)

open Miniml
open Table

(* Count occurrences of [MLrel k] in [t], using max-over-branches
   for match arms (same semantics as mlutil.ml's nb_occur_match). *)
let nb_occur_match =
  let rec nb k = function
    | MLrel i -> if Int.equal i k then 1 else 0
    | MLcase (_, a, v) ->
        (nb k a) +
        Array.fold_left
          (fun r (ids, _, _, a) -> max r (nb (k + (List.length ids)) a)) 0 v
    | MLletin (_, _, a, b) -> (nb k a) + (nb (k + 1) b)
    | MLfix (_, ids, v, _) ->
        let k = k + (Array.length ids) in
        Array.fold_left (fun r a -> r + (nb k a)) 0 v
    | MLlam (_, _, a) -> nb (k + 1) a
    | MLapp (a, l) -> List.fold_left (fun r a -> r + (nb k a)) (nb k a) l
    | MLcons (_, _, l) | MLtuple l ->
        List.fold_left (fun r a -> r + (nb k a)) 0 l
    | MLmagic a -> nb k a
    | MLparray (t, def) ->
        Array.fold_left (fun r a -> r + (nb k a)) 0 t + nb k def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> 0
  in nb

(* Check whether [MLrel k] appears in an escaping position in [t].
   An escaping position is anywhere the value could outlive its scope:
   - As argument to MLcons (stored in a data structure)
   - In body of MLlam (captured by closure)
   - In tail position (returned from function — caller owns the value)
   - As argument to MLapp (passed to unknown function)
   - In MLfix body (captured by recursive closure)

   Safe (non-escaping) positions:
   - Scrutinee of MLcase (destructured immediately)
   - Under MLmagic (transparent wrapper) *)
let escapes k t =
  (* [check k tail t] returns true if MLrel k escapes in t.
     [tail] indicates whether we're in tail position. *)
  let rec check k tail = function
    | MLrel i -> if Int.equal i k then tail else false
    | MLcase (_, scrutinee, branches) ->
        (* Scrutinee is a safe position — the value is destructured.
           But if the variable appears in a branch, that could escape. *)
        let scrut_escapes = match scrutinee with
          | MLrel i when Int.equal i k -> false  (* safe: scrutinee position *)
          | _ -> check k false scrutinee  (* recurse into complex scrutinees *)
        in
        scrut_escapes ||
        Array.exists (fun (ids, _, _, body) ->
          check (k + List.length ids) tail body
        ) branches
    | MLletin (_, _, rhs, body) ->
        check k false rhs || check (k + 1) tail body
    | MLlam (_, _, body) ->
        (* Anything referenced inside a lambda escapes (captured by closure) *)
        has_occurrence (k + 1) body
    | MLapp (head, args) ->
        (* Arguments to function calls escape (passed to unknown code).
           The head position is also escaping (could be stored/returned). *)
        check k true head ||
        List.exists (has_occurrence k) args
    | MLfix (_, ids, bodies, _) ->
        (* Anything referenced inside fix bodies escapes (captured) *)
        let k' = k + Array.length ids in
        Array.exists (has_occurrence k') bodies
    | MLcons (_, _, args) ->
        (* Arguments to constructors escape (stored in data structure) *)
        List.exists (has_occurrence k) args
    | MLtuple args ->
        List.exists (has_occurrence k) args
    | MLmagic a -> check k tail a
    | MLparray (elts, def) ->
        Array.exists (has_occurrence k) elts || has_occurrence k def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> false

  (* Simple occurrence check — does MLrel k appear anywhere in t? *)
  and has_occurrence k = function
    | MLrel i -> Int.equal i k
    | MLcase (_, a, v) ->
        has_occurrence k a ||
        Array.exists (fun (ids, _, _, body) ->
          has_occurrence (k + List.length ids) body) v
    | MLletin (_, _, a, b) ->
        has_occurrence k a || has_occurrence (k + 1) b
    | MLlam (_, _, a) -> has_occurrence (k + 1) a
    | MLapp (a, l) ->
        has_occurrence k a || List.exists (has_occurrence k) l
    | MLfix (_, ids, v, _) ->
        let k' = k + Array.length ids in
        Array.exists (has_occurrence k') v
    | MLcons (_, _, l) | MLtuple l ->
        List.exists (has_occurrence k) l
    | MLmagic a -> has_occurrence k a
    | MLparray (t, def) ->
        Array.exists (has_occurrence k) t || has_occurrence k def
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> false

  in check k true t

(* Check if an ml_type corresponds to a non-enum, non-coinductive inductive
   that would normally be wrapped in shared_ptr. Resolves Tmeta chains. *)
let rec is_shared_ptr_type = function
  | Tglob (r, _, _) ->
      (match r with
       | Names.GlobRef.IndRef _ ->
           not (is_enum_inductive r) && not (is_coinductive_type (Tglob (r, [], [])))
       | _ -> false)
  | Tmeta { contents = Some t } -> is_shared_ptr_type t
  | _ -> false

(* Analyze [body] and return the list of MLletin depth indices (0-based)
   that are safe for unique_ptr.

   We walk the AST, tracking the current letin depth. For each MLletin
   binding, we check:
   1. Type is a shared_ptr candidate (non-enum, non-coinductive inductive)
   2. Identifier is not Dummy
   3. Variable occurs at most once in continuation (max-over-branches)
   4. Variable does not escape in continuation *)
let analyze body =
  let safe = ref [] in
  let rec walk depth = function
    | MLletin (id, ty, _rhs, cont) ->
        (* Check if this binding is a unique_ptr candidate.
           The RHS must be a constructor application (MLcons) — function calls
           return shared_ptr and cannot be rewritten to unique_ptr. *)
        let is_not_dummy = id <> Dummy in
        let is_sptr_ty = is_shared_ptr_type ty in
        let is_ctor_rhs = match _rhs with MLcons _ -> true | MLmagic (MLcons _) -> true | _ -> false in
        if is_not_dummy && is_sptr_ty && is_ctor_rhs then begin
          let occ = nb_occur_match 1 cont in
          let esc = escapes 1 cont in
          if occ <= 1 && not esc then
            safe := depth :: !safe
        end;
        (* Recurse into rhs and continuation.
           rhs is at same depth; continuation increments depth for next letin. *)
        walk_inner depth _rhs;
        walk (depth + 1) cont
    | other -> walk_inner depth other

  (* Walk into subterms without incrementing letin depth
     (only MLletin increments it) *)
  and walk_inner depth = function
    | MLletin _ as t -> walk depth t
    | MLcase (_, a, v) ->
        walk_inner depth a;
        Array.iter (fun (_, _, _, body) -> walk_inner depth body) v
    | MLlam (_, _, a) -> walk_inner depth a
    | MLapp (a, l) -> walk_inner depth a; List.iter (walk_inner depth) l
    | MLfix (_, _, v, _) -> Array.iter (walk_inner depth) v
    | MLcons (_, _, l) | MLtuple l -> List.iter (walk_inner depth) l
    | MLmagic a -> walk_inner depth a
    | MLparray (t, def) ->
        Array.iter (walk_inner depth) t; walk_inner depth def
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _
    | MLuint _ | MLfloat _ | MLstring _ -> ()
  in
  walk 0 body;
  List.rev !safe
