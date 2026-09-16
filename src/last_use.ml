(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Turn a local's last read into a move.  See [last_use.mli]. *)

open Names
open Minicpp
module IdSet = Id.Set
module IdMap = Id.Map

(** {1 Reading a term} *)

let bump counts id =
  IdMap.add id (1 + (try IdMap.find id counts with Not_found -> 0)) counts

(* [fold_expr_children] and [fold_stmt_children] descend one level, so these
   three are the whole traversal: a variable is counted wherever it is named,
   a lambda body and a branch body included. *)
let rec count_expr counts e =
  let counts = match e with CPPvar id -> bump counts id | _ -> counts in
  fold_expr_children ~on_expr:count_expr ~on_stmts:count_stmts counts e

and count_stmts counts l = List.fold_left count_stmt counts l

and count_stmt counts s =
  fold_stmt_children ~on_expr:count_expr ~on_stmts:count_stmts counts s

let named counts =
  IdMap.fold (fun id _ acc -> IdSet.add id acc) counts IdSet.empty

let reads_expr e = named (count_expr IdMap.empty e)
let reads_stmts l = named (count_stmts IdMap.empty l)

(** {1 Which variables may be moved from at all} *)

(* A [const T] or a [const T &] is not a variable this pass owns: moving from
   the first is silently a copy, and the second names something the caller
   still holds. *)
let rec is_borrowed = function
  | Tref _ | Tconst _ -> true
  | Tnamespace (_, t) -> is_borrowed t
  | _ -> false

(* [Tauto] is by value -- [auto] never deduces a reference -- and is how most
   of translation's temporaries are declared, so it is worth moving even
   though its eventual type is not written down here. *)
let movable ty =
  (not (is_borrowed ty)) && (ty = Tauto || Loopify.worthwhile_move_type ty)

(** What one function body offers the liveness walk: the variables it declares
    by value, the ones it must not touch, and whether it can be analysed at
    all. *)
type scope = {
  mutable cands : IdSet.t;
  mutable banned : IdSet.t;
  mutable opaque : bool;
      (** Raw C++ is in the body, so a read may be hiding in a string. *)
}

let ban scope e = scope.banned <- IdSet.union scope.banned (reads_expr e)

(** A name bound by something other than a by-value declaration -- a structured
    binding into a match, a loop variable, a lambda parameter.

    The walk works on whole function bodies rather than on C++ blocks, so two
    sibling branches that both call their binding [a2] are one name to it.  If
    either of them binds a reference, moving from the other would move through
    it, so a name that is ever bound this way is out. *)
let bind_other scope id = scope.banned <- IdSet.add id scope.banned

let bind_other_opt scope = function
  | Some id -> bind_other scope id
  | None -> ()

(* Every construct that gives a value a second name the liveness walk does not
   follow, or that may emit one expression twice. *)
let rec scan_expr scope e =
  ( match e with
  | CPPraw _ -> scope.opaque <- true
  | CPPlambda l ->
    (* Deferred execution: the read happens when the lambda runs, which is
       not where it is written. *)
    ban scope e;
    List.iter (fun (_, id) -> bind_other_opt scope id) (lambda_params l.cl_params)
  | CPPunop (Uaddr, a) -> ban scope a
  | CPPfun_call (_, CPPglob (_, _, Some {ci_inline = Some _; _}), args) ->
    (* An inline custom is a template string, and a template string may
       mention the same argument twice. *)
    List.iter (ban scope) (to_reversed args)
  | _ -> () );
  iter_expr_children ~on_expr:(scan_expr scope) ~on_stmts:(scan_stmts scope) e

and scan_stmts scope l = List.iter (scan_stmt scope) l

and scan_stmt scope s =
  ( match s with
  | Sraw _ -> scope.opaque <- true
  | Sasgn (id, Declare ty, rhs) ->
    if is_borrowed ty then (
      (* [const auto &x = e] binds a reference into whatever [e] names. *)
      ban scope rhs;
      bind_other scope id )
    else if movable ty then
      scope.cands <- IdSet.add id scope.cands
  | Sdecl (id, ty) | Sdecl_init (id, ty) ->
    if movable ty then scope.cands <- IdSet.add id scope.cands
  | Sif_decl (id, ty, cond, _, _) ->
    if is_borrowed ty then (
      ban scope cond;
      bind_other scope id )
  | Sfor_range (id, _, _) -> bind_other scope id
  | Smatch (scrut, branches, _) ->
    (* The branches bind structured references into the scrutinee. *)
    ban scope scrut.sc_expr;
    List.iter
      (fun b ->
        bind_other_opt scope b.smb_var;
        List.iter (fun (id, _, _) -> bind_other scope id) b.smb_field_bindings )
      branches
  | Scustom_case (_, scrut, _, branches, _) ->
    ban scope scrut;
    List.iter
      (fun (ps, _, _) -> List.iter (fun (id, _) -> bind_other scope id) ps)
      branches
  | Sblock_custom (_, _, _, _, args, _) -> List.iter (ban scope) args
  | _ -> () );
  iter_stmt_children ~on_expr:(scan_expr scope) ~on_stmts:(scan_stmts scope) s

let declared_in stmts =
  let found = ref IdSet.empty in
  let note id = found := IdSet.add id !found in
  let rec fe e =
    iter_expr_children ~on_expr:fe ~on_stmts:fl e
  and fl l = List.iter fs l
  and fs s =
    ( match s with
    | Sasgn (id, Declare _, _) | Sdecl (id, _) | Sdecl_init (id, _) -> note id
    | _ -> () );
    iter_stmt_children ~on_expr:fe ~on_stmts:fl s
  in
  fl stmts;
  !found

(** {1 The backward walk} *)

(** The reads of [term] that may become moves, given that [live] is read
    afterwards.  A variable read twice in the same term is not one of them:
    C++ leaves the order of a call's arguments unspecified, so the other read
    may happen second. *)
let movable_reads scope live counts =
  IdMap.fold
    (fun id n acc ->
      if
        n = 1
        && IdSet.mem id scope.cands
        && (not (IdSet.mem id scope.banned))
        && not (IdSet.mem id live)
      then
        IdSet.add id acc
      else
        acc )
    counts
    IdSet.empty

let rec move_reads moved e =
  match e with
  (* Already a move: an earlier pass got there first, and [std::move] twice
     over reads no better than once. *)
  | CPPmove (CPPvar _) -> e
  | CPPvar id when IdSet.mem id moved -> CPPmove e
  | CPPfun_call (s, callee, args) ->
    (* The callee is how the function is reached, not a value handed to it.
       Moving it buys nothing -- [std::move(f)(x)] still calls [f] -- and
       moving the object a method is called on is worse than nothing, because
       an rvalue [std::move(v).length()] may pick a different overload from
       the one the code was written against.  A methodified callee keeps its
       receiver among the arguments, at the position the printer will lift
       out in front of the [.], so that argument is a callee too. *)
    let receiver =
      match callee with
      | CPPglob (r, _, _) -> Cpp_names.lookup_method_this_pos r
      | _ -> None
    in
    let arg i a = if Some i = receiver then a else move_reads moved a in
    CPPfun_call (s, callee, of_reversed (List.rev (List.mapi arg (call_args args))))
  | _ -> map_expr (move_reads moved) (move_reads_stmt moved) Fun.id e

and move_reads_stmt moved s =
  map_stmt (move_reads moved) (move_reads_stmt moved) Fun.id s

(** [walk scope live stmts] rewrites [stmts] back to front, [live] being what
    is read after them, and answers with what is read from their start. *)
let rec walk scope live stmts =
  List.fold_right
    (fun s (rest, live) ->
      let s, live = walk_stmt scope live s in
      (s :: rest, live) )
    stmts
    ([], live)

(** The branches of a conditional are alternatives: each is walked against the
    same [live], and what reaches the branch point is their union.  Takes and
    returns the bodies alone, so that a caller can put each back where its own
    branch representation keeps it. *)
and walk_alts scope live bodies =
  List.fold_right
    (fun body (rest, live') ->
      let body, l = walk scope live body in
      (body :: rest, IdSet.union live' l) )
    bodies
    ([], live)

(** An expression evaluated at this point, with [live] read after it. *)
and walk_expr scope live e =
  let counts = count_expr IdMap.empty e in
  let moved = movable_reads scope live counts in
  ( (if IdSet.is_empty moved then e else move_reads moved e),
    IdSet.union live (named counts) )

(** A loop body runs again, so everything the loop reads is live at the end of
    every iteration -- except what the body itself declares, which is a fresh
    variable each time round. *)
and walk_loop scope live ~extra body =
  let repeated = IdSet.diff (IdSet.union extra (reads_stmts body)) (declared_in body) in
  let body, _ = walk scope (IdSet.union live repeated) body in
  (body, IdSet.union live repeated)

and walk_stmt scope live s =
  match s with
  | Sif (c, t, e) ->
    let (t, e), live = two_alts scope live t e in
    let c, live = walk_expr scope live c in
    (Sif (c, t, e), live)
  | Sif_constexpr (c, t, e) ->
    let (t, e), live = two_alts scope live t e in
    let c, live = walk_expr scope live c in
    (Sif_constexpr (c, t, e), live)
  | Sif_decl (id, ty, c, t, e) ->
    let (t, e), live = two_alts scope live t e in
    let c, live = walk_expr scope live c in
    (Sif_decl (id, ty, c, t, e), live)
  | Sblock body ->
    let body, live = walk scope live body in
    (Sblock body, live)
  | Swhile (c, body) ->
    let body, live = walk_loop scope live ~extra:(reads_expr c) body in
    (Swhile (c, body), live)
  | Sfor_range (id, e, body) ->
    let body, live = walk_loop scope live ~extra:IdSet.empty body in
    let e, live = walk_expr scope live e in
    (Sfor_range (id, e, body), live)
  | Sswitch (e, r, branches, dflt) ->
    let bodies, live = walk_alts scope live (List.map snd branches) in
    let branches = List.map2 (fun (c, _) body -> (c, body)) branches bodies in
    let dflt, live =
      match dflt with
      | None -> (None, live)
      | Some body ->
        let body, l = walk scope live body in
        (Some body, IdSet.union live l)
    in
    let e, live = walk_expr scope live e in
    (Sswitch (e, r, branches, dflt), live)
  | Smatch (scrut, branches, els) ->
    let bodies, live = walk_alts scope live (List.map (fun b -> b.smb_body) branches) in
    let branches = List.map2 (fun b body -> {b with smb_body = body}) branches bodies in
    let els, live =
      match els with
      | None -> (None, live)
      | Some body ->
        let body, l = walk scope live body in
        (Some body, IdSet.union live l)
    in
    (* The scrutinee and the branch conditions are read before any branch
       body, and a later branch's condition runs only if an earlier one fails.
       Neither is rewritten: the scrutinee is banned outright, and a condition
       is not a place where a conditional read may become a move. *)
    let before =
      List.fold_left
        (fun acc b -> List.fold_left count_expr acc b.smb_extra_conds)
        (count_expr IdMap.empty scrut.sc_expr)
        branches
    in
    (Smatch (scrut, branches, els), IdSet.union live (named before))
  | Scustom_case (ty, scrut, tys, branches, tmpl) ->
    let bodies, live =
      walk_alts scope live (List.map (fun (_, _, body) -> body) branches)
    in
    let branches =
      List.map2 (fun (ps, rty, _) body -> (ps, rty, body)) branches bodies
    in
    ( Scustom_case (ty, scrut, tys, branches, tmpl),
      IdSet.union live (reads_expr scrut) )
  | Sreturn (Some (CPPvar _)) ->
    (* C++ moves a returned local or by-value parameter on its own, and
       writing the move here would suppress the copy elision that is better
       still. *)
    (s, IdSet.union live (named (count_stmt IdMap.empty s)))
  | _ ->
    (* Everything left holds expressions and no statements, so its reads all
       happen here, in an order C++ does not promise. *)
    let counts = count_stmt IdMap.empty s in
    let moved = movable_reads scope live counts in
    ( (if IdSet.is_empty moved then s else move_reads_stmt moved s),
      IdSet.union live (named counts) )

and two_alts scope live t e =
  let t, lt = walk scope live t in
  let e, le = walk scope live e in
  ((t, e), IdSet.union lt le)

(** {1 Entry points} *)

let body params body =
  let scope = {cands = IdSet.empty; banned = IdSet.empty; opaque = false} in
  List.iter
    (fun (id, ty) -> if movable ty then scope.cands <- IdSet.add id scope.cands)
    params;
  scan_stmts scope body;
  if scope.opaque || IdSet.is_empty scope.cands then
    body
  else
    fst (walk scope IdSet.empty body)

let rec field (f, vis, tag) =
  let f =
    match f with
    | Fmethod m -> Fmethod {m with mf_body = body m.mf_params m.mf_body}
    | Fdestructor stmts -> Fdestructor (body [] stmts)
    | Fnested_struct (id, fs) -> Fnested_struct (id, List.map field fs)
    | f -> f
  in
  (f, vis, tag)

let rec transform_decl d =
  match d with
  | Dfun ({df_shape = Ddef (ps, stmts); _} as f) ->
    Dfun {f with df_shape = Ddef (ps, body ps stmts)}
  | Dtemplate (tps, c, inner) -> Dtemplate (tps, c, transform_decl inner)
  | Dnspace (r, ds) -> Dnspace (r, List.map transform_decl ds)
  | Dstruct s -> Dstruct {s with ds_fields = List.map field s.ds_fields}
  | Dfields s -> Dfields {s with ds_fields = List.map field s.ds_fields}
  | d -> d
