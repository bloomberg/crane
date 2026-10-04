(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Turn a local's last read into a move.  See [last_use.mli]. *)

open Names
open Minicpp
module IdSet = Id.Set
module IdMap = Id.Map

(** {1 Reading a term} *)

(** What one read of a variable reads: all of it, or one member -- a field of
    a struct value, or a member of a pair read through its projection
    mapping.  Two reads of different members of one local are independent,
    which is what lets each of them move. *)
type place = Whole | Field of string

(* The variable and member a member read reads. *)
let member_read = function
  | CPPaccess (Adot, CPPvar x, f) | CPPget (CPPvar x, f) -> Some (x, Id.to_string f)
  | CPPfun_call
      ( _,
        CPPglob
          (_, _, Some {ci_inline = Some {it_shape = Inline_pair_projection f; _}; _}),
        {rev = [CPPvar x]} ) ->
    Some (x, f)
  | _ -> None

let note occ id p = IdMap.add id (p :: (try IdMap.find id occ with Not_found -> [])) occ

(* [fold_expr_children] and [fold_stmt_children] descend one level, so these
   three are the whole traversal: a variable is noted wherever it is named,
   a lambda body and a branch body included. *)
let rec occ_expr occ e =
  match member_read e with
  | Some (x, f) -> note occ x (Field f)
  | None ->
    let occ = match e with CPPvar id -> note occ id Whole | _ -> occ in
    fold_expr_children ~on_expr:occ_expr ~on_stmts:occ_stmts occ e

and occ_stmts occ l = List.fold_left occ_stmt occ l

and occ_stmt occ s =
  fold_stmt_children ~on_expr:occ_expr ~on_stmts:occ_stmts occ s

let named occ =
  IdMap.fold (fun id _ acc -> IdSet.add id acc) occ IdSet.empty

let reads_expr e = named (occ_expr IdMap.empty e)
let reads_stmts l = named (occ_stmts IdMap.empty l)

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
  | Sbind (ids, e) ->
    (* References into whatever [e] names. *)
    ban scope e;
    List.iter (bind_other scope) ids
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
    | Sbind (ids, _) -> List.iter note ids
    | _ -> () );
    iter_stmt_children ~on_expr:fe ~on_stmts:fl s
  in
  fl stmts;
  !found

(** {1 The backward walk} *)

(** How a term's reads of a variable that is dead after it give up its value:
    its one read moves all of it, or each of its reads moves a different
    member. *)
type transfer = Move_whole | Move_fields

(** The reads of [term] that may become moves, given that [live] is read
    afterwards.  A variable read twice in the same term is not one of them --
    C++ leaves the order of a call's arguments unspecified, so the other read
    may happen second -- unless every read is of a different member, which a
    move of another member leaves alone. *)
let transfers scope live occ =
  IdMap.fold
    (fun id places acc ->
      if
        IdSet.mem id scope.cands
        && (not (IdSet.mem id scope.banned))
        && not (IdSet.mem id live)
      then
        let fields =
          List.filter_map (function Field f -> Some f | Whole -> None) places
        in
        match places with
        | [Whole] -> IdMap.add id Move_whole acc
        | _
          when List.length fields = List.length places
               && List.length (List.sort_uniq String.compare fields)
                  = List.length fields ->
          IdMap.add id Move_fields acc
        | _ -> acc
      else
        acc )
    occ
    IdMap.empty

let rec move_reads moved e =
  let transfer x = IdMap.find_opt x moved in
  match e with
  (* Already a move: an earlier pass got there first, and [std::move] twice
     over reads no better than once. *)
  | CPPmove (CPPvar _) -> e
  | _ when (match member_read e with
            | Some (x, _) -> transfer x = Some Move_fields
            | None -> false) ->
    ( match e with
    | CPPaccess (a, (CPPvar _ as v), f) -> CPPaccess (a, CPPmove v, f)
    | CPPget ((CPPvar _ as v), f) -> CPPget (CPPmove v, f)
    | CPPfun_call (s, g, {rev = [(CPPvar _ as v)]}) ->
      CPPfun_call (s, g, of_reversed [CPPmove v])
    | _ -> e )
  | CPPvar id when transfer id = Some Move_whole -> CPPmove e
  (* A template that may splice an argument twice would evaluate a move
     written into it twice. *)
  | CPPfun_call (_, CPPglob (_, _, Some {ci_inline = Some {it_linear = false; _}; _}), _) ->
    e
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
  let occ = occ_expr IdMap.empty e in
  let moved = transfers scope live occ in
  ( (if IdMap.is_empty moved then e else move_reads moved e),
    IdSet.union live (named occ) )

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
        (fun acc b -> List.fold_left occ_expr acc b.smb_extra_conds)
        (occ_expr IdMap.empty scrut.sc_expr)
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
    (s, IdSet.union live (named (occ_stmt IdMap.empty s)))
  | _ ->
    (* Everything left holds expressions and no statements, so its reads all
       happen here, in an order C++ does not promise. *)
    let occ = occ_stmt IdMap.empty s in
    let moved = transfers scope live occ in
    ( (if IdMap.is_empty moved then s else move_reads_stmt moved s),
      IdSet.union live (named occ) )

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
