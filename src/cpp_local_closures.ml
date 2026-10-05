(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Local closures made and used in one place, rewritten as the code they
    stand for.  See [cpp_local_closures.mli]. *)

open Names
open Minicpp
module IdSet = Id.Set

(** {1 Shared pieces} *)

(* Whether [stmts] can return, other than from a lambda nested in them. *)
let rec has_return stmts =
  let found = ref false in
  let rec fe e =
    match e with
    | CPPlambda _ -> ()
    | _ ->
      iter_expr_children ~on_expr:fe
        ~on_stmts:(fun b -> if has_return b then found := true)
        e
  and fs s =
    match s with
    | Sreturn _ -> found := true
    | _ -> iter_stmt_children ~on_expr:fe ~on_stmts:(List.iter fs) s
  in
  List.iter fs stmts;
  !found

let mentions x stmts = List.exists (Id.equal x) (free_vars_body stmts)

(* Whether evaluating [e] can do nothing but produce its value: a variable, a
   literal, a constructor applied to such things.  A mapped constant is not
   one -- its replacement text may do anything. *)
let rec pure e =
  match e with
  | CPPvar _ | CPPint _ | CPPuint _ | CPPbool _ | CPPfloat _ | CPPstring _
  | CPPenum_val _ | CPPnullptr
  | CPPglob (GlobRef.ConstructRef _, _, _) ->
    true
  | CPPstruct (_, _, args) | CPPstructmk (_, _, args) | CPPstruct_id (_, _, args)
  | CPPbraced args ->
    List.for_all pure args
  | CPPfun_call (_, CPPglob (GlobRef.ConstructRef _, _, _), args) ->
    List.for_all pure (call_args args)
  | CPPbinop (_, a, b) -> pure a && pure b
  | CPPunop (op, a) -> op <> Uaddr && pure a
  | _ -> false

(* A lambda's parameters, an unnamed one named [_argI] -- its argument is
   still evaluated, then never read -- when it has no template parameters. *)
let named_params (l : cpp_lambda) =
  if l.cl_tparams <> [] then None
  else
    Some
      (List.mapi
         (fun i (ty, x) ->
           match x with
           | Some x -> (x, ty)
           | None -> (Id.of_string (Printf.sprintf "_arg%d" i), ty))
         (lambda_params l.cl_params))

(* What [stmts] declare at their own level: the names a splice puts into the
   scope around it.  A name declared deeper -- in a branch, a block, a
   nested lambda -- stays where it was. *)
let declared_here stmts =
  List.concat_map
    (function
      | Sasgn (id, Declare _, _) | Sdecl (id, _) | Sdecl_init (id, _) -> [id]
      | Sbind (ids, _) -> ids
      | Sblock_custom (_, _, id, _, _, _) -> [id]
      | _ -> [])
    stmts

(** A lambda opened up for splicing into the body around it: its parameters
    bound to the arguments and its locals given names nothing else in the
    function has -- [_lc<k>_x], [k] new at every expansion -- so that two
    expansions of one lambda, or one and the code around it, cannot
    collide. *)
type expansion = {
  bindings : cpp_stmt list;  (** the parameters, bound to the arguments *)
  body : cpp_stmt list;  (** the lambda's statements *)
}

let expand fresh (l : cpp_lambda) args =
  match named_params l with
  | Some params when List.length params = List.length args ->
    incr fresh;
    let prefix = Printf.sprintf "_lc%d" !fresh in
    let renamed =
      List.map
        (fun x -> (x, Generated_name.prefixed prefix x))
        (List.map fst params @ declared_here l.cl_body)
    in
    let f x = match List.assoc_opt x renamed with Some y -> y | None -> x in
    (* An unnamed parameter's argument is evaluated for what it does, and a
       pure one does nothing. *)
    let unnamed = List.map (fun (_, x) -> x = None) (lambda_params l.cl_params) in
    let bindings =
      List.concat
        (List.map2
           (fun ((p, ty), unnamed) a ->
             if unnamed && pure a then [] else [Sasgn (f p, Declare ty, a)])
           (List.combine params unnamed)
           args)
    in
    Some {bindings; body = rename_ids f l.cl_body}
  | _ -> None

(* An expansion read as straight-line code that ends by returning [e]: the
   code before, and [e]. *)
let straight_line ex =
  match List.rev ex.body with
  | Sreturn (Some e) :: rev_stmts when not (has_return (List.rev rev_stmts)) ->
    Some (ex.bindings @ List.rev rev_stmts, e)
  | _ -> None

let rec size_stmts l =
  List.fold_left
    (fun n s ->
      fold_stmt_children
        ~on_expr:(fun n e -> n + size_expr e)
        ~on_stmts:(fun n b -> n + size_stmts b)
        (n + 1) s )
    0 l

and size_expr e =
  fold_expr_children
    ~on_expr:(fun n e -> n + size_expr e)
    ~on_stmts:(fun n b -> n + size_stmts b)
    1 e

(* Whether [e] holds a lambda. *)
let rec contains_lambda e =
  match e with
  | CPPlambda _ -> true
  | _ ->
    fold_expr_children
      ~on_expr:(fun acc e -> acc || contains_lambda e)
      ~on_stmts:(fun acc _ -> acc)
      false e

(* How many times [e] reads the variable [x]. *)
let rec occurrences x e =
  let here = match e with CPPvar y when Id.equal x y -> 1 | _ -> 0 in
  fold_expr_children
    ~on_expr:(fun n e -> n + occurrences x e)
    ~on_stmts:(fun n _ -> n)
    here e

(* [e] with each variable [sub] names replaced by its expression. *)
let substitute sub e =
  let rec re e =
    match e with
    | CPPvar x -> ( match List.assoc_opt x sub with Some a -> a | None -> e )
    | _ -> map_expr re rs Fun.id e
  and rs s = map_stmt re rs Fun.id s in
  re e

(** A lambda body larger than this is not duplicated at its calls. *)
let budget = 60

(** {1 Rules} *)

(** R1.  A body ending [auto f = [..](params) { body }; return f(args);] --
    the lambda bound once and called once, as what the enclosing function
    returns -- ends with [{ params = args; body }] instead.  A [return] in
    [body] returns from the function, which is what returning the call's
    result did; a local the lambda returned through a by-reference capture is
    now the function's own, and leaves by an implicit move rather than a copy.
    The lambda must return what the function does. *)
(* Two types that spell the same C++ type: a type variable is the name it
   prints as, however it is indexed; a global is itself under any of its
   kernel names; and the expressions a [Tglob] carries are not printed. *)
let rec same_type a b =
  let all = List.equal same_type in
  match (a, b) with
  | Tvar x, Tvar y -> Id.equal (tvar_spelled x) (tvar_spelled y)
  | Tglob (r, ts, _), Tglob (r', ts', _) -> GlobRef.CanOrd.equal r r' && all ts ts'
  | Tnamespace (r, t), Tnamespace (r', t') -> GlobRef.CanOrd.equal r r' && same_type t t'
  | Tid_external (s, ts), Tid_external (s', ts') -> String.equal s s' && all ts ts'
  | Tid (i, ts), Tid (i', ts') -> Id.equal i i' && all ts ts'
  | Tqualified (t, i), Tqualified (t', i') -> same_type t t' && Id.equal i i'
  | (Tconst t, Tconst t') | (Tshared_ptr t, Tshared_ptr t') | (Tptr t, Tptr t') ->
    same_type t t'
  | Tref (k, t), Tref (k', t') -> k = k' && same_type t t'
  | Tfun (d, c), Tfun (d', c') -> all d d' && same_type c c'
  | Tvariant ts, Tvariant ts' -> all ts ts'
  | _ -> a = b

let inline_tail_call fresh ret_ty stmts =
  match List.rev stmts with
  | Sreturn (Some (CPPfun_call (_, CPPvar f', args))) :: Sasgn (f, Declare Tauto, CPPlambda l)
    :: rev_before
    when Id.equal f f'
         && (match (l.cl_ret, ret_ty) with
             | Some a, Some b -> same_type a b
             | None, _ -> true
             | _ -> false)
         && (not (mentions f l.cl_body))
         (* Called once: not again inside its own arguments. *)
         && not (List.exists (fun a -> mentions f [Sexpr a]) (call_args args)) -> (
    match expand fresh l (call_args args) with
    | Some ex -> List.rev rev_before @ [Sblock (ex.bindings @ ex.body)]
    | None -> stmts )
  | _ -> stmts

(** R2.  [T x = [..]() { stmts; return e; }();] -- a lambda invoked where it
    is written, for its initialiser -- becomes [stmts; T x = e;] when
    [stmts] cannot leave early. *)
let inline_iife_initializers fresh stmts =
  let rec go = function
    | [] -> []
    | (Sasgn (x, Declare t, CPPfun_call (_, CPPlambda l, args)) as s) :: rest
      when to_reversed args = [] && (t <> Tauto || l.cl_ret = None) -> (
      match Option.bind (expand fresh l []) straight_line with
      | Some (body, e) -> go (body @ (Sasgn (x, Declare t, e) :: rest))
      | None -> s :: go rest )
    | s :: rest -> s :: go rest
  in
  go stmts

(** R3.  A local record built from lambdas -- [P p = P{[..](..) {..}, ...};]
    -- whose every later use is a call through one of its fields becomes
    those lambdas' bodies at the calls: each call binds the lambda's
    parameters to its arguments and runs its statements where it stood.  A
    by-copy capture reads the variable it copied, which is the same value
    provided nothing assigns the variable after the record is built; and
    once no call is left the record, a value of pure constructions, is
    dropped.  Only straight-line bodies, under {!budget}, expanded at every
    call or at none. *)

let assigned_vars stmts =
  let acc = ref IdSet.empty in
  let rec fs s =
    ( match s with
    | Sasgn (id, Existing, _) | Sassign_expr (CPPvar id, _) -> acc := IdSet.add id !acc
    | _ -> () );
    iter_stmt_children ~on_expr:fe ~on_stmts:(List.iter fs) s
  and fe e = iter_expr_children ~on_expr:fe ~on_stmts:(List.iter fs) e in
  List.iter fs stmts;
  !acc

let specialize_local_records fresh stmts =
  let rec go = function
    | [] -> []
    | (Sasgn (p, Declare _, CPPstruct (record, _, fields)) as decl) :: rest -> (
      let lambdas = List.map (function CPPlambda l -> Some l | _ -> None) fields in
      (* [CPPstruct] holds the record's non-erased fields, in declaration
         order, so a projection reaches the one at its position among
         those. *)
      let live_fields =
        List.filter_map
          (fun (fr, ty) -> if Mlutil.isTdummy ty then None else Some fr)
          (Table.get_record_field_bindings record)
      in
      let field_lambda r =
        if List.length live_fields <> List.length fields then None
        else
          let rec find = function
            | Some fr :: _, l :: _ when Common.globref_equal fr r -> l
            | _ :: frs, _ :: ls -> find (frs, ls)
            | _ -> None
          in
          find (live_fields, lambdas)
      in
      let call_target e =
        match e with
        | CPPfun_call (_, CPPget' ((CPPvar p' | CPPmove (CPPvar p')), fld, _), args)
          when Id.equal p p' ->
          Option.map (fun l -> (l, call_args args)) (field_lambda fld)
        | _ -> None
      in
      (* Every use of [p] in [rest] is the receiver of such a call. *)
      let only_calls =
        let ok = ref true in
        let rec fe e =
          match call_target e with
          | Some (_, args) -> List.iter fe args
          | None ->
            (match e with CPPvar x when Id.equal x p -> ok := false | _ -> ());
            iter_expr_children ~on_expr:fe ~on_stmts:(List.iter fs) e
        and fs s = iter_stmt_children ~on_expr:fe ~on_stmts:(List.iter fs) s in
        List.iter fs rest;
        !ok
      in
      let lambdas_ok =
        List.for_all
          (function
            | Some l -> size_stmts l.cl_body <= budget && named_params l <> None
            | None -> false)
          lambdas
      in
      let captured =
        List.fold_left
          (fun acc -> function
            | Some l -> IdSet.union acc (IdSet.of_list (free_vars_body l.cl_body))
            | None -> acc)
          IdSet.empty lambdas
      in
      if only_calls && lambdas_ok && IdSet.is_empty (IdSet.inter captured (assigned_vars rest))
      then
        (* A call as an expression, where the lambda is one [return e] and
           every argument may stand in for its parameter: a pure one may be
           duplicated or dropped, any other must replace a parameter read
           exactly once.  A lambda inside [e] could capture what an argument
           names, so it declines. *)
        let as_expr (l : cpp_lambda) args =
          match (named_params l, l.cl_body) with
          | Some params, [Sreturn (Some e)]
            when List.length params = List.length args && not (contains_lambda e) ->
            let reads x = occurrences x e in
            if List.for_all2 (fun (x, _) a -> pure a || reads x = 1) params args then
              Some (substitute (List.combine (List.map fst params) args) e)
            else None
          | _ -> None
        in
        (* The whole statement a call is, expanded into the lambda's
           statements: the shape that cannot be an expression. *)
        let as_stmts e finish =
          match call_target e with
          | Some (l, args) -> (
            match Option.bind (expand fresh l args) straight_line with
            | Some (body, r) -> Some (body @ finish r)
            | None -> None )
          | None -> None
        in
        let exception Decline in
        let rec in_expr e =
          match call_target e with
          | Some (l, args) -> (
            match as_expr l (List.map in_expr args) with
            | Some e' -> e'
            | None -> raise_notrace Decline )
          | None -> map_expr in_expr in_stmt Fun.id e
        and in_stmt s = map_stmt in_expr in_stmt Fun.id s in
        let statement s =
          let whole e finish =
            match call_target e with
            | Some (l, args) when as_expr l args = None -> (
              match as_stmts e finish with Some b -> b | None -> raise_notrace Decline )
            | _ -> [in_stmt s]
          in
          match s with
          | Sexpr e -> whole e (fun r -> if pure r then [] else [Sexpr r])
          | Sasgn (v, tgt, e) -> whole e (fun r -> [Sasgn (v, tgt, r)])
          | _ -> [in_stmt s]
        in
        let rw stmts =
          match List.concat_map statement stmts with
          | stmts' when not (mentions p stmts') -> Some stmts'
          | _ | (exception Decline) -> None
        in
        match rw rest with
        | Some rest' -> go rest'
        | None -> decl :: go rest
      else decl :: go rest )
    | s :: rest -> s :: go rest
  in
  go stmts

(** {1 Entry point} *)

let body ret_ty stmts =
  let fresh = ref 0 in
  stmts
  |> inline_iife_initializers fresh
  |> specialize_local_records fresh
  |> inline_tail_call fresh ret_ty

let rec field (f, vis, tag) =
  let f =
    match f with
    | Fmethod m -> Fmethod {m with mf_body = body (Some m.mf_ret_type) m.mf_body}
    | Fnested_struct (id, fs) -> Fnested_struct (id, List.map field fs)
    | f -> f
  in
  (f, vis, tag)

let rec transform_decl d =
  match d with
  | Dfun ({df_shape = Ddef (ps, stmts); _} as f) ->
    Dfun {f with df_shape = Ddef (ps, body (Some f.df_ret) stmts)}
  | Dtemplate (tps, c, inner) -> Dtemplate (tps, c, transform_decl inner)
  | Dnspace (r, ds) -> Dnspace (r, List.map transform_decl ds)
  | Dstruct s -> Dstruct {s with ds_fields = List.map field s.ds_fields}
  | Dfields s -> Dfields {s with ds_fields = List.map field s.ds_fields}
  | d -> d
