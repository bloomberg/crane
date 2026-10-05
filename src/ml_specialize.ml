(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A recursive function specialized to the lambda a definition passes it.
    See [ml_specialize.mli]. *)

open Names
open Miniml

let same = GlobRef.CanOrd.equal

(** {1 Definitions} *)

type def = Term of ml_ast * ml_type | Fix of ml_fix_def

let definitions struc =
  let defs = ref Table.Refmap'.empty in
  let add r d = defs := Table.Refmap'.add r d !defs in
  let rec elems l =
    List.iter
      (fun (_, se) ->
        match se with
        | SEdecl (Dterm (r, b, ty)) -> add r (Term (b, ty))
        | SEdecl (Dfix [fd]) -> add fd.fd_ref (Fix fd)
        | SEmodule {ml_mod_expr = MEstruct (_, l); _} -> elems l
        | _ -> ())
      l
  in
  List.iter (fun (_, l) -> elems l) struc;
  !defs

(* The body of a global this pass may unfold, at the type arguments [tys]
   of the use: its annotations name the definition's own type variables,
   which mean something else where the body lands.  [None] for a mapped
   global, whose text is what is emitted, and where [tys] does not give
   every variable its type mentions. *)
let body_of defs g tys =
  if Table.is_custom g then None
  else
    let at body ty =
      if Mlutil.type_maxvar ty = 0 then Some body
      else if Mlutil.type_maxvar ty <= List.length tys then
        Some (Mlutil.ast_map_types (Mlutil.type_subst_list tys) body)
      else None
    in
    match Table.Refmap'.find_opt g defs with
    | Some (Term (b, ty)) -> at b ty
    | Some (Fix fd) -> at fd.fd_body fd.fd_type
    | None -> None

(** {1 Terms} *)

(* Every node counted once. *)
let rec size e =
  1
  +
  match e with
  | MLapp (f, a) -> size f + sizes a
  | MLlam (_, _, b) | MLmagic (_, b) -> size b
  | MLletin (_, _, a, b) -> size a + size b
  | MLcons (_, _, a) | MLtuple a -> sizes a
  | MLcase (_, s, brs) -> Array.fold_left (fun n (_, _, _, b) -> n + size b) (size s) brs
  | MLfix (_, _, bs, _) -> Array.fold_left (fun n b -> n + size b) 0 bs
  | _ -> 0

and sizes l = List.fold_left (fun n a -> n + size a) 0 l

(* A term whose evaluation computes nothing, and so may be duplicated or
   dropped. *)
let rec is_value = function
  | MLrel _ | MLglob _ | MLlam _ | MLuint _ | MLfloat _ | MLstring _ | MLdummy _ -> true
  | MLcons (_, _, a) | MLtuple a -> List.for_all is_value a
  | MLmagic (_, a) -> is_value a
  | _ -> false

(* [b] applied to [args], its leading lambdas instantiated: a value
   argument is substituted, any other is bound once by a [let] where its
   parameter is read more than once.  Arguments past [b]'s lambdas stay
   applied; [None] if there are fewer arguments than lambdas. *)
let instantiate b args =
  let params, body = Mlutil.collect_lams b in
  let n = List.length params in
  if List.length args < n then None
  else
    let now = List.filteri (fun i _ -> i < n) args
    and later = List.filteri (fun i _ -> i >= n) args in
    (* Outermost parameter first: [now] in order, [params] innermost first. *)
    let rec go body i = function
      | [] -> body
      | (a, (id, ty)) :: rest ->
        (* [a] lives outside every lambda; here it is under the [n - i - 1]
           still bound outside the one being instantiated. *)
        let a = Mlutil.ast_lift (n - i - 1) a in
        let body' =
          if is_value a || Mlutil.nb_occur_match body <= 1 then Mlutil.ast_subst a body
          else MLletin (id, ty, a, body)
        in
        go body' (i + 1) rest
    in
    (* Instantiate the innermost first, so each step substitutes [MLrel 1]. *)
    let pairs = List.rev (List.combine now (List.rev params)) in
    let body = go body 0 pairs in
    Some (if later = [] then body else MLapp (body, later))

(* What a known-constructor argument is: a constructor, or a call to a
   definition whose body is one. *)
let known_ctor defs e =
  match e with
  | MLcons _ -> Some e
  | MLapp (MLglob (g, tys), args) -> (
    match body_of defs g tys with
    | Some b -> (
      match (snd (Mlutil.collect_lams b), instantiate b args) with
      | MLcons _, Some e' -> Some (Mlutil.normalize e')
      | _ -> None )
    | None -> None )
  | MLglob (g, tys) -> (
    match body_of defs g tys with Some (MLcons _ as c) -> Some c | _ -> None )
  | _ -> None

(* [e] with each [let] of a value read at most once substituted: a
   constructor bound by a beta-reduction is then matched where it is used. *)
let rec subst_value_lets e =
  match Mlutil.ast_map subst_value_lets e with
  | MLletin (_, _, c, b) when is_value c && Mlutil.nb_occur_match b <= 1 ->
    Mlutil.ast_subst c b
  | e -> e

(** {1 Rewrites} *)

(** Unfolds allowed below one rewrite: a bound on compile-time work, not on
    what is profitable, which the size test decides. *)
let fuel = 16

(* [e] with its calls unfolded where an argument is a known constructor, and
   pushed into a match argument where that lets a branch unfold.  [shrunk]
   is set when anything is rewritten. *)
let rec reduce defs shrunk fuel e =
  let e = Mlutil.ast_map (reduce defs shrunk fuel) e in
  match e with
  | MLapp (MLglob (g, tys), args) when fuel > 0 -> (
    match unfold defs shrunk fuel g tys args with
    | Some e' -> e'
    | None -> Option.default e (push defs shrunk fuel g tys args) )
  | _ -> e

and unfold defs shrunk fuel g tys args =
  let known = List.map (known_ctor defs) args in
  if List.for_all Option.is_empty known then None
  else
    match body_of defs g tys with
    | None -> None
    | Some b -> (
      let args' = List.map2 (fun a k -> Option.default a k) args known in
      match instantiate b args' with
      | None -> None
      | Some e ->
        let e' = settle defs (fuel - 1) e in
        if size e' < size (MLapp (MLglob (g, []), args)) then (
          shrunk := true;
          Some e' )
        else None )

(* [e] normalized and reduced until neither changes it: an unfolding below
   exposes a match on a constructor, or a lambda applied, for the next
   normalization; within [fuel] rounds. *)
and settle defs fuel e =
  let rec go n e =
    let changed = ref false in
    let simplify e = Mlutil.normalize (subst_value_lets e) in
    let e' = simplify (reduce defs changed fuel (simplify e)) in
    if !changed && n > 0 then go (n - 1) e' else e'
  in
  go fuel e

and push defs shrunk fuel g tys args =
  let rec split before = function
    | (MLcase (ty, s, brs) as m) :: after
      when List.for_all is_value before && List.for_all is_value after ->
      ignore m;
      Some (List.rev before, ty, s, brs, after)
    | a :: after -> split (a :: before) after
    | [] -> None
  in
  match split [] args with
  | None -> None
  | Some (before, ty, s, brs, after) ->
    let any = ref false in
    let brs' =
      Array.map
        (fun (ids, bty, p, b) ->
          let k = List.length ids in
          let lift = List.map (Mlutil.ast_lift k) in
          let call = MLapp (MLglob (g, tys), lift before @ [b] @ lift after) in
          let call' = settle defs fuel call in
          if size call' < size call then (
            any := true;
            (ids, bty, p, call') )
          else
            (* Unreduced, the branch's value is still what it was -- the
               result of a match, typed by the branch -- and is passed by
               name, so it keeps that type rather than taking one from the
               parameter it now meets. *)
            let lift1 = List.map (Mlutil.ast_lift (k + 1)) in
            ( ids, bty, p,
              MLletin
                ( Id (Id.of_string "step"), bty, b,
                  MLapp (MLglob (g, tys), lift1 before @ [MLrel 1] @ lift1 after) ) ) )
        brs
    in
    if !any then (
      shrunk := true;
      Some (MLcase (ty, s, brs')) )
    else None

(** {1 Specialization} *)

(* The parameters of [fd], outermost first, and its body under them. *)
let params_of fd =
  let ps, body = Mlutil.collect_lams fd.fd_body in
  (List.rev ps, body)

(* Whether every occurrence of [f] in its body [b], under its [k] parameters,
   is a call passing parameter [j] (outermost first) unchanged. *)
let static_param f k j b =
  let exception No in
  let rec walk d e =
    match e with
    | MLapp (MLglob (g, _), a) when same g f ->
      ( match List.nth_opt a j with
      | Some (MLrel i) when i = k - j + d -> ()
      | _ -> raise_notrace No );
      List.iter (walk d) a
    | MLglob (g, _) when same g f -> raise_notrace No
    | _ -> ignore (Mlutil.ast_map_lift (fun d e -> walk d e; e) d e)
  in
  try walk 0 b; true with No -> false

(* [ty]'s arrow at position [j] dropped, and its domains, outermost first. *)
let rec drop_domain j ty =
  match (j, Mlutil.ml_resolve ty) with
  | 0, Tarr (_, c) -> Some c
  | j, Tarr (d, c) -> Option.map (fun c -> Tarr (d, c)) (drop_domain (j - 1) c)
  | _ -> None

let rec domains n ty =
  if n = 0 then Some []
  else
    match Mlutil.ml_resolve ty with
    | Tarr (d, c) -> Option.map (fun ds -> d :: ds) (domains (n - 1) c)
    | _ -> None

(** [specialize f fd tys args] is the call [f args] (at type arguments
    [tys]) with [f] specialized to the lambda among [args] that it passes
    unchanged to itself: a local fixpoint applied to the other arguments. *)
let specialize f fd tys args =
  let ps, b0 = params_of fd in
  let k = List.length ps in
  let candidate j a = j < k && (match a with MLlam _ -> true | _ -> false) && static_param f k j b0 in
  match List.find_opt (fun (j, a) -> candidate j a) (List.mapi (fun j a -> (j, a)) args) with
  | None -> None
  | Some (j, lam) -> (
    if Mlutil.type_maxvar fd.fd_type > List.length tys then None
    else
      let inst = Mlutil.type_subst_list tys in
      let fty = inst fd.fd_type in
      match (drop_domain j fty, domains k fty) with
      | Some spec_ty, Some doms ->
        (* The recursive calls, on the parameters' own [b_rec] placed under
           the [k - 1] remaining parameters and the fixpoint's binder. *)
        let rec self d e =
          match e with
          | MLapp (MLglob (g, _), a) when same g f ->
            let a = List.map (self d) a in
            MLapp (MLrel (d + k), List.filteri (fun i _ -> i <> j) a)
          | _ -> Mlutil.ast_map_lift self d e
        in
        let b_rec = Mlutil.ast_map_types inst (self 0 fd.fd_body) in
        let q i = MLrel (k - 1 - i) in
        let args_b =
          List.init k (fun i ->
              if i < j then q i else if i = j then Mlutil.ast_lift k lam else q (i - 1))
        in
        let qs =
          List.rev
            (List.filteri (fun i _ -> i <> j)
               (List.map2 (fun (id, _) d -> (id, d)) ps doms))
        in
        let fid = Label.to_id (Common.label_of_r f) in
        let fix =
          (* [b_rec] has exactly [k] lambdas, and the lambda among [args_b]
             is a value, so it is substituted for its parameter. *)
          let body = Option.get (instantiate b_rec args_b) in
          MLfix (0, [|(fid, spec_ty)|], [|Mlutil.named_lams qs body|], false)
        in
        let rest = List.filteri (fun i _ -> i <> j) args in
        Some (if rest = [] then fix else MLapp (fix, rest))
      | _ -> None )

(** The declaration [r := body] with its call specialized and simplified,
    when that shrinks it. *)
let decl defs r body ty =
  let ps, inner = Mlutil.collect_lams body in
  match inner with
  | MLapp (MLglob (f, tys), args) when not (Table.is_custom r) -> (
    match Table.Refmap'.find_opt f defs with
    | Some (Fix fd) when not (Table.is_custom f) -> (
      match specialize f fd tys args with
      | None -> None
      | Some spec ->
        let shrunk = ref false in
        let spec = reduce defs shrunk fuel (Mlutil.normalize spec) in
        (* Only as the definition's own fixpoint: a fixpoint left local is
           translated without the whole-body suspension a corecursive one
           calling itself outside its constructors needs. *)
        if not !shrunk then None
        else
          match Modutil.decl_of_term r (Mlutil.named_lams ps spec) ty with
          | Dfix _ as d -> Some d
          | _ -> None )
    | _ -> None )
  | _ -> None

let structure struc =
  let defs = definitions struc in
  let rec elems l =
    List.map
      (fun (lbl, se) ->
        match se with
        | SEdecl (Dterm (r, body, ty)) -> (
          match decl defs r body ty with Some d -> (lbl, SEdecl d) | None -> (lbl, se) )
        | SEmodule ({ml_mod_expr = MEstruct (mp, l); _} as m) ->
          (lbl, SEmodule {m with ml_mod_expr = MEstruct (mp, elems l)})
        | se -> (lbl, se))
      l
  in
  List.map (fun (mp, l) -> (mp, elems l)) struc
