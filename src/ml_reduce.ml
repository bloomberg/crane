(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A whitelisted scalar reduction, rewritten to carry an accumulator.  See
    [ml_reduce.mli]. *)

open Names
open Miniml
module MS = Mapping_semantics

(* [t] with its free indices above [m] -- past the [m] binders it sits under
   -- moved [k] further out. *)
let lift_above m k t =
  let rec go n = function
    | MLrel i as a -> if i <= n then a else MLrel (i + k)
    | a -> Mlutil.ast_map_lift go n a
  in
  go m t

(* The width an inductive is declared an unsigned integer at. *)
let nat_width = function
  | GlobRef.ConstructRef (ind, _) -> (
    match MS.find (GlobRef.IndRef ind) with
    | Some (MS.Unsigned_nat w) -> Some w
    | _ -> None )
  | _ -> None

(* [e] is that type's zero: its constant constructor. *)
let zero_width = function
  | MLcons (_, c, []) -> nat_width c
  | _ -> None

(* [e] is built from declared operations, constructors, literals and
   variables only, and so evaluates to a value and does nothing else, at any
   point. *)
let rec declared_pure = function
  | MLrel _ | MLuint _ | MLfloat _ | MLstring _ -> true
  | MLcons (_, _, args) | MLtuple args -> List.for_all declared_pure args
  | MLapp (MLglob (g, _), args) -> (
    match MS.find g with
    | Some (MS.Unsigned _) -> List.for_all declared_pure args
    | _ -> false )
  | MLmagic (_, a) -> declared_pure a
  | MLletin (_, _, a, b) -> declared_pure a && declared_pure b
  | MLcase (_, s, brs) ->
    declared_pure s && Array.for_all (fun (_, _, _, b) -> declared_pure b) brs
  | _ -> false

let rec mentions_glob r = function
  | MLglob (r', _) -> GlobRef.CanOrd.equal r r'
  | e ->
    let found = ref false in
    Mlutil.ast_iter (fun a -> if mentions_glob r a then found := true) e;
    !found

(* The result type of [ty] after [n] arguments. *)
let rec codomain n ty =
  if n = 0 then Some ty
  else
    match ty with
    | Tarr (_, b) -> codomain (n - 1) b
    | Tmeta {contents = Some t} -> codomain n t
    | _ -> None

(** [accumulate f ty body] is [body] rewritten to carry its sum forward, when
    it is the reduction this module knows and [f], of type [ty], is the
    function it defines. *)
let accumulate f ty body =
  let params, inner = Mlutil.collect_lams body in
  let n = List.length params in
  match inner with
  | MLcase (cty, MLrel j, ([|_; _|] as brs)) when j <= n -> (
    (* The spine parameter's source position. *)
    let p = n - j in
    let classify (ids, _, _, b) =
      let m0 = List.length ids in
      (* Pure [let]s in front of the addition belong to the contribution:
         [let c := ... in c + f xs]. *)
      let rec peel k lets = function
        | MLletin (id, t, e, body) when declared_pure e -> peel (k + 1) ((id, t, e) :: lets) body
        | body -> (k, lets, body)
      in
      let k, lets, core = peel 0 [] b in
      let m = m0 + k in
      match zero_width b, core with
      | Some w, _ -> `Base w
      | None, MLapp (MLglob (add, _), [a; c]) -> (
        match MS.find add with
        | Some (MS.Unsigned (MS.Add, w)) ->
          let is_rec_call = function
            | MLapp (MLglob (f', _), args)
              when GlobRef.CanOrd.equal f f' && List.length args = n ->
              let ok = ref true and field = ref None in
              List.iteri
                (fun i a ->
                  match a with
                  (* The spine's tail: one of the branch's own binders, not
                     one the peeled [let]s bound. *)
                  | MLrel r when i = p && r > k && r <= m -> field := Some r
                  | MLrel r when i <> p && r = n - i + m -> ()
                  | _ -> ok := false)
                args;
              if !ok then !field else None
            | _ -> None
          in
          let rec_and_contrib =
            match (is_rec_call a, is_rec_call c) with
            | Some r, None -> Some (r, c)
            | None, Some r -> Some (r, a)
            | _ -> None
          in
          ( match rec_and_contrib with
          | Some (field, contrib)
            when (not (mentions_glob f contrib))
                 && declared_pure contrib
                 && not (Mlutil.ast_occurs (j + m) contrib) ->
            `Step (w, add, List.rev lets, field, contrib)
          | _ -> `Other )
        | _ -> `Other )
      | _ -> `Other
    in
    let kinds = Array.map classify brs in
    let width_of = function `Base w | `Step (w, _, _, _, _) -> Some w | `Other -> None in
    let base_zero =
      Array.to_list brs
      |> List.find_map (fun ((_, _, _, b) as br) ->
             match classify br with `Base _ -> Some b | _ -> None)
    in
    match (Array.to_list kinds, base_zero, codomain n ty) with
    | ([`Base _; `Step _] | [`Step _; `Base _]), Some zero, Some nat_ty
      when width_of kinds.(0) = width_of kinds.(1) ->
      let spine_ty = snd (List.nth params (j - 1)) in
      let brs' =
        Array.map2
          (fun (ids, r, pat, _) kind ->
            let m = List.length ids in
            match kind with
            | `Base _ -> (ids, r, pat, MLrel (m + 1))
            | `Step (_, add, lets, field, contrib) ->
              (* The contribution's [let]s stay where the source has them, in
                 front of the step, each lifted past [go], the spine and the
                 accumulator at its own depth. *)
              let k = List.length lets in
              let rec rebuild i = function
                | [] ->
                  MLapp
                    ( MLrel (m + k + 3),
                      [ MLrel field;
                        MLapp
                          ( MLglob (add, []),
                            [MLrel (m + k + 1); lift_above (m + k) 3 contrib] ) ] )
                | (id, t, e) :: rest ->
                  MLletin (id, t, lift_above (m + i) 3 e, rebuild (i + 1) rest)
              in
              (ids, r, pat, rebuild 0 lets)
            | `Other -> assert false )
          brs kinds
      in
      let go_ty = Tarr (spine_ty, Tarr (nat_ty, nat_ty)) in
      let go_body =
        MLlam
          ( Id (Id.of_string "l"), spine_ty,
            MLlam (Id (Id.of_string "acc"), nat_ty, MLcase (cty, MLrel 2, brs')) )
      in
      let worker = MLfix (0, [| (Id.of_string "go", go_ty) |], [| go_body |], false) in
      Some (Mlutil.named_lams params (MLapp (worker, [MLrel j; zero])))
    | _ -> None )
  | _ -> None

let decl = function
  | Dfix [fd] as d -> (
    match accumulate fd.fd_ref fd.fd_type fd.fd_body with
    | Some body -> Dfix [{fd with fd_body = body}]
    | None -> d )
  | d -> d

let rec structure_elems sel =
  List.map
    (fun (l, se) ->
      match se with
      | SEdecl d -> (l, SEdecl (decl d))
      | SEmodule m -> (l, SEmodule {m with ml_mod_expr = module_expr m.ml_mod_expr})
      | se -> (l, se) )
    sel

and module_expr = function
  | MEstruct (mp, sel) -> MEstruct (mp, structure_elems sel)
  | MEfunctor (mbid, mt, me) -> MEfunctor (mbid, mt, module_expr me)
  | me -> me

let structure struc = List.map (fun (mp, sel) -> (mp, structure_elems sel)) struc
