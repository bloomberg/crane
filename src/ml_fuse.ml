(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A right fold of a map, fused into one traversal.  See [ml_fuse.mli]. *)

open Names
open Miniml

let same = GlobRef.CanOrd.equal

(** A definition's structural recursion over a two-constructor datatype:
    which constructors, and the type its cons branch gives the element, as
    the definition declares it. *)
type spine = {nil : GlobRef.t; cons : GlobRef.t; elem : ml_type}

(* [map]: [fun f l => match l with nil => nil | cons x xs => cons (f x) (map
   f xs)]. *)
let as_map defs g =
  match Option.map Mlutil.collect_lams (Table.Refmap'.find_opt g defs) with
  | Some
      ( [_; _],
        MLcase
          ( _, MLrel 1,
            [| ([], _, Pusual nil, MLcons (_, nil', []));
               ( [(_, elem); _], _, Pusual cons,
                 MLcons
                   ( _, cons',
                     [MLapp (MLrel 4, [MLrel 2]); MLapp (MLglob (g', _), [MLrel 4; MLrel 1])] ) )
            |] ) )
    when same nil nil' && same cons cons' && same g g' ->
    Some {nil; cons; elem}
  | _ -> None

(* [foldr]: [fun f z l => match l with nil => z | cons x xs => f x (foldr f
   z xs)]; and the type of [z]. *)
let as_foldr defs g =
  match Option.map Mlutil.collect_lams (Table.Refmap'.find_opt g defs) with
  | Some
      ( [_; (_, acc); _],
        MLcase
          ( _, MLrel 1,
            [| ([], _, Pusual nil, MLrel 2);
               ( [(_, elem); _], _, Pusual cons,
                 MLapp (MLrel 5, [MLrel 2; MLapp (MLglob (g', _), [MLrel 5; MLrel 4; MLrel 1])]) )
            |] ) )
    when same g g' ->
    Some ({nil; cons; elem}, acc)
  | _ -> None

(* A callback that evaluates to a value and does nothing else, whenever it
   is called. *)
let pure_callback = function
  | MLlam _ as f -> Ml_declared.pure (snd (Mlutil.collect_lams f))
  | MLglob (g, _) -> (
    match Mapping_semantics.find g with
    | Some (Mapping_semantics.Unsigned _) -> true
    | _ -> false )
  | MLapp (MLglob _, _) as f -> Ml_declared.pure f
  | _ -> false

(* [f] applied to [args], each a term of the context [f] is in.  A lambda
   takes a variable by substitution and anything else by a [let], so each
   argument is still evaluated once, in order. *)
let rec apply f args =
  match (f, args) with
  | f, [] -> f
  | MLlam (_, _, b), (MLrel _ as a) :: rest -> apply (Mlutil.ast_subst a b) rest
  | MLlam (id, t, b), a :: rest ->
    MLletin (id, t, a, apply b (List.map (Mlutil.ast_lift 1) rest))
  | MLapp (g, xs), _ -> MLapp (g, xs @ args)
  | f, _ -> MLapp (f, args)

(* A type of a definition, at the instance its call writes. *)
let at_instance tys t =
  if Mlutil.type_maxvar t <= List.length tys then Some (Mlutil.type_subst_list tys t) else None

let fuse defs e =
  match e with
  | MLapp (MLglob (fold, ftys), [step; z; MLapp (MLglob (map, mtys), [f; xs])]) -> (
    match (as_foldr defs fold, as_map defs map) with
    | Some (fs, acc), Some ms
      when same fs.nil ms.nil && same fs.cons ms.cons && pure_callback step
           && pure_callback f -> (
      (* The fold now walks the map's input: its element type parameter is
         instantiated at the map's element type, at the map's instance. *)
      match (Mlutil.ml_resolve fs.elem, at_instance mtys ms.elem, at_instance ftys acc) with
      | Tvar (_, k), Some x_ty, Some acc_ty when k <= List.length ftys ->
        let ftys = List.mapi (fun i t -> if i = k - 1 then x_ty else t) ftys in
        let l2 = Mlutil.ast_lift 2 in
        let step' =
          MLlam
            ( Id (Id.of_string "x"), x_ty,
              MLlam
                ( Id (Id.of_string "acc"), acc_ty,
                  apply (l2 step) [apply (l2 f) [MLrel 2]; MLrel 1] ) )
        in
        MLapp (MLglob (fold, ftys), [step'; z; xs])
      | _ -> e )
    | _ -> e )
  | _ -> e

let structure struc =
  let defs = Ml_declared.definitions struc in
  let rec rewrite e = fuse defs (Mlutil.ast_map rewrite e) in
  Ml_declared.map_decls
    (function
      | Dterm (r, body, ty) -> Dterm (r, rewrite body, ty)
      | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = rewrite fd.fd_body}) fds)
      | d -> d)
    struc
