(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A definition whose body is another's, written once.  See
    [ml_dedup.mli]. *)

open Names
open Miniml

(* [body] with what alpha-equivalence ignores taken out: binder names, type
   annotations, and [self], the definition's own name, which its recursive
   calls spell -- as [MLrel 0], an index no binder gives. *)
let rec canonical self body =
  let anon = Dummy in
  match body with
  | MLglob (r, _) when GlobRef.CanOrd.equal r self -> MLrel 0
  | MLglob (r, _) -> MLglob (r, [])
  | MLlam (_, _, b) -> MLlam (anon, Tunknown, canonical self b)
  | MLletin (_, _, a, b) -> MLletin (anon, Tunknown, canonical self a, canonical self b)
  | MLcons (_, c, args) -> MLcons (Tunknown, c, List.map (canonical self) args)
  | MLcase (_, s, brs) ->
    MLcase
      ( Tunknown,
        canonical self s,
        Array.map
          (fun (ids, _, p, b) -> (List.map (fun _ -> (anon, Tunknown)) ids, Tunknown, p, canonical self b))
          brs )
  | MLfix (i, fns, bodies, co) ->
    MLfix
      ( i,
        Array.map (fun (_, _) -> (Id.of_string "f", Tunknown)) fns,
        Array.map (canonical self) bodies,
        co )
  | MLmagic (m, a) -> MLmagic (m, canonical self a)
  | e -> Mlutil.ast_map (canonical self) e

(* A forwarder with [body]'s parameters, calling [target] at the type
   variables of [ty], in order. *)
let forwarder body ty target =
  let params, _ = Mlutil.collect_lams body in
  let n = List.length params in
  let tys = List.init (Mlutil.type_maxvar ty) (fun i -> Tvar (Schematic, i + 1)) in
  Mlutil.named_lams params
    (MLapp (MLglob (target, tys), List.init n (fun i -> MLrel (n - i))))

(* A function definition: a fixpoint, or a term that is a lambda, emitted
   as a function.  A constant is left alone -- a forwarder would compute it
   again -- and so is a mapped one, whose body is never what is emitted, and
   a projection, which is read as a field. *)
let function_def d =
  let emitted r = not (Table.is_custom r || Table.is_projection r) in
  match d with
  | Dfix [fd] when emitted fd.fd_ref -> Some (fd.fd_ref, fd.fd_body, fd.fd_type)
  | Dterm (r, (MLlam _ as body), ty) when emitted r -> Some (r, body, ty)
  | _ -> None

let structure struc =
  let rec elems seen = function
    | [] -> []
    | (l, SEdecl d) :: rest when function_def d <> None -> (
      let r, body, ty = Option.get (function_def d) in
      let key = canonical r body in
      match List.find_opt (fun (key', _, ty') -> key' = key && Mlutil.eq_ml_type ty' ty) seen with
      | Some (_, r', _) -> (l, SEdecl (Dterm (r, forwarder body ty r', ty))) :: elems seen rest
      | None -> (l, SEdecl d) :: elems ((key, r, ty) :: seen) rest )
    | (l, SEmodule m) :: rest ->
      (l, SEmodule {m with ml_mod_expr = module_expr m.ml_mod_expr}) :: elems seen rest
    | se :: rest -> se :: elems seen rest
  and module_expr = function
    | MEstruct (mp, sel) -> MEstruct (mp, elems [] sel)
    | MEfunctor (mbid, mt, me) -> MEfunctor (mbid, mt, module_expr me)
    | me -> me
  in
  List.map (fun (mp, sel) -> (mp, elems [] sel)) struc
