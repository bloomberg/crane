(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml

(* The placeholder for the [i]th call taken out of a scope, replaced once the
   binder it is read through is known. *)
let marker = "\000normalize:"

let placeholder i = MLexn (marker ^ string_of_int i)

let placeholder_index = function
  | MLexn s when String.starts_with ~prefix:marker s ->
    int_of_string_opt (String.sub s (String.length marker) (String.length s - String.length marker))
  | _ -> None

(* [replace_placeholders f e]: each placeholder [i] in [e] becomes [f i].
   Placeholders sit only at strictly evaluated positions of the scope they
   were made in, never under a binder, so no index needs adjusting. *)
let rec replace_placeholders f e =
  match placeholder_index e with
  | Some i -> f i
  | None -> Mlutil.ast_map (replace_placeholders f) e

let binder = Id (Id.of_string "_r")

(* [scope ~group_call e] -- [e] with every call [group_call] recognises that
   sits at a strictly evaluated, non-tail position bound to a variable first,
   in evaluation order.  A constructor's last direct recursive argument is
   left in place: building a cell around a recursive call is what tail
   modulo cons rewrites.  Branches, lambda bodies, let bodies, a bind's
   arguments and a coinductive constructor's are scopes of their own, and
   nothing under a coercion is touched. *)
let rec scope ~group_call e =
  let taken = ref [] in
  let count = ref 0 in
  let take call ty =
    incr count;
    taken := (call, ty) :: !taken;
    placeholder !count
  in
  let rec strict ~tail e =
    match e with
    | MLapp ((MLglob (r, _) as f), args) when Table.is_bind r ->
      (* Monadic sequencing: the action runs where the bind puts it, and a
         recursive call that is the whole action is a tail call there. *)
      MLapp (f, List.map (scope ~group_call) args)
    | MLapp (f, args) -> (
      let e' = MLapp (f, List.map (strict ~tail:false) args) in
      match group_call e' with
      | Some ty when not tail -> take e' ty
      | _ -> e' )
    | MLcons (ty, (GlobRef.ConstructRef (ind, _) as r), args)
      when Table.is_coinductive (GlobRef.IndRef ind) ->
      (* A coinductive constructor suspends its arguments. *)
      MLcons (ty, r, List.map (scope ~group_call) args)
    | MLcons (ty, r, args) when not (Table.is_custom r) ->
      (* Tail modulo cons fills one hole per cell, so only the last direct
         recursive argument stays; any before it are bound. *)
      let last_rec =
        List.fold_left
          (fun (i, last) a -> (i + 1, if group_call a <> None then Some i else last))
          (0, None) args
        |> snd
      in
      let arg i a =
        match a with
        | MLapp (f, args) when Some i = last_rec ->
          MLapp (f, List.map (strict ~tail:false) args)
        | _ -> strict ~tail:false a
      in
      MLcons (ty, r, List.mapi arg args)
    | MLcons (ty, r, args) ->
      (* A constructor mapped to custom code: only its replacement text says
         whether a direct argument stays in tail position ([%a0]) or not
         ([%a0 + 1]), so direct recursive arguments stay for Loopify. *)
      let arg a =
        match a with
        | MLapp (f, args) when group_call a <> None ->
          MLapp (f, List.map (strict ~tail:false) args)
        | _ -> strict ~tail:false a
      in
      MLcons (ty, r, List.map arg args)
    | MLtuple args -> MLtuple (List.map (strict ~tail:false) args)
    | MLcase (ty, scrut, branches) ->
      MLcase
        ( ty,
          strict ~tail:false scrut,
          Array.map (fun (ids, rty, p, body) -> (ids, rty, p, scope ~group_call body)) branches )
    | MLletin (id, ty, rhs, body) ->
      (* A right-hand side that is the call is already bound. *)
      MLletin (id, ty, strict ~tail:true rhs, scope ~group_call body)
    | MLlam (id, ty, body) -> MLlam (id, ty, scope ~group_call body)
    | MLfix (i, ids, bodies, cofix) -> MLfix (i, ids, Array.map (scope ~group_call) bodies, cofix)
    | _ -> e
  in
  let body = strict ~tail:true e in
  let calls = List.rev !taken in
  let k = List.length calls in
  (* The [i]th let sees the [i - 1] before it; the body sees all [k]. *)
  let rec wrap i = function
    | [] -> replace_placeholders (fun j -> MLrel (k - j + 1)) (Mlutil.ast_lift k body)
    | (call, ty) :: rest ->
      let rhs = replace_placeholders (fun j -> MLrel (i - j)) (Mlutil.ast_lift (i - 1) call) in
      MLletin (binder, ty, rhs, wrap (i + 1) rest)
  in
  if k = 0 then body else wrap 1 calls

(* A call to one of [group]'s functions, applied fully, with the type it
   yields.  A partial application yields a function: there is nothing to
   evaluate early, and naming it would turn a direct argument into a
   closure. *)
let group_call group = function
  | MLapp ((MLglob (r, _) as f), args) when List.exists (GlobRef.UserOrd.equal r) group -> (
    match Translation_types.ml_app_result_type f args with
    | Some (Tarr _) -> None
    | ty -> ty )
  | _ -> None

(* Whether [fd] is loopified: by its own name, or as a method of an
   inductive whose methods are (see {!Table.loopifies_methods_of}). *)
let loopified ~methods fd =
  Table.should_loopify fd.fd_ref
  ||
  match Method_registry.is_registered_method methods fd.fd_ref with
  | Some (ind, _) -> Table.loopifies_methods_of ind
  | None -> false

let decl ~methods = function
  | Dfix fds ->
    let group = List.map (fun fd -> fd.fd_ref) fds in
    Dfix
      (List.map
         (fun fd ->
           if loopified ~methods fd then
             {fd with fd_body = scope ~group_call:(group_call group) fd.fd_body}
           else fd )
         fds )
  | d -> d

let rec structure_elems ~methods sel =
  List.map
    (fun (l, se) ->
      match se with
      | SEdecl d -> (l, SEdecl (decl ~methods d))
      | SEmodule m ->
        (l, SEmodule {m with ml_mod_expr = module_expr ~methods m.ml_mod_expr})
      | se -> (l, se) )
    sel

and module_expr ~methods = function
  | MEstruct (mp, sel) -> MEstruct (mp, structure_elems ~methods sel)
  | MEfunctor (mbid, mt, me) -> MEfunctor (mbid, mt, module_expr ~methods me)
  | me -> me

(* The methods the structure's functions become.  Naming them records the
   modules they live in, which is the printer's business, not ours. *)
let methods_of struc =
  let saved = Common.mpfiles_save () in
  let methods =
    Method_registry.create ~ret_is_erased:Translation.return_type_is_erased struc
  in
  Common.mpfiles_restore saved;
  methods

let structure struc =
  let methods = methods_of struc in
  List.map (fun (mp, sel) -> (mp, structure_elems ~methods sel)) struc
