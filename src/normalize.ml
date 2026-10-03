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

(* The functions whose calls are bound: a top-level fixpoint group, by
   reference, and the local fixpoints enclosing the term, each by the depth
   its bodies start at and its functions, the [j]th being [MLrel (j + 1)]
   there. *)
type group = {globals : GlobRef.t list; locals : (int * (Id.t * ml_type) array) list}

(* A full application yields what its function's type ends in.  A partial
   one yields a function: there is nothing to evaluate early, and naming it
   would turn a direct argument into a closure. *)
let full_result = function Some (Tarr _) -> None | ty -> ty

(* The type a call at binder depth [depth] to one of [group]'s functions
   yields, if it is one and is applied fully. *)
let group_call group ~depth = function
  | MLapp ((MLglob (r, _) as f), args) when List.exists (GlobRef.UserOrd.equal r) group.globals ->
    full_result (Translation_types.ml_app_result_type f args)
  | MLapp (MLrel k, args) ->
    let value_args = List.filter (function MLdummy _ -> false | _ -> true) args in
    List.find_map
      (fun (root, ids) ->
        let j = k - (depth - root) - 1 in
        if j >= 0 && j < Array.length ids then Some (snd ids.(j)) else None )
      group.locals
    |> Option.cata
         (fun ty -> full_result (Ml_type_util.ml_codomain_after (List.length value_args) ty))
         None
  | _ -> None

(* [scope ~group ~depth e] -- [e], at binder depth [depth], with every call
   to [group] that sits at a strictly evaluated, non-tail position bound to
   a variable first, in evaluation order.  A constructor's last direct
   recursive argument is left in place: building a cell around a recursive
   call is what tail modulo cons rewrites.  Branches, lambda bodies, let
   bodies, a bind's arguments and a coinductive constructor's are scopes of
   their own, and nothing under a coercion is touched. *)
let rec scope ~group ~depth e =
  let group_call = group_call group ~depth in
  let inner ?(group = group) binders = scope ~group ~depth:(depth + binders) in
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
      MLapp (f, List.map (inner 0) args)
    | MLapp (f, args) -> (
      let e' = MLapp (strict ~tail:false f, List.map (strict ~tail:false) args) in
      match group_call e' with
      | Some ty when not tail -> take e' ty
      | _ -> e' )
    | MLcons (ty, (GlobRef.ConstructRef (ind, _) as r), args)
      when Table.is_coinductive (GlobRef.IndRef ind) ->
      (* A coinductive constructor suspends its arguments. *)
      MLcons (ty, r, List.map (inner 0) args)
    | MLcons (ty, r, args) when tail && not (Table.is_custom r) ->
      (* Tail modulo cons fills one hole: the last argument that is a
         recursive call, or a constructor in turn holding one, stays; any
         call before it is bound.  A constructor anywhere but the result is
         an ordinary value, and every call in it is bound. *)
      let rec holds_call a =
        group_call a <> None
        || match a with MLcons (_, _, args) -> List.exists holds_call args | _ -> false
      in
      let last_rec =
        List.fold_left
          (fun (i, last) a -> (i + 1, if holds_call a then Some i else last))
          (0, None) args
        |> snd
      in
      let arg i a =
        match a with
        | MLapp (f, args) when Some i = last_rec ->
          MLapp (strict ~tail:false f, List.map (strict ~tail:false) args)
        | MLcons _ when Some i = last_rec -> strict ~tail:true a
        | _ -> strict ~tail:false a
      in
      MLcons (ty, r, List.mapi arg args)
    | MLcons (ty, r, args) when not (Table.is_custom r) ->
      MLcons (ty, r, List.map (strict ~tail:false) args)
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
          Array.map
            (fun (ids, rty, p, body) -> (ids, rty, p, inner (List.length ids) body))
            branches )
    | MLletin (id, ty, rhs, body) ->
      (* A right-hand side that is the call is already bound. *)
      let rhs =
        match rhs with
        | MLapp (f, args) when group_call rhs <> None ->
          MLapp (strict ~tail:false f, List.map (strict ~tail:false) args)
        | _ -> strict ~tail:false rhs
      in
      MLletin (id, ty, rhs, inner 1 body)
    | MLlam (id, ty, body) -> MLlam (id, ty, inner 1 body)
    | MLfix (i, ids, bodies, cofix) ->
      let n = Array.length ids in
      let group =
        if cofix then group else {group with locals = (depth + n, ids) :: group.locals}
      in
      MLfix (i, ids, Array.map (inner ~group n) bodies, cofix)
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
    let group = {globals = List.map (fun fd -> fd.fd_ref) fds; locals = []} in
    Dfix
      (List.map
         (fun fd ->
           if loopified ~methods fd then
             {fd with fd_body = scope ~group ~depth:0 fd.fd_body}
           else fd )
         fds )
  | Dterm (r, body, ty) when Table.should_loopify r ->
    (* No recursion of its own, but a local fixpoint in it is loopified. *)
    Dterm (r, scope ~group:{globals = []; locals = []} ~depth:0 body, ty)
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
