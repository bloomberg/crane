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

(* A local fixpoint function: its declared type, and its arity, the
   lambdas its body starts with.  The type may still be a meta translation
   has yet to fill; the arity is what says a call is a full one. *)
type local = {l_type : ml_type; l_arity : int}

(* The functions whose calls are bound: a top-level fixpoint group, by
   reference, and the local fixpoints enclosing the term, each by the depth
   its bodies start at and its functions, the [j]th being [MLrel (j + 1)]
   there.  [fresh] names the next temporary of the declaration. *)
type group = {
  globals : GlobRef.t list;
  locals : (int * local array) list;
  fresh : unit -> ml_ident;
}

(* A supply of the declaration's temporaries, numbered from 1, so no two of
   its bindings share a name, whichever branches they sit in. *)
let temporaries () =
  let n = ref 0 in
  fun () ->
    incr n;
    Tmp (Mlutil.temporary_id !n)

(* A full application yields what its function's type ends in.  A partial
   one yields a function: there is nothing to evaluate early, and naming it
   would turn a direct argument into a closure. *)
let full_result = function Some (Tarr _) -> None | ty -> ty

(* The type a call at binder depth [depth] to one of [group]'s functions
   yields, if it is one and is applied fully. *)
let group_call group ~depth = function
  | MLapp ((MLglob (r, _) as f), args) when List.exists (GlobRef.UserOrd.equal r) group.globals ->
    full_result (Translation_types.ml_app_result_type f args)
  | MLapp (MLrel k, args) -> (
    match
      List.find_map
        (fun (root, fns) ->
          let j = k - (depth - root) - 1 in
          if j >= 0 && j < Array.length fns then Some fns.(j) else None )
        group.locals
    with
    | Some l when List.length args = l.l_arity ->
      let value_args = List.filter (function MLdummy _ -> false | _ -> true) args in
      (* What it yields, or, while translation has yet to say, a meta of its
         own for the temporary. *)
      Some
        (Option.default (Mlutil.new_meta ())
           (Ml_type_util.ml_codomain_after (List.length value_args) l.l_type))
    | _ -> None )
  | _ -> None

(* Whether [e], at binder depth [depth], calls one of [group]'s functions
   where it is evaluated with [e]: under a branch or a let body, but not
   under a lambda -- except a local fixpoint applied there and then, whose
   body runs with it. *)
let rec reaches_call group ~depth e =
  group_call group ~depth e <> None
  ||
  match e with
  | MLapp (MLfix (_, ids, bodies, false), args) ->
    List.exists (reaches_call group ~depth) args || fix_reaches_call group ~depth ids bodies
  | MLlam _ | MLfix _ -> false
  | MLletin (_, _, rhs, body) ->
    reaches_call group ~depth rhs || reaches_call group ~depth:(depth + 1) body
  | MLcase (_, scrut, branches) ->
    reaches_call group ~depth scrut || branch_reaches_call group ~depth branches
  | MLapp (f, args) -> List.exists (reaches_call group ~depth) (f :: args)
  | MLcons (_, _, args) | MLtuple args -> List.exists (reaches_call group ~depth) args
  | MLmagic (_, e) -> reaches_call group ~depth e
  | _ -> false

(* Whether a local fixpoint's bodies, below their parameters, reach [group]. *)
and fix_reaches_call group ~depth ids bodies =
  let rec params depth = function MLlam (_, _, b) -> params (depth + 1) b | b -> (depth, b) in
  Array.exists
    (fun b ->
      let depth, b = params (depth + Array.length ids) b in
      reaches_call group ~depth b )
    bodies

and branch_reaches_call group ~depth branches =
  Array.exists
    (fun (ids, _, _, b) -> reaches_call group ~depth:(depth + List.length ids) b)
    branches

(* [scope ~group ~depth e] -- [e], at binder depth [depth], with every call
   to [group] that sits at a strictly evaluated, non-tail position bound to
   a variable first, in evaluation order.  Branches, lambda bodies, let
   bodies, a bind's arguments and a coinductive constructor's are scopes of
   their own, and nothing under a coercion is touched.  Tail modulo cons
   sees through the bindings ({!Cpp_temporaries} restores the expression
   before it looks), so a constructor's arguments are bound like any
   other. *)
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
      match group_call e', f with
      | Some ty, _ when not tail -> take e' ty
      | None, MLfix (i, ids, bodies, false)
        when (not tail) && fix_reaches_call group ~depth ids bodies ->
        (* A local fixpoint applied here that recurses into the group is a
           call into it. *)
        let value_args = List.filter (function MLdummy _ -> false | _ -> true) args in
        take e'
          (Option.default (Mlutil.new_meta ())
             (Ml_type_util.ml_codomain_after (List.length value_args) (snd ids.(i))))
      | _ -> e' )
    | MLcons (ty, (GlobRef.ConstructRef (ind, _) as r), args)
      when Table.is_coinductive (GlobRef.IndRef ind) ->
      (* A coinductive constructor suspends its arguments. *)
      MLcons (ty, r, List.map (inner 0) args)
    | MLcons (ty, r, args) when not (Table.is_custom r) ->
      MLcons (ty, r, List.map (strict ~tail:false) args)
    | MLcons (ty, r, args) ->
      (* A constructor mapped to custom code is what its replacement text
         makes of its arguments.  One that is just an argument ([%a0])
         stands for it, tail position included; any other ([%a0 + 1]) is an
         ordinary call. *)
      let through = Option.bind (Table.find_custom_opt r) Foreign_template.passes_through in
      MLcons (ty, r, List.mapi (fun i a -> strict ~tail:(tail && through = Some i) a) args)
    | MLtuple args -> MLtuple (List.map (strict ~tail:false) args)
    | MLcase (ty, scrut, branches) ->
      let e' =
        MLcase
          ( ty,
            strict ~tail:false scrut,
            Array.map
              (fun (ids, rty, p, body) -> (ids, rty, p, inner (List.length ids) body))
              branches )
      in
      (* A match whose value is not the result, with a branch that recurses,
         is itself bound: the call ends its branch, so no binding inside the
         branch can take it out of the expression around the match. *)
      if (not tail) && branch_reaches_call group ~depth branches then
        let _, rty, _, _ = branches.(0) in
        take e' rty
      else e' 
    | MLletin (id, ty, rhs, body) ->
      (* A right-hand side that is the call, or a match ending in one, is
         already bound. *)
      let rhs =
        match rhs with
        | MLapp (f, args) when group_call rhs <> None ->
          MLapp (strict ~tail:false f, List.map (strict ~tail:false) args)
        | MLcase _ -> strict ~tail:true rhs
        | _ -> strict ~tail:false rhs
      in
      MLletin (id, ty, rhs, inner 1 body)
    | MLlam (id, ty, body) -> MLlam (id, ty, inner 1 body)
    | MLfix (i, ids, bodies, cofix) ->
      let n = Array.length ids in
      let group =
        if cofix then group
        else
          let fns =
            Array.mapi (fun j (_, ty) -> {l_type = ty; l_arity = Mlutil.nb_lams bodies.(j)}) ids
          in
          {group with locals = (depth + n, fns) :: group.locals}
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
      MLletin (group.fresh (), ty, rhs, wrap (i + 1) rest)
  in
  if k = 0 then body else wrap 1 calls

(* Whether [r] is loopified: by its own name, or as a method of an
   inductive whose methods are (see {!Table.loopifies_methods_of}). *)
let loopified ~methods r =
  Table.should_loopify r
  ||
  match Method_registry.is_registered_method methods r with
  | Some (ind, _) -> Table.loopifies_methods_of ind
  | None -> false

(* A declaration's body, normalized against the top-level functions
   [globals] it recurses through. *)
let body ~globals b = scope ~group:{globals; locals = []; fresh = temporaries ()} ~depth:0 b

let decl ~methods = function
  | Dfix fds when List.exists (fun fd -> loopified ~methods fd.fd_ref) fds ->
    (* A group is normalized whole: loopification inlines one member's
       partners into it, whether or not they are loopified themselves. *)
    let globals = List.map (fun fd -> fd.fd_ref) fds in
    Dfix (List.map (fun fd -> {fd with fd_body = body ~globals fd.fd_body}) fds)
  | Dterm (r, b, ty) when loopified ~methods r ->
    (* No recursion of its own, but a local fixpoint in it is loopified. *)
    Dterm (r, body ~globals:[] b, ty)
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

(* The methods the structure's functions become.  The registry is built as
   [Extract_env] builds its own, in the discovery phase (naming a file-level
   module asserts it); and naming records the modules names live in, which is
   the printer's business, not ours, so that is put back afterwards. *)
let methods_of struc =
  let saved = Common.mpfiles_save () in
  let phase = Common.get_phase () in
  Common.set_phase Common.Discover;
  Fun.protect
    ~finally:(fun () ->
      Common.set_phase phase;
      Common.mpfiles_restore saved )
    (fun () -> Method_registry.create ~ret_is_erased:Translation.return_type_is_erased struc)

let structure struc =
  let methods = methods_of struc in
  List.map (fun (mp, sel) -> (mp, structure_elems ~methods sel)) struc
