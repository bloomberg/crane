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
   lambdas its body starts with.  The type may leave its result open; the
   arity is what says a call is a full one. *)
type local = {l_type : ml_type; l_arity : int}

(* The functions whose calls are bound: a top-level fixpoint group, by
   reference, and the local fixpoints enclosing the term, each by the depth
   its bodies start at and its functions, the [j]th being [MLrel (j + 1)]
   there.  [own_tvars] counts the type variables of the declaration, [Tvar 1]
   to [Tvar own_tvars]; [fresh] names the next temporary of the declaration,
   and [effects] are the effect operations of the program it is in. *)
type group = {
  globals : GlobRef.t list;
  own_tvars : int;
  locals : (int * local array) list;
  fresh : unit -> ml_ident;
  effects : Core_effects.t;
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
   yields, if it is one and is applied fully, its application read whole as
   translation reads it ({!Mlutil.read_spine}): [(magic go) m ys] is a call
   of [go]. *)
let group_call group ~depth e =
  match Mlutil.read_spine e with
  | MLapp ((MLglob {callee = r; _} as f), args) when List.exists (GlobRef.UserOrd.equal r) group.globals ->
    full_result (Translation_types.ml_app_result_type f args)
  | MLapp (MLrel (k, _), args) -> (
    match
      List.find_map
        (fun (root, fns) ->
          let j = k - (depth - root) - 1 in
          if j >= 0 && j < Array.length fns then Some fns.(j) else None )
        group.locals
    with
    | Some l when List.length args = l.l_arity ->
      let value_args = List.filter (function MLdummy _ -> false | _ -> true) args in
      (* What it yields, or, where the fixpoint's type does not say, an open
         annotation of the temporary's own: the program is frozen. *)
      Some
        (Option.default (Mlutil.new_meta ())
           (Ml_type_util.ml_codomain_after (List.length value_args) l.l_type))
    | _ -> None )
  | _ -> None

(* How the value of a call is read where it stands: through a coercion
   into a type, as a field of the constructor it is an argument of, or
   passed on as it is to anything else. *)
type reading =
  | Coerced of ml_type
  | Stored
  | Passed

(* The type the temporary binding the call [e], of type [ty], read as
   [reading] says, is declared at, or [None] where the call is left in
   place.  A function whose result is a type index
   ({!Ml_type_util.result_is_index_only_tvar}: [eval : expr A -> A]) returns
   it boxed, and a temporary at [ty] holds it unboxed, cast where it is
   bound.  Where [ty] names a type variable the declaration does not bind
   -- one a constructor hides, the [A * B] of [fst (eval p)] or the
   components of the pair [(eval x, eval y)] -- no C++ type spells it, and
   only the box holds the value: an open annotation, which prints as the
   box.  Translation opens a boxed temporary where a coercion reads it into
   a type with a shape, and keeps it boxed where it is read at the
   function's own result type, as the pair's fields read its components.
   Coerced into a type variable, or passed on to anything else, it could be
   opened at a type of no value there, so such a call is left in place. *)
let held group ~reading e ty =
  let boxed_only =
    Mlutil.type_maxvar ty > group.own_tvars
    &&
    match Mlutil.read_spine e with
    | MLapp (MLglob {callee = r; _}, _) ->
      Option.cata Ml_type_util.result_is_index_only_tvar false (Translation_state.find_type_opt r)
    | _ -> false
  in
  if not boxed_only then Some ty
  else
    match reading with
    | Stored -> Some (Mlutil.new_meta ())
    | Coerced into -> (
      match Mlutil.type_simpl into with
      | Tvar _ | Tapp _ -> None
      | _ -> Some (Mlutil.new_meta ()) )
    | Passed -> None

(* Whether [e], at binder depth [depth], calls one of [group]'s functions
   where it is evaluated with [e]: under a branch or a let body, but not
   under a lambda -- except a local fixpoint applied there and then, whose
   body runs with it. *)
let rec reaches_call group ~depth e =
  group_call group ~depth e <> None
  ||
  match e with
  | MLapp (MLfix (_, ids, bodies, false, _), args) ->
    List.exists (reaches_call group ~depth) args || fix_reaches_call group ~depth ids bodies
  | MLlam _ | MLfix _ -> false
  | MLletin (_, _, rhs, body, _) ->
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
   their own.  A coercion is no scope: a call it reads is bound like any
   other, [S (eval x)] becoming [let t := eval x in S t], with the coercion
   kept around the temporary ({!held}).  Tail modulo cons
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
  let enters_group = function
    | MLfix (_, ids, bodies, false, _) -> fix_reaches_call group ~depth ids bodies
    | _ -> false
  in
  let rec strict ?(reading = Passed) ~tail e =
    match e with
    | MLapp ((MLglob use as f), args)
      when Core_effects.lookup group.effects use = Some {operation = Bind; mode = Sequential} ->
      (* Monadic sequencing: the action runs where the bind puts it, and a
         recursive call that is the whole action is a tail call there.  A
         reified bind is a call building the tree, its action evaluated
         first, like any other call's argument. *)
      MLapp (f, List.map (inner 0) args)
    | MLapp (f, args) -> (
      let e' = MLapp (strict ~tail:false f, List.map (strict ~tail:false) args) in
      match group_call e', f with
      | Some ty, _ when not tail -> Option.cata (take e') e' (held group ~reading e' ty)
      | None, MLfix (i, ids, _, false, _) when (not tail) && enters_group f ->
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
      MLcons (ty, r, List.map (strict ~reading:Stored ~tail:false) args)
    | MLcons (ty, r, args) ->
      (* A constructor mapped to custom code is what its replacement text
         makes of its arguments.  One that is just an argument ([%a0])
         stands for it, tail position included; any other ([%a0 + 1]) is an
         ordinary call. *)
      let through = Option.bind (Table.find_custom_opt r) Foreign_template.passes_through in
      MLcons
        ( ty,
          r,
          List.mapi
            (fun i a ->
              if through = Some i then strict ~reading ~tail a else strict ~reading:Stored ~tail:false a )
            args )
    | MLtuple args -> MLtuple (List.map (strict ~tail:false) args)
    | MLcase (ty, scrut, branches) ->
      let scrut = strict ~tail:false scrut in
      let e' =
        MLcase
          ( ty,
            scrut,
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
    | MLletin (id, ty, rhs, body, occ) ->
      (* A right-hand side that is the call, a local fixpoint applied there
         that recurses into the group, or a match ending in one, is already
         bound. *)
      let rhs =
        match rhs with
        | MLapp (f, args) when group_call rhs <> None || enters_group f ->
          MLapp (strict ~tail:false f, List.map (strict ~tail:false) args)
        | MLcase _ -> strict ~tail:true rhs
        | _ -> strict ~tail:false rhs
      in
      MLletin (id, ty, rhs, inner 1 body, occ)
    | MLlam (id, ty, body) -> MLlam (id, ty, inner 1 body)
    | MLfix (i, ids, bodies, cofix, occ) ->
      let n = Array.length ids in
      let group =
        if cofix then group
        else
          let fns =
            Array.mapi (fun j (_, ty) -> {l_type = ty; l_arity = Mlutil.nb_lams bodies.(j)}) ids
          in
          {group with locals = (depth + n, fns) :: group.locals}
      in
      MLfix (i, ids, Array.map (inner ~group n) bodies, cofix, occ)
    | MLmagic ((Mcoerce (_, into) as m), a) -> MLmagic (m, strict ~reading:(Coerced into) ~tail a)
    | MLmagic (m, a) -> MLmagic (m, strict ~tail a)
    | _ -> e
  in
  let body = strict ~tail:true e in
  let calls = List.rev !taken in
  let k = List.length calls in
  (* The [i]th let sees the [i - 1] before it; the body sees all [k]. *)
  let rec wrap i = function
    | [] -> replace_placeholders (fun j -> fresh_rel (k - j + 1)) (Mlutil.ast_lift k body)
    | (call, ty) :: rest ->
      let rhs = replace_placeholders (fun j -> fresh_rel (i - j)) (Mlutil.ast_lift (i - 1) call) in
      MLletin (group.fresh (), ty, rhs, wrap (i + 1) rest, Occurrence.fresh ())
  in
  if k = 0 then body else wrap 1 calls

(* Whether [r] is loopified: by its own name, or, made a method, where its
   inductive's methods are (see {!Table.loopifies_methods_of}) and its own
   name does not decline. *)
let loopified ~methods r =
  match Method_registry.is_registered_method methods r with
  | Some (ind, _) -> Table.loopifies_methods_of ind && Table.loopifies_method r
  | None -> Table.should_loopify r

(* The body [b] of a declaration of type [ty], normalized against the
   top-level functions [globals] it recurses through, in a program of effect
   operations [effects]. *)
let body ~effects ~globals ty b =
  scope ~group:{globals; own_tvars = Mlutil.type_maxvar ty; locals = []; fresh = temporaries (); effects} ~depth:0 b

let decl ~effects ~methods = function
  | Dfix fds when List.exists (fun fd -> loopified ~methods fd.fd_ref) fds ->
    (* A group is normalized whole: loopification inlines one member's
       partners into it, whether or not they are loopified themselves. *)
    let globals = List.map (fun fd -> fd.fd_ref) fds in
    Dfix (List.map (fun fd -> {fd with fd_body = body ~effects ~globals fd.fd_type fd.fd_body}) fds)
  | Dterm (r, b, ty) when loopified ~methods r ->
    (* No recursion of its own, but a local fixpoint in it is loopified. *)
    Dterm (r, body ~effects ~globals:[] ty b, ty)
  | d -> d

(* A definition of type [ty] as it is generated: binding a parameter at each
   of its type's arrows ({!Ml_type_util.eta_parameters}), the body it writes
   applied to the ones it does not, at each that extraction did not erase. *)
let eta_body ty b =
  match b with
  | MLaxiom _ | MLexn _ -> b
  | _ ->
    let ty = Mlutil.type_simpl ty in
    let params, body = Ml_type_util.collect_typed_lams ty b in
    match Ml_type_util.eta_parameters ty params with
    | [] -> b
    | missing ->
      let args =
        List.rev
          (List.filter_map
             (fun (i, (_, t)) -> if Ml_type_util.erased_by_extraction t then None else Some (fresh_rel (i + 1)))
             (List.mapi (fun i x -> (i, x)) missing) )
      in
      Mlutil.named_lams (missing @ params)
        (Mlutil.apply_eta_args (Mlutil.ast_lift (List.length missing) body) args)

let eta_expand =
  Modutil.map_struct_decls (function
    | Dterm (r, b, ty) -> Dterm (r, eta_body ty b, ty)
    | Dfix fds -> Dfix (List.map (fun fd -> {fd with fd_body = eta_body fd.fd_type fd.fd_body}) fds)
    | d -> d )

let let_lambdas =
  Modutil.map_struct_decls (function
    | Dterm (r, b, ty) -> Dterm (r, Core_elaborate.generated_definition ty b, ty)
    | Dfix fds ->
      Dfix (List.map (fun fd -> {fd with fd_body = Core_elaborate.generated_definition fd.fd_type fd.fd_body}) fds)
    | d -> d )

(* The methods the structure's functions become. *)
let methods_of struc = Method_registry.create ~ret_is_erased:Translation.return_type_is_erased struc

(* The effect operations are those of the program being normalized, read
   off it first ({!Core_effects.analyze}): a bind is sequencing only where
   the declaration it is written in erases its monad. *)
let structure struc =
  Modutil.map_struct_decls (decl ~effects:(Core_effects.analyze struc) ~methods:(methods_of struc)) struc
