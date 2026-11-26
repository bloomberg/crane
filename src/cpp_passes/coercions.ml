(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Base.Type_util

(** [adapter_params ~prefix dom] -- fresh parameters for an adapter lambda,
    one per domain type, in source order.

    An adapter is a lambda whose only job is to call something else with its
    own arguments passed along, so its parameters exist only to be named.
    [prefix] distinguishes the adapters from one another in the generated
    code. *)
let adapter_params ~prefix dom =
  List.mapi (fun i ty -> (ty, Some (Id.of_string (Printf.sprintf "%s%d" prefix i)))) dom

(** An {!adapter_params} parameter read back as the argument to pass along. *)
let adapter_arg (_, id) : Cpp_ir.Lowered.Expr.t = Local (Option.get id)

(** [stored_adapter params e]: the lambda taking [params], in source order,
    that returns [e] and holds its captures by copy, its return type
    deduced. *)
let stored_adapter ?(moved = []) params (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  Lambda
    { params;
      type_params = [];
      return_type = None;
      body = [Return (Some e)];
      capture = Stored;
      moved;
      binders = [];
      modes = [];
      fixpoint = None }

(** Whether a parameter of type [ty] an adapter takes is worth moving into
    a closure capture rather than copying: one it owns, by value, whose copy
    costs something ({!Ownership_ir.Region.worth_moving_cpp}).  A reference
    ([auto &&] may name the caller's lvalue) and a [const] value are
    copied. *)
let adapter_param_moves (ty : Cpp_ir.Lowered.Type.t) =
  match ty with
  | Reference _ | Const _ -> false
  | _ -> Ownership_ir.Region.worth_moving_cpp ty

(** Re-instantiate a function value that is being adapted for an erased slot:
    the values it will be applied to reached that slot erased too -- a
    [list nat] argument is stored as [List<std::any>], not [List<uint64_t>] --
    so the function has to be taken at the erased instantiation, or the
    adapter would unbox to a shape nothing ever boxed. *)
let erased_fn_instantiation ?(box = Cpp_ir.Type.Any) : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Expr.t = function
  | Entity (g, (_ :: _ as tys), xs) -> Entity (g, List.map (fun _ -> box) tys, xs)
  | e -> e

(** [regroup_curried ~from ~into expr]: [expr], a function value of the C++
    type [from], as one of [into] where the two are one function type with
    its arrows grouped otherwise ({!Cpp_ir.Types.same_arrows}): an adapter
    taking [into]'s arguments group by group and applying [expr] to them as
    [from] groups them, once it has all of a group of [from]'s.  A curried
    value reaching a flat slot is [\[=\](A a, B b) { return f(a)(b); }];
    a flat one reaching a curried slot is [\[=\](A a) { return \[=\](B b)
    { return f(a, b); }; }].  [expr] itself where the types are not so
    related. *)
let regroup_curried ~(from : Cpp_ir.Lowered.Type.t) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  (* [f] applied to [args] group by group as its type [t] takes them;
     [None] where a group would straddle the end of [args]. *)
  let rec apply f (t : Cpp_ir.Lowered.Type.t) args =
    match (strip_cpp_ref_const t, args) with
    | t, [] -> Some (f, t)
    | Function (d, c), _ when List.compare_length_with args (List.length d) >= 0 ->
      let now = List.filteri (fun i _ -> i < List.length d) args
      and rest = List.filteri (fun i _ -> i >= List.length d) args in
      apply (Cpp_ir.Build.call f now) c rest
    | _ -> None
  in
  (* The adapter for the slot [into] at depth [depth], the arguments of
     the levels above it ([pending]) not yet a whole group of [from]'s. *)
  let rec go depth pending (from : Cpp_ir.Lowered.Type.t) (into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) =
    let from = strip_cpp_ref_const from and into = strip_cpp_ref_const into in
    match into with
    | Function (dom', cod') when pending <> [] || (from <> into && Cpp_ir.Types.same_arrows from into) -> (
      let params = adapter_params ~prefix:(Printf.sprintf "_rg%d_" depth) dom' in
      let args = pending @ List.map adapter_arg params in
      let body =
        match apply expr from args with
        | Some (body, rest) -> Some (go (depth + 1) [] rest cod' body)
        | None -> (
          (* A group of [from]'s straddles this level: the next level takes
             the rest of it. *)
          match strip_cpp_ref_const cod' with
          | Function _ -> Some (go (depth + 1) args from cod' expr)
          | _ -> None )
      in
      match body with
      | Some body -> Cpp_ir.Build.lambda params None [Return (Some body)] ~capture:Stored
      | None -> expr )
    | _ -> expr
  in
  go 0 [] from into expr

(** [nest ?into params body]: a closure taking [params] and returning
    [body], its parameters grouped as the function type [into] groups its
    arrows -- [\[=\](A a) { return \[=\](B b) { return body; }; }] for a
    curried [into] -- where [into]'s domains are [params]' types, group by
    group; one flat closure otherwise.  A closure built to fill a slot (a
    partial application's) takes its arguments as the slot hands them. *)
let nest ?(into : Cpp_ir.Lowered.Type.t option) params (body : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let flat () = Cpp_ir.Build.lambda params None [Return (Some body)] ~capture:Stored in
  let same (a : Cpp_ir.Lowered.Type.t) (b : Cpp_ir.Lowered.Type.t) = strip_cpp_ref_const a = strip_cpp_ref_const b in
  (* The group sizes, where [t]'s domains are [params]' types in order. *)
  let rec groups (t : Cpp_ir.Lowered.Type.t) (ps : Cpp_ir.Lowered.Type.t list) =
    if ps = [] then Some []
    else
      match strip_cpp_ref_const t with
      | Function (d, c) when List.compare_lengths d ps <= 0 ->
        let now = List.filteri (fun i _ -> i < List.length d) ps
        and rest = List.filteri (fun i _ -> i >= List.length d) ps in
        if List.for_all2 same d now then Option.map (fun gs -> List.length d :: gs) (groups c rest) else None
      | _ -> None
  in
  match Option.map strip_cpp_ref_const into with
  | Some (Function _ as t) -> (
    match groups t (List.map fst params) with
    | Some (_ :: _ :: _ as gs) ->
      let rec build ps = function
        | [] -> body
        | g :: gs ->
          let now = List.filteri (fun i _ -> i < g) ps and rest = List.filteri (fun i _ -> i >= g) ps in
          Cpp_ir.Build.lambda now None [Return (Some (build rest gs))] ~capture:Stored
      in
      build params gs
    | _ -> flat () )
  | _ -> flat ()

(** [eta_short ~domain ~arity f]: [f], a lambda taking the first [arity] of
    [domain], applied to the rest of them by an adapter taking all of
    [domain]: what the shorter lambda returns takes the arguments it did not
    take. *)
let eta_short ~domain ~arity (f : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let params = adapter_params ~prefix:"_ee" domain in
  let taken = List.filteri (fun i _ -> i < arity) params in
  let rest = List.filteri (fun i _ -> i >= arity) params in
  let call = List.fold_left (fun acc group -> Cpp_ir.Build.call acc (List.map adapter_arg group)) f [taken; rest] in
  Cpp_ir.Build.lambda params None [Return (Some call)] ~capture:Stored

(** How many parameters the outer lambda {!eta_global} builds takes, given
    the function type a global is [declared] at and the slot type [into];
    [None] where the global's name is a value already: it takes no
    callable, and the slot takes as many arguments at once as it does. *)
let eta_global_outer ~(declared : Cpp_ir.Lowered.Type.t option) ~(into : Cpp_ir.Lowered.Type.t option) =
  let decl_dom = match declared with Some (Function (dom, _)) -> dom | _ -> [] in
  match into with
  | Some (Function (exp_dom, _)) when exp_dom <> [] && List.length decl_dom > List.length exp_dom ->
    Some (List.length exp_dom)
  | _ when List.exists (function Cpp_ir.Type.Function _ -> true | _ -> false) decl_dom -> Some (List.length decl_dom)
  | _ -> None

(** Make a global named in value position into an expression a caller can
    invoke, by eta-expanding it into a lambda that calls it.

    Two declarations need this.  A definition returning a closure ([nat -> nat
    -> nat] read as [nat -> (nat -> nat)]) is declared flat, with every arrow
    becoming a C++ parameter; that suits a direct call, but handing the bare
    name to something expecting a one-argument callable does not compile, so
    the nesting the use site asks for is rebuilt:

    {v [](uint64_t _ec0) { return [=](uint64_t _ec1) { return f(_ec0, _ec1); }; } v}

    A definition with a function-typed parameter is declared as a template
    deducing that parameter ({!Base.Common.fun_tparam_name}), and its name
    alone is an overload set rather than a value; one flat lambda gives the
    call the argument it deduces from:

    {v [](std::function<uint64_t(uint64_t)> _ec0, uint64_t _ec1) { return f(_ec0, _ec1); } v}

    A class method projected through its instance ([opN::op]) is a function
    named the same way, and is curried the same way.

    [declared] is the function type the global is declared at, and [site]
    the arrow site it is spelled at ({!Cpp_ir.Types.arrow_site}), where
    [declared] is an instantiation of it: an instantiation can push arrows
    into the codomain ([idf {A} : A -> A] at [A := nat -> nat] reads as two
    arguments), and the declaration takes only the arguments it wrote, the
    rest going to what the call returns as one more group ([Declared_at n]).

    Returns [cglob] unchanged when the declaration is already a value
    ({!eta_global_outer}). *)
let eta_global ~declared ~(into : Cpp_ir.Lowered.Type.t option) ~site ~exact (cglob : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let decl_dom, decl_cod =
    match declared with Some (Cpp_ir.Type.Function (dom, cod)) -> (dom, Some cod) | _ -> ([], None)
  in
  match eta_global_outer ~declared ~into with
  | None -> cglob
  | Some n_outer ->
    (* A function-typed parameter with erased positions in it takes a
       polymorphic function object, not the [std::function] its erasure
       spells: writing that type here would fix the very type argument the
       callee leaves to the caller.  [auto &&] passes whatever arrives
       through, which is all this adapter does with it -- unless [exact]: a
       value converted on to the erased signature is fixed at it anyway, and a
       generic adapter has no signature to convert from. *)
    let decl_dom =
      if exact then decl_dom
      else
        List.map
          (fun (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
            match ty with Function _ when has_tany_in_type ty -> Reference (Forwarding, Auto) | _ -> ty )
          decl_dom
    in
    (* Where the slot is declared at a type variable -- a parameter of
       [fold_left]'s step, [A -> B -> A] -- what the declaration takes or
       returns at a function type passes through that variable, which spells
       it as its values are spelled: the adapter takes such a parameter as
       the declaration does, and returns what follows the slot's arguments
       as one more group. *)
    let exp_dom, exp_cod =
      let rec strip (t : Cpp_ir.Lowered.Type.t) = match t with Const t | Reference (_, t) -> strip t | t -> t in
      match Option.map strip into with
      | Some (Function (dom, cod)) -> (List.map strip dom, Some (strip cod))
      | _ -> ([], None)
    in
    let params = adapter_params ~prefix:"_ec" decl_dom in
    let passed _ p : Cpp_ir.Lowered.Expr.t = adapter_arg p in
    (* The callee takes the parameters as the site it is spelled at groups
       them. *)
    let call =
      let callee_ty = Cpp_ir.Types.spell_arrows site (Function (decl_dom, Option.default Cpp_ir.Type.Auto decl_cod)) in
      (Cpp_ir.Typed.apply (Cpp_ir.Typed.typed callee_ty cglob)
         (List.mapi passed params) )
        .expr
    in
    let into =
      match (into, exp_cod, decl_cod) with
      | Some _, Some (Variable _), Some cod when List.length decl_dom > List.length exp_dom ->
        let rest = List.filteri (fun i _ -> i >= List.length exp_dom) decl_dom in
        Some (Cpp_ir.Type.Function (exp_dom, Function (rest, cod)))
      | _ -> into
    in
    (* One lambda per group of arguments the slot takes at a time, as deep as
       it nests: [fn<fn<fn<R(C)>(B)>(A)>] takes [A], then [B], then [C].  A
       group's lambda does nothing but return the next one, so the next one
       takes the parameters it owns by move ({!adapter_param_moves}); deeper
       lambdas copy them, out of a capture they cannot move from. *)
    let rec nest ~moved params (expected : Cpp_ir.Lowered.Type.t option) =
      match expected with
      | Some (Const t | Reference (_, t)) -> nest ~moved params (Some t)
      | Some (Function (dom, cod)) when dom <> [] && List.length params > List.length dom ->
        let k = List.length dom in
        let outer = List.filteri (fun i _ -> i < k) params in
        let owned = List.filter_map (fun (ty, id) -> if adapter_param_moves ty then id else None) outer in
        stored_adapter ~moved outer (nest ~moved:owned (List.filteri (fun i _ -> i >= k) params) (Some cod))
      | _ -> stored_adapter ~moved params call
    in
    nest ~moved:[] params (if n_outer < List.length params then into else None)

(** [name_at spelled expr]: a callable named, at the instantiation
    [spelled] where the scope can spell it, else at the [crane::fn] it
    deduces ({!Cpp_ir.Expr.Function_value}); one named already as it is. *)
let name_at (spelled : Cpp_ir.Lowered.Type.t option) (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match (expr, spelled) with
  | Function_value _, _ -> expr
  | _, Some f -> Converting_construct (f, [expr])
  | _, None -> Function_value expr

(** [expand p e]: [e] adapted as [p] plans.  A function of the two alone:
    whatever the context decided is in [p], and what the plan leaves to the
    value's form is read off [e], as built. *)
let rec expand (p : Cpp_ir.Lowered.Coercion.plan) (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match p with
  | Regroup_curried (from, into) -> regroup_curried ~from ~into e
  | Nest into -> (
    match e with Lambda {params; body = [Return (Some body)]; _} -> nest ?into params body | e -> e )
  | Eta_short {domain; arity} -> eta_short ~domain ~arity e
  | Eta_global {declared; into; site; exact} -> eta_global ~declared ~into ~site ~exact e
  | Name_closure -> ( match e with Lambda _ -> Function_value e | e -> e )
  | Name_at spelled -> name_at spelled e
  | Erase_as shape -> Erase_callable (shape, e)
  | Convert_to t -> Convert (t, e)
  | Represent (src_ty, dst_ty) -> Convert.gen_type_conversion_expr ~src_ty ~dst_ty e
  | Box_value (box, erase) -> (
    match e with
    (* Boxing is not idempotent: [std::any] holding a [std::any] is a box
       no consumer opens twice. *)
    | (Box (b, _) | Any_cast (b, _)) when b = box -> e
    | _ ->
      (* A closure does not survive as itself: the consumer recovers it with
         [any_cast<std::function<std::any(std::any...)>>], so it is adapted
         to that canonical shape first.  It is then boxed like any other
         value -- a custom constructor template such as [std::make_pair]
         deduces its field type from the argument, and an unboxed
         [std::function] would store [pair<any, function<any(any)>>] where
         the consumer expects [pair<any,any>]. *)
      let adapted : Cpp_ir.Lowered.Expr.t = if erase then Erase_callable (Boxed_whole, erased_fn_instantiation ~box e) else e in
      Box (box, match adapted with Box (_, x) -> x | x -> x) )
  | Recover_box {into; lambda} -> (
    match (e, lambda) with
    (* A closure built here is not a box, whatever its erased type says: what
       is boxed is what it returns.  Its returns are recovered at the
       codomain instead. *)
    | Lambda l, Some (cod, at) ->
      let rec at_returns : Cpp_ir.Lowered.Stmt.t -> Cpp_ir.Lowered.Stmt.t = function
        | Return (Some e) -> Return (Some (apply at e))
        | st -> Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:Fun.id ~stmt:at_returns ~type_:Fun.id ()) st
      in
      Lambda
        { l with
          return_type = (match l.return_type with Some t when Cpp_ir.Types.prints_as_any t -> Some cod | r -> r);
          body = List.map at_returns l.body }
    | Lambda _, None -> e
    (* Already recovered; a second cast would be reading the same box twice. *)
    | Any_cast _, _ -> e
    | _ -> (
      (* A list went into the box with its elements boxed, so that is the
         shape the cast has to name however concrete the context's element
         type is; the converting constructor then recovers each element. *)
      match Erasure.erased_list_shape into with
      (* A custom list has no converting constructor to unbox its elements
         with, so it stays at the flat shape until a consumer converts it. *)
      | Some (g, shape) when Base.Table.is_custom g -> Erasure.unbox shape e
      | Some (_, shape) -> Erasure.converting_ctor into [Erasure.unbox shape e]
      | None -> Erasure.unbox into e ) )
  | Recover_call {domain; args; result} ->
    let params = adapter_params ~prefix:"_ue" domain in
    let args = List.map2 (fun p a -> apply a (adapter_arg p)) params args in
    let call = apply result (Cpp_ir.Build.call e args) in
    Cpp_ir.Build.lambda params None [Return (Some call)] ~capture:Stored

  | Box_list_deep -> Cpp_ir.Build.call (Runtime Cpp_ir.Crane_rt.Deep_box) [e]
  | Recast_carrier t -> Container_cast (t, e, false)
  (* {!Erasure.unbox}'s structural rules; whether [into] is written as a
     box was asked where the plan was made ({!Core_to_cpp.Coerce.unbox}):
     the answer can change by the time this pass runs (a type variable a
     declaration drops as phantom prints as a box from then on). *)
  | Cast_box {into; tolerant} -> (
    match e with
    | Box (_, inner) -> inner
    | Lambda _ -> e
    | _ -> if tolerant then Tolerant_any_cast (into, e) else Any_cast (into, e) )
  | Moving (x, p) -> ( match expand p e with Lambda l -> Lambda {l with moved = [x]} | e -> e )

and apply p e = match p with Some p -> expand p e | None -> e

let () = Cpp_ir.Typed.expansion := expand

(** {!Cpp_ir.Typed.head}. *)
let head = Cpp_ir.Typed.head

(** Every coercion in [decl] expanded, innermost first, so that each plan
    reads the value it adapts as built. *)
let decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  let rec fe (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
    match Cpp_ir.Map.expr (rw ()) e with Coerce (c, e) -> expand c.plan e | e -> e
  and fs s = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  Cpp_ir.Map.decl (rw ()) d
