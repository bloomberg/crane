(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Traversal, search, and optimization functions over Core module
   structures.  See [modutil.mli]. *)

open Names
open ModPath
open CErrors
open Util
open Base.Table
open Base.Core_util

(** {1 Functions upon Core modules} *)

(* Note: a syntax like [(F M) with ...] is actually legal, see for instance bug
   #4720. Hence the code below tries to handle [Core.Module.Type.Signature], maybe not in a perfect
   way, but that should be enough for the use of [se_iter] below. *)

(** Extract module path from a module type. *)
let rec msid_of_mt = function
  | Core.Module.Type.Path mp -> mp
  | Core.Module.Type.Signature {path = mp; _} -> mp
  | Core.Module.Type.Refined {base = mt; _} -> msid_of_mt mt
  | Core.Module.Type.Functor _ -> assert false (* A functor cannot be inside a Core.Module.Type.Refined *)

(** Apply some functions upon all [Core.Decl.t] and [Core.Signature.Declaration.t] found in a
    [Core.Program.t]. *)
let se_iter do_decl do_spec do_mp =
  let rec mt_iter = function
    | Core.Module.Type.Path mp -> do_mp mp
    | Core.Module.Type.Functor {parameter_type = mt; result = mt'; _} ->
      mt_iter mt;
      mt_iter mt'
    | Core.Module.Type.Refined {base = mt;
                                refinement = Core.Module.Refinement.Type_equation {path = idl;
                                                                                   parameters = l;
                                                                                   definition = t}} ->
      let mp_mt = msid_of_mt mt in
      let l', idl' = List.sep_last idl in
      let mp_w =
        List.fold_left (fun mp l -> MPdot (mp, Label.of_id l)) mp_mt idl'
      in
      let r = GlobRef.ConstRef (Constant.make2 mp_w (Label.of_id l')) in
      mt_iter mt;
      do_spec (Core.Signature.Declaration.Type {entity = r; parameters = l; body = Some t})
    | Core.Module.Type.Refined {base = mt;
                                refinement = Core.Module.Refinement.Module_equation {path = idl; definition = mp}} ->
      let mp_mt = msid_of_mt mt in
      let mp_w =
        List.fold_left (fun mp l -> MPdot (mp, Label.of_id l)) mp_mt idl
      in
      mt_iter mt;
      do_mp mp_w;
      do_mp mp
    | Core.Module.Type.Signature {items = sign; _} -> List.iter spec_iter sign
  and spec_iter = function
    | _, Core.Module.Signature_item.Declaration s -> do_spec s
    | _, Core.Module.Signature_item.Module mt -> mt_iter mt
    | _, Core.Module.Signature_item.Module_type mt -> mt_iter mt
  in
  let rec se_iter = function
    | _, Core.Module.Structure_item.Declaration d -> do_decl d
    | _, Core.Module.Structure_item.Module (m : _ Core.Module.at) ->
      me_iter m.expr;
      mt_iter m.type_
    | _, Core.Module.Structure_item.Module_type m -> mt_iter m
  and me_iter = function
    | Core.Module.Expr.Path mp -> do_mp mp
    | Core.Module.Expr.Functor {parameter_type = mt; body = me; _} ->
      me_iter me;
      mt_iter mt
    | Core.Module.Expr.Apply {functor_ = me; argument = me'} ->
      me_iter me;
      me_iter me'
    | Core.Module.Expr.Structure {path = msid; items = sel} -> List.iter se_iter sel
  in
  se_iter

(** Every function defined outside a functor: a constant whose body is a
    lambda, and each member of a recursive group, in definition order. *)
let struct_functions struc =
  let acc = ref [] in
  let rec elems l =
    List.iter
      (fun (_, se) ->
        match se with
        | Core.Module.Structure_item.Declaration (Core.Decl.Value {entity = r;
                                                                   body = (Core.Expr.Lambda _ as b);
                                                                   type_ = ty}) ->
          acc := (r, b, ty) :: !acc
        | Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group fds) ->
          Core.Nonempty.iter
            (fun (fd : _ Core.Recursion.Definition.at) -> acc := (fd.entity, fd.body, fd.type_) :: !acc) fds
        | Core.Module.Structure_item.Module {Core.Module.expr = Core.Module.Expr.Structure {items = l; _}; _} -> elems l
        | _ -> () )
      l
  in
  List.iter (fun (_, l) -> elems l) struc;
  List.rev !acc

(** {!se_iter} over every element of every top-level structure. *)
let struct_iter do_decl do_spec do_mp s =
  List.iter
    (function
      | _, sel -> List.iter (se_iter do_decl do_spec do_mp) sel )
    s

(** {2 Reference iteration} *)

(** Callback type for reference iteration. *)
type do_ref = GlobRef.t -> unit

(** Iterate over field references in an inductive kind (Record/Type_class). *)
let record_iter_references do_term = function
  | Core.Inductive.Kind.Record l | Core.Inductive.Kind.Type_class l ->
    List.iter (fun (f : Core.Record.Field.t) -> Option.iter do_term f.projection) l
  | _ -> ()

(** Iterate over all GlobRef.t occurring in a Core type, through a resolved
    meta: a type extracted but not yet frozen reaches what it names through
    the metas unification solved. *)
let type_iter_references do_type t =
  Base.Core_util.fold_core_type
    (fun () -> function Core.Type.Global_app {head = r; _} -> do_type r | _ -> ())
    () t

(** Iterate over constructor references in a pattern. *)
let patt_iter_references do_cons p =
  let rec iter = function
    | Core.Pattern.Constructor {constructor = r; fields = l} ->
      do_cons r;
      List.iter iter l
    | Core.Pattern.Tuple l -> List.iter iter l
    | Core.Pattern.Bound_variable _ | Core.Pattern.Wildcard -> ()
  in
  iter p

(** Iterate over term, constructor, and type references in a Core term.
    [prune a] returning [true] skips [a] entirely (neither its own references
    nor those of its subterms are visited).  Used to drop subtrees that later
    passes fold away, e.g. numeral-converter applications. *)
let ast_iter_references ?(prune = fun _ -> false) do_term do_cons do_type a =
  let rec iter a =
    if prune a then ()
    else (
    ast_iter iter a;
    match a with
    (* A global instantiated at a type spells that type in the generated code
       -- [get<Bool0>] -- so whatever the type names has to be emitted
       alongside, whether it is a type-level definition or an inductive.  A
       [Prop] type reached this way is marked needed too, but it is dropped
       again where declarations are emitted: see the [logical_decl] guard in
       {!Driver.Extract_env}. *)
    | Core.Expr.Global ({callee = r; _} as use) ->
      do_term r;
      Core.Global_use.iter_types (type_iter_references do_type) use
    | Core.Expr.Match {scrutinee_type = ty; branches = v; _} ->
      type_iter_references do_type ty;
      Array.iter (fun {Core.Match.Branch.pattern = p; _} -> patt_iter_references do_cons p) v
    (* A binder's type is spelled where the binder is declared -- the
       parameter of a lambda, a local, a local fixpoint -- and a
       constructor's result type where it is built, [List<String>::nil()]:
       a type named only there is needed as much as one a global is
       instantiated at. *)
    | Core.Expr.Lambda {parameter_type = ty; _} | Core.Expr.Let {binder_type = ty; _} ->
      type_iter_references do_type ty
    | Core.Expr.Construct {constructor = r; result_type = ty; _} ->
      do_cons r;
      type_iter_references do_type ty
    | Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g ->
      Array.iter (fun (_, ty) -> type_iter_references do_type ty) (Core.Recursion.Group.functions g)
    | Core.Expr.Bound_variable _
     |Core.Expr.Apply _
     |Core.Expr.Tuple _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.Coerce _ | Core.Expr.Boxed_value _ | Core.Expr.Lambda_group_barrier _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _
     |Core.Expr.Persistent_array _ -> () )
  in
  iter a

(** Iterate over all references in an inductive definition. *)
let ind_iter_references do_term do_cons do_type kn (ind : Core.Inductive.t) =
  let type_iter = type_iter_references do_type in
  let cons_iter cp l =
    do_cons (GlobRef.ConstructRef cp);
    List.iter type_iter l
  in
  let packet_iter ip (p : Core.Inductive.Packet.t) =
    do_type (GlobRef.IndRef ip);
    ( if lang () == Cpp then
        match
          ind.equivalence
        with
        | Core.Inductive.Equivalence.Equivalent_to kne -> do_type (GlobRef.IndRef (MutInd.make1 kne, snd ip))
        | _ -> () );
    Array.iteri (fun j -> cons_iter (ip, j + 1)) p.constructor_argument_types
  in
  if lang () == Cpp then record_iter_references do_term ind.kind;
  Array.iteri (fun i -> packet_iter (kn, i)) ind.packets

(** Iterate over all references in a Core declaration.
    See {!ast_iter_references} for the meaning of [prune]. *)
let decl_iter_references ?prune do_term do_cons do_type =
  let type_iter = type_iter_references do_type
  and ast_iter = ast_iter_references ?prune do_term do_cons do_type in
  function
    | Core.Decl.Inductive {entity = kn; definition = ind} -> ind_iter_references do_term do_cons do_type kn ind
    | Core.Decl.Type_alias {entity = r; body = t; _} ->
      do_type r;
      type_iter t
    | Core.Decl.Value {entity = r; body = a; type_ = t} ->
      do_term r;
      ast_iter a;
      type_iter t
    | Core.Decl.Recursive_group fds ->
      Core.Nonempty.iter (fun (fd : _ Core.Recursion.Definition.at) -> do_term fd.entity) fds;
      Core.Nonempty.iter (fun (fd : _ Core.Recursion.Definition.at) -> ast_iter fd.body) fds;
      Core.Nonempty.iter (fun (fd : _ Core.Recursion.Definition.at) -> type_iter fd.type_) fds

(** Iterate over all references in a Core specification. *)
let spec_iter_references do_term do_cons do_type = function
  | Core.Signature.Declaration.Inductive {entity = kn; definition = ind} ->
    ind_iter_references do_term do_cons do_type kn ind
  | Core.Signature.Declaration.Type {entity = r; body = ot; _} ->
    do_type r;
    Option.iter (type_iter_references do_type) ot
  | Core.Signature.Declaration.Value {entity = r; type_ = t; _} ->
    do_term r;
    type_iter_references do_type t

(** {2 Searching occurrences of a particular term} *)

(** Raised during AST/type search when a match is found. *)
exception Found

(** Search for an AST node matching a predicate. *)
let rec ast_search f a = if f a then raise Found else ast_iter (ast_search f) a

(** Search for an AST node in a declaration. *)
let decl_ast_search f = function
  | Core.Decl.Value {body = a; _} -> ast_search f a
  | Core.Decl.Recursive_group fds ->
    Core.Nonempty.iter (fun (fd : _ Core.Recursion.Definition.at) -> ast_search f fd.body) fds
  | _ -> ()

(** Search for an AST node anywhere in a structure. *)
let struct_ast_search f s =
  try
    struct_iter (decl_ast_search f) (fun _ -> ()) (fun _ -> ()) s;
    false
  with Found -> true

(** Search for a type matching a predicate.  [f] is tested on the leaves:
    every node that is neither an arrow nor a [Core.Type.Global_app] (whose arguments are
    searched); a solved [Core.Type.Meta] is a leaf too. *)
let rec type_search f = function
  | Core.Type.Arrow {parameter = a; result = b} ->
    type_search f a;
    type_search f b
  | Core.Type.Global_app {head = r; type_arguments = l; _} -> List.iter (type_search f) l
  | u -> if f u then raise Found

(** Search for a type in a declaration. *)
let decl_type_search f = function
  | Core.Decl.Inductive {definition = {Core.Inductive.packets = p}; _} ->
    Array.iter
      (fun {Core.Inductive.Packet.constructor_argument_types = v} -> Array.iter (List.iter (type_search f)) v)
      p
  | Core.Decl.Value {type_ = u; _} -> type_search f u
  | Core.Decl.Recursive_group fds ->
    Core.Nonempty.iter (fun (fd : _ Core.Recursion.Definition.at) -> type_search f fd.type_) fds
  | Core.Decl.Type_alias {body = u; _} -> type_search f u

(** Search for a type in a specification. *)
let spec_type_search f = function
  | Core.Signature.Declaration.Inductive {definition = {Core.Inductive.packets = p}; _} ->
    Array.iter
      (fun {Core.Inductive.Packet.constructor_argument_types = v} -> Array.iter (List.iter (type_search f)) v)
      p
  | Core.Signature.Declaration.Type {body = ot; _} -> Option.iter (type_search f) ot
  | Core.Signature.Declaration.Value {type_ = u; _} -> type_search f u

(** Search for a type anywhere in a structure. *)
let struct_type_search f s =
  try
    struct_iter (decl_type_search f) (spec_type_search f) (fun _ -> ()) s;
    false
  with Found -> true

(** {2 Generating the signature} *)

(** Convert a module structure to a module signature. *)
let rec msig_of_ms = function
  | [] -> []
  | (l, Core.Module.Structure_item.Declaration (Core.Decl.Inductive {entity = kn; definition = i})) :: ms ->
    (l, Core.Module.Signature_item.Declaration (Core.Signature.Declaration.Inductive {entity = kn;
                                                                                      definition = i})) :: msig_of_ms ms
  | (l, Core.Module.Structure_item.Declaration (Core.Decl.Value {entity = r; body = b; type_ = t})) :: ms ->
    (l, Core.Module.Signature_item.Declaration (Core.Signature.Declaration.Value {entity = r;
                                                                                  body = b;
                                                                                  type_ = t})) :: msig_of_ms ms
  | (l, Core.Module.Structure_item.Declaration (Core.Decl.Type_alias {entity = r; parameters = v; body = t})) :: ms ->
    (l, Core.Module.Signature_item.Declaration (Core.Signature.Declaration.Type {entity = r;
                                                                                 parameters = v;
                                                                                 body = Some t})) :: msig_of_ms ms
  | (l, Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group fds)) :: ms ->
    List.map
      (fun (fd : _ Core.Recursion.Definition.at) ->
        (l,
          Core.Module.Signature_item.Declaration
            (Core.Signature.Declaration.Value {entity = fd.entity; body = fd.body; type_ = fd.type_})))
      (Core.Nonempty.to_list fds)
    @ msig_of_ms ms
  | (l, Core.Module.Structure_item.Module (m : _ Core.Module.at)) :: ms ->
    (l, Core.Module.Signature_item.Module m.type_) :: msig_of_ms ms
  | (l, Core.Module.Structure_item.Module_type m) :: ms ->
    (l, Core.Module.Signature_item.Module_type m) :: msig_of_ms ms

(** Convert a full structure to its type signature. *)
let signature_of_structure s = List.map (fun (mp, ms) -> (mp, msig_of_ms ms)) s

(** Convert a module expression to its module type. *)
let rec mtyp_of_mexpr = function
  | Core.Module.Expr.Functor {parameter = id; parameter_type = ty; body = e} ->
    Core.Module.Type.Functor {parameter = id; parameter_type = ty; result = mtyp_of_mexpr e}
  | Core.Module.Expr.Structure {path = mp; items = str} ->
    Core.Module.Type.Signature {path = mp; items = msig_of_ms str}
  | _ -> assert false

(** {2 Searching a declaration in a structure} *)

(** Test whether a structure element is modular (module or module type). *)
let is_modular = function
  | Core.Module.Structure_item.Declaration _ -> false
  | Core.Module.Structure_item.Module _ | Core.Module.Structure_item.Module_type _ -> true

(** Search for a label in a structure. *)
let rec search_structure l m = function
  | [] -> raise Not_found
  | (lab, d) :: _ when Label.equal lab l && (is_modular d : bool) == m -> d
  | _ :: fields -> search_structure l m fields

(** Look up a declaration by its GlobRef in a structure. *)
let get_decl_in_structure r struc =
  try
    let base_mp, ll = labels_of_ref r in
    if not (at_toplevel base_mp) then error_not_visible r;
    let sel = List.assoc_f ModPath.equal base_mp struc in
    let rec go ll sel =
      match ll with
      | [] -> assert false
      | l :: ll ->
      match search_structure l (not (List.is_empty ll)) sel with
      | Core.Module.Structure_item.Declaration d -> d
      | Core.Module.Structure_item.Module_type m -> assert false
      | Core.Module.Structure_item.Module m ->
        let rec aux = function
          | Core.Module.Expr.Structure {items = sel; _} -> go ll sel
          | Core.Module.Expr.Functor {body = sel; _} -> aux sel
          | Core.Module.Expr.Path _ | Core.Module.Expr.Apply _ -> error_not_visible r
        in
        aux m.expr
    in
    go ll sel
  with Not_found ->
    anomaly (Pp.str "reference not found in extracted structure.")

(** {2 Optimization of a Core.Program.t} *)

(* Some transformations of Core terms. [optimize_struct] simplifies all beta
    redexes (when the argument does not occur, it is just thrown away; when it
    occurs exactly once it is substituted; otherwise a let-in redex is created
    for clarity) and iota redexes, plus some other optimizations. *)

(** Convert member [i] of a [Core.Decl.Recursive_group] to a
    [Core.Expr.Fixpoint] term, for inlining. *)
let fixpoint_of_group fds i =
  let fds = Core.Nonempty.to_list fds in
  let rv = Array.of_list (List.map (fun (fd : _ Core.Recursion.Definition.at) -> fd.entity) fds) in
  let rec make_subst n s =
    if n < 0 then
      s
    else
      make_subst (n - 1) (Core.Ref.User.Map.add rv.(n) (n + 1) s)
  in
  let s = make_subst (Array.length rv - 1) Core.Ref.User.Map.empty in
  let rec subst n t =
    match t with
    | Core.Expr.Global {callee = (GlobRef.ConstRef kn as refe); _} ->
      (try Core.Expr.fresh_rel (n + Core.Ref.User.Map.find refe s) with Not_found -> t)
    | _ -> ast_map_lift subst n t
  in
  let ids =
    Array.of_list
      (List.map (fun (fd : _ Core.Recursion.Definition.at) -> (Label.to_id (label_of_r fd.entity), fd.type_)) fds)
  in
  let c = Array.of_list (List.map (fun (fd : _ Core.Recursion.Definition.at) -> subst 0 fd.body) fds) in
  Core.Expr.Fixpoint (Core.Recursion.Group.of_arrays ~selected:i ids c (Core.Occurrence.fresh ()))

(* A let-fix promoted to its declaration ([local_length]'s inner [go]) keeps
   the binder annotations it had inside it, where extraction may have left a
   metavariable for a variable the declaration's signature quantifies -- the
   [A] of [xs : list A].  The fixpoint's binders are now the signature's
   parameters, the outermost of them, so each annotation is unified with the
   signature's domain, which solves every other occurrence of its
   metavariables in the body too. *)
let unify_binders_with_signature t body =
  let rec domains t =
    match t with
    | Core.Type.Arrow {parameter = a; result = b} -> a :: domains b
    | Core.Type.Meta {contents = Some t} -> domains t
    | _ -> []
  in
  let doms = List.rev (domains t) in
  let ids, _ = collect_lams body in
  let ids = List.skipn (max 0 (List.length ids - List.length doms)) ids in
  let doms = List.skipn (max 0 (List.length doms - List.length ids)) doms in
  List.iter2 (fun (_, body_ty) sig_ty -> try_mgu body_ty sig_ty) ids doms

(** See [modutil.mli]. *)
let decl_of_term r a t =
  match dump_unused_vars (optimize_fix a) with
  (* An instance of a singleton class stays an instance, whose method the
     fixpoint is. *)
  | Core.Expr.Fixpoint {members = [|{body = c; _}|]; _} | Core.Expr.Cofixpoint {members = [|{body = c; _}|]; _}
    when singleton_instance_class r = None ->
    (* Each call of itself is a use of its own, told apart from the others
       by its occurrence. *)
    let c = Base.Core_util.ast_subst_each (fun () -> Core.Expr.Global (Base.Core_util.self_reference r)) c in
    unify_binders_with_signature t c;
    Core.Decl.Recursive_group (Core.Nonempty.singleton {Core.Recursion.Definition.entity = r; body = c; type_ = t})
    (* The self-reference instantiates [r] at its own type variables
       ({!Core.Global_use.identity}), so a self-call states no type
       arguments of its own. *)
  | a -> Core.Decl.Value {entity = r; body = a; type_ = t}

(** [optim_se] applies the [normalize] function everywhere and does the inlining
    of code. The inlined functions are kept for the moment in order to preserve
    the global interface, later [depcheck_se] will get rid of them if possible
*)
let[@tail_mod_cons] rec optim_se top to_appear s = function
  | [] -> []
  | (l, Core.Module.Structure_item.Declaration (Core.Decl.Value {entity = r; body = a; type_ = t})) :: lse ->
    let a = normalize (ast_glob_subst !s a) in
    let i = inline r a in
    if i then s := Core.Ref.User.Map.add r a !s;
    let d = decl_of_term r a t in
    (l, Core.Module.Structure_item.Declaration d) :: optim_se top to_appear s lse
  | (l, Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group fds)) :: lse ->
    let fds =
      Core.Nonempty.map
        (Core.Recursion.Definition.map_body (fun b -> normalize (ast_glob_subst !s b)))
        fds
    in
    (* This fake body ensures that no fixpoint will be auto-inlined: a
       fixpoint never is. *)
    let fake_body =
      Core.Expr.Fixpoint
        (Core.Recursion.Group.singleton (Id.of_string "fake") Core.Type.Unknown (Core.Expr.Runtime_error "")
           (Core.Occurrence.fresh ()))
    in
    List.iteri
      (fun i (fd : _ Core.Recursion.Definition.at) ->
        if inline fd.entity fake_body then
          s := Core.Ref.User.Map.add fd.entity (fixpoint_of_group fds i) !s )
      (Core.Nonempty.to_list fds);
    let fds = Core.Nonempty.map (Core.Recursion.Definition.map_body dump_unused_vars) fds in
    (l, Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group fds)) :: optim_se top to_appear s lse
  | (l, Core.Module.Structure_item.Module (m : _ Core.Module.at)) :: lse ->
    let m = {m with Core.Module.expr = optim_me to_appear s m.expr} in
    (l, Core.Module.Structure_item.Module m) :: optim_se top to_appear s lse
  | se :: lse -> se :: optim_se top to_appear s lse

and optim_me to_appear s = function
  | Core.Module.Expr.Structure {path = msid; items = lse} ->
    Core.Module.Expr.Structure {path = msid; items = optim_se false to_appear s lse}
  | Core.Module.Expr.Path mp as me -> me
  | Core.Module.Expr.Apply {functor_ = me; argument = me'} ->
    Core.Module.Expr.Apply {functor_ = optim_me to_appear s me; argument = optim_me to_appear s me'}
  | Core.Module.Expr.Functor {parameter = mbid; parameter_type = mt; body = me} ->
    Core.Module.Expr.Functor {parameter = mbid; parameter_type = mt; body = optim_me to_appear s me}

(* After these optimisations, some dependencies may not be needed anymore. For
   non-library extraction, we recompute a minimal set of dependencies for
   first-level definitions (no module pruning yet). *)

(** Normalize a GlobRef to its base inductive reference. *)
let base_r =
  let open GlobRef in
  function
    | ConstRef c as r -> r
    | IndRef (kn, _) -> IndRef (kn, 0)
    | ConstructRef ((kn, _), _) -> IndRef (kn, 0)
    | _ -> assert false

(** Dependency tracking: manage the set of needed references. *)
let reset_needed, add_needed, add_needed_mp, found_needed, is_needed =
  let needed = ref Core.Ref.User.Set.empty
  and needed_mps = ref MPset.empty in
  ( (fun () ->
      needed := Core.Ref.User.Set.empty;
      needed_mps := MPset.empty ),
    (fun r -> needed := Core.Ref.User.Set.add (base_r r) !needed),
    (fun mp -> needed_mps := MPset.add mp !needed_mps),
    (fun r -> needed := Core.Ref.User.Set.remove (base_r r) !needed),
    fun r ->
      let r = base_r r in
      Core.Ref.User.Set.mem r !needed || MPset.mem (modpath_of_r r) !needed_mps )

(** List all GlobRef.t declared by a declaration. *)
let declared_refs = function
  | Core.Decl.Inductive {entity = kn; _} -> [GlobRef.IndRef (kn, 0)]
  | Core.Decl.Type_alias {entity = r; _} -> [r]
  | Core.Decl.Value {entity = r; _} -> [r]
  | Core.Decl.Recursive_group fds ->
    List.map (fun (fd : _ Core.Recursion.Definition.at) -> fd.entity) (Core.Nonempty.to_list fds)

(** Computes the dependencies of a declaration, except in case of custom
    extraction. *)
let compute_deps_decl = function
  | Core.Decl.Inductive {entity = kn; definition = ind} ->
    (* Todo Later : avoid dependencies when Extract Inductive *)
    ind_iter_references add_needed add_needed add_needed kn ind
  | Core.Decl.Type_alias {entity = r; parameters = ids; body = t} ->
    if not (is_custom r) then type_iter_references add_needed t
  | Core.Decl.Value {entity = r; body = u; type_ = t} ->
    type_iter_references add_needed t;
    if not (is_custom r) then
      ast_iter_references add_needed add_needed add_needed u
  | Core.Decl.Recursive_group _ as d -> decl_iter_references add_needed add_needed add_needed d

(** Compute dependencies for a specification. *)
let compute_deps_spec = function
  | Core.Signature.Declaration.Inductive {entity = kn; definition = ind} ->
    (* Todo Later : avoid dependencies when Extract Inductive *)
    ind_iter_references add_needed add_needed add_needed kn ind
  | Core.Signature.Declaration.Type {entity = r; parameters = ids; body = t} ->
    if not (is_custom r) then Option.iter (type_iter_references add_needed) t
  | Core.Signature.Declaration.Value {entity = r; type_ = t; _} -> type_iter_references add_needed t

(** Dead code elimination: keep only needed declarations. *)
let rec depcheck_se = function
  | [] -> []
  | ((l, Core.Module.Structure_item.Declaration d) as t) :: se ->
    let se' = depcheck_se se in
    let refs = declared_refs d in
    let refs' = List.filter is_needed refs in
    if List.is_empty refs' then (
      List.iter remove_info_axiom refs;
      List.iter remove_opaque refs;
      se' )
    else (
      List.iter found_needed refs';
      (* Hack to avoid extracting unused part of a Core.Decl.Recursive_group *)
      match d with
      | Core.Decl.Recursive_group fds when List.for_all is_custom refs' ->
        let unused fd = {fd with Core.Recursion.Definition.body = Core.Expr.Runtime_error "UNUSED"} in
        (l, Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group (Core.Nonempty.map unused fds))) :: se'
      | _ ->
        compute_deps_decl d;
        t :: se' )
  | t :: se ->
    let se' = depcheck_se se in
    se_iter compute_deps_decl compute_deps_spec add_needed_mp t;
    t :: se'

(** Dead code elimination at the structure level. *)
let rec depcheck_struct = function
  | [] -> []
  | (mp, lse) :: struc ->
    let struc' = depcheck_struct struc in
    let lse' = depcheck_se lse in
    if List.is_empty lse' then struc' else (mp, lse') :: struc'

(** Raised when an implicit argument remains after optimization. *)
exception RemainingImplicit of Core.Erasure_reason.t

(** Warn if any implicit arguments remain in the structure. *)
let check_for_remaining_implicits struc =
  let check = function
    | Core.Expr.Erased_value (Core.Erasure_reason.Configured_implicit _ as k) -> raise (RemainingImplicit k)
    | _ -> false
  in
  try ignore (struct_ast_search check struc)
  with RemainingImplicit k -> err_or_warn_remaining_implicit k

(** Full optimization pipeline: normalize, inline, eliminate dead code. *)
let optimize_struct to_appear struc =
  let subst = ref (Core.Ref.User.Map.empty : _ Core.Expr.at Core.Ref.User.Map.t) in
  let opt_struc =
    List.map
      (fun (mp, lse) -> (mp, optim_se true (fst to_appear) subst lse))
      struc
  in
  let mini_struc =
    if library () then
      List.filter (fun (_, lse) -> not (List.is_empty lse)) opt_struc
    else (
      reset_needed ();
      List.iter add_needed (fst to_appear);
      List.iter add_needed_mp (snd to_appear);
      depcheck_struct opt_struc )
  in
  let () = check_for_remaining_implicits mini_struc in
  mini_struc

(** [s] with [decl] applied to every declaration, in modules and functor bodies
    alike: the frame of a pass that rewrites declarations one at a time.  With
    [spec], the module types are rewritten as well: [spec] is applied to every
    specification and [with_type] to the type a [with] refinement fixes. *)
let map_struct ?spec ?(with_type = Fun.id) decl s =
  let rec mtype spec = function
    | Core.Module.Type.Path _ as mt -> mt
    | Core.Module.Type.Functor {parameter = mbid; parameter_type = mt; result = mt'} ->
      Core.Module.Type.Functor {parameter = mbid; parameter_type = mtype spec mt; result = mtype spec mt'}
    | Core.Module.Type.Signature {path = mp; items = sign} ->
      Core.Module.Type.Signature {path = mp; items = List.map (fun (l, s) -> (l, specif spec s)) sign}
    | Core.Module.Type.Refined {base = mt;
                                refinement = Core.Module.Refinement.Type_equation {path = idl;
                                                                                   parameters = l;
                                                                                   definition = t}} ->
      Core.Module.Type.Refined {base = mtype spec mt;
                                refinement = Core.Module.Refinement.Type_equation {path = idl;
                                                                                   parameters = l;
                                                                                   definition = with_type t}}
    | Core.Module.Type.Refined {base = mt; refinement = (Core.Module.Refinement.Module_equation _ as w)} ->
      Core.Module.Type.Refined {base = mtype spec mt; refinement = w}
  and specif spec = function
    | Core.Module.Signature_item.Declaration s -> Core.Module.Signature_item.Declaration (spec s)
    | Core.Module.Signature_item.Module mt -> Core.Module.Signature_item.Module (mtype spec mt)
    | Core.Module.Signature_item.Module_type mt -> Core.Module.Signature_item.Module_type (mtype spec mt)
  in
  let mtype mt = match spec with Some spec -> mtype spec mt | None -> mt in
  let rec elems sel =
    List.map
      (fun (l, se) ->
        match se with
        | Core.Module.Structure_item.Declaration d -> (l, Core.Module.Structure_item.Declaration (decl d))
        | Core.Module.Structure_item.Module m ->
          (l, Core.Module.Structure_item.Module {Core.Module.expr = module_expr m.expr; type_ = mtype m.type_})
        | Core.Module.Structure_item.Module_type mt -> (l, Core.Module.Structure_item.Module_type (mtype mt)) )
      sel
  and module_expr = function
    | Core.Module.Expr.Structure {path = mp; items = sel} -> Core.Module.Expr.Structure {path = mp; items = elems sel}
    | Core.Module.Expr.Functor {parameter = mbid; parameter_type = mt; body = me} ->
      Core.Module.Expr.Functor {parameter = mbid; parameter_type = mtype mt; body = module_expr me}
    | me -> me
  in
  List.map (fun (mp, sel) -> (mp, elems sel)) s

(** {!map_struct} with the module types untouched. *)
let map_struct_decls f s = map_struct f s
