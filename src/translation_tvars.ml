(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Type variables as C++ template heads and arguments see them: the
    arguments a reference omits or writes higher-kinded, how many a type is
    written with, the dictionary parameters a signature declares, the
    substitution a body's annotations resolve its variables by, and the
    carrier a template argument abstracts over.  Below type conversion. *)

open Common
open Names
open Core_util
open Util
open Translation_state
open Type_util
open Core_query

module IntSet = Escape.IntSet

(* [ref_is_skipped] and [core_ret_is_skipped] live in {!Type_util}, which
   {!Method_registry} also asks. *)

(* {!Type_util.core_type_is_instance} works the answer out; a caller with a
   global asks {!ref_is_instance} and one with a binder asks
   {!Core_query.binder_is_instance}. *)

(** Collect [Core.Binder_name.Source.t]s for typeclass-typed parameters in a Core arrow type.

    Only a parameter whose class Crane kept: each becomes a concept-constrained
    template parameter, and one whose class was skipped has nothing to be
    constrained by.  A skipped instance still has to be recognised as one where
    it is {e used} -- see {!Core_query.binder_is_instance}. *)
let collect_typeclass_param_ids ty =
  let rec aux acc i = function
    | Core.Type.Arrow {parameter = t1; result = t2} ->
      if parameter_role t1 = Dictionary then
        aux (tc_instance_id i :: acc) (i + 1) t2
      else
        aux acc i t2
    | _ -> List.rev acc
  in
  match ty with Core.Type.Arrow _ -> aux [] 0 ty | _ -> []

(** A type variable that really denotes an associated type of a type-class
    instance parameter: [tvar] stands for [typename <instance>::<field>]. *)
type hkt_tvar_position = {
  tvar : int;  (** the Core type variable's index *)
  instance : Cpp_ir.Lowered.Type.t;  (** always an {!Cpp_ir.Type.Instance} *)
  field : Id.t;  (** the class's type parameter the variable fills *)
}

(** The type variables of a Core arrow type that stand for a higher-kinded
    class parameter: [mret : forall M, Mon M -> forall A, A -> M A] passes the
    variable for [M A] as the type-constructor argument of its [Mon]
    parameter.  Such a variable is not a C++ template parameter but the
    instance's associated type — see {!Table.get_ind_hkt_params}.

    Instance parameters are numbered as [Gen_functions.gen_dfun] numbers them --
    it walks the binders innermost first, so the source-{e last} instance is
    [_tcI0] -- or, with [~source_order], as an instance struct numbers its
    own parameters, source-first.  With one instance the two orders coincide;
    with two they do not, and a signature numbered the other way swaps the
    functors. *)
let hkt_tvar_positions_of_type ?(source_order = false) ty =
  let last = List.length (collect_typeclass_param_ids ty) - 1 in
  let number i = if source_order then i else last - i in
  let rec go i acc = function
    | Core.Type.Arrow {parameter = Core.Type.Global_app {head = class_ref; type_arguments = type_args; _};
                       result = rest}
      when Table.is_typeclass class_ref ->
      let ip_vars = Table.get_ind_ip_vars class_ref in
      let acc =
        List.fold_left
          (fun acc pos ->
            match (List.nth_opt type_args pos, List.nth_opt ip_vars pos) with
            | ( Some (Core.Type.Variable {variable = j; _} | Core.Type.Variable_app {head = j; _}),
                Some var_name ) ->
              { tvar = j;
                instance =
                  Cpp_ir.Type.Instance (tc_instance_id (number i), class_ref);
                field = var_name }
              :: acc
            | _ -> acc )
          acc
          (Table.get_ind_hkt_params class_ref)
      in
      go (i + 1) acc rest
    | Core.Type.Arrow {result = rest; _} -> go i acc rest
    | _ -> acc
  in
  go 0 [] ty

(** Why [r]'s convention declares no C++ template parameter for its scheme
    variable [v], if it does not ({!Callable_abi.omission}): asked once, by
    the planner, and recorded in [r]'s plan for its calls to read.

    A variable standing for a higher-kinded class parameter has none: it is
    the instance's associated type, and it is always erased, which would
    otherwise make [filter_erased_type_args] drop the real type arguments
    alongside it.  Nor, in a type mentioning one, has a variable the type
    does not mention at all. *)
let type_arg_omission r =
  match find_type_opt r with
  | None -> fun _ -> None
  | Some ty -> (
    match List.map (fun p -> p.tvar) (hkt_tvar_positions_of_type ty) with
    | [] -> fun _ -> None
    | hkt ->
      let occurring = collect_tvars_set IntSet.empty ty in
      fun v ->
        let i = Core.Scheme.Var.ordinal v in
        if List.mem i hkt then Some Callable_abi.Class_carrier
        else if IntSet.is_empty occurring || IntSet.mem i occurring then None
        else Some Callable_abi.Unmentioned )

(** [ty] with every family variable written applied taken back to the bare
    variable: a plain family is declared without its index. *)
let deapply_family_variables : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t =
  Cpp_ir.Types.map (function Apply ((Variable _ as v), _) -> v | t -> t)

(** The number of type parameters [g] is written with in C++: the promoted
    variables it leads with ({!Table.promoted_type_params}), then an inductive's
    parameters or the variables of a type alias's body.  A family alias under
    a [Params] section is [BotE<ptr, X>], and [BotE<ptr>] is one short. *)
let written_arity g =
  let promoted = List.length (Table.promoted_type_params g) in
  match g with
  | GlobRef.IndRef (kn, _) ->
    Option.map (( + ) promoted) (Table.get_ind_num_param_vars_opt kn)
  | GlobRef.ConstRef kn ->
    Option.map
      (fun body -> promoted + Core_util.type_maxvar body)
      (Table.lookup_typedef_unchecked kn)
  | _ -> None

(** Whether [t] is a type written with fewer arguments than it has
    parameters -- all a type-level lambda leaves once extraction writes it as
    its head ([fun T => list (box T)] as a bare [list]), or an alias carrier
    ([texp]) passed as its name.  At a plain position that is no type at
    all. *)
let under_applied_ind (t : Cpp_ir.Lowered.Type.t) =
  match t with
  | Entity_application (g, args, _) | In_namespace (_, Entity_application (g, args, _)) -> (
    match written_arity g with
    | Some n -> List.length args < n
    | None -> false )
  | _ -> false

(** [t], a type {!under_applied_ind} says is short of arguments, applied
    at [std::any] for each one missing: a family at an erased index. *)
let saturate_at_any (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  let pad g args =
    match written_arity g with
    | Some n -> args @ List.init (n - List.length args) (fun _ : Cpp_ir.Lowered.Type.t -> Any)
    | None -> args
  in
  match t with
  | Entity_application (g, args, es) -> Entity_application (g, pad g args, es)
  | In_namespace (ns, Entity_application (g, args, es)) -> In_namespace (ns, Entity_application (g, pad g args, es))
  | t -> t

(** Build Core.Type.Variable i -> concrete_type substitution by unifying two Core types
    structurally. Walks both types in parallel; when one side has Core.Type.Variable i and the
    other has a concrete type, records the mapping. Conflicting mappings are
    discarded. *)
let build_tvar_subst_from_unify ty_with_tvars ty_concrete =
  let seen = Hashtbl.create 8 in
  let rec unify t1 t2 =
    match (t1, t2) with
    | (Core.Type.Variable {variable = i; _}), _ when not (has_tvar t2) ->
      ( match Hashtbl.find_opt seen i with
      | None -> Hashtbl.replace seen i (Some t2)
      | Some (Some _) -> Hashtbl.replace seen i None
      | Some None -> () )
    | _, (Core.Type.Variable {variable = i; _}) when not (has_tvar t1) ->
      ( match Hashtbl.find_opt seen i with
      | None -> Hashtbl.replace seen i (Some t1)
      | Some (Some _) -> Hashtbl.replace seen i None
      | Some None -> () )
    | Core.Type.Arrow {parameter = a1; result = b1}, Core.Type.Arrow {parameter = a2; result = b2} ->
      unify a1 a2;
      unify b1 b2
    | Core.Type.Global_app {type_arguments = args1; _}, Core.Type.Global_app {type_arguments = args2; _}
      when List.length args1 = List.length args2 -> List.iter2 unify args1 args2
    | Core.Type.Meta {contents = Some t}, other
     |other, Core.Type.Meta {contents = Some t} -> unify t other
    | _ -> ()
  in
  unify ty_with_tvars ty_concrete;
  Hashtbl.fold
    (fun i v acc ->
      match v with
      | Some ty -> (i, ty) :: acc
      | None -> acc )
    seen
    []

(** Collect all types that should be unified with the top-level function type.
    Returns a list of types to unify pairwise with the top-level type:
    - The arrow type reconstructed from Core.Expr.Lambda annotations
    - The type annotation on the Core.Expr.Fixpoint binding (if present)
    - The arrow type from the Core.Expr.Fixpoint's inner function body *)
let collect_body_types_for_unify body =
  let types = ref [] in
  let rec from_lams = function
    | Core.Expr.Lambda {parameter_type = ty; body = inner; _} ->
      Core.Type.Arrow {parameter = ty; result = from_lams inner}
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
      Array.iter (fun (_, ty) -> types := ty :: !types) ids;
      Array.iter (fun f -> types := from_lams f :: !types) funs;
      Core.Type.Unknown
    | _ -> Core.Type.Unknown
  in
  let outer = from_lams body in
  outer :: !types

(** Resolve Tvars in the body by unifying body type annotations with the
    top-level type. Only applied when the top-level type is fully concrete (no
    Tvars, no unresolved metas). Returns the (possibly substituted) body. *)
let resolve_body_tvars b ty =
  let ty = type_simpl ty in
  if has_tvar ty then
    b (* top-level type is polymorphic, don't touch the body *)
  else
    let body_types = collect_body_types_for_unify b in
    let tvar_subst =
      List.concat_map (fun bt -> build_tvar_subst_from_unify bt ty) body_types
    in
    let tvar_subst =
      List.fold_left
        (fun acc (i, t) -> if List.mem_assoc i acc then acc else (i, t) :: acc)
        []
        tvar_subst
    in
    match tvar_subst with
    | [] -> b
    | _ -> map_types_in_ast (subst_tvars_type tvar_subst) b

(** Create a substitution function for extra type variables in CppIR types:
    an index in [extra_tvar_map] becomes its named variable, and one of the
    containing inductive's own is left for [tvar_subst_stmt].

    @param num_ind_vars    number of type vars of the containing inductive/record
    @param extra_tvar_map  mapping from Core.Type.Variable index to the name of an extra type var *)
let make_subst_extra_tvars num_ind_vars extra_tvar_map =
  let rec subst (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
    match t with
    | Variable (Index (i, None)) when List.mem_assoc i extra_tvar_map -> Variable (Named (List.assoc i extra_tvar_map))
    | Variable (Index (i, None)) when i >= 1 && i <= num_ind_vars -> Variable (Index (i, None))
    | Function (dom, cod) -> Function (List.map subst dom, subst cod)
    | Shared_pointer t -> Shared_pointer (subst t)
    | Entity_application (r, args, e) -> Entity_application (r, List.map subst args, e)
    | Reference (k, t) -> Reference (k, subst t)
    | Const t -> Const (subst t)
    | Variant (k, tys) -> Variant (k, List.map subst tys)
    | In_namespace (r, t) -> In_namespace (r, subst t)
    | Member (t, id) -> Member (subst t, id)
    | t -> t
  in
  subst

(** [abstract_cpp_type ~over ty] is [ty] with every occurrence of [over]
    -- a type variable compared by its index -- replaced by the carrier
    parameter (printed as the {!Cpp_print.ctor_alias_tvar} sentinel): the type
    constructor whose application to [over] is [ty], or [None] where [over]
    does not occur, so that there is no such constructor to name. *)
let abstract_cpp_type ~(over : Cpp_ir.Lowered.Type.t) (ty : Cpp_ir.Lowered.Type.t) =
  let fired = ref false in
  (* Never descending into a [decltype]: comparing two expressions raises on
     the closures one can hold. *)
  let same (a : Cpp_ir.Lowered.Type.t) (b : Cpp_ir.Lowered.Type.t) =
    match (a, b) with
    | (Decay (Type_of _) | Type_of _), _ | _, (Decay (Type_of _) | Type_of _) -> false
    | Variable (Index (i, _)), Variable (Index (j, _)) -> i = j
    | Variable (Named x), Variable (Named y) -> Id.equal x y
    | _ -> a = b
  in
  let abstracted =
    Cpp_ir.Types.map
      (fun t ->
        if same t over then (
          fired := true;
          Carrier_parameter )
        else t )
      ty
  in
  if !fired then Some abstracted else None

(** Mark the template arguments of [g] that its declaration spells
    [template <typename> class].  Such a position takes a bare template name
    ([wrapped<List, uint64_t>]), never an instantiation, so every site that
    spells an instantiation of [g] -- its type, its factory calls, and the
    constructor structs a match qualifies -- has to agree on this. *)
let apply_hkt_tyctors cx g (temps : Cpp_ir.Lowered.Type.t list) : Cpp_ir.Lowered.Type.t list =
  (* A template-template position takes a {e unary} constructor, and what
     reaches it may be an application of more than one argument: Rocq's
     [TFunctor (fun T => two T (FnBody T))] normalises to [two] applied to
     both, with the binder gone.  Naming that head alone spells a constructor
     of the wrong arity, and the declaration it appears in does not compile.

     Putting the binder back is what the position wants, and the printer
     already mints an alias template for a body carrying the sentinel
     ({!abstract_cpp_type}).  The argument the position varies in is
     the leading one -- the class applies its carrier to the traversed type,
     and this idiom writes that type first.

     The unary case goes through the same rule and comes out unchanged:
     [box<_CraneTcArg>] is a head plus the sentinel, which the printer
     recognises and prints as the bare name. *)
  let rec abstract_leading_arg (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
    match t with
    (* A qualification is spelling: an external carrier ([ITree]'s [itree])
       arrives wrapped, and is abstracted inside the wrapper. *)
    | In_namespace (ns, inner) -> In_namespace (ns, abstract_leading_arg inner)
    | t ->
    let args =
      match t with
      (* A custom mapping is excluded: its replacement text says for itself
         which argument the C++ template varies in, and that is not in general
         the leading one -- [itree]'s is its last.  The printer substitutes the
         sentinel through the mapping rather than into the argument list. *)
      | Entity_application (g, args, _) when not (Table.is_custom g) -> args
      | Named (_, args) | External (_, args) | Apply (_, args) -> args
      | _ -> []
    in
    (* A partial application -- [stateT S (itree E)], the carrier [itree E]
       -- varies in the argument eta-expansion appended, an unknown type
       ([Topaque], or [std::any]): the last such, by position, since an
       erased argument elsewhere may be spelled the same.  Where there is
       none, the leading one. *)
    let hole =
      List.fold_left
        (fun (i, found) a ->
          (i + 1, match (a : Cpp_ir.Lowered.Type.t) with Obligation Opaque_type | Any -> Some i | _ -> found) )
        (0, None) args
      |> snd
    in
    let with_sentinel_at k : Cpp_ir.Lowered.Type.t =
      let args =
        List.mapi
          (fun i a -> if i = k then (Carrier_parameter : Cpp_ir.Lowered.Type.t) else a)
          args
      in
      match t with
      | Entity_application (g, _, es) -> Entity_application (g, args, es)
      | Named (id, _) -> Named (id, args)
      | External (id, _) -> External (id, args)
      | Apply (h, _) -> Apply (h, args)
      | t -> t
    in
    match args with
    | over :: _ :: _ -> (
      (* Only a constructor of arity above one needs abstracting.  A unary one
         is already a head plus its argument, which the printer cuts to the
         bare name; substituting the sentinel there would hand it a body it
         reads as an abstraction rather than an application, and it would mint
         an alias for a template that can simply be named. *)
      match hole with
      | Some k when k > 0 -> with_sentinel_at k
      | _ -> (
        match abstract_cpp_type ~over t with Some b -> b | None -> t ) )
    | _ -> t
  in
  List.mapi
    (fun i t ->
      if Table.is_hkt_ind_param g i then (Type_constructor (abstract_leading_arg t) : Cpp_ir.Lowered.Type.t)
      else
        match t with
        | Apply ((Variable tv as head), _)
          when Table.is_phantom_type_param g i
               || Option.cata (is_current_typename_var cx) false
                    (match tv with Index (_, n) -> n | Named x -> Some x) ->
          (* The application cannot be written, so the head alone stands for
             it -- which is all a phantom position reads anyway, and all an
             erased family has left to say.

             The deciding fact is the {e variable's} kind in the head this
             declaration is being given, not the position's: the first branch
             already took every position [g] made a template, so what is left
             is a plain [typename], and a plain [typename] is where an applied
             template-template parameter belongs ([List::list<T1<std::any>>]).
             Stripping there is what breaks it.  A parameter the declaration
             spells [typename] is the opposite case: it is neither phantom nor
             higher-kinded, and writing the application is what made two
             readings disagree about its kind. *)
          head
        | _ -> t )
    temps

(** The name a type variable carries in [tvars], where it has one.  Core
    numbers them from one, and a scope shorter than the type -- a declaration
    read before its own quantifiers are in hand -- simply leaves the variable
    unnamed rather than being an error. *)
let tvar_name_at tvars i =
  if i >= 1 then List.nth_opt tvars (pred i) else None
