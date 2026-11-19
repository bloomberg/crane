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

(*i*)
open Util
open Names
open Libnames
open Table
(*i*)

(** {2 Exceptions} *)

exception Found

exception Impossible

(** {1 Generic traversals of Core types}

    Every traversal below sees through a resolved meta and visits every child,
    a [Core.Type.Variable_app]'s arguments as much as a [Core.Type.Global_app]'s.  A walk written by hand has to
    remember both, and several did not. *)

module IntSet = Stdlib.Set.Make (Stdlib.Int)

let rec core_resolve = function
  | Core.Type.Meta {contents = Some t} -> core_resolve t
  | t -> t

let core_type_children = function
  | Core.Type.Arrow {parameter = a; result = b} -> [a; b]
  | Core.Type.Global_app {type_arguments = l; _} | Core.Type.Variable_app {arguments = l; _} -> l
  | _ -> []

let rec exists_core_type p t =
  let t = core_resolve t in
  p t || List.exists (exists_core_type p) (core_type_children t)

let rec fold_core_type f acc t =
  let t = core_resolve t in
  List.fold_left (fold_core_type f) (f acc t) (core_type_children t)

let rec map_core_type f t =
  match core_resolve t with
  | Core.Type.Arrow {parameter = a; result = b} ->
    f (Core.Type.Arrow {parameter = map_core_type f a; result = map_core_type f b})
  | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = e} ->
    f (Core.Type.Global_app {head = r; type_arguments = List.map (map_core_type f) l; index_arguments = e})
  | Core.Type.Variable_app {head = i; arguments = l} ->
    f (Core.Type.Variable_app {head = i; arguments = List.map (map_core_type f) l})
  | t -> f t

let core_tvars t =
  fold_core_type
    (fun s -> function Core.Type.Variable {variable = i; _}
      | Core.Type.Variable_app {head = i; _} -> IntSet.add i s | _ -> s)
    IntSet.empty t

(** {1 Names operations} *)

let anonymous_name = Id.of_string "x"

let dummy_name = Id.of_string "_x"

let anonymous = Core.Binder_name.Source anonymous_name

(** Converts a Rocq [Name.t] to an identifier, mapping an anonymous name and
    [dummy_name] to [anonymous_name]. *)
let id_of_name = function
  | Name.Anonymous -> anonymous_name
  | Name.Name id when Id.equal id dummy_name -> anonymous_name
  | Name.Name id -> id

(** Move a name out of the space Crane reserves for the names it invents
    itself -- the loopified frames ([_frame], [_call], [_stack], [_result])
    and the generated members -- by carrying its leading underscores to the
    end.  C++ reserves [_X] at global scope to the implementation anyway.
    Returns the name unchanged when it does not start with an underscore, when
    it is nothing but underscores, or when carrying them would leave a digit in
    front -- [_0] must not become [0_], which is no identifier at all.  That
    last case needs no rotation anyway: Crane invents no name of the form
    [_<digit>], so [_0] has nothing to collide with. *)
let unreserve_leading_underscore s =
  let n = String.length s in
  let i = ref 0 in
  while !i < n && s.[!i] = '_' do
    incr i
  done;
  let is_digit c = c >= '0' && c <= '9' in
  if !i = 0 || !i = n || is_digit s.[!i] then s
  else Generated_name.separate_underscores (String.sub s !i (n - !i) ^ "_")

(* The prefix of a {!temporary_id}, in the reserved space. *)
let temporary_prefix = "_tmp"

let temporary_id n = Id.of_string (temporary_prefix ^ string_of_int n)

let is_temporary_id id = String.starts_with ~prefix:temporary_prefix (Id.to_string id)

(** Converts an [Core.Binder_name.t] to an [Core.Binder_name.Source.t].  The binder comes from the Rocq
    source, so a leading underscore is moved to the end: that spelling belongs
    to the names Crane invents for itself (see
    {!unreserve_leading_underscore}).  A {!temporary_id} keeps its reserved
    name. *)
let id_of_binder_name =
  let unreserve id =
    Id.of_string (unreserve_leading_underscore (Id.to_string id))
  in
  function
  | Core.Binder_name.Anonymous -> dummy_name
  | Core.Binder_name.Source id -> unreserve id
  | Core.Binder_name.Generated id when is_temporary_id id -> id
  | Core.Binder_name.Generated id -> unreserve id

let tmp_id = function
  | Core.Binder_name.Source id -> Core.Binder_name.Generated id
  | a -> a

let is_tmp = function
  | Core.Binder_name.Generated _ -> true
  | _ -> false

(** {1 Operations upon Core types (with meta)} *)

let meta_count = ref 0

(** Metavariables standing for an application whose head is itself an
    unresolved metavariable, keyed by that head and the arguments.  See
    {!apply_core_type}. *)
let pending_applications : (Core.Extracted.Meta.t * Core.Type.extracted list * Core.Type.extracted) list ref = ref []

(** An open annotation standing for an application whose head is an open
    annotation, keyed by the head's id and the arguments, which may be of
    either phase. *)
type pending_open = Pending_open : int * 'p Core.Type.at list * Core.Open.t -> pending_open

(** The {!pending_open} applications made so far. *)
let pending_opens : pending_open list ref = ref []

let reset_meta_count () =
  meta_count := 0;
  pending_applications := [];
  pending_opens := []

let preserving_meta_supply f =
  let count = !meta_count and pending = !pending_applications and opens = !pending_opens in
  Fun.protect
    ~finally:(fun () ->
      meta_count := count;
      pending_applications := pending;
      pending_opens := opens )
    f

(** Creates a fresh type metavariable for unification.  Once the program is
    frozen nothing can solve one, so what is made instead is the open
    annotation an unsolved metavariable becomes ({!Core.Type.Open}). *)
let new_meta _ : Core.Type.extracted =
  incr meta_count;
  if Core.Extracted.Meta.is_frozen () then Core.Type.Open (Core.Open.fresh !meta_count)
  else Core.Type.Meta (Core.Extracted.Meta.fresh !meta_count)

(** A fresh open annotation, which a type of any phase may hold: what
    {!new_meta} makes once the program is frozen. *)
let new_open () =
  incr meta_count;
  Core.Type.Open (Core.Open.fresh !meta_count)

(** {!new_meta} at the phase of the cell [m], which is extracted. *)
let new_meta_like (m : 'p Core.Extracted.Meta.cell) : 'p Core.Type.at =
  incr meta_count;
  if Core.Extracted.Meta.is_frozen () then Core.Type.Open (Core.Open.fresh !meta_count)
  else Core.Type.Meta (Core.Extracted.Meta.fresh_like m !meta_count)

(** Structural equality on Core types, of any two phases. *)
let rec eq_core_type : 'p 'q. 'p Core.Type.at -> 'q Core.Type.at -> bool =
 fun t1 t2 ->
  let rec eq_list : 'p 'q. 'p Core.Type.at list -> 'q Core.Type.at list -> bool =
   fun l1 l2 ->
    match (l1, l2) with
    | [], [] -> true
    | a :: l1, b :: l2 -> eq_core_type a b && eq_list l1 l2
    | _ -> false
  in
  match (t1, t2) with
  | Core.Type.Arrow {parameter = tl1; result = tr1}, Core.Type.Arrow {parameter = tl2; result = tr2} ->
    eq_core_type tl1 tl2 && eq_core_type tr1 tr2
  | Core.Type.Global_app {head = gr1;
                          type_arguments = t1; _}, Core.Type.Global_app {head = gr2; type_arguments = t2; _} ->
    GlobRef.CanOrd.equal gr1 gr2 && eq_list t1 t2
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                        variable = i1}, Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i2} ->
    Int.equal i1 i2
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid;
                        variable = i1}, Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = i2} ->
    Int.equal i1 i2
  | Core.Type.Variable_app {head = i1; arguments = l1}, Core.Type.Variable_app {head = i2; arguments = l2} ->
    Int.equal i1 i2 && eq_list l1 l2
  | Core.Type.Meta m1, Core.Type.Meta m2 -> eq_core_meta m1 m2
  | Core.Type.Hole h1, Core.Type.Hole h2 -> Int.equal h1 h2
  | Core.Type.Open o1, Core.Type.Open o2 -> Int.equal (Core.Open.id o1) (Core.Open.id o2)
  | Core.Type.Erased k1, Core.Type.Erased k2 -> k1 == k2
  | Core.Type.Unknown, Core.Type.Unknown -> true
  | Core.Type.Axiom, Core.Type.Axiom -> true
  | Core.Type.String, Core.Type.String -> true
  | ( ( Core.Type.Arrow _
      | Core.Type.Global_app _
      | Core.Type.Variable _
      | Core.Type.Variable_app _
      | Core.Type.Meta _
      | Core.Type.Hole _
      | Core.Type.Open _
      | Core.Type.Erased _
      | Core.Type.Unknown
      | Core.Type.Axiom
      | Core.Type.String ),
      _ ) -> false

and eq_core_meta : 'p 'q. 'p Core.Extracted.Meta.cell -> 'q Core.Extracted.Meta.cell -> bool =
 fun m1 m2 ->
  Int.equal m1.id m2.id
  && match (m1.contents, m2.contents) with
     | None, None -> true
     | Some a, Some b -> eq_core_type a b
     | _ -> false

(** Whether a type carries a [Core.Type.Unknown] hole.  See {!fill_placeholders}. *)
let type_has_hole t = exists_core_type (function Core.Type.Unknown -> true | _ -> false) t

(* Sees through a resolved meta, as [type_has_hole] does: one that answered
   "there is a hole" for a hole this could not reach filled nothing. *)
let fill_type_hole a = map_core_type (function Core.Type.Unknown -> a | t -> t)

(* [rpre], a reversed argument list, without its leading run of at most [n]
   placeholders. *)
let rec drop_placeholders rpre n =
  match (rpre, n) with
  | Core.Type.Unknown :: rest, n when n > 0 -> drop_placeholders rest (n - 1)
  | _ -> rpre

(* The 0-based positions of the parameters the type alias [r] applies in
   its definition, as far as that definition has been extracted: each is a
   type constructor, handed over eta-expanded like any other -- [stateT bool
   (itree noE)] arrives as [stateT(bool, itree(noE, _), _)] -- so a hole
   inside the argument there is that constructor's own placeholder, not the
   binder of a type-level lambda.  A generated inductive's higher-kinded
   parameter is different: it holds the carrier already applied at the
   element, the binder in it. *)
let constructor_params = function
  | GlobRef.ConstRef kn -> (
    match Table.lookup_typedef_unchecked kn with
    | Some body ->
      fold_core_type
        (fun acc -> function
          | Core.Type.Variable_app {head = j; _} when not (List.mem (j - 1) acc) -> (j - 1) :: acc
          | _ -> acc)
        [] body
    | None -> [] )
  | GlobRef.IndRef _ | GlobRef.ConstructRef _ | GlobRef.VarRef _ -> []

(* See [core_util.mli]. *)
let writes_binder ?(generated = true) ?(constructors = []) args =
  let binder = if generated then type_has_hole else ( = ) Core.Type.Unknown in
  List.rev (drop_placeholders (List.rev args) (List.length args))
  |> List.filteri (fun i _ -> not (List.mem i constructors))
  |> List.exists binder

(** [fill_placeholders pre args] applies a head already carrying [pre] to
    [args].

    Extraction eta-expands a type constructor passed as an argument -- what
    stands for [M] is [M _], and for [AE +' BE] it is [sum1 AE BE _], the last
    argument a placeholder extraction could not name -- so applying such a head
    to a real argument does not extend the application, it fills the
    placeholder.  Appending instead would give the constructor one argument per
    substitution it passes through: [m<std::any, A>] for an [m] that takes one,
    [Sum1<AE, BE, std::any, std::any>] for a [Sum1] that takes three.

    The placeholders are not always trailing.  A carrier that is a type-level
    lambda -- [fun T => holder T (box T)] -- has no Core spelling, and what
    extraction leaves is the body with every occurrence of the binder written
    as [Core.Type.Unknown]: [holder[_, box[_]]].  Applying that is filling each hole,
    not appending, which would give [holder] a third argument it does not
    take.

    That reading of a non-trailing hole belongs to a {e generated} head, whose
    higher-kinded parameters hold the carrier already applied at the element
    (see {!Core_to_cpp.Records.gen_record_cpp}).  A custom mapping takes a family at a
    plain [typename], its index erased -- [sum1 => "Sum1"] -- so a hole
    inside such an argument is that family's own placeholder, and filling it
    would apply the family a second time when it is applied for real:
    [sum1 (CE _) (FailE _) _] nested in [CE +' FailE +' ...] became
    [Sum1<CE, FailE, X, X>].  [~generated:false] says the head is such a
    mapping.  Its own arguments' placeholders are nested; a hole standing as
    one of its arguments, short of the trailing run, can only be the binder:
    [fun T => T * box T] arrives as [prod[_, box[_]]]. *)
let fill_placeholders ?(generated = true) ?(constructors = []) pre args =
  let kept = List.rev (drop_placeholders (List.rev pre) (List.length args)) in
  (* The trailing run of placeholders is the eta-expansion, whichever part of
     it these arguments reach; a hole anywhere else is a binder the lambda
     body writes.  [stateT S m] arrives as [stateT(S, m _, _)] -- the record's
     monad parameter is applied to the element, so the binder is written
     twice, and dropping the trailing occurrence would leave the other
     unfilled and the glob an argument short.  Where such a hole survives, the
     application is a fill of every occurrence at once, and one argument is
     all such a spelling can say where to put. *)
  match args with
  | [arg] when writes_binder ~generated ~constructors pre ->
    List.mapi (fun i a -> if List.mem i constructors then a else fill_type_hole arg a) pre
  | _ -> kept @ args

(* An unsolved head [id] applied to [args].  The head is not known yet, and a
   pending application of a metavariable is not representable.  Dropping the
   arguments would make [M nat] and [M (nat -> nat)] the very same
   metavariable, so that unifying one of them against a concrete carrier
   resolves the other at the wrong instantiation.  Stand for the application
   by an unknown of its own -- but the same one for the same head and
   arguments, so that the two occurrences of [M B] in [bind]'s type still
   unify with each other.  The head is kept, not its number, for what the
   unknown is later unified with to be read through it
   ({!discharge_pending_applications}). *)
let pending_application (head : Core.Extracted.Meta.t) args =
  match
    List.find_opt
      (fun ((h : Core.Extracted.Meta.t), a, _) -> Int.equal head.id h.id && List.equal eq_core_type a args)
      !pending_applications
  with
  | Some (_, _, u) -> u
  | None ->
    let u = new_meta () in
    pending_applications := (head, args, u) :: !pending_applications;
    u

(** {!pending_application} for the open annotation [id] as the head: an
    open annotation of its own, the same for the same head and arguments. *)
let pending_open_application id args =
  match
    List.find_map
      (fun (Pending_open (id', a, o)) ->
        if Int.equal id id' && List.length a = List.length args && List.for_all2 eq_core_type a args then Some o
        else None )
      !pending_opens
  with
  | Some o -> Core.Type.Open o
  | None ->
    incr meta_count;
    let o = Core.Open.fresh !meta_count in
    pending_opens := Pending_open (id, args, o) :: !pending_opens;
    Core.Type.Open o

(** Apply a type to [args], contracting the application when the head is
    known.  [Core.Type.Variable_app] is a redex: its head is a type variable, so substituting
    that variable with a concrete type constructor reduces it.

    A head that carries no arguments of its own ([Core.Type.Erased], [Core.Type.Unknown]) absorbs
    them, which is what a carrier erased by extraction must do. *)
let rec apply_core_type : type p. p Core.Type.at -> p Core.Type.at list -> p Core.Type.at =
 fun head args ->
  match args with
  | [] -> head
  | _ -> (
    match head with
    | Core.Type.Variable {variable = j; _} -> Core.Type.Variable_app {head = j; arguments = args}
    | Core.Type.Variable_app {head = j; arguments = pre} ->
      Core.Type.Variable_app {head = j; arguments = fill_placeholders pre args}
    (* An inductive already applied to every parameter takes nothing more
       by appending.  With no hole left it is a type: a family written
       applied at its index -- [sum1 e3 (...) X] substituted for the [E2] of
       [E2 X] -- is its own type.  With a hole in it, the application fills
       the hole, custom or not: [option (F _)], the carrier of [fun T =>
       option (F T)], applied to [V] is [option (F V)], not [option (F _) V]. *)
    | Core.Type.Global_app {head = (GlobRef.IndRef (kn, _) as r); type_arguments = pre; index_arguments = es}
      when (match Table.get_ind_num_param_vars_opt kn with
            | Some n -> List.length pre = n
            | None -> false)
           && not (List.exists (function Core.Type.Unknown -> true | _ -> false) pre) -> (
      match args with
      | [arg] when List.exists type_has_hole pre ->
        Core.Type.Global_app {head = r; type_arguments = List.map (fill_type_hole arg) pre; index_arguments = es}
      | _ -> head )
    | Core.Type.Global_app {head = r; type_arguments = pre; index_arguments = es} ->
      Core.Type.Global_app {head = r;
                            type_arguments = fill_placeholders ~generated:(not (Table.is_custom r))
                              ~constructors:(constructor_params r) pre args;
                            index_arguments = es}
    | Core.Type.Meta {contents = Some u} -> apply_core_type u args
    | Core.Type.Meta ({contents = None; phase = Core.Phase.Extracted; _} as m) -> pending_application m args
    | Core.Type.Open o -> pending_open_application (Core.Open.id o) args
    | Core.Type.Arrow _ when type_has_hole head -> (
      (* A carrier that is a type-level lambda has no Core spelling, so what
         extraction leaves is its body with the binder written as [Core.Type.Unknown]
         (see {!fill_placeholders}).  Where that body's head is an arrow there
         is no constructor to extend, and applying it is filling the hole:
         [Basics.Monads.stateT S m] unfolds to [S -> m (S * _)], and the
         method's own variable belongs in that hole.  Left unfilled the
         element position stays erased while everything around it is spelled,
         which is the [std::any] in a [pair<T1, std::any>] whose neighbour is
         concrete. *)
      match args with [a] -> fill_type_hole a head | _ -> head )
    | Core.Type.Unknown -> (
      (* The only heads extraction leaves unknown here are type constructors it
         could not name, and the one such constructor a class can be
         instantiated at is the identity ([fun A => A]): it reduces to its
         argument. *)
      match args with [a] -> a | _ -> Core.Type.Unknown )
    | _ -> head )


(** Substitutes each [Core.Type.Variable j] (either rigidity: rigidity constrains
    unification, not substitution) for which [f j] answers, leaving the
    others unchanged. *)
let type_subst_fun f t =
  let rec subst t =
    match t with
    | Core.Type.Variable {variable = j; _} -> ( match f j with Some u -> u | None -> t )
    | Core.Type.Variable_app {head = j; arguments = args} ->
      apply_core_type (subst (Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                variable = j})) (List.map subst args)
    | Core.Type.Meta {contents = None} -> t
    | Core.Type.Meta {contents = Some u} -> subst u
    | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = subst a; result = subst b}
    | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
      Core.Type.Global_app {head = r; type_arguments = List.map subst l; index_arguments = a}
    | a -> a
  in
  subst t

(** Simultaneously substitutes [[Core.Type.Variable 1; ...; Core.Type.Variable n]] by the types in [l]
    within Core type [t].  A variable out of range is left unchanged (promoted
    dependent-record variables). *)
let type_subst_list l t =
  type_subst_fun (fun j -> if j >= 1 then List.nth_opt l (j - 1) else None) t

(** Simultaneously substitutes [[|Core.Type.Variable 1; ...; Core.Type.Variable n|]] by the types in
    array [v] within Core type [t]. Type vars with indices > n are left unchanged
    (per-constructor existential type variables). *)
let type_subst_vect v t =
  let n = Array.length v in
  let rec subst t =
    match t with
    | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = j} when j >= 1 && j <= n -> v.(j - 1)
    (* Per-constructor type var, leave unchanged *)
    | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; _} -> t
    | Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = j} when j >= 1 && j <= n ->
      v.(j - 1) (* Rigidity constrains unification, not substitution *)
    | Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; _} -> t (* Per-constructor type var, leave unchanged *)
    | Core.Type.Variable_app {head = j; arguments = args} ->
      apply_core_type (subst (Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                variable = j})) (List.map subst args)
    | Core.Type.Meta {contents = None} -> t
    | Core.Type.Meta {contents = Some u} -> subst u
    | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = subst a; result = subst b}
    | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
      Core.Type.Global_app {head = r; type_arguments = List.map subst l; index_arguments = a}
    | a -> a
  in
  subst t

(** {2 From a type schema to a type. All [Core.Type.Variable] become fresh [Core.Type.Meta]} *)

let instantiate_prenex nb t = type_subst_vect (Array.init nb new_meta) t

(** {2 Replace all [Core.Type.Unknown] in a type with fresh [Core.Type.Meta]. This is used for
    existential type variables that were marked as Core.Type.Unknown during extraction.
    At use sites, we want fresh metas so they can unify with concrete types} *)

let instantiate_unknowns t =
  let rec subst t =
    match t with
    | Core.Type.Unknown -> new_meta ()
    | Core.Type.Meta {contents = None} -> t
    | Core.Type.Meta {contents = Some u} -> subst u
    | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = subst a; result = subst b}
    | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
      Core.Type.Global_app {head = r; type_arguments = List.map subst l; index_arguments = a}
    | a -> a
  in
  subst t

(** {2 Occur-check of a free meta in a type} *)

let rec type_occurs alpha t =
  match t with
  | Core.Type.Meta {id = beta; contents = None} -> Int.equal alpha beta
  | Core.Type.Meta {contents = Some u} -> type_occurs alpha u
  | Core.Type.Arrow {parameter = t1; result = t2} -> type_occurs alpha t1 || type_occurs alpha t2
  | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} -> List.exists (type_occurs alpha) l
  | Core.Type.Variable_app {arguments = l; _} -> List.exists (type_occurs alpha) l
  | Core.Type.Erased _
  | Core.Type.Variable _
  | Core.Type.Hole _
  | Core.Type.Open _
  | Core.Type.Axiom
  | Core.Type.Unknown
  | Core.Type.String -> false

(** {2 Most General Unificator} *)

type function_abbrevs = {body : 'p. GlobRef.t -> 'p Core.Type.at option}

(* The bodies of the type definitions standing for a function type, which
   extraction keeps as their names ({!type_expand_values}): [st A] where [st A
   := nat -> A * nat].  Unification unfolds one only where it meets the
   arrows it stands for. *)
let function_abbrevs = ref {body = (fun _ -> None)}

let set_function_abbrevs f = function_abbrevs := f

let rec mgu : type p. p Core.Type.at * p Core.Type.at -> unit = function
  | Core.Type.Meta (m : _ Core.Extracted.Meta.cell), Core.Type.Meta (m' : _ Core.Extracted.Meta.cell)
    when Int.equal m.id m'.id ->
    ()
  | Core.Type.Meta m, t | t, Core.Type.Meta (m : _ Core.Extracted.Meta.cell) ->
    ( match m.contents with
    | Some u -> mgu (u, t)
    | None when type_occurs m.id t -> raise Impossible
    | None ->
      Core.Extracted.Meta.solve m t;
      discharge_pending_applications () )
  (* Frozen, an open annotation unifies with itself alone. *)
  | Core.Type.Open o, Core.Type.Open o' when Int.equal (Core.Open.id o) (Core.Open.id o') -> ()
  | Core.Type.Arrow {parameter = a; result = b}, Core.Type.Arrow {parameter = a'; result = b'} ->
    mgu (a, a');
    mgu (b, b')
  | Core.Type.Global_app {head = r;
                          type_arguments = l;
                          index_arguments = a}, Core.Type.Global_app {head = r';
                                                                      type_arguments = l'; index_arguments = a'}
                                                                        when GlobRef.CanOrd.equal r r' ->
    if List.length l <> List.length l' then (
      Feedback.msg_debug
        Pp.(
          str "mgu: Global_app argument length mismatch for "
          ++ Printer.pr_global r
          ++ str ": "
          ++ int (List.length l)
          ++ str " vs "
          ++ int (List.length l') );
      (* Differing arity means the two applications cannot unify; falling
         through to [List.combine] would raise a bare [Invalid_argument]. *)
      raise Impossible );
    List.iter mgu (List.combine l l')
  | Core.Type.Erased _, Core.Type.Erased _ -> ()
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                        variable = i}, Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                           variable = j} when Int.equal i j -> ()
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid;
                        variable = i}, Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid;
                                                           variable = j} when Int.equal i j -> ()
  | Core.Type.Variable_app {head = i;
                            arguments = l}, Core.Type.Variable_app {head = j; arguments = l'} when Int.equal i j ->
    if List.length l <> List.length l' then raise Impossible;
    List.iter mgu (List.combine l l')
  | Core.Type.Unknown, Core.Type.Unknown -> ()
  | Core.Type.Axiom, Core.Type.Axiom -> ()
  | Core.Type.String, Core.Type.String -> ()
  | Core.Type.Global_app {head = r; type_arguments = l; _}, u when Option.has_some (!function_abbrevs.body r) ->
    mgu (type_subst_list l (Option.get (!function_abbrevs.body r)), u)
  | u, Core.Type.Global_app {head = r; type_arguments = l; _} when Option.has_some (!function_abbrevs.body r) ->
    mgu (u, type_subst_list l (Option.get (!function_abbrevs.body r)))
  | _ -> raise Impossible

(* An unknown standing for the application [M B] of an unsolved head
   ({!pending_application}) that is unified with [m C] -- a type variable
   applied, at as many arguments -- is that application read as [m B], so
   [B] is [C].  This is how a class method instantiated in a body generic in
   its monad -- [bind : m A -> (A -> m B) -> m B], given an [m T] -- finds
   that [A] is [T], the element type of the continuation's binder, which the
   dictionary, not naming [m], cannot say.  A head solved since stands for
   what it is solved to; only a head still unsolved, or solved to that same
   variable, is read so.  Each argument is unified on its own, so one that
   does not unify leaves the others found. *)
and discharge_pending_applications () =
  let rec resolved = function Core.Type.Meta {contents = Some t; _} -> resolved t | t -> t in
  let reads_as j (h : Core.Extracted.Meta.t) =
    match Option.map resolved h.contents with
    | None -> true
    | Some (Core.Type.Variable {variable = j'; _}) -> Int.equal j j'
    | Some _ -> false
  in
  List.iter
    (fun (h, args, u) ->
      match resolved u with
      | Core.Type.Variable_app {head = j; arguments = l} when List.length l = List.length args && reads_as j h ->
        List.iter2 (fun a c -> try mgu (a, c) with Impossible -> ()) args l
      | _ -> () )
    !pending_applications

(* Try to unify two types using mgu. Silently fails if unification is
   impossible. This mutably sets the contents of metavariables when
   successful. *)
let try_mgu t1 t2 = try mgu (t1, t2) with Impossible -> ()

let skip_typing () = is_extrcompute ()

(** Returns [true] if a type coercion ([Core.Expr.Coerce]) is needed because the two types
    in pair [p] cannot be unified. *)
let needs_magic p =
  if skip_typing () then
    false
  else
    try
      mgu p;
      false
    with Impossible -> true

(** [put_magic_if ~from ~into b a] wraps [a] in a coercion when [b] says one is
    needed.  Takes the two types explicitly because [needs_magic]'s pair is
    unordered ([mgu] is symmetric) while a backend needs to know which side
    the term is on and which side the context wants. *)
let put_magic_if ~from ~into b =
  if b then fun a -> Core.Expr.Coerce {source_type = from;
                                       target_type = into;
                                       value = a;
                                       occurrence = Core.Occurrence.fresh ()} else Fun.id

(** [put_magic ~from ~into a] wraps [a] in a coercion iff its own type [from]
    fails to unify with the type [into] its context requires. *)
let put_magic ~from ~into a = put_magic_if ~from ~into (needs_magic (from, into)) a

(** Checks if a Core expression can be generalized (polymorphic let). In C++,
    applications are excluded. *)
let generalizable a =
  lang () != Cpp
  ||
  match a with
  | Core.Expr.Apply _ -> false
  | _ -> true
(* Approximation. Safe in practice: well-typed Rocq cannot use the same
   let-binding at two distinct types, so over-generalization from non-app
   expressions cannot be triggered by valid Rocq input. *)

(** {1 Core type environment} *)

module Type_env = struct
  let meta_cmp (m : _ Core.Extracted.Meta.cell) (m' : _ Core.Extracted.Meta.cell) = compare m.id m'.id

  module Metaset = Set.Make (struct
    type t = Core.Extracted.Meta.t

    let compare = meta_cmp
  end)

  (* Main Type_env type. [env] is the real environment, whereas [free] (tries to)
     record the free meta variables occurring in [env]. *)

  type t = {
    env : (int * Core.Type.extracted) list;
    mutable free : Metaset.t;
  }

  (* Empty environment. *)

  let empty = {env = []; free = Metaset.empty}

  (* [get] returns a instantiated copy of the n-th most recently added type in
     the environment. *)

  let get type_env n =
    assert (List.length type_env.env >= n);
    let nb, t = List.nth type_env.env (n - 1) in
    instantiate_prenex nb t

  (* [find_free] finds the free meta in a type. *)

  let rec find_free set = function
    | Core.Type.Meta (m : _ Core.Extracted.Meta.cell) when Option.is_empty m.contents -> Metaset.add m set
    | Core.Type.Meta {contents = Some t} -> find_free set t
    | Core.Type.Arrow {parameter = a; result = b} -> find_free (find_free set a) b
    | Core.Type.Global_app {type_arguments = l; _} -> List.fold_left find_free set l
    | _ -> set

  (* The [free] set of an environment can be outdated after some unifications.
     [clean_free] takes care of that. *)

  let clean_free type_env =
    let rem = ref Metaset.empty
    and add = ref Metaset.empty in
    let clean (m : _ Core.Extracted.Meta.cell) =
      match m.contents with
      | None -> ()
      | Some u ->
        rem := Metaset.add m !rem;
        add := find_free !add u
    in
    Metaset.iter clean type_env.free;
    type_env.free <- Metaset.union (Metaset.diff type_env.free !rem) !add

  (* From a type to a type schema. If a [Core.Type.Meta] is still uninstantiated and does
     not appear among the free metas of [type_env], then it becomes a [Core.Type.Variable]. *)

  let generalization type_env t =
    let c = ref 0 in
    let map = ref (Int.Map.empty : int Int.Map.t) in
    let add_new i =
      incr c;
      map := Int.Map.add i !c !map;
      !c
    in
    let rec meta2var t =
      match t with
      | Core.Type.Meta {contents = Some u} -> meta2var u
      | Core.Type.Meta ({id = i} as m) ->
        ( try Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = (Int.Map.find i !map)}
          with Not_found ->
            if Metaset.mem m type_env.free then
              t
            else
              Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = (add_new i)} )
      | Core.Type.Arrow {parameter = t1; result = t2} -> Core.Type.Arrow {parameter = meta2var t1; result = meta2var t2}
      | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
        Core.Type.Global_app {head = r; type_arguments = List.map meta2var l; index_arguments = a}
      | Core.Type.Variable_app {head = i; arguments = l} ->
        Core.Type.Variable_app {head = i; arguments = List.map meta2var l}
      | t -> t
    in
    (!c, meta2var t)

  (* Adding a type in an environment, after generalizing. *)

  let push_gen type_env t =
    clean_free type_env;
    {env = generalization type_env t :: type_env.env; free = type_env.free}

  (* Adding a type with no [Core.Type.Variable], hence no generalization needed. *)

  let push_type type_env t = {env = (0, t) :: type_env.env; free = find_free type_env.free t}

  (* Adding a type with no [Core.Type.Variable] nor [Core.Type.Meta]. *)

  let push_std_type type_env t = {env = (0, t) :: type_env.env; free = type_env.free}
end

(** {1 Operations upon Core types (without meta)} *)

(** {2 Frozen instantiations} *)

(* From the one supply {!Global_use.infer_all} mints from too: two holes in
   one instantiation are filled by number. *)
let fresh_hole () = Core.Type.Hole (Core.Scheme.Hole.fresh ())

let freeze_types tys =
  let holes = Hashtbl.create 4 in
  let rec freeze = function
    | Core.Type.Meta {contents = Some t} -> freeze t
    | Core.Type.Meta {id; contents = None} -> (
      match Hashtbl.find_opt holes id with
      | Some h -> h
      | None ->
        let h = fresh_hole () in
        Hashtbl.add holes id h;
        h )
    | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = freeze a; result = freeze b}
    | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = args} ->
      Core.Type.Global_app {head = r; type_arguments = List.map freeze l; index_arguments = args}
    | Core.Type.Variable_app {head = i; arguments = l} ->
      Core.Type.Variable_app {head = i; arguments = List.map freeze l}
    | t -> t
  in
  List.map freeze tys

let rec type_holes acc = function
  | Core.Type.Hole h -> if List.mem h acc then acc else h :: acc
  | Core.Type.Arrow {parameter = a; result = b} -> type_holes (type_holes acc a) b
  | Core.Type.Global_app {type_arguments = l; _} | Core.Type.Variable_app {arguments = l; _} ->
    List.fold_left type_holes acc l
  | Core.Type.Meta {contents = Some t} -> type_holes acc t
  | _ -> acc

let rec type_has_meta = function
  | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
  | Core.Type.Meta {contents = Some _} -> true
  | Core.Type.Arrow {parameter = a; result = b} -> type_has_meta a || type_has_meta b
  | Core.Type.Global_app {type_arguments = l; _} | Core.Type.Variable_app {arguments = l; _} ->
    List.exists type_has_meta l
  | _ -> false

let rec fill_holes f = function
  | Core.Type.Hole h as t -> ( match f h with Some u -> u | None -> t )
  | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = fill_holes f a; result = fill_holes f b}
  | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = args} ->
    Core.Type.Global_app {head = r; type_arguments = List.map (fill_holes f) l; index_arguments = args}
  | Core.Type.Variable_app {head = i; arguments = l} ->
    Core.Type.Variable_app {head = i; arguments = List.map (fill_holes f) l}
  | Core.Type.Meta {contents = Some t} -> fill_holes f t
  | t -> t

module Partial = struct
  type 'p t = 'p Core.Type.at

  let instantiate inst ty =
    let scheme = Core.Scheme.Instantiation.scheme inst in
    type_subst_fun
      (fun j ->
        Option.bind (Core.Scheme.Var.of_tvar scheme j) (fun v ->
            match (Core.Scheme.Instantiation.slot inst v).solution with
            | Core.Scheme.Type u -> Some u
            | Core.Scheme.Identity -> None ) )
      ty

  let holes t = List.rev (type_holes [] t)
  let close t = if type_holes [] t = [] then Some t else None
  let resolve = fill_holes
end

(** {2 A global use's written type arguments, read by scheme variable} *)

(** A one-line rendering of a Core type, for diagnostics. *)
let rec debug_core_type = function
  | Core.Type.Arrow {parameter = a; result = b} -> "(" ^ debug_core_type a ^ " -> " ^ debug_core_type b ^ ")"
  | Core.Type.Global_app {head = r; type_arguments = []; _} -> Pp.string_of_ppcmds (GlobRef.print r)
  | Core.Type.Global_app {head = r; type_arguments = l; _} ->
    Pp.string_of_ppcmds (GlobRef.print r)
    ^ "(" ^ String.concat ", " (List.map debug_core_type l) ^ ")"
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i} -> "'" ^ string_of_int i
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = i} -> "'!" ^ string_of_int i
  | Core.Type.Variable_app {head = i; arguments = l} ->
    "'" ^ string_of_int i ^ "(" ^ String.concat ", " (List.map debug_core_type l) ^ ")"
  | Core.Type.Meta {contents = Some t} -> debug_core_type t
  | Core.Type.Meta {id; contents = None} -> "?" ^ string_of_int id
  | Core.Type.Open o -> "?" ^ string_of_int (Core.Open.id o)
  | Core.Type.Hole h -> "_" ^ string_of_int h
  | Core.Type.Erased Core.Erasure_reason.Type_argument -> "__type"
  | Core.Type.Erased Core.Erasure_reason.Proof -> "__prop"
  | Core.Type.Erased (Core.Erasure_reason.Configured_implicit _) -> "__implicit"
  | Core.Type.Unknown -> "unknown"
  | Core.Type.Axiom -> "axiom"
  | Core.Type.String -> "string"

(* A minted scheme is kept, so that every reference to [r] meets the same
   variables: one minted per call would make two readings of one callee's
   variables unequal.  A type re-registered at another arity mints anew. *)
let minted_schemes = State.cell State.Extraction GlobRef.Map.empty

let recorded_schema = function
  | GlobRef.ConstRef kn -> Table.constant_schema kn
  | _ -> None

let reference_scheme r =
  match recorded_schema r with
  | Some schema -> Some (Core.Schema.id schema)
  | None -> (
    match Table.inspect_type r {read = Core.Schema.max_tvar} with
    | exception Not_found -> None
    | arity -> (
      match GlobRef.Map.find_opt r !minted_schemes with
      | _ when arity = 0 -> None
      | Some id when Int.equal (Core.Scheme.Id.arity id) arity -> Some id
      | _ ->
        let id = Core.Scheme.Id.fresh r ~arity in
        minted_schemes := GlobRef.Map.add r id !minted_schemes;
        Some id ) )

let open_reference r =
  match reference_scheme r with
  | Some scheme -> Core.Global_use.infer_all r scheme
  | None -> Core.Global_use.monomorphic r

let self_reference r =
  match reference_scheme r with
  | Some scheme -> Core.Global_use.identity r scheme
  | None -> Core.Global_use.monomorphic r

let forwarding_use target =
  match reference_scheme target with
  | None -> Core.Global_use.monomorphic target
  | Some scheme ->
    let schema = recorded_schema target in
    Core.Global_use.polymorphic target
      (Core.Scheme.Instantiation.make scheme (fun v ->
           let own = Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = Core.Scheme.Var.ordinal v} in
           let source =
             match Option.bind schema (fun s -> Core.Schema.origin s v) with
             | Some b -> Core.Scheme.Written {binder = b.Core.Schema.binder; observed = Some own}
             | None -> Core.Scheme.Not_written
           in
           {Core.Scheme.solution = Core.Scheme.Type own; source} ) )

module Var_types = struct
  (* One scheme's variables from its first to the last spoken for, in
     order. *)
  type 'p t = (Core.Scheme.Var.t * 'p Core.Type.at) list

  let empty = []
  let is_empty t = t = []

  let through last f =
    match last with
    | None -> []
    | Some last ->
      List.filter_map
        (fun v -> if Core.Scheme.Var.compare v last <= 0 then Some (v, f v) else None)
        (Core.Scheme.Var.all (Core.Scheme.Var.owner last))

  let find t v =
    match t with
    | [] -> None
    | (w, _) :: _ ->
      if not (Core.Scheme.Id.equal (Core.Scheme.Var.owner v) (Core.Scheme.Var.owner w)) then
        invalid_arg "Core_util.Var_types.find: a variable of another scheme";
      List.find_map (fun (w, ty) -> if Core.Scheme.Var.equal v w then Some ty else None) t

  let find_tvar t i = Core.Scheme.Var.assoc_tvar i t

  let bindings t = t
  let apply t ty = type_subst_fun (find_tvar t) ty

  let equal x y =
    List.equal (fun (v, a) (w, b) -> Core.Scheme.Var.equal v w && eq_core_type a b) x y
end

let last_var vars =
  List.fold_left
    (fun last v ->
      match last with
      | Some w when Core.Scheme.Var.compare w v >= 0 -> last
      | _ -> Some v )
    None vars

let written_type_args use =
  let evidence = Core.Global_use.written_evidence use in
  Var_types.through (last_var (List.map fst evidence)) (fun v ->
      match List.find_opt (fun (w, _) -> Core.Scheme.Var.equal v w) evidence with
      | Some (_, t) -> t
      | None -> Core.Type.Erased Core.Erasure_reason.Type_argument )

let subst_written_evidence use t =
  let evidence = Core.Global_use.written_evidence use in
  type_subst_fun
    (fun j ->
      List.find_map
        (fun (v, ty) -> if Int.equal (Core.Scheme.Var.ordinal v) j then Some ty else None)
        evidence )
    t

let written_covers use n =
  let written = List.map (fun (v, _) -> Core.Scheme.Var.ordinal v) (Core.Global_use.written_evidence use) in
  List.for_all (fun j -> List.mem j written) (List.init n succ)

let instantiate_written ~reader (use : _ Core.Global_use.at) t =
  let by_variable = subst_written_evidence use t in
  if Probe.enabled () then
    Option.iter
      (fun inst ->
        let solved = (Partial.instantiate inst t :> _ Core.Type.at) in
        let tag =
          if eq_core_type solved by_variable then "INSTW_same"
          else if Option.is_empty (Partial.close (Partial.instantiate inst t)) then "INSTW_holes"
          else "INSTW_differ"
        in
        Probe.hit tag (fun () ->
            Printf.sprintf "%s %s written=%s solved=%s" reader
              (Pp.string_of_ppcmds (GlobRef.print use.callee))
              (debug_core_type by_variable) (debug_core_type solved) ) )
      (Core.Global_use.instantiation use);
  by_variable

(** {2 Does a section path occur in a Core type ?} *)

let rec type_mem_kn kn = function
  | Core.Type.Meta {contents = Some t} -> type_mem_kn kn t
  | Core.Type.Global_app {head = r; type_arguments = l; _} -> occur_kn_in_ref kn r || List.exists (type_mem_kn kn) l
  | Core.Type.Variable_app {arguments = l; _} -> List.exists (type_mem_kn kn) l
  | Core.Type.Arrow {parameter = a; result = b} -> type_mem_kn kn a || type_mem_kn kn b
  | _ -> false

(** {2 Greatest variable occurring in [t]} *)

let type_maxvar t = Core.Schema.max_tvar t

(** {2 From [a -> b -> c] to [[a;b],c]} *)

let rec type_decomp = function
  | Core.Type.Meta {contents = Some t} -> type_decomp t
  | Core.Type.Arrow {parameter = a; result = b} ->
    let l, h = type_decomp b in
    (a :: l, h)
  | a -> ([], a)

(** {2 The converse: From [[a;b],c] to [a -> b -> c]} *)

let rec type_recomp (l, t) =
  match l with
  | [] -> t
  | a :: l -> Core.Type.Arrow {parameter = a; result = type_recomp (l, t)}

(** {2 Making a definition's own type variables rigid} *)

let rec rigidify = function
  | Core.Type.Meta {contents = Some t} -> rigidify t
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i} ->
    Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = i}
  (* The head of an application is an index, not a [Core.Type.Variable] node, so there is
     no rigidity to switch on it; only the arguments carry the distinction. *)
  | Core.Type.Variable_app {head = i; arguments = l} ->
    Core.Type.Variable_app {head = i; arguments = List.map rigidify l}
  | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = rigidify a; result = rigidify b}
  | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
    Core.Type.Global_app {head = r; type_arguments = List.map rigidify l; index_arguments = a}
  | a -> a

type 'p abbrev_map = GlobRef.t -> 'p Core.Type.at option

(** {2 Delta-reduction of type constants everywhere in a Core type [t]. [env] is an
    {!abbrev_map}} *)

let type_expand env t =
  let rec expand = function
    | Core.Type.Meta {contents = Some t} -> expand t
    | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
      ( match env r with
      | Some extracted_ty -> expand (type_subst_list l extracted_ty)
      | None -> Core.Type.Global_app {head = r; type_arguments = List.map expand l; index_arguments = a} )
    | Core.Type.Variable_app {head = i; arguments = l} ->
      Core.Type.Variable_app {head = i; arguments = List.map expand l}
    | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = expand a; result = expand b}
    | a -> a
  in
  if Table.type_expand () then expand t else t

let type_simpl t = type_expand (fun _ -> None) t

let type_expand_values env t =
  let rec is_arrow = function
    | Core.Type.Meta {contents = Some t} -> is_arrow t
    | Core.Type.Arrow _ -> true
    | _ -> false
  in
  type_expand (fun r -> match env r with Some b when not (is_arrow (type_expand env b)) -> Some b | _ -> None) t

(** {2 Generating a signature from a Core type} *)

let type_to_sign env t =
  match type_expand env t with
  | Core.Type.Erased d when not (conservative_types ()) -> Core.Signature.Argument.Erased d
  | _ -> Core.Signature.Argument.Runtime

let type_to_signature env t =
  let rec f = function
    | Core.Type.Meta {contents = Some t} -> f t
    | Core.Type.Arrow {parameter = Core.Type.Erased d; result = b} when not (conservative_types ()) ->
      Core.Signature.Argument.Erased d :: f b
    | Core.Type.Arrow {result = b; _} -> Core.Signature.Argument.Runtime :: f b
    | _ -> []
  in
  f (type_expand env t)

let isKill = function
  | Core.Signature.Argument.Erased _ -> true
  | _ -> false

let is_erased_type = function
  | Core.Type.Erased _ -> true
  | _ -> false

let is_erased_value = function
  | Core.Expr.Erased_value _ -> true
  | _ -> false

let term_defs = function
  | Core.Decl.Value {entity; body; type_} -> [{Core.Recursion.Definition.entity; body; type_}]
  | Core.Decl.Recursive_group fds -> Core.Nonempty.to_list fds
  | Core.Decl.Inductive _ | Core.Decl.Type_alias _ -> []

let sign_of_id = function
  | Core.Binder_name.Anonymous -> Core.Signature.Argument.Erased Core.Erasure_reason.Proof
  | Core.Binder_name.Source _ | Core.Binder_name.Generated _ -> Core.Signature.Argument.Runtime

(** Classification of a type signature by its logical content. *)
type sign_kind =
  | EmptySig
  | NonLogicalSig (* at least a [Core.Signature.Argument.Runtime] *)
  | SafeLogicalSig (* only [Core.Signature.Argument.Erased Core.Erasure_reason.Type_argument] *)
  | UnsafeLogicalSig (* No [Core.Signature.Argument.Runtime], not all [Core.Signature.Argument.Erased
                        Core.Erasure_reason.Type_argument] *)

(** Classifies a signature as empty, non-logical, safe-logical, or
    unsafe-logical. *)
let rec sign_kind = function
  | [] -> EmptySig
  | Core.Signature.Argument.Runtime :: _ -> NonLogicalSig
  | Core.Signature.Argument.Erased k :: s ->
  match (k, sign_kind s) with
  | _, NonLogicalSig -> NonLogicalSig
  | Core.Erasure_reason.Type_argument, (SafeLogicalSig | EmptySig) -> SafeLogicalSig
  | _, _ -> UnsafeLogicalSig

(** Removes trailing [Core.Signature.Argument.Runtime] entries from a signature. *)
let rec sign_no_final_keeps = function
  | [] -> []
  | k :: s ->
  match (k, sign_no_final_keeps s) with
  | Core.Signature.Argument.Runtime, [] -> []
  | k, l -> k :: l

(** {2 Removing [Core.Type.Erased] from the top level of a Core type} *)

let type_expunge_from_sign env s t =
  let rec expunge s t =
    match (s, t) with
    | [], _ -> t
    | Core.Signature.Argument.Runtime :: s, Core.Type.Arrow {parameter = a; result = b} ->
      Core.Type.Arrow {parameter = a; result = expunge s b}
    | Core.Signature.Argument.Erased _ :: s, Core.Type.Arrow {parameter = a; result = b} -> expunge s b
    | _, Core.Type.Meta {contents = Some t} -> expunge s t
    | _, Core.Type.Global_app {head = r; type_arguments = l; _} ->
      ( match env r with
      | Some extracted_ty -> expunge s (type_subst_list l extracted_ty)
      | None -> assert false )
    | _ -> assert false
  in
  let t = expunge (sign_no_final_keeps s) t in
  if sign_kind s == UnsafeLogicalSig then
    Core.Type.Arrow {parameter = Core.Type.Erased Core.Erasure_reason.Proof; result = t}
  else
    t

let type_expunge env t = type_expunge_from_sign env (type_to_signature env t) t

(** {1 Generic functions over Core terms} *)

let apply_args f a = if List.is_empty a then f else Core.Expr.Apply {callee = f; arguments = a}

(** Equality *)

let eq_core_ident i1 i2 =
  match (i1, i2) with
  | Core.Binder_name.Anonymous, Core.Binder_name.Anonymous -> true
  | Core.Binder_name.Source id1, Core.Binder_name.Source id2 -> Id.equal id1 id2
  | Core.Binder_name.Generated id1, Core.Binder_name.Generated id2 -> Id.equal id1 id2
  | Core.Binder_name.Anonymous, (Core.Binder_name.Source _ | Core.Binder_name.Generated _)
  | Core.Binder_name.Source _, (Core.Binder_name.Anonymous | Core.Binder_name.Generated _)
  | Core.Binder_name.Generated _, (Core.Binder_name.Anonymous | Core.Binder_name.Source _) ->
    false

let rec eq_core_ast t1 t2 =
  match (t1, t2) with
  | Core.Expr.Bound_variable {index = i1; _}, Core.Expr.Bound_variable {index = i2; _} -> Int.equal i1 i2
  | Core.Expr.Apply {callee = f1; arguments = t1}, Core.Expr.Apply {callee = f2; arguments = t2} ->
    eq_core_ast f1 f2 && List.equal eq_core_ast t1 t2
  | Core.Expr.Lambda {parameter = na1; body = t1; _}, Core.Expr.Lambda {parameter = na2; body = t2; _} ->
    eq_core_ident na1 na2 && eq_core_ast t1 t2
  | Core.Expr.Let {binder = na1;
                   binder_type = ty1;
                   value = c1;
                   body = t1; _}, Core.Expr.Let {binder = na2; binder_type = ty2; value = c2; body = t2; _} ->
    eq_core_ident na1 na2 && eq_core_ast c1 c2 && eq_core_ast t1 t2
  | Core.Expr.Global {callee = gr1; _}, Core.Expr.Global {callee = gr2; _} -> GlobRef.CanOrd.equal gr1 gr2
  | Core.Expr.Construct {result_type = t1;
                         constructor = gr1;
                         arguments = c1; _}, Core.Expr.Construct {result_type = t2;
                                                                  constructor = gr2;
                                                                  arguments = c2; _} ->
    eq_core_type t1 t2
    && GlobRef.CanOrd.equal gr1 gr2
    && List.equal eq_core_ast c1 c2
  | Core.Expr.Tuple t1, Core.Expr.Tuple t2 -> List.equal eq_core_ast t1 t2
  | Core.Expr.Match {scrutinee_type = t1;
                     scrutinee = c1;
                     branches = p1; _}, Core.Expr.Match {scrutinee_type = t2; scrutinee = c2; branches = p2; _} ->
    eq_core_type t1 t2 && eq_core_ast c1 c2 && Array.equal eq_core_branch p1 p2
  | ( (Core.Expr.Fixpoint g1 | Core.Expr.Cofixpoint g1),
      (Core.Expr.Fixpoint g2 | Core.Expr.Cofixpoint g2) ) ->
    Int.equal g1.selected g2.selected
    && Array.equal (fun (m1 : _ Core.Recursion.Member.at) (m2 : _ Core.Recursion.Member.at) -> Id.equal m1.name m2.name)
         g1.members g2.members
    && Array.equal eq_core_ast (Core.Recursion.Group.bodies g1) (Core.Recursion.Group.bodies g2)
  | Core.Expr.Runtime_error e1, Core.Expr.Runtime_error e2 -> String.equal e1 e2
  | Core.Expr.Erased_value k1, Core.Expr.Erased_value k2 -> k1 == k2
  | Core.Expr.Axiom_value _, Core.Expr.Axiom_value _ -> true (* ignore the name of the axiom *)
  | ( ( Core.Expr.Coerce {value = t1; _}
      | Core.Expr.Boxed_value {value = t1; _}
      | Core.Expr.Lambda_group_barrier {value = t1; _} ),
      ( Core.Expr.Coerce {value = t2; _}
      | Core.Expr.Boxed_value {value = t2; _}
      | Core.Expr.Lambda_group_barrier {value = t2; _} ) ) ->
    eq_core_ast t1 t2
  | Core.Expr.UInt63 i1, Core.Expr.UInt63 i2 -> Uint63.equal i1 i2
  | Core.Expr.Numeral {inductive = r1; value = n1}, Core.Expr.Numeral {inductive = r2; value = n2} ->
    GlobRef.CanOrd.equal r1 r2 && Z.equal n1 n2
  | Core.Expr.Float64 f1, Core.Expr.Float64 f2 -> Float64.equal f1 f2
  | Core.Expr.String s1, Core.Expr.String s2 -> Pstring.equal s1 s2
  | Core.Expr.Persistent_array {elements = t1;
                                default = def1}, Core.Expr.Persistent_array {elements = t2; default = def2} ->
    Array.equal eq_core_ast t1 t2 && eq_core_ast def1 def2
  | ( ( Core.Expr.Bound_variable _
      | Core.Expr.Apply _
      | Core.Expr.Lambda _
      | Core.Expr.Let _
      | Core.Expr.Global _
      | Core.Expr.Construct _
      | Core.Expr.Tuple _
      | Core.Expr.Match _
      | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _
      | Core.Expr.Runtime_error _
      | Core.Expr.Erased_value _
      | Core.Expr.Axiom_value _
      | Core.Expr.Coerce _ | Core.Expr.Boxed_value _ | Core.Expr.Lambda_group_barrier _
      | Core.Expr.UInt63 _ | Core.Expr.Numeral _
      | Core.Expr.Float64 _
      | Core.Expr.String _
      | Core.Expr.Persistent_array _ ),
      _ ) -> false

and eq_core_pattern p1 p2 =
  match (p1, p2) with
  | Core.Pattern.Constructor {constructor = gr1;
                              fields = p1}, Core.Pattern.Constructor {constructor = gr2; fields = p2} ->
    GlobRef.CanOrd.equal gr1 gr2 && List.equal eq_core_pattern p1 p2
  | Core.Pattern.Tuple p1, Core.Pattern.Tuple p2 -> List.equal eq_core_pattern p1 p2
  | Core.Pattern.Bound_variable i1, Core.Pattern.Bound_variable i2 -> Int.equal i1 i2
  | Core.Pattern.Wildcard, Core.Pattern.Wildcard -> true
  | _ -> false

and eq_core_branch
    {Core.Match.Branch.binders = id1; pattern = p1; body = t1; _}
    {Core.Match.Branch.binders = id2; pattern = p2; body = t2; _} =
  List.equal (fun (x1, y1) (x2, y2) -> eq_core_ident x1 x2) id1 id2
  && eq_core_pattern p1 p2
  && eq_core_ast t1 t2

(** {2 [ast_iter_rel f t] applies [f] on every [Core.Expr.Bound_variable] in t. It takes care of
    the number of bindings crossed before reaching the [Core.Expr.Bound_variable]} *)

(** [ast_iter_rel_applied f t] calls [f n i args] on every [Core.Expr.Bound_variable i] in [t],
    with [n] the number of bindings crossed to reach it and [args] the
    arguments it is applied to there, if any. *)
let ast_iter_rel_applied f =
  let rec iter n = function
    | Core.Expr.Bound_variable {index = i; _} -> f n i []
    | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; _}; arguments = l} ->
      f n i l;
      List.iter (iter n) l
    | Core.Expr.Lambda {body = a; _} -> iter (n + 1) a
    | Core.Expr.Let {value = a; body = b; _} ->
      iter n a;
      iter (n + 1) b
    | Core.Expr.Match {scrutinee = a; branches = v; _} ->
      iter n a;
      Array.iter (fun {Core.Match.Branch.binders = l; body = t; _} -> iter (n + List.length l) t) v
    | Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g ->
      let k = Core.Recursion.Group.length g in
      Array.iter (fun (m : _ Core.Recursion.Member.at) -> iter (n + k) m.body) g.members
    | Core.Expr.Apply {callee = a; arguments = l} ->
      iter n a;
      List.iter (iter n) l
    | Core.Expr.Construct {arguments = l; _} | Core.Expr.Tuple l -> List.iter (iter n) l
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> iter n a
    | Core.Expr.Persistent_array {elements = t; default = def} ->
      Array.iter (iter n) t;
      iter n def
    | Core.Expr.Global _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _ -> ()
  in
  iter 0

let ast_iter_rel f = ast_iter_rel_applied (fun n i _ -> f (i - n))

(** {2 Map over Core terms} *)

let ast_map_branch f (br : _ Core.Match.Branch.at) = {br with Core.Match.Branch.body = f br.body}

(* Warning: in [ast_map] we assume that [f] does not change the type of [Core.Expr.Construct]
   and of [Core.Expr.Match] heads *)

let ast_map f = function
  | Core.Expr.Lambda {parameter = i; parameter_type = t; body = a} ->
    Core.Expr.Lambda {parameter = i; parameter_type = t; body = f a}
  | Core.Expr.Let {binder = i; binder_type = t; value = a; body = b; occurrence = occ} ->
    Core.Expr.Let {binder = i; binder_type = t; value = f a; body = f b; occurrence = occ}
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = a; branches = v; occurrence = occ} ->
    Core.Expr.Match {scrutinee_type = typ; scrutinee = f a; branches = Array.map (ast_map_branch f) v; occurrence = occ}
  | Core.Expr.Fixpoint g -> Core.Expr.Fixpoint (Core.Recursion.Group.map_bodies f g)
  | Core.Expr.Cofixpoint g -> Core.Expr.Cofixpoint (Core.Recursion.Group.map_bodies f g)
  | Core.Expr.Apply {callee = a; arguments = l} -> Core.Expr.Apply {callee = f a; arguments = List.map f l}
  | Core.Expr.Construct {result_type = typ; constructor = c; arguments = l; occurrence = occ} ->
    Core.Expr.Construct {result_type = typ; constructor = c; arguments = List.map f l; occurrence = occ}
  | Core.Expr.Tuple l -> Core.Expr.Tuple (List.map f l)
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
    Core.Expr.Coerce {source_type = from; target_type = into; value = f a; occurrence = mocc}
  | Core.Expr.Boxed_value {value = a; occurrence = mocc} -> Core.Expr.Boxed_value {value = f a; occurrence = mocc}
  | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
    Core.Expr.Lambda_group_barrier {value = f a; occurrence = mocc}
  | Core.Expr.Persistent_array {elements = t; default = def} ->
    Core.Expr.Persistent_array {elements = Array.map f t; default = f def}
  | ( Core.Expr.Bound_variable _
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _ | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ ) as a -> a

(** [ast_map_types f a] rewrites every [Core.Type.t] embedded in [a] with [f],
    recursing through the whole term.  Unlike {!ast_map} it descends on its
    own, because a type-level rewrite has to reach every node that carries a
    type: lambda and let binders, [Core.Expr.Global] type arguments, [Core.Expr.Construct] and
    [Core.Expr.Match] heads, pattern binders, and fixpoint signatures. *)
let rec ast_map_types f = function
  | Core.Expr.Lambda {parameter = i; parameter_type = t; body = a} ->
    Core.Expr.Lambda {parameter = i; parameter_type = f t; body = ast_map_types f a}
  | Core.Expr.Let {binder = i; binder_type = t; value = a; body = b; occurrence = occ} ->
    Core.Expr.Let {binder = i; binder_type = f t; value = ast_map_types f a; body = ast_map_types f b; occurrence = occ}
  | Core.Expr.Global use -> Core.Expr.Global (Core.Global_use.map_types f use)
  | Core.Expr.Construct {result_type = t; constructor = c; arguments = l; occurrence = occ} ->
    Core.Expr.Construct {result_type = f t; constructor = c; arguments = List.map (ast_map_types f) l; occurrence = occ}
  | Core.Expr.Tuple l -> Core.Expr.Tuple (List.map (ast_map_types f) l)
  | Core.Expr.Match {scrutinee_type = t; scrutinee = a; branches = v; occurrence = occ} ->
    let branch {Core.Match.Branch.binders = binds; result_type = bty; pattern = pat; body = body} =
      { Core.Match.Branch.binders = List.map (fun (id, bt) -> (id, f bt)) binds;
        result_type = f bty;
        pattern = pat;
        body = ast_map_types f body }
    in
    Core.Expr.Match {scrutinee_type = f t;
                     scrutinee = ast_map_types f a;
                     branches = Array.map branch v;
                     occurrence = occ}
  | Core.Expr.Fixpoint g -> Core.Expr.Fixpoint (Core.Recursion.Group.map f (ast_map_types f) g)
  | Core.Expr.Cofixpoint g -> Core.Expr.Cofixpoint (Core.Recursion.Group.map f (ast_map_types f) g)
  | Core.Expr.Apply {callee = a; arguments = l} ->
    Core.Expr.Apply {callee = ast_map_types f a; arguments = List.map (ast_map_types f) l}
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
    (* A coercion's two types must be rewritten alongside every other type in
       the term, or the boundary it records stops matching the term around
       it; a box or a barrier has none. *)
    Core.Expr.Coerce {source_type = f from; target_type = f into; value = ast_map_types f a; occurrence = mocc}
  | Core.Expr.Boxed_value {value = a; occurrence = mocc} ->
    Core.Expr.Boxed_value {value = ast_map_types f a; occurrence = mocc}
  | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
    Core.Expr.Lambda_group_barrier {value = ast_map_types f a; occurrence = mocc}
  | Core.Expr.Persistent_array {elements = t; default = def} ->
    Core.Expr.Persistent_array {elements = Array.map (ast_map_types f) t; default = ast_map_types f def}
  | ( Core.Expr.Bound_variable _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _ | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ ) as a -> a

let freshen_metas e =
  let copies = Hashtbl.create 8 in
  let copy id make =
    match Hashtbl.find_opt copies id with
    | Some m -> m
    | None ->
      let m = make () in
      Hashtbl.add copies id m;
      m
  in
  (* An open annotation exists only once the program is frozen, when a
     fresh metavariable is an open annotation too. *)
  let fresh = function
    | Core.Type.Meta ({contents = None; id} as m) -> copy id (fun () -> new_meta_like m)
    | Core.Type.Open o -> copy (Core.Open.id o) new_open
    | t -> t
  in
  ast_map_types (map_core_type fresh) e

(** [has_unknown t]: whether [t] mentions {!Core.Type.Unknown} anywhere.

    [Core.Type.Unknown] is what extraction leaves where a type was erased, so its
    presence is the marker that an annotation is missing information rather
    than genuinely opaque. *)
let rec has_unknown = function
  | Core.Type.Unknown -> true
  | Core.Type.Arrow {parameter = a; result = b} -> has_unknown a || has_unknown b
  | Core.Type.Global_app {type_arguments = l; _} -> List.exists has_unknown l
  | Core.Type.Meta {contents = Some t} -> has_unknown t
  | _ -> false

(** [recover_erased_types expected a] fills in the annotations extraction
    erased to {!Core.Type.Unknown}, using the type [a] is known to have.

    A class field's body is extracted at the class's own erased field type, so
    every type it records is spelled [option Core.Type.Unknown] even when the caller
    knows perfectly well which element type is meant.  The declared type is
    recovered elsewhere for the {e signature} (from the projection constant,
    which kept the quantifier); this pushes the same information down into the
    {e body}, so the two agree.  A body that says [Option<std::any>::Some]
    against a value of type [Option<_A0>] does not compile.

    Only annotations that mention [Core.Type.Unknown] are touched, and only where the
    context supplies something better, so a term whose types survived
    extraction intact passes through unchanged.

    [~only] narrows the recovery to the types the caller wants the declaration
    to speak about, and, where it does speak, writes the recovered type into
    the binder's own annotation as well as into the environment's copy of it.
    Both halves answer the same question.  A caller that reads its parameters
    straight off the declared signature wants the annotation left alone and
    every recovery taken; a caller whose parameter types are about to be
    guessed at wants the arrow to speak first, but only over the holes that
    guess would otherwise fill -- everywhere else the body has a pass that
    knows better than the declaration does, and an alias in particular is a
    type in its own right whose spelling the body must keep. *)
let recover_erased_types ?only ?(refine_only = false) (expected : _ Core.Type.at)
    (a : _ Core.Expr.at) : _ Core.Expr.at =
  (* [env] holds the binders' types, innermost first, as de Bruijn demands. *)
  let type_of_rel env n = try Some (List.nth env (n - 1)) with _ -> None in
  (* [Core.Type.Unknown] is not the only way an annotation says nothing.  A
     metavariable unification never resolved is just as empty, and it is what
     a record constructor inside an instance method carries: [mkStateT]'s
     annotation arrives as [stateT ?1 ?2 _], three positions and not one of
     them determined.  Asking only about [Core.Type.Unknown] declines the recovery and
     the printer then erases all three to [std::any], against a signature that
     by now spells every one of them. *)
  let rec uninformative = function
    | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
    | Core.Type.Meta {contents = Some t} -> uninformative t
    | Core.Type.Unknown -> true
    | Core.Type.Arrow {parameter = a; result = b} -> uninformative a || uninformative b
    | Core.Type.Global_app {type_arguments = l; _} -> List.exists uninformative l
    | _ -> false
  in
  (* The declaration may {e refine} an annotation, not {e respell} it.  A
     partially-known [sigT nat (unit -> _)] and the declaration's [entry] may
     well denote the same type, but they are different spellings of it, and
     taking the second throws away the structure the body had already pinned
     down -- the printer then asks a [SigT<...>] for a member named [entry].
     An alias is a type in its own right.  So the declaration is taken only
     where it agrees with the annotation head for head, filling the holes and
     changing nothing else. *)
  let rec refines ~have ~from =
    match (have, from) with
    | (Core.Type.Unknown | Core.Type.Meta {contents = None} | Core.Type.Open _), _ -> true
    | Core.Type.Meta {contents = Some h}, f -> refines ~have:h ~from:f
    | h, Core.Type.Meta {contents = Some f} -> refines ~have:h ~from:f
    | Core.Type.Arrow {parameter = a; result = b}, Core.Type.Arrow {parameter = c; result = d} ->
      refines ~have:a ~from:c && refines ~have:b ~from:d
    | Core.Type.Global_app {head = r;
                            type_arguments = l; _}, Core.Type.Global_app {head = r'; type_arguments = l'; _} ->
      GlobRef.CanOrd.equal r r'
      && Int.equal (List.length l) (List.length l')
      && List.for_all2 (fun a b -> refines ~have:a ~from:b) l l'
    | Core.Type.Variable_app {head = i; arguments = l}, Core.Type.Variable_app {head = j; arguments = l'} ->
      Int.equal i j
      && Int.equal (List.length l) (List.length l')
      && List.for_all2 (fun a b -> refines ~have:a ~from:b) l l'
    | _ -> false
  in
  let accepts = match only with None -> fun _ -> true | Some p -> p in
  let better ~have ~from =
    match from with
    | Some t
      when uninformative have
           && (not (uninformative t))
           && ((not refine_only) || refines ~have ~from:t)
           && accepts t -> t
    | _ -> have
  in
  (* The callee's declared domains for this call, instantiated at the call's
     own type arguments -- one offer per argument, [None] where the
     declaration does not reach.

     The two lists are aligned from the left and the shorter one runs out.
     Both ways of running out are ordinary and neither says the declaration is
     describing a different call: a monad whose carrier unfolds to a function
     takes the arguments of that function too, so [bind : m A -> (A -> m B) ->
     m B] at [m = stateT S m'] is declared with two domains and applied to
     three; and a partial application has fewer.  Only the positions the
     declaration actually spells are offered, which is exactly the prefix.
     Requiring the lengths to agree would withdraw every offer at such a
     call -- including the ones the declaration names perfectly well. *)
  let callee_doms (use : _ Core.Global_use.at) args =
    match (try Some (Table.find_type use.callee) with Not_found -> None) with
    | None -> []
    | Some sch ->
      let doms, _ =
        type_decomp (instantiate_written ~reader:"callee_doms" use sch)
      in
      (* An erased type argument is an arrow in the declaration and nothing in
         the application, so the two are only comparable once it is dropped.
         [Core.Type.Erased] does not say which arrows those are: it is equally what a
         *value* argument's type erases to, and such an argument is still
         passed.  [bind] on a transformer over an erased carrier declares
         [Dt -> Monad[Dt] -> Dt -> Dt -> Dt -> (nat -> Dt) -> Dt] for the same
         three arguments the informative instance spells with one [Dt] fewer,
         and dropping every one of them slides the continuation a position
         left -- so the lambda is offered the monadic value's type, or nothing.

         What the two do agree on is how many positions survive.  The erased
         type arguments come from the prenex quantifiers, so they are the
         leftmost dummies; drop only that many, from the left, and the rest
         line up with the application. *)
      let n_drop = List.length doms - List.length args in
      let doms =
        if n_drop <= 0 then doms
        else
          let left = ref n_drop in
          List.filter
            (fun d ->
              if !left > 0 && is_erased_type d then begin
                decr left;
                false
              end
              else true )
            doms
      in
      if doms = [] then []
      else
        (* A dummy that survives the alignment is a position whose type the
           declaration erased.  That is not an answer, and offering it as one
           writes [Core.Type.Erased] over a binder that is still there -- which is how a
           binder gets removed rather than typed. *)
        List.mapi
          (fun i _ ->
            match List.nth_opt doms i with
            | Some d when is_erased_type d -> None
            | o -> o )
          args
  in
  let rec go env expected a =
    match a with
    | Core.Expr.Lambda {parameter = i; parameter_type = ty; body = b} when is_erased_type ty ->
      (* An erased binder -- the [forall A] the class field quantified away --
         consumes no arrow of the declared type. *)
      Core.Expr.Lambda {parameter = i; parameter_type = ty; body = go (ty :: env) expected b}
    | Core.Expr.Lambda {parameter = i; parameter_type = ty; body = b} ->
      let dom, cod =
        match expected with
        | Some (Core.Type.Arrow {parameter = d; result = c}) -> (Some d, Some c)
        | _ -> (None, None)
      in
      (* Under [~only], the binder's annotation is recovered too.  A parameter
         whose type extraction erased is a hole that a later pass will guess
         at, and a guess made from the class rather than from the arrow cannot
         tell one associated type from another -- [takes_three (a :
         allocationId) (p : prov)] came out taking two [prov]s.  The arrow
         knows; write it down where the guess would otherwise land. *)
      let better_ty = better ~have:ty ~from:dom in
      let ty = if only = None then ty else better_ty in
      Core.Expr.Lambda {parameter = i; parameter_type = ty; body = go (better_ty :: env) cod b}
    | Core.Expr.Let {binder = i; binder_type = ty; value = e; body = b; occurrence = occ} ->
      let e = go env (if has_unknown ty then None else Some ty) e in
      Core.Expr.Let {binder = i; binder_type = ty; value = e; body = go (ty :: env) expected b; occurrence = occ}
    | Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches; occurrence = occ} ->
      (* The head type is the scrutinee's, and the scrutinee is usually a
         binder whose type the signature has already pinned down. *)
      let ty = better ~have:ty ~from:(match scrut with
        | Core.Expr.Bound_variable {index = n; _} -> type_of_rel env n
        | _ -> None )
      in
      let branch ({Core.Match.Branch.binders = binds; result_type = bty; body = body; _} as br) =
        let bty = better ~have:bty ~from:expected in
        let env = List.rev_map snd binds @ env in
        {br with Core.Match.Branch.result_type = bty; body = go env expected body}
      in
      Core.Expr.Match {scrutinee_type = ty;
                       scrutinee = go env None scrut;
                       branches = Array.map branch branches;
                       occurrence = occ}
    | Core.Expr.Construct {result_type = ty; constructor = c; arguments = args; occurrence = occ} ->
      Core.Expr.Construct {result_type = better ~have:ty ~from:expected;
                           constructor = c;
                           arguments = List.map (go env None) args;
                           occurrence = occ}
    | Core.Expr.Apply {callee = (Core.Expr.Global use as f); arguments = args} when callee_doms use args <> [] ->
      (* A lambda passed as an argument is the case with no second witness:
         its binder's type occurs nowhere in the enclosing declaration -- it
         is spelled only by the callee's parameter at that position, with this
         call's type arguments substituted in.  That is an authority of the
         same kind as the declared type, so it is pushed down the same way. *)
      Core.Expr.Apply {callee = f; arguments = List.map2 (fun d e -> go env d e) (callee_doms use args) args}
    | Core.Expr.Apply {callee = f; arguments = args} ->
      Core.Expr.Apply {callee = go env None f; arguments = List.map (go env None) args}
    | Core.Expr.Coerce {source_type = from; target_type = into; value = e; occurrence = mocc} ->
      Core.Expr.Coerce {source_type = from; target_type = into; value = go env expected e; occurrence = mocc}
    | Core.Expr.Boxed_value {value = e; occurrence = mocc} ->
      Core.Expr.Boxed_value {value = go env expected e; occurrence = mocc}
    | Core.Expr.Lambda_group_barrier {value = e; occurrence = mocc} ->
      Core.Expr.Lambda_group_barrier {value = go env expected e; occurrence = mocc}
    | a -> a
  in
  go [] (Some expected) a

(** {2 Map over Core terms, with binding depth as parameter} *)

let ast_map_lift_branch f n (br : _ Core.Match.Branch.at) =
  {br with Core.Match.Branch.body = f (n + List.length br.binders) br.body}

(* Same warning as for [ast_map]... *)

let ast_map_lift f n = function
  | Core.Expr.Lambda {parameter = i; parameter_type = t; body = a} ->
    Core.Expr.Lambda {parameter = i; parameter_type = t; body = f (n + 1) a}
  | Core.Expr.Let {binder = i; binder_type = t; value = a; body = b; occurrence = occ} ->
    Core.Expr.Let {binder = i; binder_type = t; value = f n a; body = f (n + 1) b; occurrence = occ}
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = a; branches = v; occurrence = occ} ->
    Core.Expr.Match {scrutinee_type = typ;
                     scrutinee = f n a;
                     branches = Array.map (ast_map_lift_branch f n) v;
                     occurrence = occ}
  | Core.Expr.Fixpoint g ->
    Core.Expr.Fixpoint (Core.Recursion.Group.map_bodies (f (Core.Recursion.Group.length g + n)) g)
  | Core.Expr.Cofixpoint g ->
    Core.Expr.Cofixpoint (Core.Recursion.Group.map_bodies (f (Core.Recursion.Group.length g + n)) g)
  | Core.Expr.Apply {callee = a; arguments = l} -> Core.Expr.Apply {callee = f n a; arguments = List.map (f n) l}
  | Core.Expr.Construct {result_type = typ; constructor = c; arguments = l; occurrence = occ} ->
    Core.Expr.Construct {result_type = typ; constructor = c; arguments = List.map (f n) l; occurrence = occ}
  | Core.Expr.Tuple l -> Core.Expr.Tuple (List.map (f n) l)
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
    Core.Expr.Coerce {source_type = from; target_type = into; value = f n a; occurrence = mocc}
  | Core.Expr.Boxed_value {value = a; occurrence = mocc} -> Core.Expr.Boxed_value {value = f n a; occurrence = mocc}
  | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
    Core.Expr.Lambda_group_barrier {value = f n a; occurrence = mocc}
  | Core.Expr.Persistent_array {elements = t; default = def} ->
    Core.Expr.Persistent_array {elements = Array.map (f n) t; default = f n def}
  | ( Core.Expr.Bound_variable _
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _ | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ ) as a -> a

(** {2 Iter over Core terms} *)

let ast_iter_branch f (br : _ Core.Match.Branch.at) = f br.body

let ast_iter f = function
  | Core.Expr.Lambda {parameter = i; body = a; _} -> f a
  | Core.Expr.Let {value = a; body = b; _} ->
    f a;
    f b
  | Core.Expr.Match {scrutinee = a; branches = v; _} ->
    f a;
    Array.iter (ast_iter_branch f) v
  | Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g ->
    Array.iter (fun (m : _ Core.Recursion.Member.at) -> f m.body) g.members
  | Core.Expr.Apply {callee = a; arguments = l} ->
    f a;
    List.iter f l
  | Core.Expr.Construct {arguments = l; _} | Core.Expr.Tuple l -> List.iter f l
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} -> f a
  | Core.Expr.Persistent_array {elements = t; default = def} ->
    Array.iter f t;
    f def
  | Core.Expr.Bound_variable _
   |Core.Expr.Global _
   |Core.Expr.Runtime_error _
   |Core.Expr.Erased_value _
   |Core.Expr.Axiom_value _
   |Core.Expr.UInt63 _ | Core.Expr.Numeral _
   |Core.Expr.Float64 _
   |Core.Expr.String _ -> ()

(** {1 Operations concerning De Bruijn indices} *)

(** {2 [ast_occurs k t] returns [true] if [(Rel k)] occurs in [t]} *)

let ast_occurs k t =
  try
    ast_iter_rel (fun i -> if Int.equal i k then raise Found) t;
    false
  with Found -> true

(** {2 [occurs_itvl k k' t] returns [true] if there is a [(Rel i)] in [t] with
    [k<=i<=k']} *)

let ast_occurs_itvl k k' t =
  try
    ast_iter_rel (fun i -> if k <= i && i <= k' then raise Found) t;
    false
  with Found -> true

(* Number of occurrences of [Rel 1] in [t], with special treatment of match:
   occurrences in different branches aren't added, but we rather use max. *)

let nb_occur_match e =
  let rec nb k = function
    | Core.Expr.Bound_variable {index = i; _} -> if Int.equal i k then 1 else 0
    | Core.Expr.Match {scrutinee = a; branches = v; _} ->
      nb k a
      + Array.fold_left
          (fun r {Core.Match.Branch.binders = ids; body = a; _} -> max r (nb (k + List.length ids) a))
          0
          v
    | Core.Expr.Let {value = a; body = b; _} -> nb k a + nb (k + 1) b
    | Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g ->
      let k = k + Core.Recursion.Group.length g in
      Array.fold_left (fun r (m : _ Core.Recursion.Member.at) -> r + nb k m.body) 0 g.members
    | Core.Expr.Lambda {body = a; _} -> nb (k + 1) a
    | Core.Expr.Apply {callee = a; arguments = l} -> List.fold_left (fun r a -> r + nb k a) (nb k a) l
    | Core.Expr.Construct {arguments = l; _} | Core.Expr.Tuple l -> List.fold_left (fun r a -> r + nb k a) 0 l
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> nb k a
    | Core.Expr.Persistent_array {elements = t; default = def} ->
      Array.fold_left (fun r a -> r + nb k a) 0 t + nb k def
    | Core.Expr.Global _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _ -> 0
  in
  nb 1 e

(** Replaces unused bound variables by [Core.Binder_name.Anonymous] (["_"]) throughout a Core term. *)
let dump_unused_vars a =
  let rec ren env a =
    match a with
    | Core.Expr.Bound_variable {index = i; _} ->
      let () = List.nth env (i - 1) := true in
      a
    | Core.Expr.Lambda {parameter = id; parameter_type = t; body = b} ->
      let occ_id = ref false in
      let b' = ren (occ_id :: env) b in
      if !occ_id then
        if b' == b then a else Core.Expr.Lambda {parameter = id; parameter_type = t; body = b'}
      else
        Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous; parameter_type = t; body = b'}
    | Core.Expr.Let {binder = id; binder_type = t; value = b; body = c; occurrence = occ} ->
      let occ_id = ref false in
      let b' = ren env b in
      let c' = ren (occ_id :: env) c in
      if !occ_id then
        if b' == b && c' == c then a else Core.Expr.Let {binder = id;
                                                         binder_type = t;
                                                         value = b';
                                                         body = c';
                                                         occurrence = occ}
      else (* 'let' without occurrence: shouldn't happen after simpl *)
        Core.Expr.Let {binder = Core.Binder_name.Anonymous; binder_type = t; value = b'; body = c'; occurrence = occ}
    | Core.Expr.Match {scrutinee_type = t; scrutinee = e; branches = br; occurrence = occ} ->
      let e' = ren env e in
      let br' = Array.Smart.map (ren_branch env) br in
      if e' == e && br' == br then a else Core.Expr.Match {scrutinee_type = t;
                                                           scrutinee = e';
                                                           branches = br';
                                                           occurrence = occ}
    | Core.Expr.Fixpoint g ->
      let v = Core.Recursion.Group.bodies g in
      let v' = ren_fix env v in
      if v' == v then a else Core.Expr.Fixpoint (Core.Recursion.Group.with_bodies g v')
    | Core.Expr.Cofixpoint g ->
      let v = Core.Recursion.Group.bodies g in
      let v' = ren_fix env v in
      if v' == v then a else Core.Expr.Cofixpoint (Core.Recursion.Group.with_bodies g v')
    | Core.Expr.Apply {callee = b; arguments = l} ->
      let b' = ren env b
      and l' = List.Smart.map (ren env) l in
      if b' == b && l' == l then a else Core.Expr.Apply {callee = b'; arguments = l'}
    | Core.Expr.Construct {result_type = t; constructor = r; arguments = l; occurrence = occ} ->
      let l' = List.Smart.map (ren env) l in
      if l' == l then a else Core.Expr.Construct {result_type = t; constructor = r; arguments = l'; occurrence = occ}
    | Core.Expr.Tuple l ->
      let l' = List.Smart.map (ren env) l in
      if l' == l then a else Core.Expr.Tuple l'
    | Core.Expr.Coerce {source_type = from; target_type = into; value = b; occurrence = mocc} ->
      let b' = ren env b in
      if b' == b then a else Core.Expr.Coerce {source_type = from; target_type = into; value = b'; occurrence = mocc}
    | Core.Expr.Boxed_value {value = b; occurrence = mocc} ->
      let b' = ren env b in
      if b' == b then a else Core.Expr.Boxed_value {value = b'; occurrence = mocc}
    | Core.Expr.Lambda_group_barrier {value = b; occurrence = mocc} ->
      let b' = ren env b in
      if b' == b then a else Core.Expr.Lambda_group_barrier {value = b'; occurrence = mocc}
    | Core.Expr.Persistent_array {elements = t; default = def} ->
      let t' = Array.Smart.map (ren env) t in
      let def' = ren env def in
      if def' == def && t' == t then a else Core.Expr.Persistent_array {elements = t'; default = def'}
    | Core.Expr.Global _
     |Core.Expr.Runtime_error _
     |Core.Expr.Erased_value _
     |Core.Expr.Axiom_value _
     |Core.Expr.UInt63 _ | Core.Expr.Numeral _
     |Core.Expr.Float64 _
     |Core.Expr.String _ -> a
  and ren_fix env v =
    let env' = List.init (Array.length v) (fun _ -> ref false) @ env in
    Array.Smart.map (ren env') v
  and ren_branch env ({Core.Match.Branch.binders = ids; body = b; _} as tr) =
    let occs = List.map (fun _ -> ref false) ids in
    let b' = ren (List.rev_append occs env) b in
    let ids' =
      List.map2
        (fun (id, ty) occ -> if !occ then (id, ty) else
          (Core.Binder_name.Anonymous, Core.Type.Erased Core.Erasure_reason.Type_argument) )
          (*TODO: I am making up the kill reason *)
        ids
        occs
    in
    if b' == b && List.equal (fun (x1, _) (x2, _) -> eq_core_ident x1 x2) ids ids'
    then
      tr
    else
      {tr with Core.Match.Branch.binders = ids'; body = b'}
  in
  ren [] a

(** {2 Lifting on terms. [ast_lift k t] lifts the binding depth of [t] across
    [k] bindings} *)

let ast_lift k t =
  let rec liftrec n = function
    | Core.Expr.Bound_variable {index = i; occurrence = occ} as a ->
      if i - n < 1 then a else Core.Expr.Bound_variable {index = i + k; occurrence = occ}
    | a -> ast_map_lift liftrec n a
  in
  if Int.equal k 0 then t else liftrec 0 t

let ast_pop t = ast_lift (-1) t

let rec ast_size e =
  1
  +
  match e with
  | Core.Expr.Apply {callee = f; arguments = a} -> ast_size f + ast_sizes a
  | Core.Expr.Lambda {body = b; _}
  | Core.Expr.Coerce {value = b; _}
  | Core.Expr.Boxed_value {value = b; _}
  | Core.Expr.Lambda_group_barrier {value = b; _} ->
    ast_size b
  | Core.Expr.Let {value = a; body = b; _} -> ast_size a + ast_size b
  | Core.Expr.Construct {arguments = a; _} | Core.Expr.Tuple a -> ast_sizes a
  | Core.Expr.Match {scrutinee = s; branches = brs; _} ->
    Array.fold_left (fun n (br : _ Core.Match.Branch.at) -> n + ast_size br.body) (ast_size s) brs
  | Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g ->
    Array.fold_left (fun n (m : _ Core.Recursion.Member.at) -> n + ast_size m.body) 0 g.members
  | _ -> 0

and ast_sizes l = List.fold_left (fun n a -> n + ast_size a) 0 l

(** [branch_type_applied n ty] is the result type of a match branch whose
    value, of type [ty], has been applied to [n] arguments or stripped of [n]
    lambdas: [ty] with [n] arrows taken off.  [ty] itself when it has fewer,
    which leaves it no less accurate than it was. *)
let branch_type_applied n ty =
  let rec go n ty =
    if n = 0 then Some ty
    else match core_resolve ty with
      | Core.Type.Arrow {result = r; _} -> go (n - 1) r
      | _ -> None
  in
  match go n ty with Some r -> r | None -> ty

(* [canonical_app f args], [f] canonical: the application, its head read
   through.  A global applied twice is applied once to both argument lists; a
   coercion at the head is dropped; a single-branch match at the head takes
   the arguments into its branch, past the branch's binders; an absurd head
   -- an erased value, or the throw standing for a branch the indices rule
   out -- is the whole application, which never evaluates its arguments. *)
let rec canonical_app f args =
  match f with
  | Core.Expr.Apply {callee = (Core.Expr.Global _ as g); arguments = inner} ->
    Core.Expr.Apply {callee = g; arguments = inner @ args}
  | Core.Expr.Coerce {value = f; _}
  | Core.Expr.Boxed_value {value = f; _}
  | Core.Expr.Lambda_group_barrier {value = f; _} ->
    canonical_app f args
  | Core.Expr.Runtime_error _ | Core.Expr.Erased_value _ -> f
  | Core.Expr.Match {scrutinee_type = ty;
                     scrutinee = scrut;
                     branches = [|({Core.Match.Branch.binders = ids; body = body; result_type = rty; _} as br)|];
                     occurrence = occ} ->
    (* The branch now returns its value applied to [args]. *)
    let br = {br with Core.Match.Branch.result_type = branch_type_applied (List.length args) rty} in
    let args = List.map (ast_lift (List.length ids)) args in
    let body =
      match body with
      | Core.Expr.Apply {callee = f; arguments = inner} -> Core.Expr.Apply {callee = f; arguments = inner @ args}
      | _ -> canonical_app body args
    in
    Core.Expr.Match {scrutinee_type = ty;
                     scrutinee = scrut;
                     branches = [|{br with Core.Match.Branch.body = body}|];
                     occurrence = occ}
  | _ -> Core.Expr.Apply {callee = f; arguments = args}

let rec canonical = function
  | Core.Expr.Apply {callee = f; arguments = args} -> canonical_app (canonical f) (List.map canonical args)
  | e -> ast_map canonical e

(** {2 [permut_rels k k' c] translates [Rel 1 ... Rel k] to
    [Rel (k'+1) ... Rel (k'+k)] and [Rel (k+1) ... Rel (k+k')] to
    [Rel 1 ... Rel k']} *)

let permut_rels k k' =
  let rec permut n = function
    | Core.Expr.Bound_variable {index = i; occurrence = occ} as a ->
      let i' = i - n in
      if i' < 1 || i' > k + k' then
        a
      else if i' <= k then
        Core.Expr.Bound_variable {index = i + k'; occurrence = occ}
      else
        Core.Expr.Bound_variable {index = i - k; occurrence = occ}
    | a -> ast_map_lift permut n a
  in
  permut 0

(* What a read substituted by [e] becomes: a variable put for a variable
   renames the read, which stays the occurrence it was; any other term is
   copied there, keeping the occurrences of its own reads. *)
let renamed occ =
  function Core.Expr.Bound_variable {index = j; _} -> Core.Expr.Bound_variable {index = j; occurrence = occ} | e -> e

(** {2 Substitution. [ast_subst e t] substitutes [e] for [Rel 1] in [t]. Lifting
    (of one binder) is done at the same time} *)

let ast_subst_each make =
  let rec subst n = function
    | Core.Expr.Bound_variable {index = i; occurrence = occ} as a ->
      let i' = i - n in
      if Int.equal i' 1 then
        renamed occ (ast_lift n (make ()))
      else if i' < 1 then
        a
      else
        Core.Expr.Bound_variable {index = i - 1; occurrence = occ}
    | a -> ast_map_lift subst n a
  in
  subst 0

let ast_subst e = ast_subst_each (fun () -> e)

(** {2 Generalized substitution. [gen_subst v d t] applies to [t] the
    substitution coded in the [v] array: [(Rel i)] becomes [v.(i-1)]. [d] is the
    correction applied to [Rel] greater than [Array.length v]} *)

let gen_subst v d t =
  let rec subst n = function
    | Core.Expr.Bound_variable {index = i; occurrence = occ} as a ->
      let i' = i - n in
      if i' < 1 then
        a
      else if i' <= Array.length v then
        match
          v.(i' - 1)
        with
        | None -> assert false
        | Some u -> renamed occ (ast_lift n u)
      else
        Core.Expr.Bound_variable {index = i + d; occurrence = occ}
    | a -> ast_map_lift subst n a
  in
  subst 0 t

(** {1 Operations concerning match patterns} *)

let is_basic_pattern = function
  | Core.Pattern.Bound_variable _ | Core.Pattern.Wildcard -> true
  | Core.Pattern.Constructor _ | Core.Pattern.Tuple _ -> false

(** Returns [true] if any branch contains a nested (non-basic) pattern. *)
let has_deep_pattern br =
  let deep = function
    | Core.Pattern.Constructor {fields = l; _} | Core.Pattern.Tuple l -> not (List.for_all is_basic_pattern l)
    | Core.Pattern.Bound_variable _ | Core.Pattern.Wildcard -> false
  in
  Array.exists (fun (b : _ Core.Match.Branch.at) -> deep b.pattern) br

(** Returns [true] if all branches match the standard constructor pattern with
    sequential constructor indices. *)
let is_regular_match br =
  if Array.is_empty br then
    false (* empty match becomes Core.Expr.Runtime_error *)
  else
    try
      let get_r {Core.Match.Branch.pattern = pat; _} =
        match pat with
        | Core.Pattern.Constructor {constructor = r; fields = l} ->
          let is_rel i = function
            | Core.Pattern.Bound_variable j -> Int.equal i j
            | _ -> false
          in
          if not (List.for_all_i is_rel 1 (List.rev l)) then
            raise Impossible;
          r
        | _ -> raise Impossible
      in
      let ind =
        match get_r br.(0) with
        | GlobRef.ConstructRef (ind, _) -> ind
        | _ -> raise Impossible
      in
      let is_ref i tr =
        match get_r tr with
        | GlobRef.ConstructRef (ind', j) ->
          Ind.CanOrd.equal ind ind' && Int.equal j (i + 1)
        | _ -> false
      in
      Array.for_all_i is_ref 0 br
    with Impossible -> false

(** {1 Operations concerning lambdas} *)

(** {2 [collect_lams (Lambda (id1, ..., Lambda (idn, t) ...))] returns [[idn;...;id1]] and
    the term [t]} *)

let collect_lams e =
  let rec collect acc = function
    | Core.Expr.Lambda {parameter = id; parameter_type = ty; body = t} -> collect ((id, ty) :: acc) t
    | x -> (acc, x)
  in
  collect [] e

(** {2 [collect_n_lams] does the same for a precise number of [Core.Expr.Lambda]} *)

let collect_n_lams n e =
  let rec collect acc n t =
    if Int.equal n 0 then
      (acc, t)
    else
      match
        t
      with
      | Core.Expr.Lambda {parameter = id; parameter_type = ty; body = t} -> collect ((id, ty) :: acc) (n - 1) t
      | _ -> assert false
  in
  collect [] n e

(** {2 [remove_n_lams] just removes some [Core.Expr.Lambda]} *)

let rec remove_n_lams n t =
  if Int.equal n 0 then
    t
  else
    match
      t
    with
    | Core.Expr.Lambda {body = t; _} -> remove_n_lams (n - 1) t
    | _ -> assert false

(** {2 [nb_lams] gives the number of head [Core.Expr.Lambda]} *)

let rec nb_lams = function
  | Core.Expr.Lambda {body = t; _} -> succ (nb_lams t)
  | _ -> 0

(** {2 [named_lams] does the converse of [collect_lams]} *)

let rec named_lams ids a =
  match ids with
  | [] -> a
  | (id, ty) :: ids -> named_lams ids (Core.Expr.Lambda {parameter = id; parameter_type = ty; body = a})

(** {2 The same for a specific identifier (resp. anonymous, dummy)} *)

(** [many_lams id a tys] wraps [a] in one lambda per entry of [tys], all bound
    to [id].  The list is in de Bruijn order: its head becomes the innermost
    binder, index 1 in [a]. *)
let rec many_lams id a = function
  | [] -> a
  | ty :: tys -> many_lams id (Core.Expr.Lambda {parameter = id; parameter_type = ty; body = a}) tys

let anonym_tmp_lams a tys = many_lams (Core.Binder_name.Generated anonymous_name) a tys

(* [Core.Type.Axiom] is written deliberately here and nowhere else: these binders are
   [Core.Binder_name.Anonymous], so the erasure pass removes them and no C++ path ever asks what
   they are.  A binder that survives needs a real type -- see
   {!general_optimize_fix}. *)
let dummy_lams a n = many_lams Core.Binder_name.Anonymous a (List.init n (fun _ -> Core.Type.Axiom))

(** {2 mixed according to a signature} *)

(* An anonymous lambda for each [Core.Signature.Argument.Runtime] entry of the signature, at its type
   among [types], and a [Core.Binder_name.Anonymous] one for each
   [Core.Signature.Argument.Erased].  The [types] list provides one type per
   signature element; if the lists go out of sync (e.g. the types list is
   shorter), we fall back to [Core.Type.Axiom] to avoid crashing. *)
let rec anonym_or_dummy_lams_typed a types = function
  | [] -> a
  | Core.Signature.Argument.Runtime :: s ->
    let ty, rest =
      match types with
      | t :: ts -> (t, ts)
      | [] -> (Core.Type.Axiom, [])
    in
    Core.Expr.Lambda {parameter = anonymous; parameter_type = ty; body = anonym_or_dummy_lams_typed a rest s}
  | Core.Signature.Argument.Erased k :: s ->
    let rest =
      match types with
      | _ :: ts -> ts
      | [] -> []
    in
    Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous;
                      parameter_type = Core.Type.Erased k;
                      body = anonym_or_dummy_lams_typed a rest s}

(** {1 Operations concerning eta} *)

(** {2 The following function creates [Core.Expr.Bound_variable n;...;Core.Expr.Bound_variable 1]} *)

let rec eta_args n = if Int.equal n 0 then [] else Core.Expr.fresh_rel n :: eta_args (pred n)

(** {2 Same, but filtered by a signature} *)

let rec eta_args_sign n = function
  | [] -> []
  | Core.Signature.Argument.Runtime :: s -> Core.Expr.fresh_rel n :: eta_args_sign (n - 1) s
  | Core.Signature.Argument.Erased _ :: s -> eta_args_sign (n - 1) s

(** {2 This one tests [Core.Expr.Bound_variable (n+k); ... ;Core.Expr.Bound_variable (1+k)]} *)

let rec test_eta_args_lift k n = function
  | [] -> Int.equal n 0
  | Core.Expr.Bound_variable {index = m; _} :: q -> Int.equal (k + n) m && test_eta_args_lift k (pred n) q
  | _ -> false

(** {2 Computes an eta-reduction} *)

let eta_red e =
  let ids, t = collect_lams e in
  let n = List.length ids in
  if Int.equal n 0 then
    e
  else
    match
      t
    with
    | Core.Expr.Apply {callee = f; arguments = a} ->
      let m = List.length a in
      let ids, body, args =
        if Int.equal m n then
          ([], f, a)
        else if m < n then
          (List.skipn m ids, f, a)
        else (* m > n *)
          let a1, a2 = List.chop (m - n) a in
          ([], Core.Expr.Apply {callee = f; arguments = a1}, a2)
      in
      let p = List.length args in
      if test_eta_args_lift 0 p args && not (ast_occurs_itvl 1 p body) then
        named_lams ids (ast_lift (-p) body)
      else
        e
    | _ -> e

(* Performs an eta-reduction when the core is atomic and value, or otherwise
   returns None *)

let atomic_eta_red e =
  let ids, t = collect_lams e in
  let n = List.length ids in
  match t with
  | Core.Expr.Apply {callee = f; arguments = a} when test_eta_args_lift 0 n a ->
    ( match f with
    | Core.Expr.Bound_variable {index = k; occurrence = occ} when k > n ->
      Some (Core.Expr.Bound_variable {index = k - n; occurrence = occ})
    | Core.Expr.Global _ | Core.Expr.Erased_value _ -> Some f
    | _ -> None )
  | _ -> None

(** {2 Computes all head linear beta-reductions possible in [(t a)]. Non-linear
    head beta-redex become let-in} *)

let rec linear_beta_red a t =
  match (a, t) with
  | [], _ -> t
  | a0 :: a, Core.Expr.Lambda {parameter = id; parameter_type = ty; body = t} ->
    ( match nb_occur_match t with
    | 0 -> linear_beta_red a (ast_pop t)
    | 1 -> linear_beta_red a (ast_subst a0 t)
    | _ ->
      let a = List.map (ast_lift 1) a in
      Core.Expr.Let {binder = id;
                     binder_type = ty;
                     value = a0;
                     body = linear_beta_red a t;
                     occurrence = Core.Occurrence.fresh ()} )
  | _ -> Core.Expr.Apply {callee = t; arguments = a}

(** Marks leading lambdas as temporary (for later cleanup during optimization).
*)
let rec tmp_head_lams = function
  | Core.Expr.Lambda {parameter = id; parameter_type = ty; body = t} ->
    Core.Expr.Lambda {parameter = tmp_id id; parameter_type = ty; body = tmp_head_lams t}
  | e -> e

(** {2 Applies a substitution [s] of constants by their body, plus linear beta
    reductions at modified positions. Moreover, we mark some lambdas as suitable
    for later linear reduction (this helps the inlining of recursors)} *)

(* [a] with the holes of its global uses renamed apart from every other: a
   body inlined at a call is a new set of uses, each of which leaves open
   what its original did, independently of the original and of every other
   copy. *)
let freshen_holes a =
  let renamed = Hashtbl.create 4 in
  ast_map_types
    (fill_holes (fun h ->
         match Hashtbl.find_opt renamed h with
         | Some t -> Some t
         | None ->
           let t = fresh_hole () in
           Hashtbl.add renamed h t;
           Some t ) )
    a

let instantiate_body ~reader use body =
  freshen_holes (ast_map_types (instantiate_written ~reader use) body)

let rec ast_glob_subst s t =
  (* The body of [refe] at the type arguments [tys] an occurrence names,
     with cells of its own ({!freshen_metas}).  Inlined, the body's type
     variables stand for nothing in the caller, so each is replaced: by the
     type the occurrence names, or, where it leaves one erased, by a hole
     ([Fix_F]'s family [P], erased where Equations calls it), which the
     caller's own reconstruction may fill.  None of the body's variables
     survives to be read in the caller's numbering. *)
  let body (use : _ Core.Global_use.at) =
    let b = freshen_metas (Core.Ref.User.Map.find use.callee s) in
    let informative = function Core.Type.Erased _ | Core.Type.Unknown -> false | _ -> true in
    let use =
      Core.Global_use.map_types (fun t -> if informative t then t else new_meta ()) use
    in
    instantiate_body ~reader:"ast_glob_subst" use b
  in
  match t with
  | Core.Expr.Apply {callee = (Core.Expr.Global ({callee = GlobRef.ConstRef _; _} as use) as f); arguments = a} ->
    let a = List.map (fun e -> tmp_head_lams (ast_glob_subst s e)) a in
    ( try linear_beta_red a (body use)
      with Not_found -> Core.Expr.Apply {callee = f; arguments = a} )
  | Core.Expr.Global ({callee = GlobRef.ConstRef _; _} as use) ->
    (try body use with Not_found -> t)
  | _ -> ast_map (ast_glob_subst s) t

(** {1 Auxiliary functions used in simplification of Core matches} *)

(* Factorisation of some match branches into a common "x -> f x" branch may
   break types sometimes. Example: [type 'x a = A]. Then [let id = function A ->
   A] has type ['x a -> 'y a], which is incompatible with the type of [let id x
   = x]. We check that the type arguments of the inductive are preserved by
   our transformation.

   TODO: this verification should be done someday modulo expansion of type
   definitions. *)

(** {2 [branch_as_function b typ (l,p,c)] tries to see branch [c] as a function
    [f] applied to [Core.Expr.Construct(r,l)]. For that it transforms any [Core.Expr.Construct(r,l)] in
    [Core.Expr.Bound_variable 1] and raises [Impossible] if any variable in [l] occurs outside such
    a [Core.Expr.Construct]} *)

let branch_as_fun typ (l, p, c) =
  let nargs = List.length l in
  let cons =
    match p with
    | Core.Pattern.Constructor {constructor = r; _} when Core.Pattern.binds_all nargs p ->
      Core.Expr.Construct {result_type = typ;
                           constructor = r;
                           arguments = eta_args nargs;
                           occurrence = Core.Occurrence.fresh ()}
    | Core.Pattern.Constructor {constructor = r; fields = pl} ->
      let pat2rel = function
        | Core.Pattern.Bound_variable i -> Core.Expr.fresh_rel i
        | _ -> raise Impossible
      in
      Core.Expr.Construct {result_type = typ;
                           constructor = r;
                           arguments = List.map pat2rel pl;
                           occurrence = Core.Occurrence.fresh ()}
    | _ -> raise Impossible
  in
  let rec genrec n = function
    | Core.Expr.Bound_variable {index = i; occurrence = occ} as c ->
      let i' = i - n in
      if i' < 1 then
        c
      else if i' > nargs then
        Core.Expr.Bound_variable {index = i - nargs + 1; occurrence = occ}
      else
        raise Impossible
    | Core.Expr.Construct _ as cons' when eq_core_ast cons' (ast_lift n cons) -> Core.Expr.fresh_rel (n + 1)
    | a -> ast_map_lift genrec n a
  in
  genrec 0 c

(** {2 [branch_as_cst (l,p,c)] tries to see branch [c] as a constant independent
    from the pattern [Core.Expr.Construct(r,l)]. For that is raises [Impossible] if any
    variable in [l] occurs in [c], and otherwise returns [c] lifted to appear
    like a function with one arg (for uniformity with [branch_as_fun]). NB:
    [Core.Expr.Construct(r,l)] might occur nonetheless in [c], but only when [l] is empty,
    i.e. when [r] is a constant constructor} *)

let branch_as_cst (l, _, c) =
  let n = List.length l in
  if ast_occurs_itvl 1 n c then raise Impossible;
  ast_lift (1 - n) c

(* A branch [Core.Expr.Construct(r,l)->c] can be seen at the same time as a function branch
   and a constant branch, either because: - [Core.Expr.Construct(r,l)] doesn't occur in [c].
   For example : "A -> B" - this constructor is constant (i.e. [l] is empty).
   For example "A -> A" When searching for the best factorisation below, we'll
   try both. *)

(* The following structure allows recording which element occurred at what
   position, and then finally return the most frequent element and its
   positions. *)

(** A census for branch factorization, one per {!factor_branches}: [census_add]
    records an element at a position, [census_max] returns the most frequent
    element and its positions, [census_clean] resets the census. *)
let census () =
  let h = ref [] in
  let clearf () = h := [] in
  let rec add k v = function
    | [] -> raise Not_found
    | ((k', s) as p) :: l ->
      if eq_core_ast (fst k) (fst k') then
        (k', Int.Set.add v s) :: l
      else
        p :: add k v l
  in
  let addf k i =
    try h := add k i !h with Not_found -> h := (k, Int.Set.singleton i) :: !h
  in
  let maxf () =
    let len = ref 0
    and lst = ref Int.Set.empty
    and elm = ref (Core.Expr.Axiom_value "should not appear", Core.Type.Axiom) in
    List.iter
      (fun (e, s) ->
        let n = Int.Set.cardinal s in
        if n > !len then (
          len := n;
          lst := s;
          elm := e ) )
      !h;
    (!elm, !lst)
  in
  (addf, maxf, clearf)

(* [factor_branches] return the longest possible list of branches that have the
   same factorization, either as a function or as a constant. *)

let is_opt_pat {Core.Match.Branch.pattern = p; _} =
  match p with
  | Core.Pattern.Bound_variable _ | Core.Pattern.Wildcard -> true
  | _ -> false

(** Attempts to factor common branches in a match. Returns [Some (f, ints)]
    where [f] is the factored body and [ints] the set of branch indices sharing
    that body, or [None] if no factoring is possible. *)
let factor_branches o typ br =
  if Array.exists is_opt_pat br then None (* already optimized *)
  else begin
    let census_add, census_max, census_clean = census () in
    census_clean ();
    for i = 0 to Array.length br - 1 do
      let {Core.Match.Branch.binders = ids; pattern = pat; body = body; _} = br.(i) in
      if o.opt_case_idr then
        (try census_add (branch_as_fun typ (ids, pat, body), Core.Type.Axiom) i
         with Impossible -> ());
      if o.opt_case_cst then
        (try census_add (branch_as_cst (ids, pat, body), Core.Type.Axiom) i
         with Impossible -> ());
    done;
    let br_factor, br_set = census_max () in
    census_clean ();
    let n = Int.Set.cardinal br_set in
    if n = 0 then None
    else if Array.length br >= 2 && n < 2 then None
    else Some (br_factor, br_set)
  end

(** {2 If all branches are functions, try to permute the case and the functions}
*)

(** Merges two [(Core.Binder_name.t * Core.Type.t)] lists, preferring non-Dummy names from
    either side. *)
let rec merge_ids' ids ids' =
  match (ids, ids') with
  | [], l -> l
  | l, [] -> l
  | i :: ids, i' :: ids' ->
    (if fst i == Core.Binder_name.Anonymous then i' else i) :: merge_ids' ids ids'

(** Checks if a Core node is an exception/error expression. *)
let is_exn = function
  | Core.Expr.Runtime_error _ -> true
  | _ -> false

(** Whether [a] does nothing but raise.  Binders in front of the raise do not
    change that: nothing gets to be bound, because the raise comes first. *)
let rec only_throws = function
  | Core.Expr.Runtime_error _ | Core.Expr.Axiom_value _ -> true
  | Core.Expr.Lambda {body = a; _}
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    only_throws a
  | _ -> false

(** Permutes a case expression with surrounding function applications when all
    branches are functions.  The lambdas leave the branches, so each branch's
    result type loses their arrows. *)
let permut_case_fun br acc =
  let nb = ref max_int in
  Array.iter
    (fun {Core.Match.Branch.body = t; _} ->
      let ids, c = collect_lams t in
      let n = List.length ids in
      if n < !nb && not (is_exn c) then nb := n )
    br;
  if Int.equal !nb max_int || Int.equal !nb 0 then
    ([], br)
  else
    let br = Array.copy br in
    let ids = ref [] in
    for i = 0 to Array.length br - 1 do
      let {Core.Match.Branch.binders = l; body = t; result_type = rty; _} as b = br.(i) in
      let b = {b with Core.Match.Branch.result_type = branch_type_applied !nb rty} in
      let local_nb = nb_lams t in
      if local_nb < !nb then (* t = Core.Expr.Runtime_error ... *)
        br.(i) <- {b with Core.Match.Branch.body = remove_n_lams local_nb t}
      else
        let local_ids, t = collect_n_lams !nb t in
        ids := merge_ids' !ids local_ids;
        br.(i) <- {b with Core.Match.Branch.body = permut_rels !nb (List.length l) t}
    done;
    (!ids, br)

(** {1 Generalized iota-reduction} *)

(* Definition of a generalized iota-redex: it's a [Core.Expr.Match(e,br)] where the head
   [e] is a [Core.Expr.Construct] or made of [Core.Expr.Match]'s with [Core.Expr.Construct] as leaf branches. A
   generalized iota-redex is transformed into beta-redexes. *)

(* In [iota_red], we try to simplify a [Core.Expr.Match(_,Core.Expr.Construct(typ,r,a),br)]. Argument
   [i] is the branch we consider, we should lift what comes from [br] by
   [lift] *)

let rec iota_red i lift br ((typ, r, a, occ) as cons) =
  if i >= Array.length br then raise Impossible;
  let {Core.Match.Branch.binders = ids; pattern = p; body = c; _} = br.(i) in
  match p with
  | Core.Pattern.Constructor {constructor = r'; _} when not (GlobRef.CanOrd.equal r' r) ->
    iota_red (i + 1) lift br cons
  | Core.Pattern.Constructor _ when Core.Pattern.binds_all (List.length ids) p ->
    let c = named_lams (List.rev ids) c in
    let c = ast_lift lift c in
    Core.Expr.Apply {callee = c; arguments = a}
  | Core.Pattern.Bound_variable 1 when Int.equal (List.length ids) 1 ->
    let c = Core.Expr.Lambda {parameter = fst (List.hd ids); parameter_type = snd (List.hd ids); body = c} in
    let c = ast_lift lift c in
    Core.Expr.Apply {callee = c;
                     arguments = [Core.Expr.Construct {result_type = typ;
                                                       constructor = r;
                                                       arguments = a;
                                                       occurrence = occ}]}
  | Core.Pattern.Wildcard when List.is_empty ids -> ast_lift lift c
  | _ -> raise Impossible (* TODO: handle some more cases *)

(** Performs generalized iota-reduction by traversing matches in the scrutinee.
    Each inner match's branches now end in an outer branch, so they take the
    outer match's result type: the inner one described the scrutinee they
    used to compute. *)
let iota_gen br hd =
  if Array.length br = 0 then raise Impossible;
  let rty = br.(0).Core.Match.Branch.result_type in
  let rec iota k = function
    | Core.Expr.Construct {result_type = typ; constructor = r; arguments = a; occurrence = occ} ->
      iota_red 0 k br (typ, r, a, occ)
    | Core.Expr.Match {scrutinee_type = typ; scrutinee = e; branches = br'; occurrence = occ} ->
      let new_br =
        Array.map
          (fun (b : _ Core.Match.Branch.at) ->
            {b with Core.Match.Branch.body = iota (k + List.length b.binders) b.body;
                    result_type = rty} )
          br'
      in
      Core.Expr.Match {scrutinee_type = typ; scrutinee = e; branches = new_br; occurrence = occ}
    | _ -> raise Impossible
  in
  iota 0 hd

(** Checks if a Core expression is atomic (has no subexpressions). *)
let is_atomic = function
  | Core.Expr.Bound_variable _ | Core.Expr.Global _ | Core.Expr.Runtime_error _ | Core.Expr.Erased_value _ -> true
  | _ -> false

(** Checks if an expression is an immediate application of Rel 1. *)
let is_imm_apply = function
  | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = 1; _}; _} -> true
  | _ -> false

(** Checks if an identifier is a Program-generated branch (named
    "program_branch_NN"). *)
let is_program_branch = function
  | Core.Binder_name.Generated _ | Core.Binder_name.Anonymous -> false
  | Core.Binder_name.Source id ->
    let s = Id.to_string id in
    ( try Scanf.sscanf s "program_branch_%d%!" (fun _ -> true)
      with Scanf.Scan_failure _ | End_of_file -> false )

(** Inlines a let-binding when the bound variable is used at most once (linear
    usage). *)
let expand_linear_let o id e =
  o.opt_lin_let || is_tmp id || is_program_branch id || is_imm_apply e

(** {1 The main simplification function} *)

(* Some beta-iota reductions + simplifications. *)

(* Rocq's own [simpl] additionally moved its [Core.Expr.Coerce] (our [Core.Expr.Coerce]) away
   from the node it was inserted at -- out of an application's result onto its
   head, into each branch of a match, under a lambda, off an argument
   altogether -- and collapsed the [Core.Expr.Coerce] on nested ones.  That is sound
   only while the node carries no types, as it did upstream.  Here [Core.Expr.Coerce]
   names the two types of one specific boundary (see {!Core.Expr.t}), so
   relocating the node leaves it describing a gap it is no longer at, and the
   backend's [coerce] reads those types as authoritative.  Those rewrites are
   therefore not made here; they would buy only a slightly smaller AST.

   The one case that is handled is a coercion wrapping a lambda that is
   then applied ([simpl_app] below), because leaving that beta-redex standing
   reaches the backend as an immediately-invoked lambda.  It is handled by
   {!split_arrow_coercion}, which does not move the coercion but splits it
   along the arrow it already describes. *)

(** Split a coercion between two function types into the coercion on the
    domain and the coercion on the codomain.  A value flows into the domain
    against the arrow, so that half is reversed.  Returns [None] unless both
    sides are arrows, in which case the coercion describes something other
    than a function boundary and must be left where it is. *)
let split_arrow_coercion from into =
  match (from, into) with
  | Core.Type.Arrow {parameter = d; result = c}, Core.Type.Arrow {parameter = d'; result = c'} ->
    Some
      ( put_magic_if ~from:d' ~into:d (needs_magic (d', d)),
        put_magic_if ~from:c ~into:c' (needs_magic (c, c')) )
  | _ -> None

(** The constant [label] of library [file], or of its module [modname]. *)
let con_in_file file label =
  Constant.make2 (ModPath.MPfile (dirpath_of_string file)) (Label.make label)

let con_in_module file modname label =
  Constant.make2
    (ModPath.MPdot (ModPath.MPfile (dirpath_of_string file), Label.make modname))
    (Label.make label)

(** The value a pure, total comparison takes when both arguments are one
    variable: reflexive orders and equalities are [true], strict orders
    [false].  Keyed on canonical names, so a use through a module that
    [Include]s the defining one (e.g. [Stdlib.Arith.PeanoNat.Nat]) is found. *)
let self_comparisons =
  let nat = con_in_file "Corelib.Init.Nat" in
  let n_core = con_in_module "Corelib.BinNums.NatDef" "N" in
  let n_std = con_in_module "Stdlib.NArith.BinNatDef" "N" in
  let pos_core = con_in_module "Corelib.BinNums.PosDef" "Pos" in
  let pos_std = con_in_module "Stdlib.PArith.BinPosDef" "Pos" in
  let z = con_in_module "Corelib.BinNums.IntDef" "Z" in
  let z_std = con_in_module "Stdlib.ZArith.BinIntDef" "Z" in
  let int63 = con_in_file "Corelib.Numbers.Cyclic.Int63.PrimInt63" in
  List.fold_left
    (fun m (c, v) -> Cmap.add c v m)
    Cmap.empty
    [
      (nat "leb", true); (nat "eqb", true); (nat "ltb", false);
      (n_core "leb", true); (n_std "eqb", true); (n_std "ltb", false);
      (pos_core "leb", true); (pos_core "eqb", true); (pos_std "ltb", false);
      (z "leb", true); (z "eqb", true); (z "ltb", false);
      (z_std "geb", true); (z_std "gtb", false);
      (int63 "leb", true); (int63 "eqb", true); (int63 "ltb", false);
      (con_in_file "Stdlib.Bool.Bool" "eqb", true);
    ]

(** Whether [a] and [b] are one read of storage: the same variable, or the
    same projection of the same such read -- a projection called, or a
    record match of one branch returning one of its fields.  Evaluating
    either is total and pure, so both evaluate to one value. *)
let rec same_storage a b =
  match (a, b) with
  | Core.Expr.Bound_variable {index = i; _}, Core.Expr.Bound_variable {index = j; _} -> Int.equal i j
  | ( Core.Expr.Apply {callee = Core.Expr.Global {callee = p; _}; arguments = xs},
      Core.Expr.Apply {callee = Core.Expr.Global {callee = q; _}; arguments = ys} ) ->
    (* At most the record's parameters and the record: a projection
       applied further is a call of the field. *)
    GlobRef.CanOrd.equal p q && Table.is_projection p
    && List.length xs <= Table.projection_arity p + 1
    && List.equal (fun x y -> match (x, y) with
        | Core.Expr.Erased_value _, Core.Expr.Erased_value _ -> true
        | _ -> same_storage x y) xs ys
  | ( Core.Expr.Match {scrutinee = s; branches = [|{binders = l; pattern = pat; body = Core.Expr.Bound_variable {index = i; _}; _}|]; _},
      Core.Expr.Match {scrutinee = s'; branches = [|{binders = l'; pattern = pat'; body = Core.Expr.Bound_variable {index = j; _}; _}|]; _} ) ->
    Int.equal i j && Int.equal (List.length l) (List.length l') && i <= List.length l
    && eq_core_pattern pat pat' && same_storage s s'
  | _ -> false

(** [v] as a [bool] constructor. *)
let bool_value v =
  Core.Expr.Construct {result_type = Core.Type.Global_app {head = Rocqlib.lib_ref "core.bool.type";
                                                           type_arguments = [];
                                                           index_arguments = []};
                       constructor = Rocqlib.lib_ref (if v then "core.bool.true" else "core.bool.false");
                       arguments = [];
                       occurrence = Core.Occurrence.fresh ()}

(** Whether [x] and [y] are one read of storage and the other's [negb]. *)
let negation_of_itself x y =
  let negb = Rocqlib.lib_ref "core.bool.negb" in
  let negates a b =
    match a with
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = n; _}; arguments = [a']} ->
      GlobRef.CanOrd.equal n negb && same_storage a' b
    | _ -> false
  in
  negates x y || negates y x

(** [Some v] when [f a] is a comparison of one read of storage with itself
    ({!same_storage}), or an [orb] or [andb] of one read and its [negb], [v]
    its value as a [bool] constructor. *)
let fold_self_comparison f a =
  match (f, a) with
  | Core.Expr.Global {callee = GlobRef.ConstRef c; _}, [x; y] when same_storage x y ->
    Option.map bool_value (Cmap.find_opt c self_comparisons)
  | Core.Expr.Global {callee = c; _}, [x; y] when negation_of_itself x y ->
    if GlobRef.CanOrd.equal c (Rocqlib.lib_ref "core.bool.orb") then Some (bool_value true)
    else if GlobRef.CanOrd.equal c (Rocqlib.lib_ref "core.bool.andb") then Some (bool_value false)
    else None
  | _ -> None

(** Core simplification: beta-reduction, iota-reduction, let-inlining, and
    other optimizations. *)
let rec simpl o = function
  | Core.Expr.Apply {callee = f; arguments = []} -> simpl o f
  | Core.Expr.Apply {callee = Core.Expr.Apply {callee = f; arguments = a}; arguments = a'} ->
    simpl o (Core.Expr.Apply {callee = f; arguments = a @ a'})
  | Core.Expr.Apply {callee = f; arguments = a} -> simpl_app o (List.map (simpl o) a) (simpl o f)
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = e; branches = br; occurrence = occ} ->
    let br = Array.map (fun (b : _ Core.Match.Branch.at) -> {b with Core.Match.Branch.body = simpl o b.body}) br in
    simpl_case o typ br (simpl o e) occ
  | Core.Expr.Let {binder = Core.Binder_name.Anonymous; body = e; _} -> simpl o (ast_pop e)
  | Core.Expr.Let {binder = id; binder_type = t; value = c; body = e; occurrence = occ} ->
    let e = simpl o e in
    if
      is_atomic c
      || is_atomic e
      ||
      let n = nb_occur_match e in
      Int.equal n 0 || (Int.equal n 1 && expand_linear_let o id e)
    then
      simpl o (ast_subst c e)
    else
      Core.Expr.Let {binder = id; binder_type = t; value = simpl o c; body = e; occurrence = occ}
  | Core.Expr.Fixpoint g -> simpl_fix o g (fun g -> Core.Expr.Fixpoint g)
  | Core.Expr.Cofixpoint g -> simpl_fix o g (fun g -> Core.Expr.Cofixpoint g)
    (* Dummy fixpoint *)
  (* An exception never yields a value, so there is no representation gap for
     a coercion around it to describe. *)
  | Core.Expr.Coerce {value = (Core.Expr.Runtime_error _ as e); _}
  | Core.Expr.Boxed_value {value = (Core.Expr.Runtime_error _ as e); _}
  | Core.Expr.Lambda_group_barrier {value = (Core.Expr.Runtime_error _ as e); _} -> e
  | Core.Expr.Lambda _ as e ->
    ( match atomic_eta_red e with
    | Some e' -> e'
    | None -> ast_map (simpl o) e )
  | a -> ast_map (simpl o) a

(** Simplifies function application, performing beta-reduction and pushing
    applications into let/case. Invariant: argument list [a] is non-empty. *)
(* A fixpoint group rebuilt by [fix] from new bodies, or its selected body
   alone when that body does not recurse. *)
and simpl_fix o g fix =
  let n = Core.Recursion.Group.length g in
  let selected = (Core.Recursion.Group.selected_member g).body in
  if ast_occurs_itvl 1 n selected then fix (Core.Recursion.Group.map_bodies (simpl o) g)
  else simpl o (ast_lift (-n) selected)

and simpl_app o a = function
  | Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous; parameter_type = ty; body = t} ->
    simpl o (Core.Expr.Apply {callee = ast_pop t; arguments = List.tl a})
  | Core.Expr.Lambda {parameter = id; parameter_type = ty; body = t} ->
    (* Beta redex *)
    ( match nb_occur_match t with
    | 0 -> simpl o (Core.Expr.Apply {callee = ast_pop t; arguments = List.tl a})
    | 1 when is_tmp id || o.opt_lin_beta ->
      simpl o (Core.Expr.Apply {callee = ast_subst (List.hd a) t; arguments = List.tl a})
    | _ ->
      let a' = List.map (ast_lift 1) (List.tl a) in
      simpl o (Core.Expr.Let {binder = id;
                              binder_type = ty;
                              value = List.hd a;
                              body = Core.Expr.Apply {callee = t; arguments = a'};
                              occurrence = Core.Occurrence.fresh ()}) )
  | Core.Expr.Coerce {source_type = from; target_type = into; value = (Core.Expr.Lambda _ as lam); _} as f -> (
    (* [(coerce (fun x => t)) a] -- reduce the redex without relocating the
       coercion: it is split along its own arrow, the domain half landing on
       the argument and the codomain half on the result. *)
    match split_arrow_coercion from into with
    | Some (on_dom, on_cod) ->
      let arg = on_dom (List.hd a) in
      simpl o (on_cod (Core.Expr.Apply {callee = lam;
                                        arguments = [arg]}) |> fun r -> Core.Expr.Apply {callee = r;
                                                                                         arguments = List.tl a})
    | None -> Core.Expr.Apply {callee = f; arguments = a} )
  | Core.Expr.Let {binder = id; binder_type = t; value = e1; body = e2; occurrence = occ} when o.opt_let_app ->
    (* Application of a letin: we push arguments inside *)
    Core.Expr.Let {binder = id;
                   binder_type = t;
                   value = e1;
                   body = simpl o (Core.Expr.Apply {callee = e2; arguments = List.map (ast_lift 1) a});
                   occurrence = occ}
  | Core.Expr.Match {scrutinee_type = typ; scrutinee = e; branches = br; occurrence = occ} when o.opt_case_app ->
    (* Application of a case: we push arguments inside *)
    let br' =
      Array.map
        (fun ({Core.Match.Branch.binders = l; body = t; result_type = rty; _} as b) ->
          let k = List.length l in
          let a' = List.map (ast_lift k) a in
          {b with Core.Match.Branch.body = simpl o (Core.Expr.Apply {callee = t; arguments = a'});
                  result_type = branch_type_applied (List.length a) rty} )
        br
    in
    simpl o (Core.Expr.Match {scrutinee_type = typ; scrutinee = e; branches = br'; occurrence = occ})
  | (Core.Expr.Erased_value _ | Core.Expr.Runtime_error _) as e ->
    e (* We just discard arguments in those cases. *)
  | f -> (
    match fold_self_comparison f a with
    | Some b -> b
    | None -> Core.Expr.Apply {callee = f; arguments = a} )

(** Simplifies match expressions via iota-reduction and case permutation.
    Invariant: all empty matches should be [Core.Expr.Runtime_error]. *)
and simpl_case o typ br e occ =
  try
    (* Generalized iota-redex *)
    if not o.opt_case_iot then raise Impossible;
    simpl o (iota_gen br e)
  with Impossible ->
    (* Swap the case and the lam if possible *)
    let ids, br = if o.opt_case_fun then permut_case_fun br [] else ([], br) in
    let n = List.length ids in
    if not (Int.equal n 0) then
      simpl o (named_lams ids (Core.Expr.Match {scrutinee_type = typ;
                                                scrutinee = ast_lift n e;
                                                branches = br;
                                                occurrence = occ}))
    else if
      (* Can we merge several branches as the same constant or function ? *)
      is_custom_match br
    then
      Core.Expr.Match {scrutinee_type = typ; scrutinee = e; branches = br; occurrence = occ}
    else
      match factor_branches o typ br with
      | Some ((f, _), ints) when Int.Set.cardinal ints = Array.length br
                              && not (ast_occurs 1 f) ->
        (* All branches identical and don't use scrutinee — eliminate match *)
        simpl o (ast_pop f)
      | Some ((f, _), ints) when not (ast_occurs 1 f) ->
        let rty = br.(0).result_type in
        let last_br =
          {Core.Match.Branch.binders = []; result_type = rty; pattern = Core.Pattern.Wildcard; body = ast_pop f}
        in
        let brl = Array.to_list br in
        let brl_opt = List.filteri (fun i _ -> not (Int.Set.mem i ints)) brl in
        Core.Expr.Match {scrutinee_type = typ;
                         scrutinee = e;
                         branches = Array.of_list (brl_opt @ [last_br]);
                         occurrence = occ}
      | _ -> Core.Expr.Match {scrutinee_type = typ; scrutinee = e; branches = br; occurrence = occ}

(** {1 Local prop elimination} *)
(* We try to eliminate as many [prop] as possible inside an [Core.Expr.t]. *)

(** {2 In a list, it selects only the elements corresponding to a [Core.Signature.Argument.Runtime] in the
    boolean list [l]} *)

let rec select_via_bl l args =
  match (l, args) with
  | [], _ -> args
  | Core.Signature.Argument.Runtime :: l, a :: args -> a :: select_via_bl l args
  | Core.Signature.Argument.Erased _ :: l, a :: args -> select_via_bl l args
  | _ -> assert false

(** {2 [kill_some_lams] removes some head lambdas according to the signature
    [bl]. This list is built on the identifier list model: outermost lambda is
    on the right. [Rels] corresponding to removed lambdas are not supposed to
    occur (except maybe in the case of Core.Erasure_reason.Configured_implicit), and the other [Rels] are made
    correct via a [gen_subst]. Output is not directly a [Core.Expr.t], compose with
    [named_lams] if needed} *)

let is_impl_kill = function
  | Core.Signature.Argument.Erased (Core.Erasure_reason.Configured_implicit _) -> true
  | _ -> false

(** Removes head lambdas at positions marked [Erased] in signature [bl]. Adjusts de
    Bruijn indices accordingly. *)
let kill_some_lams bl (ids, c) =
  let n = List.length bl in
  let n' = List.fold_left (fun n b -> if b == Core.Signature.Argument.Runtime then n + 1 else n) 0 bl in
  if Int.equal n n' then
    (ids, c)
  else if Int.equal n' 0 && not (List.exists is_impl_kill bl) then
    ([], ast_lift (-n) c)
  else
    let v = Array.make n None in
    let rec parse_ids i j = function
      | [] -> ()
      | Core.Signature.Argument.Runtime :: l ->
        v.(i) <- Some (Core.Expr.fresh_rel j);
        parse_ids (i + 1) (j + 1) l
      | Core.Signature.Argument.Erased (Core.Erasure_reason.Configured_implicit _ as k) :: l ->
        v.(i) <- Some (Core.Expr.Erased_value k);
        parse_ids (i + 1) j l
      | Core.Signature.Argument.Erased _ :: l -> parse_ids (i + 1) j l
    in
    parse_ids 0 1 bl;
    (select_via_bl bl ids, gen_subst v (n' - n) c)

(** {2 [kill_dummy_lams] uses the last function to kill the lambdas
    corresponding to a [dummy_name]. It can raise [Impossible] if there is
    nothing to do, or if there is no lambda left at all. In addition, it
    accepts a signature that may mention some implicits} *)

(** Merges an implicit signature with an identifier list, creating a full
    [Runtime]/[Erased] signature. *)
let rec merge_implicits ids s =
  match (ids, s) with
  | [], _ -> []
  | _, [] -> List.map sign_of_id ids
  | Core.Binder_name.Anonymous :: ids, _ :: s ->
    Core.Signature.Argument.Erased Core.Erasure_reason.Proof :: merge_implicits ids s
  | _ :: ids, (Core.Signature.Argument.Erased (Core.Erasure_reason.Configured_implicit _) as k) :: s ->
    k :: merge_implicits ids s
  | _ :: ids, _ :: s -> Core.Signature.Argument.Runtime :: merge_implicits ids s

(** Removes dummy (erased) lambda parameters from a term. Raises Impossible if
    nothing to remove. *)
let kill_dummy_lams sign c =
  let ids, c = collect_lams c in
  let bl = merge_implicits (List.map fst ids) (List.rev sign) in
  if not (List.memq Core.Signature.Argument.Runtime bl) then raise Impossible;
  let rec fst_kill n = function
    | [] -> raise Impossible
    | Core.Signature.Argument.Erased _ :: bl -> n
    | Core.Signature.Argument.Runtime :: bl -> fst_kill (n + 1) bl
  in
  let skip = max 0 (fst_kill 0 bl - 1) in
  let ids_skip, ids = List.chop skip ids in
  let _, bl = List.chop skip bl in
  let c = named_lams ids_skip c in
  let ids', c = kill_some_lams bl (ids, c) in
  ((ids, bl), named_lams ids' c)

(** Eta-expands a function to match a given signature, adding lambdas as needed.
*)
let eta_expansion_sign ?(types = []) s (ids, c) =
  let rec abs ids rels i types = function
    | [] ->
      let a =
        List.rev_map
          (function
            | Core.Expr.Bound_variable {index = x; occurrence = occ} ->
              Core.Expr.Bound_variable {index = i - x; occurrence = occ}
            | a -> a )
          rels
      in
      (ids, Core.Expr.Apply {callee = ast_lift (i - 1) c; arguments = a})
    | Core.Signature.Argument.Runtime :: l ->
      (* [types] carries one entry per signature element, so a [Core.Signature.Argument.Runtime] binder
         gets the argument's real type.  Falling back to [Core.Type.Axiom] when the
         lists go out of sync would print as the undeclared C++ type [axiom];
         [Core.Type.Unknown] at least erases to [std::any]. *)
      let ty, rest =
        match types with
        | t :: ts -> (t, ts)
        | [] -> (Core.Type.Unknown, [])
      in
      abs ((anonymous, ty) :: ids) (Core.Expr.fresh_rel i :: rels) (i + 1) rest l
    | Core.Signature.Argument.Erased k :: l ->
      let rest = match types with _ :: ts -> ts | [] -> [] in
      abs ((Core.Binder_name.Anonymous, Core.Type.Erased k) :: ids) (Core.Expr.Erased_value k :: rels) (i + 1) rest l
  in
  abs ids [] 1 types s

(** Removes erased arguments from match branches by eta-expanding and
    eliminating the erased lambdas. *)
let case_expunge ?(types = []) s e =
  let m = List.length s in
  let n = nb_lams e in
  let p =
    if m <= n then
      collect_n_lams m e
    else
      let types = if List.length types > n then List.skipn n types else [] in
      eta_expansion_sign ~types (List.skipn n s) (collect_lams e)
  in
  kill_some_lams (List.rev s) p

(** Removes erased leading lambdas from a term. Leaves one dummy lambda if all
    are logical and language is strict. *)
let term_expunge s (ids, c) =
  if List.is_empty s then
    c
  else
    let ids, c = kill_some_lams (List.rev s) (ids, c) in
    if List.is_empty ids && sign_kind s == UnsafeLogicalSig then
      Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous;
                        parameter_type = Core.Type.Erased Core.Erasure_reason.Proof;
                        body = ast_lift 1 c}
    else
      named_lams ids c

(** Removes dummy arguments from applications of [Core.Expr.Bound_variable r], purging arguments
    marked [Erased]. *)
let kill_dummy_args (ids, bl) r t =
  let m = List.length ids in
  let sign = List.rev bl in
  let rec found n = function
    | Core.Expr.Bound_variable {index = r'; _} when Int.equal r' (r + n) -> true
    | Core.Expr.Coerce {value = e; _}
    | Core.Expr.Boxed_value {value = e; _}
    | Core.Expr.Lambda_group_barrier {value = e; _} -> found n e
    | _ -> false
  in
  let rec killrec n = function
    | Core.Expr.Apply {callee = e; arguments = a} when found n e ->
      let k = max 0 (m - List.length a) in
      let a = List.map (killrec n) a in
      let a = List.map (ast_lift k) a in
      let a = select_via_bl sign (a @ eta_args k) in
      named_lams (List.firstn k ids) (Core.Expr.Apply {callee = ast_lift k e; arguments = a})
    | e when found n e ->
      let a = select_via_bl sign (eta_args m) in
      named_lams ids (Core.Expr.Apply {callee = ast_lift m e; arguments = a})
    | e -> ast_map_lift killrec n e
  in
  killrec 0 t

(** Extracts a signature from an argument list ([Erased] for a
    [Core.Expr.Erased_value], [Runtime] otherwise). *)
let sign_of_args a =
  List.map
    (function
      | Core.Expr.Erased_value k -> Core.Signature.Argument.Erased k
      | _ -> Core.Signature.Argument.Runtime )
    a

(** Removes all dummy (erased) bindings and arguments from a Core term. *)
let rec kill_dummy = function
  | Core.Expr.Fixpoint g ->
    kill_dummy_fix_term g.selected (Core.Recursion.Group.bodies g) (fun c ->
        Core.Expr.Fixpoint (Core.Recursion.Group.with_bodies g c) )
  | Core.Expr.Cofixpoint g ->
    kill_dummy_fix_term g.selected (Core.Recursion.Group.bodies g) (fun c ->
        Core.Expr.Cofixpoint (Core.Recursion.Group.with_bodies g c) )
  | Core.Expr.Apply {callee = Core.Expr.Fixpoint g; arguments = a} ->
    kill_dummy_fix_app g.selected (Core.Recursion.Group.bodies g)
      (fun c -> Core.Expr.Fixpoint (Core.Recursion.Group.with_bodies g c))
      a
  | Core.Expr.Apply {callee = Core.Expr.Cofixpoint g; arguments = a} ->
    kill_dummy_fix_app g.selected (Core.Recursion.Group.bodies g)
      (fun c -> Core.Expr.Cofixpoint (Core.Recursion.Group.with_bodies g c))
      a
  | Core.Expr.Let {binder = id;
                   binder_type = t;
                   value = Core.Expr.Fixpoint g;
                   body = e;
                   occurrence = let_occ} ->
    kill_dummy_fix_let g.selected (Core.Recursion.Group.bodies g)
      (fun c -> Core.Expr.Fixpoint (Core.Recursion.Group.with_bodies g c))
      (fun b e -> Core.Expr.Let {binder = id; binder_type = t; value = b; body = e; occurrence = let_occ})
      e
  | Core.Expr.Let {binder = id;
                   binder_type = t;
                   value = Core.Expr.Cofixpoint g;
                   body = e;
                   occurrence = let_occ} ->
    kill_dummy_fix_let g.selected (Core.Recursion.Group.bodies g)
      (fun c -> Core.Expr.Cofixpoint (Core.Recursion.Group.with_bodies g c))
      (fun b e -> Core.Expr.Let {binder = id; binder_type = t; value = b; body = e; occurrence = let_occ})
      e
  | Core.Expr.Let {binder = id; binder_type = t; value = c; body = e; occurrence = occ} ->
    ( try
        let k, c = kill_dummy_lams [] (kill_dummy_hd c) in
        let e = kill_dummy (kill_dummy_args k 1 e) in
        let c = kill_dummy c in
        if is_atomic c then ast_subst c e else Core.Expr.Let {binder = id;
                                                              binder_type = t;
                                                              value = c;
                                                              body = e;
                                                              occurrence = occ}
      with Impossible -> Core.Expr.Let {binder = id;
                                        binder_type = t;
                                        value = kill_dummy c;
                                        body = kill_dummy e;
                                        occurrence = occ} )
  | a -> ast_map kill_dummy a

(** Like [kill_dummy] but only acts on head lambdas and let-ins. *)
(* A fixpoint group selected at [i] with bodies [c], rebuilt by [fix] from
   new bodies: the three shapes [kill_dummy] prunes a fixpoint in. *)
and kill_dummy_fix_term i c fix =
  try
    let k, c = kill_dummy_fix i c [] in
    let fix = fix c in
    Option.cata (fun k -> ast_subst fix (kill_dummy_args k 1 (Core.Expr.fresh_rel 1))) fix k
  with Impossible -> fix (Array.map kill_dummy c)

and kill_dummy_fix_app i c fix a =
  let a = List.map kill_dummy a in
  (* Heuristics: if some arguments are implicit args, we try to eliminate the
     corresponding arguments of the fixpoint *)
  try
    let k, c = kill_dummy_fix i c (sign_of_args a) in
    let fake = Core.Expr.Apply {callee = Core.Expr.fresh_rel 1; arguments = List.map (ast_lift 1) a} in
    let fake' = Option.cata (fun k -> kill_dummy_args k 1 fake) fake k in
    ast_subst (fix c) fake'
  with Impossible -> Core.Expr.Apply {callee = fix (Array.map kill_dummy c); arguments = a}

and kill_dummy_fix_let i c fix letin e =
  try
    let k, c = kill_dummy_fix i c [] in
    let e = kill_dummy (Option.cata (fun k -> kill_dummy_args k 1 e) e k) in
    letin (fix c) e
  with Impossible -> letin (fix (Array.map kill_dummy c)) (kill_dummy e)

and kill_dummy_hd = function
  | Core.Expr.Lambda {parameter = id; parameter_type = ty; body = e} ->
    Core.Expr.Lambda {parameter = id; parameter_type = ty; body = kill_dummy_hd e}
  | Core.Expr.Let {binder = id; binder_type = t; value = c; body = e; occurrence = occ} ->
    ( try
        let k, c = kill_dummy_lams [] (kill_dummy_hd c) in
        let e = kill_dummy_hd (kill_dummy_args k 1 e) in
        let c = kill_dummy c in
        if is_atomic c then ast_subst c e else Core.Expr.Let {binder = id;
                                                              binder_type = t;
                                                              value = c;
                                                              body = e;
                                                              occurrence = occ}
      with Impossible -> Core.Expr.Let {binder = id;
                                        binder_type = t;
                                        value = kill_dummy c;
                                        body = kill_dummy_hd e;
                                        occurrence = occ} )
  | a -> a

(** Removes dummy lambdas from fixpoint body [i], under the signature [s] of
    the arguments it is applied to, and from every other body of the group,
    and propagates each change to all mutual bodies.  The signature [i] was
    killed under, if any, is for the caller to adjust the references to the
    fixpoint outside it; [Impossible] if no body had anything to kill.  A
    partner is reached
    only from within the group, so its calls are the only ones to adjust:
    left with its erased binders, it would take a parameter for each of
    them that the calls to it, their dummy arguments dropped, do not
    pass. *)
and kill_dummy_fix i c s =
  let n = Array.length c in
  let c = Array.copy c in
  let kill j sign =
    let k, cj = kill_dummy_lams sign (kill_dummy_hd c.(j)) in
    c.(j) <- cj;
    for j' = 0 to n - 1 do
      c.(j') <- kill_dummy_args k (n - j) c.(j')
    done;
    k
  in
  let k = try Some (kill i s) with Impossible -> None in
  let killed = ref (Option.has_some k) in
  for j = 0 to n - 1 do
    if j <> i then
      try
        ignore (kill j []);
        killed := true
      with Impossible -> ()
  done;
  if not !killed then raise Impossible;
  (k, Array.map kill_dummy c)

(** Main normalization pass: applies simplification and dummy elimination
    repeatedly until fixed point. *)
let normalize a =
  let o = optims () in
  let rec norm a =
    let a' = if o.opt_kill_dum then kill_dummy (simpl o a) else simpl o a in
    if eq_core_ast a a' then a else norm a'
  in
  norm a

(** [apply_eta_args f args] is [f] applied to [args], with the application
    placed where [f] produces its value rather than wrapped around [f].

    Eta-expansion invents its parameters after simplification has run, so the
    application it builds is a redex nothing has looked at.  Around a
    conditional that redex is not merely unsimplified but untranslatable: the
    branches of [if even n then f_even n else f_odd n] are two closures with
    two closure types, and C++ has no common type to give the conditional --
    even though each branch, applied, is an ordinary call.  {!simpl_app}
    already knows where an application belongs; this is the entry point for
    the callers that build one late.

    Placed in each branch of a match, a read among [args] is copied, and it
    is copied after {!Core_passes.Fresh_occurrences} made every read one of its own: each
    copy is given an occurrence of its own here. *)
let apply_eta_args f args =
  match args with
  | [] -> f
  | _ ->
    let reads = List.filter_map (function Core.Expr.Bound_variable {occurrence = o; _} -> Some o | _ -> None) args in
    let rec own = function
      | Core.Expr.Bound_variable {index = i; occurrence = o} when List.exists (Core.Occurrence.equal o) reads ->
        Core.Expr.fresh_rel i
      | e -> ast_map own e
    in
    own (canonical (simpl_app (optims ()) args f))

(** {1 Special treatment of fixpoints: argument reordering} *)

(** Optimizes a fixpoint by reordering arguments so that [n] leading arguments
    are directly accessible, reducing eta-expansion overhead. *)
let general_optimize_fix f ids n args m c occ =
  let v = Array.init n (fun i -> i) in
  let aux i = function
    | Core.Expr.Bound_variable {index = j; _} when v.(j - 1) >= 0 ->
      if ast_occurs (j + 1) c then raise Impossible else v.(j - 1) <- -i - 1
    | _ -> raise Impossible
  in
  List.iteri aux args;
  let args_f = List.rev_map (fun i -> Core.Expr.fresh_rel (i + m + 1)) (Array.to_list v) in
  (* The [m] binders introduced here stand for [args], one each, so a binder's
     type is the type of the outer binder its argument names -- [aux] above has
     already established that every argument is such an [Core.Expr.Bound_variable].  Binder [d]
     counting from the innermost is argument [m - d], because [args_f] maps
     argument [i] to [Core.Expr.Bound_variable (m - i)].

     They cannot be written [Core.Type.Axiom] on the premise that [normalize]
     beta-reduces them away before any C++ path sees them.  The premise holds
     only where the recursive occurrence is {e applied}: a point-free
     self-reference is no redex, the lambdas survive, and [Core.Type.Axiom] prints as
     the undeclared C++ type [axiom]. *)
  let arg_ty = function
    | Core.Expr.Bound_variable {index = j; _} -> (
      match List.nth_opt ids (j - 1) with Some (_, ty) -> ty | None -> Core.Type.Unknown
      )
    | _ -> Core.Type.Unknown
  in
  let new_tys =
    List.init m (fun d ->
        match List.nth_opt args (m - 1 - d) with
        | Some arg -> arg_ty arg
        | None -> Core.Type.Unknown )
  in
  let new_f = anonym_tmp_lams (Core.Expr.Apply {callee = Core.Expr.fresh_rel (n + m + 1);
                                                arguments = args_f}) new_tys in
  let new_c = named_lams ids (normalize (Core.Expr.Apply {callee = ast_subst new_f c; arguments = args})) in
  Core.Expr.Fixpoint (Core.Recursion.Group.singleton (fst f) (snd f) new_c occ)

(** Optimizes fixpoint definitions by inlining small recursive calls and
    eta-reducing. *)
let optimize_fix a =
  if not (optims ()).opt_fix_fun then
    a
  else
    let ids, a' = collect_lams a in
    let n = List.length ids in
    if Int.equal n 0 then
      a
    else
      match
        a'
      with
      | Core.Expr.Fixpoint {members = [|f|]; occurrence = occ; _}
      | Core.Expr.Cofixpoint {members = [|f|]; occurrence = occ; _} ->
        (* The fixpoint calls itself under the definition's binders, passing
           each on -- a binder erasure kept, a type binder under
           Conservative Types, as the dummy it stands for, as extraction
           writes an erased argument of any other call. *)
        let args =
          List.rev
            (List.mapi
              (fun i (_, ty) -> match ty with Core.Type.Erased k -> Core.Expr.Erased_value k
                | _ -> Core.Expr.fresh_rel (i + 1)) ids)
        in
        let new_f = Core.Expr.Apply {callee = Core.Expr.fresh_rel (n + 1); arguments = args} in
        let new_c = named_lams ids (normalize (ast_subst new_f f.body)) in
        Core.Expr.Fixpoint (Core.Recursion.Group.singleton f.name f.type_ new_c occ)
      | Core.Expr.Apply {callee = a'; arguments = args} ->
        let m = List.length args in
        ( match a' with
        | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _
          when test_eta_args_lift 0 n args && not (ast_occurs_itvl 1 m a') -> a'
        | Core.Expr.Fixpoint {members = [|f|]; occurrence = occ; _}
        | Core.Expr.Cofixpoint {members = [|f|]; occurrence = occ; _} ->
          (try general_optimize_fix (f.name, f.type_) ids n args m f.body occ with Impossible -> a)
        | _ -> a )
      | _ -> a

(** {1 Inlining} *)

(* Utility functions used in the decision of inlining. *)

let core_size_branch size pv =
  Array.fold_left (fun a (br : _ Core.Match.Branch.at) -> a + size br.body) 0 pv

(** Computes the size (node count) of a Core term for inlining heuristics. *)
let rec core_size = function
  | Core.Expr.Apply {callee = t; arguments = l} -> List.length l + core_size t + core_size_list l
  | Core.Expr.Lambda {body = t; _} -> 1 + core_size t
  | Core.Expr.Construct {arguments = l; _} | Core.Expr.Tuple l -> core_size_list l
  | Core.Expr.Match {scrutinee = t; branches = pv; _} -> 1 + core_size t + core_size_branch core_size pv
  | Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g -> core_size_array (Core.Recursion.Group.bodies g)
  | Core.Expr.Let {body = t; _} -> core_size t
  | Core.Expr.Coerce {value = t; _}
  | Core.Expr.Boxed_value {value = t; _}
  | Core.Expr.Lambda_group_barrier {value = t; _} -> core_size t
  | Core.Expr.Persistent_array {elements = t; default = def} -> core_size_array t + core_size def
  | Core.Expr.Global _
   |Core.Expr.Bound_variable _
   |Core.Expr.Runtime_error _
   |Core.Expr.Erased_value _
   |Core.Expr.Axiom_value _
   |Core.Expr.UInt63 _ | Core.Expr.Numeral _
   |Core.Expr.Float64 _
   |Core.Expr.String _ -> 0

and core_size_list l = List.fold_left (fun a t -> a + core_size t) 0 l

and core_size_array a = Array.fold_left (fun a t -> a + core_size t) 0 a

(** Checks if a Core expression is a fixpoint definition. *)
let is_fix = function
  | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ -> true
  | _ -> false

(** {2 Strictness} *)

(* A variable is strict if the evaluation of the whole term implies the
   evaluation of this variable. Non-strict variables can be found behind Match,
   for example. Expanding a term [t] is a good idea when it begins by at least
   one non-strict lambda, since the corresponding argument to [t] might be
   unevaluated in the expanded code. *)

exception Toplevel

let lift n l = List.map (( + ) n) l

let pop n l = List.map (fun x -> if x <= n then raise Toplevel else x - n) l

(* This function returns a list of de Bruijn indices of non-strict variables, or
   raises [Toplevel] if it has an internal non-strict variable. In fact, not all
   variables are checked for strictness, only the ones which de Bruijn index is
   in the candidates list [cand]. The flag [add] controls the behaviour when
   going through a lambda: should we add the corresponding variable to the
   candidates? We use this flag to check only the external lambdas, those that
   will correspond to arguments. *)

(** Returns de Bruijn indices of non-strict variables in a term. Raises
    [Toplevel] if an internal non-strict variable is found. *)
let rec non_stricts add cand = function
  | Core.Expr.Lambda {parameter = id; body = t; _} ->
    let cand = lift 1 cand in
    let cand = if add then 1 :: cand else cand in
    pop 1 (non_stricts add cand t)
  | Core.Expr.Bound_variable {index = n; _} -> List.filter (fun m -> not (Int.equal m n)) cand
  | Core.Expr.Apply {callee = t; arguments = l} ->
    let cand = non_stricts false cand t in
    List.fold_left (non_stricts false) cand l
  | Core.Expr.Construct {arguments = l; _} -> List.fold_left (non_stricts false) cand l
  | Core.Expr.Let {value = t1; body = t2; _} ->
    let cand = non_stricts false cand t1 in
    pop 1 (non_stricts add (lift 1 cand) t2)
  | Core.Expr.Fixpoint g | Core.Expr.Cofixpoint g ->
    let n = Core.Recursion.Group.length g in
    let cand = lift n cand in
    let cand = Array.fold_left (non_stricts false) cand (Core.Recursion.Group.bodies g) in
    pop n cand
  | Core.Expr.Match {scrutinee = t; branches = v; _} ->
    (* The only interesting case: for a variable to be non-strict, *)
    (* it is sufficient that it appears non-strict in at least one branch, *)
    (* so we make an union (in fact a merge). *)
    let cand = non_stricts false cand t in
    Array.fold_left
      (fun c {Core.Match.Branch.binders = i; body = t; _} ->
        let n = List.length i in
        let cand = lift n cand in
        let cand = pop n (non_stricts add cand t) in
        List.merge Int.compare cand c )
      []
      v
    (* [merge] may duplicates some indices, but I don't mind. *)
  | Core.Expr.Coerce {value = t; _}
  | Core.Expr.Boxed_value {value = t; _}
  | Core.Expr.Lambda_group_barrier {value = t; _} ->
    non_stricts add cand t
  | _ -> cand

(* The real test: we are looking for internal non-strict variables, so we start
   with no candidates, and the only positive answer is via the [Toplevel]
   exception. *)

(** Returns [true] if the term has at least one non-strict external lambda. *)
let is_not_strict t =
  try
    let _ = non_stricts true [] t in
    false
  with Toplevel -> true

(** {2 Inlining decision} *)

open Declareops

(** Heuristic: decides if a constant should be auto-inlined based on size and
    strictness analysis. *)
let inline_test r t =
  if not (auto_inline ()) then
    false
  else
    let c =
      match r with
      | GlobRef.ConstRef c -> c
      | _ -> assert false
    in
    let has_body =
      Environ.mem_constant c (Global.env ())
      && constant_has_body (Global.lookup_constant c)
    in
    has_body
    &&
    let t1 = eta_red t in
    let t2 = snd (collect_lams t1) in
    (not (is_fix t2)) && core_size t < 12 && is_not_strict t

(** Parses a fully qualified constant name string into a [Constant.t]. *)
let con_of_string s =
  let d, id = Libnames.split_dirpath (dirpath_of_string s) in
  Constant.make2 (ModPath.MPfile d) (Label.of_id id)

(** Set of standard library constants that are always inlined during
    extraction (e.g. well-founded recursion combinators, boolean operators). *)
let manual_inline_set =
  List.fold_right
    (fun x -> Cset_env.add (con_of_string x))
    [
      "Corelib.Init.Wf.well_founded_induction_type";
      "Corelib.Init.Wf.well_founded_induction";
      "Corelib.Init.Wf.Acc_iter";
      "Corelib.Init.Wf.Fix_F";
      "Corelib.Init.Wf.Fix";
      "Corelib.Program.Wf.Fix_F_sub";
      "Corelib.Program.Wf.Fix_sub";
      "Corelib.Init.Datatypes.andb";
      "Corelib.Init.Datatypes.orb";
      "Corelib.Init.Logic.eq_rec_r";
      "Corelib.Init.Logic.eq_rect_r";
      "Corelib.Init.Specif.proj1_sig";
      "Equations.Prop.Subterm.FixWf";
    ]
    Cset_env.empty

(** Checks if a global reference is in the manual inline set. *)
let manual_inline = function
  | GlobRef.ConstRef c -> Cset_env.mem c manual_inline_set
  | _ -> false

(** Remaps type variable indices in a Core term using function [f]. Used for
    cross-module type variable renumbering. *)
let remap_tvars f =
  let rec remap_type = function
    | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i} ->
      Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = (f i)}
    | Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = i} ->
      Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = (f i)}
    | Core.Type.Variable_app {head = i; arguments = args} ->
      Core.Type.Variable_app {head = f i; arguments = List.map remap_type args}
    | Core.Type.Arrow {parameter = t1; result = t2} ->
      Core.Type.Arrow {parameter = remap_type t1; result = remap_type t2}
    | Core.Type.Global_app {head = r; type_arguments = args; index_arguments = e} ->
      Core.Type.Global_app {head = r; type_arguments = List.map remap_type args; index_arguments = List.map remap_ast e}
    | Core.Type.Meta {contents = Some t} -> remap_type t
    | t -> t
  and remap_ast = function
    | Core.Expr.Lambda {parameter = id; parameter_type = ty; body} ->
      Core.Expr.Lambda {parameter = id; parameter_type = remap_type ty; body = remap_ast body}
    | Core.Expr.Let {binder = id; binder_type = ty; value = def; body; occurrence = occ} ->
      Core.Expr.Let {binder = id;
                     binder_type = remap_type ty;
                     value = remap_ast def;
                     body = remap_ast body;
                     occurrence = occ}
    | Core.Expr.Apply {callee = f'; arguments = args} ->
      Core.Expr.Apply {callee = remap_ast f'; arguments = List.map remap_ast args}
    | Core.Expr.Global use -> Core.Expr.Global (Core.Global_use.map_types remap_type use)
    | Core.Expr.Construct {result_type = ty; constructor = r; arguments = args; occurrence = occ} ->
      Core.Expr.Construct {result_type = remap_type ty;
                           constructor = r;
                           arguments = List.map remap_ast args;
                           occurrence = occ}
    | Core.Expr.Tuple args -> Core.Expr.Tuple (List.map remap_ast args)
    | Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches; occurrence = occ} ->
      Core.Expr.Match {scrutinee_type = remap_type ty; scrutinee = remap_ast scrut; branches = Array.map
            (fun {Core.Match.Branch.binders = ids; result_type = ty; pattern = pat; body = body} ->
              { Core.Match.Branch.binders = List.map (fun (id, t) -> (id, remap_type t)) ids;
                result_type = remap_type ty;
                pattern = pat;
                body = remap_ast body } )
            branches; occurrence = occ}
    | Core.Expr.Fixpoint g -> Core.Expr.Fixpoint (Core.Recursion.Group.map remap_type remap_ast g)
    | Core.Expr.Cofixpoint g -> Core.Expr.Cofixpoint (Core.Recursion.Group.map remap_type remap_ast g)
    | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
      Core.Expr.Coerce {source_type = from; target_type = into; value = remap_ast a; occurrence = mocc}
    | Core.Expr.Boxed_value {value = a; occurrence = mocc} ->
      Core.Expr.Boxed_value {value = remap_ast a; occurrence = mocc}
    | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
      Core.Expr.Lambda_group_barrier {value = remap_ast a; occurrence = mocc}
    | Core.Expr.Persistent_array {elements = arr; default = def} ->
      Core.Expr.Persistent_array {elements = Array.map remap_ast arr; default = remap_ast def}
    | a -> a (* Core.Expr.Bound_variable, Core.Expr.Runtime_error, Core.Expr.Erased_value, Core.Expr.Axiom_value,
                Core.Expr.UInt63, Core.Expr.Float64, Core.Expr.String, Core.Expr.Numeral *)
  in
  remap_ast

(** Final inlining decision combining auto-inlining heuristics and manual
    settings. *)
let inline r t =
  (not (to_keep r)) (* The user DOES want to keep it *)
  && (not (is_inline_custom r))
  && ( to_inline r (* The user DOES want to inline it *)
     || is_projection r
     || is_recursor r
     || manual_inline r
     || inline_test r t )
