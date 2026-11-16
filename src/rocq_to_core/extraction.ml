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
open Term
open Constr
open Context
open Declarations
open Declareops
open Environ
open Reductionops
open Retyping
open Inductiveops
open Namegen
open Base.Table
open Base.Core_util
open Base.Common
open Context.Rel.Declaration
(*i*)

(** Raised during inductive extraction to signal the kind of an inductive type
    ([Inductive], [Coinductive], [Record] or [Type_class]). Caught by
    {!extract_really_ind}'s third pass to classify the result. *)
exception I of Core.Inductive.Kind.t

(* The constants of the fixpoint group {!extract_fixpoint} is extracting, so
   a call inside the group is told apart from a call to an outside constant
   ({!extract_cst_app}); [[]] outside a group. *)
let current_fixpoints = Base.State.cell Base.State.Extraction ([] : Constant.t list)

(** The local fixpoint a [let] binds while it is extracted, with the
    applications of its name in the [let]'s body: the group's entries
    ({!erased_fix_types}). *)
let let_fix_entries = ref (None : (EConstr.t * EConstr.t array list) option)

(* For the C++ backend: deferred meta fills for erased constructor type params.
   When a constructor like nil/none has a type parameter whose meta is unresolved
   after needs_magic (because the expected type is a dependent/erased type), we
   record the meta and its erased Rocq type here.  After the whole constant is
   extracted ({!extract_std_constant}), any meta that is STILL None gets filled
   with the recorded erased type.  So [nil] in the deque_action_mismatch test
   (meta stays None) is filled with [pair<any,any>], while sigma_types (the
   [cons] meta is resolved to [nat]) is left alone. *)
let pending_cpp_meta_fills : (Core.Extracted.Meta.t * Core.Type.extracted) list ref = ref []

(* NB: [type_of] and [sort_of] might raise
   [SingletonInductiveBecomesProp]. This exception is caught in late
   wrappers around the exported functions of this file, in order to display the
   location of the issue. *)

(** The type of [c], outer casts stripped. *)
let type_of env sg c =
  Retyping.get_type_of ~polyprop:false env sg (Termops.strip_outer_cast sg c)

(** The sort quality of [c]'s type, outer casts stripped. *)
let sort_of env sg c =
  Retyping.get_sort_quality_of
    ~polyprop:false
    env
    sg
    (Termops.strip_outer_cast sg c)

(** {1 Generation of flags and signatures} *)

(** Whether a term is logical or informative:
    {ul
    {- [Logic] denotes a term of sort [Prop], or a type scheme on sort
       [Prop];}
    {- [Info] is the opposite.  [(X:Type)X] shows that an [Info] term might
       in fact be [Logic] after instantiation.}} *)
type info =
  | Logic
  | Info

(** Whether a term is a type scheme:
    {ul
    {- [TypeScheme] denotes something that becomes a type after enough
       applications: a term of type [(x_1:X_1)...(x_n:X_n)s] with [s] one of
       [Set], [Prop] or [Type];}
    {- [Default] denotes the other cases.  It may be inexact after
       instantiation: [(X:Type)X] is [Default] and may give [Set] after
       instantiation, which is rather [TypeScheme].}} *)
type scheme =
  | TypeScheme
  | Default

(** The information {!flag_of_type} gives about any Rocq term. *)
type flag = info * scheme

(** {2 [flag_of_type] transforms a type [t] into a [flag]. Really important
    function} *)

let info_of_quality = function
  | UnivGen.QualityOrSet.Qual (QConstant (QSProp | QProp)) -> Logic
  | Set | Qual (QConstant QType | QVar _) -> Info

let info_of_sort s = info_of_quality (UnivGen.QualityOrSet.of_sort s)

(** The {!flag} of a term of type [t]: [t] is reduced and its products are
    stripped; a sort at the end makes the term a [TypeScheme]. *)
let rec flag_of_type env sg t : flag =
  let t = whd_all env sg t in
  match EConstr.kind sg t with
  | Prod (x, t, c) ->
    flag_of_type (EConstr.push_rel (LocalAssum (x, t)) env) sg c
  | Sort s -> (info_of_sort (EConstr.ESorts.kind sg s), TypeScheme)
  | _ -> (info_of_quality (sort_of env sg t), Default)

(** {2 Two particular cases of [flag_of_type]} *)

(** Whether a term of type [t] is an informative value: [(Info, Default)]. *)
let is_default env sg t =
  match flag_of_type env sg t with
  | Info, Default -> true
  | _ -> false

(** Raised by {!check_default} with the reason the term is erased. *)
exception NotDefault of Core.Erasure_reason.t

(** Raises {!NotDefault} unless a term of type [t] is an informative value:
    [Core.Erasure_reason.Type_argument] for a type scheme, [Core.Erasure_reason.Proof] for a logical term. *)
let check_default env sg t =
  match flag_of_type env sg t with
  | _, TypeScheme -> raise (NotDefault Core.Erasure_reason.Type_argument)
  | Logic, _ -> raise (NotDefault Core.Erasure_reason.Proof)
  | _ -> ()

(** Whether [t] is the type of an informative type scheme: a binder at such a
    type becomes a Core type variable. *)
let is_info_scheme env sg t =
  match flag_of_type env sg t with
  | Info, TypeScheme -> true
  | _ -> false

(** Whether an argument of an applied instance survives extraction.

    [ParamsV {IP : IPtr} {IPT : IPtrTheory IP}] with [IPtrTheory] a [Prop]
    class is emitted as [template <IPtr _tcI0> struct ParamsV]: the proof
    argument takes no template parameter.  A class-argument record
    ({!Base.Table.class_arg}) is read from the Rocq type, upstream of that erasure,
    and spelled downstream of it, so it must be projected through the erasure
    where it is taken -- the reader has no Rocq type left to ask. *)
let arg_survives_extraction env sg a =
  (* The sort of the argument's TYPE: [natIPtrTheory : IPtrTheory natIPtr] is
     a proof and erases, [natIPtr : IPtr] is data and does not.  A retyping
     failure keeps the argument -- dropping one silently would be spelled as a
     shorter list, which reads as a correct one. *)
  if not (EConstr.Vars.closed0 sg a) then
    (* An argument that names a binder -- a context variable -- is the
       [Carg_unknown] the reader fills positionally; it cannot be typed in this
       environment and its position must be kept regardless. *)
    true
  else
    try info_of_quality (sort_of env sg (type_of env sg a)) != Logic
    with Retyping.RetypeError _ -> true

(** The class-argument shape an applied term writes ({!Base.Table.class_arg}), if
    its head is a constant.  Recursive: [@ParamsV natIPtr] and [@ParamsV IP]
    differ only in the argument, and the reader has to spell one of them.  An
    argument whose head is not a constant is [Carg_unknown] -- the position is
    kept, so the reader can fill it from the instances it holds -- and one
    that erases ({!arg_survives_extraction}) takes no position at all. *)
let rec class_arg_shape env sg a =
  let h, a_args = EConstr.decompose_app sg a in
  match EConstr.kind sg h with
  | Const (c, _) ->
    Some
      (Base.Table.Carg
         ( GlobRef.ConstRef c,
           List.filter_map
             (fun x ->
               if arg_survives_extraction env sg x then
                 Some
                   (Option.default Base.Table.Carg_unknown (class_arg_shape env sg x))
               else None )
             (Array.to_list a_args) ))
  | _ -> None

(** Pushes a named assumption into the Rocq environment. *)
let push_rel_assum (n, t) env = EConstr.push_rel (LocalAssum (n, t)) env

(** Pushes multiple named assumptions into the Rocq environment. *)
let push_rels_assum assums =
  EConstr.push_rel_context (List.map (fun (x, t) -> LocalAssum (x, t)) assums)

(** Retrieves the body of a constant as an [EConstr.t]. *)
let get_body lconstr = EConstr.of_constr lconstr

(** Checks if a constant is opaque and retrieves its body if accessible. *)
let get_opaque access env c =
  EConstr.of_constr (fst (Global.force_proof access c))

(** Applies a Rocq term to a list of arguments. *)
let applistc c args = EConstr.mkApp (c, Array.of_list args)

(** Pushes recursive type bindings into the environment. Same as
    [Environ.push_rec_types], but for [EConstr.t]. *)
let push_rec_types (lna, typarray, _) env =
  let ctxt =
    Array.map2_i
      (fun i na t -> LocalAssum (na, EConstr.Vars.lift i t))
      lna
      typarray
  in
  Array.fold_left (fun e assum -> EConstr.push_rel assum e) env ctxt

(** Counts the number of leading lambdas in a term. Same as [Termops.nb_lam],
    but for [EConstr.t]. *)
let nb_lam sg c = List.length (fst (EConstr.decompose_lambda sg c))

(** Decomposes the first [n] lambdas from a term. Same as
    [Term.decompose_lambda_n] but for [EConstr.t]. *)
let decompose_lambda_n sg n =
  let rec lamdec_rec l n c =
    if n <= 0 then
      (l, c)
    else
      match
        EConstr.kind sg c
      with
      | Lambda (x, t, c) -> lamdec_rec ((x, t) :: l) (n - 1) c
      | Cast (c, _, _) -> lamdec_rec l n c
      | _ -> raise Not_found
  in
  lamdec_rec [] n

(** {2 [type_sign] generates a signature aimed at treating a type application}
*)

(** One entry per product of [c]: [Core.Signature.Argument.Runtime] for a binder at an informative type
    scheme, [Core.Signature.Argument.Erased Core.Erasure_reason.Proof] for any other binder. *)
let rec type_sign env sg c =
  match EConstr.kind sg (whd_all env sg c) with
  | Prod (n, t, d) ->
    (if is_info_scheme env sg t then Core.Signature.Argument.Runtime else
      Core.Signature.Argument.Erased Core.Erasure_reason.Proof)
    :: type_sign (push_rel_assum (n, t) env) sg d
  | _ -> []

(** Counts the number of informative type-scheme arguments in a product type. *)
let rec type_scheme_nb_args env sg c =
  match EConstr.kind sg (whd_all env sg c) with
  | Prod (n, t, d) ->
    let n = type_scheme_nb_args (push_rel_assum (n, t) env) sg d in
    if is_info_scheme env sg t then n + 1 else n
  | _ -> 0

(** Positions, 0-based among the [Core.Signature.Argument.Runtime] entries of [type_sign], of the
    parameters that are type CONSTRUCTORS ([F : Type -> Type]) rather than
    plain types ([A : Type]), each paired with that constructor's arity.
    {!Base.Table.add_ind_hkt_params} records these for
    inductives so that a type class parameterised by a type constructor can be
    generated as an associated type instead of a C++ template parameter. *)
let hkt_keep_positions env sg c =
  let rec go env c j =
    match EConstr.kind sg (whd_all env sg c) with
    | Prod (n, t, d) ->
      let env' = push_rel_assum (n, t) env in
      if is_info_scheme env sg t then
        let rest = go env' d (j + 1) in
        let arity = type_scheme_nb_args env sg t in
        if arity > 0 then (j, arity) :: rest else rest
      else
        go env' d j
    | _ -> []
  in
  go env c 0

(** {2 [type_sign_vl] does the same, plus a type var list} *)

(* When generating type variables, we avoid any ' in their names (otherwise this
   may cause a lexer conflict in ocaml with 'a'). We also get rid of unicode
   characters. Anyway, since type variables are local, the created name is just
   a matter of taste... See also Bug #3227 *)

(** Generates a unique type variable name from a binder name, avoiding lexer
    conflicts and unicode.
    @param n Binder name from the Rocq term (may be anonymous or contain unicode)
    @param vl List of already-used type variable names; the result is guaranteed fresh *)
let make_typvar n vl =
  let id = id_of_name n in
  let id' =
    let s = Id.to_string id in
    if (not (String.contains s '\'')) && Unicode.is_basic_ascii s then
      id
    else
      id_of_name Anonymous
  in
  let vl = Id.Set.of_list vl in
  next_ident_away id' vl

(** {!type_sign}, plus the names of the type variables its [Core.Signature.Argument.Runtime] entries
    introduce, outermost first. *)
let rec type_sign_vl env sg c =
  match EConstr.kind sg (whd_all env sg c) with
  | Prod (n, t, d) ->
    let s, vl = type_sign_vl (push_rel_assum (n, t) env) sg d in
    if not (is_info_scheme env sg t) then
      (Core.Signature.Argument.Erased Core.Erasure_reason.Proof :: s, vl)
    else
      (Core.Signature.Argument.Runtime :: s, make_typvar n.binder_name vl :: vl)
  | _ -> ([], [])

(** Counts the number of default (non-erased) parameters in a type signature. *)
let rec nb_default_params env sg c =
  match EConstr.kind sg (whd_all env sg c) with
  | Prod (n, t, d) ->
    let n = nb_default_params (push_rel_assum (n, t) env) sg d in
    if is_default env sg t then n + 1 else n
  | _ -> 0

(** Enriches a type signature by marking implicit arguments as
    [Core.Signature.Argument.Erased Core.Erasure_reason.Configured_implicit],
    skipping the first [nb_params] parameters.
    @param r Global reference whose declared implicits are looked up
    @param s Type signature to enrich (list of
    [Core.Signature.Argument.Runtime]/[Core.Signature.Argument.Erased] entries)
    @param nb_params Number of leading parameters to skip before applying implicits *)
let sign_with_implicits r s nb_params =
  let implicits = implicits_of_global r in
  let rec add_impl i = function
    | [] -> []
    | Core.Signature.Argument.Runtime :: s when Int.Set.mem i implicits ->
      Core.Signature.Argument.Erased (Core.Erasure_reason.Configured_implicit {entity = r;
                                                                               position = i}) :: add_impl (i + 1) s
    | sign :: s -> sign :: add_impl (i + 1) s
  in
  add_impl (1 + nb_params) s

(** [c] with every product of its spine exposed: each codomain reduced to
    weak head normal form, constants unfolded. *)
let rec unfold_spine env sg c =
  let c = Reductionops.whd_all env sg c in
  match EConstr.kind sg c with
  | Prod (n, t, d) ->
    EConstr.mkProd (n, t, unfold_spine (push_rel_assum (n, t) env) sg d)
  | _ -> c

(** The schema's binder roles as a call to [r] reads them under this run's
    configuration: a binder declared implicit is erased as
    {!sign_with_implicits} erases it, and under conservative types no binder
    is.  Which variable comes from which binder does not change. *)
let schema_view r schema =
  let implicits = implicits_of_global r in
  Core.Schema.with_roles
    (fun {Core.Schema.binder; role; _} ->
      let i = Core.Scheme.Binder.position binder + 1 in
      match role with
      | Core.Schema.Erased _ when conservative_types () -> Core.Schema.Value
      | Core.Schema.Value when Int.Set.mem i implicits ->
        Core.Schema.Erased (Core.Erasure_reason.Configured_implicit {entity = r; position = i})
      | role -> role )
    schema

(** {1 Management of type variable contexts} *)

(* A De Bruijn variable context (db) is a context for translating Rocq [Rel]
   into Core type [Core.Type.Variable]. *)

(** {2 From a type signature toward a type variable context (db)} *)

(** Builds a de Bruijn variable context from a type signature. *)
let db_from_sign s =
  let rec make i acc = function
    | [] -> acc
    | Core.Signature.Argument.Runtime :: l -> make (i + 1) (i :: acc) l
    | Core.Signature.Argument.Erased _ :: l -> make i (0 :: acc) l
  in
  make 1 [] s

(** Whether a Rocq type ultimately returns a [Type]/[Set] sort, stripping
    products on the way: [Type] and [Type -> Type] do, [Type -> Prop] and
    [nat] do not.  A binder at such a type is a type parameter -- the
    higher-kinded case included -- and everything else is a value or a proof. *)
let rec returns_type_sort c =
  match Constr.kind c with
  | Sort s -> info_of_sort s == Info
  | Prod (_, _, body) -> returns_type_sort body
  | _ -> false

(** A db context read off the local context, for the places that have no
    signature to read it off instead.

    A [Core.Type.Variable] is numbered among the {e type} binders in scope, outermost first,
    exactly as {!db_from_sign} numbers them from a signature: a value binder
    takes no number and contributes [0].  Numbering every binder alike would
    name a variable no template head has -- [B] under [m], [M], [A], [f], [l],
    [b] would come out as [Core.Type.Variable 10] where the declaration calls it [T3].

    A fixpoint's body re-binds the very parameters the declaration quantifies:
    the context under [fix monad_fold_right A B f l b] holds a second [A] and
    [B] shadowing the first.  Core has no type lambdas, so both spellings
    are the one type variable, and a named binder therefore takes the number
    its name already has. *)
let db_from_rel_context env =
  let outer_first = List.rev (Environ.rel_context env) in
  let seen = ref [] in
  snd
    (List.fold_left
       (fun (rank, acc) decl ->
         if not (returns_type_sort (Context.Rel.Declaration.get_type decl)) then
           (rank, 0 :: acc)
         else
           match Context.Rel.Declaration.get_name decl with
           | Names.Name.Name id when List.mem_assoc id !seen ->
             (rank, List.assoc id !seen :: acc)
           | name ->
             ( match name with
             | Names.Name.Name id -> seen := (id, rank) :: !seen
             | Names.Name.Anonymous -> () );
             (rank + 1, rank :: acc) )
       (1, []) outer_first )

(** {2 Create a type variable context from indications taken from an inductive
    type (see just below)} *)

(** The exceptions a best-effort step gives up on: any error extraction can
    raise, its own assertions included -- a term extracted outside the context
    it was written in can trip one ([Type_env.get]'s) -- but not running out of
    memory or stack, an interrupt, or a timeout. *)
let best_effort_failure = function
  | Out_of_memory | Stack_overflow | Sys.Break | Control.Timeout -> false
  | _ -> true

(** Builds a de Bruijn context for an inductive type from a position mapping.
    @param dbmap Map from constructor argument positions to Core type variable indices
    @param i Countdown index: counts down from [ndecls] to [1], building the list in reverse *)
let rec db_from_ind dbmap i =
  if Int.equal i 0 then
    []
  else
    (try Int.Map.find i dbmap with Not_found -> 0) :: db_from_ind dbmap (i - 1)

(** {2 [parse_ind_args] builds a map: [i->j] iff the i-th Rocq argument of a
    constructor corresponds to the j-th type var of the Core inductive} *)

(* [si] is the signature of the inductive, [i] counts the Rocq args of
   [(I args)], [j] counts the Core type vars, and [relmax] is the total number
   of args of the constructor. *)

(** Maps the de Bruijn level of each constructor binder that a kept argument
    of the constructor's result type [(I args)] names directly (a bare [Rel])
    to the Core type var that argument instantiates.
    @param si Signature of the inductive type ([Core.Signature.Argument.Runtime]/[Core.Signature.Argument.Erased] list)
    @param args Array of concrete arguments from a constructor head [(I args)]
    @param relmax Total number of arguments of the constructor (used to convert de Bruijn levels) *)
let parse_ind_args si args relmax =
  let rec parse i j = function
    | [] -> Int.Map.empty
    | Core.Signature.Argument.Erased _ :: s -> parse (i + 1) j s
    | Core.Signature.Argument.Runtime :: s ->
    match Constr.kind args.(i - 1) with
    | Rel k -> Int.Map.add (relmax + 1 - k) j (parse (i + 1) (j + 1) s)
    | _ -> parse (i + 1) (j + 1) s
  in
  parse 1 1 si

(** Validates sort polymorphism compatibility, rejecting extractions that use
    Prop/SProp instantiation.
    @param sigma Evar map used to resolve the universe instance [u]
    @param gr Global reference being checked (used in the error message)
    @param u Universe instance to validate *)
let check_sort_poly sigma gr u =
  let u = EConstr.EInstance.kind sigma u in
  let qs, _ = UVars.Instance.to_array u in
  if
    Array.exists
      (function
        | Sorts.Quality.QConstant (QSProp | QProp) -> true
        | QConstant QType | QVar _ -> false )
      qs
  then
    CErrors.user_err
      Pp.(
        str "Cannot extract nontrivial sort polymorphism"
        ++ spc ()
        ++ str "(instantiation of "
        ++ Nametab.pr_global_env Id.Set.empty gr
        ++ spc ()
        ++ str "using Prop or SProp)." )

(** Determines the relevance of a primitive projection from its representation.
*)
let relevance_of_projection_repr mib p =
  let _mind, i = Names.Projection.Repr.inductive p in
  match mib.mind_record with
  | NotRecord | FakeRecord ->
    CErrors.anomaly ~label:"relevance_of_projection" Pp.(str "not a projection")
  | PrimRecord infos ->
    let _, _, rs, _ = infos.(i) in
    rs.(Names.Projection.Repr.arg p)

(** Converts a primitive projection into a fake match expression for extraction.
    Because of automatic unboxing, the easy way [mk_def c] on the constant body
    of primitive projections doesn't work. We pretend that they are implemented
    by matches until someone figures out how to clean it up (test with #4710
    when working on this). *)
let fake_match_projection env p =
  let ind = Projection.Repr.inductive p in
  let proj_arg = Projection.Repr.arg p in
  let mib, mip = Inductive.lookup_mind_specif env ind in
  let u =
    UVars.make_abstract_instance (Declareops.inductive_polymorphic_context mib)
  in
  let indu = mkIndU (ind, u) in
  let ctx, paramslet =
    let subst =
      List.init mib.mind_ntypes (fun i ->
        mkIndU ((fst ind, mib.mind_ntypes - i - 1), u) )
    in
    let ctx, cty = mip.mind_nf_lc.(0) in
    let cty = Term.it_mkProd_or_LetIn cty ctx in
    let rctx, _ = decompose_prod_decls (Vars.substl subst cty) in
    List.chop mip.mind_consnrealdecls.(0) rctx
  in
  let ci_pp_info = {style = LetStyle} in
  let ci =
    {
      ci_ind = ind;
      ci_npar = mib.mind_nparams;
      ci_cstr_ndecls = mip.mind_consnrealdecls;
      ci_cstr_nargs = mip.mind_consnrealargs;
      ci_pp_info;
    }
  in
  let relevance = relevance_of_projection_repr mib p in
  let x =
    match mib.mind_record with
    | NotRecord | FakeRecord -> assert false
    | PrimRecord info ->
      let x, _, _, _ = info.(snd ind) in
      make_annot (Name x) mip.mind_relevance
  in
  let indty = mkApp (indu, Context.Rel.instance mkRel 0 paramslet) in
  let rec fold arg j subst = function
    | [] -> assert false
    | LocalAssum (na, ty) :: rem ->
      let ty = Vars.substl subst (liftn 1 j ty) in
      if arg != proj_arg then
        let lab =
          match na.binder_name with
          | Name id -> Label.of_id id
          | Anonymous -> assert false
        in
        let kn =
          Projection.Repr.make
            ind
            ~proj_npars:mib.mind_nparams
            ~proj_arg:arg
            lab
        in
        fold
          (arg + 1)
          (j + 1)
          ( mkProj (Projection.make kn false, na.binder_relevance, mkRel 1)
          :: subst )
          rem
      else
        let p = ([|x|], liftn 1 2 ty) in
        let branch =
          let nas =
            Array.of_list (List.rev_map Context.Rel.Declaration.get_annot ctx)
          in
          (nas, mkRel (List.length ctx - (j - 1)))
        in
        let params = Context.Rel.instance mkRel 1 paramslet in
        let body =
          mkCase (ci, u, params, (p, relevance), NoInvert, mkRel 1, [|branch|])
        in
        it_mkLambda_or_LetIn (mkLambda (x, indty, body)) mib.mind_params_ctxt
    | LocalDef (_, c, t) :: rem ->
      let c = liftn 1 j c in
      let c1 = Vars.substl subst c in
      fold arg (j + 1) (c1 :: subst) rem
  in
  fold 0 1 [] (List.rev ctx)

(** {1 Extraction of a type} *)

(** Whether [a], an argument of an applied type variable, is itself a type
    rather than a value index (the [n] of [vec A n]).  Only a type argument can
    be kept in a {!Core.Type.Variable_app}; extracting a value as a type asks {!sort_of}
    for the sort of something that has none. *)
let arg_is_type env sg a =
  try EConstr.isSort sg (whd_all env sg (type_of env sg a))
  with Retyping.RetypeError _ -> false

(* [extract_type env db c args] is used to produce a Core type from the Rocq term
   [(c args)], which is supposed to be a Rocq type. *)

(* [db] is a context for translating Rocq [Rel] into Core type [Core.Type.Variable]. *)

(* [j] stands for the next Core type var. [j=0] means we do not generate Core type
   var anymore (in subterms for example). *)

(** Whether a failure of {!extract_type} means "this term is not a type",
    as opposed to something that must not be caught.

    {!extract_type} is total only on terms that really are types: it asserts
    when it meets a bare lambda, since a lambda cannot be one.  The
    speculative re-extractions that fill an unresolved [Core.Type.Meta] hand it a term
    that may turn out not to be a type at all, so there the assertion is an
    answer -- the answer being the fallback those sites already have.  An
    interrupt, a stack overflow, or an anomaly is not an answer and still
    propagates. *)
let type_extraction_declined = function
  | Assert_failure _ -> true
  | e -> CErrors.noncritical e

(** The inductives whose extraction {!extract_type} or {!extract_really_ind}
    has started out of turn and not finished.  Extracting a class to answer a
    question about one of its projections can reach that projection again;
    the memo table that would stop the recursion is only written once the
    extraction completes, so the guard has to be here. *)
let extracting_inds = ref Names.Mindset.empty

(** Whether [mind] is in {!extracting_inds}. *)
let already_extracting mind = Names.Mindset.mem mind !extracting_inds

(** Runs [f] with [mind] in {!extracting_inds}. *)
let with_extracting mind f =
  extracting_inds := Names.Mindset.add mind !extracting_inds;
  Fun.protect ~finally:(fun () ->
      extracting_inds := Names.Mindset.remove mind !extracting_inds )
    f

(** Extracts a Rocq type into a Core type. The [db] context translates [Rel]
    to [Core.Type.Variable], and [j] is the next type var.
    @param env Rocq environment for reduction and sort checking
    @param sg Evar map for universe operations
    @param db De Bruijn variable context mapping Rocq [Rel] indices to Core
    [Core.Type.Variable] indices; [0] means the Rel is not a type var
    @param j Next available Core type variable index; [0] means no new type vars are generated
    @param c The Rocq term to extract as a type (possibly a type-level function)
    @param args Arguments accumulated during [App] spine traversal *)
let rec extract_type env sg db j c args : Core.Type.extracted = fst (extract_spine env sg db j c args)

(** {!extract_type}, together with the binders of the product spine it walked
    while [j > 0] -- the spine whose type binders it numbers as variables, one
    entry per binder in source order.  Under [j = 0] no variable is numbered
    and the list is empty. *)
and extract_spine env sg db j c args =
  let leaf t = (t, []) in
  match EConstr.kind sg (whd_betaiotazeta env sg c) with
  | App (d, args') ->
    (* We just accumulate the arguments. *)
    extract_spine env sg db j d (Array.to_list args' @ args)
  | Lambda (_, _, d) ->
    ( match args with
    | [] -> assert false (* A lambda cannot be a type. *)
    | a :: args -> extract_spine env sg db j (EConstr.Vars.subst1 a d) args )
  | Prod (n, t, d) ->
    assert (List.is_empty args);
    let env' = push_rel_assum (n, t) env in
    (* The binder's entry: the kill reason its arrow's domain carries, read
       as {!Base.Core_util.type_to_signature} reads it, and the variable it was
       numbered, if any. *)
    let binder ~tvar dom (spine_ty, spine) =
      if Int.equal j 0 then (spine_ty, [])
      else
        let raw_erased =
          match Option.map (expand env) dom with
          | Some (Core.Type.Erased k) -> Some k
          | _ -> None
        in
        (spine_ty, {Core.Schema.erased = raw_erased; tvar = tvar} :: spine)
    in
    let arrow dom (spine_ty, spine) =
      match expand env spine_ty with
      | Core.Type.Erased d -> (Core.Type.Erased d, spine)
      | _ -> (Core.Type.Arrow {parameter = Lazy.force dom; result = spine_ty}, spine)
    in
    ( match flag_of_type env sg t with
    | Info, Default ->
      (* Standard case: two [extract_type] ... *)
      let dom = lazy (extract_type env sg db 0 t []) in
      let ((extracted_ty, _) as res) = arrow dom (extract_spine env' sg (0 :: db) j d []) in
      binder ~tvar:None (match extracted_ty with Core.Type.Arrow _ -> Some (Lazy.force dom) | _ -> None) res
    | Info, TypeScheme when j > 0 ->
      (* A new type var. *)
      let dom = Core.Type.Erased Core.Erasure_reason.Type_argument in
      binder ~tvar:(Some j) (Some dom)
        (arrow (lazy dom) (extract_spine env' sg (j :: db) (j + 1) d []))
    | _, lvl ->
      let reason = if lvl == TypeScheme then Core.Erasure_reason.Type_argument else Core.Erasure_reason.Proof in
      let dom = Core.Type.Erased reason in
      binder ~tvar:None (Some dom)
        (arrow (lazy dom) (extract_spine env' sg (0 :: db) j d [])) )
  | Sort _ -> leaf (Core.Type.Erased Core.Erasure_reason.Type_argument) (* The two logical cases. *)
  | _ when info_of_quality (sort_of env sg (applistc c args)) == Logic ->
    leaf (Core.Type.Erased Core.Erasure_reason.Proof)
  | Rel n ->
    ( match EConstr.lookup_rel n env with
    | LocalDef (_, t, _) ->
      extract_spine env sg db j (EConstr.Vars.lift n t) args
    | _ ->
      (* Asks [db] a translation for [n]. *)
      leaf @@
      if n > List.length db then
        Core.Type.Unknown
      else
        let n' = List.nth db (n - 1) in
        if Int.equal n' 0 then
          Core.Type.Unknown
        else if List.is_empty args || not (List.for_all (arg_is_type env sg) args)
        then
          (* No arguments, or arguments that are values: nothing a type-level
             application can hold, so the variable stands alone as before. *)
          Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = n'}
        else
          (* A type variable of arrow kind applied to arguments — the [M A] of
             a class parameterised by a type constructor.  Keeping the
             application lets the instance's carrier stay parameterised in C++
             instead of being erased at its element type. *)
          Core.Type.Variable_app {head = n'; arguments = List.map (fun a -> extract_type env sg db 0 a []) args} )
  | Const (kn, u) ->
    let r = GlobRef.ConstRef kn in
    let () = check_sort_poly sg r u in
    let typ = type_of env sg (EConstr.mkConstU (kn, u)) in
    ( match flag_of_type env sg typ with
    | Logic, _ -> assert false (* Cf. logical cases above *)
    | Info, TypeScheme ->
      leaf @@
      (* For promoted type var projections (e.g., Obj, Hom) applied to
         concrete arguments, try full reduction with whd_all.  This resolves
         expressions like Obj(base_category(toy_prestable)) → nat, which
         whd_betaiotazeta cannot reduce because it lacks delta. *)
      (* [is_promoted_type_var] is answered out of a table that
         {!extract_really_ind} fills, so before the class this projects from
         has been extracted it answers [false] -- and this occurrence is kept
         abstract while a later one, after the class has been reached by some
         other route, reduces.  Two occurrences of one Rocq type then have two
         different Core types, which is not a thing any later pass can notice:
         both are well-formed, and only the disagreement between them is
         wrong.

         Extracting the class first makes the answer independent of the order
         uses are met in.  Which class it is, the projection's own type says:
         it takes the record it projects from as its first argument. *)
      let () =
        if lang () == Cpp && args <> [] && not (Base.Table.is_promoted_type_var r)
        then
          match EConstr.kind sg (whd_all env sg typ) with
          | Prod (_, dom, _) -> (
            match EConstr.kind sg (EConstr.decompose_app sg dom |> fst) with
            | Ind ((mind, _), _) when not (already_extracting mind) ->
              with_extracting mind (fun () ->
                  try ignore (extract_ind env mind)
                  with e when CErrors.noncritical e -> () )
            | _ -> () )
          | _ -> ()
      in
      if lang () == Cpp && args <> [] && Base.Table.is_promoted_type_var r then
        let full = EConstr.applist (EConstr.mkConstU (kn, u), args) in
        let reduced =
          try whd_all env sg full
          with e when CErrors.noncritical e -> full
        in
        let is_stuck =
          match EConstr.kind sg reduced with
          | Const (kn', _) -> Constant.CanOrd.equal kn kn'
          | App (f, _) -> (
            match EConstr.kind sg f with
            | Const (kn', _) -> Constant.CanOrd.equal kn kn'
            | _ -> false )
          | Case _ -> true
          | _ -> false
        in
        if is_stuck then
          extract_type_app env sg db (r, type_sign env sg typ) args
        else
          extract_type env sg db 0 reduced []
      else (
        match sequential_monad_alias env sg (kn, u) args with
        | Some monad -> extract_type env sg db 0 monad []
        | None -> extract_type_app env sg db (r, type_sign env sg typ) args )
    | Info, Default ->
    (* Not a Core type, for example [(c:forall X, X->X) Type nat] *)
    match (lookup_constant kn env).const_body with
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ ->
      leaf Core.Type.Unknown (* Brutal approx ... *)
    | Def lbody ->
      (* We try to reduce. *)
      let newc = applistc (get_body lbody) args in
      extract_spine env sg db j newc [] )
  | Ind (((kn, i) as ind), u) ->
    let () = check_sort_poly sg (IndRef ind) u in
    let s = (extract_ind env kn).Core.Inductive.packets.(i).signature in
    leaf (extract_type_app env sg db (GlobRef.IndRef (kn, i), s) args)
  | Proj (p, r, t) ->
    (* Let's try to reduce, if it hasn't already been done. *)
    if Projection.unfolded p then
      leaf Core.Type.Unknown
    else
      extract_spine env sg db j (EConstr.mkProj (Projection.unfold p, r, t)) args
  | Case _ | Fix _ | CoFix _ -> leaf Core.Type.Unknown
  | Evar _ | Meta _ -> leaf Core.Type.Axiom (* only possible during Show Extraction *)
  | Var v ->
    (* For Show Extraction *)
    let open Context.Named.Declaration in
    ( match EConstr.lookup_named v env with
    | LocalDef (_, body, _) ->
      extract_spine env sg db j (EConstr.applist (body, args)) []
    | LocalAssum (_, ty) ->
      let r = GlobRef.VarRef v in
      ( match flag_of_type env sg ty with
      | Logic, _ -> assert false (* Cf. logical cases above *)
      | Info, TypeScheme ->
        leaf (extract_type_app env sg db (r, type_sign env sg ty) args)
      | Info, Default -> leaf Core.Type.Unknown ) )
  | Cast _ | LetIn _ | Construct _ | Int _ | Float _ | String _ | Array _ ->
    assert false

(* TODO: I think type application isn't happening/reducing in instances where
   not needed for OCaml. Type variables that are semantically instantiated in
   Rocq are appearing in extracted code at the term level. *)

(** {2 Auxiliary function dealing with type application. Precondition: [r] is a
    type scheme represented by the signature [s], and is completely applied:
    [List.length args = List.length s]} *)

(** The type constant [c] applied to [args], unfolded, where it stands for a
    monad Crane runs sequentially.  Such a monad's value is the running of
    its effects, spelled as what it yields, so an alias of one has no C++
    spelling of its own: every reader of the type -- whether a declaration
    is run when performed, whether a call returns [void], how the monad is
    erased -- must see the monad itself, as it does where the source writes
    it.  A reified monad is a tree, a value C++ spells; its alias is kept. *)
and sequential_monad_alias env sg (kn, u) args =
  if lang () != Cpp || Base.Table.is_monad (GlobRef.ConstRef kn) then None
  else
    let full = EConstr.applist (EConstr.mkConstU (kn, u), args) in
    match whd_all env sg full with
    | exception e when CErrors.noncritical e -> None
    | unfolded -> (
      let head =
        match EConstr.kind sg (fst (EConstr.decompose_app sg unfolded)) with
        | Ind (ind, _) -> Some (GlobRef.IndRef ind)
        | Const (kn', _) when not (Constant.CanOrd.equal kn kn') -> Some (GlobRef.ConstRef kn')
        | _ -> None
      in
      match head with
      | Some m when Base.Table.is_monad m && not (Base.Table.is_monad_reified m) -> Some unfolded
      | Some _ | None -> None )

(** Extracts a type application (inductive applied to arguments), given a type
    scheme and its signature. *)
and extract_type_app env sg db (r, s) args =
  let core_ty_args =
    List.fold_right
      (fun (b, c) a ->
        if b == Core.Signature.Argument.Runtime then
          let p =
            List.length (fst (whd_decompose_prod env sg (type_of env sg c)))
          in
          let db = iterate (fun l -> 0 :: l) p db in
          extract_type_scheme env sg db c p :: a
        else
          a )
      (List.combine s args)
      []
  in
  let core_args =
    List.fold_right
      (fun (b, c) a ->
        (* A kept argument is a type, already in [core_ty_args]: its place among
           the arguments a custom's text reads is held by an erased one.  As a
           term it would name a type as a value -- a functor's parameter type
           as a callee no callable plan exists for. *)
        match b with
        | Core.Signature.Argument.Runtime -> Core.Expr.Erased_value Core.Erasure_reason.Type_argument :: a
        | Core.Signature.Argument.Erased _ -> (
          try
            let p =
              List.length (fst (whd_decompose_prod env sg (type_of env sg c)))
            in
            let db = iterate (fun l -> 0 :: l) p db in
            let ty = type_of env sg c in
            let ty = extract_type_scheme env sg db ty p in
            Core_passes.Spines.spine (extract_term env sg Type_env.empty ty c []) :: a
          with e when best_effort_failure e -> a ) )
      (List.combine s args)
      []
  in
  Core.Type.Global_app {head = r; type_arguments = core_ty_args; index_arguments = core_args}

(* [extract_type_scheme env db c p] works on a Rocq term [c] which is an
   informative type scheme. It means that [c] is not a Rocq type, but will be
   when applied to sufficiently many arguments ([p] in fact). This function
   decomposes p lambdas, with eta-expansion if needed. *)

(* [db] is a context for translating Rocq [Rel] into Core type [Core.Type.Variable]. *)

(** {1 Extraction of a type scheme} *)

(** Extracts a type scheme (universally quantified type) by decomposing [p]
    lambdas with eta-expansion if needed.
    @param env Rocq environment, extended with binders as lambdas are peeled
    @param sg Evar map for universe operations
    @param db De Bruijn variable context (see {!extract_type})
    @param c The informative type-scheme term; must become a type after [p] more applications
    @param p Number of remaining type arguments to strip (eta-expanded if fewer lambdas exist) *)
and extract_type_scheme env sg db c p =
  if Int.equal p 0 then
    extract_type env sg db 0 c []
  else
    let c = whd_betaiotazeta env sg c in
    match EConstr.kind sg c with
    | Lambda (n, t, d) ->
      extract_type_scheme (push_rel_assum (n, t) env) sg db d (p - 1)
    | _ ->
      let rels = fst (whd_decompose_prod env sg (type_of env sg c)) in
      let env = push_rels_assum rels env in
      let eta_args = List.rev_map EConstr.mkRel (List.interval 1 p) in
      extract_type env sg db 0 (EConstr.Vars.lift p c) eta_args

(** Extracts [c], the argument a type variable is instantiated at, when that
    variable stands for a family over values: [P : nat -> Type], whose every
    application [P n] {!extract_type} reads as the variable itself.  The Core type
    the variable is instantiated at is then the family's body, its binders
    erased as any index is -- [fun _ => bool] instantiates it at [bool],
    [fun n => vec A n] at [vec A].  One value binder is enough to make the
    variable such a family: [P : Type -> nat -> Type] is read whole as well,
    so [fun _ _ => nat -> nat] instantiates it at [nat -> nat].  A family
    whose binders all range over types is a type constructor, and has no Core
    type: [None] -- unless it ignores them: [fun T => list nat] is the
    carrier [list nat], whatever it is applied to (see
    {!Base.Core_util.apply_core_type}).  Anything else is the plain {!extract_type}
    question. *)
and extract_family_type env sg db c =
  (* A type function bound by a [let] is its definition: [N.binary_rect]
     passes [positive_rect] its [let P' p := P (pos p)], which has no type
     variable of its own to stand for. *)
  let rec unfold_local c =
    let head, args = EConstr.decompose_app sg c in
    match EConstr.kind sg head with
    | Rel i -> (
      match EConstr.lookup_rel i env with
      | Context.Rel.Declaration.LocalDef (_, b, _) ->
        unfold_local (EConstr.mkApp (EConstr.Vars.lift i b, args))
      | Context.Rel.Declaration.LocalAssum _ -> c )
    | _ -> c
  in
  let c = unfold_local c in
  let rec peel env db n has_value c =
    match EConstr.kind sg (whd_betaiotazeta env sg c) with
    | Lambda (x, t, d) ->
      peel (push_rel_assum (x, t) env) (0 :: db) (n + 1)
        (has_value || snd (flag_of_type env sg t) == Default) d
    | _ when has_value || (n > 0 && EConstr.Vars.noccur_between sg 1 n c) ->
      Some (extract_type env sg db 0 c [])
    | _ -> None
  in
  match peel env db 0 false c with
  | Some t -> Some t
  | None -> (
    match EConstr.kind sg (whd_betaiotazeta env sg c) with
    | Lambda _ -> None
    | _ -> Some (extract_type env sg db 0 c []) )

(* First, a version with cache *)

(** {1 Extraction of an inductive type} *)

(** Extracts an inductive type, with caching to avoid redundant work. *)
and extract_ind env kn =
  (* kn is supposed to be in long form *)
  let mib = Environ.lookup_mind kn env in
  match lookup_ind kn mib with
  | Some core_ind -> core_ind
  | None ->
  try extract_really_ind env kn mib
  with SingletonInductiveBecomesProp ind -> error_singleton_become_prop ind

(* Then the real function *)

(** Performs the actual inductive type extraction, building packets,
    constructors, and detecting special cases. *)
and extract_really_ind env kn mib =
  (* First, if this inductive is aliased via a Module, we process the original
     inductive if possible. When at toplevel of the monolithic case, we cannot
     do much (cf Vector and bug #2570) *)
  let equiv =
    if
      lang () != Cpp
      || ((not (modular ())) && at_toplevel (MutInd.modpath kn))
      || KerName.equal (MutInd.canonical kn) (MutInd.user kn)
    then
      Core.Inductive.Equivalence.Distinct
    else (
      ignore (extract_ind env (MutInd.make1 (MutInd.canonical kn)));
      Core.Inductive.Equivalence.Equivalent_to (MutInd.canonical kn) )
  in
  (* Everything concerning parameters. *)
  (* We do that first, since they are common to all the [mib]. *)
  let mip0 = mib.mind_packets.(0) in
  let freezer = Core.Freezer.create () in
  let ndecls = List.length mib.mind_params_ctxt in
  let npar = mib.mind_nparams in
  let epar = push_rel_context mib.mind_params_ctxt env in
  let sg = Evd.from_env env in
  (* First pass: we store inductive signatures together with *)
  (* their type var list. *)
  let packets =
    Array.mapi
      (fun i mip ->
        let (_, u), _ = UnivGen.fresh_inductive_instance env (kn, i) in
        let ar = Inductive.type_of_inductive ((mib, mip), u) in
        let ar = EConstr.of_constr ar in
        let info = fst (flag_of_type env sg ar) = Info in
        let s, vl = if info then type_sign_vl env sg ar else ([], []) in
        if info then
          Base.Table.add_ind_hkt_params
            (GlobRef.IndRef (kn, i))
            (hkt_keep_positions env sg ar);
        let t = Array.make (Array.length mip.mind_nf_lc) [] in
        ( {
            Core.Inductive.Packet.name = mip.mind_typename;
            constructor_names = mip.mind_consnames;
            logical = not info;
            signature = s;
            type_variables = vl;
            constructor_argument_types = t;
            constructor_argument_names = Array.make (Array.length mip.mind_nf_lc) [];
          },
          u ) )
      mib.mind_packets
  in

  add_ind
    kn
    mib
    {
      Core.Inductive.kind = Core.Inductive.Kind.Inductive;
      parameter_count = npar;
      packets = Array.map fst packets;
      equivalence = equiv;
    };
  (* Helper: extract product binder names from a constructor type *)
  let rec names_prod t =
    match Constr.kind t with
    | Prod (n, _, t) -> n :: names_prod t
    | LetIn (_, _, _, t) -> names_prod t
    | Cast (t, _, _) -> names_prod t
    | _ -> []
  in
  (* Second pass: we extract constructors.
       For C++ records/classes, Sort-typed and class-typed fields are promoted
       to type variables here, in the same pass that extracts the
       constructor's argument types, so those types already name them. *)
  (* Check if this inductive is a record with a single constructor *)
  let is_record_mib =
    mib.mind_record != Declarations.NotRecord && Int.equal mib.mind_ntypes 1
  in
  for i = 0 to mib.mind_ntypes - 1 do
    let p, u = packets.(i) in
    if not p.logical then
      let types =
        Inductive.arities_of_constructors
          ((kn, i), u)
          (mib, mib.mind_packets.(i))
      in
      for j = 0 to Array.length types - 1 do
        let t = snd (decompose_prod_n_decls ndecls types.(j)) in
        let prods, head = Reduction.whd_decompose_prod epar t in
        let nprods = List.length prods in
        let args =
          match Constr.kind head with
          | App (f, args) -> args (* [Constr.kind f = Ind ip] *)
          | _ -> [||]
        in
        let orig_dbmap = parse_ind_args p.signature args (nprods + ndecls) in
        (* A field whose type is a class projection -- [p : @ptr ProvenanceV
           PointerV] -- makes this inductive depend on the instances the
           projection is applied to, and on whatever they are applied to in
           turn.  Nothing of that survives into the Core inductive, so it is
           recorded here; see {!Base.Table.add_ind_class_arg}. *)
        List.iter
          (fun decl ->
            let fty = Context.Rel.Declaration.get_type decl in
            let rec scan c =
              ( match Constr.kind c with
              | App (f, cargs) when Constr.isConst f ->
                Array.iter
                  (fun a ->
                    match class_arg_shape epar sg (EConstr.of_constr a) with
                    | Some sh -> Base.Table.add_ind_class_arg (GlobRef.IndRef (kn, 0)) sh
                    | None -> () )
                  cargs
              | _ -> () );
              Constr.iter scan c
            in
            scan fty )
          prods;
        (* For C++ records: detect Sort-typed and class-typed fields and
           promote them to type vars, numbered after the inductive's own. *)
        let dbmap =
          if lang () == Cpp && is_record_mib && Int.equal j 0 then (
            let nfields = List.length prods in
            let nb_existing_tvars =
              List.length (List.filter (fun x -> x == Core.Signature.Argument.Runtime) p.signature)
            in
            let next_tvar = ref (nb_existing_tvars + 1) in
            (* Get field names for promoted variable names *)
            let mip_i = mib.mind_packets.(i) in
            let field_names =
              List.skipn mib.mind_nparams (names_prod mip_i.mind_user_lc.(0))
            in
            let promoted_info =
              List.mapi
                (fun idx prod_decl ->
                  let prod_ty = Context.Rel.Declaration.get_type prod_decl in
                  (* A field should be promoted if its Rocq type is:
                     (a) a Sort (Type/Set) — the field carries a type, or
                     (b) a Type_class-classified inductive — the field
                         carries a typeclass dictionary that becomes a
                         concept-constrained template parameter in C++. *)
                  (* [is_typeclass] is answered out of a table this very
                     function fills, so a class asked about before it has been
                     extracted answers [false] and the field holding it is not
                     promoted -- the whole nested dictionary is then missing
                     from the resolutions, and its associated types print as
                     the file-scope [using allocationId = std::any].  Extract
                     it first, under the same guard {!extract_type} uses for
                     the sibling case: the answer must not depend on the order
                     uses are met in. *)
                  let is_typeclass_ind t =
                    let of_ind (mind, i) =
                      if not (already_extracting mind) then
                        with_extracting mind (fun () ->
                            try ignore (extract_ind env mind)
                            with e when CErrors.noncritical e -> () );
                      Base.Table.is_typeclass (GlobRef.IndRef (mind, i))
                    in
                    match Constr.kind t with
                    | Ind (ind, _) -> of_ind ind
                    | App (f, _) -> (
                      match Constr.kind f with
                      | Ind (ind, _) -> of_ind ind
                      | _ -> false )
                    | _ -> false
                  in
                  let should_promote =
                    ( match Constr.kind prod_ty with
                    | Sort s when not (Sorts.is_prop s) -> true
                    | _ -> false )
                    || is_typeclass_ind prod_ty
                  in
                  if should_promote then
                    (* prod_decl is at position (nfields-1-idx) because
                       prods lists fields in reverse order. *)
                    let field_idx = nfields - 1 - idx in
                    let pos = ndecls + 1 + field_idx in
                    let var_name =
                      if field_idx < List.length field_names then
                        let fn = List.nth field_names field_idx in
                        match fn.binder_name with
                        | Name id -> id
                        | Anonymous -> anon_tvar_id field_idx
                      else
                        anon_tvar_id field_idx
                    in
                    Some (pos, field_idx, var_name)
                  else
                    None )
                prods
            in
            (* [prods] lists fields in reverse declaration order.  Restore
               declaration order before numbering the type variables: the
               order of [type_variables] is what an instance's class arguments are
               matched against, so a class with two associated types would
               otherwise get them swapped. *)
            let promoted_entries =
              List.filter_map Fun.id promoted_info
              |> List.sort (fun (_, a, _) (_, b, _) -> Int.compare a b)
              |> List.map (fun (pos, field_idx, var_name) ->
                     let tv = !next_tvar in
                     incr next_tvar;
                     (pos, tv, field_idx, var_name) )
            in
            (* Only promote if there are promotable fields AND also other
               fields (i.e., the record has actual methods/data, not just
               types). This prevents promotion for degenerate cases. *)
            let n_non_sort = nfields - List.length promoted_entries in
            if promoted_entries = [] || n_non_sort <= 0 then
              orig_dbmap
            else
              let promoted_dbmap =
                List.fold_left
                  (fun dm (pos, tv, _, _) -> Int.Map.add pos tv dm)
                  Int.Map.empty
                  promoted_entries
              in
              let merged =
                Int.Map.union (fun _k _a b -> Some b) orig_dbmap promoted_dbmap
              in
              let promoted_var_names =
                List.map (fun (_, _, _, name) -> name) promoted_entries
              in
              (* Also register promoted type vars in the table and extend
                 type_variables *)
              let mp = MutInd.modpath kn in
              List.iter
                (fun (_, _, field_idx, var_name) ->
                  if field_idx < List.length field_names then
                    let fn = List.nth field_names field_idx in
                    match fn.binder_name with
                    | Name id ->
                      let knp = Constant.make2 mp (Label.of_id id) in
                      add_promoted_type_var (GlobRef.ConstRef knp) var_name
                    | _ -> () )
                promoted_entries;
              (* Register non-promoted type-valued fields as erased type
                 constants.  These are dependent type families like
                 [Hom : Obj -> Obj -> Type] whose type ends in Sort after
                 stripping Prod wrappers, but that weren't promoted because
                 they have term-level arguments. *)
              let promoted_field_indices =
                List.map (fun (_, _, fi, _) -> fi) promoted_entries
              in
              let rec type_ends_in_sort t =
                match Constr.kind t with
                | Sort s -> not (Sorts.is_prop s)
                | Prod (_, _, body) -> type_ends_in_sort body
                | _ -> false
              in
              List.iteri
                (fun idx prod_decl ->
                  let field_idx = nfields - 1 - idx in
                  if not (List.mem field_idx promoted_field_indices) then
                    let prod_ty =
                      Context.Rel.Declaration.get_type prod_decl
                    in
                    if type_ends_in_sort prod_ty then
                      if field_idx < List.length field_names then
                        let fn = List.nth field_names field_idx in
                        match fn.binder_name with
                        | Name id ->
                          let knp = Constant.make2 mp (Label.of_id id) in
                          add_erased_type_const (GlobRef.ConstRef knp)
                        | _ -> () )
                prods;
              p.type_variables <- p.type_variables @ promoted_var_names;
              merged )
          else
            orig_dbmap
        in
        let db = db_from_ind dbmap ndecls in
        (* A constructor type is frozen as it is stored: an index argument is
           a term, reconstructed here and solved as far as it can be. *)
        p.constructor_argument_types.(j) <-
          List.map (Core.Freezer.type_ freezer) (extract_type_cons epar sg db dbmap (EConstr.of_constr t) (ndecls + 1));
        (* Populate constructor argument names from kernel binder names only.
           [mind_user_lc] has anonymous binders when constructors use [->]
           syntax.  [Arguments_renaming] names are applied later in
           [Core_to_cpp.Naming.compute_and_register_field_names] for struct field
           declarations, but NOT for structured-binding variable names (to
           avoid variable-shadowing in nested matches). *)
        let mip_i = mib.mind_packets.(i) in
        let all_names = names_prod mip_i.mind_user_lc.(j) in
        let arg_names = List.skipn mib.mind_nparams all_names in
        p.constructor_argument_names.(j) <-
          List.map
            (fun n ->
              match n.binder_name with Name id -> Some id | Anonymous -> None)
            arg_names
      done
  done;
  (* Third pass: we determine special cases. *)
  let ind_info =
    try
      let ip = (kn, 0) in
      let r = GlobRef.IndRef ip in
      if is_custom r then raise (I Core.Inductive.Kind.Inductive);
      if mib.mind_finite == CoFinite then raise (I Core.Inductive.Kind.Coinductive);
      if not (Int.equal mib.mind_ntypes 1) then raise (I Core.Inductive.Kind.Inductive);
      let p, u = packets.(0) in
      if p.logical then raise (I Core.Inductive.Kind.Inductive);
      if not (Int.equal (Array.length p.constructor_argument_types) 1) then raise (I Core.Inductive.Kind.Inductive);
      let typ = p.constructor_argument_types.(0) in
      let l =
        if conservative_types () then
          []
        else
          List.filter (fun t -> not (is_erased_type (expand env t))) typ
      in
      if List.is_empty l then raise (I Core.Inductive.Kind.Inductive);
      if mib.mind_record == Declarations.NotRecord then raise (I Core.Inductive.Kind.Inductive);
      (* A record is emitted as a flat C++ struct holding its fields by
         value, which cannot express a field whose type mentions the record
         itself: [Inductive cell := MkCell { key : nat; kids : list cell }]
         would produce [List<cell> kids;] inside [struct cell], before the
         closing brace, i.e. an incomplete type.  The standard inductive
         representation has no such problem -- it puts recursive occurrences
         behind a smart pointer -- so fall back to it.  (The single-
         constructor "flat" layout declines self-referential types for the
         same reason, {!Base.Table.is_flat_inductive_packet}; records reach the
         flat struct by a different route and need the same guard.)  Rocq
         rejects recursive [Record]s outright, so this only fires for the
         [Inductive]-with-named-fields spelling.  The occurrence is looked
         for anywhere in the field's type, not just at its head: going
         through a container ([list cell]) leaves the struct just as
         incomplete as a bare [cell] field would. *)
      let rec mentions_self t =
        match t with
        | Core.Type.Global_app {head = gr; type_arguments = args; _} ->
          (match gr with
           | GlobRef.IndRef (kn', _) when MutInd.CanOrd.equal kn' kn -> true
           | _ -> List.exists mentions_self args)
        | Core.Type.Arrow {parameter = a; result = b} -> mentions_self a || mentions_self b
        | Core.Type.Meta {contents = Some t} -> mentions_self t
        | _ -> false
      in
      if List.exists mentions_self typ then raise (I Core.Inductive.Kind.Inductive);
      (* Now we're sure it's a record. *)
      (* First, we find its field names. *)
      let field_names =
        List.skipn mib.mind_nparams (names_prod mip0.mind_user_lc.(0))
      in
      assert (Int.equal (List.length field_names) (List.length typ));
      let mp = MutInd.modpath kn in
      let implicits = implicits_of_global (GlobRef.ConstructRef (ip, 1)) in
      let ty = Inductive.type_of_inductive ((mib, mip0), u) in
      let nparams = nb_default_params env sg (EConstr.of_constr ty) in
      let rec select_fields i l typs =
        match (l, typs) with
        | [], [] -> []
        | _ :: l, typ :: typs
          when is_erased_type (expand env typ) || Int.Set.mem i implicits ->
          select_fields (i + 1) l typs
        | {binder_name = Anonymous} :: l, typ :: typs ->
          {Core.Record.Field.projection = None; type_ = typ} :: select_fields (i + 1) l typs
        | {binder_name = Name id} :: l, typ :: typs ->
          let knp = Constant.make2 mp (Label.of_id id) in
          (* Is it safe to use [id] for projections [foo.id] ? *)
          if List.for_all (( == ) Core.Signature.Argument.Runtime) (type2signature env typ) then
            (* for OCaml inlining: *)
            add_projection nparams knp ip;
          {Core.Record.Field.projection = Some (GlobRef.ConstRef knp); type_ = typ} :: select_fields (i + 1) l typs
        | _ -> assert false
      in
      let field_glob = select_fields (1 + npar) field_names typ in
      (* Check if this is a type class registered in the Rocq typeclasses
         database *)
      let is_class = Option.has_some (Typeclasses.class_info r) in
      (* Detect "promotion": Type-valued record fields that must become type
         parameters in C++ concepts rather than struct fields.

         During the second extraction pass, Sort-typed fields (e.g., [m_carrier : Type])
         are added to [type_variables] but NOT kept in [signature] (they're not concrete
         values that can be stored in a struct). If [type_variables] has more entries
         than the [Core.Signature.Argument.Runtime] count in [signature], some fields were promoted.

         Example:
           Record Monoid := {
             m_carrier : Type;        (* promoted: Type-valued *)
             m_op : m_carrier -> ...  (* not promoted: function *)
           }.

         After promotion:
           - nb_sign_keeps = 0 (no regular fields kept)
           - type_variables = ["m_carrier"] (1 promoted field)
           - has_promoted = true → classify as Type_class for concept generation

         Without promotion, [m_carrier] would be a struct field of type "Type",
         which doesn't exist in C++. Instead, it becomes:
           template <typename I>
           concept Monoid = requires { typename I::m_carrier; ... }; *)
      let nb_sign_keeps =
        List.length (List.filter (fun x -> x == Core.Signature.Argument.Runtime) p.signature)
      in
      let has_promoted =
        lang () == Cpp && List.length p.type_variables > nb_sign_keeps
      in
      (* A promoted record (with Type-valued fields) should be a Type_class
         (C++ concept) only when it also carries function-typed fields —
         i.e., it models an algebraic structure such as Monoid whose
         operations become [requires]-clause entries.  A record with only
         data-typed promoted fields (e.g. Container with [elem : elem_type]
         and [count : nat]) stays a plain [Record] (template struct). *)
      let rec has_arrow_type = function
        | Core.Type.Arrow _ -> true
        | Core.Type.Meta { contents = Some t } -> has_arrow_type t
        | _ -> false
      in
      let has_arrow_field =
        List.exists
          (fun t ->
            let t = expand env t in
            (not (is_erased_type t)) && has_arrow_type t)
          typ
      in
      if is_class || (has_promoted && has_arrow_field) then
        Core.Inductive.Kind.Type_class field_glob
      else
        Core.Inductive.Kind.Record field_glob
    with I info -> info
  in
  let i =
    {
      Core.Inductive.kind = ind_info;
      parameter_count = npar;
      packets = Array.map fst packets;
      equivalence = equiv;
    }
  in
  add_ind kn mib i;
  add_inductive_kind kn i.kind;
  i

(** {2 [extract_type_cons] extracts the type of an inductive
  constructor toward the corresponding list of Core types.

   - [db] is a context for translating Rocq [Rel] into Core type [Core.Type.Variable]
   - [dbmap] is a translation map (produced by a call to [parse_ind_args])
   - [i] is the rank of the current product (initially [ndecls+1])} *)

(** Extracts a constructor's type signature into a list of Core types.
    @param env Rocq environment, extended as each product binder is consumed
    @param sg Evar map for universe operations
    @param db De Bruijn variable context for [Rel]→[Core.Type.Variable] translation
    @param dbmap Position-to-type-var map produced by {!parse_ind_args}
    @param c Constructor type (starting after inductive parameters have been stripped)
    @param i Rank of the current product: the de Bruijn level of its binder
      under the inductive's parameter context, so initially [ndecls + 1],
      counting let-in parameters, which the context binds as [Rel]s too *)
and extract_type_cons env sg db dbmap c i =
  match EConstr.kind sg (whd_all env sg c) with
  | Prod (n, t, d) ->
    let env' = push_rel_assum (n, t) env in
    let db' = (try Int.Map.find i dbmap with Not_found -> 0) :: db in
    let l = extract_type_cons env' sg db' dbmap d (i + 1) in
    extract_type env sg db 0 t [] :: l
  | _ -> []

(** {2 Recording the Core type abbreviation of a Rocq type scheme constant} *)

(** Looks up the Core type of a constant in the extraction environment. *)
and type_constant_body env r =
  let open GlobRef in
  match r with
  | IndRef _ | ConstructRef _ | VarRef _ -> None
  | ConstRef kn ->
    if Base.Table.is_custom r then None
      (* A promoted type variable is a name, not an abbreviation.  Its Rocq
         body is the record projection -- a [match] -- which [extract_type]
         can only answer [Core.Type.Unknown] for, so delta-reducing it replaces the
         one spelling that still says which class field this is with the
         erasure.  [frame := list ptr] then expands to [list unk] and the
         parameter is written [List<std::any>] against a return type that
         still names [frame<typename I::PTR::ptr>]. *)
    else if Base.Table.is_promoted_type_var r then None
    else
    let cb = Environ.lookup_constant kn env in
    ( match cb.const_body with
    | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ -> None
    | Def l_body ->
    match lookup_typedef kn cb with
    | Some _ as o -> o
    | None ->
      let sg = Evd.from_env env in
      let typ =
        EConstr.of_constr cb.const_type
        (* FIXME not sure if we should instantiate univs here *)
      in
      ( match flag_of_type env sg typ with
      | Info, TypeScheme ->
        let body = get_body l_body in
        let s = type_sign env sg typ in
        let db = db_from_sign s in
        let t = Core.Freezer.type_ (Core.Freezer.create ()) (extract_type_scheme env sg db body (List.length s)) in
        add_typedef kn cb t;
        Some t
      | _ -> None ) )

(** {!type_constant_body} at any phase: the frozen body widened. *)
and constant_body_at : 'p. Environ.env -> GlobRef.t -> 'p Core.Type.at option =
 fun env r -> Option.map Core.Widen.type_ (type_constant_body env r)

(** Expands a type alias using the environment. *)
and expand : 'p. Environ.env -> 'p Core.Type.at -> 'p Core.Type.at =
 fun env t -> type_expand (constant_body_at env) t

(** Converts a Core type to a type signature (Keep/Kill list). *)
and type2signature : 'p. Environ.env -> 'p Core.Type.at -> Core.Signature.t =
 fun env t -> type_to_signature (constant_body_at env) t

(** Converts a Core type to a simplified type signature (list of types). *)
and type2sign : 'p. Environ.env -> 'p Core.Type.at -> Core.Signature.Argument.t =
 fun env t -> type_to_sign (constant_body_at env) t

(** {2 Extraction of the type of a constant} *)

(** Computes and caches the Core type of a Rocq constant.
    @param env Rocq environment used for type extraction and expansion
    @param sg Evar map for universe and sort operations
    @param kn The constant whose Core type is computed
    @param opt_typ Optional pre-computed Rocq type of [kn]; if [None], the type is read from [env]
    @return The constant's scheme *)
and record_constant_type env sg kn opt_typ =
  let cb = lookup_constant kn env in
  (* The type call sites read says which arguments the declaration takes: one
     declared implicit ([Crane Extraction Implicit]) is dropped from the
     declaration as an erased one is, so its domain is a [Core.Type.Erased] there,
     carrying the signature's [Core.Erasure_reason.Configured_implicit] -- the binder's role,
     [Erased (Implicit _)], as {!Base.Type_util.binder_role} reads it. *)
  let register extracted_ty =
    let r = GlobRef.ConstRef kn in
    let rec mark s t =
      match (s, t) with
      | Core.Signature.Argument.Erased k :: s, Core.Type.Arrow {parameter = a; result = b}
        when not (is_erased_type a) ->
        Core.Type.Arrow {parameter = Core.Type.Erased k; result = mark s b}
      | _ :: s, Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = a; result = mark s b}
      | _, Core.Type.Meta {contents = Some t} -> mark s t
      | _ -> t
    in
    register_glob_def r (mark (sign_with_implicits r (type2signature env extracted_ty) 0) extracted_ty)
  in
  match lookup_cst_type kn cb with
  | Some schema ->
    register (Core.Widen.type_ (Core.Schema.body schema));
    schema_view (GlobRef.ConstRef kn) schema
  | None ->
    let typ =
      match opt_typ with
      | None -> EConstr.of_constr cb.const_type
      | Some typ -> typ
    in
    (* The binder layout comes out of the same walk that numbers the
       variables, and is cached with the body it describes. *)
    let extracted_ty, spine = extract_spine env sg [] 1 typ [] in
    (* An abbreviation on the spine -- [id : ID], [ID := forall A, A -> A] --
       hides binders the walk above stops at, and a call passes arguments for
       them as for the constant's own.  The layout is read off the type with
       the spine's abbreviations unfolded, by the same walk: it extends the
       spine above, numbering the binders it uncovers after the ones the body
       already names. *)
    let spine =
      let unfolded = unfold_spine env sg typ in
      if EConstr.eq_constr sg unfolded typ then spine
      else snd (extract_spine env sg [] 1 unfolded [])
    in
    (* A scheme is frozen as it is made: its body is read by every later
       declaration, extracted or frozen, and is never solved again. *)
    let frozen_ty = Core.Freezer.type_ (Core.Freezer.create ()) extracted_ty in
    let schema = Core.Schema.make (GlobRef.ConstRef kn) frozen_ty spine in
    List.iter
      (fun problem ->
        Base.Probe.violation "schema"
          Pp.(str "the scheme of " ++ Names.Constant.print kn ++ str ": " ++ str problem) )
      (Core.Schema.validate schema);
    add_cst_type kn cb schema;
    register extracted_ty;
    schema_view (GlobRef.ConstRef kn) schema

(* Precondition: [(c args)] is not a type scheme, and is informative. *)

(* [type_env] is a type environment [Type_env.t]. *)
(* [extracted_ty] is the Core type we want our extraction of [(c args)] to have. *)

(** {1 Extraction of a term} *)

(** The member types of a local fixpoint group that recurses at a ground
    instance, or [None] for one that does not.  [entries] are the argument
    lists the group's member [i] is entered with from outside.

    A local group is typed as one Core fixpoint group: one type per member, which its
    calls share.  A type binder passed a closed type by a call inside the
    group ([f bool ...] inside [f (A : Type)]), and something else as well --
    the [list nat] the group is entered at, say, directly or through a partner
    that passes its own binder on -- is pinned to one and coerced from the
    other: a coercion between two unrelated types that C++ cannot perform.
    Such a group's members are typed from their declared types instead, with
    every type binder unknown -- held as a [crane::obj], as OCaml holds it as
    an [Obj.t] -- and everything else left to inference.

    A binder passed only one closed type is that type throughout, and one
    whose closed types all come from entries is a generalised [let] entered at
    several instances.  One passed types built from variables is not pinned:
    [go (A * A)] does not unify with [A], so inference leaves it a variable
    the member is generic in, and the lifted member is a template calling
    itself at the bigger instance.  A group with no entry -- a recursor's
    fixpoint, which is the constant's whole body -- is the constant itself,
    whose calls are its template's. *)
and erased_fix_types env sg ~entries i (fi, ti, ci) =
  let nf = Array.length fi in
  let type_positions t =
    let rec go env k t acc =
      match EConstr.kind sg (whd_all env sg t) with
      | Prod (x, d, c) ->
        let acc = if is_info_scheme env sg d then k :: acc else acc in
        go (push_rel_assum (x, d) env) (k + 1) c acc
      | _ -> List.rev acc
    in
    go env 0 t []
  in
  let positions = Array.map type_positions ti in
  (* The binder at position [p] of member [m] is [(m, p)].  A call passing a
     caller's own binder on joins the two: inference types them as one. *)
  let parent = Hashtbl.create 7 in
  let rec find x = match Hashtbl.find_opt parent x with Some y when y <> x -> find y | _ -> x in
  let join x y = let x = find x and y = find y in if x <> y then Hashtbl.replace parent x y in
  (* What each binder is passed: a type, closed or not. *)
  let passed = ref [] in
  let pass ~inner m p t = passed := ((m, p), t, inner) :: !passed in
  let walk j =
    let lams, body = EConstr.decompose_lambda sg ci.(j) in
    let l = List.length lams in
    let own q = List.mem q positions.(j) && q < l in
    let rec search depth t =
      ( match EConstr.kind sg t with
      | App (h, args) -> (
        match EConstr.kind sg h with
        | Rel r when r - depth > l && r - depth - l <= nf ->
          let m = nf - (r - depth - l) in
          List.iter
            (fun p ->
              if p < Array.length args then
                match EConstr.kind sg args.(p) with
                | Rel a when a > depth && a - depth <= l && own (l - (a - depth)) ->
                  join (m, p) (j, l - (a - depth))
                | _ -> pass ~inner:true m p args.(p) )
            positions.(m)
        | _ -> () )
      | _ -> () );
      EConstr.iter_with_binders sg succ search depth t
    in
    search 0 body
  in
  List.iter
    (fun args ->
      List.iter (fun p -> if p < Array.length args then pass ~inner:false i p args.(p)) positions.(i))
    entries;
  (* A binder a call inside the group passes a closed type, and that is
     passed anything else too, is typed at two instances, which one Core type
     cannot be.  Entries alone differing are a [let] generalised. *)
  let pinned_twice () =
    List.iter walk (List.init nf Fun.id);
    List.exists
      (fun (x, t, inner) ->
        inner
        && EConstr.Vars.closed0 sg t
        && List.exists (fun (y, u, _) -> find x = find y && not (EConstr.eq_constr sg t u)) !passed )
      !passed
  in
  if
    lang () != Cpp
    || List.is_empty entries
    || Array.for_all List.is_empty positions
    || not (pinned_twice ())
  then None
  else
    let rec erase = function
      | Core.Type.Variable _ | Core.Type.Variable_app _ -> Core.Type.Unknown
      | Core.Type.Unknown -> new_meta ()
      | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = erase a; result = erase b}
      | Core.Type.Global_app {head = r; type_arguments = l; index_arguments = a} ->
        Core.Type.Global_app {head = r; type_arguments = List.map erase l; index_arguments = a}
      | Core.Type.Meta {contents = Some t} -> erase t
      | t -> t
    in
    try Some (Array.map (fun t -> erase (extract_type env sg [] 1 t [])) ti)
    with e when CErrors.noncritical e -> None

(** Extracts a Rocq PCUIC term into a Core expression. Precondition: term is
    informative and not a type scheme.
    @param env Rocq environment, extended as lambdas and let-ins are entered
    @param sg Evar map for type-of and sort queries
    @param type_env type environment tracking types of bound variables (de Bruijn context)
    @param extracted_ty Expected Core type of [(c args)]; used to drive unification and insert magic coercions
    @param c The Rocq term being extracted (head of the application spine)
    @param args Arguments accumulated during [App] traversal (outermost first) *)
and extract_term env sg type_env (extracted_ty : Core.Type.extracted) c args =
  match EConstr.kind sg c with
  | App (f, a) -> extract_term env sg type_env extracted_ty f (Array.to_list a @ args)
  | Lambda (n, t, d) ->
    let id = map_annot id_of_name n in
    let idna = map_annot Name.mk_name id in
    ( match args with
    | a :: l ->
      (* We make as many [LetIn] as possible. *)
      let l' = List.map (EConstr.Vars.lift 1) l in
      let d' = EConstr.mkLetIn (idna, a, t, applistc d l') in
      extract_term env sg type_env extracted_ty d' []
    | [] ->
      let env' = push_rel_assum (idna, t) env in
      let id, a =
        try
          check_default env sg t;
          (Core.Binder_name.Source id.binder_name, new_meta ())
        with NotDefault d -> (Core.Binder_name.Anonymous, Core.Type.Erased d)
      in
      let b = new_meta () in
      (* If [extracted_ty] cannot be unified with an arrow type, then magic! *)
      let magic = needs_magic (extracted_ty, Core.Type.Arrow {parameter = a; result = b}) in
      let d' = extract_term env' sg (Type_env.push_type type_env a) b d [] in
      put_magic_if ~from:(Core.Type.Arrow {parameter = a;
                                           result = b}) ~into:extracted_ty magic (Core.Expr.Lambda {parameter = id;
                                                                                           parameter_type = a;
                                                                                           body = d'}) )
  | LetIn (n, c1, t1, c2) ->
    let id = map_annot id_of_name n in
    let env' =
      EConstr.push_rel (LocalDef (map_annot Name.mk_name id, c1, t1)) env
    in
    (* We directly push the args inside the [LetIn]. TODO: the opt_let_app flag
       is supposed to prevent that *)
    let args' = List.map (EConstr.Vars.lift 1) args in
    ( try
        check_default env sg t1;
        (* Nothing erased either: an annotation that lost a component would
           overrule what inference knows about it. *)
        let rec informative_type = function
          | Core.Type.Unknown | Core.Type.Axiom | Core.Type.Erased _ -> false
          | Core.Type.Meta {contents = Some t} -> informative_type t
          | Core.Type.Global_app {type_arguments = l; _} -> List.for_all informative_type l
          | Core.Type.Arrow {parameter = a; result = b} -> informative_type a && informative_type b
          | Core.Type.Variable_app {arguments = l; _} -> List.for_all informative_type l
          | _ -> true
        in
        let a = new_meta () in
        (* The binder's declared type says what inference may not find: [let
           body : top nat := ...] fixes the event family [top] spells, which a
           body built from erased carriers ([ret], [fmap]) leaves a free
           meta -- and a free meta generalises into a parameter no call
           supplies when the binding is lifted.  Only a ground, fully
           informative annotation is given: one naming a type variable names
           it the way this context is numbered, which the term's own
           variables need not be. *)
        let () =
          if lang () == Cpp then
            match
              try Some (extract_type env sg (db_from_rel_context env) 0 t1 [])
              with e when CErrors.noncritical e -> None
            with
            | Some ty when Int.equal (type_maxvar ty) 0 && informative_type ty ->
              try_mgu a ty
            | _ -> ()
        in
        let c1' =
          match EConstr.kind sg c1 with
          | Fix _ ->
            (* The applications of the bound name in the body are the
               group's entries ({!erased_fix_types}). *)
            let entries = ref [] in
            let rec search depth t =
              ( match EConstr.kind sg t with
              | App (h, a) when EConstr.isRelN sg (depth + 1) h -> entries := a :: !entries
              | _ -> () );
              EConstr.iter_with_binders sg succ search depth t
            in
            search 0 (applistc c2 args');
            let saved = !let_fix_entries in
            let_fix_entries := Some (c1, !entries);
            Fun.protect ~finally:(fun () -> let_fix_entries := saved) (fun () -> extract_term env sg type_env a c1 [])
          | _ -> extract_term env sg type_env a c1 []
        in
        (* The type of [c1'] is generalized and stored in [type_env]. *)
        let type_env' =
          if generalizable c1' then
            Type_env.push_gen type_env a
          else
            Type_env.push_type type_env a
        in
        Core.Expr.Let {binder = Core.Binder_name.Source id.binder_name;
                       binder_type = a;
                       value = c1';
                       body = extract_term env' sg type_env' extracted_ty c2 args';
                       occurrence = Core.Occurrence.fresh ()}
      with NotDefault d ->
        let type_env' = Type_env.push_std_type type_env (Core.Type.Erased d) in
        ast_pop (extract_term env' sg type_env' extracted_ty c2 args') )
  | Const (kn, u) ->
    let () = check_sort_poly sg (ConstRef kn) u in
    extract_cst_app env sg type_env extracted_ty kn args
  | Construct (cp, u) ->
    let () = check_sort_poly sg (ConstructRef cp) u in
    extract_cons_app env sg type_env extracted_ty cp args
  | Proj (p, _, c) ->
    let p = Projection.repr p in
    let term = fake_match_projection env p in
    let ind =
      Inductiveops.find_rectype env sg (Retyping.get_type_of env sg c)
    in
    let indf, _ = Inductiveops.dest_ind_type ind in
    let _, indargs = Inductiveops.dest_ind_family indf in
    extract_term
      env
      sg
      type_env
      extracted_ty
      (beta_applist sg (EConstr.of_constr term, indargs @ [c]))
      args
  | Rel n ->
    (* As soon as the expected [extracted_ty] for the head is known, *)
    (* we unify it with an fresh copy of the stored type of [Rel n]. *)
    let extract_rel extracted_ty =
      put_magic ~from:(Type_env.get type_env n) ~into:extracted_ty (Core.Expr.fresh_rel n)
    in
    extract_app env sg type_env extracted_ty extract_rel args
  | Case (ci, u, pms, r, iv, c0, br) ->
    (* If invert_case then this is a match that will get erased later, but right
       now we don't care. *)
    let ip, r, iv, c0, br =
      EConstr.expand_case env sg (ci, u, pms, r, iv, c0, br)
    in
    let ip = ci.ci_ind in
    extract_app env sg type_env extracted_ty (extract_case env sg type_env (ip, c0, br)) args
  | Fix ((_, i), recd) ->
    (* The group is entered by this application, or, let-bound, by the
       applications of its name the let's body makes; one applied to
       variables alone is an eta-expansion of a constant that is the
       fixpoint, and enters nothing. *)
    let entries =
      match !let_fix_entries with
      | Some (c', entries) when c' == c -> entries
      | _ ->
        if args <> [] && not (List.for_all (EConstr.isRel sg) args) then [Array.of_list args] else []
    in
    ( match erased_fix_types env sg ~entries i recd with
    | None ->
      extract_app env sg type_env extracted_ty (extract_fix env sg type_env i recd false) args
    | Some tys ->
      (* The head's type is known before the arguments, so a coercion lands
         on the argument that needs it, as at a constant's call. *)
      let doms, _ = type_decomp tys.(i) in
      let rec split doms args =
        match (doms, args) with
        | d :: doms, _ :: args ->
          let typed, rest = split doms args in
          (d :: typed, rest)
        | _, args -> ([], List.map new_meta args)
      in
      let typed, rest = split doms args in
      let arg_tys = typed @ rest in
      let head = extract_fix ~tys env sg type_env i recd false tys.(i) in
      let () =
        match head with
        | Core.Expr.Fixpoint {occurrence = occ; _} | Core.Expr.Cofixpoint {occurrence = occ; _} ->
          Base.Table.add_erased_fix_group occ
        | _ -> ()
      in
      let applied = type_recomp (arg_tys, extracted_ty) in
      let head = put_magic ~from:tys.(i) ~into:applied head in
      apply_args head (List.map2 (extract_maybe_term env sg type_env) arg_tys args) )
  | CoFix (i, recd) ->
    extract_app env sg type_env extracted_ty (extract_fix env sg type_env i recd true) args
  | Cast (c, _, _) -> extract_term env sg type_env extracted_ty c args
  | Evar _ | Meta _ -> Core.Expr.Axiom_value "evar"
  | Var v ->
    (* Only during Show Extraction *)
    let open Context.Named.Declaration in
    let ty =
      match EConstr.lookup_named v env with
      | LocalAssum (_, ty) -> ty
      | LocalDef (_, _, ty) -> ty
    in
    let vty = extract_type env sg [] 0 ty [] in
    let extract_var extracted_ty =
      put_magic ~from:vty ~into:extracted_ty (Core.Expr.Global (Core.Global_use.monomorphic (GlobRef.VarRef v)))
    in
    extract_app env sg type_env extracted_ty extract_var args
  | Int i ->
    assert (args = []);
    Core.Expr.UInt63 i
  | Float f ->
    assert (args = []);
    Core.Expr.Float64 f
  | String s ->
    assert (args = []);
    (* Unify expected type with Core.Type.String so let-bound string match
       variables get the correct C++ type instead of std::any. *)
    Base.Core_util.try_mgu extracted_ty Core.Type.String;
    Core.Expr.String s
  | Array (_u, t, def, _ty) ->
    assert (args = []);
    let a = new_meta () in
    let core_arr = Array.map (fun c -> extract_term env sg type_env a c []) t in
    let def = extract_term env sg type_env a def [] in
    Core.Expr.Persistent_array {elements = core_arr; default = def}
  | Ind _ | Prod _ | Sort _ -> assert false

(** {2 [extract_maybe_term] is [extract_term] for usual terms, else [Core.Expr.Erased_value]}
*)

(** Extracts a term that might be logical, returning [Core.Expr.Erased_value] if the term is in
    Prop/SProp. *)
and extract_maybe_term env sg type_env extracted_ty c =
  try
    check_default env sg (type_of env sg c);
    extract_term env sg type_env extracted_ty c []
  with NotDefault d -> put_magic ~from:(Core.Type.Erased d) ~into:extracted_ty (Core.Expr.Erased_value d)

(* We first type all arguments starting with unknown meta types. This gives us
   the expected type of the head. Then we use the [mk_head] to produce the Core
   head from this type. *)

(** {2 Generic way to deal with an application} *)

(** Extracts a function application by typing arguments first, then building the
    head.
    @param env Rocq environment for term extraction
    @param sg Evar map for type-of queries
    @param type_env type environment for bound variables
    @param extracted_ty Expected Core type of the whole application
    @param mk_head Function that, given the inferred type of the head, produces the Core head expression
    @param args Rocq argument terms *)
and extract_app env sg type_env extracted_ty mk_head args =
  let metas = List.map new_meta args in
  let type_head = type_recomp (metas, extracted_ty) in
  let extracted_args = List.map2 (extract_maybe_term env sg type_env) metas args in
  apply_args (mk_head type_head) extracted_args

(** {2 Auxiliary function used to extract arguments of constant or constructor}
*)

(** Builds Core argument list from raw arguments, inserting dummies for erased
    positions per signature.
    @param env Rocq environment for type checking
    @param sg Evar map for reduction
    @param e type environment for bound variables
    @param s Type signature
    ([Core.Signature.Argument.Runtime]/[Core.Signature.Argument.Erased] list)
    driving which positions are kept
    @param args Rocq terms to extract (parallel to [typs] and [s])
    @param typs Expected Core types for each argument after unification *)
and make_args env sg e s args typs =
  let rec f = function
    | [], [], _ -> []
    | a :: la, t :: lt, [] -> extract_maybe_term env sg e t a :: f (la, lt, [])
    | a :: la, t :: lt, Core.Signature.Argument.Runtime :: s ->
      extract_maybe_term env sg e t a :: f (la, lt, s)
    | _ :: la, _ :: lt, _ :: s -> f (la, lt, s)
    | _ -> assert false
  in
  f (args, typs, s)

(** What the Rocq argument [a], written at a binder that is one of the
    callee's scheme variables, says the variable's type is -- the source
    evidence an instantiation slot records; [None] where it says nothing
    extraction can read.  [db] translates the caller's own [Rel]s into its
    type variables.

    A type extracts as itself ({!extract_family_type}, which also reads a
    family over values at its body).  Where extraction fails -- a type
    constructor such as [F : Type -> Type] -- two shapes still name something
    C++ can spell:
    {ul
    {- an inductive with no C++ template parameter and no custom spelling,
       whose bare name is a type ([LeftProperty], whose only parameter is a
       value); one with template parameters, a custom one ([option]) or a
       logical one has no bare spelling;}
    {- a [Rel] the caller binds at a type ({!returns_type_sort}: [A : Type],
       [F : Type -> Type]) and numbers as one of its variables.}}
    Anything else -- a proof or value [Rel], an application, a lambda -- says
    nothing. *)
and observe_type_arg env sg db a =
  let extracted =
    try extract_family_type env sg db a with e when CErrors.noncritical e -> None
  in
  match extracted with
  | Some (Core.Type.Erased _) -> None
  | Some t -> Some t
  | None -> (
    match EConstr.kind sg (whd_betaiotazeta env sg a) with
    | Ind ((kn, i), _) ->
      let ind_ref = GlobRef.IndRef (kn, i) in
      let has_cpp_template_params =
        match Base.Table.get_ind_num_param_vars_opt kn with
        | Some n -> n > 0
        | None -> false
      in
      let logical =
        try (extract_ind env kn).packets.(i).logical
        with e when CErrors.noncritical e -> false
      in
      if logical || Base.Table.is_custom ind_ref || has_cpp_template_params then None
      else Some (Core.Type.Global_app {head = ind_ref; type_arguments = []; index_arguments = []})
    | Rel n ->
      let is_type_param =
        try returns_type_sort (Context.Rel.Declaration.get_type (Environ.lookup_rel n env))
        with e when CErrors.noncritical e -> false
      in
      let n' = if is_type_param && n <= List.length db then List.nth db (n - 1) else 0 in
      if n' > 0 then Some (Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = n'}) else None
    | _ -> None )

(** {2 Extraction of a constant applied to arguments} *)

(** The use's instantiation of [schema]: for each variable, the type its
    metavariable in [metas] was solved to, frozen ({!Base.Core_util.freeze_types}), or
    [Identity] for a variable a call within the recursive group keeps [rigid];
    and the argument the call wrote at the variable's binder, if the call
    reaches that binder -- [observed = None] where what was written could not
    be read as a type. *)
and freeze_instantiation schema ~rigid metas written_at =
  let frozen = Array.of_list (freeze_types (Array.to_list metas)) in
  Core.Scheme.Instantiation.make (Core.Schema.id schema) (fun v ->
      let source =
        match (Core.Schema.origin schema v, written_at v) with
        | Some b, Some observed ->
          Core.Scheme.Written {binder = b.Core.Schema.binder; observed = Option.map type_simpl observed}
        | _ -> Core.Scheme.Not_written
      in
      let solution =
        if rigid v then Core.Scheme.Identity
        else Core.Scheme.Type frozen.(Core.Scheme.Var.ordinal v - 1)
      in
      {Core.Scheme.solution; source} )

(** Extracts a constant application (function call), handling type instantiation
    and partial application.
    @param env Rocq environment for schema lookup and argument extraction
    @param sg Evar map for universe and sort operations
    @param type_env type environment for bound variables
    @param extracted_ty Expected Core type of the result; drives magic insertion
    @param kn The constant being applied
    @param args Rocq arguments (may be fewer than the full arity — partial application) *)
and extract_cst_app env sg type_env extracted_ty kn args =
  (* First, the {!Core.Schema} of the constant, in expanded version. *)
  let schema = record_constant_type env sg kn None in
  let schema = Core.Schema.with_body (expand env (Core.Schema.body schema)) schema in
  (* The metas the scheme's type variables are instantiated with, kept so
     that the call's own type arguments can be given to them below. *)
  let tvar_metas = Array.init (Core.Schema.arity schema) (fun _ -> new_meta ()) in
  (* What the call wrote for a scheme variable: the observation of the
     argument at the binder the variable comes from, [Some None] where that
     argument says nothing readable, [None] where the call does not reach the
     binder.  A binder with no variable -- a proof, an erased family, a
     binder over propositions -- is not observed at all. *)
  let db = db_from_rel_context env in
  let observations =
    List.map
      (fun v ->
        ( v,
          Option.bind (Core.Schema.origin schema v) (fun b ->
              Option.map (observe_type_arg env sg db)
                (List.nth_opt args (Core.Scheme.Binder.position b.Core.Schema.binder)) ) ) )
      (Core.Schema.vars schema)
  in
  let written_at v =
    Option.flatten (List.find_map (fun (v', o) -> if Core.Scheme.Var.equal v v' then Some o else None) observations)
  in
  (* The type arguments the Rocq term passes are a statement about the
     scheme's type variables, and the value arguments need not repeat it: a
     monad's [bind] erases its carrier, so [m A] pins nothing, and [A] reaches
     the continuation's binder only from here.  Each is given to the variable
     its binder stands for, where it says something; a variable an argument
     already settled otherwise keeps that answer.

     Only a ground argument is given.  One naming a type variable names it
     the way [observe_type_arg] reads the Rocq context, which need not be the way
     the term around it numbers its own -- a fixpoint's are rigid -- and
     binding a meta to the wrong one plants a mismatch that surfaces later as
     a coercion. *)
  let given =
    let rec informative = function
      | Core.Type.Erased _
      | Core.Type.Unknown
      | Core.Type.Axiom
      | Core.Type.Variable_app _
      | Core.Type.Variable _
      | Core.Type.Hole _ -> false
      | Core.Type.Meta {contents = None} | Core.Type.Open _ -> false
      | Core.Type.Arrow {parameter = a; result = b} -> informative a && informative b
      | Core.Type.Global_app {type_arguments = l; _} -> List.for_all informative l
      | Core.Type.Meta {contents = Some u} -> informative u
      | Core.Type.String -> true
    in
    Array.of_list
      (List.map
         (fun v ->
           match written_at v with
           | Some (Some t) when lang () == Cpp && informative t -> Some t
           | _ -> None )
         (Core.Schema.vars schema) )
  in
  let given v = given.(Core.Scheme.Var.ordinal v - 1) in
  (* Can we instantiate the type variables of this constant?  Not inside the
     definition of its own recursive group, which is extracted at the group's
     rigid variables: a member's variable there is the caller's own, unless
     the call writes a ground type for it -- [g bool] inside [f] is [g] at
     [bool], whatever [f]'s variables are -- and then it is instantiated like
     any other constant's. *)
  let in_group =
    lang () == Cpp
    && List.exists (fun c -> QConstant.equal env kn c) !current_fixpoints
  in
  let rigid v = in_group && Option.is_empty (given v) in
  let instantiated =
    (* This is the version of the type that is instantiated (shocker) *)
    if in_group then
      rigidify
        (type_subst_fun
           (fun j ->
             match Core.Scheme.Var.of_tvar (Core.Schema.id schema) j with
             | Some v when not (rigid v) -> Some tvar_metas.(j - 1)
             | _ -> None )
           (Core.Widen.type_ (Core.Schema.body schema)) )
    else type_subst_vect tvar_metas (Core.Widen.type_ (Core.Schema.body schema))
  in
  (* Then the expected type of this constant. *)
  let a = new_meta () in
  (* We compare stored and expected types in two steps. *)
  (* First, can [kn] be applied to all args ? *)
  let metas = List.map new_meta args in
  let magic1 = needs_magic (type_recomp (metas, a), instantiated) in
  (* Second, is the resulting type compatible with the expected type [extracted_ty] ? *)
  let magic2 = needs_magic (a, extracted_ty) in
  (* Now, the extraction of the arguments. *)
  let s_full = type2signature env (Core.Schema.body schema) in
  let s_full = sign_with_implicits (GlobRef.ConstRef kn) s_full 0 in
  let s = sign_no_final_keeps s_full in
  let ls = List.length s in
  let la = List.length args in
  List.iter
    (fun v ->
      match given v with
      | Some t -> try_mgu tvar_metas.(Core.Scheme.Var.ordinal v - 1) (expand env t)
      | None -> () )
    (Core.Schema.vars schema);
  let arg_terms = make_args env sg type_env s args metas in
  (* The arguments are extracted, so the local unification is over: what it
     solved the scheme's variables to is frozen into the use, a variable it
     left open becoming a hole rather than a metavariable some later pass
     could bind to whatever it meets. *)
  let instantiation = freeze_instantiation schema ~rigid tvar_metas written_at in
  (* The internal head receives a magic if [magic1] *)
  let head =
    put_magic_if
      ~from:(type_recomp (metas, a))
      ~into:instantiated
      magic1
      (Core.Expr.Global (Core.Global_use.polymorphic (GlobRef.ConstRef kn) instantiation))
  in
  (* For strict languages, purely logical signatures lead to a dummy lam (except
     when [Core.Signature.Argument.Erased Core.Erasure_reason.Type_argument]
     everywhere). So a [Core.Expr.Erased_value] is left accordingly. *)
  let optdummy =
    match sign_kind s_full with
    | UnsafeLogicalSig -> [Core.Expr.Erased_value Core.Erasure_reason.Proof]
    | _ -> []
  in
  (* Different situations depending of the number of arguments: *)
  if la >= ls then
    (* Enough args, cleanup already done in [arg_terms], we only add the additional
       dummy if needed. *)
    put_magic_if ~from:a ~into:extracted_ty (magic2 && not magic1)
      (apply_args head (optdummy @ arg_terms))
  else
    (* Partially applied function with some logical arg missing. We complete via
       eta and expunge logical args. *)
    let ls' = ls - la in
    let s' = List.skipn la s in
    (* Recover resolved argument types from the instantiated+unified constant
       type so that eta-expansion lambdas get proper types instead of Core.Type.Axiom. *)
    let all_arg_types = List.map type_simpl (fst (type_decomp instantiated)) in
    let missing_types = List.lastn ls' all_arg_types in
    let arg_terms = List.map (ast_lift ls') arg_terms @ eta_args_sign ls' s' in
    let e = anonym_or_dummy_lams_typed (apply_args head arg_terms) missing_types s' in
    put_magic_if ~from:a ~into:extracted_ty magic2
      (remove_n_lams (List.length optdummy) e)

(* \begin{itemize} \item In Core, constructor arguments are uncurryfied. \item We
   managed to suppress logical parts inside inductive definitions, but they must
   appears outside (for partial applications for instance) \item We also
   suppressed all Rocq parameters to the inductives, since they are fixed, and
   thus are not used for the computation. \end{itemize} *)

(** {2 Extraction of an inductive constructor applied to arguments} *)

(** Extracts a constructor application, handling uncurrying, logical parameter
    suppression, and partial application.
    @param env Rocq environment for inductive lookup and argument extraction
    @param sg Evar map for sort and type operations
    @param type_env type environment for bound variables
    @param extracted_ty Expected Core type of the result; drives magic insertion
    @param cp Constructor path [((kn, i), j)] — mutual inductive [kn], packet [i], constructor [j]
    @param args Rocq arguments, including inductive type parameters *)
and extract_cons_app env sg type_env extracted_ty ((((kn, i) as ip), j) as cp) args =
  (* First, we build the type of the constructor, stored in small pieces. *)
  let mi = extract_ind env kn in
  let params_nb = mi.parameter_count in
  let oi = mi.packets.(i) in
  (* Use signature to count type vars for constructor result type, not type_variables.
     For promoted dependent records, type_variables includes promoted type variables
     (from carrier : Type fields) that are NOT parameters of the inductive type
     itself. Using signature avoids including them in the result type's type arg
     list, preventing mgu mismatches. *)
  let nb_tvars = List.length (List.filter (fun x -> x == Core.Signature.Argument.Runtime) oi.signature)
  and types = List.map (fun t -> expand env (Core.Widen.type_ t)) oi.constructor_argument_types.(j - 1) in
  let list_tvar = List.map (fun i -> Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic;
                                                         variable = i}) (List.interval 1 nb_tvars) in
  let type_cons =
    type_recomp (types, Core.Type.Global_app {head = GlobRef.IndRef ip;
                                              type_arguments = list_tvar;
                                              index_arguments = []})
  in
  let type_cons = instantiate_prenex nb_tvars type_cons in
  (* Then, the usual variables [s], [ls], [la], ... *)
  let s = List.map (type2sign env) types in
  let s = sign_with_implicits (GlobRef.ConstructRef cp) s params_nb in
  let ls = List.length s in
  let la = List.length args in
  assert (la <= ls + params_nb);
  let la' = max 0 (la - params_nb) in
  let args' = List.lastn la' args in
  (* Now, we build the expected type of the constructor *)
  let metas = List.map new_meta args' in
  (* If stored and expected types differ, then magic! *)
  let a = new_meta () in
  (* For the C++ backend, capture the calling context's arrow-arity BEFORE
     unification mutates the metas in [extracted_ty]. After [needs_magic], [extracted_ty]'s metas
     will be resolved to the constructor's full type, losing the distinction
     between "A -> B" (context sees 1-arg function returning B) and "A -> B ->
     C" (context sees 2-arg function). We need this to detect when to generate
     curried (nested) lambdas for partial application. *)
  let context_arity_before_unify =
    if lang () == Cpp then
      (* Count only the "structural" arrows in [extracted_ty] — the arrows that the
         calling context explicitly placed. We follow the outermost meta chain
         to find the root type, but then count only arrows whose codomains are
         DIRECTLY Core.Type.Arrow nodes (not metas resolving to Core.Type.Arrow). This prevents
         counting arrows inside resolved type variables. Example: map's function
         slot is Core.Type.Arrow(v1, v2) where v2 is a fresh meta variable that was later
         resolved to Core.Type.Arrow(list, list). We should report 1 (1 structural arrow),
         not 2, because the caller sees this as a 1-arg function returning an
         opaque type B. *)
      let rec deref_meta = function
        | Core.Type.Meta {contents = Some t} -> deref_meta t
        | t -> t
      in
      let rec count = function
        | Core.Type.Arrow {result = b; _} ->
          (* Only count deeper arrows if [b] is directly a Core.Type.Arrow, not a meta that
             resolves to Core.Type.Arrow. A meta in codomain position indicates a type
             variable (like B in A -> B) that should be treated as opaque even
             if it was later resolved to a function type. *)
          ( match b with
          | Core.Type.Arrow _ -> 1 + count b
          | _ -> 1 )
        | _ -> 0
      in
      count (deref_meta extracted_ty)
    else
      0
  in
  let magic1 = needs_magic (type_cons, type_recomp (metas, a)) in
  let magic2 = needs_magic (a, extracted_ty) in
  (* For C++: register any still-None type-param metas with their erased Rocq
     type ({!pending_cpp_meta_fills}).
     After the whole constant is extracted, metas that are STILL None will be
     filled — those represent genuinely erased type positions (e.g. nil inside a
     lambda whose return type is a dependent/erased type like sem_ty TagList).
     Metas that get resolved later (like sigma_types' list element = nat) will
     have contents ≠ None and will be skipped. *)
  let () =
    if lang () == Cpp then begin
      let la_now = List.length args in
      if params_nb > 0 && la_now >= params_nb then begin
        let db = db_from_rel_context env in
        let param_args = List.firstn params_nb args in
        let n_sign = List.length oi.signature in
        let param_sign = List.firstn (min params_nb n_sign) oi.signature in
        let result_metas =
          match snd (type_decomp type_cons) with
          | Core.Type.Global_app {type_arguments = l; index_arguments = []; _} -> Array.of_list l
          | _ -> [||]
        in
        let tvar_idx = ref 0 in
        List.iter2
          (fun sign_entry coq_arg ->
            ( match sign_entry with
            | Core.Signature.Argument.Runtime ->
              let idx = !tvar_idx in
              incr tvar_idx;
              if idx < Array.length result_metas then
                ( match result_metas.(idx) with
                | Core.Type.Meta r when r.contents = None ->
                  ( try
                      let ty = extract_type env sg db 0 coq_arg [] in
                      ( match type_simpl ty with
                      (* A type variable is not an erased position: left open,
                         it generalises with the term that names it -- [B] in
                         [fun (B : Type) (x : B) => [x]], a binding of its own. *)
                      | Core.Type.Unknown | Core.Type.Erased _ | Core.Type.Variable _ -> ()
                      | concrete ->
                        let rec erase_leaves = function
                          | Core.Type.Global_app {type_arguments = []; _} ->
                            Core.Type.Erased Core.Erasure_reason.Type_argument
                          | Core.Type.Global_app {head = g; type_arguments = args; index_arguments = ns} ->
                            Core.Type.Global_app {head = g;
                                                  type_arguments = List.map erase_leaves args;
                                                  index_arguments = ns}
                          | Core.Type.Arrow {parameter = a; result = b} ->
                            Core.Type.Arrow {parameter = erase_leaves a; result = erase_leaves b}
                          | _ -> Core.Type.Erased Core.Erasure_reason.Type_argument
                        in
                        pending_cpp_meta_fills :=
                          (r, erase_leaves concrete) :: !pending_cpp_meta_fills )
                    with e when best_effort_failure e -> () )
                | _ -> () )
            | Core.Signature.Argument.Erased _ -> () ))
          param_sign param_args
      end
    end
  in
  let head arg_terms =
    let typeargs =
      match snd (type_decomp type_cons) with
      | Core.Type.Global_app {type_arguments = l; index_arguments = []; _} -> List.map type_simpl l
      | _ -> assert false
    in
    (* For promoted dependent records/type classes: extract concrete types for
       the erased Type constructor args and add them to typeargs. This gives
       instance structs access to the concrete carrier types. Example: mkMagma
       nat Nat.add → typeargs = [Core.Type.Global_app(nat)] Example: Build_DirectedGraph
       Directed A (DirectedEdge A) ... → typeargs = [Directed A, A, DirectedEdge
       A] *)
    let promoted_typeargs =
      let nb_sign_keeps =
        List.length (List.filter (fun x -> x == Core.Signature.Argument.Runtime) oi.signature)
      in
      let has_promoted = List.length oi.type_variables > nb_sign_keeps in
      if lang () == Cpp && has_promoted then
        (* type_variables has more entries than signature Keep count means there are
           promoted type variables from erased Type fields. Extract concrete
           types from the erased constructor args. *)
        let db = db_from_rel_context env in
        let la' = max 0 (la - params_nb) in
        let args' = List.lastn la' args in
        let rec extract_promoted s_rem args_rem acc =
          match (s_rem, args_rem) with
          | [], _ | _, [] -> List.rev acc
          | Core.Signature.Argument.Erased Core.Erasure_reason.Type_argument :: s_rest, a :: a_rest ->
            let ty =
              (* A promoted type field whose argument does not extract is
                 erased, which is the honest answer; a critical exception
                 (an interrupt, an anomaly) is not an erasure and must not
                 be turned into one. *)
              try extract_type env sg db 0 a []
              with e when type_extraction_declined e -> Core.Type.Erased Core.Erasure_reason.Type_argument
            in
            extract_promoted s_rest a_rest (ty :: acc)
          | _ :: s_rest, _ :: a_rest -> extract_promoted s_rest a_rest acc
        in
        extract_promoted s args' []
      else
        []
    in
    (* Append promoted typeargs AFTER existing typeargs so that Core.Type.Variable indices
       match: e.g., Core.Type.Variable 1 = G, Core.Type.Variable 2 = A (from signature), Core.Type.Variable 3 = edge
       (promoted), and type_args = [Directed A, A, DirectedEdge A]. *)
    let all_typeargs = typeargs @ promoted_typeargs in
    let typ = Core.Type.Global_app {head = GlobRef.IndRef ip; type_arguments = all_typeargs; index_arguments = []} in
    put_magic_if
      ~from:type_cons
      ~into:(type_recomp (metas, a))
      magic1
      (Core.Expr.Construct {result_type = typ;
                            constructor = GlobRef.ConstructRef cp;
                            arguments = arg_terms;
                            occurrence = Core.Occurrence.fresh ()})
  in
  (* Decompose the instantiated+unified constructor type to recover the resolved
     argument types. After [instantiate_prenex] replaced Tvars with metas, and
     [needs_magic] unified those metas with the expected types, [type_simpl]
     chases the meta chains to get concrete types. These are used by
     [anonym_or_dummy_lams_typed] so that partially applied constructors get
     proper types in their eta-expansion lambdas instead of [Core.Type.Axiom]. *)
  let resolved_arg_types = List.map type_simpl (fst (type_decomp type_cons)) in
  (* Different situations depending of the number of arguments: *)
  if la < params_nb then
    let head' = head (eta_args_sign ls s) in
    put_magic_if
      ~from:a
      ~into:extracted_ty
      magic2
      (dummy_lams
         (anonym_or_dummy_lams_typed head' resolved_arg_types s)
         (params_nb - la) )
  else
    let arg_terms = make_args env sg type_env s args' metas in
    if Int.equal la (ls + params_nb) then
      put_magic_if ~from:a ~into:extracted_ty (magic2 && not magic1) (head arg_terms)
    else (* [ params_nb <= la <= ls + params_nb ] *)
      let ls' = params_nb + ls - la in
      let s' = List.lastn ls' s in
      (* Get the types for the missing (eta-expanded) args: the last ls' entries
         of the resolved constructor argument types. *)
      let missing_types = List.lastn ls' resolved_arg_types in
      let arg_terms = List.map (ast_lift ls') arg_terms @ eta_args_sign ls' s' in
      (* For the C++ backend, check if the calling context expects fewer
         arguments than the full eta-expansion provides. This happens when a
         constructor like [cons : A -> list A -> list A] is used in a context
         that expects [A -> (list A -> list A)] — i.e., a 1-arg function
         returning a function. In Core, these are identical (curried), but in C++
         they are different: a 2-arg lambda vs a 1-arg lambda returning a
         lambda. We detect this by comparing the arrow-arity of the context type
         [extracted_ty] with the number of eta-expanded args [ls'], and split the lambda
         wrapping accordingly so that the C++ translation produces properly
         nested lambdas. *)
      if
        lang () == Cpp
        && context_arity_before_unify > 0
        && context_arity_before_unify < ls'
      then
        (* Split: outer lambda has [context_arity_before_unify] params, inner
           lambda has the rest. The inner lambda captures the outer params and
           applies the constructor with all args. We wrap the inner lambda in
           [Core.Expr.Lambda_group_barrier (_, _)] so that {!Base.Core_util.collect_lams} stops at the
           outer lambda boundary: it only collects consecutive [Core.Expr.Lambda] nodes.
           [Core.Expr.Lambda_group_barrier] carries no coercion, so the C++ translation renders the
           inner lambda as the return value of the outer lambda. *)
        let ca = context_arity_before_unify in
        let outer_s = List.firstn ca s' in
        let inner_s = List.skipn ca s' in
        let outer_types = List.firstn ca missing_types in
        let inner_types = List.skipn ca missing_types in
        let inner = anonym_or_dummy_lams_typed (head arg_terms) inner_types inner_s in
        let inner_barrier = Core.Expr.Lambda_group_barrier {value = inner; occurrence = Core.Occurrence.fresh ()} in
        put_magic_if
          ~from:a
          ~into:extracted_ty
          magic2
          (anonym_or_dummy_lams_typed inner_barrier outer_types outer_s)
      else
        put_magic_if
          ~from:a
          ~into:extracted_ty
          magic2
          (anonym_or_dummy_lams_typed (head arg_terms) missing_types s')

(** {1 Extraction of a case} *)

(** Extracts a match/case expression, handling logical singleton elimination and
    branch extraction.
    @param env Rocq environment for inductive lookup and branch extraction
    @param sg Evar map for type-of and sort queries
    @param type_env type environment for bound variables
    @param ip Inductive name and packet index being matched
    @param c The scrutinee term
    @param br Array of branch bodies (in functional form, one per constructor)
    @param extracted_ty Expected Core type of the whole case expression *)
and extract_case env sg type_env (((kn, i) as ip), c, br) extracted_ty =
  (* [br]: bodies of each branch (in functional form) *)
  (* [ni]: number of arguments without parameters in each branch *)
  let ni = constructors_nrealargs env ip in
  let br_size = Array.length br in
  assert (Int.equal (Array.length ni) br_size);
  if Int.equal br_size 0 then (
    add_recursors env kn;
    (* May have passed unseen if logical ... *)
    Core.Expr.Runtime_error "absurd case" )
  else (* [c] has an inductive type, and is not a type scheme type. *)
    let t = type_of env sg c in
    (* The only non-informative case: [c] is of sort [Prop]/[SProp] *)
    if info_of_quality (sort_of env sg t) == Logic then (
      add_recursors env kn;
      (* May have passed unseen if logical ... *)
      (* Logical singleton case: *)
      (* [match c with C i j k -> t] becomes [t'] *)
      assert (Int.equal br_size 1);
      let s = iterate (fun l -> Core.Signature.Argument.Erased Core.Erasure_reason.Proof :: l) ni.(0) [] in
      let extracted_ty = iterate (fun t -> Core.Type.Arrow {parameter = Core.Type.Erased Core.Erasure_reason.Proof;
                                                   result = t}) ni.(0) extracted_ty in
      let e = extract_maybe_term env sg type_env extracted_ty br.(0) in
      snd (case_expunge s e) )
    else
      let mi = extract_ind env kn in
      let oi = mi.packets.(i) in
      (* Use signature (not type_variables) to count type vars for the head type. For
         promoted dependent records, type_variables includes promoted type variables
         from carrier : Type fields, but the inductive type itself has no type
         parameters. Using signature avoids creating a Core.Type.Global_app with too many type
         args, preventing mgu mismatches. *)
      let nb_sign_vars =
        List.length (List.filter (fun x -> x == Core.Signature.Argument.Runtime) oi.signature)
      in
      let metas = Array.init nb_sign_vars new_meta in
      (* The extraction of the head. *)
      let type_head = Core.Type.Global_app {head = GlobRef.IndRef ip;
                                            type_arguments = Array.to_list metas;
                                            index_arguments = []} in
      let a = extract_term env sg type_env type_head c [] in
      let has_unresolved_meta =
        Array.exists (fun m -> match m with
          | Core.Type.Meta {contents = None} -> true
          | _ -> false) metas
      in
      ( if has_unresolved_meta then try
          let coq_ty = whd_all env sg (Retyping.get_type_of env sg c) in
          match EConstr.kind sg coq_ty with
          | App (hd, args) ->
            let kept_args =
              let rec filter_keep sign args =
                match sign, args with
                | Core.Signature.Argument.Runtime :: s, a :: aa -> a :: filter_keep s aa
                | _ :: s, _ :: aa -> filter_keep s aa
                | _ -> []
              in
              filter_keep oi.signature (Array.to_list args)
            in
            List.iter2 (fun meta coq_arg ->
              match meta with
              | Core.Type.Meta ({contents = None} as r) ->
                let core_ty =
                  (* Leaving the meta unresolved is the fallback, so a
                     failure to extract this argument is recoverable; a
                     critical exception is not. *)
                  try extract_type env sg [] 0 coq_arg []
                  with e when type_extraction_declined e -> Core.Type.Unknown
                in
                let rec has_unknown = function
                  | Core.Type.Unknown -> true
                  | Core.Type.Meta {contents = None} -> true
                  | Core.Type.Meta {contents = Some t} -> has_unknown t
                  | Core.Type.Global_app {type_arguments = args; _} -> List.exists has_unknown args
                  | Core.Type.Arrow {parameter = a; result = b} -> has_unknown a || has_unknown b
                  | _ -> false
                in
                if not (has_unknown core_ty) then
                  Core.Extracted.Meta.solve r core_ty
              | _ -> ()
            ) (Array.to_list metas) kept_args
          | _ -> ()
        with e when type_extraction_declined e -> () );
      (* The extraction of each branch. *)
      let extract_branch i =
        let r = GlobRef.ConstructRef (ip, i + 1) in
        (* The types of the arguments of the corresponding constructor. *)
        let f t = type_subst_vect metas (expand env (Core.Widen.type_ t)) in
        let l = List.map f oi.constructor_argument_types.(i) in
        (* the corresponding signature *)
        let s = List.map (type2sign env) oi.constructor_argument_types.(i) in
        let s = sign_with_implicits r s mi.parameter_count in
        (* Extraction of the branch (in functional form). *)
        let e = extract_maybe_term env sg type_env (type_recomp (l, extracted_ty)) br.(i) in
        (* We suppress dummy arguments according to signature. *)
        let ids, e = case_expunge s e in
        {Core.Match.Branch.binders = List.rev ids;
         result_type = extracted_ty;
         pattern = Core.Pattern.binding_all r (List.length ids);
         body = e}
      in
      (* Apply standard case extraction for all inductives. *)
      let typs = List.map type_simpl (Array.to_list metas) in
      let typ = Core.Type.Global_app {head = GlobRef.IndRef ip; type_arguments = typs; index_arguments = []} in
      Core.Expr.Match {scrutinee_type = typ;
                       scrutinee = a;
                       branches = Array.init br_size extract_branch;
                       occurrence = Core.Occurrence.fresh ()}

(** {2 Extraction of a (co)-fixpoint} *)

(** Extracts a single component of a (co-)fixpoint group into a Core fix expression.
    @param env Rocq environment (extended with recursive binders inside)
    @param sg Evar map for type-of queries
    @param type_env type environment for outer bound variables
    @param i Index of the main fixpoint component to extract (the one whose type unifies with [extracted_ty])
    @param recd The raw recursive declaration: binder names [fi], types [ti], bodies [ci]
    @param is_cofix [true] for a cofixpoint, [false] for a regular fixpoint
    @param extracted_ty Expected Core type of fixpoint component [i]
    @param tys The members' types, when {!erased_fix_types} gives them *)
and extract_fix ?tys env sg type_env i ((fi, ti, ci) as recd) is_cofix extracted_ty =
  let env = push_rec_types recd env in
  let metas =
    match tys with
    | Some tys -> Array.copy tys
    | None ->
      let metas = Array.map new_meta fi in
      metas.(i) <- extracted_ty;
      metas
  in
  let type_env = Array.fold_left Type_env.push_type type_env metas in
  let ei = Array.map2 (extract_maybe_term env sg type_env) metas ci in
  let ids = Array.mapi (fun i x -> (id_of_name x.binder_name, metas.(i))) fi in
  let group = Core.Recursion.Group.of_arrays ~selected:i ids ei (Core.Occurrence.fresh ()) in
  if is_cofix then Core.Expr.Cofixpoint group else Core.Expr.Fixpoint group

(** {1 Core declarations} *)

(* [decomp_lams_eta env c t] finds the number [n] of products in the type [t],
   and decompose the term [c] in [n] lambdas, with eta-expansion if needed. *)

(** Decomposes lambdas with eta-expansion to reach [n] binders, given [m]
    existing lambdas.
    @param n Total number of binders required (from the type [t])
    @param m Number of lambdas already present in [c]
    @param env Rocq environment used to decompose the product type [t]
    @param sg Evar map for [whd_decompose_prod_n]
    @param c The term to decompose and possibly eta-expand
    @param t The product type of [c], used to supply the missing binder types *)
let decomp_lams_eta_n n m env sg c t =
  let rels = fst (whd_decompose_prod_n env sg n t) in
  let rels', c = EConstr.decompose_lambda sg c in
  let d = n - m in
  (* we'd better keep rels' as long as possible. *)
  let rels = List.firstn d rels @ rels' in
  let eta_args = List.rev_map EConstr.mkRel (List.interval 1 d) in
  (rels, applistc (EConstr.Vars.lift d c) eta_args)

(* Let's try to identify some situation where extracted code will allow
   generalisation of type variables *)

(** Checks if a type variable can be generalized in the extracted code. *)
let rec gentypvar_ok sg c =
  match EConstr.kind sg c with
  | Lambda _ | Const _ -> true
  | App (c, v) ->
    (* if all arguments are variables, these variables will disappear after
       extraction (see [empty_s] below) *)
    Array.for_all (EConstr.isRel sg) v && gentypvar_ok sg c
  | Cast (c, _, _) -> gentypvar_ok sg c
  | _ -> false

(** {2 From a constant to a Core declaration} *)

(** The identity on [t]; the count of type variables is ignored.  Type
    variables are not prefixed to the type as arrows (the commented-out body
    shows that alternative). *)
let add_tvars _n t =
  t (* if n <= 1 then t else Core.Type.Arrow (Core.Type.Variable (n-1), add_tvars (n-1) t) *)

(** Removes erased type arguments from a type scheme. *)
let type_expunge env t = type_expunge (constant_body_at env) t

(** Removes erased arguments from a type using an explicit signature. *)
and type_expunge_from_sign env s t = type_expunge_from_sign (constant_body_at env) s t

(* Sigma type precondition detection. For functions taking {x : A | P x}, detect
   P and translate to C++ assertions. *)

(** Tests whether a global reference [gr] corresponds to the Rocq library
    reference with the given name. *)
let is_ref name gr =
  try globref_equal gr (Rocqlib.lib_ref name)
  with e when best_effort_failure e -> false

(* Check if a term's head is a specific global reference *)
let head_is_ref sg name t =
  let hd = fst (EConstr.decompose_app sg t) in
  match EConstr.kind sg hd with
  | Ind (ind, _) -> is_ref name (GlobRef.IndRef ind)
  | Const (c, _) -> is_ref name (GlobRef.ConstRef c)
  | _ -> false

(* Try to extract a Peano natural number from a term. Returns Some n for
   S(S(...O)) terms, None otherwise. *)
let rec try_peano_nat env sg t =
  match EConstr.kind sg (whd_all env sg t) with
  | Construct ((ind, _), _)
    when is_ref "num.nat.O" (GlobRef.ConstructRef (ind, 1)) -> Some 0
  | App (hd, args) when Array.length args = 1 ->
    ( match EConstr.kind sg hd with
    | Construct ((ind, _), _)
      when is_ref "num.nat.O" (GlobRef.ConstructRef (ind, 1)) ->
      (* Confirmed this is a nat constructor; with 1 arg it must be S *)
      Option.map (fun n -> n + 1) (try_peano_nat env sg args.(0))
    | _ -> None )
  | _ -> None

(* Translate a predicate body (under a lambda binder) to a C++ assertion
   template. body has Rel 1 bound to the witness variable. Returns AssertExpr or
   AssertComment. *)

(** Translates assertion predicates into C++ assertion format strings for sigma
    type preconditions.
    @param env Rocq environment with the sigma witness variable bound as [Rel 1]
    @param sg Evar map for reduction and pretty-printing
    @param body The predicate body under a lambda (witness is [Rel 1])
    @return An [AssertExpr] with a [%N] format string, or [AssertComment] for unrecognized patterns *)
let translate_predicate_body env sg body =
  let open Base.Table in
  let body = whd_all env sg body in
  match EConstr.kind sg body with
  (* Pattern: @eq T x y -> False ~~> neq *)
  | Prod (_, eq_app, conclusion)
    when head_is_ref sg "core.False.type" (whd_all env sg conclusion) ->
    let eq_app = whd_all env sg eq_app in
    ( match EConstr.kind sg eq_app with
    | App (hd, args)
      when head_is_ref sg "core.eq.type" eq_app && Array.length args = 3 ->
      let lhs = args.(1)
      and rhs = args.(2) in
      ( match (EConstr.kind sg lhs, EConstr.kind sg rhs) with
      | Rel 1, Construct ((ind, _), _)
        when is_ref "num.nat.O" (GlobRef.ConstructRef (ind, 1)) ->
        AssertExpr "%0 != 0"
      | Rel 1, Rel n -> AssertExpr (Printf.sprintf "%%0 != %%%d" (n - 1))
      | Rel n, Rel 1 -> AssertExpr (Printf.sprintf "%%%d != %%0" (n - 1))
      | _ ->
        AssertComment
          (Printf.sprintf
             "%s != %s"
             (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg lhs))
             (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg rhs)) ) )
    | _ ->
      AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))
    )
  (* Pattern: @eq T x y ~~> eq *)
  | App (hd, args)
    when head_is_ref sg "core.eq.type" body && Array.length args = 3 ->
    let lhs = args.(1)
    and rhs = args.(2) in
    ( match (EConstr.kind sg lhs, EConstr.kind sg rhs) with
    | Rel 1, Construct ((ind, _), _)
      when is_ref "num.nat.O" (GlobRef.ConstructRef (ind, 1)) ->
      AssertExpr "%0 == 0"
    | Rel 1, Rel 1 -> AssertComment "x = x" (* tautology, skip assert *)
    | Rel 1, Rel n -> AssertExpr (Printf.sprintf "%%0 == %%%d" (n - 1))
    | _ ->
      AssertComment
        (Printf.sprintf
           "%s == %s"
           (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg lhs))
           (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg rhs)) ) )
  (* Pattern: le n m ~~> n <= m *)
  | App (hd, args)
    when head_is_ref sg "num.nat.le" body && Array.length args >= 2 ->
    let lhs = args.(0)
    and rhs = args.(1) in
    ( match (EConstr.kind sg lhs, EConstr.kind sg rhs) with
    | Construct ((ind, _), _), Rel 1
      when is_ref "num.nat.O" (GlobRef.ConstructRef (ind, 1)) ->
      AssertComment "0 <= n" (* tautology for nat *)
    | Rel 1, Rel n -> AssertExpr (Printf.sprintf "%%0 <= %%%d" (n - 1))
    | Rel n, Rel 1 -> AssertExpr (Printf.sprintf "%%%d <= %%0" (n - 1))
    | _, Rel 1 ->
      ( match try_peano_nat env sg lhs with
      | Some n_val -> AssertExpr (Printf.sprintf "%%0 >= %d" n_val)
      | None ->
        AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))
      )
    | Rel 1, _ ->
      ( match try_peano_nat env sg rhs with
      | Some n_val -> AssertExpr (Printf.sprintf "%%0 <= %d" n_val)
      | None ->
        AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))
      )
    | _ ->
      AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))
    )
  (* Pattern: lt n m = le (S n) m ~~> n < m *)
  | App (hd, args)
    when head_is_ref sg "num.nat.lt" body && Array.length args >= 2 ->
    let lhs = args.(0)
    and rhs = args.(1) in
    ( match (EConstr.kind sg lhs, EConstr.kind sg rhs) with
    | Construct ((ind, _), _), Rel 1
      when is_ref "num.nat.O" (GlobRef.ConstructRef (ind, 1)) ->
      AssertExpr "%0 > 0"
    | Rel 1, Rel n -> AssertExpr (Printf.sprintf "%%0 < %%%d" (n - 1))
    | Rel n, Rel 1 -> AssertExpr (Printf.sprintf "%%%d < %%0" (n - 1))
    | _, Rel 1 ->
      ( match try_peano_nat env sg lhs with
      | Some n_val -> AssertExpr (Printf.sprintf "%%0 > %d" n_val)
      | None ->
        AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))
      )
    | Rel 1, _ ->
      ( match try_peano_nat env sg rhs with
      | Some n_val -> AssertExpr (Printf.sprintf "%%0 < %d" n_val)
      | None ->
        AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))
      )
    | _ ->
      AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))
    )
  (* Fallback: emit as comment *)
  | _ ->
    AssertComment (Pp.string_of_ppcmds (Printer.pr_econstr_env env sg body))

(* Walk a function type, detect sigma-typed parameters, and register assertions.
   info_idx counts the parameters that survive as values -- matching C++ param
   indices -- not the types, which become template parameters, nor the
   proofs, nor the parameters declared implicit; [position] counts every
   product, as implicit positions do. *)

(** Detects sigma type assertions (dependent pair projections) in function
    parameters and registers them.
    @param env Rocq environment, extended with each parameter binder as the walk proceeds
    @param sg Evar map for reduction and predicate body translation
    @param kn Constant name of the function being analyzed (used as key in [Base.Table.add_sigma_assertion])
    @param typ The full Rocq type of [kn]; sigma-typed parameters are detected in the products *)
let detect_sigma_assertions env sg kn typ =
  let func_ref = GlobRef.ConstRef kn in
  (* A parameter declared implicit is no C++ parameter ({!sign_with_implicits}),
     whatever its type. *)
  let implicits = implicits_of_global func_ref in
  let rec walk env position info_idx typ =
    match EConstr.kind sg (whd_all env sg typ) with
    | Prod (n, t, d) ->
      let t_whnf = whd_all env sg t in
      let kept = not (Int.Set.mem position implicits) in
      (* Check if t is @sig A P — check regardless of is_info since sig is
         sometimes classified as non-informative due to its Prop component *)
      ( match EConstr.kind sg t_whnf with
      | App (hd, args)
        when kept && head_is_ref sg "core.sig.type" t_whnf && Array.length args >= 2 ->
        let pred = args.(1) in
        (* P : A -> Prop *)
        let pred_whnf = whd_all env sg pred in
        ( match EConstr.kind sg pred_whnf with
        | Lambda (x, x_ty, body) ->
          let env' =
            EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, x_ty)) env
          in
          let assertion = translate_predicate_body env' sg body in
          Base.Table.add_sigma_assertion func_ref info_idx assertion
        | _ ->
          let s = Pp.string_of_ppcmds (Printer.pr_econstr_env env sg pred) in
          Base.Table.add_sigma_assertion func_ref info_idx (Base.Table.AssertComment s) )
      | _ -> () );
      (* sig types may be classified as non-informative but still kept as
         params *)
      let is_sig_type = head_is_ref sg "core.sig.type" t_whnf in
      let next_info =
        if kept && (is_default env sg t || is_sig_type) then info_idx + 1 else info_idx
      in
      walk (push_rel_assum (n, t) env) (position + 1) next_info d
    | _ -> ()
  in
  walk env 1 0 typ

(** Extracts a standard (non-record) constant definition, handling lambda
    decomposition and type expunging.
    @param env Rocq environment for type and term extraction
    @param sg Evar map for sort and type-of queries
    @param kn The constant name (used for schema caching and implicit lookup)
    @param body The definition body as an [EConstr.t] (pre-substituted for mutual fixpoints)
    @param typ The Rocq type of the constant
    @return A pair [(Core.Expr.t, Core.Type.t)] of the extracted term and its Core type *)
let extract_std_constant env sg kn body typ =
  reset_meta_count ();
  pending_cpp_meta_fills := [];
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let schema = record_constant_type env sg kn (Some typ) in
  let numtvars = Core.Schema.arity schema and t = Core.Widen.type_ (Core.Schema.body schema) in
  (* Detect sigma type preconditions and register assertions *)
  (try detect_sigma_assertions env sg kn typ with e when best_effort_failure e -> ());
  (* An instance of a singleton class keeps its class's type, but its body is
     the class's method, and is extracted at the method's type: unfolded at
     the class in [typ], the method's own [forall]s are type variables the
     body's annotations can name, where the class spelling erases them. *)
  let singleton = Base.Table.singleton_instance_class ~env (GlobRef.ConstRef kn) <> None in
  let typ_body, t_body =
    if not singleton then (typ, t)
    else
      let ctx, concl = EConstr.decompose_prod_decls sg typ in
      let concl = Reductionops.whd_all (EConstr.push_rel_context ctx env) sg concl in
      let typ' = EConstr.it_mkProd_or_LetIn concl ctx in
      (typ', extract_type env sg [] 1 typ' [])
  in
  (* The real type [t']: without head products, expanded, *)
  (* and with its own type variables made rigid (not instantiable). *)
  let l, t' = type_decomp (expand env (rigidify t_body)) in
  let s = List.map (type2sign env) l in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits (GlobRef.ConstRef kn) s 0 in
  (* Decomposing the top level lambdas of [body]. If there isn't enough, it's
     ok, as long as remaining args aren't to be pruned (and initial lambdas
     aren't to be all removed if the target language is strict). In other
     situations, eta-expansions create artificially enough lams (but that may
     break user's clever let-ins and partial applications). *)
  let rels, c =
    let n = List.length s
    and m = nb_lam sg body in
    if n <= m then
      decompose_lambda_n sg n body
    else
      let s, s' = List.chop m s in
      if List.for_all (( == ) Core.Signature.Argument.Runtime) s' && sign_kind s != UnsafeLogicalSig then
        decompose_lambda_n sg m body
      else
        decomp_lams_eta_n n m env sg body typ_body
  in
  (* Should we do one eta-expansion to avoid non-generalizable '_a ? *)
  let rels, c =
    let n = List.length rels in
    let s, s' = List.chop n s in
    let k = sign_kind s in
    let empty_s = k == EmptySig || k == SafeLogicalSig in
    if
      empty_s
      && (not (gentypvar_ok sg c))
      && (not (List.is_empty s'))
      && not (Int.equal (type_maxvar t_body) 0)
    then
      decomp_lams_eta_n (n + 1) n env sg body typ_body
    else
      (rels, c)
  in
  let n = List.length rels in
  let s = List.firstn n s in
  let l, l' = List.chop n l in
  let t' = type_recomp (l', t') in
  (* The initial type environment. *)
  let type_env = List.fold_left Type_env.push_std_type Type_env.empty l in
  (* The lambdas names. *)
  let ids = List.map (fun (n, _) -> Core.Binder_name.Source (id_of_name n.binder_name)) rels in
  (* The according Rocq environment. *)
  let env = push_rels_assum rels env in
  (* The real extraction: *)
  let e = extract_term env sg type_env t' c [] in
  (* For C++: fill any type-param metas that remained unresolved after full extraction.
     These represent genuinely erased type positions (e.g. the element type of nil
     inside a lambda whose return type is a dependent/erased type). *)
  if lang () == Cpp then
    List.iter
      (fun ((r : Core.Extracted.Meta.t), erased) ->
        if r.contents = None then Core.Extracted.Meta.solve r erased)
      !pending_cpp_meta_fills;
  pending_cpp_meta_fills := [];
  (* Expunging term and type from dummy lambdas. *)
  let trm = term_expunge s (List.combine ids (List.rev l), e) in
  (* Only the arrows the short type writes are expunged from it. *)
  let s =
    if not singleton then s
    else
      let rec arrows = function
        | Core.Type.Arrow {result = b; _} -> 1 + arrows b
        | Core.Type.Meta {contents = Some t} -> arrows t
        | _ -> 0
      in
      List.firstn (min (arrows t) (List.length s)) s
  in
  (trm, add_tvars numtvars (type_expunge_from_sign env s t))

(* Extracts the type of an axiom, honors the Extraction Implicit declaration. *)

(** Extracts an axiom declaration, honoring the Extraction Implicit declaration.
    @param env Rocq environment for schema recording and expansion
    @param sg Evar map for sort and type-of queries
    @param kn The axiom constant name
    @param typ The Rocq type of the axiom
    @return The Core type of the axiom, with erased arguments removed *)
let extract_axiom env sg kn typ =
  reset_meta_count ();
  (* The short type [t] (i.e. possibly with abbreviations). *)
  let t = Core.Widen.type_ (Core.Schema.body (record_constant_type env sg kn (Some typ))) in
  (* The real type [t']: without head products, expanded, *)
  (* and with its own type variables made rigid (not instantiable). *)
  let l, _ = type_decomp (expand env (rigidify t)) in
  let s = List.map (type2sign env) l in
  (* Check for user-declared implicit information *)
  let s = sign_with_implicits (GlobRef.ConstRef kn) s 0 in
  type_expunge_from_sign env s t

(** Extracts a fixpoint (recursive function) definition, handling mutual
    recursion.
    @param env Rocq environment for sort checking and term extraction
    @param sg Evar map for [fresh_global] and sort operations
    @param vkn Array of constant names for each mutually recursive function
    @param is_fix [true] for a regular fixpoint, [false] for a cofixpoint
    @param fi, ti, ci Binder names, types, and bodies of the fixpoint group *)
let extract_fixpoint env sg vkn is_fix (fi, ti, ci) =
  let n = Array.length vkn in
  let types = Array.make n (Core.Type.Erased Core.Erasure_reason.Proof)
  and terms = Array.make n (Core.Expr.Erased_value Core.Erasure_reason.Proof) in
  let kns = Array.to_list vkn in
  (* for replacing recursive calls [Rel ..] by the corresponding [Const]: *)
  let sg, sub =
    CList.fold_left_map
      (fun sg con -> Evd.fresh_global env sg (ConstRef con))
      sg
      (List.rev kns)
  in
  current_fixpoints := kns;
  Fun.protect ~finally:(fun () -> current_fixpoints := []) (fun () ->
  for i = 0 to n - 1 do
    if info_of_quality (sort_of env sg ti.(i)) != Logic then
      try
        let e, t =
          extract_std_constant
            env
            sg
            vkn.(i)
            (EConstr.Vars.substl sub ci.(i))
            ti.(i)
        in
        terms.(i) <- e;
        types.(i) <- t
      with SingletonInductiveBecomesProp ind ->
        error_singleton_become_prop ind
  done);
  (* Register CoFixpoints. is_fix=true means regular fixpoint, is_fix=false
     means cofixpoint *)
  if not is_fix then
    Array.iter (fun kn -> add_cofixpoint (GlobRef.ConstRef kn)) vkn;
  (* [vkn] names the bodies of a kernel (co)fixpoint, of which there is at
     least one. *)
  Core.Decl.Recursive_group
    (Core.Nonempty.of_list_exn
       (List.init n (fun i ->
            {Core.Recursion.Definition.entity = GlobRef.ConstRef vkn.(i); body = terms.(i); type_ = types.(i)} )))

(** Main entry point for extracting a constant declaration, dispatching on its
    {!flag} and on its body (symbol, primitive or axiom, transparent
    definition, primitive projection, opaque definition). *)
let extract_constant access env kn cb =
  let sg = Evd.from_env env in
  let r = GlobRef.ConstRef kn in
  let typ = EConstr.of_constr cb.const_type in
  let warn_info () = if not (is_any_custom r) then add_info_axiom r in
  let warn_log () = if not (constant_has_body cb) then add_log_axiom r in
  let mk_typ_ax () =
    let n = type_scheme_nb_args env sg typ in
    let ids = iterate (fun l -> anonymous_name :: l) n [] in
    Core.Decl.Type_alias {entity = r; parameters = ids; body = Core.Type.Axiom}
  in
  let mk_typ c =
    let s, vl = type_sign_vl env sg typ in
    let db = db_from_sign s in
    let t = extract_type_scheme env sg db c (List.length s) in
    let is_logical =
      try fst (flag_of_type env sg c) == Logic
      with Retyping.RetypeError _ -> false
    in
    if is_logical then Core.Decl.Type_alias {entity = r;
                                             parameters = vl;
                                             body = Core.Type.Erased Core.Erasure_reason.Type_argument}
    else begin
      (match t with
       | Core.Type.Unknown | Core.Type.Axiom -> add_erased_type_const r
       | _ -> ());
      Base.Table.add_type_scheme_arity r (List.length vl);
      (* An alias body is where a type-level [Definition] under a [Context]
         writes its dependence on that context; see
         {!Base.Table.add_type_alias_body}. *)
      Base.Table.add_type_alias_body r (Core.Freezer.type_ (Core.Freezer.create ()) t);
      Core.Decl.Type_alias {entity = r; parameters = vl; body = t}
    end
  in
  let mk_ax () =
    let t = extract_axiom env sg kn typ in
    (* If all arguments of this axiom are dummy (Prop/SProp), the function can
       never be called with real values — treat it as logical. *)
    let rec all_args_dummy = function
      | Core.Type.Arrow {parameter = t1; result = t2} ->
        if is_erased_type t1 then
          all_args_dummy t2
        else
          false
      | t -> is_erased_type t (* only erase if return type is also dummy *)
    in
    let has_args =
      match t with
      | Core.Type.Arrow _ -> true
      | _ -> false
    in
    if has_args && all_args_dummy t then
      Core.Decl.Value {entity = r;
                       body = Core.Expr.Erased_value Core.Erasure_reason.Proof;
                       type_ = Core.Type.Erased Core.Erasure_reason.Proof}
    else (
      Core.Decl.Value {entity = r; body = Core.Expr.Axiom_value (Constant.to_string kn); type_ = t} )
  in
  (* An instance's class arguments are where its erased names come from.
     [PIV : @PI ProvenanceV PointerV] declares no type of its own: [ptr]
     belongs to [PointerV] and [prov] to [ProvenanceV], and neither reaches the
     Core type, which records the class alone.  This is the last point at which
     the connection is written down, so it is recorded here rather than
     rediscovered; see {!Base.Table.add_instance_class_shape}.

     No [is_typeclass] test: the tables it would consult are filled as
     extraction proceeds, and the reader runs after all of it. *)
  let record_class_shape () =
    let class_arg = class_arg_shape env sg in
    (* The shape an applied type writes, if its head is one a reader can name.

       A type-level [Definition] is such a head for the same reason an
       inductive is: [packed : @dbox natIPtr] is where the alias is applied to
       the instance its body depends on.  Whether the head is an alias is not
       asked here -- extraction reaches declarations before their types, so the
       alias body may not be recorded yet; a head that turns out to have no
       class arguments resolves nothing, which is what it did when it was not
       recorded at all. *)
    let shape_of t =
      let hd, args = EConstr.decompose_app sg t in
      let head_ref =
        match EConstr.kind sg hd with
        | Ind (ind, _) -> Some (GlobRef.IndRef ind)
        | Const (c, _) -> Some (GlobRef.ConstRef c)
        | _ -> None
      in
      match head_ref with
      | None -> None
      | Some head_ref ->
        let shapes =
          List.map
            (fun x ->
              match class_arg x with
              | Some sh -> Some sh
              | None ->
                (* A {e type} argument is not a class argument and never
                   resolves anything; all it owes the reader is its position.
                   [@ToDvalueBase natParams nat] has an inductive at the second
                   position, which [class_arg] cannot name, and refusing the
                   whole shape for it also threw away the [natParams] beside
                   it -- the only thing that says which [ptr] the instance
                   means.  An argument that is not a type is different: it is
                   one the reader would have had to spell, so all-or-none
                   still applies there. *)
                if
                  EConstr.Vars.closed0 sg x
                  && (try is_info_scheme env sg (type_of env sg x)
                      with e when best_effort_failure e -> false)
                then Some Base.Table.Carg_unknown
                else None )
            (List.filter
               (arg_survives_extraction env sg)
               (Array.to_list args) )
        in
        if List.for_all Option.has_some shapes then
          Some (head_ref, List.map Option.get shapes)
        else None
    in
    (* The instance need not be applied at the conclusion's head.  [w0 :=
       @wrap (@ParamsV natIPtr)] has type [dval -> option (list dval)]: the
       head is an arrow, and under it the applied type sits inside [list],
       inside [option].  A declaration whose type mentions an instance anywhere
       is a declaration whose reader can spell it, so the whole type is
       searched -- outermost first, so the conclusion's own head still wins,
       and the first applied type that says something about a class is
       kept. *)
    let rec search t =
      match shape_of t with
      | Some ((_, _ :: _) as sh) -> Some sh
      | _ ->
        EConstr.fold sg
          (fun acc sub -> match acc with Some _ -> acc | None -> search sub)
          None t
    in
    let _, concl = EConstr.decompose_prod sg typ in
    match search typ with
    | Some sh -> Base.Table.add_instance_class_shape r sh
    | None -> (
      (* Nothing in the type applies a class.  The conclusion's head is still
         worth recording: what it reaches through its own payloads
         ({!Base.Table.get_type_class_args}) is read from the head alone. *)
      match shape_of concl with
      | Some sh -> Base.Table.add_instance_class_shape r sh
      | None -> () )
  in
  (* The instances the type applies to the declaration's own class binders --
     [get_size : forall {Pa : Params}, @memM Pa (@MemStateV Pa) nat].  [memM]
     reaches the Core type without its dictionary arguments, and a body that
     only forwards to another declaration names no instance, so nothing
     downstream says which instance [memM]'s [state] belongs to; see
     {!Base.Table.add_context_instance_apps}.  A binder is given by its ordinal
     among the informative class-typed ones, the ones that become the
     declaration's [_tcI] template parameters. *)
  let record_context_instance_apps () =
    let prods, concl = EConstr.decompose_prod sg typ in
    let outer_first = List.rev prods in
    let ordinals, _, _ =
      List.fold_left
        (fun (ords, k, env) (x, t) ->
          let is_class =
            ( match EConstr.kind sg (fst (EConstr.decompose_app sg t)) with
            | Const (c, _) -> Typeclasses.is_class (GlobRef.ConstRef c)
            | Ind (i, _) -> Typeclasses.is_class (GlobRef.IndRef i)
            | _ -> false )
            && (try is_default env sg t with e when best_effort_failure e -> false)
          in
          ( ords @ [(if is_class then Some k else None)],
            (if is_class then k + 1 else k),
            push_rel_assum (x, t) env ) )
        ([], 0, env) outer_first
    in
    let found = ref [] in
    (* [m] of the declaration's binders are in scope, and [depth] binders of
       the type's own above them. *)
    let rec search m depth t =
      let h, args = EConstr.decompose_app sg t in
      ( match EConstr.kind sg h with
      | Const (c, _) when Array.length args > 0 ->
        let ordinal a =
          match EConstr.kind sg a with
          | Rel i when i > depth && i - depth <= m ->
            List.nth ordinals (m - (i - depth))
          | _ -> None
        in
        let os = List.map ordinal (Array.to_list args) in
        if List.for_all Option.has_some os then
          let app = (GlobRef.ConstRef c, List.map Option.get os) in
          if not (List.mem app !found) then found := !found @ [app]
      | _ -> () );
      EConstr.iter_with_binders sg succ (search m) depth t
    in
    List.iteri (fun p (_, t) -> search p 0 t) outer_first;
    search (List.length outer_first) 0 concl;
    if !found <> [] then Base.Table.add_context_instance_apps r !found
  in
  let mk_def c =
    record_class_shape ();
    record_context_instance_apps ();
    let e, t = extract_std_constant env sg kn c typ in
    (* [record_constant_type] registered the {i short} type, the one still
       spelled with the abbreviations the user wrote.  Where the body's binders
       reach past an abbreviation standing in the codomain -- an instance of a
       one-method class, say, whose class is a synonym for a function type --
       [extract_std_constant] unfolds it, and the declaration is emitted with
       the parameters that uncovers.  A call site reads the registered type to
       work out how many arguments the declaration takes, so when the two
       disagree on that count the unfolded type is the one to keep. *)
    ( match Base.Table.find_extracted_type r with
    | exception Not_found -> ()
    | short ->
      if
        List.length (Base.Type_util.core_value_domains short)
        < List.length (Base.Type_util.core_value_domains t)
      then register_glob_def r t );
    Core.Decl.Value {entity = r; body = e; type_ = t}
  in
  try
    match flag_of_type env sg typ with
    | Logic, TypeScheme ->
      warn_log ();
      let s, vl = type_sign_vl env sg typ in
      Core.Decl.Type_alias {entity = r; parameters = vl; body = Core.Type.Erased Core.Erasure_reason.Type_argument}
    | Logic, Default ->
      warn_log ();
      Core.Decl.Value {entity = r;
                       body = Core.Expr.Erased_value Core.Erasure_reason.Proof;
                       type_ = Core.Type.Erased Core.Erasure_reason.Proof}
    | Info, TypeScheme ->
      ( match cb.const_body with
      | Symbol _ ->
        add_symbol r;
        mk_typ_ax ()
      | Primitive _ | Undef _ ->
        warn_info ();
        mk_typ_ax ()
      | Def c ->
        ( match Structures.PrimitiveProjections.find_opt kn with
        | None -> mk_typ (get_body c)
        | Some p ->
          let body = fake_match_projection env p in
          mk_typ (EConstr.of_constr body) )
      | OpaqueDef c ->
        add_opaque r;
        if access_opaque () then
          mk_typ (get_opaque access env c)
        else
          mk_typ_ax () )
    | Info, Default ->
    match cb.const_body with
    | Symbol _ ->
      add_symbol r;
      mk_ax ()
    | Primitive _ | Undef _ ->
      warn_info ();
      mk_ax ()
    | Def c ->
      ( match Structures.PrimitiveProjections.find_opt kn with
      | None -> mk_def (get_body c)
      | Some p ->
        let body = fake_match_projection env p in
        mk_def (EConstr.of_constr body) )
    | OpaqueDef c ->
      add_opaque r;
      if access_opaque () then
        mk_def (get_opaque access env c)
      else
        mk_ax ()
  with SingletonInductiveBecomesProp ind -> error_singleton_become_prop ind

(** Extracts the specification (type signature) of a constant for module
    signatures. *)
let extract_constant_spec env kn cb =
  let sg = Evd.from_env env in
  let r = GlobRef.ConstRef kn in
  let typ = EConstr.of_constr cb.const_type in
  try
    match flag_of_type env sg typ with
    | Logic, TypeScheme ->
      let s, vl = type_sign_vl env sg typ in
      Core.Signature.Declaration.Type {entity = r;
                                       parameters = vl;
                                       body = Some (Core.Type.Erased Core.Erasure_reason.Type_argument)}
    | Logic, Default ->
      Core.Signature.Declaration.Value
        {entity = r; body = Core.Expr.Axiom_value "SVAL extraction issue";
          type_ = Core.Type.Erased Core.Erasure_reason.Proof}
    | Info, TypeScheme ->
      let s, vl = type_sign_vl env sg typ in
      (* A type scheme with more signature slots than type variables takes at
         least one VALUE argument (e.g. [sym_semty : sym -> Type], [s=[Core.Signature.Argument.Erased]],
         [vl=[]]).  Such a family applied to a runtime value is not
         representable as a C++ type; record it so that C++ type conversion
         ([convert_core_type_to_cpp_type]) erases it to [std::any] at use sites
         instead of emitting [typename M::sym_semty] and needing a runtime
         [any_cast] guard.  A family with a body is that only if the body says
         so, as a declaration's does ({!extract_constant}): [EvenT n := {m |
         n = 2 * m}] mentions its value only in a proof, and is [Sig<nat>]. *)
      let value_dep = List.length s > List.length vl in
      ( match cb.const_body with
      | Undef _ | OpaqueDef _ | Primitive _ | Symbol _ ->
        if value_dep then Base.Table.add_value_dep_type_scheme r;
        Core.Signature.Declaration.Type {entity = r; parameters = vl; body = None}
      | Def body ->
        let db = db_from_sign s in
        let body = get_body body in
        let t = extract_type_scheme env sg db body (List.length s) in
        ( match t with
        | (Core.Type.Unknown | Core.Type.Axiom) when value_dep -> Base.Table.add_value_dep_type_scheme r
        | _ -> () );
        Core.Signature.Declaration.Type {entity = r; parameters = vl; body = Some t} )
    | Info, Default ->
      let t = Core.Widen.type_ (Core.Schema.body (record_constant_type env sg kn (Some typ))) in
      let mk_spec c =
        let e, ty = extract_std_constant env sg kn c typ in
        Core.Signature.Declaration.Value {entity = r; body = e; type_ = ty}
      in
      ( match cb.const_body with
      | Def c ->
        ( match Structures.PrimitiveProjections.find_opt kn with
        | None -> mk_spec (get_body c)
        | Some p ->
          let body = fake_match_projection env p in
          mk_spec (EConstr.of_constr body) )
      | _ ->
        Core.Signature.Declaration.Value
          {entity = r; body = Core.Expr.Axiom_value "SVAL extraction issue"; type_ = type_expunge env t} )
  with SingletonInductiveBecomesProp ind -> error_singleton_become_prop ind

(** Extracts a module-level "with type" constraint. *)
let extract_with_type env sg c =
  try
    let typ = type_of env sg c in
    match flag_of_type env sg typ with
    | Info, TypeScheme ->
      let s, vl = type_sign_vl env sg typ in
      let db = db_from_sign s in
      let t = extract_type_scheme env sg db c (List.length s) in
      Some (vl, t)
    | _ -> None
  with SingletonInductiveBecomesProp ind -> error_singleton_become_prop ind

(** Extracts a single term with its Core type, for [Crane Show Extraction]; see
    {!Extract_env.show_extraction}. *)
let extract_constr env sg c =
  reset_meta_count ();
  try
    let typ = type_of env sg c in
    match flag_of_type env sg typ with
    | _, TypeScheme ->
      (Core.Expr.Erased_value Core.Erasure_reason.Type_argument, Core.Type.Erased Core.Erasure_reason.Type_argument)
    | Logic, _ -> (Core.Expr.Erased_value Core.Erasure_reason.Proof, Core.Type.Erased Core.Erasure_reason.Proof)
    | Info, Default ->
      let extracted_ty = extract_type env sg [] 1 typ [] in
      (extract_term env sg Type_env.empty extracted_ty c [], extracted_ty)
  with SingletonInductiveBecomesProp ind -> error_singleton_become_prop ind

(** Main entry point for extracting an inductive type definition, filtering
    dummy types and implicits. *)
let extract_inductive env kn =
  let ind = extract_ind env kn in
  add_recursors env kn;
  let f i j l =
    let implicits =
      implicits_of_global (GlobRef.ConstructRef ((kn, i), j + 1))
    in
    let rec filter i = function
      | [] -> []
      | t :: l ->
        let l' = filter (succ i) l in
        if is_erased_type (expand env t) || Int.Set.mem i implicits then
          l'
        else
          t :: l'
    in
    filter (1 + ind.parameter_count) l
  in
  let packets =
    Array.mapi
      (fun i (p : Core.Inductive.Packet.t) ->
        {p with Core.Inductive.Packet.constructor_argument_types = Array.mapi (f i) p.constructor_argument_types})
      ind.packets
  in
  {ind with Core.Inductive.packets = packets}

(** {2 Is a [Core.Decl.t] logical ?} *)

let logical_decl = function
  | Core.Decl.Value {body = Core.Expr.Erased_value _; type_ = Core.Type.Erased _; _} -> true
  | Core.Decl.Type_alias {body = Core.Type.Erased _; _} -> true
  | Core.Decl.Recursive_group fds ->
    Core.Nonempty.for_all
      (fun (fd : Core.Recursion.Definition.extracted) -> is_erased_value fd.body && is_erased_type fd.type_) fds
  | Core.Decl.Inductive {definition = (i : Core.Inductive.t); _} ->
    Array.for_all (fun (ip : Core.Inductive.Packet.t) -> ip.logical) i.packets
  | _ -> false

(** {2 Is a [Core.Signature.Declaration.t] logical ?} *)

let logical_spec = function
  | Core.Signature.Declaration.Type {body = Some (Core.Type.Erased _); _} -> true
  | Core.Signature.Declaration.Value {type_ = Core.Type.Erased _; _} -> true
  | Core.Signature.Declaration.Inductive {definition = (i : Core.Inductive.t); _} ->
    Array.for_all (fun (ip : Core.Inductive.Packet.t) -> ip.logical) i.packets
  | _ -> false
