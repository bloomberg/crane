(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Type conversion for translation: Core types to C++ types
    ({!cpp_ir_of_core_type}, {!cpp_of_core}), promoted type variables, the
    template arguments and parameter lists built from Core types, and
    typedef unfolding.  Reaches expression generation only through
    {!type_term_arg}. *)

open Base.Common
open Names
open Base.Core_util
open Base.Table
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query

(** [promoted_var_binding var_id] -- what the scope says the promoted variable
    named [var_id] stands for, by name.  Reached from a globref through
    {!promoted_var_resolution}, and by name alone where only the name survives
    -- see {!Base.Table.ind_promoted_params}. *)
let promoted_var_binding cx var_id =
  let r = Option.map snd
    (List.find_opt
       (fun (n, _) -> Id.equal n var_id)
       cx.ctx.lexical.promoted_var_map ) in
  r

(** [ind_promoted_type_args g] -- the leading template arguments a mention of
    the type [g] passes for the promoted variables its definition names.  [g]
    is an inductive, whose payloads name them, or a type-level [Definition],
    whose body does.

    Such a variable is a type the definition does not own: it belongs to
    whichever instance was in scope where it was declared, so it is a
    parameter there (see {!Base.Table.promoted_type_params} and its uses in
    [Emit.Entities] and [Lower_decl.gen_type_alias]) and an argument at every use.  Inside the inductive's own
    declaration the argument is that parameter, which is what the [Tpromoted]
    fallback spells; a scope that knows no instance spells the file-scope
    alias, as it did before there was a parameter at all. *)
let ind_promoted_type_args cx g : Cpp_ir.Lowered.Type.t list =
  List.map
    (fun v ->
      match promoted_var_binding cx v with
      | Some t -> t
      | None -> Promoted_member v )
    (Base.Table.promoted_type_params g)

(** [convert_core_type_to_cpp_type] only resolves [Core.Type.Variable] indices within
    [tvars]; anything out of range comes back as [Core.Type.Variable (Tv_index (_, None))], which
    prints as a bogus, undeclared template parameter name (e.g. "T3").
    Normalize those to [Topaque]: the variable was quantified somewhere we
    cannot see, so [std::any] is the only spelling available, but nothing here
    establishes that the value is actually boxed. *)
let rec erase_unresolved_tvars : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Variable (Index (_, None)) -> Obligation Opaque_type
  | Entity_application (g, ts, es) -> Entity_application (g, List.map erase_unresolved_tvars ts, es)
  | Function (dom, cod) ->
    Function (List.map erase_unresolved_tvars dom, erase_unresolved_tvars cod)
  | Shared_pointer t -> Shared_pointer (erase_unresolved_tvars t)
  | Reference (k, t) -> Reference (k, erase_unresolved_tvars t)
  | t -> t

(** [names_only_scoped_tvars ty] -- whether every type variable [ty] spells is
    one this scope declares.  A slot type read off a callee's signature is
    written in the callee's type variables, which name nothing here, so such a
    type cannot be used as the type a use site wants. *)
let names_only_scoped_tvars cx ty =
  let scope = current_scope_type_names cx in
  List.for_all (fun id -> List.exists (Id.equal id) scope) (get_tvars ty)

(** [ty], where this scope can write it: every variable it names is in scope,
    and it is not erased. *)
let spell_in_scope cx ty =
  if names_only_scoped_tvars cx ty && not (Cpp_ir.Types.prints_as_any ty) then Some ty else None

(** [promoted_var_resolution g] -- what the promoted type variable [g] stands
    for here, if the scope says.  A promoted variable is a class's [Type]
    field, and the type that mentions one records the field alone, never the
    instance it belongs to; the enclosing scope is what supplies that, through
    [promoted_var_map].  A variable the scope does not answer has no spelling
    here, which is a different thing from having an erased one. *)
let promoted_var_resolution cx g =
  match Base.Table.promoted_type_var_name g with
  | Some var_id -> promoted_var_binding cx var_id
  | None -> None

(** Whether [ty] names a class field the current scope does not resolve, so
    that it would print through the field's file-scope [std::any] alias: a
    type read off another declaration, whose own instance resolved it. *)
let mentions_unresolved_promoted cx (ty : Cpp_ir.Lowered.Type.t) =
  Cpp_ir.Types.exists
    (fun (t : Cpp_ir.Lowered.Type.t) ->
      match t with
      | Promoted_member v -> promoted_var_binding cx v = None
      | Entity_application (g, _, _) -> Base.Table.is_promoted_type_var g && promoted_var_resolution cx g = None
      | _ -> false )
    ty

(** How a term argument of a custom type is generated: by {!gen_expr_typed}, which
    fills this in once it is defined.  The one place type conversion calls
    back into expression generation -- a mapped type applied to a term, as a
    fixed-size array is to its length -- so it is the edge the two are
    separated at. *)
let type_term_arg : (Lowering_state.t -> env -> Core.Expr.t -> Cpp_ir.Lowered.Expr.t) ref =
  ref (fun _ _ _ -> CErrors.anomaly (Pp.str "Lower_expr.type_term_arg: unset"))

(** Whether a function whose Core result is [t2], converted to [c], returns
    C++ [void]: [c] is the unit type, or [t2] is unit under a sequential
    monad ({!Monadic.core_type_is_void_call}).  Every function type's codomain
    is decided here, so a body generated against a function's result reads
    the same answer its signature does. *)
let result_is_void (t2 : Core.Type.t) (c : Cpp_ir.Lowered.Type.t) =
  is_cpp_unit_type c || Monadic.core_type_is_void_call t2

(** [cpp_ir_of_core_type env ~ns tvars t] is the C++ type of the Core type [t],
    a variable named as [tvars] names it; [ns] are the inductives whose
    recursive occurrences, at a constructor's storage, are held behind a
    pointer. *)
let rec cpp_ir_of_core_type cx
    env
    ?(ns : Core.Ref.User.Set.t = Core.Ref.User.Set.empty)
    (tvars : Id.t list)
    (core_t : Core.Type.t) : Cpp_ir.Lowered.Type.t =
  (* [ns] is the only source of recursive-storage wrapping.  Most callers
     omit it (defaulting to empty), so types like [List<tree>] stay value
     shaped in function signatures.  Struct-field storage conversion passes the
     owning inductive in [ns], so non-coinductive recursive occurrences at
     constructor storage sites become [shared_ptr]. *)
  match core_t with
  | Core.Type.Arrow {parameter = t1; result = t2} ->
    (* std::function<F(A)> is already a value type and provides the heap
       indirection needed to break recursive layout cycles.  Always pass an
       empty [ns] for domain and codomain so that recursive self-references
       inside function types stay as value types instead of being wrapped in
       shared_ptr.  The outer field-position wrapping (shared_ptr for direct
       self-ref fields) is handled at the call site, not here. *)
    let t1c = cpp_ir_of_core_type cx env tvars t1 in
    (* Reify monadic domain types: itree E R in parameter position becomes
       shared_ptr<ITree<R>> so the tree can be passed as a value. *)
    let t1c = Monadic.reify_monadic_param_type cx t1 t1c in
    let t2c = cpp_ir_of_core_type cx env tvars t2 in
    (* Skip erased params: is_erased_type catches direct Core.Type.Erased, is_cpp_dummy_type
       catches Core.Type.Erased wrapped in Core.Type.Meta (e.g.,
       Core.Type.Meta{contents=Some(Core.Type.Erased Core.Erasure_reason.Proof)}
       which converts to dummy_prop glob). Do NOT use prints_as_any here as it
       also catches Tany (std::any), which is a valid type for universally
       quantified parameters — stripping it would incorrectly collapse (A -> IO)
       into just IO. *)
    if erased_by_extraction t1 || match t1c with Erased _ -> true | _ -> false then
      t2c
    else (
      (* Void-ify unit codomain: function types returning [unit] (directly
         or via monadic wrapper like [itree E unit]) should map to [void]
         to match void-ified function definitions. Check the Core type [t2]
         since the C++ type may still be a monad Core.Type.Global_app, not bare unit. *)
      let voidify_cod (c : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
        if result_is_void t2 c then Void else c
      in
      (* A result the arguments only pin down as a type index is not something
         a template parameter can stand for; erase it. *)
      let voidify_cod c : Cpp_ir.Lowered.Type.t =
        if result_is_index_only_tvar core_t then Any else voidify_cod c
      in
      match
        t2c
      with
      | Function (l, t) -> Function (t1c :: l, voidify_cod t)
      | _ -> Function (t1c :: [], voidify_cod t2c) )
  | Core.Type.Global_app {head = g; _} when is_void g -> Void
  (* PROMOTED TYPE VARIABLES: Handle references to record fields that were
     "promoted" from value-level fields to type-level parameters.

     A "promoted" field is a Type-valued record field (e.g., [m_carrier : Type]
     in [Record Monoid]) that became a C++ concept type requirement instead of
     a struct field. At usage sites, references to these fields must be treated
     as TYPES, not values.

     Example:
       Coq: [mfold (M : Monoid) (l : list (m_carrier M))]
            Here [m_carrier M] is a TYPE (the carrier type of the monoid M)

       C++: [template <Monoid _tcI0> ... List<typename _tcI0::m_carrier> ...]
            Must qualify as a type, not access as a field: NOT _tcI0->m_carrier

     Three contexts for promoted type vars:
     1. Inside template functions with typeclass params: [promoted_var_map] is
        populated, resolve to qualified types like [typename _tcI0::m_carrier]
     2. Module-level (constructor expressions): Use module aliases ([std::any])
     3. No context: Mark with [Tpromoted] for later resolution *)
  | Core.Type.Global_app {head = g; type_arguments = ts; _} when Base.Table.is_promoted_type_var g ->
    ( match Base.Table.promoted_type_var_name g with
    | Some var_id ->
      ( match promoted_var_resolution cx g with
      | Some resolved -> resolved
      | None ->
        (* No resolution found.  When the constructor-expression flag is set,
           all promoted vars become [Tany] (= std::any) because module-level
           type aliases are always std::any and non-Type promoted vars (like
           [base_category]) have no alias at all.  Otherwise keep the marker
           for concept generation and signature printing. *)
        if cx.ctx.lexical.in_constructor_expr then Any
        else Promoted_member var_id )
    | None -> Any )
  | Core.Type.Global_app {head = g; _} when Base.Table.is_value_dep_type_scheme g ->
    (* Value-dependent type scheme (e.g. [sym_semty : sym -> Type]) applied to a
       runtime value — not representable as a C++ type, so erase to [std::any].
       This keeps erasure consistent: such values are already stored as
       [std::any], so the types that mention them are [std::any] too, and no
       [any_cast] guard is needed at use sites. *)
    Any
  | Core.Type.Global_app {head = g; type_arguments = ts; index_arguments = args} when is_custom g ->
    Entity_application
      ( g,
        List.map (cpp_ir_of_core_type cx env ~ns tvars) ts,
        (* A typed mapping spells its type from the type arguments alone
           ({!Base.Mapping_plan.cpp_type}): the term arguments, among them
           the erased one holding each type argument's place, are none of
           its type, and two spellings of one type differ in them only
           where one was annotated without them. *)
        if Base.Mapping_plan.is_type_head g then [] else List.map (fun a -> !type_term_arg cx env a) args )
  | Core.Type.Global_app {head = g; type_arguments = ts; _} ->
    (* For inductives, only keep type args that correspond to parameters (not
       indices). Parameters become template params in C++; indices are
       erased. *)
    let filtered_ts =
      match g with
      | GlobRef.IndRef (kn, _) ->
        (* Filter type args to keep only parameters (not indices). Use
           get_ind_num_param_vars_opt to determine how many to keep. For
           local/self-references with non-empty tvars, we can use tvars length
           as a fallback, but prefer the table lookup for accuracy. *)
        ( match Base.Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars ->
          (* Only keep the first num_param_vars type args - the rest are
             indices *)
          safe_firstn num_param_vars ts
        | None ->
          (* Fallback: if tvars is non-empty and this is a local reference, use
             tvars length *)
          let is_local = Core.Ref.User.Set.mem g ns || spells_bare cx g in
          if is_local && tvars <> [] then
            safe_firstn (List.length tvars) ts
          else
            ts )
        (* Keep all if we can't determine *)
      | _ -> ts
    in
    (* Only propagate ns into type arguments when g itself is a self-ref.
       For non-self types (e.g. list inside tree's definition), type args
       stay bare — the field-level wrapping handles the cycle-breaking.
       This ensures type variables are never shared_ptr-wrapped at instantiation. *)
    let ns_for_args =
      if Core.Ref.User.Set.mem g ns then ns else Core.Ref.User.Set.empty
    in
    let converted_ts =
      List.map (cpp_ir_of_core_type cx env ~ns:ns_for_args tvars) filtered_ts
    in
    let converted_ts =
      match g with
      (* Only where a later parameter's type mentions an earlier one --
         [sigT A (P : A -> Type)] -- does erasing the earlier one erase the
         later.  An erased family ([tree void1 R], [void1] logical) is
         nothing [R] depends on. *)
      | GlobRef.IndRef _ when Base.Table.has_dependent_params g ->
        let rec first_ktype_idx i = function
          | [] -> max_int
          | (Core.Type.Erased Core.Erasure_reason.Type_argument
          | Core.Type.Meta {contents = Some (Core.Type.Erased Core.Erasure_reason.Type_argument)}) :: _ -> i
          | _ :: rest -> first_ktype_idx (i + 1) rest
        in
        let cutoff = first_ktype_idx 0 filtered_ts in
        if cutoff < max_int then
          List.mapi
            (fun i t -> if i > cutoff then index_erase_type t else t)
            converted_ts
        else
          converted_ts
      | _ -> converted_ts
    in
    let converted_ts = Tvars.apply_hkt_tyctors cx g converted_ts in
    let converted_ts = ind_promoted_type_args cx g @ converted_ts in
    let core : Cpp_ir.Lowered.Type.t = Entity_application (g, converted_ts, []) in
    ( match g with
    | GlobRef.IndRef _ ->
      (* Enum inductives are value types - no shared_ptr wrapping *)
      if is_enum_inductive g then
        let is_local = Core.Ref.User.Set.mem g ns || spells_bare cx g in
        if is_local then
          core
        else
          In_namespace (g, core)
      else
        (* Check if this inductive is in the explicit ns list or in
           local_inductives context *)
        let is_self_ref = Core.Ref.User.Set.mem g ns in
        (* Check if g is a mutual sibling: shares the same MutInd.t KerName
           as any member of ns, but at a different index. Mutual siblings
           need shared_ptr because their types are incomplete (forward-declared). *)
        let is_mutual_sibling =
          (not is_self_ref) &&
          match g with
          | GlobRef.IndRef (kn_g, _) ->
            Core.Ref.User.Set.exists (fun r ->
              match r with
              | GlobRef.IndRef (kn_r, _) ->
                MutInd.CanOrd.equal kn_g kn_r
              | _ -> false) ns
          | _ -> false
        in
        let is_local = is_self_ref || spells_bare cx g in
        let is_uniform_self_ref =
          if not is_self_ref then
            true
          else if converted_ts = [] then
            (* Non-parametric inductive: self-reference is trivially uniform.
               The surrounding context may have type vars (e.g. T1 in rect<T1>)
               that are unrelated to the inductive's own parameters — don't
               let those force shared_ptr for a monomorphic self-reference. *)
            true
          else
            List.length converted_ts = List.length tvars
            && List.for_all2
                 (fun ty id ->
                   match (ty : Cpp_ir.Lowered.Type.t) with
                   | Variable (Index (_, Some id') | Named id') -> Id.equal id id'
                   | _ -> false)
                 converted_ts
                 tvars
        in
        if
          (is_self_ref || is_mutual_sibling)
          && not (Base.Table.is_coinductive g)
          && is_uniform_self_ref
        then
          (* Recursive value-type self/mutual references are owned by their
             containing constructor. The pointed-to type may be incomplete at
             field declaration time, so it still needs indirection, but unique
             ownership plus explicit clone is enough. (Arena mode rewrites this
             shared_ptr to a raw arena pointer at the field-declaration site in
             gen_decls, so that method return/parameter positions are unaffected.) *)
          Shared_pointer core
        else if (is_self_ref || is_mutual_sibling) && Base.Table.is_coinductive g
        then
          (* A coinductive value is already a handle on one shared node, so
             a field holding one holds it by value.  The constructor struct
             that holds it is a member template, completed only once the
             coinductive is -- see [Fdeferred_struct]. *)
          core
        else if is_self_ref || is_mutual_sibling then
          (* Non-uniform recursion uses shared_ptr rather than unique_ptr
             because destructor instantiation would diverge. *)
          Shared_pointer core
        else if is_local then
          (* Local non-self inductive: value type, no pointer wrapping *)
          core
        else if not (get_record_fields g == []) then
          (* Record inductive: value type, no pointer wrapping *)
          core
        else
          (* External inductive: value type, namespace-qualified *)
          In_namespace (g, core)
    | _ -> core )
  | Core.Type.Variable {variable = i; _} -> Variable (Index (i, Tvars.tvar_name_at tvars i))
  (* A higher-kinded variable applied to arguments.  The head stays a type
     variable here; [Lower_decl.apply_hkt_resolutions] rewrites it to the
     instance's associated type, leaving [Tapply] to render the application. *)
  | Core.Type.Variable_app {head = i; arguments = args} ->
    let head : Cpp_ir.Lowered.Type.t = Variable (Index (i, Tvars.tvar_name_at tvars i)) in
    Apply (head, List.map (cpp_ir_of_core_type cx env ~ns tvars) args)
  | Core.Type.Meta {contents = Some t} -> cpp_ir_of_core_type cx env ~ns tvars t
  | Core.Type.Meta {contents = None} | Core.Type.Open _ ->
    (* Unresolved meta - use std::any for type erasure. This happens for
       existential type variables in indexed inductives. *)
    Any
  (* Core.Type.Erased marks erased type/prop/implicit parameters in the Core term. We convert
     them to Core.Type.Global_app(VarRef "dummy_*") as intermediate markers so that downstream
     filtering (is_cpp_dummy_type / prints_as_any / filter_erased_type_args in
     gen_expr, eta_fun, and gen_decl_for_pp) can detect and drop them. These
     markers should never survive to the C++ output — the filtering pipeline
     removes them from template argument lists and function signatures. *)
  | Core.Type.Erased Core.Erasure_reason.Type_argument -> Erased Type
  | Core.Type.Erased Core.Erasure_reason.Proof -> Erased Proof
  | Core.Type.Erased (Core.Erasure_reason.Configured_implicit _) -> Erased Implicit
  (* A string literal's type is Rocq's primitive string: the type its
     mapping spells, where one maps it. *)
  | Core.Type.String -> (
    match Base.Mapping_plan.mapped_prim_string () with
    | Some g -> Entity_application (g, [], [])
    | None -> External ("std::string", []) )
  (* Extraction gave up naming this type.  It prints as [std::any], but we
     know nothing about how the value is actually represented. *)
  | Core.Type.Unknown -> Obligation Opaque_type
  (* A hole is ordinary data inside an instantiation, and a reader resolves
     it, leaves the parameter to deduction, or declines before converting:
     one reaching a C++ type is a reader that did none of these. *)
  | Core.Type.Hole hole ->
    Base.Probe.violation "inference hole"
      Pp.(str "hole _" ++ int hole ++ str " reached a C++ type");
    Obligation Opaque_type
  | Core.Type.Axiom -> Entity_application (GlobRef.VarRef (Id.of_string "axiom"), [], [])

(** [resolves_to_any_type ty] — true if [ty] ultimately resolves to
    [std::any].  Handles direct [Tany], erased-type constants (aliases for
    [std::any] registered via {!Base.Table.is_erased_type_const}), and type
    aliases that expand to an erased type.  Used to decide whether a
    scrutinee's template argument makes a constructor field store its
    value as [std::any] at runtime. *)
let rec resolves_to_any_type cx : Cpp_ir.Lowered.Type.t -> bool = function
  | Any | Obligation Opaque_type -> true
  | Erased _ -> false
  | Entity_application (g, [], _) when Base.Table.is_erased_type_const g -> true
  | Entity_application (g, [], _) ->
    let via_core_ty =
      match find_type_opt g with
      | Some core_ty ->
        let tvars = get_current_type_vars cx in
        Some (cpp_ir_of_core_type cx (empty_env ()) tvars core_ty)
      | None ->
        (match g with
         | GlobRef.ConstRef kn ->
           (match Base.Table.lookup_typedef_unchecked kn with
            | Some core_ty ->
              let tvars = get_current_type_vars cx in
              Some (cpp_ir_of_core_type cx (empty_env ()) tvars core_ty)
            | None -> None)
         | _ -> None)
    in
    (match via_core_ty with
     | Some cvt -> resolves_to_any_type cx cvt
     | None -> false)
  | t when Cpp_ir.Types.prints_as_any t -> true
  | _ -> false

(** How a slot of C++ type [t] already known to be boxed boxes its value
    ({!slot_repr_of_cpp_type}). *)
let box_kind_of_cpp_type t = if names_erased_alias t then Family_box else Var_box

(** The representation a value takes in a slot of C++ type [t]: the one
    classifier a slot's {!Base.Type_util.slot_repr} is decided by.  A type that
    resolves to [std::any] is boxed, as a [Family_box] where it names a
    declaration whose body erased, spelled through its alias -- a
    value-indexed family -- and as a [Var_box] otherwise
    ({!box_kind_of_cpp_type}, for a slot already known to be boxed). *)
let slot_repr_of_cpp_type cx t =
  if resolves_to_any_type cx t then Boxed (box_kind_of_cpp_type t) else Native

(** [cpp_of_core env t] converts a Core type in the type-variable scope that is
    currently in effect.  Nearly every conversion inside expression generation
    wants this, and spelling out {!get_current_type_vars} at each one invites
    passing the wrong scope. *)
let cpp_of_core cx env t = cpp_ir_of_core_type cx env (get_current_type_vars cx) t

(** [spell_as_declared orig t]: [t], the C++ type of a callee's parameter
    declared at the Core type [orig] once the call's instantiation is
    substituted, with its arrows grouped as the declaration groups them
    ({!Cpp_ir.Types.arrow_site}): the arrows [orig] writes in one group,
    and a function type a type variable of [orig] is instantiated at as one
    more, spelled as its values are.  [fold_left]'s step, declared
    [B -> A -> B], at [B := nat -> nat -> nat] takes
    [crane::fn<uint64_t(uint64_t, uint64_t)>] and the element, and returns
    the flat [B], not three arguments in one group. *)
let spell_as_declared (orig : Core.Type.t) (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  let rec spell (orig : Core.Type.t) (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
    match (orig, t) with
    | Core.Type.Meta {contents = Some o}, _ -> spell o t
    | Core.Type.Arrow _, Function (doms, cod) ->
      let odoms = core_value_domains orig in
      let k = List.length odoms in
      if k = 0 then
        (* Every arrow erased: the C++ type is the codomain's. *)
        let rec codomain = function
          | Core.Type.Arrow {result; _} -> codomain result
          | Core.Type.Meta {contents = Some o} -> codomain o
          | o -> o
        in
        spell (codomain orig) t
      else if List.length doms < k then t
      else
        let here = List.filteri (fun i _ -> i < k) doms and rest = List.filteri (fun i _ -> i >= k) doms in
        let ocod = core_drop_arrows k orig in
        let cod = spell ocod (if rest = [] then cod else Function (rest, cod)) in
        Function (List.map2 spell odoms here, cod)
    (* An inductive's arguments, or a carrier variable's, are spelled as
       the declaration writes them too: [list (A -> A)] at a function [A]
       holds callables taking [A] as one group, and so does [F (A -> B)]. *)
    | ( (Core.Type.Global_app {type_arguments = oargs; _} | Core.Type.Variable_app {arguments = oargs; _}),
        Entity_application (g, args, vs) )
      when List.compare_lengths oargs args = 0 ->
      Entity_application (g, List.map2 spell oargs args, vs)
    | _, In_namespace (r, t') -> In_namespace (r, spell orig t')
    | _ -> t
  in
  spell orig t

(** What a callee of the Core type [t] returns once given [n] value
    arguments, converted; [auto] (C++ deduces it) where [t] has fewer
    arrows. *)
let codomain_after cx env n t : Cpp_ir.Lowered.Type.t =
  match Base.Type_util.strip_arrows_n n t with Some c -> cpp_of_core cx env c | None -> Auto

(** [template_arg_of_core_type ~site env tvars ty] converts [ty] for a template
    argument position, its arrows spelled as [site] says
    ({!Cpp_ir.Types.arrow_site}).

    [Declared] for every type argument, of an inductive's parameter or of a
    function's: a type variable stands for the type of values, which are
    spelled at the flat arity {!cpp_ir_of_core_type} gives a declaration, so
    an instantiation spelled otherwise would disagree with the values passed
    and returned at it.  [Through_tvar] only for a higher-kinded carrier. *)
let template_arg_of_core_type cx ~site env tvars ty =
  (* Template params emitted at expression/function-call sites are public API
     types. Recursive storage wrapping is introduced only when converting
     constructor fields with an explicit storage namespace. *)
  Cpp_ir.Types.spell_arrows site (cpp_ir_of_core_type cx env ~ns:Core.Ref.User.Set.empty tvars (type_simpl ty))

let build_template_params cx ~site env tvars tys =
  List.map
    (fun ty ->
      let t = template_arg_of_core_type cx ~site env tvars ty in
      (* Check for unbound type variables *)
      match t with
      | Variable (Index (_, None)) when tvars <> [] ->
        (* Type variable has no binding, but we're in a context with typename
           params. This means the Core.Type.Variable index exceeds the scope of tvars.
           Mark as dummy_type to trigger full erasure via filter_erased_type_args.
           Using the unbound Core.Type.Variable would generate invalid C++ references. *)
        (Erased Type : Cpp_ir.Lowered.Type.t)
      | _ ->
        (* Type is either bound, or we're in an untyped context (tvars = []).
           Keep the type as-is. *)
        t )
    tys

(** Generate code for a custom-extracted constructor application.

    Custom-extracted constructors have user-defined C++ syntax (registered via
    [Crane Extract Constant]) that may include type argument placeholders like
    [%t0], [%t1], etc. This function builds the C++ expression by:
    1. Filtering the Core type argument list to keep only type parameters
       (dropping index arguments that don't correspond to C++ template params)
    2. Converting Core types to C++ types via [build_template_params]
    3. Filtering erased types (Core.Type.Erased Core.Erasure_reason.Type_argument → dummy_type) to avoid passing
       empty or partial template argument lists to custom syntax
    4. Wrapping in [mk_cppglob] to apply the custom syntax template

    The filtering is critical because custom syntax strings expect concrete
    type arguments for their placeholders. If we pass an empty or erased
    type arg list, the custom syntax renderer in cpp_print.ml will raise
    an anomaly ("Custom syntax: unbound type argument").

    Example:
    - Core: [Core.Expr.Construct(Core.Type.Global_app(option, [Core.Type.Global_app(nat)]), cons_ctor, [5])]
    - Custom syntax: [(Datatypes.option, 0) := "std::optional<%t0>"]
    - After filtering: [std::optional<unsigned int>]
    - Generated C++: [std::make_optional<unsigned int>(5u)]

    Note: This only handles custom constructors. Regular (non-custom) inductives
    follow a different code path via the main [gen_expr] Core.Expr.Construct case.

    @param env Translation environment (contains type context)
    @param ty  Core type of the constructor application (contains type args)
    @param r   Constructor reference (must be custom-extracted)
    @param ts  Core expression arguments (converted to C++ recursively)
    @return C++ expression applying custom syntax with type/value arguments *)

(** [template_params_of_core ~site:Through_tvar env tys] is {!build_template_params} against the
    type variables the enclosing scope has in hand; see {!cpp_of_core}. *)
let template_params_of_core cx ~site env tys = build_template_params cx ~site env (get_current_type_vars cx) tys

(** [param_expected_cpp_ty env param_tys i] is the C++ type the callee declares
    for its [i]th parameter, and so the type an argument generated for that
    position should aim at.  [None] when the position says nothing useful:
    either the callee has fewer parameters, or the declared type is erased and
    naming [std::any] as the expectation would only invite a spurious box. *)
let param_expected_cpp_ty cx env param_tys i =
  match List.nth_opt param_tys i with
  | Some core_ty ->
    let cpp_ty = cpp_of_core cx env core_ty in
    if Cpp_ir.Types.prints_as_any cpp_ty then None else Some cpp_ty
  | None -> None

(** Follow a name for a type through to the type it stands for.  A [using]
    alias hides the arguments its right-hand side was written with, and those
    arguments are exactly what a value built into such a slot has to agree
    with.  Returns the type unchanged when it is not an alias. *)
let rec unfold_cpp_typedef cx env (cpp_ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  match cpp_ty with
  | In_namespace (_, inner) -> unfold_cpp_typedef cx env inner
  | Entity_application (GlobRef.ConstRef kn, args, _) -> (
    match Base.Table.lookup_typedef_unchecked kn with
    | Some core_ty ->
      let body = cpp_of_core cx env core_ty in
      let n_promoted =
        let n = List.length (Base.Table.promoted_type_params (GlobRef.ConstRef kn)) in
        if List.length args >= n + Base.Core_util.type_maxvar core_ty then n else 0
      in
      if args = [] then body
      else Cpp_ir.Types.substitute (fun i -> if i >= 1 then List.nth_opt args (n_promoted + i - 1) else None) body
    | None -> cpp_ty )
  | _ -> cpp_ty

(** Whether [a] and [b] are one type with its arrows grouped otherwise
    ({!Cpp_ir.Types.same_arrows}) once every alias in either is unfolded:
    [crane::fn<st<nat>(nat)>] and [crane::fn<std::pair<nat, nat>(nat,
    nat)>] at [st A := nat -> A * nat].  Not two spellings of one type
    that differ only in the aliases they write. *)
let regrouped_through_aliases cx env a b =
  let unfold = Cpp_ir.Types.map (unfold_cpp_typedef cx env) in
  let a = unfold a and b = unfold b in
  a <> b && Cpp_ir.Types.same_arrows a b

(** [t] with every type variable named by the default spelling of its
    index ({!Base.Common.tvar_name}) written by the index alone: the two
    print the same, and lowering records a binder's type before its
    variables are named. *)
let default_tvar_names (t : Cpp_ir.Lowered.Type.t) =
  Cpp_ir.Types.map
    (fun (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
      match t with
      | Variable (Index (i, Some n)) when String.equal (Id.to_string n) (Base.Common.tvar_name i) ->
        Variable (Index (i, None))
      | t -> t )
    t

(** Collapse the erased parts of a type to [std::any]: the type itself when it
    resolves to [std::any], and, structurally, a function type's arguments and
    result.  Lets an expected type argument be compared against a computed one
    on equal terms, the computed side already being erased. *)
let rec normalize_erased_types cx : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | t when resolves_to_any_type cx t -> Any
  | Function (ps, r) ->
    Function (List.map (normalize_erased_types cx) ps, normalize_erased_types cx r)
  | t -> t

(* Whether a constructor of the inductive [i] of [kn], of [nparams]
   parameters, stores a value whose C++ type writes a variable other than a
   parameter inside another type: [A * nat], a parameter of an inductive, an
   arrow -- not bare, and not at an inductive's index, which its generated
   type strips. *)
let stores_written_variable kn i nparams =
  match Base.Table.lookup_ind kn (Global.lookup_mind kn) with
  | exception Not_found -> true
  | None -> true
  | Some ind -> (
    match List.nth_opt (Array.to_list ind.Core.Inductive.packets) i with
    | None -> true
    | Some (p : Core.Inductive.Packet.t) ->
      let rec written ~under (t : Core.Type.t) =
        match resolve_meta t with
        | Variable {variable = j; _} -> under && j > nparams
        | Variable_app {head; arguments} -> (under && head > nparams) || List.exists (written ~under:true) arguments
        | Global_app {head = GlobRef.IndRef (kn', _); type_arguments; _} ->
          let np = match Base.Table.get_ind_num_param_vars_opt kn' with Some k -> k | None -> List.length type_arguments in
          List.exists (fun (k, a) -> k < np && written ~under:true a) (List.mapi (fun k a -> (k, a)) type_arguments)
        | Global_app {type_arguments; _} -> List.exists (written ~under:true) type_arguments
        | Arrow {parameter; result} -> written ~under:true parameter || written ~under:true result
        | _ -> false
      in
      Array.exists (List.exists (written ~under:false)) p.constructor_argument_types )

(** Whether [id]'s declaration declares a template parameter for its scheme
    variable of index [i]: one its declared type spells
    ({!Base.Type_util.spelled_tvars_indexed}), but a result standing only at
    an index, which the declaration returns boxed; and one inside a compound
    index, which a body casts back to.  A callee written
    by a mapping's text rather than declared by Crane takes the arguments its
    text names, so every variable counts. *)
let declares_tvar cx id =
  match callee_core_type cx id with
  | _ when Base.Table.is_custom id || Base.Table.is_mapped_operation id -> fun _ -> true
  | None -> fun _ -> true
  | Some core_ty ->
    let cty = cpp_ir_of_core_type cx (empty_env ()) [] (type_simpl core_ty) in
    let declared = IntSet.of_list (List.map fst (Base.Type_util.spelled_tvars_indexed cty)) in
    (* A result that is a variable the arguments carry only as an index is
       the box ([crane::obj]) the declaration returns
       ({!Base.Type_util.index_only_result_tvar}): nothing spells it, and a
       call that knows the index converts the result itself. *)
    let index_result = Base.Type_util.index_only_result_tvar core_ty in
    (* A variable at an index of a family some constructor of which stores
       a value whose C++ type writes a variable of its own inside another type
       -- [mk_pair_wrap : forall A, A * nat -> pair_wrap A] -- is what a body
       casts the stored value back to ([std::pair<A, nat>]): a cast at the
       box would test another type, so it stays a parameter.  So does a
       variable inside a compound index.  One a family only ever stores bare,
       or at another family's index, is only ever boxed. *)
    let cast_back =
      let acc = ref IntSet.empty in
      let rec vars (t : Core.Type.t) =
        match resolve_meta t with
        | Variable {variable = j; _} -> acc := IntSet.add j !acc
        | Variable_app {head; arguments} -> acc := IntSet.add head !acc; List.iter vars arguments
        | Global_app {type_arguments; _} -> List.iter vars type_arguments
        | Arrow {parameter; result} -> vars parameter; vars result
        | _ -> ()
      in
      let rec walk (t : Core.Type.t) =
        match resolve_meta t with
        | Global_app {head = GlobRef.IndRef (kn, i); type_arguments; _} ->
          let nparams = match Base.Table.get_ind_num_param_vars_opt kn with Some k -> k | None -> List.length type_arguments in
          List.iteri
            (fun k a ->
              if k < nparams then walk a
              else
                match resolve_meta a with
                | Variable {variable = j; _} -> if stores_written_variable kn i nparams then acc := IntSet.add j !acc
                | a -> vars a)
            type_arguments
        | Global_app {type_arguments; _} -> List.iter walk type_arguments
        | Variable_app {arguments; _} -> List.iter walk arguments
        | Arrow {parameter; result} -> walk parameter; walk result
        | _ -> ()
      in
      walk core_ty;
      !acc
    in
    (* The C++ type above may write a variable through something it does not
       spell as an application -- a class's [Type -> Type] field, [memM B] --
       so the Core type is read too: a variable occurring there outside the
       positions a custom template does not name, and outside the
       parameters C++ drops (erased ones, type-class instances), is
       spelled. *)
    let rec spelled_in i (t : Core.Type.t) =
      match resolve_meta t with
      | Variable {variable = j; _} -> j = i
      | Variable_app {head; arguments} -> head = i || List.exists (spelled_in i) arguments
      | Global_app {head = g; type_arguments; _} -> (
        match (Base.Type_util.custom_referenced_positions_opt g, g) with
        | Some referenced, _ ->
          List.exists (fun (k, t) -> IntSet.mem k referenced && spelled_in i t) (List.mapi (fun k t -> (k, t)) type_arguments)
        (* An inductive's index is stripped from the generated type. *)
        | None, GlobRef.IndRef (kn, _) ->
          let nparams = match Base.Table.get_ind_num_param_vars_opt kn with Some k -> k | None -> List.length type_arguments in
          List.exists (fun (k, t) -> k < nparams && spelled_in i t) (List.mapi (fun k t -> (k, t)) type_arguments)
        | None, _ -> List.exists (spelled_in i) type_arguments )
      | Arrow {parameter; result} ->
        ((not (Base.Core_util.is_erased_type parameter || Base.Table.is_typeclass_type parameter)) && spelled_in i parameter)
        || spelled_in i result
      | _ -> false
    in
    fun i -> IntSet.mem i cast_back || (index_result <> Some i && (IntSet.mem i declared || spelled_in i core_ty))

(** How many of [id]'s leading template parameters no signature mentions:
    its leading phantoms, among the variables it declares
    ({!declares_tvar}), of the run {!Base.Type_util.explicit_tvar_prefix}
    counts off its declared type.  Nothing deduces them, so a call writes
    them, and {!Core_plan.Callable_abi} records them as [Phantom] parameters
    of [id]'s plan.  The declaration emitter counts the same run and leaves
    those parameters undefaulted. *)
let leading_phantom_count cx id =
  match callee_core_type cx id with
  | None -> 0
  | Some core_ty ->
    let cty = cpp_ir_of_core_type cx (empty_env ()) [] (type_simpl core_ty) in
    let force_required = collect_core_type_index_tvars core_ty in
    let n = explicit_tvar_prefix ~force_required cty in
    let indexed =
      List.sort_uniq Int.compare
        (List.map fst (Base.Type_util.get_tvars_indexed cty) @ IntSet.elements force_required)
    in
    let declares = declares_tvar cx id in
    List.length (List.filter declares (List.filteri (fun k _ -> k < n) indexed))
