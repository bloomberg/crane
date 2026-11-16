(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Shared mutable state for lowering Core bodies to CppIR.

    Holds the per-declaration lowering context ([tctx]) and its accessors,
    so that lowering ({!Translation} and the [Translation_*] modules it
    drives) and the declaration generators ({!Gen_functions},
    {!Gen_instances}, ...) can share this state without a dependency cycle:
    it sits below every lowering module.  {!Cpp_state} is the printer's
    counterpart.

    The context is split by how each part composes ({!translation_ctx}):
    {!input}, what a declaration's generator sets before lowering its body
    and lowering only reads; {!lexical}, what holds for the scope being
    lowered, extended on entry and restored on exit; and {!threaded}, the
    counters siblings advance in turn.  What lowering produces for later
    phases is output, collected apart from the context: the helpers it
    lifts ({!collecting_lifted}). *)

module IntMap = Map.Make (Int)

open Common
open Names
open Core_query

(** An [Entity] for the global [r] at [tys], its custom extraction
    ({!Table.inline_custom_text}) looked up once here.  [yields] is what
    the global evaluates to, and is worth passing whenever the caller has the
    global's instantiated type: for a [%result] block template in value
    position it is the only record of the type, since there is no call node to
    carry one. *)
let mk_cppglob ?yields (r : GlobRef.t) (tys : Cpp_ir.Lowered.Type.t list) : Cpp_ir.Lowered.Expr.t =
  Entity (r, tys, Some {inline = Option.map Cpp_ir.Foreign.template_of_text (Table.inline_custom_text r);
                        custom_yields = yields})

(** What a binder of the lexical environment stands for ({!Lexenv.role}). *)
type binder_role = Lexenv.role =
  | Value
  | Dictionary

(** A binder of the lexical environment ({!Lexenv.binder}). *)
type env_binder = Lexenv.binder = {
  id : Id.t;
  type_ : Core.Type.t;
  role : binder_role;
}

(** What bound the binder a variable read reads. *)
module Binder_kind = struct
  type t =
    | Outer  (** bound outside the region *)
    | Parameter  (** a lambda's parameter *)
    | Let
    | Fix  (** a local fixpoint's function *)
    | Pattern  (** a pattern's, or a record projection's *)
end

(** What decided a binder's C++ type, and so which answer wins when both are
    available: an instantiation a pattern match pinned down is more precise
    than the type the binder was given where it was bound. *)
module Binder_origin = struct
  type t =
    | Binding  (** Assigned at the binding site, from the binder's Core type *)
    | Pattern  (** Pinned down by the scrutinee's instantiation in a branch *)
end

(** A variable read's binder as {!Representation_plan} plans it: whether it
    holds a box, what bound it, and the C++ type it is planned at, where it
    is planned at one. *)
module Planned_read = struct
  type t = {
    boxed : bool;
    kind : Binder_kind.t;
    type_ : Cpp_ir.Lowered.Type.t option;
  }
end

(** A pattern binder's representation as {!Representation_plan} plans it:
    whether it holds a box.  [bound_boxed] is whether it holds a box at
    the Core type it is bound at, nothing pinned down: how the reuse arm,
    which declares the same fields again, and a record projection in an
    expression declare it.  That answer rests on no other binder. *)
type planned_repr = {
  boxed : bool;
  bound_boxed : bool;
}

(** Mode for ITree effect extraction: sequential erases the tree,
    reified preserves it as [shared_ptr<ITree<R>>] ({!Core_effects.mode}). *)
type itree_extraction_mode = Core_effects.mode =
  | Sequential  (** Default: erase [itree E R] to [R]; bind becomes [;] *)
  | Reified     (** Preserve structure: [itree E R] becomes [shared_ptr<ITree<R>>] *)

(** Where generation is ({!input.generating}). *)
and generation_site =
  | In_module of Names.ModPath.t  (** the body of this module *)
  | Outside_modules  (** a pass over the whole unit or program *)

(** What the analysis of the whole program decided that lowering reads
    ({!Program_facts.analyze_program}), for every unit of the extraction:
    the definitions whose body only throws, which are spelled as
    zero-argument functions ({!Translation_suspension.thunk_reason}), which
    parameters of each function it owns, innermost first, settled across
    calls ({!Ownership.summarize}), and the parameters of a member of a
    recursive group a partner's call passes a closure for
    ({!Translation_callable_params.partner_closure_params}). *)
type program_facts = {
  throwing_values : Ref.Can.Set.t;
  parameter_ownership : bool list Ref.User.Map.t;
  partner_closure_params : int list Ref.User.Map.t;
}

(** The facts of a program nothing was analysed for: lowering outside an
    extraction's units, or before its program is frozen. *)
let no_program_facts =
  { throwing_values = Ref.Can.Set.empty;
    parameter_ownership = Ref.User.Map.empty;
    partner_closure_params = Ref.User.Map.empty }

(** What analysing and planning the unit being extracted decided that
    lowering reads, set for the extent of the unit
    ({!with_unit_facts}): the projections used as function values, which
    are written as standalone functions, and the effect operations its
    applications are ({!Program_facts.t}), and the elaborations of the
    unit's calls ({!Core_elaborate.structure}), [None] until the unit is
    walked; and the unit's context ({!Unit_context}). *)
type unit_facts = {
  higher_order_projections : Ref.User.Set.t;
  effects : Core_effects.t;
  elaborations : Core_elaborate.t option;
  context : Unit_context.t;
}

(** The facts of no unit: lowering outside a unit's extent. *)
let no_unit_facts =
  { higher_order_projections = Ref.User.Set.empty;
    effects = Core_effects.empty;
    elaborations = None;
    context = Unit_context.detached }

(** What the generator of a declaration says about the body it lowers, set
    before lowering starts and not changed by it: the declaration's head,
    parameters, owner, effect mode and module, and the program's and unit's
    facts.  A declaration emitter sets these and restores them on the way
    out; lowering only reads them.  A field belongs here when every point
    of one body sees the same value: no scope inside the body changes it,
    so a nested lambda or lifted helper reads its enclosing declaration's
    answer. *)
type input = {
  (* The declaration's template head, verbatim: every parameter it declares,
     with the kind it declares it at.  Two questions are answered from it and
     neither can be answered from {!current_type_vars}, which keeps only the
     names and only the Core-indexed ones:

     - whether an occurrence may be written applied, which turns on [typename]
       versus [template <typename> class] (see {!is_current_typename_var});
     - which parameters are the enclosing class instances, which a lifted
       helper must redeclare because the body it lifts spells them (see
       {!current_class_temps}).

     Only the emitters that build the head know it, so a scope that does not
     say leaves this empty and both readers answer negatively.  Input: a
     lifted helper redeclares the head's class instances, so it must see the
     enclosing declaration's head. *)
  current_template_head : Cpp_ir.Lowered.phase Cpp_ir.Template.parameters;
  (** The Core binders of the parameters of the declaration whose body is
     being generated ({!Core_binder}), which call sites and matches ask a
     variable's type as a parameter of: by binder, since every binder the
     body pushes shifts a parameter's index.  Keying by binder rather than
     index is what lets it stay fixed for the body. *)
  current_parameters : Core_binder.t list;
  (** The definition whose body is being generated
     ({!Gen_context.begin_body}): what its Core binders are binders of
     ({!Core_binder}).  [None] outside a body, where {!with_region} plans
     no representation or positions. *)
  body_owner : GlobRef.t option;
  (** Whether that body is a function's, generated as one, rather than a
     constant's initialiser or a member's: Loopify lowers every local
     fixpoint of a function's body, and only the tail loops of others. *)
  body_function : bool;
  (** ITree extraction mode: controls whether itree types are erased
     ([Sequential]) or preserved as [shared_ptr<ITree<R>>] ([Reified]).  A
     property of the declaration ({!with_itree_mode}). *)
  itree_mode : itree_extraction_mode;
  (** When generating a method body, holds the set of self-references
     (the inductive type(s) this method belongs to). Merged into the ns
     argument of convert_core_type_to_cpp_type so that self-refs inside
     container types (e.g. List<tree>) get shared_ptr wrapping, matching
     the struct definition. Empty outside method bodies. *)
  method_self_ns : Ref.User.Set.t;
  (** Where generation is, as far as which inductives it spells bare goes:
     inside the body of a module, whose planned local inductives
     ({!Scope_plan.local_inductives}) it spells bare, or outside every
     module, where it spells none.  Set where generation enters a module
     ({!generating_in}) or a pass over the whole unit
     ({!generating_outside_modules}); [None] before either, where nothing
     may ask ({!local_inductives_in_scope}).  The plan is asked on each
     read rather than its answer kept here. *)
  generating : generation_site option;
  (** What the analysis of the whole program decided ({!program_facts}),
     set for the extent of the extraction's units
     ({!with_program_facts}). *)
  program : program_facts;
  (** What analysing and planning the unit decided ({!unit_facts}), set for
     the extent of the unit ({!with_unit_facts}). *)
  unit : unit_facts;
}

(** What holds for the scope being lowered: the binders in scope and their
    types, the type variables and return type of the innermost function,
    and the plans of the region it is in.  Lowering extends it on entering
    a scope and restores it on leaving ({!with_field}, {!with_scope}), so a
    sibling never sees what a scope set.  A field belongs here when a scope
    nested in the body (a lambda, a let, a branch, a lifted helper) may give
    it another value that must not outlive the scope. *)
type lexical = {
  (* Template type variables for the function currently being translated:
      lexical because a lifted helper or polymorphic lambda has its own. *)
  current_type_vars : Id.t list;
  (** C++ return type of the enclosing function, set by the function and
     instance generators ({!with_cpp_return_type}). Used to recover erased
     template type args at call sites where C++ can't deduce them from lambda
     arguments ({!current_cpp_return_type}).  Lexical: a lambda's body has
     its own return type. *)
  current_cpp_return_type : Cpp_ir.Lowered.Type.t option;
  (** De Bruijn environment: each variable's binder, with its Core type and
     role.  Extended by every binder a scope introduces. *)
  env_types : Lexenv.t;
  (** The C++ type of {e every} binder in scope, by de Bruijn index, paired
      with what decided it.

      A binder is typed once, where it is bound ({!Binder_origin.Binding}, written by
      [push_binders]); a pattern match that pins a field down more precisely
      than its definition-site type says -- matching [SigT<Tag,
      std::function<any(any)>>] records [Function (\[Any\], Any)] for the
      function field -- overrides it ({!Binder_origin.Pattern}, written by
      [populate_erased_field_env]).  Whether a binder is boxed is read off
      this map rather than tracked beside it, so the two answers cannot drift
      apart.

      Shifted by {!push_env_types} and cleared by {!reset_env_types}. *)
  cpp_binder_types : (Cpp_ir.Lowered.Type.t * Binder_origin.t) IntMap.t;
  (** The C++ types a declaration's head declares its innermost parameters
     at, innermost first, beside the depth of the binder stack they were
     pushed at: what a region generated directly in that scope plans those
     binders at ({!Representation_plan.region}).  [None] where the head
     declares none beyond the conversion of their Core types.  Lexical
     because it is tied to a depth of [env_types], and is cleared with it
     ({!reset_env_types}). *)
  declared_outer : (int * Cpp_ir.Lowered.Type.t option list) option;
  (** Maps promoted record fields to their C++ qualified types.
     Example: [m_carrier] maps to [Member (Variable _tcI0, m_carrier)]
     (prints as: [typename _tcI0::m_carrier]).
     Set ({!with_promoted_var_map}) when generating template functions and
     instances with typeclass parameters. Used by
     {!Translation_types.cpp_ir_of_core_type} to resolve [Promoted_member]
     markers.  Lexical: each such function or instance binds its own class
     parameters. *)
  promoted_var_map : (Id.t * Cpp_ir.Lowered.Type.t) list;
  (** When true, we are inside a constructor expression (module-level static
     initializer). Promoted type vars that can't be resolved via
     [promoted_var_map] fall back to [Any] ([std::any]) instead of keeping
     [Promoted_member] markers, because module-level aliases apply. *)
  in_constructor_expr : bool;
  (** The template parameter of the polymorphic function object being
     generated, if any.  Inside such a lambda every erased type denotes that
     one parameter -- it is the type the rank-2 binder quantified over -- so a
     producer with nothing else to say about a type argument says the carrier
     instead of [std::any].  See {!Rank2}. *)
  rank2_carrier : Id.t option;
  (** The local fixpoints, by occurrence, whose members are being generated
     as helpers lifted out of that body, around the point being generated:
     a helper's machine may adopt a fixpoint in its flow, a local
     fixpoint's lambda never does. *)
  lifted_fixpoints : Core.Occurrence.t list;
  (** Which binders the region being generated owns where each is read, and
     which reads are last uses where their value may be taken
     ({!Ownership_ir}).  Set where the region's body is generated
     ({!with_region}), and emptied where a body or a closure begins. *)
  move_plan : Ownership_ir.t;
  (** Whether each pattern binder of the region being generated holds a box,
     as {!Representation_plan} plans it from the region's Core body: by Core
     site and field.  Set beside {!move_plan} ({!with_region}) in a body;
     under [CRANE_CHECK_IR] translation checks it against the binder's
     recorded C++ type. *)
  representation : (Core_binder.site * int * planned_repr) list;
  (** Whether the binder each variable read of the region reads holds a box,
     as {!Representation_plan} plans it: by the read's occurrence.  Set
     beside {!representation}; the only answer lowering reads
     ({!Translation_binders.read_is_boxed}). *)
  planned_reads : (Core.Occurrence.t * Planned_read.t) list;
  (** The C++ type the position each coercion of the region fills is
     generated against, as {!Position_plan} plans it: by the coercion's
     occurrence, a region nested in another first.  Set beside
     {!planned_reads}. *)
  planned_positions : (Core.Occurrence.t * Cpp_ir.Lowered.Type.t option) list;
  (** Perceus reuse: inside a [use_count() == 1]-guarded reuse arm of a
     match, the token [tok] (the moved, uniquely-owned storage the
     match frees) the constructions the arm's plan names
     ({!Ownership_ir.allocation}) are built in, as [<ctor>__reuse(tok, ...)]
     instead of the normal factory.  The plan names at most one on any path,
     so nothing here tracks whether it has been taken. *)
  reuse_token : Cpp_ir.Lowered.Expr.t option;
}

(** What lowering accumulates across siblings within a body: the counters
    fresh names are numbered by.  One generation advances them and the next
    reads the advanced value.  A body starts them at zero
    ({!Gen_context.begin_body}), and so does a closure's body, which is
    generated as one ({!with_escape_analysis}); a
    {!with_scope} bracket puts them back, as it puts back the whole
    context.  A field belongs here when siblings must see each other's
    effect on it: a name minted in one branch must not be minted again in
    the next, which a lexical restore would allow. *)
type threaded = {
  (* Counter for generating unique match scrutinee variable names
     ([_mp0], [_mp1], ...). Reset at function boundaries. *)
  match_param_counter : int;
  (** Counter for generating unique scrutinee cache variable names
     ({!Common.scrutinee_cache_id}) for a custom match whose template reads
     its scrutinee more than once. Reset at function boundaries. *)
  cs_counter : int;
}

(** The translation context, by role.  What lowering produces for later
    phases is not part of it: the helpers it lifts go to the generation
    collecting them ({!lifted_so_far}), whatever scope lifted them. *)
type translation_ctx = {
  input : input;  (** fixed for a body *)
  lexical : lexical;  (** extended per scope, restored on exit *)
  threaded : threaded;  (** advanced by siblings in turn *)
}

(** The global translation context, reset between top-level declarations.

    The record is immutable and the mutability lives in this one [ref], so
    saving and restoring the context around a subtree is total: [let saved =
    !tctx in ... ; tctx := saved] cannot forget a field, whatever fields are
    added later. *)
let tctx =
  ref
    { input =
        { current_template_head = [];
          current_parameters = [];
          body_owner = None;
          body_function = false;
          itree_mode = Sequential;
          method_self_ns = Ref.User.Set.empty;
          generating = None;
          program = no_program_facts;
          unit = no_unit_facts };
      lexical =
        { current_type_vars = [];
          current_cpp_return_type = None;
          env_types = Lexenv.empty;
          cpp_binder_types = IntMap.empty;
          declared_outer = None;
          promoted_var_map = [];
          in_constructor_expr = false;
          rank2_carrier = None;
          lifted_fixpoints = [];
          move_plan = Ownership_ir.empty;
          representation = [];
          planned_reads = [];
          planned_positions = [];
          reuse_token = None };
      threaded = {match_param_counter = 0; cs_counter = 0} }

(** Update the input part of the context with [f]. *)
let set_input f = tctx := { !tctx with input = f (!tctx).input }

(** Update the lexical part of the context with [f]; nothing restores it. *)
let set_lexical f = tctx := { !tctx with lexical = f (!tctx).lexical }

(** Update the threaded part of the context with [f]. *)
let set_threaded f = tctx := { !tctx with threaded = f (!tctx).threaded }

(** [with_field get set v f] runs [f] with one context field set to [v], and
    puts the enclosing value back on the way out however [f] leaves --
    returning or raising.

    Only the one field is restored, deliberately: the effects [f] means to
    have on the rest of the context (a counter advanced, a reuse token
    consumed) must survive, so saving and restoring the whole record would be
    wrong here even though it is right at a declaration boundary.

    Every dynamic-extent field gets a [with_*] built from this, so that no
    caller writes the save/set/restore by hand -- an omitted restore does not
    fail, it silently leaks the setting into whatever is translated next. *)
let with_field get set v f =
  let saved = get !tctx in
  set v;
  Fun.protect ~finally:(fun () -> set saved) f

(** Accessors for {!lexical.current_type_vars}: the template type
    variables in scope for the function currently being translated.

    Reach for {!with_type_vars} first.  These two are for the few scopes whose
    extent is not a lexical one -- opened partway through a declaration
    emitter and closed at each of its exits. *)
let set_current_type_vars (tvars : Id.t list) =
  set_lexical (fun l -> { l with current_type_vars = tvars })

(** The template type variables in scope ({!lexical.current_type_vars}). *)
let get_current_type_vars () = (!tctx).lexical.current_type_vars

(** Empty {!lexical.current_type_vars}. *)
let clear_current_type_vars () = set_lexical (fun l -> { l with current_type_vars = [] })

(** Accessors for {!input.current_template_head}.  Set only by an
    emitter that has just built the declaration's template head, and restored
    by it on the way out; every other scope leaves the enclosing answer
    standing rather than guessing at one.  The readers below derive their
    answers from it rather than each keeping a list of their own. *)
let set_current_template_head (head : Cpp_ir.Lowered.phase Cpp_ir.Template.parameters) =
  set_input (fun i -> { i with current_template_head = head })

(** The current declaration's template head ({!input.current_template_head}). *)
let get_current_template_head () = (!tctx).input.current_template_head

(** Whether the head declares [id] as a plain [typename], so that an applied
    occurrence of it cannot be written. *)
let is_current_typename_var (id : Id.t) =
  List.exists
    (fun (tt, i) ->
      Id.equal id i
      && match (tt : _ Cpp_ir.Template.Parameter_kind.t) with Typename | Typename_default _ -> true | _ -> false )
    (!tctx).input.current_template_head

(** The head's concept-constrained parameters: the class instances the
    declaration is written against.  A helper lifted out of its body spells
    them, so it has to declare them too. *)
let current_class_temps () =
  List.filter
    (fun (tt, _) -> match (tt : _ Cpp_ir.Template.Parameter_kind.t) with Concept _ -> true | _ -> false)
    (!tctx).input.current_template_head

(** Every type name the current declaration's head puts in scope: its
    Core-indexed type variables and the class instances it is written against.
    A resolved class field names the latter -- [typename StateV<_tcI0>::state]
    -- and is as much this scope's as [T1] is. *)
let current_scope_type_names () =
  (!tctx).lexical.current_type_vars @ List.map snd (current_class_temps ())

(** [with_type_vars tvars f] runs [f] with [tvars] as the type-variable scope,
    and puts the enclosing scope back on the way out however [f] leaves --
    returning or raising.

    Prefer this to a hand-written save/set/restore wherever the scope's extent
    is a lexical one.  Everything that converts a type reads the scope
    ambiently (see {!Translation_types.cpp_of_core}), so a restore that a path skips
    does not fail: the next conversion quietly numbers its type variables
    against the wrong function. *)
let with_type_vars (tvars : Id.t list) (f : unit -> 'a) : 'a =
  with_field (fun c -> c.lexical.current_type_vars) set_current_type_vars tvars f

(** [with_cpp_return_type ty f] runs [f] with [ty] as the enclosing
    function's C++ return type -- the type a tail expression is cast to. *)
let with_cpp_return_type (ty : Cpp_ir.Lowered.Type.t option) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.lexical.current_cpp_return_type)
    (fun t -> set_lexical (fun l -> { l with current_cpp_return_type = t }))
    ty f

(** The enclosing function's C++ return type
    ({!lexical.current_cpp_return_type}). *)
let current_cpp_return_type () : Cpp_ir.Lowered.Type.t option = (!tctx).lexical.current_cpp_return_type

(** Whether the enclosing function returns [void]. *)
let returns_void () =
  match (!tctx).lexical.current_cpp_return_type with Some Cpp_ir.Type.Void -> true | _ -> false

(** [with_parameters bs f] runs [f] with [bs] as the binders of the
    declaration's parameters ({!input.current_parameters}). *)
let with_parameters (bs : Core_binder.t list) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.input.current_parameters)
    (fun bs -> set_input (fun i -> { i with current_parameters = bs }))
    bs f

(** [with_method_self_ns ns f] runs [f] with [ns] as the inductives whose
    methods are being generated, so self-references inside container types get
    the same [shared_ptr] wrapping as in the struct definition. *)
let with_method_self_ns (ns : Ref.User.Set.t) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.input.method_self_ns)
    (fun ns -> set_input (fun i -> { i with method_self_ns = ns }))
    ns f

(** [with_program_facts facts f] runs [f] lowering the units of a program
    analysed for [facts] ({!input.program}). *)
let with_program_facts (facts : program_facts) (f : unit -> 'a) : 'a =
  with_field (fun c -> c.input.program) (fun p -> set_input (fun i -> { i with program = p })) facts f

(** [with_unit_facts facts f] runs [f] lowering a unit analysed and
    planned for [facts] ({!input.unit}). *)
let with_unit_facts (facts : unit_facts) (f : unit -> 'a) : 'a =
  with_field (fun c -> c.input.unit) (fun u -> set_input (fun i -> { i with unit = u })) facts f

(** The facts of the unit being lowered ({!input.unit}). *)
let unit_facts () = (!tctx).input.unit

(** Whether the unit uses the projection [r] as a function value, which is
    then written as a standalone function ({!unit_facts}). *)
let is_higher_order_projection r = Ref.User.Set.mem r (!tctx).input.unit.higher_order_projections

(** The elaborations of the unit's calls ({!unit_facts}): [None] until the
    unit is walked. *)
let elaborations () = (!tctx).input.unit.elaborations

(** The context of the unit being lowered ({!unit_facts}). *)
let unit_context () = (!tctx).input.unit.context

(** Whether the unit being lowered counts references non-atomically
    ({!Unit_context.non_atomic_rc}). *)
let non_atomic_rc () = Unit_context.non_atomic_rc (unit_context ())

(** The callable plans of the unit being lowered ({!Unit_context.t.callables}). *)
let callables () = (unit_context ()).callables

(** [callee_core_type r] -- the Core type of the callable [r] as the unit's plan
    of it records it ({!Callable_abi.core_type}): the signature call
    translation rebuilds a C++ head from.  While the plans are being made a
    global has none, and is read off the table; under [CRANE_CHECK_IR] a
    planned one is held to the table, and emission finding none is a
    violation. *)
let callee_core_type (r : GlobRef.t) : Core.Type.t option =
  match Callable_abi.planned_core_type (callables ()) r with
  | Some planned ->
    if Probe.checking () then begin
      let live = find_type_opt r in
      let agrees =
        match (planned, live) with
        | Some a, Some b -> a == b || Core_util.eq_core_type a b
        | None, None -> true
        | _ -> false
      in
      Probe.hit "callee-ml-type" (fun () -> if agrees then "planned agree" else "planned disagree");
      if not agrees then
        Probe.violation "callee signature"
          Pp.(str "the plan of " ++ GlobRef.print r ++ str " records an ML type the table does not have")
    end;
    planned
  | None ->
    let emitting = match Common.get_phase () with Common.Emit -> true | Common.Plan -> false in
    Probe.hit "callee-ml-type"
      (fun () -> (if emitting then "unplanned emit " else "unplanned plan ") ^ Pp.string_of_ppcmds (GlobRef.print r));
    if emitting && Option.has_some (find_type_opt r) then
      Probe.violation "callee signature"
        Pp.(str "emission reads the signature of " ++ GlobRef.print r ++ str ", which no plan covers");
    find_type_opt r

(** {!callee_core_type}, raising [Not_found] where there is none. *)
let callee_core_type_exn r = match callee_core_type r with Some t -> t | None -> raise Not_found

(** Whether the analysis of the program found that the body of the
    definition [r] only throws ({!program_facts}). *)
let is_throwing_value r = Ref.Can.Set.mem r (!tctx).input.program.throwing_values

(** The ownership of the global [r]'s parameters, innermost first, settled
    across calls ({!program_facts}): [None] for one the analysis did not
    settle. *)
let settled_ownership r = Ref.User.Map.find_opt r (!tctx).input.program.parameter_ownership

(** [generating_at site f] runs [f] with generation at [site]
    ({!input.generating}); the entries below are the only callers. *)
let generating_at (site : generation_site) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.input.generating)
    (fun g -> set_input (fun i -> { i with generating = g }))
    (Some site) f

(** [generating_in mp f] runs [f] generating an element of the body of the
    module [mp], whose planned local inductives it spells bare. *)
let generating_in (mp : ModPath.t) (f : unit -> 'a) : 'a =
  match Scope_plan.local_inductives (unit_context ()).scopes mp with
  | Some _ -> generating_at (In_module mp) f
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the body of the module " ++ str (ModPath.to_string mp) ++ str " has no planned local inductives.")

(** [generating_outside_modules f] runs [f] generating outside the body of
    every module, where no inductive is spelled bare: a pass over the whole
    unit or program that asks what a type converts to, not how a module
    writes it. *)
let generating_outside_modules (f : unit -> 'a) : 'a = generating_at Outside_modules f

(** The inductives spelled bare where generation is: the planned ones of the
    module it entered ({!generating_in}), none outside every module
    ({!generating_outside_modules}).  Generation that entered neither has no
    answer. *)
let local_inductives_in_scope () =
  match (!tctx).input.generating with
  | Some (In_module mp) -> (
    match Scope_plan.local_inductives (unit_context ()).scopes mp with
    | Some local -> local
    | None ->
      CErrors.anomaly
        Pp.(str "Crane: the body of the module " ++ str (ModPath.to_string mp)
            ++ str " has no planned local inductives.") )
  | Some Outside_modules -> []
  | None -> CErrors.anomaly Pp.(str "Crane: generation asked which inductives it spells bare outside every entry.")

(** Whether generation spells the inductive [r] bare, unqualified by its
    namespace ({!local_inductives_in_scope}). *)
let spells_bare r = List.exists (GlobRef.CanOrd.equal r) (local_inductives_in_scope ())

(** The type of the inductive [r] at [args] as generation spells it: bare
    where it is local, qualified by its namespace elsewhere. *)
let inductive_type r args es : Cpp_ir.Lowered.Type.t =
  let t : Cpp_ir.Lowered.Type.t = Entity_application (r, args, es) in
  if spells_bare r then t else In_namespace (r, t)

(** [with_lifted_fixpoint occurrence f] runs [f] generating the members of
    the local fixpoint at [occurrence] as lifted helpers
    ({!lexical.lifted_fixpoints}). *)
let with_lifted_fixpoint (occurrence : Core.Occurrence.t) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.lexical.lifted_fixpoints)
    (fun os -> set_lexical (fun l -> { l with lifted_fixpoints = os }))
    (occurrence :: (!tctx).lexical.lifted_fixpoints)
    f

(** [with_promoted_var_map m f] runs [f] with [m] as the resolution for the
    promoted type variables in scope -- see {!lexical.promoted_var_map}. *)
let with_promoted_var_map (m : (Id.t * Cpp_ir.Lowered.Type.t) list) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.lexical.promoted_var_map)
    (fun m -> set_lexical (fun l -> { l with promoted_var_map = m }))
    m f

(** [with_in_constructor_expr b f] runs [f] with
    {!lexical.in_constructor_expr} set to [b]. *)
let with_in_constructor_expr (b : bool) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.lexical.in_constructor_expr)
    (fun b -> set_lexical (fun l -> { l with in_constructor_expr = b }))
    b f

(** [with_rank2_carrier x f] runs [f] with [x] as the carrier of the
    polymorphic function object being generated -- see {!Rank2}.  The extent
    is the lambda's body, so it has to be put back when that body is done. *)
let with_rank2_carrier (x : Id.t option) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.lexical.rank2_carrier)
    (fun x -> set_lexical (fun l -> { l with rank2_carrier = x }))
    x f

(** The carrier of the polymorphic function object being generated, if any. *)
let get_rank2_carrier () = (!tctx).lexical.rank2_carrier

(** [with_itree_mode m f] runs [f] extracting itree-typed terms in mode [m].
    The mode is a property of the declaration being generated, so it has to be
    put back when that declaration is done. *)
let with_itree_mode (m : itree_extraction_mode) (f : unit -> 'a) : 'a =
  with_field
    (fun c -> c.input.itree_mode)
    (fun m -> set_input (fun i -> { i with itree_mode = m }))
    m f

(** {!Representation_plan.region}, which is translation's to name: it reads
    types the way translation converts them. *)
let plan_representation :
    (translation_ctx ->
    Core.Expr.t ->
    (Core_binder.site * int * planned_repr) list * (Core.Occurrence.t * Planned_read.t) list)
    ref =
  ref (fun _ _ -> ([], []))

(** {!Position_plan.region}, which is translation's to name, for the same
    reason as {!plan_representation}. *)
let plan_positions :
    (outer:Lexenv.t -> reads:(Core.Occurrence.t * Planned_read.t) list -> Core.Expr.t ->
      (Core.Occurrence.t * Cpp_ir.Lowered.Type.t option) list)
    ref =
  ref (fun ~outer:_ ~reads:_ _ -> [])

(** [with_region ~owned ~copied ~resumes body f] runs [f], which generates
    [body] as one C++ body owning the variables at the de Bruijn indices
    [owned], its closures owning their copy of those at [copied], lowered as
    a machine resuming at [resumes], if any -- [certain]ly, or perhaps --
    with the moves planned over [body] ({!Ownership_ir.region}), those
    into the frames entering the machine's entries recorded
    ({!Ownership_ir.Entry_moves}). *)
let with_region ?(owned = []) ?(copied = []) ?resumes ?certain (body : Core.Expr.t) (f : unit -> 'a) : 'a =
  let outer = Lexenv.type_opt (!tctx).lexical.env_types in
  let p =
    Ownership_ir.region ~owned ~copied ~outer ?resumes ?certain ~effects:(!tctx).input.unit.effects
      ~n_outer:(List.length (!tctx).lexical.current_type_vars) body
  in
  (* The frames a machine enters its entries by are planned with it. *)
  Ownership_ir.Entry_moves.record_plan p;
  (* A region inside another of the same body -- a lambda's -- was walked
     with it, at the binders outside it as the enclosing walk planned them;
     planning it again from its own scope would read those at the types they
     are bound at, not the ones their matches pinned down.  Its plan only adds
     what the enclosing one has no answer for. *)
  let representation, reads, positions =
    match (!tctx).input.body_owner with
    | Some _ ->
      let binders, reads = !plan_representation !tctx body in
      (* A nested region's positions are planned at its own return type,
         which the enclosing walk does not know; they come first. *)
      let reads = (!tctx).lexical.planned_reads @ reads in
      let positions = !plan_positions ~outer:(!tctx).lexical.env_types ~reads body in
      ((!tctx).lexical.representation @ binders, reads, positions @ (!tctx).lexical.planned_positions)
    | None -> ([], [], [])
  in
  with_field
    (fun c -> (c.lexical.representation, c.lexical.planned_reads, c.lexical.planned_positions))
    (fun (r, rd, ps) ->
      set_lexical (fun l -> { l with representation = r; planned_reads = rd; planned_positions = ps }))
    (representation, reads, positions)
  @@ fun () -> with_field (fun c -> c.lexical.move_plan) (fun p -> set_lexical (fun l -> { l with move_plan = p })) p f

(** [with_plan p f] runs [f] with the moves planned by [p], an alternative
    plan of the region being generated ({!Ownership_ir.reuse_arm}). *)
let with_plan (p : Ownership_ir.t) (f : unit -> 'a) : 'a =
  with_field (fun c -> c.lexical.move_plan) (fun p -> set_lexical (fun l -> { l with move_plan = p })) p f

(** Whether the construction [e] takes the reuse token. *)
let takes_reuse_token e =
  Option.has_some (!tctx).lexical.reuse_token && Ownership_ir.allocation (!tctx).lexical.move_plan e = Reuse

(** [with_reuse_token tok f] runs [f] with [tok] as the Perceus reuse token
    of the arm it generates. *)
let with_reuse_token (tok : Cpp_ir.Lowered.Expr.t option) (f : unit -> 'a) : 'a
    =
  with_field
    (fun c -> c.lexical.reuse_token)
    (fun t -> set_lexical (fun l -> { l with reuse_token = t }))
    tok f

(** Set {!input.current_parameters}. *)
let set_current_parameters (bs : Core_binder.t list) =
  set_input (fun i -> { i with current_parameters = bs })

(** The helpers lifted so far out of the bodies the innermost
    {!collecting_lifted} is generating, newest first, and [None] outside every
    one.  Not a field of {!tctx}: a helper belongs to the generation it was
    lifted in, whatever scope inside that generation lifted it, so no scope
    restores it. *)
let lifted_so_far : Cpp_ir.Lowered.Decl.t list option ref = ref None

(** Lift a declaration out of the body being generated, to the generation
    collecting its helpers ({!collecting_lifted}).

    A helper's identity is the declaration it comes out of and the binder it
    was bound to there ({!Lifted}), so a generation lifting one identity
    twice lifts one helper and keeps the first.  That is sound only where
    both are the same declaration, which [CRANE_CHECK_IR] holds it to. *)
let add_lifted_decl (d : Cpp_ir.Lowered.Decl.t) =
  match !lifted_so_far with
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: a helper was lifted outside every generation that places one.")
  | Some ds -> (
    let same_helper d' =
      match (Cpp_ir.Globrefs.declared d, Cpp_ir.Globrefs.declared d') with
      | Some r, Some r' -> globref_equal r r'
      | _ -> false
    in
    match List.find_opt same_helper ds with
    | None -> lifted_so_far := Some (d :: ds)
    | Some d' ->
      if compare d d' <> 0 then
        Probe.violation "lifted helpers"
          Pp.(
            str "one generation lifted two different helpers as "
            ++ Option.cata GlobRef.print (mt ()) (Cpp_ir.Globrefs.declared d)) )

(** [collecting_lifted f] runs [f] and returns, with its result, the helpers
    lifted out of the bodies it generated, in the order they were lifted: a
    generation's helpers are part of what it generates, for whoever records
    the generation to place. *)
let collecting_lifted f =
  let outer = !lifted_so_far in
  lifted_so_far := Some [];
  Fun.protect
    ~finally:(fun () -> lifted_so_far := outer)
    (fun () ->
      let v = f () in
      (v, List.rev (Option.default [] !lifted_so_far)) )

(** [relift ds] lifts [ds] again, to the generation collecting the current
    body's helpers: a generation that takes another's output takes the
    helpers lifted out of it along with it. *)
let relift ds = List.iter add_lifted_decl ds

(** Run [f] with the whole translation scope restored afterwards, however [f]
    leaves -- returning or raising.

    This is the bracket to reach for at a scope boundary: it saves the context
    wholesale, so it cannot forget a field the way an explicit list of fields
    can.  What [f] produces is not context: the helpers it lifts go to the
    generation collecting them ({!collecting_lifted}).  Use the single-field
    {!with_field} brackets instead where the point is precisely that the rest of
    the scope's effects must escape. *)
let with_scope f =
  let saved = !tctx in
  Fun.protect ~finally:(fun () -> tctx := saved) f

(** Prepend bindings to the de Bruijn environment type stack.
    Also shifts all indices in {!cpp_binder_types} upward by [n] to account
    for the new bindings, keeping de Bruijn references consistent. *)
let push_env_binders (binders : env_binder list) =
  let n = List.length binders in
  let shift m =
    if n > 0 && not (IntMap.is_empty m) then
      IntMap.fold (fun k v acc -> IntMap.add (k + n) v acc) m IntMap.empty
    else m
  in
  set_lexical (fun l -> { l with cpp_binder_types = shift l.cpp_binder_types });
  set_lexical (fun l -> { l with env_types = Lexenv.push binders l.env_types })

(** Prepend value bindings, innermost first. *)
let push_env_types (ids : (Id.t * Core.Type.t) list) =
  push_env_binders (List.map (fun (id, type_) -> { id; type_; role = Value }) ids)

(** Prepend a declaration's parameters, innermost first: each at a class type
    is a dictionary ({!parameter_role}). *)
let push_env_parameters (ids : (Id.t * Core.Type.t) list) =
  push_env_binders
    (List.map (fun (id, type_) -> { id; type_; role = parameter_role type_ }) ids)

(** Restore the de Bruijn environment type stack to a [saved] prefix, undoing
    whatever {!push_env_binders} did to {!cpp_binder_types} in between.

    A caller that saves and restores [env_types] by hand is closing a scope,
    and the binder types have to close with it: the entries for the binders
    being dropped go away, and everything the pushes shifted upward comes back
    down.  Leaving them shifted is worse than leaving them stale -- every
    surviving binder's recorded type then describes some other binder, so a
    concrete value can be read back as a box. *)
let restore_env_types (saved : Lexenv.t) =
  let n = Lexenv.depth (!tctx).lexical.env_types - Lexenv.depth saved in
  if n > 0 && not (IntMap.is_empty (!tctx).lexical.cpp_binder_types) then
    set_lexical (fun l ->
        { l with
          cpp_binder_types =
            IntMap.fold (fun k v acc -> if k > n then IntMap.add (k - n) v acc else acc)
              l.cpp_binder_types IntMap.empty });
  set_lexical (fun l -> { l with env_types = saved })

(** Retrieve the Core type of the variable at de Bruijn index [i] (1-based). *)
let get_env_type (i : int) : Core.Type.t =
  (List.nth ((!tctx).lexical.env_types :> env_binder list) (pred i)).type_

(** The binder at de Bruijn index [i] (1-based), or [None] when [i] is out of
    range (or non-positive). *)
let get_env_binder_opt (i : int) : env_binder option = Lexenv.binder (!tctx).lexical.env_types i

(** Like {!get_env_type} but returns [None] instead of raising when [i] is out
    of range (or non-positive). *)
let get_env_type_opt (i : int) : Core.Type.t option =
  Option.map (fun b -> b.type_) (get_env_binder_opt i)

(** The Core type of the innermost binder named [id], if any. *)
let env_type_of_id (id : Id.t) : Core.Type.t option =
  Option.map (fun b -> b.type_)
    (List.find_opt (fun b -> Id.equal b.id id) ((!tctx).lexical.env_types :> env_binder list))

(** The lexical environment the traversal is generating code in. *)
let current_lexenv () : Lexenv.t = (!tctx).lexical.env_types

(** The Core binder of the variable at de Bruijn index [db] in [env], in the
    definition whose body is being generated ({!Core_binder}): [env] binds
    the definition's Core binders, its parameters first, so the variable's
    level is the number bound outside it.  [site] is the let, bind or
    pattern binding it, where one does. *)
let core_binder ?site env db =
  Option.map
    (fun origin -> Core_binder.make ~origin ~level:(List.length (fst env) - db) ?site ())
    (!tctx).input.body_owner

(** The de Bruijn index of the innermost name [id] in a list of names,
    innermost first, the first numbered [db]; [None] if absent. *)

let rec index_of_name id db = function
  | [] -> None
  | x :: xs -> if Id.equal x id then Some db else index_of_name id (db + 1) xs

(** The Core binders of [params], parameters of a function whose body is
    generated under [env], by name: [env] gives no two binders in scope one
    name, so a parameter's is the binder [env] names so. *)
let parameter_binders env params =
  List.filter_map
    (fun (id, _) ->
      Option.bind (index_of_name id 1 (fst env)) (fun db ->
          Option.map (fun b -> (id, b)) (core_binder env db) ) )
    params

(** The Core binder of the local [id] in scope in [env], by name, as
    {!parameter_binders} has a parameter's, bound at [site] where one is
    given ({!core_binder}). *)
let local_binder ?site env id = Option.bind (index_of_name id 1 (fst env)) (core_binder ?site env)

(** The Core type of the variable at de Bruijn index [i] in [env], where it is
    a parameter of the declaration whose body is being generated
    ({!input.current_parameters}). *)
let parameter_type env i =
  match core_binder env i with
  | Some b when List.exists (Core_binder.equal b) (!tctx).input.current_parameters -> get_env_type_opt i
  | Some _ | None -> None

(** Reset the environment type stack to empty.
    Also clears {!cpp_binder_types} and the head's declared types
    ([declared_outer]). *)
let reset_env_types () =
  set_lexical (fun l -> { l with env_types = Lexenv.empty });
  set_lexical (fun l -> { l with cpp_binder_types = IntMap.empty; declared_outer = None })

(** Run [f] in a fresh escape-analysis scope, restoring the enclosing one
    afterwards.  Escape analysis runs at several nesting levels (lambdas,
    let-in expressions, top-level functions) and each level has its own set of
    safe bindings. *)
let with_escape_analysis f =
  (* Prevent void optimization from leaking into IIFE/lambda bodies: when the
     outer function returns void, gen_stmts generates bare 'return;' for tt,
     but IIFE bodies return their own type (e.g. monostate), not void. *)
  let inner_return_type =
    match current_cpp_return_type () with
    | Some Cpp_ir.Type.Void -> None
    | rt -> rt
  in
  (* A lambda body is not part of the constructor expression that encloses it.
     Both flags make an unresolvable type variable erase to [std::any], which
     is right for a constructor's own arguments and wrong for the body of a
     lambda that merely happens to be one -- the lambda has its own binders
     and its own slots. *)
  with_scope @@ fun () ->
  tctx :=
    { !tctx with
      lexical =
        { (!tctx).lexical with
          move_plan = Ownership_ir.empty;
          in_constructor_expr = false;
          current_cpp_return_type = inner_return_type };
      threaded = {match_param_counter = 0; cs_counter = 0} };
  f ()

(** Bracket for an IIFE that stands in for a SUB-expression (a let-in, a
    fixpoint, or a record destructure in argument position).  The lambda
    returns THIS expression's value, not the enclosing function's, so the
    ambient return type must be re-based on the expression's own expected type
    ([None] wherever the context imposes none).  Without this the enclosing
    function's return type leaks into the IIFE body and its tail expression is
    cast to it — e.g. [any_cast<uint64_t>] on an erased record field that the
    caller then projects with [.first.first]. *)
let with_iife_return_type (expected_ty : Cpp_ir.Lowered.Type.t option) f = with_cpp_return_type expected_ty f
