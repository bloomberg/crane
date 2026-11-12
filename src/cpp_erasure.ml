(** Erasure decisions, and the passes that finish a declaration after the
    seam.

    A value that crosses into a [std::any] has to be read back out at the shape
    it was written in, and how to do that is not always knowable when the cast
    is built: a pair whose components were boxed one at a time is physically a
    [pair<any, any>] however concrete its type says it is, and a cast whose
    target is an associated type of a type-class instance cannot be resolved
    until C++ instantiates the instance.  [crane_any_cast] in
    [theories/cpp/crane_fn.h] handles both by deferring to [if constexpr].

    Translation builds boxes and casts in MiniCpp ({!converting_ctor},
    {!unbox}); which caster a cast is written with is decided once, after the
    seam, over CppIR ({!resolve_casts}), so the printer only spells out what
    the program already says.

    This module is also the single home for the question "is this type spelled
    [std::any]" ({!is_any_shaped_ir}). *)

open Names

(** {2 Axiom types}

    A Rocq axiom has no computational content, so its type extracts to
    [std::any].  The classification is global to a session — the registry is
    populated from each unit's declarations before anything about the unit
    is planned ({!Cpp.prepare_structure}) and read here: a function whose
    type mentions one is never [constexpr], since it may call a throwing
    axiom stub ({!decide_constexpr}). *)

let axiom_type_refs : unit Ref.User.Tbl.t = Ref.User.Tbl.create 16

(** Register a GlobRef as an axiom type. *)
let register_axiom_type (r : GlobRef.t) = Ref.User.Tbl.replace axiom_type_refs r ()

(** Whether a GlobRef has been registered as an axiom type. *)
let is_axiom_type_ref (r : GlobRef.t) = Ref.User.Tbl.mem axiom_type_refs r

(** {2 Building and reading boxes in MiniCpp} *)

module Legacy = struct
  open Minicpp

  (** [erased_list_shape ty] -- see [cpp_erasure.mli]. *)
  let erased_list_shape ty =
    let rec go = function
      | Tnamespace (ns_g, t) -> (
        match go t with
        | Some (g, t') -> Some (g, Tnamespace (ns_g, t'))
        | None -> None )
      | Tglob (g, [elem], _)
        when Ml_type_util.is_list_global g
             && not (Ml_type_util.prints_as_any elem) ->
        Some (g, Tglob (g, [Tany], []))
      | _ -> None
    in
    go ty

  (** [converting_ctor ty args] -- see [cpp_erasure.mli]. *)
  let converting_ctor ty args =
    match args with
    | [inner] when Ml_type_util.prints_as_any ty ->
      (* Boxing a box is two sites each believing they owned the boundary; the
         inner value would then be unreachable, because the consumer casts once.
         Re-box what was inside instead. *)
      let inner = match inner with CPPbox (_, x) -> x | x -> x in
      CPPbox (ty, inner)
    | _ -> CPPconverting_ctor (ty, args)

  (** [empty_box] -- see [cpp_erasure.mli]. *)
  let empty_box = converting_ctor Tany []

  (** [unbox ty e] -- see [cpp_erasure.mli]. *)
  let unbox ty e =
    match e with
    (* [any_cast] to an erased type does not unwrap the box: it asks whether the
       box holds a *further* box, and throws when it does not. *)
    | _ when Ml_type_util.prints_as_any ty -> e
    (* A cast applied straight to a box built here is dead work. *)
    | CPPbox (_, inner) -> inner
    (* Nor is a closure built here a box: [std::any_cast] would wrap it in a
       [std::any] holding the closure type and throw -- a definitional
       instance [:= @id lit], eta-expanded, read back at [Endo<lit>]. *)
    | CPPlambda _ -> e
    | _ -> CPPany_cast (ty, e)

  (** [unbox_tolerant ty e] -- see [cpp_erasure.mli]. *)
  let unbox_tolerant ty e =
    match e with
    | CPPbox (_, inner) -> inner
    | CPPlambda _ -> e
    | _ -> CPPany_cast_tolerant (ty, e)
end

let erased_list_shape = Legacy.erased_list_shape
let converting_ctor = Legacy.converting_ctor
let empty_box = Legacy.empty_box
let unbox = Legacy.unbox
let unbox_tolerant = Legacy.unbox_tolerant

(** {2 The boxedness oracle} *)

open Cpp_ir.Grammar

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type decl = Cpp_ir.Lowered.Decl.t
type phase = Cpp_ir.Lowered.phase

module Map = Cpp_ir.Map
module Types = Cpp_ir.Types

(** Names introduced by [using X = std::any;].  Populated as declarations are
    walked, in the order they are emitted, so an alias is visible exactly where
    C++ would see it. *)
let any_type_aliases : Id.Set.t ref = Cpp_state.owned_ref Id.Set.empty

(** The member aliases the struct being walked declares.  A type-level
    declaration whose body erased -- a higher-kinded class field [memM] among
    them -- is spelled through its file-scope alias, [using memM = std::any];
    inside an instance struct the same name is that struct's own alias
    ([natMMP::memM<A> = A]) and says nothing about a box. *)
let member_aliases : Id.Set.t ref = ref Id.Set.empty

let alias_name = function
  | GlobRef.ConstRef c -> Some (Label.to_id (Constant.label c))
  | _ -> None

(** [is_any_shaped_ir ty] — [ty] is spelled [std::any] in the generated code,
    whether directly, through a type modifier, through an alias introduced by a
    [using] declaration, or because it is an axiom type. *)
let rec is_any_shaped_ir : type p. p Cpp_ir.Type.t -> bool = function
  | Any | Erased _ | Obligation Opaque_type -> true
  | Const inner | Reference (_, inner) | In_namespace (_, inner) -> is_any_shaped_ir inner
  | Named (id, []) -> Id.Set.mem id !any_type_aliases
  | Entity_application (g, _, _)
    when Table.is_erased_type_const g
         && ( match alias_name g with
            | Some id -> not (Id.Set.mem id !member_aliases)
            | None -> false ) ->
    true
  | Entity_application (GlobRef.ConstRef c, _, _) ->
    is_axiom_type_ref (GlobRef.ConstRef c)
    || ( try
           let t = Table.find_type (GlobRef.ConstRef c) in
           t = Miniml.Tunknown || t = Miniml.Taxiom
         with Not_found -> false )
  | _ -> false

let is_any_shaped = is_any_shaped_ir

(** Each unresolved type variable in [ty] spelled [std::any], so that a cast
    target has a C++ spelling. *)
let resolve_tvars_to_any (ty : ty) = Types.map (function Variable (Index (_, None)) -> Any | t -> t) ty

(** Each leaf of [ty] erased, the containers it is made of kept: the cast
    target of an erased container field. *)
let rec erase_type_to_any : ty -> ty = function
  | Entity_application (g, args, ns) when args <> [] -> Entity_application (g, List.map erase_type_to_any args, ns)
  | In_namespace (ns_g, inner) -> In_namespace (ns_g, erase_type_to_any inner)
  | _ -> Any

(** {!erased_list_shape} of a type in CppIR. *)
let erased_list_shape_ir (ty : ty) =
  let rec go : ty -> (GlobRef.t * ty) option = function
    | In_namespace (ns_g, t) -> (
      match go t with Some (g, t') -> Some (g, In_namespace (ns_g, t')) | None -> None )
    | Entity_application (g, [elem], _) when Ml_type_util.is_list_global g && not (Types.prints_as_any elem) ->
      Some (g, Entity_application (g, [Any], []))
    | _ -> None
  in
  go ty

(** The instance parameter a type is qualified under, if any. *)
let rec instance_dependent : ty -> (Id.t * GlobRef.t) option = function
  | Member (base, _) | Apply (base, _) -> instance_dependent base
  | Instance (id, class_ref) -> Some (id, class_ref)
  | _ -> None

(** [needs_deep_recovery ty] — recovering a [ty] from a box needs the tolerant
    caster rather than a plain [std::any_cast].  A pair with a concrete
    component may have had its components boxed one at a time, so the box holds
    [pair<any, any>] and each component has to be recovered in turn.  An
    all-erased pair is stored as itself and needs no such walk. *)
let needs_deep_recovery : ty -> bool = function
  | Entity_application (g, ([_; _] as args), _) ->
    Ml_type_util.is_prod_global g && List.exists (fun a -> not (is_any_shaped a)) args
  | _ -> false

(** [tolerant ty] — a cast to [ty] cannot be resolved now and must defer to
    [crane_any_cast].  A bare type variable is one: instantiated at
    [std::any] -- [trigger]'s answer type under an erased interpretation --
    a plain [std::any_cast<std::any>] looks for a box inside the box. *)
let tolerant (ty : ty) =
  instance_dependent ty <> None || needs_deep_recovery ty || match ty with Variable _ -> true | _ -> false

(** [is_method n] -- [n] is rendered as a member function: one the registry
    found in its up-front scan, which every candidate a render collects is
    ({!Method_registry.planned_candidate}). *)
let is_method (n : GlobRef.t) : bool = Cpp_state.is_registered_method n <> None

(** [returns_a_box e] -- [e] is a call whose result is declared [std::any], so
    reading it at a concrete type needs a cast.  Method results are the only
    boxed-return positions the registry tracks; an application through the
    erased convention counts too, since that convention hands back a box. *)
let returns_a_box : expr -> bool = function
  | Access_call (Arrow, Entity (n, _, _), _, _) -> Cpp_state.method_returns_any n
  | Call (_, Entity (n, _, _), _) when is_method n -> Cpp_state.method_returns_any n
  | Call (_, Project (_, n, _), _) -> Cpp_state.method_returns_any n
  | Erased_call _ -> true
  | _ -> false

(** [castable_to ty] -- [ty] names something [any_cast] can ask for.  A type
    variable or an unresolved type does not. *)
let rec castable_to : ty -> bool = function
  | Variable _ -> false
  | Obligation _ | Any | Auto -> false
  | Const inner -> castable_to inner
  | Entity_application (GlobRef.ConstRef _, _, _) -> false
  | _ -> true

(** {2 Rewriting} *)

(** The rewrite applying [expr], [stmt] and [type_] to each child. *)
let rewriter ?stmts ~expr ~stmt ~type_ () : phase Map.t = Map.make ?stmts ~expr ~stmt ~type_ ()

let same_type (t : ty) = t

(** A call of [f] on [args], with nothing known of its signature. *)
let call (f : expr) (args : expr list) : expr =
  Call ({yields = Untyped; params = Unknown; constructs = None; occurrence = None}, f, args)

(** Whether a lambda's body names its scope, and whether it names [this]:
    what it must capture.  A variable a nested lambda reads from outside
    itself counts. *)
let lambda_needs_capture (params : (ty * Id.t option) list) (body : stmt list) : bool * bool =
  let names ps = List.fold_left (fun acc (_, x) -> match x with Some id -> Id.Set.add id acc | None -> acc) Id.Set.empty ps in
  let param_names = names params in
  let uses_this = ref false in
  let rec collect_from_expr (refs, decls) (e : expr) =
    match e with
    | Local id -> (Id.Set.add id refs, decls)
    | Dereference e -> collect_from_expr (refs, decls) e
    | This | Shared_from_this _ ->
      uses_this := true;
      (refs, decls)
    | Lambda {params = inner_params; body = inner_body; _} ->
      let inner_refs, inner_decls = List.fold_left collect_from_stmt (Id.Set.empty, Id.Set.empty) inner_body in
      let inner_free = Id.Set.diff inner_refs (Id.Set.union (names inner_params) inner_decls) in
      (Id.Set.union refs inner_free, decls)
    | _ ->
      let acc = ref (refs, decls) in
      Cpp_ir.Subterms.expr
        ~expr:(fun e' -> acc := collect_from_expr !acc e')
        ~stmts:(fun stmts -> acc := List.fold_left collect_from_stmt !acc stmts)
        e;
      !acc
  and collect_from_stmt (refs, decls) (s : stmt) =
    match s with
    | Declare (id, _, _) -> (refs, Id.Set.add id decls)
    | Bind_variable (id, binding, e) -> (
      let refs', decls' = collect_from_expr (refs, decls) e in
      match binding with
      | Declare _ | Declare_static _ -> (refs', Id.Set.add id decls')
      | Existing -> (Id.Set.add id refs', decls') )
    | Assign (lhs, e) ->
      let refs', decls' = collect_from_expr (refs, decls) lhs in
      collect_from_expr (refs', decls') e
    | Custom_match m ->
      List.fold_left
        (fun (r, d) (b : phase Custom_match.branch) ->
          let branch_decls = List.fold_left (fun acc (p : phase Custom_match.param) -> Id.Set.add p.name acc) d b.params in
          List.fold_left collect_from_stmt (r, branch_decls) b.body )
        (collect_from_expr (refs, decls) m.scrutinee)
        m.branches
    | Foreign_block b ->
      let refs', decls' = List.fold_left collect_from_expr (refs, decls) b.values in
      (refs', Id.Set.add b.result decls')
    | Match (scrut, branches, default) -> (
      let refs, decls = collect_from_expr (refs, decls) scrut.expr in
      let acc =
        List.fold_left
          (fun acc (br : phase Match.branch) ->
            let refs', decls' = List.fold_left collect_from_expr acc br.extra_conditions in
            let branch_decls =
              let d = List.fold_left (fun d (fb : phase Match.field_binding) -> Id.Set.add fb.name d) decls' br.field_bindings in
              match br.var with Some id -> Id.Set.add id d | None -> d
            in
            List.fold_left collect_from_stmt (refs', branch_decls) br.body )
          (refs, decls) branches
      in
      match default with Some stmts -> List.fold_left collect_from_stmt acc stmts | None -> acc )
    | _ ->
      let acc = ref (refs, decls) in
      Cpp_ir.Subterms.stmt
        ~expr:(fun e -> acc := collect_from_expr !acc e)
        ~stmts:(fun stmts -> acc := List.fold_left collect_from_stmt !acc stmts)
        s;
      !acc
  in
  let all_refs, local_decls = List.fold_left collect_from_stmt (Id.Set.empty, Id.Set.empty) body in
  let free_vars = Id.Set.diff all_refs (Id.Set.union param_names local_decls) in
  ((not (Id.Set.is_empty free_vars)) || !uses_this, !uses_this)

(** Whether [e] holds a lambda that captures, read off the captures as
    written down ({!decide_captures}). *)
let rec expr_contains_capturing_lambda (e : expr) : bool =
  match e with
  | Lambda {capture = Written Nothing; body; _} -> List.exists stmt_contains_capturing_lambda body
  | Lambda {capture = Written (By_reference | By_copy _); _} -> true
  | Lambda {capture = Runs_in_place | Stored; _} ->
    invalid_arg "Cpp_erasure.expr_contains_capturing_lambda: a capture not written down"
  | _ ->
    let exception Found in
    ( try
        Cpp_ir.Subterms.expr
          ~expr:(fun e' -> if expr_contains_capturing_lambda e' then raise Found)
          ~stmts:(fun stmts -> if List.exists stmt_contains_capturing_lambda stmts then raise Found)
          e;
        false
      with Found -> true )

and stmt_contains_capturing_lambda (s : stmt) : bool =
  let exception Found in
  try
    Cpp_ir.Subterms.stmt
      ~expr:(fun e -> if expr_contains_capturing_lambda e then raise Found)
      ~stmts:(fun stmts -> if List.exists stmt_contains_capturing_lambda stmts then raise Found)
      s;
    false
  with Found -> true

(** {2 Casts} *)

(** The printable phase of a declaration: a lowered declaration whose every
    type has the representation it is written with.  {!materialise} is its
    only producer. *)
type settled = decl

(** Record any [std::any] alias a declaration introduces, so that later casts
    in the same emission order can see it. *)
let note_alias id ty = if is_any_shaped ty then any_type_aliases := Id.Set.add id !any_type_aliases

(** [applies_erased_callee e] -- [e] applies a callable that was recovered
    from a box, so its result is a box too however concrete the position it
    lands in is. *)
let applies_erased_callee : expr -> bool = function Erased_call _ -> true | _ -> false

(** [boxed_var boxed e] -- [e] reads a binder that is declared [std::any]. *)
let rec boxed_var boxed : expr -> bool = function
  | Local id -> Id.Set.mem id boxed
  | Move e -> boxed_var boxed e
  | _ -> false

(** [unbox_ir ty e] is {!unbox} in CppIR. *)
let unbox_ir (ty : ty) (e : expr) : expr =
  match e with
  | _ when Types.prints_as_any ty -> e
  | Box (_, inner) -> inner
  | Lambda _ -> e
  | _ -> Any_cast (ty, e)

(* [boxed] is the set of binders in scope whose declared type is [std::any].
   It is threaded through the walk so that a binder is boxed exactly where
   C++ would see its declaration.  [ret] is the enclosing lambda's declared
   return type, or [None] outside one. *)
let rec resolve_expr boxed (e : expr) : expr =
  match e with
  | Any_cast (ty, inner) ->
    let inner = resolve_expr boxed inner in
    if is_any_shaped ty then
      (* Casting a box to [std::any] is the identity, not a cast: [any_cast]
         would look for a further [std::any] stored inside and throw. *)
      inner
    else if tolerant ty then Tolerant_any_cast (ty, inner)
    else Any_cast (ty, inner)
  | Lambda l ->
    let boxed =
      List.fold_left
        (fun acc (ty, id_opt) -> match id_opt with Some id when is_any_shaped ty -> Id.Set.add id acc | _ -> acc)
        boxed l.params
    in
    Lambda {l with body = List.map (resolve_stmt ~ret:l.return_type boxed) l.body}
  | _ ->
    Map.expr
      (rewriter ~expr:(resolve_expr boxed) ~stmt:(resolve_stmt ~ret:None boxed) ~type_:same_type ())
      e

and resolve_stmt ?(ret = None) boxed (s : stmt) : stmt =
  (match s with Local_type_alias (id, ty) -> note_alias id ty | _ -> ());
  match s with
  (* A lambda that returns one of its own boxed parameters has to unbox it to
     reach the declared return type -- [std::function<uint64_t(std::any)>]
     does not compile otherwise.  Only a bare parameter: an any-returning call
     in the same position is already correctly typed in loopified bodies, and
     casting it would silently change the value (regression:
     tests/regression/loopify_variant_self_assign and friends). *)
  | Return (Some e)
    when (match ret with Some t -> castable_to t | None -> false) && (boxed_var boxed e || applies_erased_callee e) ->
    let t = resolve_tvars_to_any (Option.get ret) in
    Return (Some (resolve_expr boxed (Any_cast (t, e))))
  | Custom_match m ->
    let branches =
      List.map
        (fun (b : phase Custom_match.branch) ->
          let boxed =
            List.fold_left
              (fun acc (p : phase Custom_match.param) -> if is_any_shaped p.type_ then Id.Set.add p.name acc else acc)
              boxed b.params
          in
          {b with body = List.map (resolve_stmt ~ret boxed) b.body} )
        m.branches
    in
    Custom_match {m with scrutinee = resolve_expr boxed m.scrutinee; branches}
  | _ -> Map.stmt (rewriter ~expr:(resolve_expr boxed) ~stmt:(resolve_stmt ~ret boxed) ~type_:same_type ()) s

let resolve_expr = resolve_expr Id.Set.empty
let resolve_stmt = resolve_stmt ~ret:None Id.Set.empty
let resolving = rewriter ~expr:resolve_expr ~stmt:resolve_stmt ~type_:same_type ()

let rec resolve_field ((f, vis, tag) as field : phase Field.member) : phase Field.member =
  match f with
  | Nested_type_alias ([], id, ty) ->
    note_alias id ty;
    field
  | Nested_struct (id, fields) -> (Nested_struct (id, List.map resolve_field fields), vis, tag)
  | _ -> Map.member resolving field

let rec resolve_casts (d : settled) : settled =
  match d with
  (* Spelled out rather than left to [Map.decl] only where the alias registry
     has to see a field, or where the recursion must be into [resolve_casts]
     itself so that it does. *)
  | Template (tps, constr, inner) ->
    let inner = resolve_casts inner in
    Template (tps, Option.map resolve_expr constr, inner)
  | Namespace (r, decls) -> Namespace (r, List.map resolve_casts decls)
  | Struct s ->
    let declared =
      List.fold_left
        (fun acc ((f, _, _) : phase Field.member) ->
          match f with Nested_type_alias (_, id, _) -> Id.Set.add id acc | _ -> acc )
        Id.Set.empty s.fields
    in
    let saved = !member_aliases in
    member_aliases := Id.Set.union declared saved;
    let fields =
      Fun.protect ~finally:(fun () -> member_aliases := saved) (fun () -> List.map resolve_field s.fields)
    in
    Struct {s with fields}
  (* A constant initialised from a boxed call has to unbox to reach its own
     declared type; saying it in the program means the cast goes through the
     normalisation above like every other one. *)
  | Variable ({type_ = ty; init = e; _} as a) when returns_a_box e && castable_to ty ->
    Variable {a with init = resolve_expr (unbox_ir (resolve_tvars_to_any ty) e)}
  | _ -> Map.decl resolving d

(** {2 Reading boxed values}

    A value in a [std::any] is read back at a known type by an explicit
    {!Cpp_ir.Grammar.Expr.Unbox}.  Which binders hold boxes is read off their
    declared types -- a parameter, lambda parameter, match binding or
    custom-match branch parameter typed [std::any] -- and a custom pair match
    on a boxed scrutinee says that its branch parameters are boxed too,
    holding values of their declared types.  Reads are then made explicit
    where the context expects a concrete type: a custom template's argument
    or scrutinee, and every use of a branch parameter that holds a known type
    in a box. *)

type reads = {
  boxed : Id.Set.t;  (** binders holding a [std::any] *)
  stored : ty Id.Map.t;
      (** binders holding a value of this type in a box: read at it on every
          use *)
}

let no_reads = {boxed = Id.Set.empty; stored = Id.Map.empty}

let with_boxed_params r params =
  { r with
    boxed = List.fold_left (fun acc (id, ty) -> if is_any_shaped ty then Id.Set.add id acc else acc) r.boxed params }

(* A type a value can be cast to: not a variable, not unknown, not a constant
   whose definition may itself be [std::any]. *)
let rec is_concrete : ty -> bool = function
  | Variable _ | Obligation _ | Any | Auto -> false
  | Const inner -> is_concrete inner
  | Entity_application (GlobRef.ConstRef _, _, _) -> false
  | _ -> true

(* A call that hands back a box: a method registered as returning
   [std::any], or an erased call. *)
let returns_box : expr -> bool = function
  | Access_call (Arrow, Entity (n, _, _), _, _) -> Cpp_state.method_returns_any n
  | Call (_, Entity (n, _, _), _) when Cpp_names.lookup_method_this_pos n <> None -> Cpp_state.method_returns_any n
  | Call (_, Project (_, n, _), _) -> Cpp_state.method_returns_any n
  | Erased_call _ -> true
  | _ -> false

let rec is_boxed_binder r : expr -> bool = function
  | Local id -> Id.Set.mem id r.boxed && not (Id.Map.mem id r.stored)
  | Move e -> is_boxed_binder r e
  | _ -> false

(* [read_as r original e expected] -- [e], the rewritten [original], read at
   [expected] where [original] is a box and [expected] is concrete. *)
let read_as r original (e : expr) expected : expr =
  if (returns_box original || is_boxed_binder r original) && is_concrete expected then
    Unbox (To (resolve_tvars_to_any expected), e)
  else e

(* A use of a binder holding a value of type [ty] in a box. *)
let read_stored id (ty : ty) : expr =
  let resolved = resolve_tvars_to_any ty in
  match erased_list_shape_ir resolved with
  | Some (g, flat) ->
    (* A custom list's erased shape is a deque of bare boxes; a converting
       read would re-box it.  Another list converts from its flat form. *)
    if Table.is_custom g then Unbox (To flat, Local id) else Unbox (List (resolved, flat), Local id)
  | None -> (
    match ty with
    | Member _ | Entity_application (GlobRef.ConstRef _, _, _) -> Unbox (Or_keep ty, Local id)
    | _ -> Unbox (To resolved, Local id) )

let rec reads_expr r (e : expr) : expr =
  let ex = reads_expr r in
  match e with
  | Local id when Id.Map.mem id r.stored -> read_stored id (Id.Map.find id r.stored)
  (* The cast already names the type; the binder is read bare inside it. *)
  | Any_cast (_, Local id) when Id.Map.mem id r.stored -> e
  | Lambda l ->
    let r' = with_boxed_params r (List.filter_map (fun (ty, id) -> Option.map (fun id -> (id, ty)) id) l.params) in
    Map.expr (reads r') e
  | Call (res, (Entity (_, _, Some {inline = Some {form = Templated; _}; _}) as f), args) ->
    let expected = match res.params with Types ts -> ts | Unknown -> [] in
    let arg i a = match List.nth_opt expected i with Some exp -> read_as r a (ex a) exp | None -> ex a in
    let args = List.mapi arg args in
    Call (res, ex f, args)
  | _ -> Map.expr (reads r) e

and reads_stmt r (s : stmt) : stmt =
  let ex = reads_expr r and st = reads_stmt r in
  match s with
  | Match (scrut, branches, default) ->
    let branch (b : phase Match.branch) =
      let r' = with_boxed_params r (List.map (fun (fb : phase Match.field_binding) -> (fb.name, fb.type_)) b.field_bindings) in
      {b with body = List.map (reads_stmt r') b.body}
    in
    let default = Option.map (List.map st) default in
    let branches = List.map branch branches in
    Match ({scrut with expr = ex scrut.expr}, branches, default)
  | Custom_match m -> reads_custom_match r m
  | _ -> Map.stmt (reads r) s

and reads r = rewriter ~expr:(reads_expr r) ~stmt:(reads_stmt r) ~type_:same_type ()

(* A custom match.  A pair match on a boxed scrutinee reads the pair at
   [pair<any, any>] -- what a boxed pair holds -- so its type arguments are
   [std::any] and its branch parameters are boxes. *)
and reads_custom_match r (m : phase Custom_match.t) : stmt =
  let typ = m.return_type and scrut = m.scrutinee in
  let tokens = Foreign_template.match_template m.template in
  let prod_of : ty -> GlobRef.t option = function
    | Entity_application (g, _, _) when Ml_type_util.is_prod_global g -> Some g
    | _ -> None
  in
  let erased_pair g : ty = Entity_application (g, [Any; Any], []) in
  let scrut_boxed = match scrut with Local id -> Id.Set.mem id r.boxed | _ -> false in
  let known_prod =
    match scrut with
    | Any_cast (ty, _) when prod_of ty <> None -> prod_of ty
    | _ -> (
      match typ with Entity_application (g, _ :: _, _) when Ml_type_util.is_prod_global g -> Some g | _ -> prod_of typ )
  in
  let preset =
    match scrut with
    | Any_cast (ty, _) -> prod_of ty <> None
    | Local _ when scrut_boxed -> (
      match typ with Entity_application (g, _ :: _, _) -> Ml_type_util.is_prod_global g | _ -> false )
    | _ -> false
  in
  let has_scrut = List.mem Foreign_template.CCscrut tokens in
  let effective, at_scrut =
    match (scrut, typ) with
    | Local _, Entity_application (g, _ :: _, _) when scrut_boxed && Ml_type_util.is_prod_global g ->
      (erased_pair g, true)
    | Local _, _ when scrut_boxed ->
      if Ml_type_util.is_prod_global m.inductive then
        ((match known_prod with Some g -> erased_pair g | None -> typ), true)
      else (typ, false)
    | Any_cast (ty, _), _ when prod_of ty <> None -> (erased_pair (Option.get (prod_of ty)), true)
    | _ -> (typ, false)
  in
  let overridden = preset || (has_scrut && at_scrut) in
  (* The type arguments a template spells before its scrutinee are read
     before the override is known, unless it was known from the start. *)
  let ty_arg_before_scrut =
    let rec go = function
      | [] -> false
      | Foreign_template.CCscrut :: _ -> false
      | (Foreign_template.CCty_arg _ | Foreign_template.CCelem _) :: _ -> true
      | _ :: rest -> go rest
    in
    go tokens
  in
  let type_args =
    if overridden && (preset || not ty_arg_before_scrut) then List.map (fun _ : ty -> Any) m.type_args
    else m.type_args
  in
  let scrut' = if has_scrut then read_as r scrut (reads_expr r scrut) effective else scrut in
  let scrut_is_cast_pair =
    match scrut with Any_cast (Entity_application (g, _, _), _) -> Ml_type_util.is_prod_global g | _ -> false
  in
  let branch (b : phase Custom_match.branch) : phase Custom_match.branch =
    let r' = with_boxed_params r (List.map (fun (p : phase Custom_match.param) -> (p.name, p.type_)) b.params) in
    let r' =
      if overridden || scrut_is_cast_pair then
        List.fold_left
          (fun r' ({name = id; type_ = ty; _} : phase Custom_match.param) ->
            let is_pair = match ty with Entity_application (g, _ :: _, _) -> Ml_type_util.is_prod_global g | _ -> false in
            if is_any_shaped ty || is_pair then {r' with boxed = Id.Set.add id r'.boxed}
            else
              let erased : ty =
                match ty with
                | Entity_application (g, args, ns) when args <> [] ->
                  Entity_application (g, List.map erase_type_to_any args, ns)
                | In_namespace (g, inner) -> In_namespace (g, erase_type_to_any inner)
                | t -> t
              in
              {r' with stored = Id.Map.add id erased r'.stored} )
          r' b.params
      else r'
    in
    {b with body = List.map (reads_stmt r') b.body}
  in
  Custom_match {m with scrutinee = scrut'; type_args; branches = List.map branch m.branches}

let reads_method r (m : phase Method.t) =
  let r' = with_boxed_params {r with boxed = Id.Set.empty} m.params in
  {m with body = List.map (reads_stmt r') m.body}

let rec reads_decl (d : settled) : settled =
  match d with
  | Template (tps, c, inner) -> Template (tps, c, reads_decl inner)
  | Namespace (r, ds) -> Namespace (r, List.map reads_decl ds)
  | Function ({shape = Definition (params, body); _} as f) ->
    let r = with_boxed_params no_reads params in
    Function {f with shape = Definition (params, List.map (reads_stmt r) body)}
  | _ -> (
    let rec field ((f, vis, tag) : phase Field.member) : phase Field.member =
      let f : phase Field.t =
        match f with
        | Method m -> Method (reads_method no_reads m)
        | Out_of_line_declaration (Method m) -> Out_of_line_declaration (Method (reads_method no_reads m))
        | Nested_struct (id, fs) -> Nested_struct (id, List.map field fs)
        | f -> f
      in
      (f, vis, tag)
    in
    match d with
    | Struct s -> Struct {s with fields = List.map field s.fields}
    | Merged_struct_members s -> Merged_struct_members {s with fields = List.map field s.fields}
    | Member_definition ({member = Method m; _} as md) -> Member_definition {md with member = Method (reads_method no_reads m)}
    | d -> Map.decl (reads no_reads) d )

let lower_boxed_reads (d : settled) : settled = reads_decl d

(** {2 Supplying template arguments} *)

(* [tys] extended with [std::any] for each argument past its end that a
   template parsed into [tokens] names. *)
let supplied tokens (tys : ty list) =
  let missing = Foreign_template.type_arity tokens - List.length tys in
  if missing > 0 then tys @ List.init missing (fun _ : ty -> Any) else tys

(* A mapped type takes its arguments as the printer reads them: a mapping
   that does not say where they go takes those it is given
   ({!Foreign_template.custom_template_with_args}).  A type constructor named
   unapplied is left as it is: the printer names it by the arguments it has,
   positionally. *)
let rec supply_type_args (t : ty) : ty =
  Types.rewrite
    (fun (t : ty) ->
      match t with
      | Type_constructor _ -> Some t
      | Entity_application (r, tys, args) when Table.to_inline r -> (
        match Table.find_custom_opt r with
        | Some s ->
          let tokens = Foreign_template.term_template (Foreign_template.custom_template_with_args s (List.length tys)) in
          Some (Entity_application (r, supplied tokens (List.map supply_type_args tys), args))
        | None -> None )
      | _ -> None )
    t

(* [%ret] spells the type a call yields: only a template applied as a call
   has one, and only where translation recorded it.  Refused here, before
   anything is printed, wherever it has none. *)
let names_ret text = List.mem Foreign_template.CCret (Foreign_template.term_template text)

let refuse_ret r why = CErrors.user_err Pp.(str "Crane: the mapping " ++ GlobRef.print r ++ str " names %ret" ++ str why)

let in_block = " in a block template."

let check_ret : expr -> unit = function
  | Call (res, Entity (r, _, Some {inline = Some tmpl; _}), _) when names_ret tmpl.text -> (
    match (tmpl.form, res.yields) with
    | Templated, Yields _ -> ()
    | Templated, Untyped -> refuse_ret r ", but the type its call yields is not known here."
    | (Block | Bare_callee), _ -> refuse_ret r in_block )
  | Entity (r, _, Some {inline = Some {form = Block; text; _}; _}) when names_ret text -> refuse_ret r in_block
  | _ -> ()

(** The text of a custom match's template, as its scrutinee is held. *)
let custom_match_text (m : phase Custom_match.t) =
  match m.hold with
  | Owned when Foreign_template.structured_binding m.template <> None -> Foreign_template.bound_by_value m.template
  | Owned | Borrowed -> m.template

let supply_template_args (d : settled) : settled =
  let rec fe (e : expr) : expr =
    check_ret e;
    match e with
    | Entity (r, tys, (Some {inline = Some tmpl; _} as ci)) ->
      Entity (r, supplied (Foreign_template.term_template tmpl.text) (List.map supply_type_args tys), ci)
    | e -> Map.expr (rw ()) e
  and fs (s : stmt) : stmt =
    match Map.stmt (rw ()) s with
    | Foreign_block b ->
      if names_ret b.template then refuse_ret b.custom in_block;
      Foreign_block {b with type_args = supplied (Foreign_template.term_template b.template) b.type_args}
    | Custom_match c ->
      let tokens = Foreign_template.match_template (custom_match_text c) in
      Custom_match {c with type_args = supplied tokens c.type_args}
    | s -> s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:supply_type_args () in
  Map.decl (rw ()) d

(** {2 Instantiating mappings} *)

(** Whether [ty] recurses through a container with a [Boxed Element]
    wrapper. *)
let rec recurses_boxed : ty -> bool = function
  | Entity_application (r, args, _) | Foreign {custom = r; types = args; _} ->
    Table.is_boxed_recursive_ind r || List.exists recurses_boxed args
  | In_namespace (_, t) -> recurses_boxed t
  | _ -> false

(* The inductive whose mapping a constructor's text belongs to, where a
   [Boxed Element] wrapper is declared. *)
let container_of = function GlobRef.ConstructRef (ind, _) -> GlobRef.IndRef ind | r -> r

let wrapper_pieces wrapper : Cpp_ir.Foreign.wrapper_piece list =
  List.map
    (function
      | Foreign_template.CCstring s -> Cpp_ir.Foreign.Wrapper_text s
      | CCty_arg 0 | CCelem 0 -> Wrapper_element
      | CCty_arg i -> Wrapper_text (Printf.sprintf "%%t%d" i)
      | CCelem i -> Wrapper_text (Printf.sprintf "%%elem%d" i)
      | _ -> CErrors.anomaly (Pp.str "wrapper_pieces: a wrapper is a type template") )
    (Foreign_template.type_template wrapper)

let foreign_pieces ~element tokens : Cpp_ir.Foreign.piece list =
  List.map
    (function
      | Foreign_template.CCstring s -> Cpp_ir.Foreign.Text s
      | CCty_arg i -> Type_argument i
      | CCelem i -> Element (i, element i)
      | CCarg i -> Value i
      | CCret -> Yields
      | CCresult -> Result
      | CCscrut | CCty | CCbody _ | CCbr_var _ | CCbr_var_ty _ ->
        CErrors.anomaly (Pp.str "foreign_pieces: a match template's hole in a type or term template") )
    tokens

(* The wrapper the element hole [i] of [r]'s text, applied at [tys], is
   written inside: where it holds an element recursing through the container. *)
let boxed_by ~boxing r (tys : ty list) i =
  if boxing && recurses_boxed (Option.default (Any : ty) (List.nth_opt tys i)) then
    Table.find_boxed_wrapper_opt (container_of r)
  else None

let is_templated : phase Cpp_ir.Foreign.custom option -> bool = function
  | Some {inline = Some {form = Templated; _}; _} -> true
  | _ -> false

(** The form an inline mapping's text is written in. *)
let form_of_text s = (Legacy_minicpp_to_cpp_ir.inline_template (Minicpp.inline_template s)).form

let rec instantiated_type ~boxing (t : ty) : ty =
  Types.rewrite
    (fun (t : ty) ->
      match t with
      (* A constructor removed from the output ([Crane Extract Skip], or a
         skipped module's) is the identity on what it is applied to: its
         argument is the whole of what there is to write. *)
      | Apply (Entity_application (r, _, _), [arg]) when Ml_type_util.ref_has_no_cpp_name r ->
        Some (instantiated_type ~boxing arg)
      (* Written through the inductive's own head. *)
      | In_namespace ((GlobRef.IndRef _ as r), Entity_application (r', tys, args)) when Common.globref_equal r r' ->
        let args = List.map (instantiated_expr ~boxing) args in
        Some (In_namespace (r, Entity_application (r', List.map (instantiated_type ~boxing) tys, args)))
      | Entity_application (r, tys, args) -> (
        match Table.inline_custom_text r with
        (* An empty text is a global removed from the output, written as
           its arguments alone ({!Ml_type_util.ref_has_no_cpp_name}). *)
        | Some s when s <> "" ->
          let tokens = Foreign_template.term_template (Foreign_template.custom_template_with_args s (List.length tys)) in
          Some (Foreign (instantiated_foreign ~boxing r tokens tys args None))
        | Some _ | None ->
          let args = List.map (instantiated_expr ~boxing) args in
          Some (Entity_application (r, List.map (instantiated_type ~boxing) tys, args)) )
      | Type_of e -> Some (Type_of (instantiated_expr ~boxing e))
      | _ -> None )
    t

(* Each element hole is decided on the argument the use supplies, before
   that argument is itself instantiated. *)
and instantiated_foreign ~boxing r tokens tys values yields : phase Cpp_ir.Foreign.t =
  let element i = Option.map wrapper_pieces (boxed_by ~boxing r tys i) in
  let pieces = foreign_pieces ~element tokens in
  let yields = Option.map (instantiated_type ~boxing) yields in
  let values = List.map (instantiated_expr ~boxing) values in
  let types = List.map (instantiated_type ~boxing) tys in
  {custom = r; types; values; yields; pieces}

(* A [%result] block's statements, each element hole decided on the
   argument the use supplies. *)
and instantiated_block ~boxing r text tys values yields : phase Cpp_ir.Foreign.t =
  let element i = Option.map wrapper_pieces (boxed_by ~boxing r tys i) in
  let pieces =
    List.concat_map
      (fun stmt -> foreign_pieces ~element stmt @ [Cpp_ir.Foreign.Statement_end])
      (Foreign_template.block_statements text)
  in
  let yields = Option.map (instantiated_type ~boxing) yields in
  let values = List.map (instantiated_expr ~boxing) values in
  let types = List.map (instantiated_type ~boxing) tys in
  {custom = r; types; values; yields; pieces}

(* A text with no hole, applied to the type arguments [tys]: [text<t0, t1>]. *)
and bare_callee ~boxing r text tys : phase Cpp_ir.Foreign.t =
  let applied : Cpp_ir.Foreign.piece list =
    match tys with
    | [] -> []
    | _ ->
      [Cpp_ir.Foreign.Text "<"]
      @ List.concat (List.mapi (fun i _ -> (if i > 0 then [Cpp_ir.Foreign.Text ", "] else []) @ [Type_argument i]) tys)
      @ [Cpp_ir.Foreign.Text ">"]
  in
  let pieces = Cpp_ir.Foreign.Text text :: applied in
  {custom = r; types = List.map (instantiated_type ~boxing) tys; values = []; yields = None; pieces}

and instantiated_expr ~boxing (e : expr) : expr =
  match e with
  | Call (res, Entity (n, tys, Some {inline = Some ({form = Templated; _} as tmpl); _}), args) ->
    let tokens = Foreign_template.term_template tmpl.text in
    (* An argument past the last one the text names is not its own: the
       call's result is applied to it. *)
    let named = List.fold_left (fun n -> function Foreign_template.CCarg i -> max n (i + 1) | _ -> n) 0 tokens in
    let yields = match res.yields with Yields t -> Some t | Untyped -> None in
    Foreign (Call, instantiated_foreign ~boxing n tokens tys (CList.firstn (min named (List.length args)) args) yields)
  | Entity (x, tys, Some {inline = Some {form = Block; text; _}; custom_yields}) ->
    value_block (instantiated_block ~boxing x text tys [] custom_yields)
  (* Every argument of a block's call is its own, spliced or not. *)
  | Call (res, Entity (n, tys, Some {inline = Some {form = Block; text; _}; _}), args) ->
    let yields = match res.yields with Yields t -> Some t | Untyped -> None in
    value_block (instantiated_block ~boxing n text tys args yields)
  (* A text that places nothing is a callee: the call stays a call, of the
     text applied to the type arguments, and its arguments are written as a
     call's, not spliced. *)
  | Call (res, Entity (n, tys, Some {inline = Some {form = Bare_callee; text; _}; _}), args) ->
    Map.expr (instantiating ~boxing) (Call (res, Foreign (Constant, bare_callee ~boxing n text tys), args))
  | Entity (x, tys, (Some {inline = Some tmpl; _} as ci)) when is_templated ci ->
    Foreign (Constant, instantiated_foreign ~boxing x (Foreign_template.type_template tmpl.text) tys [] None)
  (* Not applied, a callee is its text as it stands. *)
  | Entity (x, _, Some {inline = Some {form = Bare_callee; text; _}; _}) ->
    Foreign (Constant, bare_callee ~boxing x text [])
  (* Spelled as a value, a mapped qualifier is its text as written, given
     no arguments it does not place itself. *)
  | Type_member (Entity_application (r, tys, []), id) when Table.inline_custom_text r <> None -> (
    match Table.inline_custom_text r with
    | Some s when form_of_text s = Templated ->
      Type_member (Foreign (instantiated_foreign ~boxing r (Foreign_template.type_template s) tys [] None), id)
    | Some s when form_of_text s = Bare_callee -> Type_member (Foreign (bare_callee ~boxing r s []), id)
    | Some _ | None -> Type_member (Entity_application (r, List.map (instantiated_type ~boxing) tys, []), id) )
  (* For a callee generic over the element, whose declaration never boxes
     it. *)
  | Container_cast (t, e', suppress) ->
    let e' = instantiated_expr ~boxing e' in
    Container_cast (instantiated_type ~boxing:(boxing && not suppress) t, e', suppress)
  | e -> Map.expr (instantiating ~boxing) e

(* A block used as a value runs where it is written: the lambda it is
   written as captures by reference the locals its arguments read, which
   are spliced into its body, or nothing. *)
and value_block (fr : phase Cpp_ir.Foreign.t) : expr =
  let reads_locals = fst (lambda_needs_capture [] (List.map (fun a : stmt -> Expression a) fr.values)) in
  Foreign (Block_value (if reads_locals then By_reference else Nothing), fr)

and instantiated_stmt ~boxing (s : stmt) : stmt =
  match s with
  (* The variable the block assigns is declared in front of it. *)
  | Foreign_block b ->
    let value : expr = Foreign (Statements, instantiated_block ~boxing b.custom b.template b.type_args b.values (Some b.result_type)) in
    Bind_variable (b.result, Declare (instantiated_type ~boxing b.result_type, b.binder), value)
  | s -> Map.stmt (instantiating ~boxing) s

and instantiating ~boxing =
  rewriter ~expr:(instantiated_expr ~boxing) ~stmt:(instantiated_stmt ~boxing) ~type_:(instantiated_type ~boxing) ()

(* A match template's pieces, on the scrutinee [scrut] it is written with. *)
let match_pieces (m : phase Custom_match.t) scrut : Custom_match.piece list =
  List.map
    (function
      | Foreign_template.CCstring s -> Custom_match.Text s
      | CCscrut -> Scrutinee {parenthesised = Cpp_ir.Written.written_with_leading_pointer_operator scrut}
      | CCty -> Matched_type
      | CCty_arg i -> Type_argument i
      | CCbody i -> Branch i
      | CCbr_var (i, j) -> Binder (i, j)
      | CCbr_var_ty (i, j) -> Binder_type (i, j)
      | CCelem _ | CCarg _ | CCret | CCresult ->
        CErrors.anomaly (Pp.str "match_pieces: a term template's hole in a match template") )
    (Foreign_template.match_template (custom_match_text m))

let type_pieces r text (tys : ty list) =
  let tokens = Foreign_template.type_template (Foreign_template.custom_template_with_args text (List.length tys)) in
  foreign_pieces ~element:(fun i -> Option.map wrapper_pieces (boxed_by ~boxing:true r tys i)) tokens

(* A custom match is instantiated on its instantiated scrutinee: the one
   that is written. *)
let instantiate_foreign (d : settled) : settled =
  let boxing = true in
  let rec fs (s : stmt) : stmt =
    match instantiated_stmt ~boxing s with
    | Custom_match m ->
      let branches = List.map (fun (b : phase Custom_match.branch) -> {b with body = List.map fs b.body}) m.branches in
      Custom_match {m with branches; pieces = Instantiated (match_pieces m m.scrutinee)}
    | s -> Map.stmt (rw ()) s
  and fe e = Map.expr (rw ()) e
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:same_type () in
  Map.decl (rw ()) (Map.decl (instantiating ~boxing) d)

(* A type that qualifies a member in value position, [T::f(..)], spelled as
   the value it names: a named global written as an expression -- no
   [typename], since what follows is not a type, and with the namespace
   prefix the value spelling elides where it is in scope.  Anything else
   keeps its type spelling, without the keyword. *)
let value_qualifier : ty -> expr option = function
  | Entity_application (r, tys, []) ->
    let inline =
      Option.map
        (fun s -> Legacy_minicpp_to_cpp_ir.inline_template (Minicpp.inline_template s))
        (Table.inline_custom_text r)
    in
    Some (Entity (r, tys, Some {inline; custom_yields = None}))
  | _ -> None

let lower_qualifiers (d : settled) : settled =
  let qualified ty id : expr = match value_qualifier ty with Some q -> Scope (q, id, []) | None -> Type_member (ty, id) in
  let rec fe (e : expr) : expr =
    match Map.expr (rw ()) e with
    (* A suspension is its type's [lazy_] factory applied to the thunk. *)
    | Suspend (ty, thunk) ->
      Call
        ( {yields = Yields ty; params = Unknown; constructs = None; occurrence = None},
          qualified ty (Id.of_string "lazy_"),
          [thunk] )
    | Type_member (ty, id) -> qualified ty id
    | e -> e
  and fs s = Map.stmt (rw ()) s
  (* A type may hold an expression: [decltype(T::f(..))]. *)
  and ft t = Types.map (function Type_of e -> Type_of (fe e) | t -> t) t
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:ft () in
  Map.decl (rw ()) d

(* A pointer is written in the slot its pointee is held in
   ({!Pointer_slot}): a shared value is its own handle, [shared_box<T>]; where
   only a functor's instantiation knows, [shared_or_t<T, P>] chooses between
   that and the pointer [P].  What is left as a pointer is an ordinary
   pointer.  A slot already chosen is a fixed point: [shared_or_t]'s pointer
   argument is not chosen again.  Expressions a type holds are reached too. *)
let pointer_slots () =
  let rec ft (t : ty) : ty =
    Types.rewrite
      (fun (t : ty) ->
        match t with
        | External (n, [p; Shared_pointer p']) when String.equal n Crane_rt.shared_or ->
          let p' = ft p' in
          Some (External (n, [ft p; Shared_pointer p']))
        | Shared_pointer p -> (
          let p' = ft p in
          match Pointer_slot.of_ir_pointee p with
          | Pointer_slot.Shared -> Some (External (Crane_rt.shared_box, [p']))
          | Pointer_slot.At_instantiation -> Some (External (Crane_rt.shared_or, [p'; Shared_pointer p']))
          | Pointer_slot.Pointer -> Some (Shared_pointer p') )
        | Type_of e -> Some (Type_of (fe e))
        | Entity_application (r, tys, (_ :: _ as args)) ->
          let args = List.map fe args in
          Some (Entity_application (r, List.map ft tys, args))
        | Foreign fr ->
          let yields = Option.map ft fr.yields in
          let values = List.map fe fr.values in
          Some (Foreign {fr with types = List.map ft fr.types; values; yields})
        | _ -> None )
      t
  and fe (e : expr) : expr =
    match Map.expr (rw ()) e with
    (* A shared value goes into its slot as it is: no cell to allocate. *)
    | Allocate ((Heap | Arena_scoped), t) when Pointer_slot.of_ir_pointee t = Pointer_slot.Shared ->
      Type_member (External (Crane_rt.shared_box, [t]), Id.of_string "make")
    (* A unit of non-atomic pointers allocates in an arena through its own
       pointer's factory. *)
    | Allocate (Arena_scoped, t) when Table.non_atomic_rc () ->
      Type_member (External (Crane_rt.rc, [t]), Id.of_string "make")
    | e -> e
  and fs s = Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:ft () in
  rw

let lower_pointer_slots (d : settled) : settled = Map.decl (pointer_slots () ()) d

let instantiate_type t = (pointer_slots () ()).type_ (instantiated_type ~boxing:true t)

(** {2 Naming scrutinees} *)

(* The local a match holds its scrutinee in, named after the match's first
   binding variable -- [_m3] gives [_sv3], a frame dispatch's [_f2] gives
   [_fsv2] -- so that two matches in one scope never declare the same name
   and need no block of their own. *)
let scrutinee_name (branches : phase Match.branch list) =
  let after prefix s =
    if String.starts_with ~prefix s then Some (String.sub s (String.length prefix) (String.length s - String.length prefix))
    else None
  in
  match List.find_map (fun (br : phase Match.branch) -> br.var) branches with
  | None -> "_sv"
  | Some id -> (
    let s = Id.to_string id in
    match (after "_m" s, after "_f" s) with
    | Some k, _ -> "_sv" ^ k
    | None, Some k -> "_fsv" ^ k
    | None, None -> "_sv" )

(* An object a match can read its variant through as it stands: a local, or
   the receiver. *)
let is_named_object : expr -> bool = function Local _ | This | Dereference This -> true | _ -> false

(* The declaration a match's scrutinee is held in, if the match holds it, and
   the scrutinee reading that local.  A variant read through a computed object
   ([e->v()], [e.v()]) binds the object, by forwarding reference so that a
   temporary lives across the branches; any other computed scrutinee is bound
   whole by [const] reference.  A match of one constructor, exhaustive, that
   binds nothing never reads its scrutinee, and holds nothing. *)
let held_scrutinee (scrut : phase Match.scrutinee) (branches : phase Match.branch list) default : (stmt * expr) option =
  let local () = Id.of_string (scrutinee_name branches) in
  let is_v v = Id.to_string v = "v" in
  let forwarding : ty = Reference (Forwarding, Auto) in
  match (branches, default, scrut.expr) with
  | [{field_bindings = []; var = None; _}], None, _ -> None
  | _, _, Access_call (Arrow, obj, v, []) when is_v v && not (is_named_object obj) ->
    let x = local () in
    Some (Bind_variable (x, Declare (forwarding, None), obj), Access_call (Arrow, Local x, v, []))
  | _, _, Call (sg, Access (Dot, obj, v), []) when is_v v && not (is_named_object obj) ->
    let x = local () in
    Some (Bind_variable (x, Declare (forwarding, None), obj), Call (sg, Access (Dot, Local x, v), []))
  | _, _, (Access_call (Arrow, _, v, []) | Call (_, Access (Dot, _, v), [])) when is_v v -> None
  | _, _, (Local _ | Dereference This) -> None
  | _, _, e ->
    let x = local () in
    Some (Bind_variable (x, Declare (Reference (Lvalue, Const Auto), None), e), Local x)

let name_scrutinees (d : settled) : settled =
  let rec stmts ss = List.concat_map stmt ss
  and stmt (s : stmt) : stmt list =
    match Map.stmt (rw ()) s with
    | Match (scrut, branches, default) as s -> (
      match held_scrutinee scrut branches default with
      | Some (held, expr) -> [held; Match ({scrut with expr}, branches, default)]
      | None -> [s] )
    | s -> [s]
  (* Every statement a statement or a declaration holds is in a list, which
     [stmts] rewrites; nothing asks for one statement alone. *)
  and one s =
    match stmt s with
    | [s] -> s
    | _ -> CErrors.anomaly (Pp.str "name_scrutinees: a match held outside a statement list")
  and fe e = Map.expr (rw ()) e
  and rw () = rewriter ~stmts ~expr:fe ~stmt:one ~type_:same_type () in
  Map.decl (rw ()) d

(** {2 Captures} *)

(* Inner lambdas first: what an outer body names is read off the inner
   lambdas' bodies, which deciding leaves as they are. *)
let decide_captures (d : settled) : settled =
  let rec fe (e : expr) : expr =
    match Map.expr (rw ()) e with
    | Lambda ({capture = (Runs_in_place | Stored) as how; _} as l) ->
      let names_scope, this = lambda_needs_capture l.params l.body in
      let written : Written_capture.t =
        if not names_scope then Nothing
        else match how with Runs_in_place -> By_reference | _ -> By_copy {this; moved = l.moved}
      in
      Lambda {l with capture = Written written}
    | e -> e
  and fs s = Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:same_type () in
  Map.decl (rw ()) d

(* An initialiser invoked in place by a lambda capturing nothing, which is
   what this pass writes, is left as it is: the pass is a fixed point. *)
let invoke_capturing_initialisers (d : settled) : settled =
  let invoked_in_place : expr -> bool = function
    | Call (_, Lambda {params = []; capture = Written Nothing; body = [Return (Some _)]; _}, []) -> true
    | _ -> false
  in
  let rec decl : decl -> decl = function
    | Variable a when (not (invoked_in_place a.init)) && expr_contains_capturing_lambda a.init ->
      let returning : expr =
        Lambda
          { params = [];
            type_params = [];
            return_type = None;
            body = [Return (Some a.init)];
            capture = Written Nothing;
            moved = [];
            binders = [];
            fixpoint = None }
      in
      Variable {a with init = call returning []}
    | Template (tps, c, inner) -> Template (tps, c, decl inner)
    | Namespace (id, ds) -> Namespace (id, List.map decl ds)
    | d -> d
  in
  decl d

(** {2 Methods and projections} *)

(* The lambda a methodified function [n] is written as where it is a value,
   its receiver at [pos].  It takes the function's parameters at the types the
   method was declared at, not [const auto &]: a generic lambda has no
   deducible signature, so whatever inspects one -- [crane_erase_fn] probing
   whether it accepts [std::any], [std::function] CTAD -- must instantiate its
   body to find out, and an instantiation that does not type-check is a hard
   error rather than a substitution failure.  A type mentioning a template
   parameter can only be spelled where that parameter is in scope, which a
   lambda in a static data member's initialiser is not, so such a type is left
   generic; a method planned nowhere leaves only the generic form. *)
let method_value n (tys : ty list) pos : expr =
  let contains_tvar = Cpp_ir.Children.exists_type (function Variable _ | Auto -> true | _ -> false) in
  let spellable ty = if contains_tvar ty then None else Some ty in
  let receiver =
    match Cpp_state.is_registered_method n with
    | None -> None
    | Some (epon_ref, _) ->
      let positions = Cpp_state.lookup_method_ind_tvar_positions n in
      let ind_tys = List.filteri (fun i _ -> List.mem i positions) tys in
      (* Every one of the receiver's template parameters has to be recovered:
         an inductive spelled with too few is not a type. *)
      if List.length ind_tys <> Table.get_ind_nb_tparams epon_ref then None
      else spellable (Entity_application (epon_ref, ind_tys, []))
  in
  let params, receiver_pos =
    match Cpp_state.lookup_method_arity n with
    | arity when arity <= 1 -> ([receiver], 0)
    | arity ->
      (* The plan records the declared parameters in order, without the
         receiver's slot; each carries however many qualifiers the
         declaration gave it, and the lambda spells its own. *)
      let declared = List.map Legacy_minicpp_to_cpp_ir.lower_type (Option.default [] (Callable_abi.method_params n)) in
      let rec unqualified : ty -> ty = function Reference (_, t) | Const t -> unqualified t | t -> t in
      let param i =
        if i = pos then receiver
        else
          let i = if i > pos then i - 1 else i in
          Option.bind (List.nth_opt declared i) (fun ty -> spellable (unqualified ty))
      in
      (List.init arity param, pos)
  in
  Method_value
    {method_ = n; access = Dot; receiver = receiver_pos; params; type_args = Cpp_names.method_type_args n tys}

(* Whether a global is written as a function of its own, not a mapping's
   text. *)
let not_inline : phase Cpp_ir.Foreign.custom option -> bool = function None | Some {inline = None; _} -> true | _ -> false

let lower_method_calls (d : settled) : settled =
  let rec fe (e : expr) : expr =
    match e with
    | Call (_, Entity (n, tys, ci), args) when not_inline ci -> (
      match Cpp_names.lookup_method_this_pos n with
      | None -> Map.expr (rw ()) e
      | Some pos -> (
        match Common.extract_at_pos pos args with
        | Some receiver, rest ->
          (* Every inductive is a value type, reached with a dot; [this] is a
             raw pointer and a dereference dereferences a smart one, and both
             are reached with an arrow instead.  A method takes its receiver
             as a const [this], so moving it gives the method nothing, and
             on a coinductive's projection picks the overload that copies the
             field out ({!Borrow_projection}). *)
          let receiver = match fe receiver with Move r -> r | r -> r in
          let ((access, receiver) : Access.t * expr) =
            match receiver with This -> (Arrow, This) | Dereference p -> (Arrow, p) | receiver -> (Dot, receiver)
          in
          let args = List.map fe rest in
          Method_call {method_ = n; access; receiver; type_args = Cpp_names.method_type_args n tys; args}
        | None, _ -> Map.expr (rw ()) e ) )
    | Entity (n, tys, ci) when not_inline ci -> (
      match Cpp_names.lookup_method_this_pos n with Some pos -> method_value n tys pos | None -> e )
    | e -> Map.expr (rw ()) e
  and fs s = Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:same_type () in
  Map.decl (rw ()) d

(* A projection reads a field, and the field's name does not depend on what
   the record was instantiated at, so its type arguments are ignored rather
   than required to be absent: one of a module obtained by functor
   application is applied at a type, and once fell through to an ordinary
   call of a function a suppressed projection never has. *)
let lower_projections (d : settled) : settled =
  let rec fe (e : expr) : expr =
    match e with
    | Call (_, Entity (r, _, ci), record :: rest) when not_inline ci && Table.is_projection r ->
      let args = List.map fe rest in
      Projection {projection = r; record = fe record; args}
    | Entity (r, _, ci) when not_inline ci && Table.is_projection r -> Projection_value r
    | e -> Map.expr (rw ()) e
  and fs s = Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:same_type () in
  Map.decl (rw ()) d

(** {2 Choices} *)

(* A string literal outside any nested statement: as a [?:] branch it stays a
   [const char*], where the lambda's declared return type converted it. *)
let rec reads_string_literal (e : expr) =
  match e with
  | Literal (String _) -> true
  | _ ->
    let found = ref false in
    Cpp_ir.Subterms.expr ~expr:(fun e -> if not !found then found := reads_string_literal e) ~stmts:(fun _ -> ()) e;
    !found

(* The two values a lambda's body chooses between, when all it does is choose:
   a match of one alternative against the rest, an [if], or a mapped two-way
   case whose template is an [if]. *)
let chosen_values (l : phase Lambda.t) : (expr * expr * expr) option =
  match l with
  | {params = []; body = [Match (scrut, branches, wildcard)]; capture = Runs_in_place; _} -> (
    let returns_only (br : phase Match.branch) =
      match br with {field_bindings = []; extra_conditions = []; body = [Return (Some e)]; _} -> Some e | _ -> None
    in
    let tested (br : phase Match.branch) e1 e2 = Some (call (Holds_alternative br.ctor_type) [scrut.expr], e1, e2) in
    match (branches, wildcard) with
    | [br1; br2], None -> (
      match (returns_only br1, returns_only br2) with Some e1, Some e2 -> tested br1 e1 e2 | _ -> None )
    | [br1], Some [Return (Some e2)] -> ( match returns_only br1 with Some e1 -> tested br1 e1 e2 | None -> None )
    | _ -> None )
  | {params = []; body = [If {condition; then_ = [Return (Some e1)]; else_ = [Return (Some e2)]}]; _}
    when not (reads_string_literal e1 || reads_string_literal e2) ->
    Some (condition, e1, e2)
  | { params = [];
      body =
        [ Custom_match
            {scrutinee; branches = [{body = [Return (Some e1)]; _}; {body = [Return (Some e2)]; _}]; template; _} ];
      _ }
    when String.trim template = "if (%scrut) { %br0 } else { %br1 }"
         && not (reads_string_literal e1 || reads_string_literal e2) ->
    Some (scrutinee, e1, e2)
  | _ -> None

(* The guards read the lambda as written, before anything nested inside it is
   rewritten: a nested conditional exposes the string literals its own lambda
   kept inside a statement. *)
let lower_conditionals (d : settled) : settled =
  let rec fe (e : expr) : expr =
    match e with
    | Call (_, Lambda l, []) -> (
      match chosen_values l with
      | Some (c, e1, e2) ->
        let e2 = fe e2 in
        let e1 = fe e1 in
        Conditional (fe c, e1, e2)
      | None -> Map.expr (rw ()) e )
    | e -> Map.expr (rw ()) e
  and fs s = Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:same_type () in
  Map.decl (rw ()) d

(* Bottom-up, so that a move hoisted out of an inner access reaches the outer
   one, and one hoisted into a move already there is that move: the member
   read was moved already. *)
let lower_access_moves (d : settled) : settled =
  let rec fe (e : expr) : expr =
    match Map.expr (rw ()) e with
    | Access (acc, Move inner, id) -> Move (Access (acc, inner, id))
    | Access_call (acc, Move inner, m, args) -> Access_call (acc, inner, m, args)
    | Move (Move _ as moved) -> moved
    | e -> e
  and fs s = Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:same_type () in
  Map.decl (rw ()) d

(** {2 Literal types} *)

let rec is_literal_type (ty : ty) =
  (not (is_any_shaped ty))
  &&
  match ty with
  | Shared_pointer _ | Void | Variable _ | Instance _ | Promoted_member _ | Any | Obligation _ | Auto -> false
  (* [std::function] erases what it holds. *)
  | Function _ | Decay _ -> false
  (* A mapping asks what the application it instantiates asks. *)
  | Foreign fr -> is_literal_type (Entity_application (fr.custom, fr.types, fr.values))
  | Entity_application (r, _, _) when is_axiom_type_ref r -> false
  | Entity_application (r, [], _) when Table.is_custom_scalar_ref r -> true
  (* A generated inductive other than an enum has user-provided constructors
     that are not [constexpr], so it is not a literal type. *)
  | Entity_application ((GlobRef.IndRef _ as r), tys, _) -> Table.is_enum_inductive r && List.for_all is_literal_type tys
  | Const t | Reference (_, t) | Pointer t | Non_deduced t | In_namespace (_, t) | Member (t, _) -> is_literal_type t
  | Variant (_, tys) -> List.for_all is_literal_type tys
  (* A defined constant with no arguments is an alias nothing here sees
     through, as is a named type with none. *)
  | Entity_application (GlobRef.ConstRef _, [], _) | Named (_, []) -> false
  | Entity_application (_, tys, _) | Named (_, tys) | External (_, tys) -> List.for_all is_literal_type tys
  | Rebind (h, x) -> is_literal_type h && is_literal_type x
  | Carrier_parameter | Erased _ -> true
  | Type_of _ | Decltype_auto -> false
  (* An applied associated type is whatever the instance makes it. *)
  | Type_constructor _ | Apply _ -> false

let literal_signature ret params = List.for_all is_literal_type (ret :: List.map snd params)

let eligible b : phase Constexpr.t = if b then Eligible else Ineligible

let decide_constexpr (d : settled) : settled =
  let method_ (m : phase Method.t) =
    { m with
      constexpr = eligible (m.receiver = Static && (not m.no_pure) && literal_signature m.return_type m.params) }
  in
  let rec fields fs = List.map (fun ((f, vis, tag) : phase Field.member) -> (field f, vis, tag)) fs
  and field : phase Field.t -> phase Field.t = function
    | Method m -> Method (method_ m)
    | Out_of_line_declaration (Method m) -> Out_of_line_declaration (Method (method_ m))
    | Nested_struct (id, fs) -> Nested_struct (id, fields fs)
    | f -> f
  in
  let struct_ (s : phase Struct.t) = {s with fields = fields s.fields} in
  let rec decl : decl -> decl = function
    | Template (tps, c, d) -> Template (tps, c, decl d)
    | Namespace (r, ds) -> Namespace (r, List.map decl ds)
    | Function f ->
      let types, throws =
        match f.shape with
        | Definition (params, body) ->
          (List.map snd params, match body with [Return (Some (Abort _))] -> true | _ -> false)
        | Declaration params -> (List.map snd params, false)
      in
      Function
        { f with
          constexpr = eligible ((not (throws || f.no_pure)) && List.for_all is_literal_type (f.return_type :: types)) }
    | Variable a ->
      let literal =
        match a.init with
        | Numeral _ | Literal (Uint63 _ | Int _ | Bool _) | Enum_value _ -> true
        (* A mapped constant constructor of a literal type ([true]) is that
           type's literal. *)
        | Entity ((GlobRef.ConstructRef _ as r), [], _) -> Table.is_custom r
        (* And so is its text once instantiated ({!instantiate_foreign}). *)
        | Foreign (Constant, {custom = GlobRef.ConstructRef _ as r; types = []; values = []; _}) -> Table.is_custom r
        | _ -> false
      in
      Variable {a with constexpr = eligible (literal && is_literal_type a.type_)}
    | Struct s -> Struct (struct_ s)
    | Merged_struct_members s -> Merged_struct_members (struct_ s)
    | Member_definition ({member = Method m; _} as md) -> Member_definition {md with member = Method (method_ m)}
    | d -> d
  in
  decl d

(** {2 Free type variables} *)

(** Whether [t] is the type variable named [id], under either spelling a
    variable's head may have. *)
let tvar_is id (t : ty) =
  match t with
  | Variable (Named n) -> Id.equal n id
  | Variable (Index (i, name)) ->
    (match name with Some n -> Id.equal n id | None -> false) || Id.equal (Minicpp.tvar_id i) id
  | _ -> false

(** Every spelling of every type variable [ty] names: the parameter name a
    variable was given and the positional name its index prints as. *)
let tvar_spellings (ty : ty) =
  let acc = ref Id.Set.empty in
  ignore
    (Cpp_ir.Children.exists_type
       (fun (t : ty) ->
         ( match t with
         | Variable (Named n) -> acc := Id.Set.add n !acc
         | Variable (Index (i, name)) ->
           Option.iter (fun n -> acc := Id.Set.add n !acc) name;
           acc := Id.Set.add (Minicpp.tvar_id i) !acc
         | _ -> () );
         false )
       ty );
  !acc

(** [bind_free_tvars decl] spells [std::any] every type variable a body names
    that nothing in scope declares.

    A declaration's head is the authority on what type variables it has.  The
    head is built from the instance context a definition sits in; the body is
    generated against the ML type, which still carries the definition's own
    [forall].  Where the two disagree the body wins nothing -- it names [T2]
    under a head declaring [T1], and a name nothing declares does not compile.
    Erasing the use is the same repair {!Minicpp.drop_tparams} makes for a
    lambda, one level up, and for the same reason: half a quantifier is worth
    less than none.

    Scope is threaded rather than collected, because it genuinely nests -- a
    function template inside a struct template inside a namespace, and a
    lambda with template parameters of its own inside all three.  The
    signature counts as declaring: whatever a parameter or the return type
    names, the head had to declare for the signature itself to compile, so the
    body may name it too.

    Only bodies are rewritten.  A signature naming a variable its head does
    not declare is the same defect, but the honest repair there is a different
    one -- give the head the parameter -- and erasing it here would hide the
    case rather than fix it. *)
let bind_free_tvars (d : settled) : settled =
  let add_ids ids bound = List.fold_left (fun acc id -> Id.Set.add id acc) bound ids in
  let add_ty ty bound = Id.Set.union (tvar_spellings ty) bound in
  let add_tys tys bound = List.fold_left (fun acc t -> add_ty t acc) bound tys in
  let erase bound =
    Types.map (fun (t : ty) ->
        match t with Variable _ when not (Id.Set.exists (fun b -> tvar_is b t) bound) -> Any | _ -> t )
  in
  (* A lambda is the one expression that introduces type variables, so it is
     the one expression this has to spell out. *)
  let rec fe bound (e : expr) : expr =
    match e with
    | Lambda l ->
      let bound = add_ids l.type_params bound in
      Lambda (Map.lambda (rw bound) l)
    | _ -> Map.expr (rw bound) e
  and fs bound (s : stmt) : stmt =
    match Map.stmt (rw bound) s with
    (* A structured binding writes none of its field types -- [const auto
       &[a0, a1]] spells only the names -- so a free variable among them is
       not a name the compiler can fail on, and erasing it would convert an
       imprecision in the program into a decision about representation, which
       the printer then has to paper over with a cast at every use.  Restore
       them from the statement as it came in. *)
    | Match (scrut, branches', dflt) ->
      let restore (b' : phase Match.branch) (b : phase Match.branch) = {b' with field_bindings = b.field_bindings} in
      let branches =
        match s with
        | Match (_, branches, _) when List.length branches = List.length branches' -> List.map2 restore branches' branches
        | _ -> branches'
      in
      Match (scrut, branches, dflt)
    | s' -> s'
  and rw bound = rewriter ~expr:(fe bound) ~stmt:(fs bound) ~type_:(erase bound) () in
  let body bound stmts = List.map (fs bound) stmts in
  let method_scope bound (m : phase Method.t) =
    bound |> add_ids (List.map snd m.type_params) |> add_ty m.return_type |> add_tys (List.map snd m.params)
  in
  let member bound : phase Out_of_line.t -> phase Out_of_line.t = function
    | Method m ->
      let bound = method_scope bound m in
      Method {m with body = body bound m.body}
    | Destructor stmts -> Destructor (body bound stmts)
  in
  let rec field bound ((f, vis, tag) as fld : phase Field.member) : phase Field.member =
    match f with
    | Method m ->
      let bound = method_scope bound m in
      (Method {m with body = body bound m.body}, vis, tag)
    | Constructor c ->
      let bound = bound |> add_ids (List.map snd c.type_params) |> add_tys (List.map snd c.params) in
      (Constructor {c with body = body bound c.body}, vis, tag)
    | Destructor stmts -> (Destructor (body bound stmts), vis, tag)
    | Nested_struct (id, fields) -> (Nested_struct (id, List.map (field bound) fields), vis, tag)
    (* An out-of-line declaration is the half without a body; the body is the
       member definition that follows, and is reached there. *)
    | _ -> fld
  in
  let rec go bound (d : decl) : decl =
    match d with
    | Template (tps, cstr, inner) -> Template (tps, cstr, go (add_ids (List.map snd tps) bound) inner)
    | Namespace (r, decls) -> Namespace (r, List.map (go bound) decls)
    | Struct st -> Struct (struct_ bound st)
    | Merged_struct_members st -> Merged_struct_members (struct_ bound st)
    | Member_definition dm ->
      let bound = add_ids (List.map snd dm.type_params) bound in
      Member_definition {dm with member = member bound dm.member}
    | Function ({shape = Definition (params, stmts); return_type; _} as f) ->
      let bound = bound |> add_ty return_type |> add_tys (List.map snd params) in
      Function {f with shape = Definition (params, body bound stmts)}
    (* A global's initialiser is a body like any other, and its declared type
       is as much a signature as a function's return type. *)
    | Variable a -> Variable {a with init = fe (add_ty a.type_ bound) a.init}
    | _ -> d
  and struct_ bound (st : phase Struct.t) =
    let bound = add_ids (List.map snd st.type_params) bound in
    {st with fields = List.map (field bound) st.fields}
  in
  go Id.Set.empty d

(** {2 The seam} *)

(** Whether [ty] mentions anywhere a global with no C++ name, asked of the
    type as the printer writes it: an application of a nameless constructor
    comes out as its argument ({!Ml_type_util.has_no_cpp_spelling}). *)
let has_no_cpp_spelling (ty : ty) =
  let as_printed =
    Types.map
      (fun (t : ty) ->
        match t with Apply (Entity_application (r, _, _), [arg]) when Ml_type_util.ref_has_no_cpp_name r -> arg | t -> t )
      ty
  in
  Cpp_ir.Children.exists_type
    (function Entity_application (r, _, _) -> Ml_type_util.ref_has_no_cpp_name r | _ -> false)
    as_printed

(** Report what {!has_no_cpp_spelling} saw of a custom match's binder.

    Two audiences.  A [Crane Extract Skip] on a constant that a custom
    template later needs {e by name} degrades silently: the binder becomes
    [std::any] and the only symptom is a type error a long way downstream, so
    that one is always warned about, naming the directive to remove.  A module
    left out by [Crane Extract Skip Module] was left out wholesale and on
    purpose, so it is not worth a word unless asked.

    [CRANE_DBG_UNSPELLABLE] adds the full shape.  The ordinal is the
    discriminator: firings are reported in the order declarations are
    finished, which is the only handle on {e which} site fired when several
    share a custom template, and the alternative -- a table of the
    declaration being finished -- is the thing that must not be built. *)
let unspellable_firings = ref 0

let unspellable_warned : (string, unit) Hashtbl.t = Hashtbl.create 7

let report_unspellable where (ty : ty) =
  let empty_custom = ref [] and skipped_mod = ref [] in
  ignore
    (Cpp_ir.Children.exists_type
       (fun (t : ty) ->
         match t with
         | Entity_application (r, _, _) when Ml_type_util.ref_has_no_cpp_name r ->
           let n = Pp.string_of_ppcmds (GlobRef.print r) in
           if Ml_type_util.ref_has_no_spelling r then empty_custom := n :: !empty_custom
           else skipped_mod := n :: !skipped_mod;
           false
         | _ -> false )
       ty );
  incr unspellable_firings;
  List.iter
    (fun n ->
      if not (Hashtbl.mem unspellable_warned n) then begin
        Hashtbl.add unspellable_warned n ();
        Feedback.msg_warning
          (Pp.str
             (Printf.sprintf
                "crane: a custom template needs %s by name, but [Crane Extract Skip] removed it, so the binder is \
                 typed std::any and the type is lost here.  If %s is still reachable, drop the directive that skips \
                 it."
                n n ) )
      end )
    (List.rev !empty_custom);
  if Sys.getenv_opt "CRANE_DBG_UNSPELLABLE" <> None then begin
    let shape : ty -> string = function
      | Entity_application _ -> "Tglob"
      | Apply _ -> "Tapply"
      | Member _ -> "Tqualified"
      | Variable _ -> "Tvar"
      | Instance _ -> "Tinstance"
      | Promoted_member _ -> "Tpromoted"
      | Named _ -> "Tid"
      | External _ -> "Tid_external"
      | Non_deduced _ -> "Tnondeduced"
      | Rebind _ -> "Trebind"
      | Carrier_parameter -> "Thole"
      | Reference (Forwarding, _) -> "Tfwd_ref"
      | Type_of _ -> "Texpr_type"
      | Decltype_auto -> "Tdecltype_auto"
      | Type_constructor _ -> "Ttyctor"
      | Any -> "Tany"
      | _ -> "other"
    in
    let tagged tag l = List.map (fun n -> n ^ " [" ^ tag ^ "]") l in
    Feedback.msg_warning
      (Pp.str
         (Printf.sprintf "crane: firing %d: %s yields std::any; outermost %s; nameless globs: %s" !unspellable_firings
            where (shape ty)
            (String.concat ", " (tagged "empty custom" (List.rev !empty_custom) @ tagged "skipped module" (List.rev !skipped_mod))) ) )
  end

(* Whether the template of [m] writes down the type of branch [i]'s binder
   [j], [p], which C++ cannot spell. *)
let unspellable_binder (m : phase Custom_match.t) =
  let written = Foreign_template.match_template (custom_match_text m) in
  fun i j (p : phase Custom_match.param) ->
    List.mem (Foreign_template.CCbr_var_ty (i, j)) written && has_no_cpp_spelling p.type_

(* An unknown representation in [ty] settled into [std::any], inside a
   carrier abstraction's body too: {!Cpp_ir.Types.map} stops at a type
   constructor, whose body is still written down where the carrier is minted
   an alias template. *)
let settle_opaque (ty : ty) : ty =
  let in_body = Types.rewrite (fun (t : ty) -> match t with Obligation Opaque_type -> Some Any | _ -> None) in
  Types.map
    (fun (t : ty) ->
      match t with Obligation Opaque_type -> Any | Type_constructor body -> Type_constructor (in_body body) | t -> t )
    ty

let materialise (d : decl) : settled =
  let spelled (m : phase Custom_match.t) =
    let unspellable = unspellable_binder m in
    fun i (b : phase Custom_match.branch) : phase Custom_match.branch ->
      let params =
        List.mapi
          (fun j (p : phase Custom_match.param) ->
            if unspellable i j p then begin
              report_unspellable (Printf.sprintf "branch %d var %d of %s" i j (custom_match_text m)) p.type_;
              {p with type_ = Any}
            end
            else p )
          b.params
      in
      {b with params}
  in
  let rec fe e = Map.expr (rw ()) e
  and fs (s : stmt) : stmt =
    match s with
    | Custom_match m -> Map.stmt (rw ()) (Custom_match {m with branches = List.mapi (spelled m) m.branches})
    | s -> Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:settle_opaque () in
  Map.decl (rw ()) d

let writes_unspellable_binder (d : settled) =
  let exception Found in
  let rec fe e = Map.expr (rw ()) e
  and fs (s : stmt) : stmt =
    ( match s with
    | Custom_match m ->
      let unspellable = unspellable_binder m in
      List.iteri
        (fun i (b : phase Custom_match.branch) ->
          List.iteri (fun j p -> if unspellable i j p then raise_notrace Found) b.params )
        m.branches
    | _ -> () );
    Map.stmt (rw ()) s
  and rw () = rewriter ~expr:fe ~stmt:fs ~type_:same_type () in
  match ignore (Map.decl (rw ()) d) with () -> false | exception Found -> true
