(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Tail-modulo-cons loopification for {!Loopify}: detection, the
    destination-passing rewrite, and the Perceus reuse cursor the loop uses
    under [Crane Reuse]. *)

open Names
open Minicpp
open Loopify_analysis
open Loopify_tail

(** {3 Tail Modulo Cons (TMC)}

    When a non-tail recursive call appears nested inside one or more constructor
    factories (e.g., [Cons_(x, RECURSE(xs))] or
    [Cons_(x, Cons_(x, RECURSE(xs)))]), the function can be optimized using
    destination-passing style: allocate the constructor cells immediately with
    [nullptr] holes, link them together, then fill the innermost hole on the
    next iteration.  This achieves O(1) extra space instead of O(n) frame stack.

    See Bour, Clément, Scherer 2021 — "Tail Modulo Cons". *)

(** One constructor cell allocation in a (possibly nested) TMC chain.
    For [cons x (cons x (stutter xs))], the outer [cons x _] and inner
    [cons x _] are each represented by one [tmc_cell_alloc]. *)
type tmc_cell_alloc = {
  tca_factory : cpp_expr;
      (** Constructor factory function, e.g., [list<T>::ctor::Cons_] *)
  tca_constructor : GlobRef.t;  (** The constructor the cell is built by *)
  tca_type : cpp_type;
      (** The cell's type, e.g., [list<T>], as the factory call records what
          it yields: spelled as a type, which the factory's qualifier, a
          value's spelling, is not *)
  tca_ctor_name : string;
      (** Constructor name without trailing underscore, e.g., ["Cons"] *)
  tca_rec_field_idx : int;
      (** Index of the recursive argument in the constructor args *)
  tca_non_rec_args : (int * cpp_expr) list;
      (** [(index, expr)] for non-recursive arguments *)
  tca_n_args : int;
      (** Total number of constructor arguments *)
  tca_ptr_fields : ptr_field list;
      (** The fields stored as [shared_ptr] in the struct, indexed like the
          arguments.  Used by {!build_cell_call} to wrap value-type args in
          [make_shared] for direct struct construction. *)
}

(** Information about a single TMC-eligible branch: a return expression of the
    form [CtorFactory(... CtorFactory(non_rec_args, RECURSE(rec_args)) ...)].
    The cell list is outermost-first, innermost-last. *)
type tmc_branch_info = {
  tmc_cells : tmc_cell_alloc list;
      (** Constructor cells, outermost first, innermost last *)
  tmc_rec_args : cpp_expr list;
      (** Arguments to the innermost recursive call *)
  tmc_call : cpp_expr;  (** The innermost recursive call *)
}

(** Where a loop assembles its result, decided once per function from the
    return type and the reuse policy.  Each says what [_write] points at and
    what the function returns, so the three cannot be mixed within a loop. *)
type result_storage =
  | Value_root of cpp_type
      (** A value-type result, assembled in a local [std::optional]: the first
          node is the result itself, so only the cells below it are
          allocated, and an empty result allocates nothing.  [_write] is null
          until that first node has been placed. *)
  | Boxed_root of cpp_type
      (** A value-type result whose first cell is a heap cell like the rest,
          moved out at the end.  The Perceus reuse cursor needs it: it recycles
          an input cell into every output cell, the first included. *)
  | Pointer_result of cpp_type
      (** A result that is itself the pointer at the head of the chain. *)

let storage_of ret_ty =
  let rec shared = function
    | Tglob (r, _, _) -> Table.is_shared_variant r
    | Tnamespace (_, t) | Tconst t -> shared t
    | _ -> false
  in
  let shared = shared ret_ty in
  if is_value_type_ret ret_ty then
    (* A shared variant's slot holds no cell for the cursor to recycle. *)
    if Table.reuse () && Table.non_atomic_rc () && not shared then Boxed_root ret_ty
    else Value_root ret_ty
  else Pointer_result ret_ty

(** The value type a cell holds behind its pointer, when cells are values. *)
let cell_value_type = function
  | Value_root t | Boxed_root t -> Some t
  | Pointer_result _ -> None

(** {3 TMC detection}

    Analyze function bodies to detect the Tail-Modulo-Cons pattern:
    non-tail recursive calls nested inside one or more constructor factories. *)

(** Test whether an expression is a constructor factory call, i.e.,
    [Type::cons(args)].  Returns [(c, factory, ty, ctor_name, args)] where
    [c] is the constructor, [factory] the callee, [ty] the type the call
    yields (e.g., [list<T>]), [ctor_name] the constructor struct name (e.g.,
    ["Cons"]), and [args] the constructor arguments.

    The qualifier of [factory] names the same type, but as a value spells
    it, to select a member function; as a type an inductive is written as
    translation recorded it, the one place that knows the inductives in
    scope: a [Fin.t] whose struct was put at file scope is [T], not
    [Fin::T].

    A factory call records the constructor it builds ({!Minicpp.call_sig}),
    and the struct is named after that constructor
    ({!Ml_type_util.ctor_struct_name_of_ref}).  The factory's own name does
    not say: it is the struct's lowercased, so [PeanoSucc] and [WW] have
    factories [peanosucc] and [ww], from which no capitalisation recovers
    them. *)
let is_ctor_factory_call = function
  | CPPfun_call ({cs_constructs = Some c; cs_yields; _}, (CPPqualified_t (qualifier, _) as factory), args) ->
    let ty = match cs_yields with Ryields t -> t | Ropaque -> qualifier in
    let struct_name = Ml_type_util.ctor_struct_name_of_ref c in
    (* A TMC-wrapping constructor has a field behind the pointer -- the hole
       the recursion writes into -- so it is recorded in [ctor_ptr_fields];
       one that has none is no cell. *)
    if not (Hashtbl.mem ctor_ptr_fields (Common.ctor_owner_key c, struct_name)) then None
    else
      (* The arguments come back as stored -- reversed.  Everything downstream
         indexes them in that space; see [uptr_idxs] in [make_cell]. *)
      Some (c, factory, ty, struct_name, to_reversed args)
  | _ -> None

(** The cell the call of [factory] on [args] builds by the constructor [c],
    of the constructor struct [ctor_name] of [cell_ty], its argument [idx]
    the hole. *)
let make_cell ~constructor ~factory ~cell_ty ~ctor_name args idx =
  let n_args = List.length args in
  let uptr_idxs =
    (* [ctor_ptr_fields] records shared_ptr field positions in STRUCT-field
       order, but [idx]/[tca_non_rec_args] here index into [args] from
       [is_ctor_factory_call], which are stored REVERSED (as [CPPfun_call]
       keeps them).  Map the struct-order positions into the same reversed
       arg-space ([n_args - 1 - j]) so [build_cell_call]'s lookup of an
       argument's field aligns — otherwise a non-pointer field (e.g. a
       [cons] element) is spuriously [make_shared]-wrapped. *)
    match Hashtbl.find_opt ctor_ptr_fields (Common.ctor_owner_key constructor, ctor_name) with
    | Some fields ->
      List.map
        (function
          | Recursive j -> Recursive (n_args - 1 - j)
          | Boxed j -> Boxed (n_args - 1 - j))
        fields
    | None -> [Recursive idx]
  in
  { tca_factory = factory;
    tca_constructor = constructor;
    tca_type = cell_ty;
    tca_ctor_name = ctor_name;
    tca_rec_field_idx = idx;
    tca_non_rec_args =
      List.concat (List.mapi (fun i a -> if i <> idx then [(i, a)] else []) args);
    tca_n_args = n_args;
    tca_ptr_fields = uptr_idxs }

(** The constructors a branch builds around a recursive call, outermost
    first, each with the argument, in its declared order, that is its hole;
    and the occurrence the call is made of, where it is known. *)
type shape = {
  constructors : (GlobRef.t * int) list;
  call : Miniml.Occurrence.t option;
}

(** The shapes of the recursion plan's [chains] ({!Recursion_plan.strategy}),
    which do not say which call each is around. *)
let chain_shapes chains =
  List.map
    (fun (ch : Recursion_plan.chain) ->
      { constructors = List.map (fun (c : Recursion_plan.cell) -> (c.constructor, c.hole)) (ch.around @ [ch.innermost]);
        call = None } )
    chains

(** The shapes of the turns [into] of a loop's ControlIR that build what
    they return, each around the call it continues by. *)
let control_shapes into =
  List.map
    (fun (c : Control_ir.Term.continue_into) ->
      { constructors = List.map (fun (cell : Control_ir.Term.cell) -> (cell.constructor, cell.hole)) c.cells;
        call = Some c.next.occurrence } )
    into

(** The return expression [expr] as the branch of the first of [shapes] it
    has: the factory calls it nests, each building its cell's constructor,
    holding the next in the cell's hole, the innermost a recursive call,
    made of the shape's call where it says.  A hole is counted among the
    constructor's declared arguments; a factory call stores them reversed. *)
let branch_along shapes check expr =
  let rec follow expr call = function
    | [] -> None
    | (constructor, hole) :: inner -> (
      let expr = match expr with CPPmove e -> e | e -> e in
      match is_ctor_factory_call expr with
      | Some (c, factory, cell_ty, ctor_name, args) when Common.globref_equal c constructor ->
        let idx = List.length args - 1 - hole in
        let held = if idx < 0 then None else List.nth_opt args idx in
        let this = make_cell ~constructor:c ~factory ~cell_ty ~ctor_name args idx in
        Option.bind held (fun held ->
            match inner with
            | [] ->
              let made_of_call =
                match (call, Loopify_analysis.made_of held) with
                | None, _ -> true
                | Some o, Some o' -> Miniml.Occurrence.equal o o'
                | Some _, None -> false
              in
              if made_of_call then
                Option.map (fun cs -> {tmc_cells = [this]; tmc_rec_args = cs.cs_args; tmc_call = held}) (check held)
              else None
            | _ -> Option.map (fun br -> {br with tmc_cells = this :: br.tmc_cells}) (follow held call inner) )
      | Some _ | None -> None )
  in
  List.find_map (fun sh -> follow expr sh.call sh.constructors) shapes
(** {3 TMC transformation}

    Converts non-tail recursive functions where the recursive call is wrapped
    in one or more constructors (e.g., [cons x (f xs)] or
    [cons x (cons x (f xs))]) into iterative loops that build the result
    top-down using destination-passing style.

    Instead of an O(n) frame stack, TMC uses O(1) extra space by allocating
    constructor cells immediately with [nullptr] holes, linking nested cells
    together, then filling the innermost hole on the next iteration.

    Single-cell example ([cons x (f xs)]):
    {[
      auto _cell = Cons_(x, nullptr);
      <patch _head/_last with _cell>
      _last = _cell;
    ]}

    Nested-cell example ([cons x (cons x (f xs))]):
    {[
      auto _cell  = Cons_(x, nullptr);   // outer
      auto _cell1 = Cons_(x, nullptr);   // inner
      _cell.tail  = _cell1;              // link
      <patch _head/_last with _cell>
      _last = _cell1;                    // advance to innermost
    ]} *)

(** Generate [std::get<typename Type::Ctor>(ptr->v_mut()).<field> = val] —
    the statement that patches the recursive field of a TMC cell.

    The field index accounts for the reversed AST argument order
    (see translation.ml:1776): AST index [rec_field_idx] maps to struct
    field index [n_args - 1 - rec_field_idx].  The actual field name is
    resolved via {!Common.lookup_ctor_field_name}, which returns the
    descriptive Rocq binder name (e.g. [d_tl]) when one was registered
    during inductive definition, or falls back to the positional name
    [d_a{idx}].

    {!cell_rec_field} returns that lvalue split as [(object, field)], because
    the write-pointer update needs to take its address rather than assign to
    it; {!patch_cell_field} is the assignment. *)
let cell_struct cell = Tqualified (cell.tca_type, Id.of_string cell.tca_ctor_name)

let cell_rec_field ?(access = Aarrow) cell ptr =
  let field_idx = cell.tca_n_args - 1 - cell.tca_rec_field_idx in
  let v_mut = CPPaccess_call (access, ptr, id_v_mut, []) in
  ( CPPstd_get (cell_struct cell, Some v_mut),
    Common.lookup_ctor_field_name ~owner:cell.tca_constructor cell.tca_ctor_name field_idx )

let patch_cell_field cell ptr val_expr =
  let obj, field_id = cell_rec_field cell ptr in
  Sassign_expr (CPPget (obj, field_id), val_expr)

(** A heap allocation of a [ty] built from [v]. *)
let alloc_value ty v =
  CPPfun_call
    ( call_sig ~yields:(Tshared_ptr ty) ~nargs:1 (),
      CPPalloc (Alloc_heap, ty),
      of_reversed [v] )

(** [v] written where [storage] says the next value goes, as an expression
    that denotes the node it now is: the root, while nothing has been placed,
    and otherwise a fresh cell in the hole [_write] points at.

    That is: if [_write] is null, [_root.emplace(v)]; otherwise assign a
    fresh [std::make_shared<T>(v)] through [_write] and dereference what was
    assigned.

    [v] is spliced into both arms, of which one runs: callers pass a local. *)
let place_value ty v =
  CPPcond
    ( CPPvar id_write,
      CPPderef (CPPbinop (Bassign, CPPderef (CPPvar id_write), alloc_value ty v)),
      CPPaccess_call (Adot, CPPvar id_root, id_emplace, [v]) )

(** Write the base value [e] where the result is being assembled. *)
let place_base storage e =
  match storage with
  | Value_root ty ->
    [ Sasgn (id_value, Declare (Tauto, None), e);
      Sexpr (place_value ty (CPPmove (CPPvar id_value))) ]
  | Boxed_root ty ->
    [Sexpr (CPPbinop (Bassign, CPPderef (CPPvar id_write), alloc_value ty e))]
  | Pointer_result _ ->
    [Sexpr (CPPbinop (Bassign, CPPderef (CPPvar id_write), e))]

(** Build a constructor call with [nullptr] at the recursive argument position.

    When [~vt_ret] is [Some ret_ty], the factory method cannot accept [nullptr]
    because the recursive parameter is a value type.  Instead we construct the
    inner struct directly and wrap it:
    [std::make_unique<list<T>>(typename list<T>::Cons\{x, nullptr\})]

    @param token [Some e] routes the allocation through
      [crane::make_rc_reusing_unchecked], recycling the cell [e] denotes
      instead of allocating (see {!section:reuse-cursor}).  [None] allocates.
    @param cell A single TMC cell allocation descriptor
    @param vt_ret [Some ret_ty] for value-type returns, [None] otherwise *)
let build_cell_call ?token ?(rec_arg = CPPnullptr) ?(allocate = true) ~vt_ret cell =
  (* The cell being built is not always of the function's return type: a
     constructor may nest one of a DIFFERENT inductive ([rnode (cons r nil)]
     wraps the recursive [rose] in a [list rose]).  Allocate at the cell's own
     type, which [tca_type] carries. *)
  let mk_shared_cell = CPPalloc (Alloc_heap, cell.tca_type) in
  (* What that allocation yields, recorded at the one place that knows it. *)
  let shared_cell_sig =
    call_sig ~yields:(Tshared_ptr cell.tca_type) ~nargs:1 ()
  in
  let expr_builds_cell_type e =
    match is_ctor_factory_call e with
    | Some (_, _, ty, _, _) -> ty = cell.tca_type
    | None -> false
  in
  let args =
    List.init cell.tca_n_args (fun i ->
      if i = cell.tca_rec_field_idx then rec_arg
      else
        match List.assoc_opt i cell.tca_non_rec_args with
        | Some e when vt_ret <> None -> (
          match List.find_opt (fun f -> ptr_field_index f = i) cell.tca_ptr_fields with
          | Some (Boxed _) ->
            (* A boxed field holds some other inductive: allocate at the
               argument's own type. *)
            let boxed = Tdecay (Texpr_type e) in
            CPPfun_call
              ( call_sig ~yields:(Tshared_ptr boxed) ~nargs:1 (),
                CPPalloc (Alloc_heap, boxed),
                of_reversed [e] )
          | Some (Recursive _) ->
            CPPfun_call (shared_cell_sig, mk_shared_cell, of_reversed ([e]))
          | None when expr_builds_cell_type e ->
            CPPfun_call (shared_cell_sig, mk_shared_cell, of_reversed ([e]))
          | None -> e )
        | Some e -> e
        | None ->
          Cpp_erasure.converting_ctor Tany [] )
  in
  match vt_ret with
  | Some _ ->
    (* Direct struct construction wrapped in make_unique:
       std::make_unique<Type>(typename Type::Ctor{args...}) *)
    let struct_init =
      CPPtype_name (cell_struct cell)
    in
    let cell_expr = CPPfun_call (call_opaque, struct_init, of_reversed (args)) in
    if not allocate then cell_expr
    else (match token with
     | Some tok ->
       (* T is deduced from the token's [rc<T>]; the cell value is built from
          the constructor struct exactly as [make_rc] would build it. *)
       CPPfun_call (call_opaque, CPPrt Crane_rt.Make_rc_reusing_unchecked,
                    of_reversed ([cell_expr; tok]))   (* reversed: (token, cell) *)
     | None -> CPPfun_call (shared_cell_sig, mk_shared_cell, of_reversed ([cell_expr])))
  | None ->
    CPPfun_call (call_opaque, cell.tca_factory, of_reversed (args))

(** Borrowing fix-up for the TMC loop: the scrutinee is reached through a
    pointer shadow.  See the ownership discussion in {!transform_tmc} -- under
    the reuse cursor the scrutinee is owned but not known to be unique, and only
    [crane::reuse_step] may consume it. *)
let borrow_cursor_matches shadow_params stmts =
  Minicpp.borrow_matches_on
    (List.filter_map
       (fun (id, ty) -> match ty with Tptr _ -> Some id | _ -> None)
       shadow_params)
    stmts

(** Drop [std::move] from every read of a loop-invariant parameter.

    An invariant parameter lives in function scope and is read by every
    iteration of the loop, but the recursion it came from gave each activation
    its own copy.  Translation's last-use analysis sees only the source
    program's single syntactic occurrence, so it happily marks e.g. the base
    case of [repeat_with_sep] as [_result = std::move(s)] -- and the resume
    handler then reads [s] again on the next turn of the loop.  The last
    syntactic use is not the last dynamic use once the body is a loop.

    Types whose move constructor was suppressed (the iterative drain
    destructor) hid this: the "move" was a copy, so the stale read still saw a
    live value.  Restore cheap moves on those types and the same code
    segfaults, so this must be fixed for the loop shape itself, not for one
    special-member policy.

    Dropping a move only ever copies where it could have moved, so the pass
    cannot change meaning. *)
let unmove_in invariant_params ~block stmts =
  let rec expr = function
    | CPPmove (CPPvar id) when Id.Set.mem id invariant_params -> CPPvar id
    | CPPlambda l when List.exists (fun x -> Id.Set.mem x invariant_params) l.cl_moved ->
      expr
        (CPPlambda {l with cl_moved = List.filter (fun x -> not (Id.Set.mem x invariant_params)) l.cl_moved})
    | e -> map_expr ~fl:(block stmt) expr stmt Fun.id e
  and stmt s = map_stmt ~fl:(block stmt) expr stmt Fun.id s in
  if Id.Set.is_empty invariant_params then stmts else block stmt stmts

let unmove_invariant_params invariant_params stmts =
  unmove_in invariant_params ~block:List.map stmts

(** Drop the moves of a loop-invariant parameter from every path that goes
    round the loop again: a read the source program's single activation
    takes last -- a closure capturing it after the recursive call, in a tail
    modulo cons -- is read again by the next iteration.  A path that leaves
    the loop, by [break] or [return], is its last reader, and keeps its moves. *)
let unmove_invariant_on_continue invariant_params stmts =
  let rec mentions_continue l =
    List.exists
      (fun s ->
        s = Scontinue
        || fold_stmt_children ~on_expr:(fun acc _ -> acc)
             ~on_stmts:(fun acc l -> acc || mentions_continue l)
             false s )
      l
  in
  let leaves l =
    (match List.rev l with (Sbreak | Sreturn _ | Sthrow _) :: _ -> true | _ -> false)
    && not (mentions_continue l)
  in
  unmove_in invariant_params
    ~block:(fun stmt l -> if leaves l then l else List.map stmt l)
    stmts

(** [stmts], the loop's body, with every [break] that would leave only a
    [switch] replaced by [return ret], what follows the loop.  A base case
    leaves the loop by [break], and inside an enum's match, a [switch], that
    leaves the switch alone: the loop then goes round again on the same
    input, for ever.  An inner loop's [break] is its own, and a lambda's
    body is not this loop's. *)
let return_from_switches ret stmts =
  let rec block ~in_switch l = List.map (stmt ~in_switch) l
  and stmt ~in_switch = function
    | Sbreak when in_switch -> Sreturn (Some ret)
    | Sswitch (scrut, r, branches, default) ->
      Sswitch
        ( scrut, r,
          List.map (fun (p, b) -> (p, block ~in_switch:true b)) branches,
          Option.map (block ~in_switch:true) default )
    | (Swhile _ | Sfor_range _) as s -> s
    | s -> map_stmt Fun.id (stmt ~in_switch) Fun.id s
  in
  block ~in_switch:false stmts

(** Whether [e] reads a variable the recursive field [field] is reached
    through. *)
let reads_field field =
  let through = free_vars_expr field in
  fun e -> List.exists (fun v -> List.exists (Id.equal v) through) (free_vars_expr e)

(** The branch [br] with every read of [field] other than the cursor's own
    advance -- an argument of a cell, the next value of a shadow other than
    [cursor_id] -- bound to a temporary, and the declarations of those
    temporaries.  [reuse_step] moves the field out of a unique cell, so a read
    evaluated after it sees a null handle; the cell's constructor cannot run
    before it, since recycling destroys the old payload the field lives in. *)
let read_before_step ~cursor_id ~field varying shadow_params br =
  let reads = reads_field field in
  let decls = ref [] in
  let bind e =
    if not (reads e) then e
    else
      let n = List.length !decls in
      let id = Id.of_string (if n = 0 then "_read" else "_read" ^ string_of_int n) in
      decls := Sasgn (id, Declare (Tauto, None), e) :: !decls;
      CPPvar id
  in
  let cells =
    List.map
      (fun cell -> {cell with tca_non_rec_args = List.map (fun (i, e) -> (i, bind e)) cell.tca_non_rec_args})
      br.tmc_cells
  in
  let shadows = ref shadow_params in
  let rec_args =
    List.map2
      (fun is_varying e ->
        if not is_varying then e
        else
          match !shadows with
          | (sid, _) :: rest ->
            shadows := rest;
            if Id.equal sid cursor_id then e else bind e
          | [] -> e)
      varying br.tmc_rec_args
  in
  (List.rev !decls, {br with tmc_cells = cells; tmc_rec_args = rec_args})

(** {2:reuse-cursor Perceus reuse cursor}

    A TMC loop walks its input by borrowed pointer and allocates a fresh output
    cell per iteration.  When the input spine is owned and unshared, that is one
    allocation and one free per element for cells that are structurally the same
    shape -- the input cell is dead the moment its output counterpart is built.
    Recycling it directly is Perceus/FBIP reuse, and turns a linear traversal
    into a zero-allocation one.

    Two things are needed that the borrowed walk does not have.  First, an
    owning handle: a raw pointer cannot hand a cell to be recycled, so the loop
    carries [_own], the [rc] on the cell the cursor stands on ([_own] is null on
    the first iteration, where the cursor is on the by-value root -- not a heap
    cell, hence nothing to recycle).  Second, a uniqueness test, since a shared
    cell must not be touched; [_uniq] carries it, and latches false permanently
    on the first shared cell, because a cell reachable from another holder makes
    every deeper cell reachable too.

    Both live in [crane::reuse_step] (rc.h), which returns the recycling token
    and an owning handle on the recursive field -- taken before the cell is
    recycled out from under it.  The emitted body is therefore straight-line
    with no reuse branch of its own:

    {[
      const auto& [a0, a1] = std::get<Cons>(_loop_l->v());
      auto _rs   = crane::reuse_step(_own, _uniq, a1);
      auto _cell = crane::make_rc_reusing_unchecked(std::move(_rs.token),
                                                    lst::Cons(f(a0), nullptr));
      *_write = std::move(_cell);
      _write  = &std::get<Cons>(_cell->v_mut()).a1;   // via the new cell
      _own    = std::move(_rs.next);
      _loop_l = _own.get();
    ]}

    Identify the cursor: the single varying parameter that the loop walks by
    pointer and whose recursive argument is a dereference of one of the matched
    cell's fields, i.e. exactly the spine being consumed -- and whose cells are
    the output's own type, since a recycled cell is rebuilt in place: [combine]
    walks a [list B] beside the [list A] it consumes and builds a
    [list (A * B)], and no cell of either input is the right size for its
    output.  Everything else -- accumulators, unchanged parameters, several
    pointer-walked parameters at once -- yields [None] and the ordinary
    allocating path.

    [reuse_step] steals the recursive field, so whatever else the iteration
    reads of it is read first ({!read_before_step}); a temporary can hold a
    cell's argument or a value shadow's next value, but not another pointer
    shadow's, which would then point into the temporary -- such a walk
    declines the cursor. *)
let tmc_reuse_cursor ~storage varying shadow_params br =
  match storage with
  | Value_root _ | Pointer_result _ -> None
  | Boxed_root ret_ty ->
    let rec_args = filter_by_mask varying br.tmc_rec_args in
    if List.length rec_args <> List.length shadow_params then None
    else
      let rec pointee = function Tconst t -> pointee t | t -> t in
      let updates = List.combine shadow_params rec_args in
      let candidates =
        List.filter_map
          (fun ((sid, sty), arg) ->
            match sty, arg with
            | Tptr t, CPPderef inner when Ml_type_util.cpp_ty_eq (pointee t) ret_ty ->
              Some (sid, inner)
            | _ -> None)
          updates
      in
      match candidates with
      | [((cursor_id, field) as c)] ->
        let reads = reads_field field in
        if
          List.exists
            (fun ((sid, sty), arg) ->
              (not (Id.equal sid cursor_id))
              && (match sty with Tptr _ -> true | _ -> false)
              && reads arg)
            updates
        then None
        else Some c
      | _ -> None

(** Generate statements for a TMC branch with possibly nested constructor cells.
    Allocates all cells with [nullptr] holes, links consecutive pairs via
    {!patch_cell_field}, patches the destination with the outermost cell, and
    sets [_last] to the innermost.

    For a single cell (v1 behaviour), emits the same code as before.
    For nested cells (e.g., [cons x (cons x (RECURSE xs))]), emits:
    {[
      auto _cell  = Cons_(x, nullptr);    // outer
      auto _cell1 = Cons_(x, nullptr);    // inner
      outer.tail = _cell1;                // link
      <patch _head/_last with _cell>      // destination
      _last = _cell1;                     // advance
      <shadow updates>
    ]} *)
let build_tmc_branch_stmts ?(cursor_used = ref false) ?(derefs = []) ~storage br
    varying shadow_params =
  let vt_ret = cell_value_type storage in
  (* 0. Perceus reuse cursor.  See {!section:reuse-cursor}: when the loop walks
        an owned spine by pointer, the cell it is standing on is dead as soon as
        the iteration's output cell is built, so it can be recycled into that
        output instead of being freed and a fresh one allocated. *)
  let cursor = tmc_reuse_cursor ~storage varying shadow_params br in
  if cursor <> None then cursor_used := true;
  let step_decl, br =
    match cursor with
    | Some (cursor_id, rec_field) ->
      let reads, br = read_before_step ~cursor_id ~field:rec_field varying shadow_params br in
      (* CPPfun_call holds its arguments reversed (see translation.ml:1776),
         so [reuse_step(_own, _uniq, a1)] is written innermost-first here. *)
      ( reads
        @ [ Sasgn (id_rstep, Declare (Tauto, None),
                   CPPfun_call (call_opaque, CPPrt Crane_rt.Reuse_step,
                                of_reversed ([rec_field; CPPvar id_uniq; CPPvar id_own]))) ],
        br )
    | None -> ([], br)
  in
  let token =
    Option.map
      (fun _ ->
        CPPmove (CPPaccess (Adot, CPPvar id_rstep, Id.of_string "token")) )
      cursor
  in
  (* Generate unique cell names: _cell, _cell1, _cell2, ... *)
  let cell_names =
    List.mapi
      (fun i _ ->
        Id.of_string (if i = 0 then "_cell" else "_cell" ^ string_of_int i))
      br.tmc_cells
  in
  (* Link consecutive cells: outer.rec_field = inner.  For value-type returns
     the inner cell is moved into the outer, so the links are made
     innermost-first, or an outer link would read a moved-from pointer. *)
  let rec link_cells cells names =
    match cells, names with
    | cell :: rest_cells, outer_name :: (inner_name :: _ as rest_names) ->
      patch_cell_field cell
        (CPPvar outer_name)
        (match vt_ret with
         | Some _ -> CPPmove (CPPvar inner_name)
         | None -> CPPvar inner_name)
      :: link_cells rest_cells rest_names
    | _ -> []
  in
  (* The recursive field of the innermost cell, reached from [ptr] -- the
     outermost cell, read through [access] -- down the chain's recursive
     fields, which are pointers. *)
  let rec innermost_hole access ptr = function
    | [] -> assert false
    | [cell] ->
      let obj, field_id = cell_rec_field ~access cell ptr in
      CPPget (obj, field_id)
    | cell :: rest ->
      let obj, field_id = cell_rec_field ~access cell ptr in
      innermost_hole Aarrow (CPPget (obj, field_id)) rest
  in
  let advance_to hole =
    Sexpr (CPPbinop (Bassign, CPPvar id_write, CPPunop (Uaddr, hole)))
  in
  let placement =
    match storage with
    | Value_root ty ->
      (* The cells below the first are allocated and linked as ever; the first
         is built as a value with the chain already in its recursive field, and
         becomes the root or fills the hole. *)
      let inner_cells = List.tl br.tmc_cells and inner_names = List.tl cell_names in
      let inner_decls =
        List.map
          (fun (cell_id, cell) ->
            Sasgn (cell_id, Declare (Tauto, None), build_cell_call ~vt_ret cell))
          (List.combine inner_names inner_cells)
      in
      let inner_links = List.rev (link_cells inner_cells inner_names) in
      let rec_arg =
        match inner_names with
        | n :: _ -> CPPmove (CPPvar n)
        | [] -> CPPnullptr
      in
      let outer = List.hd br.tmc_cells in
      inner_decls @ inner_links
      @ [ Sasgn
            ( List.hd cell_names,
              Declare (Tauto, None),
              build_cell_call ~rec_arg ~allocate:false ~vt_ret outer );
          Sasgn
            ( id_node,
              Declare (Tref (Lvalue, ty), None),
              place_value ty (CPPmove (CPPvar (List.hd cell_names))) );
          advance_to (innermost_hole Adot (CPPvar id_node) br.tmc_cells) ]
    | Boxed_root _ | Pointer_result _ ->
      (* Only the outermost cell may take the token: one input cell dies per
         iteration, so a nested chain still recycles exactly one of its cells. *)
      let cell_decls =
        List.mapi
          (fun i (cell_id, cell) ->
            let token = if i = 0 then token else None in
            Sasgn (cell_id, Declare (Tauto, None), build_cell_call ?token ~vt_ret cell))
          (List.combine cell_names br.tmc_cells)
      in
      let link_stmts = List.rev (link_cells br.tmc_cells cell_names) in
      let outermost = CPPvar (List.hd cell_names) in
      let patch =
        Sexpr
          (CPPbinop
             ( Bassign,
               CPPderef (CPPvar id_write),
               match storage with
               | Boxed_root _ -> CPPmove outermost
               | _ -> outermost ))
      in
      let hole =
        match storage with
        | Boxed_root _ ->
          (* The chain is held inside the cells, so walk down from [*_write]
             through each outer cell's recursive field. *)
          innermost_hole Aarrow (CPPderef (CPPvar id_write)) br.tmc_cells
        | _ ->
          innermost_hole Aarrow
            (CPPvar (List.rev cell_names |> List.hd))
            [List.rev br.tmc_cells |> List.hd]
      in
      cell_decls @ link_stmts @ [patch; advance_to hole]
  in
  (* Shadow variable updates.  The cursor advances through [_own] instead:
     the recursive field has been stolen into [_rs.next] (the cell it lived
     in may since have been recycled), and [_own] is what keeps the next cell
     alive now that the current one is gone. *)
  let shadow_updates =
    make_shadow_updates ~derefs shadow_params (filter_by_mask varying br.tmc_rec_args)
  in
  let shadow_updates =
    match cursor with
    | None -> shadow_updates
    | Some (cursor_id, _) ->
      let is_cursor_update = function
        | Sasgn (id, Existing, _) | Sexpr (CPPbinop (Bassign, CPPvar id, _)) ->
          Id.equal id cursor_id
        | _ -> false
      in
      List.filter (fun s -> not (is_cursor_update s)) shadow_updates
      @ [ Sexpr (CPPbinop (Bassign, CPPvar id_own,
                           CPPmove (CPPaccess (Adot, CPPvar id_rstep,
                                               Id.of_string "next"))));
          Sexpr (CPPbinop (Bassign, CPPvar cursor_id,
                           CPPaccess_call (Adot, CPPvar id_own, id_get, []))) ]
  in
  step_decl @ placement @ shadow_updates

(** Rewrite a single statement for TMC loopification.

    Constructs a TMC {!top_rewrite_config} and delegates to
    {!generic_rewrite_stmt}.  The inner config emits a plain [Sif].  Base
    returns patch the write pointer and break; TMC branches allocate cells
    with holes.  Tail calls
    at the top level append [Scontinue]; inside visitor lambdas they do not
    (the lambda returns and the [while] loop naturally continues).

    @param storage where the result is assembled
    @param branch  a returned expression as a TMC branch ({!branch_along})
    @param check   Call checker for identifying recursive calls *)
let rewrite_tmc_visit_stmt ?(cursor_used = ref false) ~jumped ~storage ~branch check
    varying shadow_params =
  (* Emit code for a non-tail return in the TMC context.
     [suffix] is appended after TMC branches: empty inside visitor lambdas,
     [[Scontinue]] at the top level. *)
  let tmc_on_other_return ~derefs ~suffix e =
    let n = count_calls_expr check e in
    if n = 0 then
      (* Base case — patch destination and stop *)
      place_base storage e @ [Sbreak]
    else
      (* TMC branch — allocate cell(s) with holes, patch, continue *)
      match branch e with
      | Some br ->
        jumped br.tmc_call;
        build_tmc_branch_stmts ~cursor_used ~derefs ~storage br varying shadow_params
        @ suffix
      | None ->
        (* A call the plan's chains do not reach stays a call; the loop is
           then not taken ({!Loopify.apply_nontail_loopification}). *)
        [Sreturn (Some e)]
  in
  let inner_rc =
    { rc_check = check;
      rc_varying = varying;
      rc_shadow_params = shadow_params;
      rc_jumped = jumped }
  in
  generic_rewrite_stmt
    { trc_inner = inner_rc;
      trc_tail_suffix = [Scontinue];
      trc_on_other =
        (fun ~derefs e -> wrap_as_block (tmc_on_other_return ~derefs ~suffix:[Scontinue] e));
      trc_rewrite_branch = Fun.id;
      trc_detect_void_tail = false }

(** Transform a TMC-eligible function body into a [while] loop with
    destination-passing style.

    @param param_inits Optional custom initializers for shadow variables
    @param jumped told each recursive call rewritten: a tail call into a jump,
                  and the call a branch's cells are built around
    @param varying which parameters the loop varies, where the caller knows;
                   read off the calls otherwise
    @param shapes the branches' shapes ({!branch_along})
    @param check Call checker for identifying recursive calls
    @param params Function parameters
    @param ret_ty Return type
    @param body Function body
    @return Transformed body with TMC while loop *)
let transform_tmc ?(param_inits = []) ?(jumped = ignore) ?varying ~shapes tparams check params ret_ty body =
  let branch = branch_along shapes check in
  let storage = storage_of ret_ty in
  let { ss_varying = varying; ss_varying_params = varying_params;
        ss_shadow_params = shadow_params; ss_subs = subs } =
    build_shadow_setup ?varying tparams check params body
  in
  (* Where the result is assembled, and the hole [_write] starts at. *)
  let head_ty = match storage with
    | Value_root t | Boxed_root t -> Tshared_ptr t
    | Pointer_result t -> t
  in
  let root_decls =
    match storage with
    | Value_root t ->
      [ Sdecl_init (id_root, Tid_external ((Cpp_state.sn ()).ns ^ "::optional", [t]));
        Sasgn (id_write, Declare (Tptr head_ty, None), CPPnullptr) ]
    | Boxed_root _ | Pointer_result _ ->
      [ Sdecl_init (id_head, head_ty);
        Sasgn (id_write, Declare (Tptr head_ty, None), CPPunop (Uaddr, CPPvar id_head)) ]
  in
  (* Shadow variable declarations.
     For pointer params with custom inits (e.g., _self = this in methods), only
     strip references but keep const — const T* must stay const to match this.
     For other params (typically const shared_ptr<T>&), strip both ref and const
     so the shadow variable becomes a mutable shared_ptr<T>. *)
  let shadow_decls =
    List.map2
      (fun (orig_id, ty) (shadow_id, shadow_ty) ->
        let has_custom_init = List.mem_assoc orig_id param_inits in
        let init_expr =
          match List.assoc_opt orig_id param_inits with
          | Some custom -> custom
          | None -> tail_shadow_init orig_id shadow_ty ty
        in
        (* Declare the shadow at the shadow's type, not the parameter's: where
           {!tail_shadow_type} chose something else, it chose it because the
           parameter's own type cannot hold what the loop will put here. *)
        let decl_ty = match shadow_ty with
          | Tptr _ -> shadow_ty
          | _ ->
            if has_custom_init then strip_ref_type shadow_ty
            else strip_ref_and_const_type shadow_ty
        in
        Sasgn (shadow_id, Declare (decl_ty, None), init_expr) )
      varying_params
      shadow_params
  in
  (* Substitute param references in body *)
  let body' = List.map (subst_stmt subs) body in
  (* Rewrite body for TMC, then flatten unnecessary Sblock wrappers *)
  let cursor_used = ref false in
  let body'' =
    List.map
      (rewrite_tmc_visit_stmt ~cursor_used ~jumped ~storage ~branch check varying shadow_params)
      body'
    |> strip_unnecessary_blocks
    |> rewrite_borrowed_shadow_uses shadow_params
  in
  (* The matches the loop reads through its pointer shadows.  Escape analysis
     may have passed a scrutinee owned so that a loop would have cells to
     recycle, which also made translation emit a destructive match ([auto&]
     over [v_mut()], fields moved out).  That is exactly what must not happen
     here: a shadow is a [const] pointer to a cell the loop does not own --
     under the reuse cursor, whether the cell may be consumed is not known
     until [reuse_step] tests it, and on a shared spine moving its fields out
     would corrupt the other holder; without the cursor (a walk the cursor
     declined, [combine]'s second list) nothing may consume it at all.  So the
     matches revert to borrowing, and [reuse_step] does the one steal that is
     licensed -- the recursive field of a cell it has just proven unique. *)
  let body'' = borrow_cursor_matches shadow_params body'' in
  let cursor_decls =
    if not !cursor_used then []
    else
      [ Sasgn (id_own, Declare (head_ty, None), Cpp_erasure.converting_ctor head_ty []);
        (* [Tid] is the *user-defined* type constructor, so the printer
           namespace-qualifies it ("Mod::bool").  This is the builtin, which
           must never be qualified. *)
        Sasgn
          ( id_uniq,
            Declare (Tid_external ("bool", []), None),
            CPPbool true )
      ]
  in
  let ret_expr = match storage with
    | Value_root _ -> CPPmove (CPPderef (CPPvar id_root))
    | Boxed_root _ -> CPPmove (CPPderef (CPPvar id_head))
    | Pointer_result _ -> CPPvar id_head
  in
  let shadow_decls, body'' = drop_unread_shadows shadow_decls body'' in
  let body'' = strip_unnecessary_blocks body'' in
  let invariant_params =
    Id.Set.of_list (List.filteri (fun i _ -> not (List.nth varying i)) (List.map fst params))
  in
  let body'' = unmove_invariant_on_continue invariant_params body'' in
  let body'' = return_from_switches ret_expr body'' in
  root_decls
  @ cursor_decls
  @ shadow_decls
  @ [
      Swhile (CPPbool true, body'');
      Sreturn (Some ret_expr);
    ]
