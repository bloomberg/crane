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
  tca_type : cpp_type;
      (** The type the factory is qualified by, e.g., [list<T>] *)
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
}

(** Summary of TMC analysis for a whole function.  The type is a unit-like
    marker: [Some ()] signals that all TMC branches are eligible and use the
    same constructor and recursive field.  The per-branch details are carried
    directly in the [tmc_cell_alloc] records inside each [tmc_branch]. *)
type tmc_info = unit [@@warning "-34"]

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
    [Type::cons(args)].  Returns [(ty, ctor_name, factory_name, args)]
    where [ty] is the base type (e.g., [list<T>]), [ctor_name] is the
    constructor struct name (e.g., ["Cons"]), [factory_name] is the factory
    method name (e.g., ["cons"]), and [args] are the constructor arguments.

    Factory calls are the only use of [CPPfun_call(CPPqualified_t(...), ...)]
    in the MiniCpp AST.  The struct name is the capitalized factory name. *)
let is_ctor_factory_call = function
  | CPPfun_call (_, CPPqualified_t (ty, factory_id), args) ->
    let factory_s = Id.to_string factory_id in
    let n = String.length factory_s in
    (* Strip trailing underscore (collision escape) before capitalizing *)
    let base =
      if n > 0 && factory_s.[n - 1] = '_' then
        String.sub factory_s 0 (n - 1)
      else factory_s
    in
    let struct_name = String.capitalize_ascii base in
    (* A genuine TMC-wrapping data constructor always has a recursive
       (shared_ptr) field — the hole the recursion writes into — so it is
       recorded in [ctor_ptr_fields].  A qualified call whose "constructor" is
       NOT registered there is not a data constructor at all (e.g. a record's
       function-typed field applied as [M::m_op(x, rec)] on the abstract record
       type); TMC-decomposing it would fabricate a nonexistent variant cell with
       a [nullptr] hole.  Requiring registration rejects those. *)
    (* Skip built-in accessors and other non-factory qualified calls *)
    let ptr_fields =
      match cell_owner ty with
      | Some owner ->
        Hashtbl.find_opt ctor_ptr_fields
          (Common.ctor_owner_key owner, struct_name)
      | None -> None
    in
    if factory_s = "v" || factory_s = "v_mut" || factory_s = "lazy_"
       || ptr_fields = None
    then None
    else
      (* The arguments come back as stored -- reversed.  Everything downstream
         indexes them in that space; see [uptr_idxs] in [try_tmc_decompose]. *)
      Some (ty, struct_name, factory_s, to_reversed args)
  | _ -> None

(** Try to decompose a return expression as a TMC-eligible branch.  Handles
    both single-level ([cons x (RECURSE xs)]) and nested constructors
    ([cons x (cons x (RECURSE xs))]).  Strips [CPPmove] wrapping before
    checking.

    {b Example.}  Given [cons x (cons y (f xs))]:
    - Outer constructor [cons(x, HOLE)] is cell 0 (allocated first, returned to
      the caller via [_head]).
    - Inner constructor [cons(y, HOLE)] is cell 1 (allocated second, linked
      into cell 0's recursive field).
    - [f xs] is the recursive call that fills cell 1's HOLE.

    Cells are returned outermost-first so the caller can chain them:
    allocate cell 0, allocate cell 1, link cell 1 into cell 0, then loop with
    [_last] pointing to cell 1 for the next iteration to fill.

    @return [Some tmc_branch_info] with a chain of cells, outermost first *)
let rec try_tmc_decompose check expr =
  let expr' = match expr with CPPmove e -> e | e -> e in
  match is_ctor_factory_call expr' with
  | None -> None
  | Some (cell_ty, ctor_name, factory_s, args) ->
    let n_args = List.length args in
    let indexed = List.mapi (fun i a -> (i, a)) args in
    let non_rec_of idx =
      List.filter_map
        (fun (i, a) -> if i <> idx then Some (i, a) else None)
        indexed
    in
    let make_cell idx =
      let uptr_idxs =
        (* [ctor_ptr_fields] records shared_ptr field positions in STRUCT-field
           order, but [idx]/[tca_non_rec_args] here index into [args] from
           [is_ctor_factory_call], which are stored REVERSED (as [CPPfun_call]
           keeps them).  Map the struct-order positions into the same reversed
           arg-space ([n_args - 1 - j]) so [build_cell_call]'s lookup of an
           argument's field aligns — otherwise a non-pointer field (e.g. a
           [cons] element) is spuriously [make_shared]-wrapped. *)
        match
          match cell_owner cell_ty with
          | Some owner ->
            Hashtbl.find_opt ctor_ptr_fields
              (Common.ctor_owner_key owner, ctor_name)
          | None -> None
        with
        | Some fields ->
          List.map
            (function
              | Recursive j -> Recursive (n_args - 1 - j)
              | Boxed j -> Boxed (n_args - 1 - j))
            fields
        | None -> [Recursive idx]
      in
      {
      tca_factory =
        CPPqualified_t (cell_ty, Id.of_string factory_s);
      tca_type = cell_ty;
      tca_ctor_name = ctor_name;
      tca_rec_field_idx = idx;
      tca_non_rec_args = non_rec_of idx;
      tca_n_args = n_args;
      tca_ptr_fields = uptr_idxs;
    } in
    (* Find which args are direct recursive calls *)
    let direct =
      List.filter_map
        (fun (i, a) ->
          match check a with Some cs -> Some (i, cs) | None -> None)
        indexed
    in
    ( match direct with
    | [(idx, cs)] ->
      (* Single direct recursive call — innermost cell.  Destination passing
         needs a hole it can leave empty and point at, so the field the call
         fills must be a [shared_ptr].  It is not always: a constructor may
         nest one of another inductive whose corresponding field is a value
         ([rnode (cons r nil)] fills [list rose]'s element).  There is no null
         [rose] to write, so such a chain is not TMC-eligible and the function
         stays plainly recursive. *)
      let cell = make_cell idx in
      if not (List.exists (fun f -> ptr_field_index f = idx) cell.tca_ptr_fields) then None
      else Some { tmc_cells = [cell]; tmc_rec_args = cs.cs_args }
    | [] ->
      (* No direct call — look for a nested constructor wrapping a call *)
      let nested =
        List.filter_map
          (fun (i, a) ->
            if count_calls_expr check a = 1 then Some (i, a) else None)
          indexed
      in
      ( match nested with
      | [(idx, nested_expr)] ->
        ( match try_tmc_decompose check nested_expr with
        | Some inner ->
          Some { tmc_cells = make_cell idx :: inner.tmc_cells;
                 tmc_rec_args = inner.tmc_rec_args }
        | None -> None )
      | _ -> None )
    | _ -> None (* Multiple direct calls — not TMC *) )

(** Classify an entire function body for TMC eligibility.  Walks all return
    positions (including inside match branches) and checks that:
    - Every return is either a tail call, a base case (0 recursive calls), or a
      TMC-eligible constructor wrapping
    - All TMC branches use the {e same} constructor name and recursive field

    @return [Some tmc_info] if the function is TMC-eligible *)
let try_tmc_classify check body =
  (* Scan a single return expression, threading (branches, compatible) *)
  let scan_return_expr (branches, compatible) e =
    if not compatible then (branches, false)
    else
      match check e with
      | Some _ -> (branches, compatible) (* tail call — compatible *)
      | None ->
        let n = count_calls_expr check e in
        if n = 0 then (branches, compatible) (* base case *)
        else if n = 1 then (
          match try_tmc_decompose check e with
          | Some br -> (br :: branches, compatible)
          | None -> (branches, false) )
        else (branches, false)
  in
  (* Walk all return positions in statements, scanning each for TMC
     eligibility. *)
  let rec scan_stmts acc stmts = List.fold_left scan_stmt acc stmts
  and scan_stmt acc = function
    | Sreturn (Some e) -> scan_return_expr acc e
    | Sif (_, then_br, else_br) ->
      scan_stmts (scan_stmts acc then_br) else_br
    | Scustom_case (_, _, _, branches, _) ->
      List.fold_left (fun acc (_, _, body) -> scan_stmts acc body) acc branches
    | Sswitch (_, _, branches, _) ->
      List.fold_left (fun acc (_, body) -> scan_stmts acc body) acc branches
    | Smatch (scrut, branches, default) ->
      let acc =
        List.fold_left (fun acc br -> scan_stmts acc br.smb_body) acc branches in
      (match default with Some ss -> scan_stmts acc ss | None -> acc)
    | Sblock stmts -> scan_stmts acc stmts
    | _ -> acc
  in
  let (tmc_branches, compatible) = scan_stmts ([], true) body in
  if not compatible || tmc_branches = [] then None
  else
    let first = List.hd tmc_branches in
    (* All branches must use the same innermost constructor and recursive
       field — the innermost cell determines _head/_last type and patching. *)
    let inner br = List.rev br.tmc_cells |> List.hd in
    let first_inner = inner first in
    let all_same =
      List.for_all
        (fun br ->
          let i = inner br in
          i.tca_ctor_name = first_inner.tca_ctor_name
          && i.tca_rec_field_idx = first_inner.tca_rec_field_idx )
        tmc_branches
    in
    if all_same then Some ()
    else None

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
let cell_rec_field ?(access = Aarrow) ~cell_ty ~ctor_name ~n_args ~rec_field_idx ptr =
  let field_idx = n_args - 1 - rec_field_idx in
  let v_mut = CPPaccess_call (access, ptr, id_v_mut, []) in
  ( CPPstd_get (Tqualified (cell_ty, Id.of_string ctor_name), Some v_mut),
    cell_field_name ~cell_ty ~ctor_name field_idx )

let patch_cell_field ~cell_ty ~ctor_name ~n_args ~rec_field_idx ptr val_expr =
  let obj, field_id =
    cell_rec_field ~cell_ty ~ctor_name ~n_args ~rec_field_idx ptr
  in
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
    [ Sasgn (id_value, Declare Tauto, e);
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
    | Some (ty, _, _, _) -> ty = cell.tca_type
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
      CPPtype_name (Tqualified (cell.tca_type, Id.of_string cell.tca_ctor_name))
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
let unmove_invariant_params invariant_params stmts =
  if Id.Set.is_empty invariant_params then stmts
  else
    let rec expr = function
      | CPPmove (CPPvar id) when Id.Set.mem id invariant_params -> CPPvar id
      | e -> map_expr expr stmt Fun.id e
    and stmt s = map_stmt expr stmt Fun.id s in
    List.map stmt stmts

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
    allocating path. *)
let tmc_reuse_cursor ~storage varying shadow_params br =
  match storage with
  | Value_root _ | Pointer_result _ -> None
  | Boxed_root ret_ty ->
    let rec_args = filter_by_mask varying br.tmc_rec_args in
    if List.length rec_args <> List.length shadow_params then None
    else
      let rec pointee = function Tconst t -> pointee t | t -> t in
      let candidates =
        List.filter_map
          (fun ((sid, sty), arg) ->
            match sty, arg with
            | Tptr t, CPPderef inner when Ml_type_util.cpp_ty_eq (pointee t) ret_ty ->
              Some (sid, inner)
            | _ -> None)
          (List.combine shadow_params rec_args)
      in
      match candidates with [c] -> Some c | _ -> None

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
let build_tmc_branch_stmts ?(cursor_used = ref false) ~storage br
    varying shadow_params =
  let vt_ret = cell_value_type storage in
  (* 0. Perceus reuse cursor.  See {!section:reuse-cursor}: when the loop walks
        an owned spine by pointer, the cell it is standing on is dead as soon as
        the iteration's output cell is built, so it can be recycled into that
        output instead of being freed and a fresh one allocated. *)
  let cursor = tmc_reuse_cursor ~storage varying shadow_params br in
  if cursor <> None then cursor_used := true;
  let step_decl =
    match cursor with
    | Some (_, rec_field) ->
      (* CPPfun_call holds its arguments reversed (see translation.ml:1776),
         so [reuse_step(_own, _uniq, a1)] is written innermost-first here. *)
      [ Sasgn (id_rstep, Declare Tauto,
               CPPfun_call (call_opaque, CPPrt Crane_rt.Reuse_step,
                            of_reversed ([rec_field; CPPvar id_uniq; CPPvar id_own]))) ]
    | None -> []
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
      patch_cell_field
        ~cell_ty:cell.tca_type ~ctor_name:cell.tca_ctor_name
        ~n_args:cell.tca_n_args ~rec_field_idx:cell.tca_rec_field_idx
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
      let obj, field_id =
        cell_rec_field ~access ~cell_ty:cell.tca_type ~ctor_name:cell.tca_ctor_name
          ~n_args:cell.tca_n_args ~rec_field_idx:cell.tca_rec_field_idx ptr
      in
      CPPget (obj, field_id)
    | cell :: rest ->
      let obj, field_id =
        cell_rec_field ~access ~cell_ty:cell.tca_type ~ctor_name:cell.tca_ctor_name
          ~n_args:cell.tca_n_args ~rec_field_idx:cell.tca_rec_field_idx ptr
      in
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
            Sasgn (cell_id, Declare Tauto, build_cell_call ~vt_ret cell))
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
              Declare Tauto,
              build_cell_call ~rec_arg ~allocate:false ~vt_ret outer );
          Sasgn
            ( id_node,
              Declare (Tref (Lvalue, ty)),
              place_value ty (CPPmove (CPPvar (List.hd cell_names))) );
          advance_to (innermost_hole Adot (CPPvar id_node) br.tmc_cells) ]
    | Boxed_root _ | Pointer_result _ ->
      (* Only the outermost cell may take the token: one input cell dies per
         iteration, so a nested chain still recycles exactly one of its cells. *)
      let cell_decls =
        List.mapi
          (fun i (cell_id, cell) ->
            let token = if i = 0 then token else None in
            Sasgn (cell_id, Declare Tauto, build_cell_call ?token ~vt_ret cell))
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
    make_shadow_updates shadow_params (filter_by_mask varying br.tmc_rec_args)
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

    @param vt_ret  [Some ret_ty] when the return type is a value type
    @param check   Call checker for identifying recursive calls
    @param ti      TMC info from {!try_tmc_classify} *)
let rewrite_tmc_visit_stmt ?(cursor_used = ref false) ~storage check
    varying shadow_params =
  (* Emit code for a non-tail return in the TMC context.
     [suffix] is appended after TMC branches: empty inside visitor lambdas,
     [[Scontinue]] at the top level. *)
  let tmc_on_other_return ~suffix e =
    let n = count_calls_expr check e in
    if n = 0 then
      (* Base case — patch destination and stop *)
      place_base storage e @ [Sbreak]
    else
      (* TMC branch — allocate cell(s) with holes, patch, continue *)
      match try_tmc_decompose check e with
      | Some br ->
        build_tmc_branch_stmts ~cursor_used ~storage br varying shadow_params
        @ suffix
      | None ->
        (* Fallback: shouldn't happen if try_tmc_classify was correct *)
        [Sreturn (Some e)]
  in
  let inner_rc =
    { rc_check = check;
      rc_varying = varying;
      rc_shadow_params = shadow_params }
  in
  generic_rewrite_stmt
    { trc_inner = inner_rc;
      trc_tail_suffix = [Scontinue];
      trc_on_other =
        (fun e -> wrap_as_block (tmc_on_other_return ~suffix:[Scontinue] e));
      trc_rewrite_branch = Fun.id;
      trc_detect_void_tail = false }

(** Transform a TMC-eligible function body into a [while] loop with
    destination-passing style.

    @param param_inits Optional custom initializers for shadow variables
    @param check Call checker for identifying recursive calls
    @param ti TMC info from {!try_tmc_classify}
    @param params Function parameters
    @param ret_ty Return type
    @param body Function body
    @return Transformed body with TMC while loop *)
let transform_tmc ?(param_inits = []) tparams check params ret_ty body =
  let storage = storage_of ret_ty in
  let { ss_varying = varying; ss_varying_params = varying_params;
        ss_shadow_params = shadow_params; ss_subs = subs } =
    build_shadow_setup tparams check params body
  in
  (* Where the result is assembled, and the hole [_write] starts at. *)
  let head_ty = match storage with
    | Value_root t | Boxed_root t -> Tshared_ptr t
    | Pointer_result t -> t
  in
  let root_decls =
    match storage with
    | Value_root t ->
      Common.require_header "optional";
      [ Sdecl_init (id_root, Tid_external ((Cpp_state.sn ()).ns ^ "::optional", [t]));
        Sasgn (id_write, Declare (Tptr head_ty), CPPnullptr) ]
    | Boxed_root _ | Pointer_result _ ->
      [ Sdecl_init (id_head, head_ty);
        Sasgn (id_write, Declare (Tptr head_ty), CPPunop (Uaddr, CPPvar id_head)) ]
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
        Sasgn (shadow_id, Declare decl_ty, init_expr) )
      varying_params
      shadow_params
  in
  (* Substitute param references in body *)
  let body' = List.map (subst_stmt subs) body in
  (* Rewrite body for TMC, then flatten unnecessary Sblock wrappers *)
  let cursor_used = ref false in
  let body'' =
    List.map
      (rewrite_tmc_visit_stmt ~cursor_used ~storage check varying shadow_params)
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
      [ Sasgn (id_own, Declare head_ty, Cpp_erasure.converting_ctor head_ty []);
        (* [Tid] is the *user-defined* type constructor, so the printer
           namespace-qualifies it ("Mod::bool").  This is the builtin, which
           must never be qualified. *)
        Sasgn
          ( id_uniq,
            Declare (Tid_external ("bool", [])),
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
  root_decls
  @ cursor_decls
  @ shadow_decls
  @ [
      Swhile (CPPbool true, body'');
      Sreturn (Some ret_expr);
    ]
