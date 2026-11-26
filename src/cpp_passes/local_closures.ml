(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Local closures made and used in one place, rewritten as the code they
    stand for.  See [cpp_local_closures.mli]. *)

open Names
module IdSet = Id.Set
module V = Cpp_ir.Variables

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type lambda = Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t

(** {1 Shared pieces} *)

(* A rewrite of the children of a node: [expr] for expressions, [stmt] for
   statements. *)
let children ~expr ~stmt : Cpp_ir.Lowered.phase Cpp_ir.Map.t = Cpp_ir.Map.make ~expr ~stmt ~type_:Fun.id ()

(* Visits of the expressions and statements below a node. *)
let visit ~expr ~stmt : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor = {expr; stmt; type_ = (fun _ -> ())}

(* Whether [stmts] can return, other than from a lambda nested in them. *)
let has_return (stmts : stmt list) =
  let exception Found in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = ignore}
  and expr (e : expr) = match e with Lambda _ -> () | _ -> Cpp_ir.Children.expr v e
  and stmt (s : stmt) = match s with Return _ -> raise_notrace Found | _ -> Cpp_ir.Children.stmt v s in
  match List.iter stmt stmts with () -> false | exception Found -> true

(* Whether [stmts] read [x] free. *)
let mentions x stmts = V.mem x (V.free_in_body stmts)

(* A lambda's parameters, an unnamed one named [_argI] -- its argument is
   still evaluated, then never read -- when it has no template parameters. *)
let named_params (l : lambda) =
  if l.type_params <> [] then None
  else
    Some
      (List.mapi
         (fun i (ty, x) ->
           match x with Some x -> (x, ty) | None -> (Id.of_string (Printf.sprintf "_arg%d" i), ty) )
         l.params )

(* What [stmts] declare at their own level: the names a splice puts into the
   scope around it.  A name declared deeper -- in a branch, a block, a
   nested lambda -- stays where it was. *)
let declared_here (stmts : stmt list) =
  List.concat_map
    (function
      | (Bind_variable (id, (Declare _ | Declare_deduced _), _) | Declare (id, _, _) | Declare_value_initialized (id, _) : stmt) -> [id]
      | Structured_binding (ids, _) -> ids
      | Foreign_block b -> [b.result]
      | _ -> [] )
    stmts

(* [stmts] with [f] applied to every identifier they declare or read: a
   local, every kind of declaration, a match's and a mapping's binders, a
   lambda's parameters and the names its local fixpoint goes by.  Applied to
   all of them alike it renames consistently, so a body comes out
   alpha-equivalent as long as [f]'s fresh names are fresh.  A type is left
   as it is.  What a lambda captures by move is a variable of the enclosing
   body, renamed with it. *)
let rename_ids f stmts =
  let keys = List.map (fun (x, b) -> (f x, b)) in
  let rec expr (e : expr) : expr =
    match e with
    | Local x -> Local (f x)
    | Lambda l ->
      let fixpoint (lf : Cpp_ir.Expr.Local_fixpoint.t) : Cpp_ir.Expr.Local_fixpoint.t =
        { lf with
          name = f lf.name;
          captured = keys lf.captured;
          encoding =
            (match lf.encoding with Self_passing selves -> Self_passing (List.map f selves)
              | (Knot | Lowered) as e -> e) }
      in
      Cpp_ir.Map.expr (m ())
        (Lambda
           { l with
             params = List.map (fun (t, x) -> (t, Option.map f x)) l.params;
             moved = List.map f l.moved;
             binders = keys l.binders;
             fixpoint = Option.map fixpoint l.fixpoint })
    | _ -> Cpp_ir.Map.expr (m ()) e
  and stmt (s : stmt) : stmt =
    let renamed : stmt =
      match s with
      | Bind_variable (x, b, e) -> Bind_variable (f x, b, e)
      | Declare (x, t, b) -> Declare (f x, t, b)
      | Declare_value_initialized (x, t) -> Declare_value_initialized (f x, t)
      | Structured_binding (xs, e) -> Structured_binding (List.map f xs, e)
      | If_declaration i -> If_declaration {i with name = f i.name}
      | For_range (x, e, ss) -> For_range (f x, e, ss)
      | Foreign_block b -> Foreign_block {b with result = f b.result}
      | Match (sc, branches, default) ->
        let branch (b : _ Cpp_ir.Stmt.Match.branch) : _ Cpp_ir.Stmt.Match.branch =
          { b with
            var = Option.map f b.var;
            field_bindings = List.map
              (fun (fb : _ Cpp_ir.Stmt.Match.field_binding) -> {fb with name = f fb.name}) b.field_bindings }
        in
        Match (sc, List.map branch branches, default)
      | Custom_match c ->
        let branch (b : _ Cpp_ir.Stmt.Custom_match.branch) : _ Cpp_ir.Stmt.Custom_match.branch =
          {b with params = List.map (fun (p : _ Cpp_ir.Stmt.Custom_match.param) -> {p with name = f p.name}) b.params}
        in
        Custom_match {c with branches = List.map branch c.branches}
      | _ -> s
    in
    Cpp_ir.Map.stmt (m ()) renamed
  and m () = children ~expr ~stmt in
  List.map stmt stmts

(** A lambda opened up for splicing into the body around it: its parameters
    bound to the arguments and its locals given names nothing else in the
    function has -- [_lc<k>_x], [k] new at every expansion -- so that two
    expansions of one lambda, or one and the code around it, cannot
    collide. *)
type expansion = {
  bindings : stmt list;  (** the parameters, bound to the arguments *)
  body : stmt list;  (** the lambda's statements *)
}

(** The variable an argument names: [y] itself, or [y] moved from. *)
let named_variable (a : expr) = match a with Local y | Move (Local y) -> Some y | _ -> None

(** The parameters of [l] that may stand for the variable their argument in
    [args] names, rather than be bound to it: a parameter [p] whose argument
    is [y] or [std::move(y)], when [l] never assigns [p], does not name [y]
    itself -- free, or declared at any depth, where a reference to [y] would
    mean another variable -- and no other argument names [y].  Reading [p]
    is then reading [y].  Used only where the call is the last thing its
    body does, so that nothing reads [y] after the lambda's statements could
    have changed what it holds. *)
let aliased_params (l : lambda) params args =
  let free = V.free_in_body l.body
  and assigned = V.assigned l.body
  and declared = V.declared l.body in
  let vars = List.filter_map named_variable args in
  let once y = List.length (List.filter (Id.equal y) vars) = 1 in
  List.concat
    (List.map2
       (fun ((p, _), named) a ->
         match named_variable a with
         | Some y
           when named && (not (Id.Set.mem p assigned)) && (not (V.mem y free)) && (not (V.mem y declared))
                && once y ->
           [(p, y)]
         | _ -> [] )
       (List.combine params (List.map (fun (_, x) -> x <> None) l.params))
       args )

(* [l] applied to [args], opened up; [None] if its parameters are templated
   or do not match [args] in number.  With [alias], a parameter
   {!aliased_params} admits is renamed to the variable its argument names
   instead of being bound to it. *)
let expand ?(alias = false) fresh (l : lambda) args =
  match named_params l with
  | Some params when List.length params = List.length args ->
    incr fresh;
    let prefix = Printf.sprintf "_lc%d" !fresh in
    let aliased = if alias then aliased_params l params args else [] in
    let renamed =
      aliased
      @ List.map (fun x -> (x, Base.Generated_name.prefixed prefix x))
          (List.filter (fun x -> not (List.mem_assoc x aliased)) (List.map fst params) @ declared_here l.body)
    in
    let f x = match List.assoc_opt x renamed with Some y -> y | None -> x in
    (* An unnamed parameter's argument is evaluated for what it does, and a
       pure one does nothing; an aliased parameter is its argument. *)
    let unnamed = List.map (fun (_, x) -> x = None) l.params in
    let bindings =
      List.concat
        (List.map2
           (fun ((p, ty), unnamed) a : stmt list ->
             if (unnamed && V.pure a) || List.mem_assoc p aliased then []
             else [Cpp_ir.Typed.bind (f p) (ty) (a)] )
           (List.combine params unnamed) args )
    in
    Some {bindings; body = rename_ids f l.body}
  | _ -> None

(* An expansion read as straight-line code that ends by returning [e]: the
   code before, and [e]. *)
let straight_line ex =
  match List.rev ex.body with
  | (Return (Some e) : stmt) :: rev_stmts when not (has_return (List.rev rev_stmts)) ->
    Some (ex.bindings @ List.rev rev_stmts, e)
  | _ -> None

(* The number of statement and expression nodes, compared against
   {!budget}. *)
let size_stmts (l : stmt list) =
  let n = ref 0 in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> expr e); stmt = (fun s -> stmt s); type_ = ignore}
  and expr e =
    incr n;
    Cpp_ir.Children.expr v e
  and stmt s =
    incr n;
    Cpp_ir.Children.stmt v s
  in
  List.iter stmt l;
  !n

(* Whether [e] holds a lambda, other than in a statement. *)
let rec contains_lambda (e : expr) =
  match e with
  | Lambda _ -> true
  | _ ->
    let found = ref false in
    Cpp_ir.Children.expr (visit ~expr:(fun c -> found := !found || contains_lambda c) ~stmt:ignore) e;
    !found

(* How many times [e] reads the variable [x], other than in a statement. *)
let rec occurrences x (e : expr) =
  let n = ref (match e with Local y when Id.equal x y -> 1 | _ -> 0) in
  Cpp_ir.Children.expr (visit ~expr:(fun c -> n := !n + occurrences x c) ~stmt:ignore) e;
  !n

(* [e] with each variable [sub] names replaced by its expression. *)
let substitute sub e =
  let rec re (e : expr) : expr =
    match e with
    | Local x -> ( match List.assoc_opt x sub with Some a -> a | None -> e )
    | _ -> Cpp_ir.Map.expr (children ~expr:re ~stmt:rs) e
  and rs s = Cpp_ir.Map.stmt (children ~expr:re ~stmt:rs) s in
  re e

(** A lambda body larger than this is not duplicated at its calls. *)
let budget = 60

(** {1 Rules} *)

(* The name a type variable is written under. *)
let spelled : Cpp_ir.Type.Type_variable.t -> Id.t = function
  | Index (_, Some n) | Named n -> n
  | Index (i, None) -> Id.of_string ("T" ^ string_of_int i)

(* Two types that spell the same C++ type: a type variable is the name it
   prints as, however it is indexed; a global is itself under any of its
   kernel names; and the expressions an entity application carries are not
   printed. *)
let rec same_type (a : ty) (b : ty) =
  let all = List.equal same_type in
  match (a, b) with
  | Variable x, Variable y -> Id.equal (spelled x) (spelled y)
  | Entity_application (r, ts, _), Entity_application (r', ts', _) -> GlobRef.CanOrd.equal r r' && all ts ts'
  | In_namespace (r, t), In_namespace (r', t') -> GlobRef.CanOrd.equal r r' && same_type t t'
  | External (s, ts), External (s', ts') -> String.equal s s' && all ts ts'
  | Named (i, ts), Named (i', ts') -> Id.equal i i' && all ts ts'
  | Member (t, i), Member (t', i') -> same_type t t' && Id.equal i i'
  | (Const t, Const t') | (Shared_pointer t, Shared_pointer t') | (Pointer t, Pointer t') -> same_type t t'
  | Reference (k, t), Reference (k', t') -> k = k' && same_type t t'
  | Function (d, c), Function (d', c') -> all d d' && same_type c c'
  | Variant (k, ts), Variant (k', ts') -> k = k' && all ts ts'
  | _ -> a = b

(** R1.  A statement list ending [auto f = [..](params) { body }; return
    f(args);] -- the lambda bound once and called once, as what the
    enclosing function returns -- ends with [{ params = args; body }]
    instead.  A [return] in [body] returns from the function, which is what
    returning the call's result did; a local the lambda returned through a
    by-reference capture is now the function's own, and leaves by an
    implicit move rather than a copy.  The lambda must return what the
    function does, and call itself through nothing: a local fixpoint whose
    control was lowered to a loop qualifies.  A parameter whose argument is
    a variable stands for it ({!aliased_params}): nothing runs after the
    call, so the variable is read by the body alone, and a mapped identity
    passed so is used where it was created ({!Local_storage}). *)
let inline_tail_call fresh ret_ty (stmts : stmt list) =
  match List.rev stmts with
  | Return (Some (Call (_, Local f', args))) :: Bind_variable (f, Declare_deduced _, Lambda l) :: rev_before
    when Id.equal f f'
         && (match (l.return_type, ret_ty) with Some a, Some b -> same_type a b | None, _ -> true | _ -> false)
         && (not (mentions f l.body))
         (* Called once: not again inside its own arguments. *)
         && not (List.exists (fun a -> mentions f [Expression a]) args) -> (
    match expand ~alias:true fresh l args with
    | Some ex -> List.rev rev_before @ [Block (ex.bindings @ ex.body)]
    | None -> stmts )
  | _ -> stmts

(** [rule] applied to every statement list of [stmts] -- each branch,
    block and loop body, innermost first, then [stmts] itself -- but not to
    the body of a lambda, whose [return]s are its own. *)
let rec everywhere (rule : stmt list -> stmt list) (stmts : stmt list) : stmt list =
  let m = Cpp_ir.Map.make ~stmts:(everywhere rule) ~expr:Fun.id ~stmt:(nested rule) ~type_:Fun.id () in
  rule (List.map (Cpp_ir.Map.stmt m) stmts)

and nested rule (s : stmt) : stmt =
  Cpp_ir.Map.stmt (Cpp_ir.Map.make ~stmts:(everywhere rule) ~expr:Fun.id ~stmt:(nested rule) ~type_:Fun.id ()) s

(** R2.  [T x = [..]() { stmts; return e; }();] -- a lambda invoked where it
    is written, for its initialiser -- becomes [stmts; T x = e;] when
    [stmts] cannot leave early. *)
let inline_iife_initializers fresh stmts =
  let rec go : stmt list -> stmt list = function
    | [] -> []
    | (Bind_variable (x, ((Declare _ | Declare_deduced _) as tgt), Call (_, Lambda l, [])) as s) :: rest
      when (match tgt with Declare (t, _) -> t <> Auto | _ -> false) || l.return_type = None -> (
      match Option.bind (expand fresh l []) straight_line with
      | Some (body, e) -> go (body @ (Bind_variable (x, tgt, e) :: rest))
      | None -> s :: go rest )
    | s :: rest -> s :: go rest
  in
  go stmts

(** R3.  A local record built from lambdas -- [P p = P{[..](..) {..}, ...};]
    -- whose every later use is a call through one of its fields becomes
    those lambdas' bodies at the calls: each call binds the lambda's
    parameters to its arguments and runs its statements where it stood.  A
    by-copy capture reads the variable it copied, which is the same value
    provided nothing assigns the variable after the record is built; and
    once no call is left the record, a value of pure constructions, is
    dropped.  Only straight-line bodies, under {!budget}, expanded at every
    call or at none. *)
let specialize_local_records fresh stmts =
  let rec go : stmt list -> stmt list = function
    | [] -> []
    | (Bind_variable (p, (Declare _ | Declare_deduced _), Aggregate {struct_ = record; values = fields; _}) as decl) :: rest -> (
      let lambdas = List.map (function (Lambda l : expr) -> Some l | _ -> None) fields in
      (* An aggregate holds the record's non-erased fields, in declaration
         order, so a projection reaches the one at its position among
         those. *)
      let live_fields =
        List.filter_map
          (fun {Core.Record.Field.projection = fr; type_ = ty} -> if Base.Core_util.is_erased_type ty then None else Some fr)
          (Base.Table.get_record_field_bindings record)
      in
      let field_lambda r =
        if List.length live_fields <> List.length fields then None
        else
          let rec find = function
            | Some fr :: _, l :: _ when Base.Common.globref_equal fr r -> l
            | _ :: frs, _ :: ls -> find (frs, ls)
            | _ -> None
          in
          find (live_fields, lambdas)
      in
      let call_target (e : expr) =
        match e with
        | Call (_, Project ((Local p' | Move (Local p')), fld, _), args) when Id.equal p p' ->
          Option.map (fun l -> (l, args)) (field_lambda fld)
        | _ -> None
      in
      (* Every use of [p] in [rest] is the receiver of such a call. *)
      let only_calls =
        let ok = ref true in
        let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
          {expr = (fun e -> fe e); stmt = (fun s -> fs s); type_ = ignore}
        and fe (e : expr) =
          match call_target e with
          | Some (_, args) -> List.iter fe args
          | None ->
            (match e with Local x when Id.equal x p -> ok := false | _ -> ());
            Cpp_ir.Children.expr v e
        and fs s = Cpp_ir.Children.stmt v s in
        List.iter fs rest;
        !ok
      in
      let lambdas_ok =
        List.for_all
          (function Some (l : lambda) -> size_stmts l.body <= budget && named_params l <> None | None -> false)
          lambdas
      in
      let captured =
        List.fold_left
          (fun acc -> function
            | Some (l : lambda) -> IdSet.union acc (IdSet.of_list (V.free_in_body l.body))
            | None -> acc)
          IdSet.empty lambdas
      in
      if only_calls && lambdas_ok && IdSet.is_empty (IdSet.inter captured (V.assigned rest)) then
        (* A call as an expression, where the lambda is one [return e] and
           every argument may stand in for its parameter: a pure one may be
           duplicated or dropped, any other must replace a parameter read
           exactly once.  A lambda inside [e] could capture what an argument
           names, so it declines. *)
        let as_expr (l : lambda) args =
          match (named_params l, l.body) with
          | Some params, [Return (Some e)] when List.length params = List.length args && not (contains_lambda e) ->
            let reads x = occurrences x e in
            if List.for_all2 (fun (x, _) a -> V.pure a || reads x = 1) params args then
              Some (substitute (List.combine (List.map fst params) args) e)
            else None
          | _ -> None
        in
        (* The whole statement a call is, expanded into the lambda's
           statements: the shape that cannot be an expression. *)
        let as_stmts e finish =
          match call_target e with
          | Some (l, args) -> (
            match Option.bind (expand fresh l args) straight_line with
            | Some (body, r) -> Some (body @ finish r)
            | None -> None )
          | None -> None
        in
        let exception Decline in
        let rec in_expr e =
          match call_target e with
          | Some (l, args) -> (
            match as_expr l (List.map in_expr args) with Some e' -> e' | None -> raise_notrace Decline )
          | None -> Cpp_ir.Map.expr (children ~expr:in_expr ~stmt:in_stmt) e
        and in_stmt s = Cpp_ir.Map.stmt (children ~expr:in_expr ~stmt:in_stmt) s in
        let statement (s : stmt) =
          let whole e finish =
            match call_target e with
            | Some (l, args) when as_expr l args = None -> (
              match as_stmts e finish with Some b -> b | None -> raise_notrace Decline )
            | _ -> [in_stmt s]
          in
          match s with
          | Expression e -> whole e (fun r -> if V.pure r then [] else [Expression r])
          | Bind_variable (v, tgt, e) -> whole e (fun r -> [Bind_variable (v, tgt, r)])
          | _ -> [in_stmt s]
        in
        let rw stmts =
          match List.concat_map statement stmts with
          | stmts' when not (mentions p stmts') -> Some stmts'
          | _ | (exception Decline) -> None
        in
        match rw rest with Some rest' -> go rest' | None -> decl :: go rest
      else decl :: go rest )
    | s :: rest -> s :: go rest
  in
  go stmts

(** R4.  [auto f = [..](params) { body };] -- a lambda every later use of
    which is a direct call of it, outside every lambda -- runs only at its
    calls, inside the scope that made it.  A parameter of a mapped type
    that every call passes the same variable [y], declared before the
    lambda and never assigned after it, and that [body] only reads, becomes
    [y] itself: the lambda drops it, its calls drop the argument, and it
    borrows its scope ([Runs_in_place], a by-reference capture).  Such a
    parameter is the reference or array a loop helper threads through its
    recursion unchanged; captured, it is used where it was created, so
    {!Local_storage} may keep it in a local.

    A by-reference capture reads what the variable holds at the call, not
    when the lambda was made: it declines when [body] would capture a
    variable the statements after it assign or move from.  The lambda never
    outlives its scope, since nothing but a direct call names it. *)

(* The mapped head a declared type names, under [const] and references. *)
let rec mapped_head (t : ty) =
  match t with
  | Reference (_, t) | Const t | In_namespace (_, t) -> mapped_head t
  | Entity_application (r, _, _) when Base.Mapping_plan.is_type_head r -> Some r
  | _ -> None

(* The argument lists of the calls [stmts] make of [f], when every
   occurrence of [f] in them is the callee of a call, outside every lambda,
   whose arguments do not name [f]; [None] otherwise. *)
let direct_calls f (stmts : stmt list) =
  let calls = ref [] and ok = ref true in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> fe e); stmt = (fun s -> fs s); type_ = ignore}
  and fe (e : expr) =
    match e with
    | Call (_, Local f', args) when Id.equal f f' ->
      if List.exists (fun a -> mentions f [Expression a]) args then ok := false;
      calls := args :: !calls
    | Local f' when Id.equal f f' -> ok := false
    | Lambda _ -> if mentions f [Expression e] then ok := false
    | _ -> Cpp_ir.Children.expr v e
  and fs s = Cpp_ir.Children.stmt v s in
  List.iter fs stmts;
  if !ok then Some (List.rev !calls) else None

(* The variables [stmts] move from, anywhere. *)
let moved_from (stmts : stmt list) =
  let acc = ref IdSet.empty in
  let rec v : Cpp_ir.Lowered.phase Cpp_ir.Children.visitor =
    {expr = (fun e -> fe e); stmt = (fun s -> Cpp_ir.Children.stmt v s); type_ = ignore}
  and fe (e : expr) =
    (match e with Move (Local x) -> acc := IdSet.add x !acc | _ -> ());
    Cpp_ir.Children.expr v e
  in
  List.iter (Cpp_ir.Children.stmt v) stmts;
  !acc

(* [rest] with each direct call of [f] keeping the arguments [keep] says. *)
let drop_arguments f keep (rest : stmt list) =
  let filter xs = List.filteri (fun i _ -> List.nth keep i) xs in
  let rec fe (e : expr) : expr =
    match e with
    | Call (sg, (Local f' as callee), args) when Id.equal f f' ->
      let params : _ Cpp_ir.Expr.Call.params =
        match sg.params with Types ts when List.length ts = List.length keep -> Types (filter ts) | p -> p
      in
      Call ({sg with params}, callee, filter args)
    | _ -> Cpp_ir.Map.expr (children ~expr:fe ~stmt:fs) e
  and fs s = Cpp_ir.Map.stmt (children ~expr:fe ~stmt:fs) s in
  List.map fs rest

let in_place_lambdas (stmts : stmt list) =
  let rec go : stmt list -> stmt list = function
    | [] -> []
    | (Bind_variable (f, tgt, Lambda l) as s) :: rest when l.type_params = [] && not (mentions f l.body) -> (
      let rest = go rest in
      match (direct_calls f rest, named_params l) with
      | Some (_ :: _ as calls), Some params
        when List.for_all (fun args -> List.length args = List.length params) calls -> (
        let outer = V.free_in_body (s :: rest) in
        let assigned_rest = V.assigned rest in
        let assigned_body = V.assigned l.body and declared_body = V.declared l.body in
        let invariant i (p, ty) =
          match (mapped_head ty, List.map (fun args -> named_variable (List.nth args i)) calls) with
          | Some _, Some y :: ys
            when List.for_all (function Some y' -> Id.equal y y' | None -> false) ys
                 && V.mem y outer
                 && (not (IdSet.mem y assigned_rest))
                 && (not (IdSet.mem p assigned_body))
                 && not (V.mem y declared_body) ->
            Some y
          | _ -> None
        in
        let dropped = List.mapi invariant params in
        let sub =
          List.concat (List.map2 (fun (p, _) d -> match d with Some y -> [(p, y)] | None -> []) params dropped)
        in
        let keep = List.map (fun d -> d = None) dropped in
        let body = rename_ids (fun x -> match List.assoc_opt x sub with Some y -> y | None -> x) l.body in
        let remaining = List.filteri (fun i _ -> List.nth keep i) params in
        let captured = V.without (List.map fst remaining) (V.free_in_body body) in
        let invalidated = IdSet.union assigned_rest (moved_from rest) in
        match sub with
        | [] -> s :: rest
        | _ when List.exists (fun x -> IdSet.mem x invalidated) captured -> s :: rest
        | _ ->
          let named xs = List.filter (fun (x, _) -> not (List.mem_assoc x sub)) xs in
          let l' =
            { l with
              params = List.filteri (fun i _ -> List.nth keep i) l.params;
              body;
              binders = named l.binders;
              modes = named l.modes;
              capture = Runs_in_place }
          in
          Bind_variable (f, tgt, Lambda l') :: drop_arguments f keep rest )
      | _ -> s :: rest )
    | s :: rest -> s :: go rest
  in
  go stmts

(** {1 Entry point} *)

(* One function body, returning [ret_ty], through R2, R3, R1 then R4; one
   counter numbers every expansion in it.  R1 and R4 apply in every
   statement list of the body ({!everywhere}): a lambda bound in a branch
   is as local as one bound at the top. *)
let body ret_ty stmts =
  let fresh = ref 0 in
  stmts
  |> inline_iife_initializers fresh
  |> specialize_local_records fresh
  |> everywhere (inline_tail_call fresh ret_ty)
  |> everywhere in_place_lambdas

let rec field ((f, vis, tag) : Cpp_ir.Lowered.phase Cpp_ir.Field.member) : _ Cpp_ir.Field.member =
  let f : _ Cpp_ir.Field.t =
    match f with
    | Method m -> Method {m with body = body (Some m.return_type) m.body}
    | Nested_struct (id, fs) -> Nested_struct (id, List.map field fs)
    | f -> f
  in
  (f, vis, tag)

let rec transform_decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  match d with
  | Function ({shape = Definition (ps, stmts); _} as f) ->
    Function {f with shape = Definition (ps, body (Some f.return_type) stmts)}
  | Template (tps, c, inner) -> Template (tps, c, transform_decl inner)
  | Namespace (r, ds) -> Namespace (r, List.map transform_decl ds)
  | Struct s -> Struct {s with fields = List.map field s.fields}
  | Merged_struct_members s -> Merged_struct_members {s with fields = List.map field s.fields}
  | d -> d
