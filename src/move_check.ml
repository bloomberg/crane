(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** No local is read after it is moved.  See [move_check.mli]. *)

open Names
open Cpp_ir.Grammar

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t
type phase = Cpp_ir.Lowered.phase

(* What a read or a move reaches: a whole local, or one member of it; or the
   storage of a local, which a reuse arm hands its constructor as the token,
   to be rebuilt in place; or, through a reference bound into a local, the
   part of it the reference names, which is not known to be any one member,
   or a member of that part. *)
type place =
  | Whole of Id.t
  | Member of Id.t * string
  | Storage of Id.t
  | Through of {alias : Id.t; base : Id.t; member : string option}

let var = function Whole x | Member (x, _) | Storage x | Through {base = x; _} -> x

(* A move of one place takes what a read of the other needs: the same local,
   unless they are two different members of it, or two different parts
   references name, or a value taken out of a local before its storage is
   rebuilt.  A part a reference names may be any member, so a member and
   such a part are not known to meet: the whole is what both are read of. *)
let conflict p q =
  Id.equal (var p) (var q)
  &&
  match (p, q) with
  | Member (_, f), Member (_, g) -> String.equal f g
  | Through {alias = a; member = f; _}, Through {alias = b; member = g; _} ->
    Id.equal a b && (f = None || g = None || f = g)
  | (Whole _ | Member _ | Through _), Storage _ | Member _, Through _ | Through _, Member _ -> false
  | _ -> true

(* The references in scope, each to the local it was bound into. *)
type aliases = Id.t Id.Map.t

(* What a read of the local [x] reaches. *)
let local (aliases : aliases) x =
  match Id.Map.find_opt x aliases with Some base -> Through {alias = x; base; member = None} | None -> Whole x

(* What evaluating an expression reads and moves, as a later or a concurrent
   evaluation sees it. *)
type effect_ = {reads : place list; moves : place list}

let none = {reads = []; moves = []}
let union a b = {reads = a.reads @ b.reads; moves = a.moves @ b.moves}

(* Raw C++ in a body: a read may hide in a string. *)
exception Opaque

(* What is read after a [continue], and after a [break]. *)
type jumps = {continue_ : place list; break_ : place list}

(* The variables found read after a move, in the body being checked; the
   references, each with the local it was bound into, found read after that
   local is given a new value; the locals the body declares as pointers. *)
type report = {mutable found : Id.t list; mutable stale : (Id.t * Id.t) list; pointers : Id.t list}

(* A move in [a] read by [b], [b] running after [a] or beside it. *)
let check_after report a b =
  List.iter
    (fun m -> if List.exists (conflict m) (b.reads @ b.moves) then report.found <- var m :: report.found)
    a.moves

(* The local whose variant [e] reaches into: [x.v_mut()], [x->v()]. *)
let variant_of : expr -> expr option = function
  | Call (_, Access (Dot, (Local _ as x), _), []) | Access_call (_, (Local _ as x), _, []) -> Some x
  | _ -> None

(* The local [e] names storage inside of, as a reference bound to [e] does:
   the local itself, a field of it, the alternative its variant holds, a
   field of that.  Through a pointer, what is named is not the local's. *)
let rec reaches aliases (e : expr) =
  match e with
  | Local x -> Some (match Id.Map.find_opt x aliases with Some base -> base | None -> x)
  | Access (Dot, e, _) | Member (e, _) | Variant_get (_, Some e) -> reaches aliases e
  | Call (_, Access (Dot, e, _), []) | Access_call (Dot, e, _, []) -> reaches aliases e
  | _ -> None

(* [aliases] with each of [xs] a local of its own. *)
let own (aliases : aliases) xs = List.fold_left (fun m x -> Id.Map.remove x m) aliases xs

(* [aliases] with each of [xs] a reference into what [e] reaches, if it
   reaches a local, or else a local of its own. *)
let bind_into aliases xs e =
  match reaches aliases e with
  | Some base -> List.fold_left (fun m x -> Id.Map.add x base m) aliases xs
  | None -> own aliases xs

let rec is_reference : ty -> bool = function Reference _ -> true | In_namespace (_, t) -> is_reference t | _ -> false

(* [aliases] once [s] has run: a structured binding, or a declaration of a
   reference, binds its names into what it names; any other declaration
   binds a local of its own. *)
let aliases_after aliases : stmt -> aliases = function
  | Structured_binding (xs, e) -> bind_into aliases xs e
  | Bind_variable (x, Declare (ty, _), e) when is_reference ty -> bind_into aliases [x] e
  | Bind_variable (x, (Declare _ | Declare_static _), _) | Declare (x, _, _) | Declare_value_initialized (x, _)
  | Foreign_block {result = x; _} ->
    own aliases [x]
  | _ -> aliases

(* The member a read reaches when it reads one: a field, a field of the
   alternative a variant holds -- the cell a reuse arm hands its constructor
   as the token -- or a pair component through the projection mapping. *)
let member (e : expr) : (expr * string) option =
  match e with
  | Access (Dot, Variant_get (_, Some holder), f) when variant_of holder <> None ->
    Some (Option.get (variant_of holder), Id.to_string f)
  | Access (Dot, x, f) | Member (x, f) -> Some (x, Id.to_string f)
  | Call (_, Entity (_, _, Some {inline = Some {shape = Pair_projection f; _}; _}), [x]) -> Some (x, f)
  (* A pair projection's mapping instantiated ([%a0.first]). *)
  | Foreign
      ( Call,
        {values = [pair]; pieces = [Text ""; Value 0; Text f] | [Value 0; Text f]; _} )
    when f = ".first" || f = ".second" ->
    Some (pair, String.sub f 1 (String.length f - 1))
  | _ -> None

(* A member of the local [x]; of a reference, the part it names. *)
let member_of aliases x f =
  match local aliases x with Through t -> Through {t with member = Some f} | _ -> Member (x, f)

let rec expr report aliases (e : expr) : effect_ =
  let expr = expr report aliases in
  match (member e, e) with
  | Some (Local x, f), _ -> {none with reads = [member_of aliases x f]}
  | Some (Move (Local x), f), _ -> {none with moves = [member_of aliases x f]}
  | _, Move m when (match member m with Some (Local _, _) -> true | _ -> false) -> (
    match member m with Some (Local x, f) -> {none with moves = [member_of aliases x f]} | _ -> none )
  | _, Foreign_text _ -> raise Opaque
  | _, Local x -> {none with reads = [local aliases x]}
  | _, Move (Local x) -> {none with moves = [local aliases x]}
  (* A reuse factory takes the storage of the local it is handed as its
     token, first, to rebuild it in place. *)
  | _, Call (_, (Type_member (_, f) | Scope (_, f, [])), args) when Generated_name.is_companion "reuse" f -> (
    match args with
    | Move (Local x) :: rest -> unsequenced report ({none with moves = [Storage x]} :: List.map expr rest)
    | args -> unsequenced report (List.map expr args) )
  (* A method is called on the whole object, a variant's accessor included. *)
  | _, Call (_, Access (Dot, Local x, _), args) ->
    let args = List.map expr args in
    unsequenced report ({none with reads = [local aliases x]} :: args)
  (* A condition runs first, and one arm after it. *)
  | _, Conditional (c, a, b) ->
    let c = expr c and arms = union (expr a) (expr b) in
    check_after report c arms;
    union c arms
  | _, Binary ((And | Or), l, r) ->
    let l = expr l and r = expr r in
    check_after report l r;
    union l r
  (* The value assigned is computed before the place it goes to. *)
  | _, Binary (Assign, l, r) ->
    let l = expr l and r = expr r in
    check_after report r l;
    union l r
  (* A braced initialiser evaluates its elements in order. *)
  | _, (Aggregate {values = es; _} | Local_aggregate {values = es; _} | Braced es) ->
    List.fold_left
      (fun before e ->
        let e = expr e in
        check_after report before e;
        union before e )
      none es
  (* A closure reads what it closes over where it is made, and takes there
     what it moves; its body is a body of its own.  What it closes over is
     what is free in it, scope by scope: a parameter of a lambda inside it
     is that lambda's, not a local of the scope the closure is made in. *)
  | _, Lambda l ->
    body report aliases l.body;
    {reads = List.map (local aliases) (Cpp_ir.Variables.free_in_expr e); moves = List.map (local aliases) l.moved}
  | _ ->
    (* Everything else evaluates its parts in an order C++ does not fix. *)
    let parts = ref [] in
    Cpp_ir.Subterms.expr ~expr:(fun e -> parts := expr e :: !parts) ~stmts:(body report aliases) e;
    unsequenced report !parts

and unsequenced report parts =
  List.iteri (fun i p -> List.iteri (fun j q -> if i <> j then check_after report p q) parts) parts;
  List.fold_left union none parts

and body report aliases ss = try ignore (walk report {continue_ = []; break_ = []} aliases [] ss) with Opaque -> ()

(* [walk report jumps aliases live ss] checks [ss], run with the references
   [aliases] in scope, and is what is read from its start, [live] being read
   after it; [jumps] is what is read after a [continue] and after a
   [break]. *)
and walk report jumps aliases live = function
  | [] -> live
  | s :: ss -> stmt report jumps aliases (walk report jumps (aliases_after aliases s) live ss) s

and at report aliases live e =
  let eff = expr report aliases e in
  check_after report eff {none with reads = live};
  eff.reads @ eff.moves @ live

(* Before [p] is assigned, nothing read after reads what it holds: a whole
   local's members and the parts references name among them; a reference
   once it names something else. *)
and kill p live =
  List.filter
    (fun q ->
      not
        ( match (p, q) with
        | Whole x, Through {alias; _} -> Id.equal x alias || Id.equal x (var q)
        | Whole x, _ -> Id.equal x (var q)
        | _ -> q = p ) )
    live

and kill_all xs live = List.fold_left (fun l x -> kill (Whole x) l) live xs

and stmt report jumps aliases live (s : stmt) =
  let at' = at report aliases and walk' = walk report jumps aliases in
  match s with
  | Foreign_text _ -> raise Opaque
  | Return None | Throw _ -> []
  | Return (Some e) -> at' [] e
  | Continue -> jumps.continue_
  | Break -> jumps.break_
  | Bind_variable (x, Existing, e) ->
    reassigned report aliases x live;
    at' (kill (Whole x) live) e
  | Bind_variable (x, _, e) -> at' (kill (Whole x) live) e
  | Assign (lhs, e) | Expression (Binary (Assign, lhs, e)) -> (
    match (member lhs, lhs) with
    | Some (Local x, f), _ -> at' (kill (member_of aliases x f) live) e
    | _, Local x ->
      reassigned report aliases x live;
      at' (kill (local aliases x) live) e
    | _ -> at' (at' live lhs) e )
  | Declare (x, _, _) | Declare_value_initialized (x, _) -> kill (Whole x) live
  | If {condition = c; then_ = t; else_ = e} -> at' (walk' live t @ walk' live e) c
  | If_constexpr {then_ = t; else_ = e; _} -> walk' live t @ walk' live e
  | If_declaration {name = x; init = c; then_ = t; else_ = e; _} ->
    let walk = walk report jumps (own aliases [x]) in
    at' (kill (Whole x) (walk live t @ walk live e)) c
  | Block ss -> walk' live ss
  | While (c, ss) -> loop report aliases live (fun report l -> at report aliases l c) ss
  | For_range (x, e, ss) -> at' (loop report (own aliases [x]) live (fun _ l -> kill (Whole x) l) ss) e
  | Switch {scrutinee = e; branches; default = dflt; _} ->
    let alts = List.map (fun (_, ss) -> walk' live ss) branches in
    let other = match dflt with Some ss -> walk' live ss | None -> live in
    at' (List.concat (other :: alts)) e
  (* A branch binds its fields by reference into the scrutinee; with no
     fields, it binds the alternative, by reference unless it owns the
     scrutinee, and then it moves the alternative out into a local of its
     own. *)
  | Match (scrut, branches, els) ->
    let branch (b : phase Match.branch) =
      let fields = List.map (fun (fb : phase Match.field_binding) -> fb.name) b.field_bindings in
      let aliases, bound =
        match (fields, b.var) with
        | [], Some x when scrut.owned -> (own aliases [x], [x])
        | [], Some x -> (bind_into aliases [x] scrut.expr, [x])
        | _, _ -> (bind_into aliases fields scrut.expr, fields)
      in
      let l = kill_all bound (walk report jumps aliases live b.body) in
      List.fold_right (fun c l -> at report aliases l c) b.extra_conditions l
    in
    let other = match els with Some ss -> walk' live ss | None -> live in
    at' (List.concat (other :: List.map branch branches)) scrut.expr
  | Custom_match m ->
    let branch (b : phase Custom_match.branch) =
      let xs = List.map (fun (p : phase Custom_match.param) -> p.name) b.params in
      kill_all xs (walk report jumps (own aliases xs) live b.body)
    in
    at' (List.concat_map branch m.branches) m.scrutinee
  | Structured_binding (xs, e) -> at' (kill_all xs live) e
  (* A block template declares the variable it binds. *)
  | Foreign_block {result = x; values = args; _} ->
    let eff = List.fold_left (fun acc a -> union acc (expr report aliases a)) none args in
    let live = kill (Whole x) live in
    check_after report eff {none with reads = live};
    eff.reads @ eff.moves @ live
  | _ ->
    let live = ref live in
    Cpp_ir.Subterms.stmt ~expr:(fun e -> live := at' !live e) ~stmts:(fun _ -> ()) s;
    !live

(* The local [x] is given a new value, [live] being read after: a
   reference bound into what it held before, read after, names storage the
   assignment destroyed or replaced.  A pointer given a new value leaves
   what it pointed at as it was. *)
and reassigned report aliases x live =
  let base = match Id.Map.find_opt x aliases with Some b -> b | None -> x in
  if not (List.exists (Id.equal base) report.pointers) then
    List.iter
      (function
        | Through {alias; base = b; _} when Id.equal b base && not (Id.equal alias x) ->
          report.stale <- (alias, base) :: report.stale
        | _ -> () )
      live

(* A loop body runs again: its end is followed by the loop's head, which is
   followed by the body's start and by what comes after the loop.  The head is
   found quietly, until nothing new reaches it; then the body is checked once
   against it. *)
and loop report aliases after head_of ss =
  let pass report head =
    head_of report (walk report {continue_ = head; break_ = after} aliases head ss @ after)
  in
  let quiet = {report with found = []; stale = []} in
  let rec fix head n =
    let head' = List.sort_uniq compare (pass quiet head @ head) in
    if n = 0 || List.length head' = List.length head then head' else fix head' (n - 1)
  in
  let head = fix (List.sort_uniq compare after) 16 in
  pass report head

(* The backend's own storage -- a loop's accumulator, a frame, a temporary
   -- is named with a leading underscore and handed over by protocols this
   walk cannot see: a frame pushed after a move of [_result] is resumed only
   once a base case has assigned it again.  Loopify checks the loops it
   builds against their ControlIR; this checks the program's locals. *)
let backend x = String.length (Id.to_string x) > 0 && (Id.to_string x).[0] = '_'

(* The locals [ss] declares as pointers, in any scope. *)
let pointers ss =
  let rec is_pointer : ty -> bool = function Pointer _ -> true | Const t | In_namespace (_, t) -> is_pointer t | _ -> false in
  let found = ref [] in
  let rec fe e = Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) =
    ( match s with
    | Bind_variable (x, Declare (ty, _), _) | Declare (x, ty, _) when is_pointer ty -> found := x :: !found
    | _ -> () );
    Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.iter (fun s -> ignore (fs s)) ss;
  !found

(* Walk the body [ss] from an empty set of references, collecting what it
   reads after a move and the references it reads stale. *)
let walk_body ss =
  let report = {found = []; stale = []; pointers = pointers ss} in
  body report Id.Map.empty ss;
  report

let moved_reads ss = List.sort_uniq Id.compare (List.filter (fun x -> not (backend x)) (walk_body ss).found)

let stale_references ss = List.sort_uniq compare (walk_body ss).stale

(* Report, as [owner]'s, every moved read and stale reference of [ss],
   the backend's own storage aside. *)
let check_body owner ss =
  let report = walk_body ss in
  List.iter
    (fun x ->
      Probe.violation "moved value read"
        Pp.(str "in " ++ owner ++ str ", " ++ Id.print x ++ str " is read after it is moved") )
    (List.sort_uniq Id.compare (List.filter (fun x -> not (backend x)) report.found));
  List.iter
    (fun (alias, base) ->
      Probe.violation "borrow outlives its base"
        Pp.(
          str "in " ++ owner ++ str ", the reference " ++ Id.print alias ++ str " into " ++ Id.print base
          ++ str " is read after " ++ Id.print base ++ str " is given a new value" ) )
    (List.sort_uniq compare report.stale)

(* Whether a parameter of type [t] is declared by reference: a [const]
   type is one, as the declaration writes it. *)
let rec declared_by_reference : ty -> bool = function
  | Reference _ | Const _ -> true
  | In_namespace (_, t) -> declared_by_reference t
  | _ -> false

(* What the parameters [params] of a callable whose plan passes them as
   [passing] says, and whose body is [body], break of it. *)
let passing_violations (passing : Callable_abi.passing list) params body =
  if List.compare_lengths passing params <> 0 then
    [ Printf.sprintf "the plan passes %d parameters, the declaration takes %d" (List.length passing)
        (List.length params) ]
  else
    (* What the body moves by name, and the names it declares again: a
       frame handler binds a parameter's name to the frame's field. *)
    let moved = ref [] and declared = ref [] in
    let rec fe (e : expr) =
      (match e with Move (Local x) -> moved := x :: !moved | _ -> ());
      Cpp_ir.Map.expr (rw ()) e
    and fs (s : stmt) =
      (match s with Bind_variable (x, Declare _, _) -> declared := x :: !declared | _ -> ());
      Cpp_ir.Map.stmt (rw ()) s
    and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
    List.iter (fun s -> ignore (fs s)) body;
    List.concat
      (List.map2
         (fun (p : Callable_abi.passing) (x, (ty : ty)) ->
           let name = Id.to_string x in
           match (p, ty) with
           | Forwarded, Reference (Forwarding, _) -> []
           | Forwarded, _ -> ["the plan forwards " ^ name ^ ", declared otherwise"]
           | (Owned | Borrowed), Reference (Forwarding, _) -> ["the declaration forwards " ^ name ^ ", the plan does not"]
           | Owned, _ when declared_by_reference ty -> ["the plan owns " ^ name ^ ", declared by reference"]
           | Borrowed, _
             when declared_by_reference ty && List.exists (Id.equal x) !moved
                  && not (List.exists (Id.equal x) !declared) ->
             ["the body moves out of " ^ name ^ ", which the plan lends it"]
           | (Owned | Borrowed), _ -> [] )
         passing params )

let convention_violations r params body =
  Option.map
    (fun passing -> passing_violations passing params body)
    (Option.bind (Callable_abi.lookup r) Callable_abi.passing)

let report_conventions owner =
  List.iter (fun what -> Probe.violation "callable convention" Pp.(str "in " ++ owner ++ str ", " ++ str what))

let check_convention owner r params body =
  report_conventions owner (Option.default [] (convention_violations r params body))

(* The lambda of each local fixpoint in [ss] against the plan of the
   function it is generated for ({!Ownership_ir.Local_passing}): the
   parameters it takes other than the members it calls through. *)
let check_local_conventions owner ss =
  let rec fe (e : expr) =
    ( match e with
    | Lambda {fixpoint = Some lf; params; body; _} -> (
      match Ownership_ir.Local_passing.lookup lf.member with
      | Some passing ->
        let selves = match lf.encoding with Self_passing ids -> ids | Knot | Lowered -> [] in
        let params =
          List.filter_map
            (fun (ty, x) ->
              match x with
              | Some x when List.exists (Id.equal x) selves -> None
              | Some x -> Some (x, ty)
              | None -> Some (Id.of_string "_", ty) )
            params
        in
        report_conventions
          Pp.(owner ++ str ", the local fixpoint " ++ Id.print lf.name)
          (passing_violations (List.filter_map Fun.id passing) params body)
      | None -> () )
    | _ -> () );
    Cpp_ir.Map.expr (rw ()) e
  and fs s = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.iter (fun s -> ignore (fs s)) ss

(* Whether [l] reads the scope it is made in by reference. *)
let by_reference (l : phase Lambda.t) =
  match l.capture with Runs_in_place | Written By_reference -> true | Stored | Written _ -> false

(* The names the statements [ss] let escape among [xs], locals bound to
   lambdas reading their scope by reference, [group] being all such in the
   block: named other than as the function a call applies -- or as an
   argument of a call applying one of [callees], the members of a group
   handing themselves on -- or named at all inside a lambda that copies
   what it captures.  [callees] holds [group], and the members of its
   knots taking the knot's members as parameters ([Self_passing]):
   whether or not such a member reads its own scope, it takes its partners
   by reference, for the call, and lets them escape no further
   ({!check_by_reference_closures} checks it does not). *)
let escaping ~group ~callees xs ss =
  let found = ref [] in
  let mem x = List.exists (Id.equal x) xs in
  let rec expr (e : expr) =
    match e with
    | Call (_, Local f, args) when List.exists (Id.equal f) callees ->
      List.iter (fun (a : expr) -> match a with Local x when List.exists (Id.equal x) group -> () | a -> expr a) args
    | Local x when mem x -> found := x :: !found
    | Lambda l when not (by_reference l) ->
      List.iter (fun x -> if mem x then found := x :: !found) (Cpp_ir.Variables.free_in_expr e)
    | _ -> Cpp_ir.Subterms.expr ~expr ~stmts:(List.iter stmt) e
  and stmt s = Cpp_ir.Subterms.stmt ~expr ~stmts:(List.iter stmt) s in
  List.iter stmt ss;
  List.sort_uniq Id.compare !found

(* Each lambda of a local fixpoint function whose plan holds a capture
   [By_reference] ({!Ownership_ir.Local_captures}) in [ss]: written
   capturing by reference, and not let escape by the statements after the
   one binding it, in the block binding it -- the scope it reads; nor any
   lambda capturing one by reference; nor its partners by the members of
   its knot they are lent to. *)
let check_by_reference_closures owner ss =
  let report what = Probe.violation "closure captures" Pp.(str "in " ++ owner ++ str ", " ++ what) in
  let rec block ss =
    let planned =
      List.filter_map
        (fun (s : stmt) ->
          match s with
          | Bind_variable (x, Declare _, Lambda {fixpoint = Some lf; _})
            when Ownership_ir.Local_captures.by_reference lf.member ->
            Some (x, fst lf.member)
          | _ -> None )
        ss
    in
    let group = List.map fst planned in
    (* The members of those knots that take the knot's members as
       parameters, each with those parameters and its body. *)
    let impls =
      List.filter_map
        (fun (s : stmt) ->
          match s with
          | Bind_variable (y, Declare _, Lambda {fixpoint = Some {member; encoding = Self_passing selves; _}; body; _})
            when List.exists (fun (_, o) -> Miniml.Occurrence.equal o (fst member)) planned ->
            Some (y, selves, body)
          | _ -> None )
        ss
    in
    let callees = group @ List.map (fun (y, _, _) -> y) impls in
    (* What a call applying one of [impls] is lent, it calls, or lends a
       call applying one of them, and lets go of nothing else. *)
    List.iter
      (fun (y, selves, body) ->
        List.iter
          (fun self ->
            report
              Pp.(
                str "the local fixpoint lambda " ++ Id.print y ++ str " lets its partner " ++ Id.print self
                ++ str ", which may read its scope by reference, escape" ) )
          (escaping ~group:selves ~callees:selves selves body) )
      impls;
    (* [reading]: the locals bound so far in the block that read its scope
       by reference -- the members planned so, and the lambdas capturing
       one of [reading] by reference, as a group's wrappers do the impls,
       which may outlive the scope no more than what they read. *)
    let rec go reading : stmt list -> unit = function
      | [] -> ()
      | (Bind_variable (x, Declare _, Lambda ({fixpoint = Some lf; _} as l)) as s) :: rest
        when Ownership_ir.Local_captures.by_reference lf.member && l.capture <> Written Nothing ->
        (* One the C++ has capture nothing -- what the plan reads is a
           dictionary, a template parameter -- refers into no scope. *)
        if not (by_reference l) then
          report Pp.(str "the local fixpoint " ++ Id.print lf.name ++ str " copies what its plan reads by reference");
        List.iter
          (fun x -> report Pp.(str "the local fixpoint lambda " ++ Id.print x ++ str " reads its scope by reference and escapes it"))
          (escaping ~group ~callees [x] rest);
        stmt s;
        go (x :: reading) rest
      | (Bind_variable (x, Declare _, (Lambda l as e)) as s) :: rest
        when by_reference l && List.exists (fun y -> List.exists (Id.equal y) reading) (Cpp_ir.Variables.free_in_expr e) ->
        List.iter
          (fun x ->
            report
              Pp.(str "the lambda " ++ Id.print x ++ str " reads a local fixpoint by reference and escapes it") )
          (escaping ~group ~callees [x] rest);
        stmt s;
        go (x :: reading) rest
      | s :: rest ->
        stmt s;
        go reading rest
    in
    go [] ss
  and expr e = Cpp_ir.Subterms.expr ~expr ~stmts:block e
  and stmt s = Cpp_ir.Subterms.stmt ~expr ~stmts:block s in
  block ss

(* Every body of [d] through all four checks: moved reads, local fixpoint
   conventions, by-reference closures, and, for a top-level function or a
   method with a globref, its own callable convention. *)
let rec check_decl (d : Cpp_ir.Lowered.Decl.t) =
  let rec field ((f, _, _) : phase Field.member) =
    match f with
    | Method m ->
      check_body (Id.print m.name) m.body;
      check_local_conventions (Id.print m.name) m.body;
      check_by_reference_closures (Id.print m.name) m.body;
      Option.iter (fun r -> check_convention (Id.print m.name) r m.params m.body) m.globref
    | Nested_struct (_, fs) -> List.iter field fs
    | _ -> ()
  in
  match d with
  | Function {shape = Definition (params, ss); path; _} ->
    let r, _ = match List.rev path.inner with inner :: _ -> inner | [] -> path.outer in
    check_body (GlobRef.print r) ss;
    check_local_conventions (GlobRef.print r) ss;
    check_by_reference_closures (GlobRef.print r) ss;
    if path.inner = [] then check_convention (GlobRef.print r) r params ss
  | Template (_, _, inner) -> check_decl inner
  | Namespace (_, ds) -> List.iter check_decl ds
  | Struct s | Merged_struct_members s -> List.iter field s.fields
  | _ -> ()
