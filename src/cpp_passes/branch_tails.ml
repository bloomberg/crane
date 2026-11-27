(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What the branches of a conditional end with, written once.  See
    [branch_tails.mli]. *)

module V = Cpp_ir.Variables

type stmt = Cpp_ir.Lowered.Stmt.t

(* [f] applied to the body of every function and method [d] defines. *)
let on_bodies (f : stmt list -> stmt list) (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  let rec member ((m, a, b) : _ Cpp_ir.Field.member) : _ Cpp_ir.Field.member =
    match m with
    | Method x -> (Method {x with body = f x.body}, a, b)
    | Nested_struct (x, ms) -> (Nested_struct (x, List.map member ms), a, b)
    | Out_of_line_declaration (Method x) -> (Out_of_line_declaration (Method {x with body = f x.body}), a, b)
    | _ -> (m, a, b)
  in
  let rec decl (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
    match d with
    | Function ({shape = Definition (ps, body); _} as fn) -> Function {fn with shape = Definition (ps, f body)}
    | Template (ps, c, d) -> Template (ps, c, decl d)
    | Namespace (x, ds) -> Namespace (x, List.map decl ds)
    | Struct s -> Struct {s with fields = List.map member s.fields}
    | Merged_struct_members s -> Merged_struct_members {s with fields = List.map member s.fields}
    | Member_definition ({member = Method m; _} as md) ->
      Member_definition {md with member = Method {m with body = f m.body}}
    | _ -> d
  in
  decl d

(** {2 Trailing returns} *)

(* The one branch of an instantiated custom match whose body is the last
   code its template runs: a template with a single [%br] after which it
   writes nothing but closing braces and semicolons -- a pair taken apart,
   [auto [a, b] = p; %br0].  Control leaving that body leaves the match. *)
let tail_branch (m : _ Cpp_ir.Stmt.Custom_match.t) =
  match m.pieces with
  | Instantiated pieces -> (
    let closing = String.for_all (fun c -> String.contains " \t\n};" c) in
    let rec after_branch = function
      | Cpp_ir.Stmt.Custom_match.Branch i :: rest ->
        if List.for_all (function Cpp_ir.Stmt.Custom_match.Text t -> closing t | _ -> false) rest then Some i else None
      | _ :: rest -> after_branch rest
      | [] -> None
    in
    match List.filter (function Cpp_ir.Stmt.Custom_match.Branch _ -> true | _ -> false) pieces with
    | [_] -> after_branch pieces
    | _ -> None )
  | _ -> None

(* [ss], the tail of a function's body, without the [return;] control
   reaches its end with: its last statement if that is one, or the last
   statements of the branches of a conditional or a match that ends it, or
   of the tail branch of a custom match ({!tail_branch}).  A
   branch the drop would leave empty keeps its [return;] -- [if (c) {} else
   { ... }] reads worse than an early exit -- except an [if]'s [else]
   branch, which is then not written. *)
let rec drop_tail (ss : stmt list) : stmt list =
  let keep_nonempty b = match drop_tail b with [] -> b | b' -> b' in
  match List.rev ss with
  | Return None :: rest -> List.rev rest
  | If i :: rest ->
    let else_ = drop_tail i.else_ in
    let then_ = if else_ = [] then drop_tail i.then_ else keep_nonempty i.then_ in
    List.rev ((If {i with then_; else_} : stmt) :: rest)
  | Match (scrut, branches, default) :: rest ->
    let branch (b : _ Cpp_ir.Stmt.Match.branch) = {b with body = keep_nonempty b.body} in
    List.rev ((Match (scrut, List.map branch branches, Option.map keep_nonempty default) : stmt) :: rest)
  | Custom_match m :: rest -> (
    match tail_branch m with
    | Some k ->
      let branches = List.mapi (fun i (b : _ Cpp_ir.Stmt.Custom_match.branch) -> if i = k then {b with body = keep_nonempty b.body} else b) m.branches in
      List.rev ((Custom_match {m with branches} : stmt) :: rest)
    | None -> ss )
  | Block b :: rest -> List.rev ((Block (drop_tail b) : stmt) :: rest)
  | _ -> ss

let drop_trailing_returns = on_bodies drop_tail

(** {2 Common suffixes} *)

(* Whether [s] may run after the [if] rather than at the end of each of its
   branches: an assignment (to an expression, or to a variable already
   declared) or an expression, which jumps nowhere and declares nothing. *)
let movable (s : stmt) =
  match s with
  | Assign _ | Expression _ | Bind_variable (_, Existing, _) -> true
  | _ -> false

(* Structural equality, refusing what cannot be compared. *)
let same (a : stmt) (b : stmt) = try a = b with Invalid_argument _ -> false

(* The longest common suffix of [xs] and [ys] made of movable statements,
   with what precedes it in each: [(xs', ys', suffix)]. *)
let split_suffix xs ys =
  let rec go rx ry acc =
    match (rx, ry) with
    | x :: rx', y :: ry' when movable x && same x y -> go rx' ry' (x :: acc)
    | _ -> (List.rev rx, List.rev ry, acc)
  in
  go (List.rev xs) (List.rev ys) []

(* The negation of the condition [c], where it can be written without
   parentheses the printer might not supply: a comparison for equality
   flipped, a negation dropped, a variable negated.  A mapping's text -- [a
   < b] -- is not negated: [!] would bind to its first operand. *)
let negation (c : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t option =
  match c with
  | Binary (Equal, a, b) -> Some (Binary (Not_equal, a, b))
  | Binary (Not_equal, a, b) -> Some (Binary (Equal, a, b))
  | Unary (Not, a) -> Some a
  | Local _ -> Some (Unary (Not, c))
  | _ -> None

(* An [if] whose branches share a suffix reading no variable either branch
   declares, followed by that suffix.  The suffix is cut down from its front
   until it reads none: what remains still ends both branches.  A [then]
   branch left empty takes the [else] branch under the negated condition;
   where the condition cannot be negated plainly ({!negation}), nothing is
   hoisted, since [if (c) {} else { ... }] reads worse than the repeated
   statements. *)
let hoist (s : stmt) : stmt list =
  match s with
  | If ({then_ = _ :: _; else_ = _ :: _; _} as i) ->
    let then_, else_, suffix = split_suffix i.then_ i.else_ in
    let rec fit then_ else_ suffix =
      match suffix with
      | [] -> [s]
      | s0 :: rest ->
        let declared = V.declared then_ @ V.declared else_ in
        if List.exists (fun x -> V.mem x declared) (V.free_in_body suffix) then
          fit (then_ @ [s0]) (else_ @ [s0]) rest
        else
          match (then_, else_) with
          | [], [] when V.pure i.condition -> suffix
          | [], [] -> (Expression i.condition : stmt) :: suffix
          | [], _ -> (
            match negation i.condition with
            | Some condition -> (If {condition; then_ = else_; else_ = []} : stmt) :: suffix
            | None -> [s] )
          | _ -> (If {i with then_; else_} : stmt) :: suffix
    in
    fit then_ else_ suffix
  | _ -> [s]

let hoist_common_suffixes (d : Cpp_ir.Lowered.Decl.t) : Cpp_ir.Lowered.Decl.t =
  let rec stmts ss = List.concat_map (fun s -> hoist (stmt s)) ss
  and stmt s = Cpp_ir.Map.stmt (rw ()) s
  and expr e = Cpp_ir.Map.expr (rw ()) e
  and rw () = Cpp_ir.Map.make ~stmts ~expr ~stmt ~type_:Fun.id () in
  Cpp_ir.Map.decl (rw ()) d
