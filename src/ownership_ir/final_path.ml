(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Moves of a frame machine's loop invariants on its final path.  See
    [final_path.mli]. *)

open Names
open Cpp_ir.Grammar

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

let opt_list = function Some x -> [x] | None -> []

let pushed = function
  | Stmt.Expression (Expr.Call (_, Expr.Access (_, Expr.Local st, eb), [Expr.Local_aggregate {struct_; _}]))
    when String.equal (Id.to_string st) "_stack" && String.equal (Id.to_string eb) "emplace_back" ->
    Some struct_
  | _ -> None

let is_push ~entry s = match pushed s with Some t -> Id.equal t entry | None -> false

let rec pushes ~entry (s : stmt) =
  is_push ~entry s
  ||
  let found = ref false in
  Cpp_ir.Subterms.stmt
    ~expr:(fun e -> if expr_pushes ~entry e then found := true)
    ~stmts:(fun l -> if List.exists (pushes ~entry) l then found := true)
    s;
  !found

and expr_pushes ~entry (e : expr) =
  let found = ref false in
  Cpp_ir.Subterms.expr
    ~expr:(fun e -> if expr_pushes ~entry e then found := true)
    ~stmts:(fun l -> if List.exists (pushes ~entry) l then found := true)
    e;
  !found

(* The most entry frames a path through [l] pushes, 2 standing for more than
   one: a loop or a closure that pushes may push any number. *)
let rec most_pushes ~entry l = List.fold_left (fun n s -> min 2 (n + most_pushes_stmt ~entry s)) 0 l

and most_pushes_stmt ~entry (s : stmt) =
  if is_push ~entry s then 1
  else
    let alternatives test bodies =
      if expr_pushes ~entry test then 2 else List.fold_left (fun n b -> max n (most_pushes ~entry b)) 0 bodies
    in
    match s with
    | Stmt.If i -> alternatives i.condition [i.then_; i.else_]
    | Stmt.If_constexpr i -> max (most_pushes ~entry i.then_) (most_pushes ~entry i.else_)
    | Stmt.If_declaration i -> alternatives i.init [i.then_; i.else_]
    | Stmt.Switch w ->
      alternatives w.scrutinee (opt_list w.default @ List.map snd w.branches)
    | Stmt.Custom_match m -> alternatives m.scrutinee (List.map (fun (b : _ Custom_match.branch) -> b.body) m.branches)
    | Stmt.Match (sc, branches, default) ->
      alternatives sc.expr (opt_list default @ List.map (fun (b : _ Match.branch) -> b.body) branches)
    | Stmt.Block b -> most_pushes ~entry b
    | s -> if pushes ~entry s then 2 else 0

(* [s] with every move of a local in [vars] turned into a read of it. *)
let strip vars =
  let rec fe (e : expr) : expr =
    match e with
    | Expr.Move (Expr.Local id) when Id.Set.mem id vars -> Expr.Local id
    | Expr.Lambda l when List.exists (fun x -> Id.Set.mem x vars) l.moved ->
      fe (Expr.Lambda {l with moved = List.filter (fun x -> not (Id.Set.mem x vars)) l.moved})
    | e -> Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  (fe, fs)

(* Rewrite [stmts] path by path: [on_final] is applied to a statement no
   entry push follows and that pushes none, [elsewhere] to the parts of any
   other statement that are not themselves paths -- a test, a scrutinee, a
   loop, a closure. *)
let by_path ~entry ~on_final ~elsewhere ~elsewhere_expr stmts =
  let rec block ~after l =
    fst (List.fold_right (fun s (acc, after) -> (stmt ~after s :: acc, after || pushes ~entry s)) l ([], after))
  and stmt ~after (s : stmt) : stmt =
    if (not after) && not (pushes ~entry s) then on_final s
    else
      match s with
      | Stmt.If i ->
        Stmt.If {condition = elsewhere_expr i.condition; then_ = block ~after i.then_; else_ = block ~after i.else_}
      | Stmt.If_constexpr i -> Stmt.If_constexpr {i with then_ = block ~after i.then_; else_ = block ~after i.else_}
      | Stmt.If_declaration i ->
        Stmt.If_declaration
          {i with init = elsewhere_expr i.init; then_ = block ~after i.then_; else_ = block ~after i.else_}
      | Stmt.Switch w ->
        Stmt.Switch
          { w with
            scrutinee = elsewhere_expr w.scrutinee;
            branches = List.map (fun (c, b) -> (c, block ~after b)) w.branches;
            default = Option.map (block ~after) w.default }
      | Stmt.Custom_match m ->
        Stmt.Custom_match
          { m with
            scrutinee = elsewhere_expr m.scrutinee;
            branches = List.map (fun (b : _ Custom_match.branch) -> {b with body = block ~after b.body}) m.branches }
      | Stmt.Match (sc, branches, default) ->
        Stmt.Match
          ( {sc with expr = elsewhere_expr sc.expr},
            List.map
              (fun (b : _ Match.branch) ->
                {b with extra_conditions = List.map elsewhere_expr b.extra_conditions; body = block ~after b.body} )
              branches,
            Option.map (block ~after) default )
      | Stmt.Block b -> Stmt.Block (block ~after b)
      | s -> elsewhere s
  in
  block ~after:false stmts

let keep_final_moves ~entry keep stmts =
  if Id.Set.is_empty keep then stmts
  else
    let fe, fs = strip keep in
    by_path ~entry ~on_final:Fun.id ~elsewhere:fs ~elsewhere_expr:fe stmts

let movable ~entry ~entry_body ~others candidates =
  if
    most_pushes ~entry entry_body <= 1
    && not (List.exists (List.exists (pushes ~entry)) others)
  then
    let read_elsewhere = Id.Set.of_list (List.concat_map Cpp_ir.Variables.free_in_body others) in
    Id.Set.filter (fun id -> not (Id.Set.mem id read_elsewhere)) candidates
  else Id.Set.empty

(* Whether [l] takes an address anywhere: a frame may then point into a
   local the final path moves. *)
let takes_address l =
  let found = ref false in
  let rec fe (e : expr) : expr =
    (match e with Expr.Unary (Unary_operator.Address_of, _) -> found := true | _ -> ());
    Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.iter (fun s -> ignore (fs s)) l;
  !found

let moves_in l =
  let found = ref Id.Set.empty in
  let rec fe (e : expr) : expr =
    (match e with Expr.Move (Expr.Local id) -> found := Id.Set.add id !found | _ -> ());
    Cpp_ir.Map.expr (rw ()) e
  and fs (s : stmt) = Cpp_ir.Map.stmt (rw ()) s
  and rw () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.iter (fun s -> ignore (fs s)) l;
  !found

(* Whether a frame struct declared among [prev] keeps a pointer: it may
   point into a local the final path moves. *)
let frames_point prev =
  let rec is_pointer (t : _ Type.t) =
    match t with Type.Pointer _ -> true | Type.Const t -> is_pointer t | _ -> false
  in
  List.exists
    (function Stmt.Local_struct (_, fields) -> List.exists (fun (_, t) -> is_pointer t) fields | _ -> false)
    prev

let erase_final_moves stmts =
  let rec block l = block_after [] l
  and block_after prev l =
    match l with
    | init :: (Stmt.While (cond, ([_; Stmt.Match (sc, branches, default)] as loop_body)) as w) :: rest -> (
      let fallback () = init :: stmt w :: block_after (w :: init :: prev) rest in
      match pushed init with
      | Some entry when default = None && (not (takes_address loop_body)) && not (frames_point prev) -> (
        let is_entry (b : _ Match.branch) =
          match b.ctor_type with Type.External (n, _) -> String.equal n (Id.to_string entry) | _ -> false
        in
        match List.partition is_entry branches with
        | [eb], others ->
          let declared_inside =
            Id.Set.diff (moves_in [w]) (Id.Set.of_list (Cpp_ir.Variables.free_in_stmt w))
          in
          let read_after = Id.Set.of_list (Cpp_ir.Variables.free_in_body rest) in
          let candidates = Id.Set.diff (Id.Set.diff (moves_in eb.body) declared_inside) read_after in
          let others = List.map (fun (b : _ Match.branch) -> b.body) others in
          let vars = movable ~entry ~entry_body:eb.body ~others candidates in
          if Id.Set.is_empty vars then fallback ()
          else
            let eb_body =
              by_path ~entry ~on_final:(snd (strip vars)) ~elsewhere:Fun.id ~elsewhere_expr:Fun.id eb.body
            in
            let branches = List.map (fun b -> if is_entry b then {b with body = eb_body} else b) branches in
            let loop_body = match loop_body with [bind; _] -> [bind; Stmt.Match (sc, branches, default)] | l -> l in
            init :: stmt (Stmt.While (cond, loop_body)) :: block_after (w :: init :: prev) rest
        | _ -> fallback () )
      | _ -> fallback () )
    | s :: rest -> stmt s :: block_after (s :: prev) rest
    | [] -> []
  and stmt (s : stmt) : stmt = Cpp_ir.Map.stmt (Cpp_ir.Map.make ~stmts:block ~expr:expr ~stmt:stmt ~type_:Fun.id ()) s
  and expr (e : expr) : expr = Cpp_ir.Map.expr (Cpp_ir.Map.make ~stmts:block ~expr:expr ~stmt:stmt ~type_:Fun.id ()) e in
  block stmts
