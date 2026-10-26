(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** No local is read after it is moved.  See [move_check.mli]. *)

open Names
open Minicpp

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

(* The variables found read after a move, in the body being checked. *)
type report = {mutable found : Id.t list}

(* A move in [a] read by [b], [b] running after [a] or beside it. *)
let check_after report a b =
  List.iter
    (fun m -> if List.exists (conflict m) (b.reads @ b.moves) then report.found <- var m :: report.found)
    a.moves

(* The local whose variant [e] reaches into: [x.v_mut()], [x->v()]. *)
let variant_of = function
  | CPPfun_call (_, CPPaccess (Adot, (CPPvar _ as x), _), {rev = []}) | CPPaccess_call (_, (CPPvar _ as x), _, []) ->
    Some x
  | _ -> None

(* The local [e] names storage inside of, as a reference bound to [e] does:
   the local itself, a field of it, the alternative its variant holds, a
   field of that.  Through a pointer, what is named is not the local's. *)
let rec reaches aliases e =
  match e with
  | CPPvar x -> Some (match Id.Map.find_opt x aliases with Some base -> base | None -> x)
  | CPPaccess (Adot, e, _) | CPPget (e, _) | CPPstd_get (_, Some e) -> reaches aliases e
  | CPPfun_call (_, CPPaccess (Adot, e, _), {rev = []}) | CPPaccess_call (Adot, e, _, []) -> reaches aliases e
  | _ -> None

(* [aliases] with each of [xs] a local of its own. *)
let own (aliases : aliases) xs = List.fold_left (fun m x -> Id.Map.remove x m) aliases xs

(* [aliases] with each of [xs] a reference into what [e] reaches, if it
   reaches a local, or else a local of its own. *)
let bind_into aliases xs e =
  match reaches aliases e with
  | Some base -> List.fold_left (fun m x -> Id.Map.add x base m) aliases xs
  | None -> own aliases xs

let rec is_reference = function Tref _ -> true | Tnamespace (_, t) -> is_reference t | _ -> false

(* [aliases] once [s] has run: a structured binding, or a declaration of a
   reference, binds its names into what it names; any other declaration
   binds a local of its own. *)
let aliases_after aliases = function
  | Sbind (xs, e) -> bind_into aliases xs e
  | Sasgn (x, Declare (ty, _), e) when is_reference ty -> bind_into aliases [x] e
  | Sasgn (x, (Declare _ | Declare_static _), _) | Sdecl (x, _, _) | Sdecl_init (x, _) | Sblock_custom (_, _, x, _, _, _, _)
    ->
    own aliases [x]
  | _ -> aliases

(* The member a read reaches when it reads one: a field, a field of the
   alternative a variant holds -- the cell a reuse arm hands its constructor
   as the token -- or a pair component through the projection mapping. *)
let member e =
  match e with
  | CPPaccess (Adot, CPPstd_get (_, Some holder), f) when variant_of holder <> None ->
    Some (Option.get (variant_of holder), Id.to_string f)
  | CPPaccess (Adot, x, f) | CPPget (x, f) -> Some (x, Id.to_string f)
  | CPPfun_call
      (_, CPPglob (_, _, Some {ci_inline = Some {it_shape = Inline_pair_projection f; _}; _}), {rev = [x]}) ->
    Some (x, f)
  | _ -> None

(* A member of the local [x]; of a reference, the part it names. *)
let member_of aliases x f =
  match local aliases x with Through t -> Through {t with member = Some f} | _ -> Member (x, f)

let rec expr report aliases e : effect_ =
  let expr = expr report aliases in
  match (member e, e) with
  | Some (CPPvar x, f), _ -> {none with reads = [member_of aliases x f]}
  | Some (CPPmove (CPPvar x), f), _ -> {none with moves = [member_of aliases x f]}
  | _, CPPmove m when (match member m with Some (CPPvar _, _) -> true | _ -> false) -> (
    match member m with Some (CPPvar x, f) -> {none with moves = [member_of aliases x f]} | _ -> none )
  | _, CPPraw _ -> raise Opaque
  | _, CPPvar x -> {none with reads = [local aliases x]}
  | _, CPPmove (CPPvar x) -> {none with moves = [local aliases x]}
  (* A reuse factory takes the storage of the local it is handed as its
     token, first, to rebuild it in place. *)
  | _, CPPfun_call (_, CPPqualified_t (_, f), args) when Generated_name.is_companion "reuse" f -> (
    match call_args args with
    | CPPmove (CPPvar x) :: rest -> unsequenced report ({none with moves = [Storage x]} :: List.map expr rest)
    | args -> unsequenced report (List.map expr args) )
  (* A method is called on the whole object, a variant's accessor included. *)
  | _, CPPfun_call (_, CPPaccess (Adot, CPPvar x, _), args) ->
    let args = List.map expr (call_args args) in
    unsequenced report ({none with reads = [local aliases x]} :: args)
  (* A condition runs first, and one arm after it. *)
  | _, CPPcond (c, a, b) ->
    let c = expr c and arms = union (expr a) (expr b) in
    check_after report c arms;
    union c arms
  | _, CPPbinop ((Band | Bor), l, r) ->
    let l = expr l and r = expr r in
    check_after report l r;
    union l r
  (* The value assigned is computed before the place it goes to. *)
  | _, CPPbinop (Bassign, l, r) ->
    let l = expr l and r = expr r in
    check_after report r l;
    union l r
  (* A braced initialiser evaluates its elements in order. *)
  | _, (CPPstruct (_, _, es) | CPPstruct_id (_, _, es) | CPPbraced es) ->
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
  | _, CPPlambda l ->
    body report aliases l.cl_body;
    {reads = List.map (local aliases) (free_vars_expr e); moves = List.map (local aliases) l.cl_moved}
  | _ ->
    (* Everything else evaluates its parts in an order C++ does not fix. *)
    let parts = ref [] in
    iter_expr_children ~on_expr:(fun e -> parts := expr e :: !parts) ~on_stmts:(body report aliases) e;
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

and stmt report jumps aliases live s =
  let at' = at report aliases and walk' = walk report jumps aliases in
  match s with
  | Sraw _ -> raise Opaque
  | Sreturn None | Sthrow _ -> []
  | Sreturn (Some e) -> at' [] e
  | Scontinue -> jumps.continue_
  | Sbreak -> jumps.break_
  | Sasgn (x, _, e) -> at' (kill (Whole x) live) e
  | Sassign_expr (lhs, e) | Sexpr (CPPbinop (Bassign, lhs, e)) -> (
    match (member lhs, lhs) with
    | Some (CPPvar x, f), _ -> at' (kill (member_of aliases x f) live) e
    | _, CPPvar x -> at' (kill (local aliases x) live) e
    | _ -> at' (at' live lhs) e )
  | Sdecl (x, _, _) | Sdecl_init (x, _) -> kill (Whole x) live
  | Sif (c, t, e) -> at' (walk' live t @ walk' live e) c
  | Sif_constexpr (_, t, e) -> walk' live t @ walk' live e
  | Sif_decl (x, _, c, t, e) ->
    let walk = walk report jumps (own aliases [x]) in
    at' (kill (Whole x) (walk live t @ walk live e)) c
  | Sblock ss -> walk' live ss
  | Swhile (c, ss) -> loop report aliases live (fun report l -> at report aliases l c) ss
  | Sfor_range (x, e, ss) -> at' (loop report (own aliases [x]) live (fun _ l -> kill (Whole x) l) ss) e
  | Sswitch (e, _, branches, dflt) ->
    let alts = List.map (fun (_, ss) -> walk' live ss) branches in
    let other = match dflt with Some ss -> walk' live ss | None -> live in
    at' (List.concat (other :: alts)) e
  (* A branch binds its fields by reference into the scrutinee; with no
     fields, it binds the alternative, by reference unless it owns the
     scrutinee, and then it moves the alternative out into a local of its
     own. *)
  | Smatch (scrut, branches, els) ->
    let branch b =
      let fields = List.map (fun fb -> fb.fb_name) b.smb_field_bindings in
      let aliases, bound =
        match (fields, b.smb_var) with
        | [], Some x when scrut.sc_owned -> (own aliases [x], [x])
        | [], Some x -> (bind_into aliases [x] scrut.sc_expr, [x])
        | _, _ -> (bind_into aliases fields scrut.sc_expr, fields)
      in
      let l = kill_all bound (walk report jumps aliases live b.smb_body) in
      List.fold_right (fun c l -> at report aliases l c) b.smb_extra_conds l
    in
    let other = match els with Some ss -> walk' live ss | None -> live in
    at' (List.concat (other :: List.map branch branches)) scrut.sc_expr
  | Scustom_case (_, scrut, _, branches, _) ->
    let branch (ps, _, ss) =
      let xs = List.map (fun p -> p.cp_name) ps in
      kill_all xs (walk report jumps (own aliases xs) live ss)
    in
    at' (List.concat_map branch branches) scrut
  | Sbind (xs, e) -> at' (kill_all xs live) e
  (* A block template declares the variable it binds. *)
  | Sblock_custom (_, _, x, _, args, _, _) ->
    let eff = List.fold_left (fun acc a -> union acc (expr report aliases a)) none args in
    let live = kill (Whole x) live in
    check_after report eff {none with reads = live};
    eff.reads @ eff.moves @ live
  | _ ->
    let live = ref live in
    iter_stmt_children ~on_expr:(fun e -> live := at' !live e) ~on_stmts:(fun _ -> ()) s;
    !live

(* A loop body runs again: its end is followed by the loop's head, which is
   followed by the body's start and by what comes after the loop.  The head is
   found quietly, until nothing new reaches it; then the body is checked once
   against it. *)
and loop report aliases after head_of ss =
  let pass report head =
    head_of report (walk report {continue_ = head; break_ = after} aliases head ss @ after)
  in
  let quiet = {found = []} in
  let rec fix head n =
    let head' = List.sort_uniq compare (pass quiet head @ head) in
    if n = 0 || List.length head' = List.length head then head' else fix head' (n - 1)
  in
  let head = fix (List.sort_uniq compare after) 16 in
  pass report head

(* The backend's own storage -- a loop's accumulator, a frame, a temporary
   -- is named with a leading underscore and handed over by protocols this
   walk cannot see: a frame pushed after a move of [_result] is resumed only
   once a base case has assigned it again.  Loopify checks its frames against
   the recursion plan; this checks the program's locals. *)
let backend x = String.length (Id.to_string x) > 0 && (Id.to_string x).[0] = '_'

let moved_reads ss =
  let report = {found = []} in
  body report Id.Map.empty ss;
  List.sort_uniq Id.compare (List.filter (fun x -> not (backend x)) report.found)

let check_body owner ss =
  List.iter
    (fun x ->
      Probe.violation "moved value read"
        Pp.(str "in " ++ owner ++ str ", " ++ Id.print x ++ str " is read after it is moved") )
    (moved_reads ss)

let rec check_decl d =
  let rec field (f, _, _) =
    match f with
    | Fmethod m -> check_body (Id.print m.mf_name) m.mf_body
    | Fnested_struct (_, fs) -> List.iter field fs
    | _ -> ()
  in
  match d with
  | Dfun {df_shape = Ddef (_, ss); df_path; _} ->
    let r, _ = match List.rev df_path.dp_inner with inner :: _ -> inner | [] -> df_path.dp_outer in
    check_body (GlobRef.print r) ss
  | Dtemplate (_, _, inner) -> check_decl inner
  | Dnspace (_, ds) -> List.iter check_decl ds
  | Dstruct s | Dfields s -> List.iter field s.ds_fields
  | _ -> ()
