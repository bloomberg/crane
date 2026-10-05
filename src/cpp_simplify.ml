(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Small local simplifications.  See [cpp_simplify.mli]. *)

open Names
open Minicpp
module MS = Mapping_semantics

(** {1 Branch facts} *)

(** A term a fact may be about: a variable or a numeral. *)
type term = Var of Id.t | Num of Z.t

let term_of = function
  | CPPvar x -> Some (Var x)
  | CPPnumeral (_, n) -> Some (Num n)
  | _ -> None

(** [small <= big], as unsigned integers. *)
type fact = {small : term; big : term}

let le a b =
  match (term_of a, term_of b) with
  | Some small, Some big -> [{small; big}]
  | _ -> []

(* [x != 0]: [1 <= x]. *)
let positive x = match term_of x with Some big -> [{small = Num Z.one; big}] | None -> []

let is_zero = function CPPnumeral (_, n) -> Z.equal n Z.zero | _ -> false

let is_nonzero_numeral = function CPPnumeral (_, n) -> not (Z.equal n Z.zero) | _ -> false

(** What the condition [c] establishes where it holds, and where it does
    not, read through the declared meanings of the comparisons it applies. *)
let rec facts_of c =
  match c with
  | CPPunop (Unot, c) ->
    let t, f = facts_of c in
    (f, t)
  | _ -> (
    match Cpp_declared.applied c with
    (* [x <= y], or [x < y]: either way [x <= y] where it holds, and
       [y <= x] where it does not. *)
    | Some (MS.Unsigned ((MS.Leb | MS.Ltb), _), [x; y]) -> (le x y, le y x)
    | Some (MS.Unsigned (MS.Eqb, _), [x; y]) ->
      ( le x y @ le y x,
        if is_zero y then positive x else if is_zero x then positive y else [] )
    | _ -> ([], []) )

(** Whether [facts] give [small <= big]. *)
let entails facts small big =
  match (term_of small, term_of big) with
  | Some s, Some b ->
    let covers f =
      f.big = b
      && (f.small = s
         || match (s, f.small) with Num k, Num k' -> Z.leq k k' | _ -> false)
    in
    (match s with Num k -> Z.equal k Z.zero | Var _ -> false)
    || s = b || List.exists covers facts
  | _ -> false

(** [facts] without those about [vars]. *)
let without vars facts =
  let stable = function Var x -> not (Id.Set.mem x vars) | Num _ -> true in
  List.filter (fun f -> stable f.small && stable f.big) facts

(** [facts] and the [new_facts] a condition gives, for the branch [body] it
    dominates: none about a name [body] redeclares, which would be another
    variable there.  An assignment ends a fact where it happens
    ({!stmts}). *)
let in_branch facts new_facts body =
  without (Id.Set.of_list (declared_ids body)) (facts @ new_facts)

(** {1 Rules} *)

(* The truth value [e] is written as: a [bool] literal, or a constructor of
   a declared boolean -- the first is [true]. *)
let truth = function
  | CPPbool b -> Some b
  | CPPglob (GlobRef.ConstructRef (ind, j), _, _) when MS.is_boolean ind -> Some (j = 1)
  | _ -> None

(* A declared operation the context makes unguarded, as the operator. *)
let unguarded facts e =
  match Cpp_declared.applied e with
  | Some (MS.Unsigned (op, (MS.W32 | MS.W64)), [a; b]) -> (
    match op with
    | MS.Div when is_nonzero_numeral b -> CPPbinop (Bdiv, a, b)
    | MS.Mod when is_nonzero_numeral b -> CPPbinop (Bmod, a, b)
    | MS.Sub_truncated when entails facts b a -> CPPbinop (Bsub, a, b)
    | _ -> e )
  | _ -> e

(* A [bool]: what a comparison, a connective or a declared comparison
   yields. *)
let is_bool = function
  | CPPbinop ((Beq | Bneq | Band | Bor), _, _) | CPPunop (Unot, _) | CPPbool _ -> true
  | c -> (
    match Cpp_declared.applied c with
    | Some (MS.Unsigned ((MS.Eqb | MS.Ltb | MS.Leb), _), _) -> true
    | _ -> false )

(* Drop each binding of a pure value nothing after it reads or assigns. *)
let rec drop_unused = function
  | [] -> []
  | Sasgn (x, Declare _, e) :: rest
    when pure_expr e
         && (not (List.exists (Id.equal x) (free_vars_body rest)))
         && not (Id.Set.mem x (assigned_vars rest)) ->
    drop_unused rest
  | s :: rest -> s :: drop_unused rest

(* A match on a declared boolean: its branches, true first. *)
let boolean_match cm =
  match cm.cm_inductive with GlobRef.IndRef ind -> MS.is_boolean ind | _ -> false

let nat_match cm =
  match cm.cm_inductive with GlobRef.IndRef ind -> MS.nat_width ind <> None | _ -> false

(* A two-way choice on [c] between [t] and [e], rebuilt by [rebuild]: a
   literal condition selects its branch, each branch learns what [c] tells
   it, and returning [c]'s truth value returns [c] -- when [c] is a [bool],
   which a boolean match's scrutinee is by its type. *)
let rec choice ?(typed_bool = false) facts c t e rebuild =
  match truth c with
  | Some b -> Sblock (stmts facts (if b then t else e))
  | None -> (
    let ft, ff = facts_of c in
    let t = stmts (in_branch facts ft t) t and e = stmts (in_branch facts ff e) e in
    match (t, e) with
    | [Sreturn (Some r1)], [Sreturn (Some r2)]
      when truth r1 = Some true && truth r2 = Some false && (typed_bool || is_bool c) ->
      Sreturn (Some c)
    | _ -> rebuild c t e )

(** [ss] simplified in order: a fact about a variable lasts until a statement
    assigns it.  The right-hand side of an assignment is evaluated before the
    store, so it still has the fact; a statement that assigns the variable
    anywhere inside -- a loop, a branch -- loses it throughout, since a later
    iteration reads what an earlier one stored. *)
and stmts facts ss =
  let rec go facts = function
    | [] -> []
    | s :: rest ->
      let assigned = assigned_vars [s] in
      let s =
        match s with
        | Sasgn (x, Existing, e) -> Sasgn (x, Existing, expr facts e)
        | _ -> stmt (without assigned facts) s
      in
      s :: go (without (Id.Set.union assigned (Id.Set.of_list (declared_ids [s]))) facts) rest
  in
  drop_unused (go facts ss)

and stmt facts s =
  match s with
  | Sif (c, t, e) -> choice facts (expr facts c) t e (fun c t e -> Sif (c, t, e))
  | Scustom_case (ty, c, tys, [(p0, t0, b0); (p1, t1, b1)], cm) when boolean_match cm ->
    choice ~typed_bool:true facts (expr facts c) b0 b1 (fun c b0 b1 ->
        Scustom_case (ty, c, tys, [(p0, t0, b0); (p1, t1, b1)], cm))
  (* The successor branch of a match on an unsigned nat: [1 <= x]. *)
  | Scustom_case (ty, (CPPvar _ as x), tys, [(p0, t0, b0); (p1, t1, b1)], cm)
    when nat_match cm ->
    Scustom_case
      ( ty, x, tys,
        [(p0, t0, stmts facts b0); (p1, t1, stmts (in_branch facts (positive x) b1) b1)],
        cm )
  (* Facts reach every other nested block as they are. *)
  | _ -> map_stmt ~fl:(stmts facts) (expr facts) (stmt facts) Fun.id s

and expr facts e =
  match e with
  | CPPlambda _ -> map_expr ~fl:(stmts []) (expr []) (stmt []) Fun.id e
  | CPPcond (c, x, y) when truth c <> None ->
    expr facts (if truth c = Some true then x else y)
  | _ -> unguarded facts (map_expr ~fl:(stmts facts) (expr facts) (stmt facts) Fun.id e)

let transform_decl d = map_decl ~fl:(stmts []) (expr []) (stmt []) Fun.id d
