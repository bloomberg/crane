
(** Direct MiniML → Go pretty-printer.

    Converts MiniML AST nodes to Go 1.18+ source code.

    Key design decisions:
    - Algebraic data types use a tagged-struct representation:
      a single impl struct with discriminant [_v int] and all constructor
      fields, plus a public pointer alias [type T[A any] = *tImpl[A]].
    - All-nullary inductives (enums) map to [type T int] + iota [const] blocks.
    - Records map to plain Go structs with named fields.
    - Pattern matching becomes [switch _scrut._v { case N: ... }] wrapped in
      an immediately-invoked function expression (IIFE) when in expression
      context.
    - Curried lambdas are collected and emitted as a single multi-parameter
      Go function literal.
    - Type parameters follow from ML type variables [Tvar i → T{i} any].
*)

open Pp
open Names
open Table
open Miniml
open Mlutil
open Common

(* ===================================================================
   Import tracking
   =================================================================== *)

module SSet = Set.Make (String)

let _needed_imports : SSet.t ref = ref SSet.empty

(** Constructors emitted as enum constants (not function calls).
    Populated by [pp_go_ind_packet] for all-nullary inductives. *)
let go_enum_ctor_set : (Names.GlobRef.t, unit) Hashtbl.t = Hashtbl.create 16

(** Maps renamed Go variable [Id.t] → its ML type.
    Used in [pp_go_expr] to decide when to insert type assertions. *)
let var_types : (Names.Id.t, ml_type) Hashtbl.t = Hashtbl.create 64

(** Set of variables that are ACTUALLY typed [any] in Go because they were
    assigned from an [any]-typed impl-struct field (e.g. [_c1_d0 any]).
    These variables may need type assertions at use sites. *)
let go_any_typed_vars : (Names.Id.t, unit) Hashtbl.t = Hashtbl.create 32

(** Set of variables bound inside custom match templates (e.g. [%b1a0] in
    the nat/sumbool/list templates).  Their Go types come from the template
    expression, not from [any] field accesses, so they must NOT receive type
    assertions even when their ML type is [Taxiom]. *)
let go_custom_match_vars : (Names.Id.t, unit) Hashtbl.t = Hashtbl.create 32

(** Maps global term [GlobRef.t] → its ML type.
    Populated by [pp_go_dterm] / [pp_go_dfix] before generating each body so
    that [MLapp] can propagate expected argument types and insert assertions
    when an [any]-typed actual argument is passed to a concretely-typed param. *)
let go_term_types : (Names.GlobRef.t, ml_type) Hashtbl.t = Hashtbl.create 64

(** Maps record [IndRef] → ordered list of [(field_name, ml_type)] pairs.
    Populated by [pp_go_record_packet]; consulted by [pp_go_case] to
    generate direct field access instead of [*fooImpl] pointer boxing, and
    to register variables with their actual (concrete) field ML types so
    that [pp_go_expr] does not insert spurious type assertions. *)
let go_record_ind_fields : (Names.GlobRef.t, (string * ml_type) list) Hashtbl.t =
  Hashtbl.create 8

let reset_go_state () =
  _needed_imports := SSet.empty;
  Hashtbl.clear go_enum_ctor_set;
  Hashtbl.clear var_types;
  Hashtbl.clear go_any_typed_vars;
  Hashtbl.clear go_custom_match_vars;
  Hashtbl.clear go_term_types;
  Hashtbl.clear go_record_ind_fields

let register_enum_ctor (r : Names.GlobRef.t) =
  Hashtbl.replace go_enum_ctor_set r ()

let is_enum_ctor (r : Names.GlobRef.t) =
  Hashtbl.mem go_enum_ctor_set r

let register_var_type (id : Names.Id.t) (ty : ml_type) =
  Hashtbl.replace var_types id ty

let lookup_var_type (id : Names.Id.t) : ml_type =
  match Hashtbl.find_opt var_types id with
  | Some ty -> ty
  | None -> Taxiom

(** True when a ML type prints as [any] — type assertions cannot help. *)
let is_opaque_ty = function
  | Taxiom | Tunknown | Tdummy _ | Tmeta _ -> true
  | _ -> false

(* ===================================================================
   Go keyword set
   =================================================================== *)

let go_keywords =
  List.fold_right
    (fun s -> Id.Set.add (Id.of_string s))
    [
      (* Reserved words *)
      "break"; "case"; "chan"; "const"; "continue"; "default"; "defer";
      "else"; "fallthrough"; "for"; "func"; "go"; "goto"; "if"; "import";
      "interface"; "map"; "package"; "range"; "return"; "select"; "struct";
      "switch"; "type"; "var";
      (* Pre-declared identifiers *)
      "any"; "bool"; "byte"; "complex64"; "complex128"; "error";
      "float32"; "float64"; "int"; "int8"; "int16"; "int32"; "int64";
      "rune"; "string"; "uint"; "uint8"; "uint16"; "uint32"; "uint64";
      "uintptr"; "true"; "false"; "nil"; "iota";
      "append"; "cap"; "clear"; "close"; "complex"; "copy"; "delete";
      "imag"; "len"; "make"; "max"; "min"; "new"; "panic"; "print";
      "println"; "real"; "recover";
      (* Our own synthetic names *)
      "_v";
    ]
    Id.Set.empty

(* ===================================================================
   Utilities
   =================================================================== *)

let pp_comma_sep f l = prlist_with_sep (fun () -> str ", ") f l

(** Resolve ml_ident to an Id.t, using "_" for anonymous/dummy. *)
let id_of_mlident = function
  | Id i -> i
  | Dummy -> Id.of_string "_"
  | Tmp i -> i

(** Check if a GlobRef has a custom type mapping. *)
let find_type_custom_opt r =
  if is_custom r then Some (find_type_custom r) else None

(** Count maximum distinct Tvar index + 1 appearing in a type. *)
let rec count_tvars = function
  | Tarr (t1, t2) -> max (count_tvars t1) (count_tvars t2)
  | Tglob (_, tys, _) ->
    List.fold_left (fun acc t -> max acc (count_tvars t)) 0 tys
  | Tvar i | Tvar' i -> i + 1
  | _ -> 0

(** Replace [Tvar i] and [Tvar' i] with [Taxiom] for all [i >= valid_count].
    Used to eliminate "phantom" type variables from return types when those
    variables do not appear in any parameter type and therefore cannot be
    inferred by the Go compiler at call sites. *)
let rec mask_phantom_tvars valid_count = function
  | Tvar i | Tvar' i -> if i < valid_count then Tvar i else Taxiom
  | Tarr (t1, t2) ->
    Tarr (mask_phantom_tvars valid_count t1,
          mask_phantom_tvars valid_count t2)
  | Tglob (r, tys, k) ->
    Tglob (r, List.map (mask_phantom_tvars valid_count) tys, k)
  | t -> t

(** Erase all [Tvar] / [Tvar'] occurrences to [Taxiom].
    Used when looking up a global function's type from [go_term_types] at a
    call site: the type variables in a polymorphic function's ML type are
    meaningful inside that function's scope (where T1, T2 are declared) but
    undefined at arbitrary call sites. Erasing them avoids emitting [list[T1]]
    in a function that has no type-parameter declaration. *)
let rec erase_tvars = function
  | Tvar _ | Tvar' _ -> Taxiom
  | Tarr (t1, t2) -> Tarr (erase_tvars t1, erase_tvars t2)
  | Tglob (r, tys, k) -> Tglob (r, List.map erase_tvars tys, k)
  | t -> t

(** Collect arrow types: [Tarr(A, Tarr(B, C))] → [(A; B), C]. *)
let rec collect_arrows = function
  | Tarr (t1, t2) ->
    let ts, ret = collect_arrows t2 in
    (t1 :: ts, ret)
  | t -> ([], t)

(** Drop the first [n] arrow types from [ty].
    Stops early when [ty] is already opaque or not an arrow.
    Used to compute the effective return type after applying [n] arguments. *)
let rec drop_arrows n ty = match n, ty with
  | 0, t -> t
  | _, (Taxiom as t) | _, (Tunknown as t) -> t
  | _, Tarr (_, r) -> drop_arrows (n - 1) r
  | _, t -> t

(** Template substitution helpers.

    Recognised escape sequences in all template strings:
    - [%%]   → literal [%]
    - [%tN]  → type argument N  (apply_type_template / apply_ctor_template)
    - [%aN]  → value argument N (apply_expr_template / apply_ctor_template)
    - [%scrut], [%brN], [%bNaN] → case-expression placeholders
      (handled by the Rocq extraction framework before we ever see them)
    Any other [%X] sequence is passed through unchanged.
*)

(** Substitute [%t{n}] placeholders in a custom template string.
    [pp_ty] renders a single type argument. *)
let apply_type_template templ tys pp_ty =
  let len = String.length templ in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if templ.[!i] = '%' && !i + 1 < len then begin
      let c = templ.[!i + 1] in
      if c = '%' then begin
        (* %% → literal % *)
        Buffer.add_char buf '%'; i := !i + 2
      end else if c = 't' && !i + 2 < len then begin
        let j = ref (!i + 2) in
        while !j < len && templ.[!j] >= '0' && templ.[!j] <= '9' do incr j done;
        if !j > !i + 2 then begin
          let idx = int_of_string (String.sub templ (!i + 2) (!j - !i - 2)) in
          Buffer.add_string buf
            (if idx < List.length tys
             then string_of_ppcmds (pp_ty (List.nth tys idx))
             else "any");
          i := !j
        end else begin
          Buffer.add_char buf templ.[!i]; incr i
        end
      end else begin
        Buffer.add_char buf templ.[!i]; incr i
      end
    end else begin
      Buffer.add_char buf templ.[!i]; incr i
    end
  done;
  str (Buffer.contents buf)

(** Substitute both [%t{n}] (type) and [%a{n}] (argument) placeholders in
    a constructor template.  Used for inductive constructor templates that
    mention the enclosing type's parameters, e.g.:
    ["struct{ fst %t0; snd %t1 }{fst: %a0, snd: %a1}"]. *)
let apply_ctor_template templ tys pp_ty pp_args =
  let len = String.length templ in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if templ.[!i] = '%' && !i + 1 < len then begin
      let c = templ.[!i + 1] in
      if c = '%' then begin
        (* %% → literal % *)
        Buffer.add_char buf '%'; i := !i + 2
      end else if (c = 't' || c = 'a') && !i + 2 < len then begin
        let j = ref (!i + 2) in
        while !j < len && templ.[!j] >= '0' && templ.[!j] <= '9' do incr j done;
        if !j > !i + 2 then begin
          let idx = int_of_string (String.sub templ (!i + 2) (!j - !i - 2)) in
          let s =
            if c = 't' then
              if idx < List.length tys
              then string_of_ppcmds (pp_ty (List.nth tys idx))
              else "any"
            else
              if idx < List.length pp_args
              then string_of_ppcmds (List.nth pp_args idx)
              else "_a" ^ string_of_int idx
          in
          Buffer.add_string buf s;
          i := !j
        end else begin
          Buffer.add_char buf templ.[!i]; incr i
        end
      end else begin
        Buffer.add_char buf templ.[!i]; incr i
      end
    end else begin
      Buffer.add_char buf templ.[!i]; incr i
    end
  done;
  str (Buffer.contents buf)

(** Substitute [%a{n}] placeholders in a custom expression template.
    [pp_args] is a list of already-rendered argument Pp.t values. *)
let apply_expr_template templ pp_args =
  let len = String.length templ in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if templ.[!i] = '%' && !i + 1 < len then begin
      let c = templ.[!i + 1] in
      if c = '%' then begin
        (* %% → literal % *)
        Buffer.add_char buf '%'; i := !i + 2
      end else if c = 'a' && !i + 2 < len then begin
        let j = ref (!i + 2) in
        while !j < len && templ.[!j] >= '0' && templ.[!j] <= '9' do incr j done;
        if !j > !i + 2 then begin
          let idx = int_of_string (String.sub templ (!i + 2) (!j - !i - 2)) in
          Buffer.add_string buf
            (if idx < List.length pp_args
             then string_of_ppcmds (List.nth pp_args idx)
             else "_a" ^ string_of_int idx);
          i := !j
        end else begin
          Buffer.add_char buf templ.[!i]; incr i
        end
      end else begin
        Buffer.add_char buf templ.[!i]; incr i
      end
    end else begin
      Buffer.add_char buf templ.[!i]; incr i
    end
  done;
  str (Buffer.contents buf)

(* ===================================================================
   Type pretty-printing
   =================================================================== *)

(** Pretty-print a MiniML type as a Go type expression. *)
let rec pp_go_type = function
  | Tarr (t1, t2) ->
    str "func(" ++ pp_go_type t1 ++ str ") " ++ pp_go_type t2
  | Tglob (r, tys, _) ->
    ( match find_type_custom_opt r with
    | Some (_, templ) -> apply_type_template templ tys pp_go_type
    | None ->
      let name = str (pp_global_name Type r) in
      if tys = [] then name
      else name ++ str "[" ++ pp_comma_sep pp_go_type tys ++ str "]" )
  | Tvar i | Tvar' i -> str ("T" ^ string_of_int i)
  | Tstring -> str "string"
  | Tdummy _ | Tunknown | Tmeta _ | Taxiom -> str "any"

(** Pretty-print Go generic type-parameter declarations for functions.
    MiniML Tvar indices are 1-based: Tvar 1 = first real param.
    [count_tvars] returns max(i)+1, so index 0 is never a real param.
    We emit T1…T{n-1} (skipping T0). *)
let pp_go_type_params n =
  if n <= 1 then mt ()
  else
    str "["
    ++ prlist_with_sep (fun () -> str ", ")
         (fun i -> str ("T" ^ string_of_int i) ++ str " any")
         (List.init (n - 1) (fun i -> i + 1))
    ++ str "]"

(** Pretty-print named Go type-parameter declarations from an Id list.
    MiniML uses 1-based Tvar indices (Tvar 1 = first param), so we emit
    T1, T2, … to match what [pp_go_type] produces for [Tvar i]. *)
let pp_go_tparams ids =
  let n = List.length ids in
  if n = 0 then mt ()
  else
    str "["
    ++ prlist_with_sep (fun () -> str ", ")
         (fun i -> str ("T" ^ string_of_int (i + 1)) ++ str " any")
         (List.init n Fun.id)
    ++ str "]"

(** Pretty-print type arguments [T1, T2, …] matching the 1-based Tvar scheme. *)
let pp_go_targs ids =
  let n = List.length ids in
  if n = 0 then mt ()
  else
    str "["
    ++ prlist_with_sep (fun () -> str ", ")
         (fun i -> str ("T" ^ string_of_int (i + 1)))
         (List.init n Fun.id)
    ++ str "]"

(* ===================================================================
   Expression pretty-printing
   =================================================================== *)

(** Counter for unique scrutinee variable names to avoid shadowing in
    nested pattern matches. *)
let scrut_counter = ref 0

let fresh_scrut () =
  incr scrut_counter;
  Id.of_string ("_scrut" ^ string_of_int !scrut_counter)

(** Reset the scrutinee counter between extraction passes. *)
let reset_scrut_counter () = scrut_counter := 0

(** Flatten a curried application tree.
    [MLapp(MLapp(f, a1), a2)] → [(f, a1 @ a2)].
    MiniML represents multi-argument calls in curried form; flattening lets
    monad erasure and inline-custom template expansion see all args at once. *)
let rec flatten_app f args =
  match f with
  | MLapp (inner_f, inner_args) -> flatten_app inner_f (inner_args @ args)
  | _ -> (f, args)

(** Returns [true] when expression [e] will produce a Go [any]-typed value.
    Used in let-bindings to decide whether to tag the bound variable in
    [go_any_typed_vars] so that later use sites can insert type assertions.

    Conservative rules:
    - [MLcase _]          → always [func() any { ... }()], so result is [any].
    - [MLapp (f, args)]   → [any] iff the effective return type of [f] after
                            applying all args is opaque (Taxiom / Tunknown).
    - [MLrel id]          → [any] iff [id] is itself in [go_any_typed_vars] or
                            has an opaque registered type.
    - [MLletin _],[MLfix _] → conservative [any] (nested IIFEs default to any).
    - Everything else     → concrete Go type, so [false]. *)
let rec is_rhs_any env e =
  match e with
  | MLcase (_, _, branches) ->
    (* Standard case expressions always produce any-typed IIFEs.
       Exception: single-branch record matches where the body is a direct
       field access (MLrel n) on a field with a non-opaque ML type.
       In those cases pp_go_case infers the IIFE return type from the field
       type (via effective_iife_ty), so the bound variable is concrete.

       De Bruijn convention: push_vars' (List.rev ids_typed) env pushes
       ids[n-1] first and ids[0] last, so ids[k] gets de Bruijn k+1.
       The pp_assigns loop uses renamed[k] → field_info[k], where
       renamed[k] = renamed-of-ids[n-1-k], so ids[j] → field_info[n-1-j].
       Combining: de Bruijn m = ids[m-1] → field_info[n_ids - m].
       We use field_info from go_record_ind_fields (which has concrete types)
       rather than the potentially-erased MiniML ids types. *)
    not (
      Array.length branches = 1 &&
      ( match branches.(0) with
      | (ids, _, pat, MLrel n) ->
        ( match pat with
        | Pusual (GlobRef.ConstructRef ((kn2, ii2), _))
        | Pcons  (GlobRef.ConstructRef ((kn2, ii2), _), _) ->
          let ind_ref2 = GlobRef.IndRef (kn2, ii2) in
          ( match Hashtbl.find_opt go_record_ind_fields ind_ref2 with
          | None -> false
          | Some fi ->
            let n_ids = List.length ids in
            n >= 1 && n <= n_ids &&
            ( match List.nth_opt fi (n_ids - n) with
            | Some (_, ft) -> not (is_opaque_ty ft)
            | None -> false ) )
        | _ -> false )
      | _ -> false )
    )
  | MLapp (f0, args0) ->
    let f, args = flatten_app f0 args0 in
    ( match f with
    (* Inline-custom templates expand to Go expressions with concrete types. *)
    | MLglob (r, _) when is_inline_custom r -> false
    (* [ret x] is erased to [x]; the bound value has the same Go type as [x]. *)
    | MLglob (r, _) when Table.is_ret r ->
      ( match List.rev args with
      | last :: _ -> is_rhs_any env last
      | []        -> false )
    | _ ->
      (* Determine the ML type of the function, if known. *)
      let f_ty_opt = match f with
        | MLrel n ->
          let vty = lookup_var_type (get_db_name n env) in
          if vty = Taxiom then None else Some vty
        | MLglob (r, _) ->
          ( match Hashtbl.find_opt go_term_types r with
          | Some ty -> Some (erase_tvars ty)
          | None    -> None )
        | _ -> None
      in
      (* Return [true] only when the function's return type is KNOWN and opaque.
         Unknown functions (not in go_term_types, not MLrel) are assumed to
         return a concrete Go type, avoiding spurious [any] tagging. *)
      ( match f_ty_opt with
      | None    -> false
      | Some ft -> is_opaque_ty (drop_arrows (List.length args) ft) ) )
  | MLrel n ->
    let id = get_db_name n env in
    Hashtbl.mem go_any_typed_vars id || is_opaque_ty (lookup_var_type id)
  | MLletin _ | MLfix _ -> true
  | _ -> false

(** Pretty-print a MiniML expression as Go.
    [par]    – whether to wrap in parentheses when the result is a compound.
    [exp_ty] – expected result type; used to pick concrete IIFE return types
               and to insert type assertions when a variable is typed [any]
               but the context expects a concrete type. *)
let rec pp_go_expr env par ?(exp_ty : ml_type = Taxiom) ast =
  match ast with

  | MLrel n ->
    let id    = get_db_name n env in
    let id_pp = Id.print id in
    (* Insert a type assertion when ALL of:
       (a) [exp_ty] is concrete (not opaque) — we know the target Go type,
       (b) the variable is NOT in [go_custom_match_vars] — template variables
           (e.g. [%b1a0 := _su_ - 1]) carry their Go types from the template,
           not from [any] fields, so they must never be asserted, AND
       (c) the variable IS in [go_any_typed_vars] — it was explicitly tagged as
           [any] in Go because it came from an impl-field access, a function
           parameter typed [any], or a let-binding whose RHS produces [any].
       Using only [go_any_typed_vars] (not [is_opaque_ty var_ty]) avoids
       spurious assertions on let-bound variables whose ML type is erased to
       Taxiom but whose Go type is already concrete (e.g. [new_pos : position]
       from [move_pos(...)], or [row : uint] from a function parameter). *)
    ignore (lookup_var_type id);  (* var_ty no longer used in needs_assert *)
    let needs_assert =
      not (is_opaque_ty exp_ty)
      && not (Hashtbl.mem go_custom_match_vars id)
      && Hashtbl.mem go_any_typed_vars id
    in
    if needs_assert then
      str "(" ++ id_pp ++ str ").(" ++ pp_go_type exp_ty ++ str ")"
    else
      id_pp

  | MLapp (f0, args0) ->
    (* Flatten curried application tree so monad/inline-custom dispatch
       sees the complete argument list regardless of how many MLapp nodes
       Rocq's MiniML stacked up. *)
    let f, args = flatten_app f0 args0 in
    ( match f with

    (* Monad bind erasure: [bind x (fun y -> body)] → IIFE [{y := x; body}]. *)
    | MLglob (r, _) when Table.is_bind r ->
      let a_ml, f_ml = Common.last_two args in
      ( match f_ml with
      | MLlam (mid, bind_ty, body) ->
        let id       = id_of_mlident mid in
        let renamed, env' = push_vars [id] env in
        let id'      = List.hd renamed in
        register_var_type id' bind_ty;
        if is_rhs_any env a_ml then Hashtbl.replace go_any_typed_vars id' ();
        let pp_a    = pp_go_expr env  false a_ml in
        let pp_body = pp_go_expr env' false ~exp_ty body in
        let iife_ty = if is_opaque_ty exp_ty then str "any" else pp_go_type exp_ty in
        (* "_ :=" is invalid Go — use blank assignment "_ = expr" for Dummy. *)
        let bind_stmt =
          if mid = Dummy then str "\t_ = " ++ pp_a
          else str "\t" ++ Id.print id' ++ str " := " ++ pp_a
        in
        let iife =
          str "(func() " ++ iife_ty ++ str " {" ++ fnl ()
          ++ bind_stmt ++ fnl ()
          ++ str "\treturn " ++ pp_body ++ fnl ()
          ++ str "})()"
        in
        if par then str "(" ++ iife ++ str ")" else iife
      | _ ->
        (* f is not a lambda — apply directly *)
        let pp_f = pp_go_expr env false f_ml in
        let pp_a = pp_go_expr env false a_ml in
        let call = pp_f ++ str "(" ++ pp_a ++ str ")" in
        if par then str "(" ++ call ++ str ")" else call )

    (* Monad ret erasure: [Ret x] → [x]. *)
    | MLglob (r, _) when Table.is_ret r ->
      let x = List.hd (List.rev args) in
      pp_go_expr env par ~exp_ty x

    (* Inline-custom constant: apply the template to all value args.
       Look up the function's ML type to propagate expected argument types,
       enabling type assertions for any-typed variables (e.g. [(rel1).(float64)]
       when rel1 is any but the inline-custom function expects float64). *)
    | MLglob (r, _) when is_inline_custom r ->
      let templ   = find_custom r in
      let f_ml_ty = match Hashtbl.find_opt go_term_types r with
        | Some ty -> erase_tvars ty
        | None    -> Taxiom
      in
      let arg_tys, _ = collect_arrows f_ml_ty in
      let n_known    = List.length arg_tys in
      let pp_args    = List.mapi (fun i arg ->
        let arg_exp = if i < n_known then List.nth arg_tys i else Taxiom in
        pp_go_expr env false ~exp_ty:arg_exp arg
      ) args in
      let result  = apply_expr_template templ pp_args in
      if par then str "(" ++ result ++ str ")" else result

    (* General function application.
       We look up the ML function type (from [var_types] for lambda-bound
       names; from [go_term_types] for global terms) and use it to:
       (a) propagate expected argument types so [MLrel] inserts type
           assertions when an [any] variable is passed to a concrete param;
       (b) wrap the call result when the function returns [any] but the
           enclosing context expects a concrete type. *)
    | _ ->
      let pp_f    = pp_go_expr env true f in
      let f_ml_ty = match f with
        (* Lambda/let-bound variable: keep type vars (T1, T2) intact.
           [f : func(T1) T2] with [a : any] → propagates [exp_ty = Tvar 1]
           so [MLrel a] emits [(a).(T1)] which is valid in T1's scope. *)
        | MLrel n -> lookup_var_type (get_db_name n env)
        (* Global term: erase type vars to Taxiom so that we never emit
           [list[T1]] at a call site where T1 is not declared. *)
        | MLglob (r, _) ->
          ( match Hashtbl.find_opt go_term_types r with
          | Some ty -> erase_tvars ty
          | None    -> Taxiom )
        | _ -> Taxiom
      in
      let arg_tys, _ = collect_arrows f_ml_ty in
      let n_known = List.length arg_tys in
      let pp_args = List.mapi (fun i arg ->
        let arg_exp =
          if i < n_known then List.nth arg_tys i else Taxiom
        in
        pp_go_expr env false ~exp_ty:arg_exp arg
      ) args in
      let call = pp_f ++ str "(" ++ pp_comma_sep Fun.id pp_args ++ str ")" in
      (* Compute effective return type after applying all args *)
      let eff_ret = drop_arrows (List.length args) f_ml_ty in
      let result =
        if is_opaque_ty eff_ret && not (is_opaque_ty exp_ty) then
          str "(" ++ call ++ str ").(" ++ pp_go_type exp_ty ++ str ")"
        else call
      in
      if par then str "(" ++ result ++ str ")" else result )

  | MLlam _ -> pp_go_lam env par ast

  | MLletin (mlid, bind_ty, e, body) ->
    let id         = id_of_mlident mlid in
    let ids', env' = push_vars [id] env in
    let id'        = List.hd ids' in
    register_var_type id' bind_ty;
    (* Propagate [bind_ty] (after dereferencing Tmeta chains) as [exp_ty] for
       the RHS.  When [bind_ty_simpl] is concrete (e.g. [float64]), this causes
       [pp_go_custom_match] to wrap the template IIFE with a type assertion
       (e.g. [(func() any {...}()).(float64)]), making the bound variable
       concrete in Go rather than [any].
       Only tag the variable as Go-[any] when the simpled bind_ty is still
       opaque, meaning the RHS will genuinely produce an [any] value.
       If [bind_ty_simpl] is non-opaque, the binding-site assertion makes the
       variable concrete — tagging it in [go_any_typed_vars] would cause
       spurious double assertions at use sites. *)
    let bind_ty_simpl = Mlutil.type_simpl bind_ty in
    if is_rhs_any env e && is_opaque_ty bind_ty_simpl then
      Hashtbl.replace go_any_typed_vars id' ();
    let pp_e    = pp_go_expr env  false ~exp_ty:bind_ty_simpl e in
    let pp_body = pp_go_expr env' false ~exp_ty body in
    let iife_ty = if is_opaque_ty exp_ty then str "any" else pp_go_type exp_ty in
    (* "_ :=" is invalid Go — use blank assignment "_ = expr" for Dummy. *)
    let assign_stmt =
      if mlid = Dummy then str "\t_ = " ++ pp_e
      else str "\t" ++ Id.print id' ++ str " := " ++ pp_e
    in
    let iife =
      str "(func() " ++ iife_ty ++ str " {" ++ fnl ()
      ++ assign_stmt ++ fnl ()
      ++ str "\treturn " ++ pp_body ++ fnl ()
      ++ str "})()"
    in
    if par then str "(" ++ iife ++ str ")" else iife

  | MLglob (r, _tys) ->
    let s =
      if is_inline_custom r then find_custom r
      else pp_global Term r
    in
    str s

  | MLcons (ty, r, args)    -> pp_go_cons env par ty r args
  | MLcase (ty, scrut, brs) -> pp_go_case env par ty ~exp_ty scrut brs
  | MLfix (i, defs, bodies, _) -> pp_go_fix env par ~exp_ty i defs bodies

  | MLexn s ->
    str ("(func() any { panic(\"" ^ String.escaped s ^ "\") })()")

  | MLdummy _ -> str "nil"

  | MLaxiom s ->
    str ("(func() any { panic(\"axiom: " ^ String.escaped s ^ "\") })()")

  | MLmagic a -> pp_go_expr env par ~exp_ty a

  | MLuint n   -> str (Int64.to_string (Uint63.to_int64 n))
  | MLfloat f  -> str (Printf.sprintf "%h" (Float64.to_float f))
  | MLstring s -> str ("\"" ^ String.escaped (Pstring.to_string s) ^ "\"")

  | MLtuple args ->
    let n = List.length args in
    let ft = String.concat "; "
               (List.init n (fun i -> Printf.sprintf "_%d any" i)) in
    let pp_fields = List.mapi (fun i a ->
      str (Printf.sprintf "_%d: " i) ++ pp_go_expr env false a) args in
    str ("struct{" ^ ft ^ "}{")
    ++ pp_comma_sep Fun.id pp_fields
    ++ str "}"

  | MLparray (arr, _def) ->
    str "[]any{"
    ++ pp_comma_sep Fun.id
         (Array.to_list (Array.map (pp_go_expr env false) arr))
    ++ str "}"

(** Collect and emit a chain of MLlam as a single Go function literal. *)
and pp_go_lam env par ast =
  (* collect_lams returns (innermost-first list, body) *)
  let params_rev, body = collect_lams ast in
  (* Reverse for printing order (outermost first) *)
  let params = List.rev params_rev in
  (* push_vars in innermost-first order so de Bruijn indices work *)
  let ids_rev  = List.map (fun (mid, _) -> id_of_mlident mid) params_rev in
  let renamed_rev, env' = push_vars ids_rev env in
  (* renamed_rev is innermost-first; reverse for pairing with params *)
  let renamed  = List.rev renamed_rev in
  (* Register lambda parameter types for type-assertion decisions.
     Parameters whose Go type is [any] (printed as [any] because ML type is
     opaque) are tagged in [go_any_typed_vars] so that [MLrel] can insert
     type assertions when the parameter is used in a typed context. *)
  List.iter2 (fun id' (_, ty) ->
    register_var_type id' ty;
    if is_opaque_ty ty then Hashtbl.replace go_any_typed_vars id' ()
  ) renamed params;
  let pp_params =
    pp_comma_sep
      (fun (id', (_, ty)) -> Id.print id' ++ str " " ++ pp_go_type ty)
      (List.combine renamed params)
  in
  let pp_body = pp_go_expr env' false body in
  let fn =
    str "func(" ++ pp_params ++ str ") any {" ++ fnl ()
    ++ str "\treturn " ++ pp_body ++ fnl ()
    ++ str "}"
  in
  if par then str "(" ++ fn ++ str ")" else fn

(** Pretty-print a constructor call.
    [ty] is the ML type of the constructor result, used to fill [%t{n}]
    placeholders in the custom constructor template. *)
and pp_go_cons env par ty r args =
  let result =
    if is_inline_custom r then begin
      let pp_args   = List.map (pp_go_expr env false) args in
      let templ     = find_custom r in
      (* Always run apply_ctor_template: it handles both %t{n} (type) and
         %a{n} (arg) placeholders.  When type_args is empty there are no
         %t{n} to substitute and it degrades to apply_expr_template. *)
      let type_args = match ty with Tglob (_, tys, _) -> tys | _ -> [] in
      let raw = apply_ctor_template templ type_args pp_go_type pp_args in
      (* Wrap with the inductive's Go type when it is a numeric primitive
         so that nat constructor chains produce uint rather than int.
         Without this, Go infers `int` for untyped constant arithmetic like
         `(0 + 1 + 1 + ...)`, causing compile errors when those values are
         passed to functions expecting uint/int/float. *)
      let ind_go_type_opt =
        match r with
        | GlobRef.ConstructRef ((kn, i), _) ->
          let ind_ref = GlobRef.IndRef (kn, i) in
          ( match find_type_custom_opt ind_ref with
          | Some (_, t) -> Some t
          | None -> None )
        | _ -> None
      in
      let needs_cast = match ind_go_type_opt with
        | Some t ->
          let t = String.trim t in
          (* Only cast plain type names (no template args like %t0) that are
             numeric Go primitives.  Parameterised types and non-numeric types
             (any, bool, string) do not need a cast. *)
          not (String.contains t '%') &&
          t <> "any" && t <> "bool" && t <> "string" &&
          ( (String.length t >= 4 && String.sub t 0 4 = "uint")
          || (String.length t >= 3 && String.sub t 0 3 = "int")
          || (String.length t >= 5 && String.sub t 0 5 = "float") )
        | None -> false
      in
      if needs_cast then
        str (Option.get ind_go_type_opt) ++ str "(" ++ raw ++ str ")"
      else raw
    end else begin
      let name    = str (pp_global Cons r) in
      (* For record constructors, look up field types and propagate them as
         [exp_ty] so that [any]-typed arguments (e.g. from case-match IIFEs
         or function parameters) receive type assertions at the call site. *)
      let field_tys =
        match r with
        | GlobRef.ConstructRef ((kn, ii), _) ->
          let ind_ref = GlobRef.IndRef (kn, ii) in
          ( match Hashtbl.find_opt go_record_ind_fields ind_ref with
          | Some fields -> List.map snd fields
          | None -> [] )
        | _ -> []
      in
      let pp_args = List.mapi (fun i arg ->
        let exp =
          if i < List.length field_tys then List.nth field_tys i else Taxiom
        in
        pp_go_expr env false ~exp_ty:exp arg
      ) args in
      if pp_args = [] then
        (* Enum constructors are integer constants; zero-arg struct constructors
           are package-level vars.  Both are referenced by bare name. *)
        name
      else
        name ++ str "(" ++ pp_comma_sep Fun.id pp_args ++ str ")"
    end
  in
  if par then str "(" ++ result ++ str ")" else result

(** Pretty-print a pattern-match expression as a Go IIFE with switch.
    [ty]     – ML type of the scrutinee; used to box/assert when it is [any].
    [exp_ty] – expected return type of the whole case expression; used to
               give the IIFE a concrete return type instead of [any]. *)
and pp_go_case env par ty ?(exp_ty : ml_type = Taxiom) scrut branches =
  ignore ty;  (* ML scrutinee type is erased; we derive what we need from patterns *)
  if is_custom_match branches then
    pp_go_custom_match env par ~exp_ty scrut branches
  else begin
    let sv   = fresh_scrut () in
    let sv_s = Id.to_string sv in
    let pp_sc = pp_go_expr env false scrut in
    let iife_ty = if is_opaque_ty exp_ty then str "any" else pp_go_type exp_ty in
    (* Check if any branch pattern comes from a record inductive.
       Records use direct Go structs (no [_v] discriminant, no [*impl] pointer),
       so we generate direct field bindings instead of a switch statement. *)
    let get_record_fields () =
      Array.fold_left (fun acc (_, _, pat, _) ->
        match acc with
        | Some _ -> acc
        | None ->
          ( match pat with
          | Pusual (GlobRef.ConstructRef ((kn2, ii2), _))
          | Pcons  (GlobRef.ConstructRef ((kn2, ii2), _), _) ->
            let ind_ref2 = GlobRef.IndRef (kn2, ii2) in
            Hashtbl.find_opt go_record_ind_fields ind_ref2
          | _ -> None )
      ) None branches
    in
    match get_record_fields () with
    | Some field_info ->
      (* ---- record match: single constructor, direct field access ---- *)
      (* Use the first non-Pwild branch (records have one constructor). *)
      let rec first_ctor_branch i =
        if i >= Array.length branches then branches.(0)
        else match branches.(i) with
          | (_, _, Pwild, _) -> first_ctor_branch (i + 1)
          | br -> br
      in
      let (ids, _, _, body) = first_ctor_branch 0 in
      (* Keep original mlidents to detect Dummy (blank) variables.
         Dummy variables appear as "_" (renamed to "_0" etc.); they must not
         be emitted as assignments to avoid "declared and not used" errors. *)
      let ids_orig = List.map (fun (mid, _) -> mid) ids in
      let ids_typed = List.map (fun (mid, ty') -> (id_of_mlident mid, ty')) ids in
      let renamed_rev, env' = push_vars' (List.rev ids_typed) env in
      let renamed = List.rev renamed_rev in
      (* Register variables using the concrete field type from the record
         definition (not the potentially-erased MiniML ids type), so that
         [MLrel] does not insert spurious type assertions. *)
      List.iteri (fun k (id', _) ->
        let field_ty = match List.nth_opt field_info k with
          | Some (_, ty) -> ty | None -> Taxiom
        in
        register_var_type id' field_ty
      ) renamed;
      let pp_assigns = List.mapi (fun k (id', _) ->
        (* Skip blank-identifier variables (Dummy in MiniML). *)
        let orig_mid = List.nth ids_orig k in
        if orig_mid = Dummy then mt ()
        else
          let (fname, _) = match List.nth_opt field_info k with
            | Some fi -> fi | None -> ("_f" ^ string_of_int k, Taxiom)
          in
          str (Printf.sprintf "\t%s := %s.%s" (Id.to_string id') sv_s fname) ++ fnl ()
      ) renamed in
      let pp_body = pp_go_expr env' false ~exp_ty body in
      (* Compute the IIFE return type.  When [exp_ty] is concrete, use it.
         When it is opaque (e.g. the record match is used inside an inline
         custom template argument that passes no [exp_ty]), infer from the
         body variable's registered field type so that arithmetic operators
         and comparisons on the result compile without an explicit assertion. *)
      let effective_iife_ty =
        if not (is_opaque_ty exp_ty) then iife_ty
        else match body with
          | MLrel n ->
            let id = get_db_name n env' in
            let vty = lookup_var_type id in
            if is_opaque_ty vty then iife_ty else pp_go_type vty
          | _ -> iife_ty
      in
      (* If the scrutinee is [any]-typed in Go (e.g. bound from an impl-struct
         field like [_c1_d0 any]), accessing struct fields directly on it will
         fail at compile time.  Detect this by checking if the scrutinee MLrel
         is in [go_any_typed_vars], and if so, box through [any] and assert to
         the concrete record type before accessing fields. *)
      let record_type_name =
        Array.fold_left (fun acc (_, _, pat, _) ->
          match acc with | Some _ -> acc | None ->
            match pat with
            | Pusual (GlobRef.ConstructRef ((kn2, ii2), _))
            | Pcons  (GlobRef.ConstructRef ((kn2, ii2), _), _) ->
              let ind_ref2 = GlobRef.IndRef (kn2, ii2) in
              Some (pp_global_name Type ind_ref2)
            | _ -> None
        ) None branches
      in
      let scrut_is_any = match scrut with
        | MLrel n ->
          let sid = get_db_name n env in
          Hashtbl.mem go_any_typed_vars sid
        | _ -> false
      in
      let scrut_setup =
        if scrut_is_any then
          match record_type_name with
          | Some tn ->
            str "\tvar _rbox any = " ++ pp_sc ++ fnl ()
            ++ str ("\t" ^ sv_s ^ " := _rbox.(" ^ tn ^ ")") ++ fnl ()
          | None ->
            str ("\t" ^ sv_s ^ " := ") ++ pp_sc ++ fnl ()
        else
          str ("\t" ^ sv_s ^ " := ") ++ pp_sc ++ fnl ()
      in
      let result =
        str "(func() " ++ effective_iife_ty ++ str " {" ++ fnl ()
        ++ scrut_setup
        ++ prlist Fun.id pp_assigns
        ++ str "\treturn " ++ pp_body ++ fnl ()
        ++ str "})()"
      in
      if par then str "(" ++ result ++ str ")" else result

    | None ->
      (* ---- enum or standard tagged-struct match ---- *)
      (* If every branch has no bound variables the inductive is all-nullary
         (an enum: [type T int]).  Switch directly on the value; otherwise
         switch on the tagged-struct discriminant [._v]. *)
      let all_nullary =
        Array.for_all (fun (ids, _, _, _) -> ids = []) branches
      in
      let switch_expr = if all_nullary then sv_s else sv_s ^ "._v" in
      (* For non-enum structural matches, box the scrutinee through [any] and
         type-assert to the concrete (non-generic) impl pointer.  This is
         required when the scrutinee variable is typed [any] in Go because the
         ML type was erased to Taxiom.
         We recover the impl struct name from the branch patterns to avoid
         relying on [ty] (which may itself be Taxiom after ML erasure). *)
      let get_impl_from_branches () =
        Array.fold_left (fun acc (_, _, pat, _) ->
          match acc with
          | Some _ -> acc
          | None ->
            ( match pat with
            | Pusual (GlobRef.ConstructRef ((kn2, ii2), _))
            | Pcons  (GlobRef.ConstructRef ((kn2, ii2), _), _) ->
              let ind_ref2 = GlobRef.IndRef (kn2, ii2) in
              if is_custom ind_ref2 then None
              else
                let tname = pp_global_name Type ind_ref2 in
                Some (String.uncapitalize_ascii tname ^ "Impl")
            | _ -> None )
        ) None branches
      in
      let scrut_setup =
        if all_nullary then
          str ("\t" ^ sv_s ^ " := ") ++ pp_sc ++ fnl ()
        else
          match get_impl_from_branches () with
          | Some impl_name ->
            str "\tvar _box any = " ++ pp_sc ++ fnl ()
            ++ str ("\t" ^ sv_s ^ " := _box.(*" ^ impl_name ^ ")") ++ fnl ()
          | None ->
            (* Custom or unrecognised inductive: plain assignment.
               If the scrutinee is [any], accessing [._v] will fail at compile
               time; add a custom Extract Inductive directive to fix this. *)
            str ("\t" ^ sv_s ^ " := ") ++ pp_sc ++ fnl ()
      in
      let pp_brs =
        prlist_with_sep fnl
          (pp_go_branch env sv_s ~is_enum:all_nullary ~case_ty:exp_ty)
          (Array.to_list branches)
      in
      let result =
        str "(func() " ++ iife_ty ++ str " {" ++ fnl ()
        ++ scrut_setup
        ++ str ("\tswitch " ^ switch_expr ^ " {") ++ fnl ()
        ++ pp_brs ++ fnl ()
        ++ str "\t}" ++ fnl ()
        ++ str "\tpanic(\"unreachable\")" ++ fnl ()
        ++ str "})()"
      in
      if par then str "(" ++ result ++ str ")" else result
  end

(** Pretty-print one switch branch.
    [sv_s]    – Go identifier string for the scrutinee.
    [is_enum] – true when the inductive is all-nullary (type T int);
                in that case [case] uses the constructor name, not an int.
    [case_ty] – expected return type of the branch body, propagated from
                the enclosing [pp_go_case] so that type assertions are
                inserted where needed. *)
and pp_go_branch env sv_s ?(is_enum = false) ?(case_ty : ml_type = Taxiom) (ids, _, pat, body) =
  let ids_orig  = List.map fst ids in   (* original mlidents, to detect Dummy *)
  let ids_typed = List.map (fun (mid, ty) -> (id_of_mlident mid, ty)) ids in
  (* ids_typed is in constructor-arg order (first arg first).
     We must reverse before push_vars' so that de Bruijn indices work:
     MLrel 1 = last constructor arg, MLrel n = first. *)
  let renamed_rev, env' = push_vars' (List.rev ids_typed) env in
  (* reversed list → forward list for field-index correlation *)
  let renamed = List.rev renamed_rev in
  (* Register the ML types of the pattern-bound variables.
     These types are used by [MLrel] to decide whether to insert a type
     assertion when the variable is used in a typed context. *)
  List.iter (fun (id', ty) -> register_var_type id' ty) renamed;
  match pat with
  | Pwild ->
    str "\tdefault:" ++ fnl ()
    ++ pp_go_stmts env' ~indent:"\t\t" ~exp_ty:case_ty body

  | Pusual r | Pcons (r, _) ->
    let j = match r with
      | GlobRef.ConstructRef (_, k) -> k - 1
      | _ -> 0
    in
    (* For enum types, switch on the constructor name; for struct types on the
       integer discriminant. *)
    let case_label =
      if is_enum then
        let cname = match r with
          | GlobRef.ConstructRef _ ->
            if is_custom r then find_custom r
            else pp_global_name Cons r
          | _ -> string_of_int j
        in
        str ("\tcase " ^ cname ^ ":") ++ fnl ()
      else
        str (Printf.sprintf "\tcase %d:" j) ++ fnl ()
    in
    let pp_assigns =
      List.mapi (fun k (id', ty) ->
        (* Skip blank-identifier variables (Dummy in MiniML). *)
        let orig_mid = List.nth ids_orig k in
        if orig_mid = Dummy then mt ()
        else begin
          let field_access = Printf.sprintf "%s._c%d_d%d" sv_s j k in
          (* The impl struct fields are typed [any].
             If the variable's ML type is concrete (not opaque), add a type
             assertion at the assignment so Go infers the concrete type.
             If ML type is erased (opaque/Taxiom), the variable will be [any]
             in Go — register it in [go_any_typed_vars] so that [MLrel] can
             insert type assertions at use sites when the context demands it. *)
          let rhs =
            if is_opaque_ty ty then begin
              Hashtbl.replace go_any_typed_vars id' ();
              field_access
            end else
              Printf.sprintf "(%s).(%s)" field_access
                (string_of_ppcmds (pp_go_type ty))
          in
          str (Printf.sprintf "\t\t%s := %s" (Id.to_string id') rhs) ++ fnl ()
        end
      ) renamed
    in
    case_label
    ++ prlist Fun.id pp_assigns
    ++ pp_go_stmts env' ~indent:"\t\t" ~exp_ty:case_ty body

  | Ptuple _ | Prel _ ->
    (* Fallback for non-standard patterns *)
    str "\t/* unsupported pattern */" ++ fnl ()
    ++ str "\tdefault: return nil"

(** Apply a custom match template (from Extract Inductive ... match).
    [exp_ty] – expected return type, propagated to branch bodies. *)
and pp_go_custom_match env par ?(exp_ty : ml_type = Taxiom) scrut branches =
  let templ   = find_custom_match branches in
  let pp_sc   = pp_go_expr env false scrut in
  let sc_s    = string_of_ppcmds pp_sc in
  (* Pre-process each branch: rename vars, register types, render body.
     Variables bound in custom match templates get their Go type from the
     template expression (e.g. [%b1a0 := _su_ - 1] → uint), NOT from an
     [any] field.  Mark them in [go_custom_match_vars] so [MLrel] skips
     type assertions for them even if their ML type is opaque. *)
  let br_data = Array.to_list (Array.map (fun (ids, _, _, body) ->
    let ids_typed =
      List.map (fun (mid, ty) -> (id_of_mlident mid, ty)) ids
    in
    let renamed_rev, env' = push_vars' (List.rev ids_typed) env in
    let renamed = List.rev renamed_rev in
    List.iter (fun (id', ty) ->
      register_var_type id' ty;
      Hashtbl.replace go_custom_match_vars id' ()
    ) renamed;
    (renamed, pp_go_expr env' false ~exp_ty body)
  ) branches) in
  (* Parse the template, substituting %scrut, %br{n}, %b{n}a{m} *)
  let t   = templ in
  let len = String.length t in
  let buf = Buffer.create len in
  let i   = ref 0 in
  while !i < len do
    if !i + 6 <= len && String.sub t !i 6 = "%scrut" then begin
      Buffer.add_string buf sc_s; i := !i + 6
    end else if !i + 2 < len && t.[!i] = '%' && t.[!i+1] = 'b' then begin
      if !i + 3 < len && t.[!i+2] = 'r' then begin
        (* %br{n} → branch body *)
        let j = ref (!i + 3) in
        while !j < len && t.[!j] >= '0' && t.[!j] <= '9' do incr j done;
        let idx = if !j > !i + 3
                  then int_of_string (String.sub t (!i+3) (!j - !i - 3))
                  else 0 in
        Buffer.add_string buf
          (if idx < List.length br_data
           then string_of_ppcmds (snd (List.nth br_data idx))
           else "_br" ^ string_of_int idx);
        i := !j
      end else begin
        (* %b{n}a{m} → variable name in branch n at position m *)
        let j = ref (!i + 2) in
        while !j < len && t.[!j] >= '0' && t.[!j] <= '9' do incr j done;
        let br_idx = if !j > !i + 2
                     then int_of_string (String.sub t (!i+2) (!j - !i - 2))
                     else 0 in
        if !j < len && t.[!j] = 'a' then begin
          incr j;
          let k = ref !j in
          while !k < len && t.[!k] >= '0' && t.[!k] <= '9' do incr k done;
          let arg_idx = if !k > !j
                        then int_of_string (String.sub t !j (!k - !j))
                        else 0 in
          let var_s =
            if br_idx < List.length br_data then
              let renamed = fst (List.nth br_data br_idx) in
              if arg_idx < List.length renamed
              then Id.to_string (fst (List.nth renamed arg_idx))
              else "_b" ^ string_of_int br_idx ^ "a" ^ string_of_int arg_idx
            else "_b" ^ string_of_int br_idx ^ "a" ^ string_of_int arg_idx
          in
          Buffer.add_string buf var_s;
          i := !k
        end else begin
          Buffer.add_char buf t.[!i]; incr i
        end
      end
    end else if !i + 2 < len && t.[!i] = '%' && t.[!i+1] = 't' then begin
      (* %t{n} → type arg placeholder, just emit "any" *)
      let j = ref (!i + 2) in
      while !j < len && t.[!j] >= '0' && t.[!j] <= '9' do incr j done;
      Buffer.add_string buf "any"; i := !j
    end else begin
      Buffer.add_char buf t.[!i]; incr i
    end
  done;
  (* Custom match templates always generate [func() any { ... }()].
     When the caller expects a concrete type, wrap with a type assertion
     so the result can be returned directly without a further cast.
     Also fix any "_ :=" that arose from Dummy branch variables — Go
     requires blank assignments to use "_ =" not "_ :=". *)
  let contents =
    (* Fix "_ :=" and "_N :=" (N = 0, 1, ...) that arose from Dummy branch
       variables: Go requires blank assignments to use "_ =" not "_ :=".
       Match "_" or "_<digits>" at a word boundary (not preceded by an
       identifier character), followed by " :=".  Names like "_scrut0" are
       not matched because "scrut" is not all-digits.
       Examples fixed: "_ :=", "_0 :=", "_1 :=" → "_ =".
       Examples preserved: "_su_ :=", "_scrut0 :=". *)
    let s    = Buffer.contents buf in
    let slen = String.length s in
    let is_id_char c =
      (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
      || (c >= '0' && c <= '9') || c = '_'
    in
    let b = Buffer.create slen in
    let i = ref 0 in
    while !i < slen do
      let c = s.[!i] in
      if c = '_' && (!i = 0 || not (is_id_char s.[!i - 1])) then begin
        (* Scan over optional trailing digits to get the full blank name *)
        let j = ref (!i + 1) in
        while !j < slen && s.[!j] >= '0' && s.[!j] <= '9' do incr j done;
        (* Check that the next chars are " :=" (blank assignment) *)
        if !j + 3 <= slen && String.sub s !j 3 = " :=" then begin
          Buffer.add_string b "_ =";
          i := !j + 3
        end else begin
          Buffer.add_char b s.[!i]; incr i
        end
      end else begin
        Buffer.add_char b s.[!i]; incr i
      end
    done;
    Buffer.contents b
  in
  let raw = str contents in
  let result =
    if is_opaque_ty exp_ty then raw
    else str "(" ++ raw ++ str ").(" ++ pp_go_type exp_ty ++ str ")"
  in
  if par then str "(" ++ result ++ str ")" else result

(** Pretty-print a fixpoint group as an IIFE containing local funcs.
    [exp_ty] is accepted for API uniformity but not yet used to type the
    inner function variables (they remain [func() any]). *)
and pp_go_fix env par ?(exp_ty : ml_type = Taxiom) i defs bodies =
  ignore exp_ty;
  let n      = Array.length defs in
  let names  = Array.to_list (Array.map fst defs) in
  let names', env' = push_vars names env in
  let pp_funcs = List.mapi (fun j name' ->
    let body    = bodies.(j) in
    let pp_body = pp_go_expr env' false body in
    str "\tvar " ++ Id.print name' ++ str " func() any" ++ fnl ()
    ++ str "\t" ++ Id.print name'
    ++ str " = func() any { return " ++ pp_body ++ str " }" ++ fnl ()
  ) names' in
  ignore n; (* all functions declared; only call the i-th *)
  let result =
    str "(func() any {" ++ fnl ()
    ++ prlist Fun.id pp_funcs
    ++ str "\treturn " ++ Id.print (List.nth names' i) ++ str "()" ++ fnl ()
    ++ str "})()"
  in
  if par then str "(" ++ result ++ str ")" else result

(** Emit an expression as a flat sequence of Go statements at the given
    [indent] prefix (e.g. ["\t"] for function bodies, ["\t\t"] for case
    branches).

    Consecutive [MLletin] bindings and monad-bind applications are unwound
    into plain assignment statements; the final expression becomes a
    [return] statement.  All other nodes fall through to [pp_go_expr].

    This replaces the nested-IIFE pattern that causes the Go compiler to OOM
    on deeply-chained bindings like [process_frame] (21+ levels of nesting).

    All per-binding state ([go_any_typed_vars], [var_types]) is updated
    exactly as in the [MLletin] / bind-erasure branches of [pp_go_expr]. *)
and pp_go_stmts env ~indent ~(exp_ty : ml_type) ast =
  match ast with
  (* Plain let-binding: emit [id := rhs] and recurse. *)
  | MLletin (mlid, bind_ty, e, body) ->
    let id          = id_of_mlident mlid in
    let ids', env'  = push_vars [id] env in
    let id'         = List.hd ids' in
    register_var_type id' bind_ty;
    let bind_ty_simpl = Mlutil.type_simpl bind_ty in
    if is_rhs_any env e && is_opaque_ty bind_ty_simpl then
      Hashtbl.replace go_any_typed_vars id' ();
    let pp_e = pp_go_expr env false ~exp_ty:bind_ty_simpl e in
    let assign_stmt =
      if mlid = Dummy then str (indent ^ "_ = ") ++ pp_e
      else str indent ++ Id.print id' ++ str " := " ++ pp_e
    in
    assign_stmt ++ fnl () ++ pp_go_stmts env' ~indent ~exp_ty body
  (* Monad-bind application [bind a (fun y -> body)]: emit [y := a] and
     recurse, flattening the continuation into the same statement block. *)
  | MLapp (f0, args0) ->
    let f, args = flatten_app f0 args0 in
    ( match f with
    | MLglob (r, _) when Table.is_bind r ->
      let a_ml, f_ml = Common.last_two args in
      ( match f_ml with
      | MLlam (mid, bind_ty, body) ->
        let id       = id_of_mlident mid in
        let renamed, env' = push_vars [id] env in
        let id'      = List.hd renamed in
        register_var_type id' bind_ty;
        if is_rhs_any env a_ml then Hashtbl.replace go_any_typed_vars id' ();
        let pp_a = pp_go_expr env false a_ml in
        let assign_stmt =
          if mid = Dummy then str (indent ^ "_ = ") ++ pp_a
          else str indent ++ Id.print id' ++ str " := " ++ pp_a
        in
        assign_stmt ++ fnl () ++ pp_go_stmts env' ~indent ~exp_ty body
      | _ ->
        (* Continuation is not a lambda — cannot flatten; emit as return. *)
        str (indent ^ "return ") ++ pp_go_expr env false ~exp_ty ast )
    | _ ->
      str (indent ^ "return ") ++ pp_go_expr env false ~exp_ty ast )
  (* Everything else: emit as the final [return] expression. *)
  | _ ->
    str (indent ^ "return ") ++ pp_go_expr env false ~exp_ty ast

(* ===================================================================
   Inductive-type printing
   =================================================================== *)

(** True when every constructor of every packet is nullary. *)
let is_go_enum ind =
  Array.for_all
    (fun ip -> Array.for_all (fun tys -> tys = []) ip.ip_types)
    ind.ind_packets

(** Render a single inductive packet (standard/coinductive). *)
let pp_go_ind_packet kn ind_idx ind ip =
  let type_name  = Id.to_string ip.ip_typename in
  let type_lc    = String.uncapitalize_ascii type_name in
  let impl_name  = type_lc ^ "Impl" in
  let tparams    = ip.ip_vars in
  let pp_tparams = pp_go_tparams tparams in
  ignore (pp_go_targs tparams);  (* pp_targs unused after type-erasure refactor *)
  let ind_ref    = GlobRef.IndRef (kn, ind_idx) in
  if is_custom ind_ref then mt ()
  else if is_go_enum ind then begin
    (* ---- enum: type T int + const iota block ---- *)
    str "type " ++ str type_name ++ str " int" ++ fnl ()
    ++ str "const (" ++ fnl ()
    ++ Array.fold_left (++) (mt ()) (Array.mapi (fun j cname ->
         let cr    = GlobRef.ConstructRef ((kn, ind_idx), j + 1) in
         (* Register so that zero-arg uses emit the bare constant name,
            not a function call. *)
         register_enum_ctor cr;
         let cname_s =
           if is_custom cr then find_custom cr else Id.to_string cname
         in
         str "\t" ++ str cname_s
         ++ (if j = 0 then str (" " ^ type_name ^ " = iota") else mt ())
         ++ fnl ()
       ) ip.ip_consnames)
    ++ str ")" ++ fnl2 ()
  end else begin
    (* ---- tagged struct (type-erased) ----
       The impl struct is NOT generic: all constructor fields are typed [any].
       This avoids type-parameter inference failures at call sites when the
       struct is produced or consumed through an [any]-typed variable.
       The public alias remains generic so call sites can write list[cell] etc.,
       but all instantiations share the same underlying ptr-to-impl type.
       Scrutinee boxing in pp_go_case uses _box.( star-impl) without
       needing to know the type argument. *)

    (* 1. Impl struct: non-generic, all fields typed [any] *)
    let field_lines =
      Array.mapi (fun j ctypes ->
        List.mapi (fun k _ ->
          str (Printf.sprintf "\t_c%d_d%d any" j k) ++ fnl ()
        ) ctypes
      ) ip.ip_types
      |> Array.to_list
      |> List.flatten
    in
    let pp_impl =
      str "type " ++ str impl_name
      ++ str " struct {" ++ fnl ()
      ++ str "\t_v int" ++ fnl ()
      ++ prlist Fun.id field_lines
      ++ str "}" ++ fnl2 ()
    in
    (* 2. Public pointer alias: type list[T1 any] = *listImpl (non-parameterised impl) *)
    let pp_alias =
      str "type " ++ str type_name ++ pp_tparams
      ++ str " = *" ++ str impl_name ++ fnl2 ()
    in
    (* 3. Constructors.
         Zero-arg ctors → Go vars   (no type parameters needed; value is ready-made)
         Non-zero-arg   → Go funcs  (keep original ML param types for call-site inference;
                                     store into [any] fields; return [*impl_name]) *)
    let pp_ctors =
      Array.fold_left (++) (mt ()) (Array.mapi (fun j cname ->
        let cr      = GlobRef.ConstructRef ((kn, ind_idx), j + 1) in
        let ctypes  = ip.ip_types.(j) in
        if is_inline_custom cr then mt ()
        else begin
          let cname_s =
            if is_custom cr then find_custom cr else pp_global_name Cons cr
          in
          ignore cname;  (* silence unused-variable warning *)
          let n_params   = List.length ctypes in
          let init_v     = "_v: " ^ string_of_int j in
          if n_params = 0 then begin
            (* Zero-arg constructor → package-level var *)
            let init_s = "{" ^ init_v ^ "}" in
            str "var " ++ str cname_s
            ++ str (" *" ^ impl_name ^ " = &" ^ impl_name ^ init_s) ++ fnl2 ()
          end else begin
            let param_names = List.init n_params (fun k -> "a" ^ string_of_int k) in
            (* All constructor parameters are typed [any].
               The impl struct stores everything as [any] anyway, and the
               Go type system cannot infer type parameters when branches
               extract values as [any].  Using [any] parameters avoids
               both phantom-type issues and "cannot use X as T1" errors. *)
            let pp_params =
              pp_comma_sep
                (fun pn -> str pn ++ str " any")
                param_names
            in
            let ret_ty = str ("*" ^ impl_name) in
            let init_fs  = List.mapi (fun k pn ->
              Printf.sprintf "_c%d_d%d: %s" j k pn) param_names in
            let init_s   = String.concat ", " (init_v :: init_fs) in
            str "func " ++ str cname_s
            ++ str "(" ++ pp_params ++ str ") " ++ ret_ty ++ str " {" ++ fnl ()
            ++ str ("\treturn &" ^ impl_name)
            ++ str ("{" ^ init_s ^ "}") ++ fnl ()
            ++ str "}" ++ fnl2 ()
          end
        end
      ) ip.ip_consnames)
    in
    pp_impl ++ pp_alias ++ pp_ctors
  end

(** Render a record packet as a plain Go struct. *)
let pp_go_record_packet kn ind_idx ip =
  let type_name  = Id.to_string ip.ip_typename in
  let tparams    = ip.ip_vars in
  let pp_tparams = pp_go_tparams tparams in
  let ind_ref    = GlobRef.IndRef (kn, ind_idx) in
  if is_custom ind_ref then mt ()
  else begin
    let ctypes = if Array.length ip.ip_types > 0
                 then ip.ip_types.(0)
                 else [] in
    let fnames = if Array.length ip.ip_consarg_names > 0
                 then ip.ip_consarg_names.(0)
                 else [] in
    (* Register this inductive as a record with field names AND types so that
       [pp_go_case] can (a) generate direct field access instead of impl boxing,
       and (b) register branch variables with concrete field types rather than
       erased Taxiom types from the MiniML branch ids. *)
    let field_info = List.mapi (fun k ty ->
      let fn = match List.nth_opt fnames k with
        | Some (Some id) -> Id.to_string id
        | _              -> "_f" ^ string_of_int k
      in
      (fn, ty)
    ) ctypes in
    Hashtbl.replace go_record_ind_fields ind_ref field_info;
    let field_lines = List.mapi (fun k ty ->
      let fn =
        match List.nth_opt fnames k with
        | Some (Some id) -> Id.to_string id
        | _              -> "_f" ^ string_of_int k
      in
      str ("\t" ^ fn ^ " ") ++ pp_go_type ty ++ fnl ()
    ) ctypes in
    let pp_struct =
      str "type " ++ str type_name ++ pp_tparams
      ++ str " struct {" ++ fnl ()
      ++ prlist Fun.id field_lines
      ++ str "}" ++ fnl2 ()
    in
    (* Generate a constructor function matching the record name.
       e.g. [mkPos(prow uint, pcol uint) position { return position{prow:prow,...} }] *)
    let pp_ctor =
      if Array.length ip.ip_consnames = 0 then mt ()
      else begin
        let cr       = GlobRef.ConstructRef ((kn, ind_idx), 1) in
        if is_inline_custom cr || is_custom cr then mt ()
        else begin
          let ctor_s   = pp_global_name Cons cr in
          let n_fields = List.length ctypes in
          let param_names = List.init n_fields (fun k ->
            match List.nth_opt fnames k with
            | Some (Some id) -> Id.to_string id
            | _              -> "_f" ^ string_of_int k)
          in
          let pp_params =
            if n_fields = 0 then mt ()
            else pp_comma_sep
              (fun (pn, ty) -> str pn ++ str " " ++ pp_go_type ty)
              (List.combine param_names ctypes)
          in
          let init_s = String.concat ", "
            (List.mapi (fun k pn ->
              let fn = match List.nth_opt fnames k with
                | Some (Some id) -> Id.to_string id
                | _              -> "_f" ^ string_of_int k
              in Printf.sprintf "%s: %s" fn pn)
            param_names)
          in
          str "func " ++ str ctor_s ++ pp_tparams
          ++ str "(" ++ pp_params ++ str ") " ++ str type_name ++ pp_tparams
          ++ str " {" ++ fnl ()
          ++ str ("\treturn " ^ type_name) ++ pp_tparams
          ++ str ("{" ^ init_s ^ "}") ++ fnl ()
          ++ str "}" ++ fnl2 ()
        end
      end
    in
    pp_struct ++ pp_ctor
  end

(** Dispatch inductive rendering by kind. *)
let pp_go_ind kn ind =
  match ind.ind_kind with
  | Record _ | TypeClass _ ->
    Array.fold_left (++) (mt ())
      (Array.mapi (fun i ip -> pp_go_record_packet kn i ip) ind.ind_packets)
  | Standard | Coinductive ->
    Array.fold_left (++) (mt ())
      (Array.mapi
         (fun i ip -> pp_go_ind_packet kn i ind ip)
         ind.ind_packets)

(* ===================================================================
   Declaration printing
   =================================================================== *)

let pp_go_dtype r ids ty =
  if is_custom r then mt ()
  else
    str "type " ++ str (pp_global_name Type r)
    ++ pp_go_tparams ids ++ str " = " ++ pp_go_type ty ++ fnl2 ()

let pp_go_dterm r body ty =
  if is_inline_custom r then begin
    (* Register inline-custom constants so that MLapp can propagate their
       expected argument types to any-typed variables, enabling type
       assertions (e.g. [rel1.(float64)] when rel1 is any but Rlt_dec
       expects float64). *)
    Hashtbl.replace go_term_types r ty;
    mt ()
  end
  else if is_custom r then
    str "var " ++ str (pp_global_name Term r)
    ++ str " = " ++ str (find_custom r) ++ fnl2 ()
  else begin
    (* Register the ML type of this global so that [MLapp] call sites can
       look it up to propagate expected argument types (enabling type
       assertions for [any]-typed variables passed to concrete params). *)
    Hashtbl.replace go_term_types r ty;
    (* Clear per-function variable state to avoid cross-function pollution.
       Variable names are reused across functions; stale [go_any_typed_vars]
       entries from a previous function (e.g. [row] from a list branch) would
       cause spurious type assertions for same-named parameters in later
       functions (e.g. [row uint] in [get_cell]).
       [go_term_types] and [go_record_ind_fields] are intentionally preserved —
       they accumulate global information used at call sites. *)
    Hashtbl.clear var_types;
    Hashtbl.clear go_any_typed_vars;
    Hashtbl.clear go_custom_match_vars;
    let env          = empty_env () in
    let name         = pp_global_name Term r in
    (* collect_lams returns (innermost-first, body) *)
    let params_rev, inner_body = collect_lams body in
    let params       = List.rev params_rev in
    let n_tvars      = count_tvars ty in
    let pp_tparams   = pp_go_type_params n_tvars in
    if params = [] then begin
      (* Check for eta-reduced definitions: the extractor may have
         simplified [fun a b => f a b] to [f] even though [ty] is still
         an arrow type.  When that happens [collect_lams] returns no
         params, but we must still emit a [func] so that call sites work. *)
      let eta_param_tys, eta_ret_ty = collect_arrows ty in
      if eta_param_tys = [] then
        (* Include an explicit type annotation so that untyped integer
           arithmetic (e.g. Peano chains) is not inferred as [int] when
           the expected Go type is [uint] or another concrete type.
           Pass [exp_ty] so that any IIFE generated inside the body uses the
           correct return type rather than [any]. *)
        let go_ty = pp_go_type ty in
        str "var " ++ str name ++ str " " ++ go_ty ++ str " = "
        ++ pp_go_expr env false ~exp_ty:ty inner_body ++ fnl2 ()
      else begin
        (* Synthesise parameter names from the arrow type. *)
        let n       = List.length eta_param_tys in
        let pnames  = List.init n (fun i -> Id.of_string ("a" ^ string_of_int i)) in
        let renamed, env' = push_vars pnames env in
        let pp_params =
          pp_comma_sep
            (fun (id', ty') -> Id.print id' ++ str " " ++ pp_go_type ty')
            (List.combine renamed eta_param_tys)
        in
        let pp_ret  = pp_go_type eta_ret_ty in
        (* For inline-custom bodies, apply the template directly to the
           synthesised param names instead of calling the name-less value. *)
        let pp_body =
          match inner_body with
          | MLglob (r', _) when is_inline_custom r' ->
            apply_expr_template (find_custom r')
              (List.map Id.print renamed)
          | _ ->
            (* General: call the first-class function value with the args. *)
            pp_go_expr env false inner_body ++ str "("
            ++ pp_comma_sep Id.print renamed ++ str ")"
        in
        str "func " ++ str name ++ pp_tparams
        ++ str "(" ++ pp_params ++ str ") " ++ pp_ret ++ str " {" ++ fnl ()
        ++ str "\treturn " ++ pp_body ++ fnl ()
        ++ str "}" ++ fnl2 ()
      end
    end
    else begin
      let ids_rev      = List.map (fun (mid, _) -> id_of_mlident mid) params_rev in
      let renamed_rev, env' = push_vars ids_rev env in
      let renamed      = List.rev renamed_rev in
      let param_tys    = List.map snd params in
      (* Register types so that inner [MLrel] nodes can insert assertions.
         Parameters whose ML type is opaque (Taxiom / Tunknown → printed as
         [any] in Go) are also tagged in [go_any_typed_vars] so that MLrel
         inserts type assertions when they are used in a typed context. *)
      List.iter2 register_var_type renamed param_tys;
      List.iter2 (fun id' ty' ->
        if is_opaque_ty ty' then Hashtbl.replace go_any_typed_vars id' ()
      ) renamed param_tys;
      let pp_params =
        pp_comma_sep
          (fun (id', ty') -> Id.print id' ++ str " " ++ pp_go_type ty')
          (List.combine renamed param_tys)
      in
      let (_, ret_ty) = collect_arrows ty in
      (* Emit only the type parameters that actually appear in parameter types.
         Type variables that appear only in the return type are "phantom":
         the Go compiler cannot infer them at call sites when all params are
         typed [any].  Replace phantom Tvars with [any] in the return type
         so the function can be called without explicit type arguments. *)
      let n_tvars_from_params =
        List.fold_left (fun acc t -> max acc (count_tvars t)) 0 param_tys in
      let effective_pp_tparams = pp_go_type_params n_tvars_from_params in
      let masked_ret_ty        = mask_phantom_tvars n_tvars_from_params ret_ty in
      let pp_body = pp_go_stmts env' ~indent:"\t" ~exp_ty:masked_ret_ty inner_body in
      str "func " ++ str name ++ effective_pp_tparams
      ++ str "(" ++ pp_params ++ str ") " ++ pp_go_type masked_ret_ty ++ str " {" ++ fnl ()
      ++ pp_body ++ fnl ()
      ++ str "}" ++ fnl2 ()
    end
  end

(** Render a mutual-fixpoint group as independent top-level functions.
    Register ALL types upfront so that mutually-recursive call sites can
    look up the type of a peer even before its body is generated. *)
let pp_go_dfix rv bodies tys =
  Array.iteri (fun i r ->
    if not (is_inline_custom r) && not (is_custom r) then
      Hashtbl.replace go_term_types r tys.(i)
  ) rv;
  Array.fold_left (++) (mt ()) (Array.init (Array.length rv) (fun i ->
    if is_inline_custom rv.(i) then mt ()
    else pp_go_dterm rv.(i) bodies.(i) tys.(i)
  ))

(** Dispatch for ml_decl. *)
let pp_go_decl = function
  | Dind (kn, ind)          -> pp_go_ind kn ind
  | Dtype (r, ids, ty)      -> pp_go_dtype r ids ty
  | Dterm (r, body, ty)     -> pp_go_dterm r body ty
  | Dfix (rv, bodies, tys)  -> pp_go_dfix rv bodies tys

(* ===================================================================
   Structure traversal
   =================================================================== *)

let rec pp_go_struct_elem = function
  | SEdecl d -> pp_go_decl d
  | SEmodule m ->
    ( match m.ml_mod_expr with
    | MEstruct (mp, struc) ->
      push_visible mp [];
      let pp = pp_go_module_struc struc in
      pop_visible ();
      pp
    | _ -> mt () )
  | SEmodtype _ -> mt ()

and pp_go_module_struc struc =
  prlist (fun (_, e) -> pp_go_struct_elem e) struc

(** True if [needle] appears anywhere in [haystack]. *)
let string_contains haystack needle =
  let hlen = String.length haystack
  and nlen = String.length needle in
  if nlen = 0 then true
  else if hlen < nlen then false
  else begin
    let found = ref false and i = ref 0 in
    while !i <= hlen - nlen && not !found do
      if String.sub haystack !i nlen = needle then found := true;
      incr i
    done;
    !found
  end

(** Entry point: render a full ml_structure.
    Performs a two-pass scan to detect [math.] usage and prepend the import. *)
let pp_go_struct mlstruct =
  reset_scrut_counter ();
  (* First pass: generate all declarations (side effects populate go_enum_ctor_set etc.) *)
  let body_pp =
    prlist
      (fun (mp, struc) ->
        push_visible mp [];
        let pp = pp_go_module_struc struc in
        pop_visible ();
        pp)
      mlstruct
  in
  (* Second pass: scan rendered output for package references *)
  let body_s = string_of_ppcmds body_pp in
  let imports =
    if string_contains body_s "math." then
      str "import \"math\"" ++ fnl2 ()
    else mt ()
  in
  imports ++ str body_s

(** No separate header file for Go. *)
let pp_go_hstruct _mlstruct = mt ()

(* ===================================================================
   Preamble
   =================================================================== *)

(** Generate the [package <name>] declaration. *)
let pp_go_preamble basename _comment _mps _usf =
  let override = Table.go_package_name () in
  let name =
    if override = "" then String.lowercase_ascii (Id.to_string basename)
    else override
  in
  str ("package " ^ name)
  ++ fnl2 ()

let pp_go_sig _mls = mt ()

let pp_go_sig_preamble _ _ _ _ = mt ()
