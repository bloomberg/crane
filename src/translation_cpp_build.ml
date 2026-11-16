(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Small CppIR fragments lowering assembles without converting a type: a
    lambda with template parameters of its own, the type of a
    never-returning expression, an IIFE inlined into a statement
    continuation, an inline custom's block template, the guard comparison
    around a body, and a numeral literal checked against its C++ range. *)

open Names
open Util
open Translation_state
open Type_util

(** What a branch throws when the scrutinee's indices rule it out.

    Two places recognise such a branch -- the coercion seam, where extraction
    records a [unit] flowing into a type no value of [unit] can become, and the
    sweep over a finished body, where a [return tt] contradicts the declared
    return type -- and a reader of the generated code should not have to tell
    them apart. *)
let dead_branch_message = "unreachable: impossible dependent match branch"

(** [mk_lambda ?tparams params ret body ~capture] is {!Cpp_ir.Build.lambda}
    with template parameters of its own, [tparams], less those none of its
    [params] (source order) deduces ({!Head_relaxation.settle_lowered_lambda}). *)
let mk_lambda ?(tparams = []) params (ret : Cpp_ir.Lowered.Type.t option) body ~capture : Cpp_ir.Lowered.Expr.t =
  match tparams with
  | [] -> Cpp_ir.Build.lambda params ret body ~capture
  | _ ->
    let l : Cpp_ir.Lowered.phase Cpp_ir.Expr.Lambda.t =
      Head_relaxation.settle_lowered_lambda
        { params;
          type_params = tparams;
          return_type = (match ret with Some (Const t) -> Some t | r -> r);
          body;
          capture;
          moved = [];
          binders = [];
          fixpoint = None }
    in
    ( match (params, body) with
    | [], [Throw msg] -> Abort (msg, Option.default (Any : Cpp_ir.Lowered.Type.t) l.return_type)
    | _ -> Lambda l )

(** The type a never-returning expression is spelled with, given whatever type
    the slot it sits in called for, held in CppIR.  {!Tany} is what an erased slot asks for,
    and the only thing left to say when the slot named no type; nothing here
    guesses past that. *)
let abort_ty : Cpp_ir.Lowered.Type.t option -> Cpp_ir.Lowered.Type.t = function
  | Some ty -> ty
  | None -> Any

(** [body] under the [Crane Guard Compare] of [n], if it has one: where its
    first two arguments of one type are the same value, the guard's
    constructor at once, [body] otherwise.  The rest of the body is the
    guard's [else], not a statement after it, so a loop transformation that
    turns the [return] into an assignment still skips it.  The same value is
    the same word for a shared variant -- one block, or one constructor with
    no fields -- and the same object otherwise. *)
let guard_compare n (ids : (Id.t * Cpp_ir.Lowered.Type.t) list) (body : Cpp_ir.Lowered.Stmt.t list) :
    Cpp_ir.Lowered.Stmt.t list =
  match Table.find_guard_compare n with
  | None -> body
  | Some ctor_ref ->
    let strip_wrappers t =
      let rec go : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
        | Reference (_, t) | Const t | In_namespace (_, t) -> go t
        | t -> t
      in
      go t
    in
    let rec find_pair = function
      | (id1, ty1) :: rest ->
        let base1 = strip_wrappers ty1 in
        ( match
            List.find_opt
              (fun (_, ty2) -> cpp_ty_eq base1 (strip_wrappers ty2))
              rest
          with
        | Some (id2, _) -> Some (id1, id2)
        | None -> find_pair rest )
      | [] -> None
    in
    ( match find_pair ids with
    | Some (p1, p2) ->
      let ctor_expr : Cpp_ir.Lowered.Expr.t =
        match ctor_ref with
        | _ when Table.is_custom ctor_ref -> mk_cppglob ctor_ref []
        | GlobRef.ConstructRef ((kn, i), cidx)
          when Table.is_enum_inductive (GlobRef.IndRef (kn, i)) ->
          let ctor_name = Id.of_string (Common.enum_ctor_name_of_ref kn i cidx) in
          Enum_value (GlobRef.IndRef (kn, i), ctor_name)
        | GlobRef.ConstructRef ((kn, i), _cidx) ->
          let ind = GlobRef.IndRef (kn, i) in
          let fname = Translation_naming.factory_name_of_ctor ctor_ref in
          let p1_ty = strip_wrappers (snd (List.find (fun (i, _) -> i = p1) ids)) in
          Cpp_ir.Build.call
            (Type_member (Entity_application (ind, [p1_ty], []), Id.of_string fname))
            []
        | _ -> mk_cppglob ctor_ref []
      in
      let same : Cpp_ir.Lowered.Expr.t =
        match strip_wrappers (snd (List.find (fun (i, _) -> i = p1) ids)) with
        | Entity_application (r, _, _) when Table.is_shared_variant r ->
          let v x = Cpp_ir.Build.call (Access (Dot, Local x, Id.of_string "v")) [] in
          Access_call (Dot, v p1, Id.of_string "same_as", [v p2])
        | _ -> Binary (Equal, Unary (Address_of, Local p1), Unary (Address_of, Local p2))
      in
      [If {condition = same; then_ = [Return (Some ctor_expr)]; else_ = body}]
    | None -> body )

(** When [expr] is a single-argument IIFE
    [Call(_, Lambda
      { params = [(ty, Some id)];
        return_type = Some ret;
        body;
        capture = Runs_in_place }, [arg])], lift the
    lambda body into assignment statements targeting [target_var]:
    {[
      Type target_var{};
      const auto& param = arg;
      <body with "return X;" rewritten to "target_var = X;">
    ]}
    Returns [Some stmts] on success, [None] if [expr] is not a liftable IIFE.
    [target_ty] is [None] where the declaration has no type of its own to
    impose, and the lambda's return type is used instead. *)
let lift_iife_assignment target_var (target_ty : Cpp_ir.Lowered.Type.t option) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Stmt.t list option =
  match expr with
  | Call
      ( _,
        Lambda
          { params = [(param_ty, Some param_id)];
            return_type = Some ret_ty;
            body;
            capture = Runs_in_place;
            _ },
        [arg] ) ->
    let actual_ty = match target_ty with Some t -> t | None -> ret_ty in
    let lifted_body =
      List.map
        (fun (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t ->
          match s with
          | Return (Some e) -> Bind_variable (target_var, Existing, e)
          | s -> s )
        body
    in
    Some
      (Declare_value_initialized (target_var, actual_ty)
      :: Bind_variable (param_id, Declare (param_ty, None), arg)
      :: lifted_body )
  | _ -> None

(** [inline_iife k expr] checks whether [expr] is an IIFE
    ([Call(_, Lambda
      { params = \[\];
        body;
        _ }, \[\])]).  If so, it replaces
    the final [Return(Some v)] in [body] with [k v] and returns the
    inlined statement list.  Otherwise it falls back to [\[k expr\]].

    Only zero-argument, zero-parameter IIFEs are inlined — parameterised
    lambdas and those with explicit return-type annotations involving
    captures are left untouched, since they may have name-scoping or
    type-deduction side-effects.

    @param k     the statement-level continuation (e.g. [Sreturn], [Sasgn])
    @param expr  the expression produced by [gen_expr] *)
let inline_iife (k : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) (e : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Stmt.t list =
  match e with
  | Call (_, Lambda {params = []; return_type = ret_ty; body; _}, []) when body <> [] ->
    let k_is_return =
      match k (Literal (Int 0)) with Return _ -> true | _ -> false
    in
    if not k_is_return then
      [k (Cpp_ir.Build.iife ret_ty body)]
    else
    let map_all_or_none transform branches =
      let results = List.map transform branches in
      if List.for_all (fun x -> x <> None) results then
        Some (List.filter_map Fun.id results)
      else None
    in
    let rec replace_last_return : Cpp_ir.Lowered.Stmt.t list -> Cpp_ir.Lowered.Stmt.t list option = function
      | [Return (Some v)] -> Some [k v]
      | [Return None] -> None
      | [Throw _] as stmts -> Some stmts
      | [If i] ->
        ( match (replace_last_return i.then_, replace_last_return i.else_) with
        | Some then_br', Some else_br' -> Some [If {condition = i.condition; then_ = then_br'; else_ = else_br'}]
        | _ -> None )
      | [Switch w] ->
        let default' =
          match w.default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun (id, stmts) ->
              Option.map (fun stmts' -> (id, stmts')) (replace_last_return stmts))
            w.branches, default')
        with
        | Some branches', Some default' -> Some [Switch {w with branches = branches'; default = default'}]
        | _ -> None )
      | [Custom_match m] ->
        Option.map
          (fun branches' -> [(Custom_match {m with branches = branches'} : Cpp_ir.Lowered.Stmt.t)])
          (map_all_or_none
            (fun (b : Cpp_ir.Lowered.phase Cpp_ir.Stmt.Custom_match.branch) ->
              Option.map (fun stmts' -> {b with body = stmts'}) (replace_last_return b.body))
            m.branches)
      | [Match (scrut, branches, default)] ->
        let default' =
          match default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun (br : Cpp_ir.Lowered.phase Cpp_ir.Stmt.Match.branch) ->
              Option.map (fun body' -> { br with body = body' }) (replace_last_return br.body))
            branches, default')
        with
        | Some branches', Some default' ->
          Some [Match (scrut, branches', default')]
        | _ -> None )
      | stmt :: rest when rest <> [] ->
        Option.map (fun rest' -> stmt :: rest') (replace_last_return rest)
      | _ -> None
    in
    ( match replace_last_return body with
    | Some stmts -> stmts
    | None -> [k (Cpp_ir.Build.iife ret_ty body)] )
  | expr -> [k expr]

(** Extract block template info from an inline custom expression.
    Returns [Some(ref, template, args, tyargs)] if the expression is
    an inline custom whose template contains [%result]. *)
let extract_block_template : Cpp_ir.Lowered.Expr.t -> _ = function
  | Entity (ref, tys, Some ci) -> begin
    match ci.inline with
    | Some {form = Block; text = tmpl; _} -> Some (ref, tmpl, [], tys)
    | _ -> None
    end
  | Call (_, Entity (ref, tys, Some ci), args) -> begin
    match ci.inline with
    | Some {form = Block; text = tmpl; _} -> Some (ref, tmpl, args, tys)
    | _ -> None
    end
  | _ -> None

(** The inclusive range of a fixed-width C++ integer type, or [None] when the
    spelling is not one this compiler can bound (a user-defined bignum, say).
    Only the spellings a numeral mapping can name are listed; anything else is
    left unchecked rather than guessed at. *)
let cpp_integer_range = function
  | "bool" -> Some (Z.zero, Z.one)
  | "uint8_t" | "unsigned char" -> Some (Z.zero, Z.of_string "255")
  | "uint16_t" | "unsigned short" -> Some (Z.zero, Z.of_string "65535")
  | "uint32_t" | "unsigned" | "unsigned int" ->
    Some (Z.zero, Z.of_string "4294967295")
  | "uint64_t" | "size_t" | "unsigned long" | "unsigned long long" ->
    Some (Z.zero, Z.of_string "18446744073709551615")
  | "int8_t" | "signed char" -> Some (Z.of_string "-128", Z.of_string "127")
  | "int16_t" | "short" -> Some (Z.of_string "-32768", Z.of_string "32767")
  | "int32_t" | "int" ->
    Some (Z.of_string "-2147483648", Z.of_string "2147483647")
  | "int64_t" | "long" | "long long" | "ptrdiff_t" ->
    Some (Z.of_string "-9223372036854775808",
          Z.of_string "9223372036854775807")
  | _ -> None

(** Render a folded literal through a numeral mapping's format string.

    A numeral inductive is unbounded in Rocq but its C++ image usually is not,
    and the format string ([UINT64_C(%n)]) carries the value without checking
    it.  Emitting an out-of-range literal moves the failure to the C++
    compiler at best and wraps silently at worst, so refuse it here, where the
    Rocq definition responsible can still be named. *)
let render_numeral info (n : Z.t) : Cpp_ir.Lowered.Expr.t =
  let cpp_ty = Table.find_custom_opt info.Table.ind in
  ( match Option.bind cpp_ty cpp_integer_range with
  | Some (lo, hi) when Z.lt n lo || Z.gt n hi ->
    CErrors.user_err
      (Pp.(
         str "Crane: the literal " ++ str (Z.to_string n)
         ++ str " does not fit in " ++ str (Option.get cpp_ty)
         ++ str ", the C++ type "
         ++ Printer.pr_global info.Table.ind
         ++ str " extracts to."))
  | _ -> () );
  Numeral (info.Table.ind, {value = n; text = Common.render_template [("%n", Z.to_string n)] info.Table.fmt})
