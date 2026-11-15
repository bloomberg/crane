(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The types a local definition leaves open are its own variables.  See
    [local_types.mli]. *)


(* [f] at every type [e] annotates, in order.  A global use is not walked:
   its instantiation was frozen by extraction and holds no metavariable. *)
let rec iter_annotations f = function
  | Core.Expr.Lambda {parameter_type = ty; body; _} ->
    f ty;
    iter_annotations f body
  | Core.Expr.Let {binder_type = ty; value = a; body = b; _} ->
    f ty;
    iter_annotations f a;
    iter_annotations f b
  | Core.Expr.Global _ -> ()
  | Core.Expr.Construct {result_type = ty; arguments = args; _} ->
    f ty;
    List.iter (iter_annotations f) args
  | Core.Expr.Match {scrutinee_type = ty; scrutinee = e; branches = brs; _} ->
    f ty;
    iter_annotations f e;
    Array.iter
      (fun {Core.Match.Branch.binders = ids; result_type = ty; body = body; _} ->
        List.iter (fun (_, t) -> f t) ids;
        f ty;
        iter_annotations f body )
      brs
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    Array.iter (fun (_, ty) -> f ty) ids;
    Array.iter (iter_annotations f) funs
  | Core.Expr.Apply {callee = g; arguments = args} ->
    iter_annotations f g;
    List.iter (iter_annotations f) args
  | Core.Expr.Coerce {value = a; _}
  | Core.Expr.Boxed_value {value = a; _}
  | Core.Expr.Lambda_group_barrier {value = a; _} ->
    iter_annotations f a
  | Core.Expr.Persistent_array {elements = arr; default = def} ->
    Array.iter (iter_annotations f) arr;
    iter_annotations f def
  | Core.Expr.Tuple args -> List.iter (iter_annotations f) args
  | Core.Expr.Bound_variable _
  | Core.Expr.Runtime_error _
  | Core.Expr.Erased_value _
  | Core.Expr.Axiom_value _
  | Core.Expr.UInt63 _
  | Core.Expr.Numeral _
  | Core.Expr.Float64 _
  | Core.Expr.String _ -> ()

(* Solves each unsolved metavariable of a type, in order, to the rigid
   variable [!next], advancing [next], and tells [minted] the variable. *)
let rec mint ~minted ~next = function
  | Core.Type.Meta ({contents = None} as m) ->
    let v = Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; variable = !next} in
    Core.Extracted.Meta.solve m v;
    incr next;
    minted v
  | Core.Type.Meta {contents = Some t} -> mint ~minted ~next t
  | Core.Type.Arrow {parameter = a; result = b} ->
    mint ~minted ~next a;
    mint ~minted ~next b
  | Core.Type.Global_app {type_arguments = args; _} -> List.iter (mint ~minted ~next) args
  | _ -> ()

(* The number each let-bound lambda's variables were minted past, by the
   variables minted for them: what lowering the lambda is checked against.
   A minted variable is told apart by the node itself, which freezing keeps
   where it replaces the cell solved to it ({!Core_phase.freeze}): numbers say
   nothing, every lambda's starting past a head of its own. *)
module Minted = Hashtbl.Make (struct
  type t = Core.Type.t

  let equal = ( == )
  let hash = Hashtbl.hash
end)

let let_lambda_bases : int Minted.t = Minted.create 16
let () = State.on_reset State.Extraction (fun () -> Minted.reset let_lambda_bases)

(** The type a term builds in tail position, where its own annotations say so.

    A constructor application answers: [Core.Expr.Construct] carries the inductive it
    builds (see the typing note on {!Core.Expr.t}), so it knows its type
    without reconstruction.  So does a fully applied global, from its declared
    codomain as the call instantiates it
    ({!Translation_calls.core_app_result_type}).  A recursive call, its head a
    local, answers nothing: it says nothing the fixpoint's own type does not
    already.  A match answers with its first branch that does. *)
let rec tail_result_type = function
  | Core.Expr.Lambda {body = b; _}
  | Core.Expr.Let {body = b; _}
  | Core.Expr.Coerce {value = b; _}
  | Core.Expr.Boxed_value {value = b; _}
  | Core.Expr.Lambda_group_barrier {value = b; _} -> tail_result_type b
  | Core.Expr.Construct {result_type = ty; _} -> Some ty
  | Core.Expr.Apply {callee = f; arguments = args} -> Translation_calls.core_app_result_type f args
  | Core.Expr.Match {branches = brs; _} ->
    Array.fold_left
      (fun acc {Core.Match.Branch.body = b; _} -> match acc with Some _ -> acc | None -> tail_result_type b)
      None brs
  | _ -> None

(** Recover a fixpoint's return type from its body.

    An eliminator's motive is erased, so the fixpoint Core builds for
    [nat_rect] carries a type variable where its result type belongs -- one no
    parameter mentions and no caller supplies.  Lifted to a C++ template that
    becomes a template parameter nothing deduces, leaving the call site to
    guess: [_shifted_F<std::any>] against a body returning [Positive].

    The body knows.  Where the variable is undeducible -- absent from every
    parameter type -- and a tail position builds a constructor, that
    constructor's inductive is what the function returns, and substituting it
    makes the signature say so.

    A variable some parameter mentions is genuine polymorphism and is left
    alone.  So is one whose body builds nothing:
    [tests/regression/anon_lift_name_collision]'s [_count_F] returns [T1] from
    integer literals, and its call site supplies the argument. *)
let recover_fix_codomain ((id, ty) : Names.Id.t * Core.Type.t) (body : Core.Expr.t) =
  let dom, cod = Core_util.type_decomp ty in
  match cod with
  | Core.Type.Variable {variable = i; _}
    when not (List.exists (fun t -> Core_util.IntSet.mem i (Core_util.core_tvars t)) dom) -> (
    match tail_result_type body with
    | Some t ->
      let subst = Type_util.subst_tvars_type [(i, t)] in
      ((id, subst ty), Type_util.map_types_in_ast subst body)
    | None -> ((id, ty), body) )
  | _ -> ((id, ty), body)

let recover_fix_codomains ids funs =
  let settled = Array.map2 recover_fix_codomain ids funs in
  (Array.map fst settled, Array.map snd settled)

(* A codomain extraction left a hole is filled from the body the same way,
   by solving the hole: the cell is shared with every annotation the body
   writes it into, so filling it is the substitution.  It is filled before
   anything is minted -- a variable already standing for the result type is
   no longer asking what the body builds. *)
let fill_codomain_hole (_, ty) body =
  match snd (Core_util.type_decomp ty) with
  | Core.Type.Meta ({contents = None} as cell) -> Option.iter (Core.Extracted.Meta.solve cell) (tail_result_type body)
  | _ -> ()

(* Settles one group as translation reads it: codomains filled and recovered,
   then the signatures' remaining metavariables minted from [1].  The minting
   goes on for an applied group, into its bodies and arguments. *)
let settle ids funs =
  Array.iter2 fill_codomain_hole ids funs;
  let ids, funs = recover_fix_codomains ids funs in
  let mint = mint ~minted:ignore ~next:(ref 1) in
  Array.iter (fun (_, ty) -> mint ty) ids;
  (funs, mint)

(* Whether [ty] still holds an unsolved metavariable or an open type. *)
let rec left_open = function
  | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
  | Core.Type.Meta {contents = Some t} -> left_open t
  | Core.Type.Arrow {parameter = a; result = b} -> left_open a || left_open b
  | Core.Type.Global_app {type_arguments = args; _} -> List.exists left_open args
  | _ -> false

let violation what = Probe.violation "frozen program" (Pp.str what)

let check_minted ids =
  if Probe.checking () && Array.exists (fun (_, ty) -> left_open ty) ids then
    violation
      ( "the local fixpoint " ^ Names.Id.to_string (fst ids.(0))
      ^ " is lowered with a type freezing left open" )

let check_let_lambda ~outer t a =
  if Probe.checking () then begin
    let base = ref None and unsolved = ref false in
    let rec visit = function
      | Core.Type.Meta {contents = None} | Core.Type.Open _ -> unsolved := true
      | Core.Type.Meta {contents = Some t} -> visit t
      | Core.Type.Variable {rigidity = Core.Type.Rigidity.Rigid; _} as v ->
        if !base = None then base := Minted.find_opt let_lambda_bases v
      | Core.Type.Arrow {parameter = x; result = y} ->
        visit x;
        visit y
      | Core.Type.Global_app {type_arguments = args; _} -> List.iter visit args
      | _ -> ()
    in
    visit t;
    iter_annotations visit a;
    if !unsolved then violation "a let-bound lambda is lowered with a type freezing left open";
    match !base with
    | Some b when b <> outer ->
      violation
        (Printf.sprintf
           "a let-bound lambda's variables were numbered past %d, and it is lowered under a head \
            of %d"
           b outer )
    | _ -> ()
  end

(* Mints the open variables of the local definitions in [e], under a
   declaration whose own variables number up to [outer]. *)
let rec expr ~outer = function
  | Core.Expr.Let {value = (Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group);
                   body = b; _} ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    ignore (settle ids funs);
    Array.iter (expr ~outer) funs;
    expr ~outer b
  | Core.Expr.Apply {callee = (Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group);
                     arguments = args} ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    let recovered, mint = settle ids funs in
    Array.iter (iter_annotations mint) recovered;
    List.iter (iter_annotations mint) args;
    Array.iter (expr ~outer) funs;
    List.iter (expr ~outer) args
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    ignore (settle ids funs);
    Array.iter (expr ~outer) funs
  | Core.Expr.Let {binder_type = t; value = (Core.Expr.Lambda _ as a); body = b; _} ->
    let minted v = Minted.replace let_lambda_bases v outer in
    let mint = mint ~minted ~next:(ref (outer + 1)) in
    mint t;
    iter_annotations mint a;
    expr ~outer b
  | e -> Core_util.ast_iter (expr ~outer) e

let structure =
  Modutil.struct_iter
    (function
      | (Core.Decl.Value _ | Core.Decl.Recursive_group _) as d ->
        List.iter
          (fun (fd : Core.Recursion.Definition.t) ->
            expr ~outer:(Core_util.IntSet.fold max (Core_util.core_tvars fd.type_) 0) fd.body)
          (Core_util.term_defs d)
      | Core.Decl.Inductive _ | Core.Decl.Type_alias _ -> () )
    ignore ignore
