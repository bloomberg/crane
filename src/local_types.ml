(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The types a local definition leaves open are its own variables.  See
    [local_types.mli]. *)

open Miniml

(* [f] at every type [e] annotates, in order.  A global use is not walked:
   its instantiation was frozen by extraction and holds no metavariable. *)
let rec iter_annotations f = function
  | MLlam (_, ty, body) ->
    f ty;
    iter_annotations f body
  | MLletin (_, ty, a, b) ->
    f ty;
    iter_annotations f a;
    iter_annotations f b
  | MLglob _ -> ()
  | MLcons (ty, _, args) ->
    f ty;
    List.iter (iter_annotations f) args
  | MLcase (ty, e, brs) ->
    f ty;
    iter_annotations f e;
    Array.iter
      (fun (ids, ty, _, body) ->
        List.iter (fun (_, t) -> f t) ids;
        f ty;
        iter_annotations f body )
      brs
  | MLfix (_, ids, funs, _) ->
    Array.iter (fun (_, ty) -> f ty) ids;
    Array.iter (iter_annotations f) funs
  | MLapp (g, args) ->
    iter_annotations f g;
    List.iter (iter_annotations f) args
  | MLmagic (_, a) -> iter_annotations f a
  | MLparray (arr, def) ->
    Array.iter (iter_annotations f) arr;
    iter_annotations f def
  | MLtuple args -> List.iter (iter_annotations f) args
  | MLrel _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> ()

(* Solves each unsolved metavariable of a type, in order, to the rigid
   variable [!next], advancing [next], and tells [minted] the variable. *)
let rec mint ~minted ~next = function
  | Tmeta ({contents = None} as m) ->
    let v = Tvar (Rigid, !next) in
    Meta.solve m v;
    incr next;
    minted v
  | Tmeta {contents = Some t} -> mint ~minted ~next t
  | Tarr (a, b) ->
    mint ~minted ~next a;
    mint ~minted ~next b
  | Tglob (_, args, _) -> List.iter (mint ~minted ~next) args
  | _ -> ()

(* The number each let-bound lambda's variables were minted past, by the
   variables minted for them: what lowering the lambda is checked against.
   A minted variable is told apart by the node itself, which freezing keeps
   where it replaces the cell solved to it ({!Core.freeze}): numbers say
   nothing, every lambda's starting past a head of its own. *)
module Minted = Hashtbl.Make (struct
  type t = ml_type

  let equal = ( == )
  let hash = Hashtbl.hash
end)

let let_lambda_bases : int Minted.t = Minted.create 16
let () = State.on_reset State.Extraction (fun () -> Minted.reset let_lambda_bases)

(** The type a term builds in tail position, where its own annotations say so.

    Only a constructor application answers.  [MLcons] carries the inductive it
    builds (see the typing note on {!Miniml.ml_ast}), so it is the one node
    that knows its type without reconstruction; a recursive call, by
    definition, says nothing the fixpoint's own type does not already. *)
let rec tail_result_type = function
  | MLlam (_, _, b) | MLletin (_, _, _, b) | MLmagic (_, b) -> tail_result_type b
  | MLcons (ty, _, _) -> Some ty
  | MLapp (f, args) -> Translation_types.ml_app_result_type f args
  | MLcase (_, _, brs) ->
    Array.fold_left
      (fun acc (_, _, _, b) -> match acc with Some _ -> acc | None -> tail_result_type b)
      None brs
  | _ -> None

(** Recover a fixpoint's return type from its body.

    An eliminator's motive is erased, so the fixpoint MiniML builds for
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
let recover_fix_codomain ((id, ty) : Names.Id.t * ml_type) (body : ml_ast) =
  let dom, cod = Mlutil.type_decomp ty in
  match cod with
  | Tvar (_, i) when not (List.exists (fun t -> Mlutil.IntSet.mem i (Mlutil.ml_tvars t)) dom) -> (
    match tail_result_type body with
    | Some t ->
      let subst = Ml_type_util.subst_tvars_type [(i, t)] in
      ((id, subst ty), Ml_type_util.map_types_in_ast subst body)
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
  match snd (Mlutil.type_decomp ty) with
  | Tmeta ({contents = None} as cell) -> Option.iter (Meta.solve cell) (tail_result_type body)
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

let rec left_open = function
  | Tmeta {contents = None} | Topen _ -> true
  | Tmeta {contents = Some t} -> left_open t
  | Tarr (a, b) -> left_open a || left_open b
  | Tglob (_, args, _) -> List.exists left_open args
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
      | Tmeta {contents = None} | Topen _ -> unsolved := true
      | Tmeta {contents = Some t} -> visit t
      | Tvar (Rigid, _) as v -> if !base = None then base := Minted.find_opt let_lambda_bases v
      | Tarr (x, y) ->
        visit x;
        visit y
      | Tglob (_, args, _) -> List.iter visit args
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

let rec expr ~outer = function
  | MLletin (_, _, MLfix (_, ids, funs, _), b) ->
    ignore (settle ids funs);
    Array.iter (expr ~outer) funs;
    expr ~outer b
  | MLapp (MLfix (_, ids, funs, _), args) ->
    let recovered, mint = settle ids funs in
    Array.iter (iter_annotations mint) recovered;
    List.iter (iter_annotations mint) args;
    Array.iter (expr ~outer) funs;
    List.iter (expr ~outer) args
  | MLfix (_, ids, funs, _) ->
    ignore (settle ids funs);
    Array.iter (expr ~outer) funs
  | MLletin (_, t, (MLlam _ as a), b) ->
    let minted v = Minted.replace let_lambda_bases v outer in
    let mint = mint ~minted ~next:(ref (outer + 1)) in
    mint t;
    iter_annotations mint a;
    expr ~outer b
  | e -> Mlutil.ast_iter (expr ~outer) e

let structure =
  Modutil.struct_iter
    (function
      | (Dterm _ | Dfix _) as d ->
        List.iter
          (fun fd -> expr ~outer:(Mlutil.IntSet.fold max (Mlutil.ml_tvars fd.fd_type) 0) fd.fd_body)
          (Mlutil.term_defs d)
      | Dind _ | Dtype _ -> () )
    ignore ignore
