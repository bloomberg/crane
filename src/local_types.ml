(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The types a local definition leaves open are its own variables.  See
    [local_types.mli]. *)

open Miniml

let rec mint ?late ~rigidity ~next = function
  | Tmeta ({contents = None} as m) ->
    let i = !next in
    next := i + 1;
    Mlutil.try_mgu ?late (Tmeta m) (Tvar (rigidity, i))
  | Tmeta {contents = Some t} -> mint ?late ~rigidity ~next t
  | Tarr (a, b) ->
    mint ?late ~rigidity ~next a;
    mint ?late ~rigidity ~next b
  | Tglob (_, args, _) -> List.iter (mint ?late ~rigidity ~next) args
  | _ -> ()

let rec mint_in_ast mint = function
  | MLlam (_, ty, body) ->
    mint ty;
    mint_in_ast mint body
  | MLletin (_, ty, a, b) ->
    mint ty;
    mint_in_ast mint a;
    mint_in_ast mint b
  | MLglob _ -> ()
  | MLcons (ty, _, args) ->
    mint ty;
    List.iter (mint_in_ast mint) args
  | MLcase (ty, e, brs) ->
    mint ty;
    mint_in_ast mint e;
    Array.iter
      (fun (ids, ty, _, body) ->
        List.iter (fun (_, t) -> mint t) ids;
        mint ty;
        mint_in_ast mint body )
      brs
  | MLfix (_, ids, funs, _) ->
    Array.iter (fun (_, ty) -> mint ty) ids;
    Array.iter (mint_in_ast mint) funs
  | MLapp (f, args) ->
    mint_in_ast mint f;
    List.iter (mint_in_ast mint) args
  | MLmagic (_, a) -> mint_in_ast mint a
  | MLparray (arr, def) ->
    Array.iter (mint_in_ast mint) arr;
    mint_in_ast mint def
  | MLtuple args -> List.iter (mint_in_ast mint) args
  | MLrel _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> ()

let rec unsolved = function
  | Tmeta {contents = None} -> true
  | Tmeta {contents = Some t} -> unsolved t
  | Tarr (a, b) -> unsolved a || unsolved b
  | Tglob (_, args, _) -> List.exists unsolved args
  | _ -> false

let check_minted ids =
  if Probe.checking () && Array.exists (fun (_, ty) -> unsolved ty) ids then
    Probe.violation "frozen program"
      Pp.(
        str "the local fixpoint " ++ Names.Id.print (fst ids.(0))
        ++ str " is lowered with a type freezing left open" )

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
  | Tmeta ({contents = None} as cell) ->
    Option.iter (Meta.solve cell) (tail_result_type body)
  | _ -> ()

(* Settles one group as translation reads it: codomains filled and recovered,
   then the signatures' remaining metavariables minted from [1].  The counter
   is returned for an applied group, which goes on to its bodies and
   arguments. *)
let settle ids funs =
  Array.iter2 fill_codomain_hole ids funs;
  let ids, funs = recover_fix_codomains ids funs in
  let next = ref 1 in
  Array.iter (fun (_, ty) -> mint ~rigidity:Rigid ~next ty) ids;
  (funs, mint ~rigidity:Rigid ~next)

let rec expr = function
  | MLletin (_, _, MLfix (_, ids, funs, _), b) ->
    ignore (settle ids funs);
    Array.iter expr funs;
    expr b
  | MLapp (MLfix (_, ids, funs, _), args) ->
    let recovered, mint = settle ids funs in
    Array.iter (mint_in_ast mint) recovered;
    List.iter (mint_in_ast mint) args;
    Array.iter expr funs;
    List.iter expr args
  | MLfix (_, ids, funs, _) ->
    ignore (settle ids funs);
    Array.iter expr funs
  | MLletin (_, _, MLlam _, b) -> expr b
  | e -> Mlutil.ast_iter expr e

let structure =
  Modutil.struct_iter
    (function
      | (Dterm _ | Dfix _) as d -> List.iter (fun fd -> expr fd.fd_body) (Mlutil.term_defs d)
      | Dind _ | Dtype _ -> () )
    ignore ignore
