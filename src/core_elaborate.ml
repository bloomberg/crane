(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Global calls elaborated from Core, ahead of translation
    (docs/Pipeline-Disentangling-Plan.md, section 4.7).  See
    [core_elaborate.mli]. *)

open Miniml
open Names
open Util
open Translation_state
open Ml_type_util
open Translation_support
open Translation_types
open Table

(** [classify ~lex id written] -- the role each argument the call of [id]
    writes has, as Core elaborates the call from the call alone
    ({!Elaborated_call.role}): a dictionary, a regular argument, one past the
    callee's arity and so applied to its result, or one at no value position.
    A variable argument is read off the binder it names in [lex], the
    environment the call is typed in, by its ML type and its role
    ({!Lexenv.binder}); no C++ name is consulted, and nothing of the
    traversal that asks. *)
let classify ~lex id written =
  (* Each argument with its position, so that the partition below says
     where each one went rather than handing back the arguments. *)
  let args = List.mapi (fun i a -> (i, a)) written in
  (* When the call has more args than the function's ML value-domain, the
     excess args are curried applications to the result. This is common with
     Rocq's Function vernacular _correct proof terms, where the extraction
     produces e.g. div2_rect f f0 f1 n _res __ but div2_rect only has 4
     value-domain params (f, f0, f1, n). The trailing _res and __ are applied
     to the result via currying.

     Split into: - primary_args: first n_value_dom args (passed to the
     function) - excess_args: remaining non-dummy args (curried onto the
     result) Only activates when n_args > n_value_dom; otherwise unchanged. *)
  let args_before_split = args in
  let args, excess_args =
    let is_value_arg = function
      | MLdummy _ -> false
      (* A variable bound at an erased type carries no more than a dummy:
         under [Conservative Types] a definition keeps its type binders and
         passes them on ([length A l']). *)
      | MLrel i -> (
        match Lexenv.type_opt lex i with
        | Some t -> not (erased_by_extraction t)
        | None -> true )
      | _ -> true
    in
    let is_value (_, a) = is_value_arg a in
    let is_value_dom t =
      match resolve_tmeta t with
      | Miniml.Tdummy _ -> false
      | _ -> true
    in
    let rec collect_tarr_dom acc = function
      | Miniml.Tarr (t1, t2) -> collect_tarr_dom (resolve_tmeta t1 :: acc) t2
      | _ -> List.rev acc
    in
    match find_type_opt id with
    | Some ml_ty ->
      let all_dom = collect_tarr_dom [] ml_ty in
      (* Count value-domain entries by filtering out ALL [Tdummy] positions
         (both [Ktype] for erased type params and [Kprop] for erased proofs).
         Symmetrically, filter the arg list to exclude [MLdummy] entries.
         Comparing these two filtered counts avoids false excess detection
         when erased params appear in [args] as [MLdummy] instead of (or in
         addition to) being carried in [tys]. *)
      let n_value_dom = List.length (List.filter is_value_dom all_dom) in
      (* An erased argument at a position the declaration takes a value at
         stays: the category classes over [obj : Type] take their objects
         as values, and at [obj := Type -> Type] those objects are families
         the call erases.  Dropping them would change the call's arity; the
         declaration receives an empty box instead. *)
      let value_args =
        (* Two conventions meet here.  The arguments the Rocq term gave
           have the declaration's erased domains dropped ([make_mlargs]
           kills each [Tdummy]), so each is at a value domain, erased or
           not.  The tail an eta-expansion invents keeps them: a dummy at
           each erased domain, a variable at each value one
           ([STRefToIxNat __ __ ref]).  The tail is the longest suffix
           paired with the domains that way, provided what precedes it
           fills the remaining value domains exactly; with none, every
           argument is at a value domain or past the last one.  The one
           dummy with no domain at all is the one a purely logical
           signature is applied to. *)
        if n_value_dom = 0 then List.filter is_value args
        else
          let n_args = List.length args and n_dom = List.length all_dom in
          let eta_paired k =
            List.for_all2
              (fun d a -> is_value_dom d = is_value a)
              (List.lastn k all_dom) (List.lastn k args)
            && List.length
                 (List.filter is_value_dom (List.firstn (n_dom - k) all_dom))
               = n_args - k
          in
          let rec longest k =
            if k = 0 then None else if eta_paired k then Some k else longest (k - 1)
          in
          match longest (min n_args n_dom) with
          | Some k ->
            List.firstn (n_args - k) args
            @ List.filter is_value (List.lastn k args)
          | None -> args
      in
      let n_value_args = List.length value_args in
      if n_value_args > n_value_dom then
        let primary =
          List.filteri (fun i _ -> i < n_value_dom) value_args
        in
        let excess =
          List.filteri
            (fun i a -> i >= n_value_dom && is_value a)
            value_args
        in
        (primary, excess)
      else
        (value_args, [])
    | None -> (List.filter is_value args, [])
  in
  (* A value argument that vanishes here vanishes from the emitted call, and
     the parameter it would have filled is dropped from the declaration by
     the same [Tdummy] reading of the callee's domain -- leaving a body that
     names a binder nothing supplies.  Report it rather than make it a
     question about reading the generated C++ back. *)
  let () =
    if Sys.getenv_opt "CRANE_DBG_DROPPED_ARGS" <> None then
      let n_in = List.length args_before_split in
      let n_out = List.length args + List.length excess_args in
      if n_out < n_in then
        Feedback.msg_warning
          (Pp.str
             (Printf.sprintf
                "crane: call to %s drops %d of %d arguments (%d dummy, %d \
                 value domains declared)"
                (Table.kername_of_global id)
                (n_in - n_out) n_in
                (List.length
                   (List.filter
                      (function _, MLdummy _ -> true | _ -> false)
                      args_before_split ))
                (List.length args) ) )
  in
  (* An erased instance leaves the call but not the declaration: its
     parameter is still one of the callee's, so a position counted in the
     declaration's parameter list steps over it. *)
  let instances, regular = List.partition (fun (_, a) -> is_typeclass_instance_arg ~lex a) args in
  let erased, kept = List.partition (fun (_, a) -> instance_arg_is_erased ~lex a) instances in
  (* The erased arguments left among the regular ones are the ones the
     declaration takes a value at (see [value_args] above); they are
     generated as empty boxes rather than as the [CPPabort] an [MLdummy] is
     elsewhere. *)
  let role_of i =
    let at l = List.exists (fun (j, _) -> Int.equal i j) l in
    if at kept then Elaborated_call.Dictionary
    else if at erased then Elaborated_call.Erased_dictionary
    else if at regular then Elaborated_call.Regular
    else if at excess_args then Elaborated_call.Excess
    else Elaborated_call.Dropped
  in
  List.mapi (fun i _ -> role_of i) written

(* The call of [use] to [args], each argument in the role at its position. *)
let of_roles use args roles =
  let id = use.callee in
  (* Order the instance arguments the way the callee numbered its own
     [_tcI] parameters.  [Gen_decls.gen_dfun] iterates [collect_lams]
     output, which is reversed from source order, so a plain constrained
     function's first instance parameter is the source-last one; an instance
     struct is stripped left to right by [Gen_decls.gen_instance_struct] and
     keeps source order.  Call sites have the arguments in source order. *)
  let dictionaries =
    if ref_returns_typeclass id then Elaborated_call.Source_order else Elaborated_call.Reversed
  in
  Elaborated_call.of_roles ~callee:id ~callee_type:(find_type id) ~dictionaries
    ~tyargs:(Call_tyargs.of_use use) args roles

let elaborate_arguments ~lex use args = of_roles use args (classify ~lex use.callee args)

(** A global application of the program: the occurrence of the use naming
    its callee, and the roles of the arguments it writes. *)
type entry = {
  occurrence : Occurrence.t;
  roles : Elaborated_call.role list;
}

type t = {
  calls : entry list Ref.User.Map.t;  (** By callee, each newest first. *)
  named : GlobRef.Set_env.t;  (** Every global the bodies name, applied or not. *)
}

let empty = {calls = Ref.User.Map.empty; named = GlobRef.Set_env.empty}

(* What the walk has found so far: the walk's own, never seen outside
   {!structure}. *)
type builder = t ref

let name (b : builder) r = b := {!b with named = GlobRef.Set_env.add r !b.named}

let record (b : builder) lex use args =
  match classify ~lex use.callee args with
  | roles ->
    let others = Option.default [] (Ref.User.Map.find_opt use.callee !b.calls) in
    let entry = {occurrence = Global_use.occurrence use; roles} in
    b := {!b with calls = Ref.User.Map.add use.callee (entry :: others) !b.calls}
  (* A callee with no type is never translated as a call: the traversal
     reaches it by another route or not at all. *)
  | exception Not_found -> ()

let binder role (x, ty) = {Lexenv.eb_id = Mlutil.id_of_mlid x; eb_type = ty; eb_role = role}

(* The binders [ids], innermost first, as [collect_lams] returns them. *)
let push role ids lex = Lexenv.push (List.map (binder role) ids) lex

let rec walk b ~n_outer lex = function
  (* A spine is read whole, as translation reads it: a global applied in
     stages is called once with every argument, and applying a one-branch
     match applies its branch.  A coercion of the callee is seen through:
     what is called is what it coerces, at every argument -- [not] applied
     to the proposition it erases, in a type written [{P} + {~P}]. *)
  | MLapp (MLapp ((MLglob _ as g), inner), outer) -> walk b ~n_outer lex (MLapp (g, inner @ outer))
  | MLapp (MLmagic (_, f), args) -> walk b ~n_outer lex (MLapp (f, args))
  | MLapp (MLcase (ty, scrut, [|(ids, rty, pat, body)|]), outer) ->
    let outer = List.map (Mlutil.ast_lift (List.length ids)) outer in
    let body =
      match body with
      | MLapp (f, inner) -> MLapp (f, inner @ outer)
      | _ -> MLapp (body, outer)
    in
    walk b ~n_outer lex (MLcase (ty, scrut, [|(ids, rty, pat, body)|]))
  | MLapp (MLglob use, args) ->
    walk_use b ~n_outer lex use;
    record b lex use args;
    List.iter (walk b ~n_outer lex) args
  | MLapp (f, args) ->
    walk b ~n_outer lex f;
    List.iter (walk b ~n_outer lex) args
  | MLlam _ as e ->
    let ids, body = Mlutil.collect_lams e in
    List.iter (fun (_, ty) -> walk_type b ~n_outer lex ty) ids;
    walk b ~n_outer (push Lexenv.Value ids lex) body
  (* An alias of a polymorphic function is not bound but put in place of its
     uses ({!Translation_support.let_lambda}), and its calls are those of
     what it abbreviates, at the arguments each use gives it. *)
  | MLletin (x, ty, (MLlam _ as a), body) -> (
    walk_type b ~n_outer lex ty;
    match let_lambda ~lex ~n_outer ty a body with
    | Inlined body -> walk b ~n_outer lex body
    | Bound | At_instance _ | Lifted ->
      walk b ~n_outer lex a;
      walk b ~n_outer (push Lexenv.Value [(x, ty)] lex) body )
  | MLletin (x, ty, a, body) ->
    walk_type b ~n_outer lex ty;
    walk b ~n_outer lex a;
    walk b ~n_outer (push Lexenv.Value [(x, ty)] lex) body
  | MLcons (ty, _, args) ->
    walk_type b ~n_outer lex ty;
    List.iter (walk b ~n_outer lex) args
  | MLtuple args -> List.iter (walk b ~n_outer lex) args
  | MLcase (ty, scrut, branches) ->
    walk_type b ~n_outer lex ty;
    walk b ~n_outer lex scrut;
    (* A branch's result type is written under its binders: a custom match
       declares it as the type its arm returns. *)
    Array.iter
      (fun (ids, rty, _, body) ->
        List.iter (fun (_, ty) -> walk_type b ~n_outer lex ty) ids;
        let lex = push Lexenv.Value (List.rev ids) lex in
        walk_type b ~n_outer lex rty;
        walk b ~n_outer lex body )
      branches
  | MLfix (_, fs, defs, _, _) ->
    Array.iter (fun (_, ty) -> walk_type b ~n_outer lex ty) fs;
    (* The last function of the group is the innermost binder. *)
    let fs = List.rev_map (fun (f, ty) -> (Id f, ty)) (Array.to_list fs) in
    Array.iter (walk b ~n_outer (push Lexenv.Value fs lex)) defs
  | MLmagic (_, e) -> walk b ~n_outer lex e
  | MLparray (elems, def) ->
    Array.iter (walk b ~n_outer lex) elems;
    walk b ~n_outer lex def
  (* A global named but not applied -- a function passed as a value -- is
     translated as its call with no arguments. *)
  | MLglob use ->
    walk_use b ~n_outer lex use;
    record b lex use []
  | MLrel _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> ()

and walk_use b ~n_outer lex use =
  name b use.callee;
  Global_use.iter_types (walk_type b ~n_outer lex) use

(* A custom type applied to a term -- a fixed-size array to its length --
   has calls of its own, translated where the type is converted. *)
and walk_type b ~n_outer lex ty =
  match resolve_tmeta ty with
  | Tglob (g, tys, args) ->
    List.iter (walk_type b ~n_outer lex) tys;
    if Table.is_custom g then List.iter (walk b ~n_outer lex) args
  | Tarr (dom, cod) ->
    walk_type b ~n_outer lex dom;
    walk_type b ~n_outer lex cod
  | Tapp (_, tys) -> List.iter (walk_type b ~n_outer lex) tys
  | _ -> ()

(* The variables a declaration of type [ty] is generated under: the type
   variables of its head, which a let-bound lambda in its body is numbered
   past ({!Local_types}). *)
let head_variables ty = Mlutil.IntSet.fold max (Mlutil.ml_tvars ty) 0

(* A declaration's own parameters are bound as its parameters, at the types
   its body is generated with ({!Translation_support.reconcile_parameter_type}):
   the class-typed ones are its dictionaries
   ({!Translation_state.parameter_role}).  Translation unifies a parameter's
   annotation with the declaration's type when it generates the head; an
   annotation that is still a bare metavariable is solved to the declared
   type there, so that is the type read here, without solving anything.  The
   lambdas bind the declaration's outermost domains; a body short of the
   rest is generated eta-expanded, applied to a parameter at each of them
   that is not erased ({!Gen_functions.dfun_body_scope}), and that
   application is what is elaborated: a definition that is another
   function, [add := Z.add], calls it. *)
let declaration_scope ty body =
  let ty = Mlutil.type_simpl ty in
  let params, body = collect_typed_lams ty body in
  let doms = List.rev (Ml_type_util.ml_domains ty) in
  let n_missing = max 0 (List.length doms - List.length params) in
  let declared = List.skipn n_missing doms in
  let parameter (x, body_ty) sig_ty =
    let body_ty =
      match resolve_tmeta body_ty with Tmeta {contents = None} | Topen _ -> sig_ty | t -> t
    in
    let ty = reconcile_parameter_type body_ty sig_ty in
    binder (parameter_role ty) (x, ty)
  in
  let missing =
    List.mapi
      (fun i t -> binder (parameter_role t) (Id (Common.eta_param_id (n_missing - 1 - i)), t))
      (List.firstn n_missing doms)
  in
  let body =
    match body with
    | (MLaxiom _ | MLexn _) as b -> b
    | b ->
      let args =
        List.rev
          (List.filter_map
             (fun (i, t) -> if erased_by_extraction t then None else Some (MLrel (i + 1)))
             (List.mapi (fun i t -> (i, t)) (List.firstn n_missing doms)) )
      in
      Mlutil.apply_eta_args (Mlutil.ast_lift n_missing b) args
  in
  (Lexenv.push missing (Lexenv.push (List.map2 parameter params declared) Lexenv.empty), body)

(* A declaration's calls, read in that scope. *)
let declaration b ty body =
  let lex, body = declaration_scope ty body in
  let ty = Mlutil.type_simpl ty in
  let n_outer = head_variables ty in
  walk_type b ~n_outer Lexenv.empty ty;
  walk b ~n_outer lex body

(* A constant typed by a name that stands for arrows -- an instance of a
   single-method class is typed by the class -- is generated eta-expanded to
   those arrows ({!Gen_functions.gen_spec}): the slot it initialises is a
   function of the full signature, which no partial application fills. *)
let constant_at_alias b ty body =
  let ty = Mlutil.type_simpl ty in
  let body = match body with MLmagic (_, b) -> b | b -> b in
  if Ml_type_util.ml_domains ty = [] then
    match Ml_type_util.eta_expand_to (Ml_type_util.expand_ml_fun_alias ty) body with
    | expanded when expanded != body -> walk b ~n_outer:(head_variables ty) Lexenv.empty expanded
    | _ -> ()

(* An instance's methods are generated from its record's fields not as
   written but as {!Instance_methods} elaborates them -- expanded to the arity
   the class declares, or, a function named point-free, applied to
   parameters of its own -- and under the instance's own parameters, so those
   are the bodies the calls inside them are elaborated in.  The record as
   written is walked too, with the rest of the declaration. *)
let instance_methods b name body ty =
  Option.iter
    (fun (lam_params, methods) ->
      let lex =
        Lexenv.push (List.rev_map (fun (x, ty) -> binder (parameter_role ty) (Id x, ty)) lam_params) Lexenv.empty
      in
      let n_outer = head_variables ty in
      List.iter
        (fun (m : Instance_methods.method_) ->
          walk b ~n_outer lex m.body;
          let params, inner = Instance_methods.params m in
          if List.for_all (fun p -> p.Instance_methods.erased) params then
            Option.iter
              (fun (eta, call) ->
                walk b ~n_outer (push Lexenv.Value (List.rev_map (fun (x, ty) -> (Id x, ty)) eta) lex) call )
              (Instance_methods.eta_call m inner) )
        methods )
    (Instance_methods.methods name body ty)

(* A call converts its callee's declared type, instantiated, so the terms
   custom types are applied to there -- [not] in [{x = y} + {x <> y}] -- are
   elaborated with it; the unit's own declarations' types are walked with
   them, the others' here, as closed types.  Walking one may name another
   global, whose type is then walked in turn. *)
let rec foreign_types b ~walked =
  let pending = GlobRef.Set_env.diff !b.named walked in
  if not (GlobRef.Set_env.is_empty pending) then begin
    GlobRef.Set_env.iter (fun r -> Option.iter (walk_type b ~n_outer:0 Lexenv.empty) (find_type_opt r)) pending;
    foreign_types b ~walked:(GlobRef.Set_env.union walked pending)
  end

let structure struc =
  let b = ref empty in
  let defined = ref GlobRef.Set_env.empty in
  let define r = defined := GlobRef.Set_env.add r !defined in
  let closed_type = walk_type b ~n_outer:0 Lexenv.empty in
  let inductive ind = Array.iter (fun p -> Array.iter (List.iter closed_type) p.ip_types) ind.ind_packets in
  Modutil.struct_iter
    (function
      | Dterm (r, body, ty) ->
        define r;
        declaration b ty body;
        constant_at_alias b ty body;
        instance_methods b r body ty
      | Dfix fds ->
        List.iter
          (fun fd ->
            define fd.fd_ref;
            declaration b fd.fd_type fd.fd_body )
          fds
      | Dind (_, ind) -> inductive ind
      | Dtype (_, _, ty) -> closed_type ty )
    (function
      | Sind (_, ind) -> inductive ind
      | Stype (_, _, ty) -> Option.iter closed_type ty
      | Sval (_, _, ty) -> closed_type ty )
    ignore struc;
  foreign_types b ~walked:!defined;
  !b

let referenced t = GlobRef.Set_env.elements t.named

let installed = State.cell State.Unit empty

type tally = {found : int; recomputed : int}

let tally = State.cell State.Unit {found = 0; recomputed = 0}

let install t =
  installed := t;
  tally := {found = 0; recomputed = 0}

(* A body's annotations may be rewritten before it is translated, which
   rebuilds every node, so the use's occurrence is what identifies the
   application; one a rewrite duplicated is found only where every copy has
   the same roles. *)
let roles t use n =
  match Ref.User.Map.find_opt use.callee t.calls with
  | None -> None
  | Some entries -> (
    let occurrence = Global_use.occurrence use in
    match
      List.filter
        (fun e -> Occurrence.equal e.occurrence occurrence && Int.equal (List.length e.roles) n)
        entries
    with
    | [] -> None
    | e :: rest when List.for_all (fun e' -> List.equal ( = ) e.roles e'.roles) rest ->
      Some e.roles
    | _ -> None )

let elaboration ~lex use args =
  let elaborate () = elaborate_arguments ~lex use args in
  match Common.get_phase () with
  | Common.Plan -> elaborate ()
  | Common.Emit -> (
    match roles !installed use (List.length args) with
    | Some roles ->
      tally := {!tally with found = !tally.found + 1};
      let call = of_roles use args roles in
      if Probe.checking () && not (Elaborated_call.same_roles call (elaborate ())) then
        CErrors.anomaly
          Pp.(
            str "Crane: a call to " ++ str (Table.kername_of_global use.callee)
            ++ str " elaborated from Core disagrees with its elaboration where it is translated." );
      call
    | None ->
      tally := {!tally with recomputed = !tally.recomputed + 1};
      Probe.violation "elaborated calls"
        Pp.(
          str "a call to " ++ str (Table.kername_of_global use.callee)
          ++ str " is translated where Core elaboration did not reach it.");
      elaborate () )

let report () =
  let n = Ref.User.Map.fold (fun _ l acc -> acc + List.length l) !installed.calls 0 in
  Printf.sprintf "elaborated calls: %d planned; emission found %d, elaborated %d itself" n
    !tally.found !tally.recomputed
