(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A definition whose body is another's, written once.  See
    [ml_dedup.mli]. *)

open Names

(* [body] with what alpha-equivalence ignores taken out: binder names, type
   annotations, and [self], the definition's own name, which its recursive
   calls spell -- as [Core.Expr.Bound_variable 0], an index no binder gives. *)
let rec canonical self body =
  let anon = Core.Binder_name.Anonymous in
  match body with
  | Core.Expr.Global {callee = r; _} when GlobRef.CanOrd.equal r self -> Core.Expr.fresh_rel 0
  | Core.Expr.Global {callee = r; _} -> Core.Expr.Global (Core.Global_use.monomorphic r)
  | Core.Expr.Lambda {body = b; _} ->
    Core.Expr.Lambda {parameter = anon; parameter_type = Core.Type.Unknown; body = canonical self b}
  | Core.Expr.Let {value = a; body = b; occurrence = occ; _} ->
    Core.Expr.Let {binder = anon;
                   binder_type = Core.Type.Unknown;
                   value = canonical self a;
                   body = canonical self b;
                   occurrence = occ}
  | Core.Expr.Construct {constructor = c; arguments = args; occurrence = occ; _} ->
    Core.Expr.Construct {result_type = Core.Type.Unknown;
                         constructor = c;
                         arguments = List.map (canonical self) args;
                         occurrence = occ}
  | Core.Expr.Match {scrutinee = s; branches = brs; occurrence = occ; _} ->
    Core.Expr.Match {scrutinee_type = Core.Type.Unknown; scrutinee = canonical self s; branches = Array.map
          (fun {Core.Match.Branch.binders = ids; pattern = p; body = b; _} ->
            { Core.Match.Branch.binders = List.map (fun _ -> (anon, Core.Type.Unknown)) ids;
              result_type = Core.Type.Unknown;
              pattern = p;
              body = canonical self b } )
          brs; occurrence = occ}
  | Core.Expr.Fixpoint {selected = i; functions = fns; bodies; occurrence = occ} ->
    Core.Expr.Fixpoint {selected = i; functions = Array.map (fun _ -> (Id.of_string "f", Core.Type.Unknown)) fns; bodies = Array.map (canonical self) bodies; occurrence = occ}
  | Core.Expr.Cofixpoint {selected = i; functions = fns; bodies; occurrence = occ} ->
    Core.Expr.Cofixpoint {selected = i; functions = Array.map (fun _ -> (Id.of_string "f", Core.Type.Unknown)) fns; bodies = Array.map (canonical self) bodies; occurrence = occ}
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
    Core.Expr.Coerce {source_type = from; target_type = into; value = canonical self a; occurrence = mocc}
  | Core.Expr.Boxed_value {value = a; occurrence = mocc} ->
    Core.Expr.Boxed_value {value = canonical self a; occurrence = mocc}
  | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
    Core.Expr.Lambda_group_barrier {value = canonical self a; occurrence = mocc}
  | e -> Mlutil.ast_map (canonical self) e

(* A forwarder with [body]'s parameters, calling [target] at its own type
   variables, in order. *)
let forwarder body target =
  let params, _ = Mlutil.collect_lams body in
  let n = List.length params in
  Mlutil.named_lams params
    (Core.Expr.Apply {callee = Core.Expr.Global (Mlutil.forwarding_use target);
                      arguments = List.init n (fun i -> Core.Expr.fresh_rel (n - i))})

(* A function definition: a fixpoint, or a term that is a lambda, emitted
   as a function.  A constant is left alone -- a forwarder would compute it
   again -- and so is a mapped one, whose body is never what is emitted, and
   a projection, which is read as a field. *)
let function_def d =
  let emitted r = not (Table.is_custom r || Table.is_projection r) in
  match d with
  | Core.Decl.Recursive_group {head = fd; tail = []} when emitted fd.entity -> Some (fd.entity, fd.body, fd.type_)
  | Core.Decl.Value {entity = r; body = (Core.Expr.Lambda _ as body); type_ = ty} when emitted r -> Some (r, body, ty)
  | _ -> None

let structure struc =
  let rec elems seen = function
    | [] -> []
    | (l, Core.Module.Structure_item.Declaration d) :: rest when function_def d <> None -> (
      let r, body, ty = Option.get (function_def d) in
      (* A forwarder runs its target's precondition checks, so two
         definitions are one only if those are the same too. *)
      let key = (canonical r body, Table.get_sigma_assertions r) in
      match List.find_opt (fun (key', _, ty') -> key' = key && Mlutil.eq_ml_type ty' ty) seen with
      | Some (_, r', _) ->
        (l, Core.Module.Structure_item.Declaration (Core.Decl.Value {entity = r;
                                                                     body = forwarder body r';
                                                                     type_ = ty})) :: elems seen rest
      | None -> (l, Core.Module.Structure_item.Declaration d) :: elems ((key, r, ty) :: seen) rest )
    | (l, Core.Module.Structure_item.Module (m : Core.Module.t)) :: rest ->
      (l, Core.Module.Structure_item.Module {m with Core.Module.expr = module_expr m.expr}) :: elems seen rest
    | se :: rest -> se :: elems seen rest
  and module_expr = function
    | Core.Module.Expr.Structure {path = mp; items = sel} ->
      Core.Module.Expr.Structure {path = mp; items = elems [] sel}
    | Core.Module.Expr.Functor {parameter = mbid; parameter_type = mt; body = me} ->
      Core.Module.Expr.Functor {parameter = mbid; parameter_type = mt; body = module_expr me}
    | me -> me
  in
  List.map (fun (mp, sel) -> (mp, elems [] sel)) struc
