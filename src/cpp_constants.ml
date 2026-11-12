(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A function's constants as named locals.  See [cpp_constants.mli]. *)

open Names

type expr = Cpp_ir.Lowered.Expr.t
type stmt = Cpp_ir.Lowered.Stmt.t

(* [Some (name, init)] where [e] is a constant translation marked
   ({!Crane_rt.Constant}). *)
let marked : expr -> _ = function
  | Call (_, Runtime (Crane_rt.Constant name), [init]) -> Some (Id.of_string name, init)
  | _ -> None

(* [Some e] where [e] is an erased closure ([crane_erase_fn]) over a closed
   lambda: like a marked constant, the same value wherever it is evaluated,
   and an allocation each time. *)
let closed_erase_fn (e : expr) =
  match e with
  | Erase_callable (_, l) when Cpp_ir.Variables.closed_lambda l -> Some e
  | _ -> None

(* The identifiers [body] declares or reads, which a constant's name must not
   shadow or be shadowed by -- the globals it names included: a constant is
   named after the function that builds it. *)
let names_in (body : stmt list) =
  let names = ref Id.Set.empty in
  let add id = names := Id.Set.add id !names in
  let rec fe (e : expr) =
    ( match e with
    | Local id -> add id
    | Entity (r, _, _) -> add (Label.to_id (Common.label_of_r r))
    | _ -> () );
    Cpp_ir.Map.expr (children ()) e
  and fs (s : stmt) =
    (match s with Bind_variable (id, _, _) | Declare (id, _, _) -> add id | _ -> ());
    Cpp_ir.Map.stmt (children ()) s
  and children () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  List.iter (fun s -> ignore (fs s)) body;
  !names

(* [body] with each marked constant read from a [static const] declared at
   its top, one per distinct constant.  The initialiser is evaluated once, as
   a global's is, so it is [unmark]ed. *)
let rec hoist_body (body : stmt list) : stmt list =
  let hoisted = ref [] in
  (* Names are only needed where there is something to name. *)
  let taken = lazy (ref (names_in body)) in
  let fresh hint =
    let taken = Lazy.force taken in
    let rec go k =
      (* [case_] numbers as [case_1]: a double underscore is reserved. *)
      let id =
        if k = 0 then hint
        else
          let h = Id.to_string hint in
          let sep = if h <> "" && h.[String.length h - 1] = '_' then "" else "_" in
          Id.of_string (h ^ sep ^ string_of_int k)
      in
      if Id.Set.mem id !taken then go (k + 1) else id
    in
    let id = go 0 in
    taken := Id.Set.add id !taken;
    id
  in
  let rec fe (e : expr) : expr =
    match closed_erase_fn e with
    | Some init -> hoisted_var (Id.of_string "erased_fn") init
    | None -> (
      match marked e with
      | Some (hint, init) -> hoisted_var hint init
      | None -> Cpp_ir.Map.expr (children ()) e )
  and hoisted_var hint init : expr =
    let init = unmark init in
    let id =
      match List.assoc_opt init !hoisted with
      | Some id -> id
      | None ->
        let id = fresh hint in
        hoisted := (init, id) :: !hoisted;
        id
    in
    Local id
  and fs s = Cpp_ir.Map.stmt (children ()) s
  and children () = Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id () in
  let body' = List.map fs body in
  if !hoisted = [] then body
  else
    List.rev_map
      (fun (init, id) : stmt ->
        Bind_variable
          ( id,
            Declare_static (Const Auto),
            Call
              ( {yields = Untyped; params = Unknown; constructs = None; occurrence = None},
                Runtime Crane_rt.Immortal,
                [init] ) ) )
      !hoisted
    @ body'

(* Outside any function -- in a global's initialiser, evaluated once anyway --
   a constant is its initialiser, unless it is inside a lambda there: a
   lambda's body is a function's, and its constants are declared at its top. *)
and unmark (e : expr) : expr =
  match marked e with
  | Some (_, init) -> unmark init
  | None -> Cpp_ir.Map.expr (Cpp_ir.Map.make ~stmts:hoist_body ~expr:unmark ~stmt:unmark_stmt ~type_:Fun.id ()) e

and unmark_stmt s = Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:unmark ~stmt:unmark_stmt ~type_:Fun.id ()) s

let decl (d : Cpp_ir.Lowered.Decl.t) =
  Cpp_ir.Map.decl (Cpp_ir.Map.make ~stmts:hoist_body ~expr:unmark ~stmt:unmark_stmt ~type_:Fun.id ()) d
