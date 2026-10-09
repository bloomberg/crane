(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A function's constants as named locals.  See [cpp_constants.mli]. *)

open Names
open Minicpp

(* [Some (name, init)] where [e] is a constant translation marked
   ({!Crane_rt.Constant}). *)
let marked e =
  match e with
  | CPPfun_call (_, CPPrt (Crane_rt.Constant name), args) -> (
    match call_args args with
    | [init] -> Some (Id.of_string name, init)
    | _ -> None )
  | _ -> None

(* [Some e] where [e] is an erased closure ([crane_erase_fn]) over a closed
   lambda: like a marked constant, the same value wherever it is evaluated,
   and an allocation each time. *)
let closed_erase_fn e =
  match e with
  | CPPerase_fn (_, l) when Cpp_print.closed_lambda l -> Some e
  | _ -> None

(* The identifiers [body] declares or reads, which a constant's name must not
   shadow or be shadowed by -- the globals it names included: a constant is
   named after the function that builds it. *)
let names_in body =
  let names = ref Id.Set.empty in
  let add id = names := Id.Set.add id !names in
  let rec fe e =
    ( match e with
    | CPPvar id -> add id
    | CPPglob (r, _, _) -> add (Label.to_id (Common.label_of_r r))
    | _ -> () );
    map_expr fe fs Fun.id e
  and fs s =
    ( match s with Sasgn (id, _, _) | Sdecl (id, _) -> add id | _ -> () );
    map_stmt fe fs Fun.id s
  in
  List.iter (fun s -> ignore (fs s)) body;
  !names

(* [body] with each marked constant read from a [static const] declared at
   its top, one per distinct constant.  The initialiser is evaluated once, as
   a global's is, so it is [unmark]ed. *)
let rec hoist_body body =
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
  let rec fe e =
    match closed_erase_fn e with
    | Some init -> hoisted_var (Id.of_string "erased_fn") init
    | None ->
    match marked e with
    | Some (hint, init) -> hoisted_var hint init
    | None -> map_expr fe fs Fun.id e
  and hoisted_var hint init =
    let init = unmark init in
    let id =
      match List.assoc_opt init !hoisted with
      | Some id -> id
      | None ->
        let id = fresh hint in
        hoisted := (init, id) :: !hoisted;
        id
    in
    CPPvar id
  and fs s = map_stmt fe fs Fun.id s in
  let body' = List.map fs body in
  if !hoisted = [] then body
  else
    List.rev_map
      (fun (init, id) ->
        Sasgn (id, Declare_static (Tconst Tauto), mk_call (CPPrt Crane_rt.Immortal) [init]))
      !hoisted
    @ body'

(* Outside any function -- in a global's initialiser, evaluated once anyway --
   a constant is its initialiser, unless it is inside a lambda there: a
   lambda's body is a function's, and its constants are declared at its top. *)
and unmark e =
  match marked e with
  | Some (_, init) -> unmark init
  | None -> map_expr ~fl:hoist_body unmark unmark_stmt Fun.id e

and unmark_stmt s = map_stmt unmark unmark_stmt Fun.id s

let decl d = map_decl ~fl:hoist_body unmark unmark_stmt Fun.id d
