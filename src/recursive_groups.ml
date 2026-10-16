(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml
module Map = Ref.User.Map
module Set = Ref.User.Set
module Tbl = Ref.User.Tbl

(* Each member of a group, mapped to the group's members in definition
   order. *)
type t = Names.GlobRef.t list Map.t

let empty = Map.empty

let analyze struc =
  let defs = ref [] in
  Modutil.struct_iter
    (fun d -> List.iter (fun fd -> defs := fd :: !defs) (Mlutil.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let defs = List.rev !defs in
  let position = Tbl.create 64 in
  List.iteri (fun i fd -> Tbl.replace position fd.fd_ref i) defs;
  let callees body =
    let found = ref Set.empty in
    let rec scan = function
      | MLglob {callee = r; _} when Tbl.mem position r -> found := Set.add r !found
      | a -> Mlutil.ast_iter scan a
    in
    scan body;
    !found
  in
  let edges = Tbl.create 64 in
  List.iter (fun fd -> Tbl.replace edges fd.fd_ref (callees fd.fd_body)) defs;
  let succ r = Option.default Set.empty (Tbl.find_opt edges r) in
  (* Tarjan's algorithm. *)
  let index = Tbl.create 64 and low = Tbl.create 64 and on_stack = Tbl.create 64 in
  let counter = ref 0 and stack = ref [] and groups = ref Map.empty in
  let rec visit v =
    Tbl.replace index v !counter;
    Tbl.replace low v !counter;
    incr counter;
    stack := v :: !stack;
    Tbl.replace on_stack v ();
    Set.iter
      (fun w ->
        if not (Tbl.mem index w) then (
          visit w;
          Tbl.replace low v (min (Tbl.find low v) (Tbl.find low w)) )
        else if Tbl.mem on_stack w then Tbl.replace low v (min (Tbl.find low v) (Tbl.find index w)) )
      (succ v);
    if Tbl.find low v = Tbl.find index v then begin
      let rec pop acc =
        match !stack with
        | w :: rest ->
          stack := rest;
          Tbl.remove on_stack w;
          if Ref.User.equal w v then w :: acc else pop (w :: acc)
        | [] -> acc
      in
      let component = pop [] in
      let recursive = match component with [w] -> Set.mem w (succ w) | _ -> true in
      if recursive then
        let members =
          List.sort (fun a b -> compare (Tbl.find position a) (Tbl.find position b)) component
        in
        List.iter (fun m -> groups := Map.add m members !groups) members
    end
  in
  List.iter (fun fd -> if not (Tbl.mem index fd.fd_ref) then visit fd.fd_ref) defs;
  !groups

let group t r = Map.find_opt r t

let in_group t r r' =
  match Map.find_opt r t with Some ms -> List.exists (Ref.User.equal r') ms | None -> false

let equal = Map.equal (List.equal Ref.User.equal)

let current : t ref = State.cell State.Extraction empty
let install t = current := t
let installed () = !current
