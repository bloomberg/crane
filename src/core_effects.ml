(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

type mode =
  | Sequential
  | Reified

type operation =
  | Bind
  | Return

type effect = {operation : operation; mode : mode}

let mode_of_monad m = if Table.is_monad_reified m then Reified else Sequential

let declaration_mode ty =
  match Ml_type_util.ml_codomain ty with
  | Tglob (m, _, _) when Table.is_monad m -> mode_of_monad m
  | _ -> Sequential

let operation_of r =
  if Table.is_bind r then Some Bind else if Table.is_ret r then Some Return else None

type entry = {occurrence : Occurrence.t; effect : effect}

type t = entry list Ref.User.Map.t

let empty = Ref.User.Map.empty

let analyze struc =
  let found = ref empty in
  let record mode use =
    match operation_of use.callee with
    | None -> ()
    | Some operation ->
      let e = {occurrence = Global_use.occurrence use; effect = {operation; mode}} in
      found :=
        Ref.User.Map.update use.callee
          (fun l -> Some (e :: Option.default [] l))
          !found
  in
  let rec body mode = function
    | MLglob use -> record mode use
    | a -> Mlutil.ast_iter (body mode) a
  in
  Modutil.struct_iter
    (fun d -> List.iter (fun fd -> body (declaration_mode fd.fd_type) fd.fd_body) (Mlutil.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  !found

let equal =
  Ref.User.Map.equal
    (List.equal (fun a b -> Occurrence.equal a.occurrence b.occurrence && a.effect = b.effect))

let installed = State.cell State.Unit empty

type counts = {found : int; decided : int}

let counts = State.cell State.Unit {found = 0; decided = 0}

let install t =
  installed := t;
  counts := {found = 0; decided = 0}

(* A body's annotations may be rewritten before it is translated, which
   rebuilds every node, so the use's occurrence is what identifies it. *)
let find use =
  match Ref.User.Map.find_opt use.callee !installed with
  | None -> None
  | Some entries -> (
    let occurrence = Global_use.occurrence use in
    match List.filter (fun e -> Occurrence.equal e.occurrence occurrence) entries with
    | [] -> None
    | e :: rest when List.for_all (fun e' -> e'.effect = e.effect) rest -> Some e.effect
    | _ -> None )

let tally ~found =
  counts :=
    if found then {!counts with found = !counts.found + 1}
    else {!counts with decided = !counts.decided + 1}

let report () =
  let n = Ref.User.Map.fold (fun _ l acc -> acc + List.length l) !installed 0 in
  Printf.sprintf "effect operations: %d analysed; translation found %d, decided %d itself" n
    !counts.found !counts.decided
