(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)


type mode =
  | Sequential
  | Reified

type operation =
  | Bind
  | Return

type effect_ = {operation : operation; mode : mode}

let mode_of_monad m = if Table.is_monad_reified m then Reified else Sequential

(* The mode a declaration of type [ty] is generated in: its codomain's
   monad's, and [Sequential], the mode a generation starts in, for a
   codomain that is no monad. *)
let declaration_mode ty =
  match Type_util.codomain_monad ty with
  | Some m -> mode_of_monad m
  | None -> Sequential

let operation_of r =
  if Table.is_bind r then Some Bind else if Table.is_ret r then Some Return else None

type entry = {occurrence : Core.Occurrence.t; effect_ : effect_}

type t = entry list Ref.User.Map.t

let empty = Ref.User.Map.empty

let analyze struc =
  let found = ref empty in
  let record mode (use : Core.Global_use.t) =
    match operation_of use.callee with
    | None -> ()
    | Some operation ->
      let e = {occurrence = Core.Global_use.occurrence use; effect_ = {operation; mode}} in
      found :=
        Ref.User.Map.update use.callee
          (fun l -> Some (e :: Option.default [] l))
          !found
  in
  let rec body mode = function
    | Core.Expr.Global use -> record mode use
    | a -> Core_util.ast_iter (body mode) a
  in
  Modutil.struct_iter
    (fun d ->
      List.iter (fun (fd : Core.Recursion.Definition.t) -> body (declaration_mode fd.type_) fd.body)
        (Core_util.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  !found

let equal =
  Ref.User.Map.equal
    (List.equal (fun a b -> Core.Occurrence.equal a.occurrence b.occurrence && a.effect_ = b.effect_))

let found_count = State.cell State.Unit 0

(* A body's annotations may be rewritten before it is translated, which
   rebuilds every node, so the use's occurrence is what identifies it. *)
let lookup t (use : Core.Global_use.t) =
  match Ref.User.Map.find_opt use.callee t with
  | None -> None
  | Some entries -> (
    let occurrence = Core.Global_use.occurrence use in
    match List.filter (fun e -> Core.Occurrence.equal e.occurrence occurrence) entries with
    | [] -> None
    | e :: rest when List.for_all (fun e' -> e'.effect_ = e.effect_) rest -> Some e.effect_
    | _ -> None )

let tally () = incr found_count

let report t =
  let n = Ref.User.Map.fold (fun _ l acc -> acc + List.length l) t 0 in
  Printf.sprintf "effect operations: %d analysed; translation found %d" n !found_count
