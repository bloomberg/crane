(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Minicpp
open Callable_abi

type t =
  | Deduce_all
  | Explicit_prefix of cpp_type list

(* A value at the kind its parameter declares: a template-template parameter
   takes the template name, a type parameter a type -- a carrier abstraction
   applied at the erased index, as a bare family head is. *)
let adapt kind v =
  match (kind, v) with
  | TTtemplate _, Ttyctor _ -> v
  | TTtemplate _, v -> Ttyctor v
  | _, (Ttyctor body as t) -> (
    match Minicpp.tapply t [Tany] with Tapply _ -> body | applied -> applied )
  | _, v -> v

let value ~instance ~scheme p =
  match p.origin with
  | From_instance k -> instance k
  | From_scheme v -> scheme v
  | From_callable _ | Derived _ -> None

(* What a parameter with no value of its own may be written as, so that a
   later one can be: its default, or the filler a phantom is written with. *)
let filler p =
  match p.write with
  | Defaulted d | Phantom d -> Some d
  | Writable | Deduce_only -> None

let plan abi ~instance ~scheme =
  let valued =
    List.map
      (fun p -> (p, Option.map (adapt p.kind) (value ~instance ~scheme p)))
      (template_head abi)
  in
  (* A parameter is written when it has a value, and a phantom always is:
     nothing deduces it and it has no default. *)
  let required (p, v) =
    Option.has_some v || match p.write with Phantom _ -> true | _ -> false
  in
  let rec prefix = function
    | [] -> []
    | (_, Some v) :: rest -> v :: prefix rest
    | (p, None) :: rest ->
      if List.exists required ((p, None) :: rest) then
        match filler p with
        | Some f -> f :: prefix rest
        | None -> []
      else []
  in
  match prefix valued with
  | [] -> Deduce_all
  | args -> Explicit_prefix args

let to_list = function
  | Deduce_all -> []
  | Explicit_prefix args -> args

let validate abi app =
  let args = to_list app in
  let head = template_head abi in
  let length =
    if List.length args <= List.length head then []
    else ["more arguments than the head has parameters"]
  in
  let kinds =
    List.concat
      (List.mapi
         (fun k a ->
           match List.nth_opt head k with
           | Some {kind = TTtemplate _; _} -> (
             match a with
             | Ttyctor _ -> []
             | _ -> [Printf.sprintf "argument %d is no template name" k] )
           | Some _ -> (
             match a with
             | Ttyctor _ -> [Printf.sprintf "argument %d is a template name at a type parameter" k]
             | Terased _ -> [Printf.sprintf "argument %d writes an erased placeholder" k]
             | _ -> [] )
           | None -> [] )
         args )
  in
  length @ kinds
