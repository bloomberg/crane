(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type 'a t = {head : 'a; tail : 'a list}

let singleton x = {head = x; tail = []}

let of_list_exn = function
  | [] -> invalid_arg "Nonempty.of_list_exn"
  | head :: tail -> {head; tail}

let to_list {head; tail} = head :: tail

let map f {head; tail} =
  let head = f head in
  {head; tail = List.map f tail}

let iter f {head; tail} = f head; List.iter f tail

let exists p {head; tail} = p head || List.exists p tail

let for_all p {head; tail} = p head && List.for_all p tail
