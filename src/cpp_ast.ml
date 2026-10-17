(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

module Needs = struct
  type t = {templates : string list; names : string list; defines : string list}

  let none = {templates = []; names = []; defines = []}
  let is_none n = n.templates = [] && n.names = [] && n.defines = []
end

type t =
  | Text of Pp.t
  | Decl of {text : Pp.t; needs : Needs.t}
  | Seq of t list
  | Top_level of t
  | Member of ModPath.t * t

let text d = Text d
let empty = Seq []
let decl ~needs text = Decl {text; needs}
let seq l = Seq l

let rec is_empty = function
  | Text d -> Pp.ismt d
  | Decl {text; needs} -> Pp.ismt text && Needs.is_none needs
  | Seq l -> List.for_all is_empty l
  | Top_level _ | Member _ -> false

let top_level t = if is_empty t then t else Top_level t
let member mp t = if is_empty t then t else Member (mp, t)

let rec concat sep = function
  | [] -> empty
  | [t] -> t
  | t :: rest -> Seq [t; Text (sep ()); concat sep rest]

let top_slot_tag = "crane.slot"
let member_slot_tag = "crane.member:"
let writes_tag = "crane.writes:"
let names_tag = "crane.names:"
let defines_tag = "crane.defines:"

let rec to_pp = function
  | Text d -> d
  | Decl {text; needs} ->
    let tagged tag names doc = match names with [] -> doc | _ -> Pp.tag (tag ^ String.concat " " names) doc in
    text
    |> tagged writes_tag needs.templates
    |> tagged names_tag needs.names
    |> tagged defines_tag needs.defines
  | Seq l -> List.fold_left (fun acc t -> Pp.(acc ++ to_pp t)) (Pp.mt ()) l
  | Top_level t -> Pp.tag top_slot_tag (to_pp t)
  | Member (mp, t) -> Pp.tag (member_slot_tag ^ ModPath.to_string mp) (to_pp t)

type carried =
  | Writes of string list
  | Names of string list
  | Defines of string list

let carried_by tag =
  let names prefix =
    let n = String.length prefix in
    String.split_on_char ' ' (String.sub tag n (String.length tag - n))
  in
  if String.starts_with ~prefix:writes_tag tag then Some (Writes (names writes_tag))
  else if String.starts_with ~prefix:names_tag tag then Some (Names (names names_tag))
  else if String.starts_with ~prefix:defines_tag tag then Some (Defines (names defines_tag))
  else None
