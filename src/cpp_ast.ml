(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

module Needs = struct
  type t = {templates : string list; names : string list; defines : string list}

  let none = {templates = []; names = []; defines = []}
  let is_none n = n.templates = [] && n.names = [] && n.defines = []
  let union a b = {templates = a.templates @ b.templates; names = a.names @ b.names; defines = a.defines @ b.defines}
end

type t =
  | Text of Pp.t
  | Decl of {text : Pp.t; needs : Needs.t}
  | Seq of t list
  | Top_level of t
  | Member of ModPath.t * t
  | Declarations of Pp.t list

let text d = Text d
let empty = Seq []
let decl ~needs text = Decl {text; needs}
let seq l = Seq l

let rec is_empty = function
  | Text d -> Pp.ismt d
  | Decl {text; needs} -> Pp.ismt text && Needs.is_none needs
  | Seq l -> List.for_all is_empty l
  | Top_level _ | Member _ -> false
  | Declarations l -> l = []

let top_level t = if is_empty t then t else Top_level t
let member mp t = if is_empty t then t else Member (mp, t)

let rec concat sep = function
  | [] -> empty
  | [t] -> t
  | t :: rest -> Seq [t; Text (sep ()); concat sep rest]

let rec needs = function
  | Text _ | Declarations _ -> Needs.none
  | Decl {needs; _} -> needs
  | Seq l -> List.fold_left (fun acc t -> Needs.union acc (needs t)) Needs.none l
  | Top_level t | Member (_, t) -> needs t

let cut2 () = Pp.(brk (0, -100000) ++ brk (0, 0))

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
  | Declarations l -> Pp.(prlist_with_sep fnl (fun d -> d) l ++ cut2 ())

type template = {name : string; home : ModPath.t option; holder : bool; declaration : Pp.t}
type forward = {struct_ : string; forward_declaration : Pp.t}
type translation_unit = {prologue : Pp.t; sections : t list}
type scheduled = {opening : Pp.t; body : t list}

(* The chunks are numbered in the order written, in both passes: a chunk at
   namespace scope and a member of a struct each take the next number. *)
let schedule ~templates ~forwards u =
  let template_slot = Hashtbl.create 16 and struct_slot = Hashtbl.create 16 and defined_in = Hashtbl.create 16 in
  let count = ref 0 in
  (* Where each template and constrained struct is first needed, from the
     innermost chunk at namespace scope [top] and the members [members]
     enclosing the declaration that needs it, innermost first; and which
     structs each chunk at namespace scope defines, which a chunk returns. *)
  let rec first_uses ~top ~members = function
    | Text _ | Declarations _ -> []
    | Seq l -> List.concat_map (first_uses ~top ~members) l
    | Top_level t ->
      incr count;
      let k = !count in
      let defined = first_uses ~top:(Some k) ~members t in
      Hashtbl.replace defined_in k defined;
      defined
    | Member (mp, t) ->
      incr count;
      first_uses ~top ~members:((mp, !count) :: members) t
    | Decl {needs; _} ->
      List.iter
        (fun name ->
          match List.find_opt (fun (a : template) -> String.equal a.name name) templates with
          | Some a when not (Hashtbl.mem template_slot name) ->
            let homed =
              Option.bind a.home (fun home ->
                  List.find_map (fun (mp, k) -> if ModPath.equal mp home then Some k else None) members )
            in
            Hashtbl.replace template_slot name (if Option.has_some homed then homed else top)
          | Some _ | None -> () )
        needs.templates;
      List.iter (fun name -> if not (Hashtbl.mem struct_slot name) then Hashtbl.replace struct_slot name top) needs.names;
      needs.defines
  in
  List.iter (fun t -> ignore (first_uses ~top:None ~members:[] t)) u.sections;
  let templates_due k =
    let due = List.filter (fun (a : template) -> Hashtbl.find_opt template_slot a.name = Some k) templates in
    let holders, aliases = List.partition (fun (a : template) -> a.holder) due in
    List.map (fun (a : template) -> a.declaration) (holders @ aliases)
  in
  let forwards_due k =
    List.filter_map
      (fun f ->
        match Hashtbl.find_opt struct_slot f.struct_ with
        | Some (Some k') when k' = k && not (List.mem f.struct_ (Hashtbl.find defined_in k)) ->
          Some f.forward_declaration
        | _ -> None )
      forwards
  in
  let in_front due t = match due with [] -> t | l -> Seq [Declarations l; t] in
  count := 0;
  let rec placed = function
    | (Text _ | Decl _ | Declarations _) as t -> t
    | Seq l -> Seq (List.map placed l)
    | Top_level t ->
      incr count;
      let k = !count in
      let due = forwards_due k @ templates_due (Some k) in
      in_front due (Top_level (placed t))
    | Member (mp, t) ->
      incr count;
      let due = templates_due (Some !count) in
      in_front due (Member (mp, placed t))
  in
  let body = List.map placed u.sections in
  let opening = match templates_due None with [] -> u.prologue | l -> Pp.(u.prologue ++ to_pp (Declarations l)) in
  {opening; body}

let print s = Pp.(s.opening ++ List.fold_left (fun acc t -> acc ++ to_pp t) (mt ()) s.body)

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
