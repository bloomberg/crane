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
  | Module of {module_ : ModPath.t; enclosure : enclosure; fields : t; members : t list}
  | Declarations of Pp.t list

and enclosure = Struct of {head : Pp.t; tail : Pp.t} | Out_of_line | In_enclosing_scope

let text d = Text d
let empty = Seq []
let decl ~needs text = Decl {text; needs}
let seq l = Seq l

let rec is_empty = function
  | Text d -> Pp.ismt d
  | Decl {text; needs} -> Pp.ismt text && Needs.is_none needs
  | Seq l -> List.for_all is_empty l
  | Top_level _ -> false
  | Module {enclosure = Struct _; _} -> false
  | Module {fields; members; _} -> members = [] && is_empty fields
  | Declarations l -> l = []

let top_level t = if is_empty t then t else Top_level t

type body = {body_module : ModPath.t; body_members : t list}

let module_body mp members = {body_module = mp; body_members = List.filter (fun t -> not (is_empty t)) members}
let body_is_empty b = b.body_members = []

let module_ enclosure ?(fields = empty) b =
  let t = Module {module_ = b.body_module; enclosure; fields; members = b.body_members} in
  if is_empty t then empty else t

let rec concat sep = function
  | [] -> empty
  | [t] -> t
  | t :: rest -> Seq [t; Text (sep ()); concat sep rest]

let rec needs = function
  | Text _ | Declarations _ -> Needs.none
  | Decl {needs; _} -> needs
  | Seq l -> List.fold_left (fun acc t -> Needs.union acc (needs t)) Needs.none l
  | Top_level t -> needs t
  | Module {fields; members; _} -> needs (Seq (fields :: members))

let cut2 () = Pp.(brk (0, -100000) ++ brk (0, 0))

(* Declarations scheduled in front of a chunk are not part of it: the break
   in front of a member was chosen by the member, before any was placed. *)
let starts_with_doc_comment t =
  let rec first_output = function
    | [] -> None
    | p :: rest -> (
      match Pp.repr p with
      | Ppcmd_empty | Ppcmd_print_break _ -> first_output rest
      | Ppcmd_string text -> Some (String.starts_with ~prefix:"///" text)
      | Ppcmd_glue parts -> (
        match first_output parts with Some _ as result -> result | None -> first_output rest )
      | Ppcmd_box (_, contents) | Ppcmd_tag (_, contents) -> (
        match first_output [contents] with Some _ as result -> result | None -> first_output rest )
      | Ppcmd_force_newline | Ppcmd_comment _ -> Some false )
  in
  let rec first = function
    | [] -> None
    | t :: rest -> (
      let inner =
        match t with
        | Text d | Decl {text = d; _} -> first_output [d]
        | Declarations _ -> None
        | Seq l -> first l
        | Top_level t -> first [t]
        | Module {enclosure = Struct {head; _}; _} -> first_output [head]
        | Module {fields; members; _} -> first (fields :: members)
      in
      match inner with Some _ -> inner | None -> first rest )
  in
  match first [t] with Some result -> result | None -> false

(* A module's members, each two separated by a break, or by a newline where
   the second opens with a doc comment: an unbroken [}///] or [;///] reads
   as a trailing comment, which the formatter cannot repair. *)
let rec join_members = function
  | [] -> []
  | [t] -> [t]
  | t :: (next :: _ as rest) ->
    t :: Text (if starts_with_doc_comment next then Pp.fnl () else cut2 ()) :: join_members rest

let spliced b = Seq (join_members b.body_members)

let rec to_pp = function
  | Text d -> d
  | Decl {text; _} -> text
  | Seq l -> List.fold_left (fun acc t -> Pp.(acc ++ to_pp t)) (Pp.mt ()) l
  | Top_level t -> to_pp t
  | Module {enclosure; fields; members; _} -> (
    let inside = to_pp (Seq (fields :: (if members = [] then [] else join_members members @ [Text (Pp.fnl ())]))) in
    match enclosure with Struct {head; tail} -> Pp.(head ++ inside ++ tail) | Out_of_line | In_enclosing_scope -> inside )
  | Declarations l -> Pp.(prlist_with_sep fnl (fun d -> d) l ++ cut2 ())

type template = {name : string; homed : bool; holder : bool; declaration : Pp.t}
type forward = {struct_ : string; forward_declaration : Pp.t}
type translation_unit = {prologue : Pp.t; sections : t list}
type scheduled = {opening : Pp.t; body : t list}

(* The chunks are numbered in the order written, in both passes: a chunk at
   namespace scope and a member of a struct each take the next number. *)
let schedule ~templates ~forwards u =
  let template_slots = Hashtbl.create 16 and placed_in = Hashtbl.create 16 in
  let struct_slot = Hashtbl.create 16 and defined_in = Hashtbl.create 16 in
  let count = ref 0 in
  (* Where each template and constrained struct is first needed, from the
     innermost chunk at namespace scope [top], the innermost member [member]
     and the innermost module struct [scope] enclosing the declaration that
     needs it; and which structs each chunk at namespace scope defines,
     which a chunk returns.  A homed template is first needed once in each
     struct: a sibling's declaration is not in scope, and the name, a digest
     of the body, is the same in every struct writing the same text. *)
  let rec first_uses ~top ~member ~scope = function
    | Text _ | Declarations _ -> []
    | Seq l -> List.concat_map (first_uses ~top ~member ~scope) l
    | Top_level t ->
      incr count;
      let k = !count in
      let defined = first_uses ~top:(Some k) ~member ~scope t in
      Hashtbl.replace defined_in k defined;
      defined
    | Module {module_; enclosure; fields; members} ->
      let defined = first_uses ~top ~member ~scope fields in
      let scope = match enclosure with Struct _ -> Some module_ | Out_of_line | In_enclosing_scope -> scope in
      defined
      @ List.concat_map
          (fun t ->
            incr count;
            first_uses ~top ~member:(Some !count) ~scope t )
          members
    | Decl {needs; _} ->
      List.iter
        (fun name ->
          match List.find_opt (fun (a : template) -> String.equal a.name name) templates with
          | Some a -> (
            let in_, slot = if a.homed && Option.has_some member then (scope, member) else (None, top) in
            if not (Hashtbl.mem placed_in (name, in_)) then (
              Hashtbl.replace placed_in (name, in_) ();
              Hashtbl.add template_slots slot name ) )
          | None -> () )
        needs.templates;
      List.iter (fun name -> if not (Hashtbl.mem struct_slot name) then Hashtbl.replace struct_slot name top) needs.names;
      needs.defines
  in
  List.iter (fun t -> ignore (first_uses ~top:None ~member:None ~scope:None t)) u.sections;
  let templates_due k =
    let due = List.filter (fun (a : template) -> List.mem a.name (Hashtbl.find_all template_slots k)) templates in
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
    | Module m ->
      let fields = placed m.fields in
      let members =
        List.map
          (fun t ->
            incr count;
            let due = templates_due (Some !count) in
            in_front due (placed t) )
          m.members
      in
      Module {m with fields; members}
  in
  let body = List.map placed u.sections in
  let opening = match templates_due None with [] -> u.prologue | l -> Pp.(u.prologue ++ to_pp (Declarations l)) in
  {opening; body}

let print s = Pp.(s.opening ++ List.fold_left (fun acc t -> acc ++ to_pp t) (mt ()) s.body)

