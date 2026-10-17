(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type scope =
  | Global
  | Namespace of string
  | Class of string
  | Parameter of string

type t =
  | Name of {scopes : scope list; base : string}
  | Foreign of string

let scope_text = function
  | Global -> ""
  | Namespace s | Class s | Parameter s -> s

let names_something = function Global -> true | s -> scope_text s <> ""

let name scopes base = Name {scopes = List.filter names_something scopes; base}
let unqualified base = Name {scopes = []; base}
let foreign text = Foreign text

(* Only a foreign name is ever split as text: it is the one kind of name whose
   structure nobody but its author knew. *)
let split_foreign text =
  match String.rindex_opt text ':' with
  | Some i when i > 0 && i < String.length text - 1 && text.[i - 1] = ':' ->
    (String.sub text 0 (i + 1), String.sub text (i + 1) (String.length text - i - 1))
  | _ -> ("", text)

let scopes = function Name n -> n.scopes | Foreign _ -> []
let base = function Name n -> n.base | Foreign text -> snd (split_foreign text)

let is_qualified = function
  | Name n -> n.scopes <> []
  | Foreign text -> String.contains text ':'

let scope_string s = scope_text s ^ "::"

let within s = function
  | Name n -> name (s :: n.scopes) n.base
  | Foreign text -> Foreign (scope_string s ^ text)

let to_string = function
  | Name n -> String.concat "" (List.map (fun s -> scope_text s ^ "::") n.scopes) ^ n.base
  | Foreign text -> text

let inside outer kind n =
  match (outer, n) with
  | Name o, Name n -> name (o.scopes @ (kind o.base :: n.scopes)) n.base
  | _ -> Foreign (to_string outer ^ "::" ^ to_string n)

let map_base f = function
  | Name n -> Name {n with base = f n.base}
  | Foreign text ->
    let prefix, last = split_foreign text in
    Foreign (prefix ^ f last)

let enclosing = function
  | Name {scopes; _} -> (
    match List.rev scopes with
    | last :: rev_outer when last <> Global -> Some (name (List.rev rev_outer) (scope_text last))
    | _ -> None )
  | Foreign _ -> None

(* A qualifier's kind travels in the tag around its text; [written] reads it
   back.  The tag is invisible to every formatter the printer writes with. *)
let tag_prefix = "crane.scope:"
let foreign_tag = "crane.foreign"

let tag_of = function
  | Global -> tag_prefix ^ "g:"
  | Namespace s -> tag_prefix ^ "n:" ^ s
  | Class s -> tag_prefix ^ "c:" ^ s
  | Parameter s -> tag_prefix ^ "p:" ^ s

let scope_of_tag tag =
  let n = String.length tag_prefix in
  if String.length tag < n + 2 || not (String.starts_with ~prefix:tag_prefix tag) then None
  else
    let text = String.sub tag (n + 2) (String.length tag - n - 2) in
    match tag.[n] with
    | 'g' -> Some Global
    | 'n' -> Some (Namespace text)
    | 'c' -> Some (Class text)
    | 'p' -> Some (Parameter text)
    | _ -> None

let pp_scope s = Pp.tag (tag_of s) (Pp.str (scope_string s))

let pp_scopes scopes = Pp.prlist pp_scope scopes

let pp ?(template_keyword = false) = function
  | Name n ->
    let disambiguator = if template_keyword && n.scopes <> [] then Pp.str "template " else Pp.mt () in
    Pp.(pp_scopes n.scopes ++ disambiguator ++ str n.base)
  | Foreign text ->
    let text =
      match split_foreign text with
      | prefix, last when template_keyword && prefix <> "" -> prefix ^ "template " ^ last
      | _ -> text
    in
    Pp.tag foreign_tag (Pp.str text)

let pp_qualifier kind = function
  | Name n -> pp_scopes (n.scopes @ [kind n.base])
  | Foreign text -> Pp.(tag foreign_tag (str text) ++ str "::")

let pp_type_qualifier kind doc =
  Pp.tag (tag_of (kind (Pp.string_of_ppcmds doc))) Pp.(doc ++ str "::")

let equal a b =
  match (a, b) with
  | Name a, Name b -> List.equal ( = ) a.scopes b.scopes && String.equal a.base b.base
  | Foreign a, Foreign b -> String.equal a b
  | _ -> false

type written =
  | Scope of scope
  | Foreign_text of string
  | Untagged of string

let written doc =
  let found = ref [] and run = Buffer.create 64 in
  let flush () =
    if Buffer.length run > 0 then begin
      found := Untagged (Buffer.contents run) :: !found;
      Buffer.clear run
    end
  in
  let emit w = flush (); found := w :: !found in
  let rec go d =
    match Pp.repr d with
    | Pp.Ppcmd_empty | Ppcmd_comment _ -> ()
    | Ppcmd_print_break _ | Ppcmd_force_newline -> Buffer.add_char run ' '
    | Ppcmd_string s -> Buffer.add_string run s
    | Ppcmd_glue ds -> List.iter go ds
    | Ppcmd_box (_, d) -> go d
    | Ppcmd_tag (tag, d) -> (
      match scope_of_tag tag with
      | Some s -> emit (Scope s)
      | None when String.equal tag foreign_tag -> emit (Foreign_text (Pp.string_of_ppcmds d))
      | None -> go d )
  in
  go doc;
  flush ();
  List.rev !found
