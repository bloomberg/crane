(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Extract doc comments from Rocq (.v) source files.

    Parses [(** ... *)] documentation comments and associates each with the
    definition that immediately follows it. The table is set explicitly via
    [set_table] and queried via [find] during C++ pretty-printing. *)

(** {2 Doc-comment table}

    The table is populated by [parse_file] (which returns a fresh table) and
    installed via [set_table]. Queries go through [find]. *)

let current_table : (string, string) Hashtbl.t ref = ref (Hashtbl.create 0)

(** Install a doc comment table for the current extraction pass. *)
let set_table tbl = current_table := tbl

(** Look up a doc comment by definition name. *)
let find name = Hashtbl.find_opt !current_table name

(** Reset the doc comment table (called between extraction passes). *)
let reset () = current_table := Hashtbl.create 0

(** {2 Comment parser}

    Scans a [.v] file for [(** ... *)] blocks, handling nested comments.
    Associates each doc comment with the definition keyword that immediately
    follows it. *)

(** Definition keywords that introduce a named Rocq declaration. *)
let definition_keywords =
  [
    "Definition";
    "Fixpoint";
    "Inductive";
    "CoInductive";
    "Record";
    "Module";
    "Module Type";
    "Class";
    "Instance";
    "Let";
    "Variant";
    "Axiom";
    "Parameter";
    "Theorem";
    "Lemma";
    "Corollary";
    "Proposition";
    "Example";
    "Program";
  ]

(** Skip whitespace and regular [(* ... *)] comments, returning the index of the
    next non-whitespace, non-comment character. Returns [String.length s] if end
    of string is reached. *)
let rec skip_whitespace_and_comments s i =
  let len = String.length s in
  if i >= len then
    i
  else
    match
      s.[i]
    with
    | ' ' | '\t' | '\n' | '\r' -> skip_whitespace_and_comments s (i + 1)
    | '(' when i + 1 < len && s.[i + 1] = '*' ->
      (* Check if this is a doc comment — if so, don't skip it *)
      if i + 2 < len && s.[i + 2] = '*' && not (i + 3 < len && s.[i + 3] = ')')
      then
        i (* doc comment: stop here *)
      else (* Regular comment: skip over it *)
        let j = skip_nested_comment s (i + 2) 1 in
        skip_whitespace_and_comments s j
    | _ -> i

(** Skip over a nested comment starting after the opening [(*]. [depth] tracks
    nesting level. Returns the index after the closing [*)]. *)
and skip_nested_comment s i depth =
  let len = String.length s in
  if i >= len then
    i
  else if depth = 0 then
    i
  else
    match
      s.[i]
    with
    | '(' when i + 1 < len && s.[i + 1] = '*' ->
      skip_nested_comment s (i + 2) (depth + 1)
    | '*' when i + 1 < len && s.[i + 1] = ')' ->
      skip_nested_comment s (i + 2) (depth - 1)
    | _ -> skip_nested_comment s (i + 1) depth

(** Extract the body of a doc comment starting at index [i] (pointing to the
    opening paren). Returns [(body, end_index)] where [body] is the comment text
    with the doc-comment delimiters stripped, and [end_index] is the index after
    the closing delimiter. *)
let extract_doc_comment s i =
  let len = String.length s in
  let start = i + 3 in
  (* Skip the leading space after the doc-comment opener if present *)
  let start = if start < len && s.[start] = ' ' then start + 1 else start in
  let rec find_end j depth =
    if j >= len then
      (j, j)
    else
      match
        s.[j]
      with
      | '(' when j + 1 < len && s.[j + 1] = '*' -> find_end (j + 2) (depth + 1)
      | '*' when j + 1 < len && s.[j + 1] = ')' ->
        if depth = 1 then
          (j, j + 2)
        else
          find_end (j + 2) (depth - 1)
      | _ -> find_end (j + 1) depth
  in
  let body_end, next = find_end (i + 2) 1 in
  (* Trim trailing whitespace from body *)
  let body_end' = ref (body_end - 1) in
  while
    !body_end' >= start
    && ( s.[!body_end'] = ' '
       || s.[!body_end'] = '\n'
       || s.[!body_end'] = '\r'
       || s.[!body_end'] = '\t' )
  do
    decr body_end'
  done;
  let body =
    if !body_end' >= start then
      String.sub s start (!body_end' - start + 1)
    else
      ""
  in
  (body, next)

(** {3 Identifier scanning}

    Shared helper for collecting an identifier token during doc-comment
    association. *)

(** Test whether [c] is an identifier-terminating character.  These are
    characters that cannot appear inside a Rocq identifier: whitespace,
    parentheses, braces, colon, period, and the constructor bar. *)
let is_ident_delim c =
  match c with
  | ' ' | '\t' | '\n' | '\r' | '(' | '{' | ':' | '.' | '|' -> true
  | _ -> false

(** Collect a contiguous identifier starting at position [i] in [s], stopping
    at any {!is_ident_delim} character.  Returns [Some (name, end_pos)] where
    [end_pos] is one past the last character of the identifier, or [None] if
    [i] is already at a delimiter or past the end of [s]. *)
let collect_identifier s i =
  let len = String.length s in
  let j = ref i in
  while !j < len && not (is_ident_delim s.[!j]) do
    incr j
  done;
  if !j > i then Some (String.sub s i (!j - i), !j) else None

(** Skip horizontal whitespace (spaces and tabs) starting at [i].
    Returns the index of the first non-blank character. *)
let skip_hspace s i =
  let len = String.length s in
  let j = ref i in
  while !j < len && (s.[!j] = ' ' || s.[!j] = '\t') do
    incr j
  done;
  !j

(** Skip all whitespace (spaces, tabs, newlines) starting at [i].
    Returns the index of the first non-whitespace character. *)
let skip_all_whitespace s i =
  let len = String.length s in
  let j = ref i in
  while
    !j < len
    && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\n' || s.[!j] = '\r')
  do
    incr j
  done;
  !j

(** {3 Name matchers}

    Each matcher attempts to identify the Rocq name that a doc comment should
    be associated with.  They are tried in order by {!parse_file}:
    definition keyword, then constructor bar, then record field. *)

(** Try to match a definition keyword at position [i] and extract the
    definition name that follows it.  Returns [Some name] or [None]. *)
let try_match_definition s i =
  let len = String.length s in
  let try_keyword kw =
    let klen = String.length kw in
    if i + klen <= len && String.sub s i klen = kw then
      (* Must be followed by whitespace *)
      if
        i + klen < len
        && (s.[i + klen] = ' ' || s.[i + klen] = '\t' || s.[i + klen] = '\n')
      then
        let after_ws = skip_all_whitespace s (i + klen) in
        collect_identifier s after_ws |> Option.map fst
      else None
    else None
  in
  (* Try "Module Type" first (longer match), then other keywords *)
  let rec try_keywords = function
    | [] -> None
    | kw :: rest -> (
      match try_keyword kw with
      | Some _ as result -> result
      | None -> try_keywords rest )
  in
  try_keywords
    ( "Module Type"
    :: List.filter (fun k -> k <> "Module Type") definition_keywords )

(** Try to match a constructor line at position [i]: [| CtorName].
    Matches the ['|'] separator, skips horizontal whitespace, then collects the
    constructor identifier.  Returns [Some name] or [None]. *)
let try_match_constructor s i =
  let len = String.length s in
  if i < len && s.[i] = '|' then
    let after_ws = skip_hspace s (i + 1) in
    collect_identifier s after_ws |> Option.map fst
  else None

(** Try to match a record field at position [i]: [fieldname : Type].
    Collects an identifier, then verifies it is followed by (optional
    whitespace and) a colon.  Returns [Some name] or [None]. *)
let try_match_field s i =
  let len = String.length s in
  match collect_identifier s i with
  | None -> None
  | Some (name, j) ->
    let after_ws = skip_hspace s j in
    if after_ws < len && s.[after_ws] = ':' then Some name else None

(** Try each name matcher in order until one succeeds.  Returns [Some name]
    from the first matcher that recognises the text at position [i], or [None]
    if none match. *)
let try_match_name s i =
  match try_match_definition s i with
  | Some _ as hit -> hit
  | None -> (
    match try_match_constructor s i with
    | Some _ as hit -> hit
    | None -> try_match_field s i )

(** Parse a [.v] file and return a fresh doc comment table mapping definition
    names to their comment text.

    Scans linearly for [(** ... *)] blocks.  For each one, skips any
    intervening whitespace and regular comments, then uses {!try_match_name}
    to associate the comment with the immediately following definition,
    constructor, or record field. *)
let parse_file path =
  let tbl = Hashtbl.create 64 in
  ( try
      let ic = open_in path in
      let len = in_channel_length ic in
      let s = Bytes.create len in
      really_input ic s 0 len;
      close_in ic;
      let s = Bytes.to_string s in
      let slen = String.length s in
      let i = ref 0 in
      while !i < slen do
        let pos = !i in
        (* Look for doc comments *)
        if
          pos + 3 < slen
          && s.[pos] = '('
          && s.[pos + 1] = '*'
          && s.[pos + 2] = '*'
          (* Exclude the degenerate case which is not a doc comment *)
          && not (pos + 3 < slen && s.[pos + 3] = ')')
        then (
          let body, next = extract_doc_comment s pos in
          ( if body <> "" then
              let def_start = skip_whitespace_and_comments s next in
              match try_match_name s def_start with
              | Some name -> Hashtbl.replace tbl name body
              | None -> () );
          i := next )
        else
          incr i
      done
    with Sys_error _ -> () );
  tbl

(** {2 Bracket reference translation}

    Translates rocq doc bracket references like [[add]] in doc comment text to
    their C++ names using a provided name-translation function. *)

(** Translate bracket references [[name]] in a doc comment string. The
    [translate] function maps a Rocq name to its C++ equivalent (or returns the
    name unchanged if no translation is found). *)
let translate_brackets ~translate text =
  let len = String.length text in
  let buf = Buffer.create len in
  let i = ref 0 in
  while !i < len do
    if text.[!i] = '[' then (
      (* Find the matching ']', handling nesting *)
      let start = !i + 1 in
      let j = ref start in
      let depth = ref 1 in
      while !j < len && !depth > 0 do
        ( match text.[!j] with
        | '[' -> incr depth
        | ']' -> decr depth
        | _ -> () );
        if !depth > 0 then incr j
      done;
      if !depth = 0 then (
        let content = String.sub text start (!j - start) in
        let translated = translate content in
        Buffer.add_string buf translated;
        i := !j + 1 )
      else (
        Buffer.add_char buf '[';
        i := start ) )
    else (
      Buffer.add_char buf text.[!i];
      incr i )
  done;
  Buffer.contents buf

(** {2 Formatting}

    Shared helper for rendering doc comment text as C++ [///] comment lines. *)

(** Format a doc comment string as a list of [///]-prefixed lines. Translates
    bracket references [[name]] by stripping the brackets. *)
let format_as_cpp_lines text =
  let text = translate_brackets ~translate:(fun s -> s) text in
  let lines = String.split_on_char '\n' text in
  List.map
    (fun line ->
      let trimmed = String.trim line in
      if trimmed = "" then "///" else "/// " ^ trimmed )
    lines
