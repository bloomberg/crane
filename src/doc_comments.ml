(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Extract doc comments from Rocq (.v) source files.

    Parses [(** ... *)] documentation comments and associates each with the
    definition that immediately follows it. The result is stored in a global
    table consulted during C++ pretty-printing to emit [///] comments. *)

(** {2 Global doc-comment table}

    Maps Rocq definition names (as they appear in the source, e.g. ["add"],
    ["MyList"]) to their doc comment text. *)

let doc_table : (string, string) Hashtbl.t = Hashtbl.create 64

let clear () = Hashtbl.clear doc_table

let find_opt name = Hashtbl.find_opt doc_table name

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

(** Try to match a definition keyword at position [i] and extract the definition
    name that follows it. Returns [Some name] or [None]. *)
let try_match_definition s i =
  let len = String.length s in
  let try_keyword kw =
    let klen = String.length kw in
    if i + klen <= len && String.sub s i klen = kw then
      (* Must be followed by whitespace *)
      if
        i + klen < len
        && (s.[i + klen] = ' ' || s.[i + klen] = '\t' || s.[i + klen] = '\n')
      then (
        (* Skip whitespace to find the name *)
        let j = ref (i + klen) in
        while
          !j < len
          && (s.[!j] = ' ' || s.[!j] = '\t' || s.[!j] = '\n' || s.[!j] = '\r')
        do
          incr j
        done;
        (* Collect the identifier *)
        let name_start = !j in
        while
          !j < len
          && s.[!j] <> ' '
          && s.[!j] <> '\t'
          && s.[!j] <> '\n'
          && s.[!j] <> '\r'
          && s.[!j] <> '('
          && s.[!j] <> '{'
          && s.[!j] <> ':'
          && s.[!j] <> '.'
        do
          incr j
        done;
        if !j > name_start then
          Some (String.sub s name_start (!j - name_start))
        else
          None )
      else
        None
    else
      None
  in
  (* Try "Module Type" first (longer match), then other keywords *)
  let rec try_keywords = function
    | [] -> None
    | kw :: rest ->
    match try_keyword kw with
    | Some _ as result -> result
    | None -> try_keywords rest
  in
  try_keywords
    ( "Module Type"
    :: List.filter (fun k -> k <> "Module Type") definition_keywords )

(** Parse a [.v] file and populate the global doc comment table. *)
let parse_file path =
  clear ();
  try
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
            (* Skip whitespace/regular comments after doc comment to find
               definition *)
            let def_start = skip_whitespace_and_comments s next in
            match try_match_definition s def_start with
            | Some name -> Hashtbl.replace doc_table name body
            | None -> () );
        i := next )
      else
        incr i
    done
  with Sys_error _ -> ()

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
