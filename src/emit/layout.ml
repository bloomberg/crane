(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Layout of generated C++ source.

    The printer writes each construct as a stream of tokens with the spacing
    between them decided, but no indentation and no line width: where it
    breaks lines is incidental.  This module turns that stream into the text
    Crane writes, in the LLVM style as clang-format applies it with
    [SeparateDefinitionBlocks: Always]:

    - the stream is cut into lines the way clang-format cuts it (one
      statement, declaration or block opening per line), ignoring the line
      breaks of the input except for blank lines, which are kept, one at
      most;
    - blocks are indented by two, access specifiers and case labels one
      level out, preprocessor directives at the first column;
    - a function or lambda body holding at most one statement, an empty
      record and a short enum are merged into the line opening them when
      they fit;
    - a line longer than {!column_limit} is broken by a document layout
      (Wadler and Oppen, with the extensions clang-format's choices call
      for): bracketed lists are packed and aligned after the opening
      bracket, or broken after it and indented by four; binary operands
      are aligned; the right side of an assignment moves to its own line
      when that lets it fit; a conditional breaks before [:], aligned with
      [?]; a long string literal is split between words;
    - definitions are separated by a blank line, and an access specifier
      starting a new group of members is preceded by one;
    - each run of [#include] lines is sorted and duplicates dropped.

    Nested brackets are where layouts go wrong, and three rules keep them
    in check, all after clang-format:

    - a list breaking after its opening bracket indents four columns past
      the start of the operand or list item it is in, not past the bracket:
      brackets opened on one line share one continuation, so indentation
      grows by four a line however many brackets the line opens
      ({!out.last_space});
    - a choice between layouts (aligned or broken after the bracket, the
      right side of an assignment on its line or the next, an item on this
      line or the next) is made by laying both out on trial, the choices
      inside on trial too, two levels deep, and ranking them by columns past
      the limit, then line breaks inside template arguments, then lines
      ({!measure});
    - lists nested deeper than the width left could hold at four columns a
      level are laid out flat: breaking them would only add lines, so a
      chain thousands deep takes one line, not one a level
      ({!nests_deeper}).

    The layout reads tokens only, so it applies equally to text a custom
    extraction supplies.  It is pure: text in, text out. *)

(** The width lines are broken to fit. *)
let column_limit = 80

(** The indentation of a block's contents past the line opening it. *)
let indent_width = 2

(** The indentation of a continuation line past the line it continues. *)
let continuation_width = 4

(** {2 Tokens} *)

type kind =
  | Word  (** an identifier, keyword or number *)
  | Literal  (** a string or character literal *)
  | Punct
  | Line_comment
  | Block_comment
  | Directive  (** a whole preprocessor line *)

(** A token of the input.  [space] records whether whitespace preceded it
    there, which tells a reference declarator ([T& x]) from a binary
    operator ([a & b]) and a template argument list ([f<T>]) from a
    comparison ([a < b]); [gap] is whether the output writes a space before
    it, which starts as [space] and is then normalised. *)
type token = {
  text : string;
  kind : kind;
  space : bool;
  lines : int;  (** line breaks before the token in the input *)
  column : int;  (** the token's column in the input *)
  mutable gap : bool;
}

let is_ident_start c =
  c = '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || Char.code c >= 128

let is_digit c = c >= '0' && c <= '9'
let is_ident_char c = is_ident_start c || is_digit c

let puncts3 = ["<<="; ">>="; "<=>"; "->*"; "..."]

(** Two-character punctuators.  [>>] is not one: it is lexed as two [>],
    which close two template argument lists far more often than they shift. *)
let puncts2 =
  [ "::"; "->"; "++"; "--"; "<<"; "&&"; "||"; "=="; "!="; "<="; ">="; "+="; "-="; "*="; "/="; "%="; "&="; "|="; "^=";
    ".*"; "##" ]

let string_prefixes = ["L"; "u"; "U"; "u8"; "R"; "LR"; "uR"; "UR"; "u8R"]

(** The index of the first occurrence of [sub] in [s] at or after [from]. *)
let find_sub s sub from =
  let n = String.length s and m = String.length sub in
  let rec go i =
    if i + m > n then None else if String.sub s i m = sub then Some i else go (i + 1)
  in
  go from

(** Splits [s] into tokens. *)
let lex (s : string) : token array =
  let n = String.length s in
  let toks = ref [] in
  let i = ref 0 and line_start = ref 0 in
  let space = ref true and lines = ref 0 and at_line_start = ref true in
  let emit kind start stop =
    let text = String.sub s start (stop - start) in
    toks := {text; kind; space = !space; lines = !lines; column = start - !line_start; gap = !space} :: !toks;
    space := false;
    lines := 0;
    at_line_start := false;
    i := stop
  in
  let rec quoted q j =
    if j >= n || s.[j] = '\n' then j
    else if s.[j] = '\\' then quoted q (j + 2)
    else if s.[j] = q then j + 1
    else quoted q (j + 1)
  in
  let raw_string j =
    match String.index_from_opt s (j + 1) '(' with
    | None -> quoted '"' (j + 1)
    | Some p -> (
      let close = ")" ^ String.sub s (j + 1) (p - j - 1) ^ "\"" in
      match find_sub s close (p + 1) with
      | Some q -> q + String.length close
      | None -> n )
  in
  let suffix j =
    let k = ref j in
    while !k < n && is_ident_char s.[!k] do incr k done;
    !k
  in
  let note_newlines start stop =
    for k = start to stop - 1 do
      if s.[k] = '\n' then line_start := k + 1
    done
  in
  while !i < n do
    let c = s.[!i] in
    let next = if !i + 1 < n then s.[!i + 1] else '\000' in
    if c = '\n' then (
      incr lines;
      space := true;
      at_line_start := true;
      incr i;
      line_start := !i )
    else if c = ' ' || c = '\t' || c = '\r' || c = '\012' then (
      space := true;
      incr i )
    else if c = '#' && !at_line_start then (
      let j = ref !i and continued = ref true in
      while !continued do
        while !j < n && s.[!j] <> '\n' do incr j done;
        if !j < n && !j > !i && s.[!j - 1] = '\\' then incr j else continued := false
      done;
      let stop = ref !j in
      while !stop > !i && (s.[!stop - 1] = ' ' || s.[!stop - 1] = '\t' || s.[!stop - 1] = '\r') do decr stop done;
      let start = !i in
      emit Directive start !stop;
      note_newlines start !stop;
      i := !j )
    else if c = '/' && next = '/' then (
      let j = ref !i in
      while !j < n && s.[!j] <> '\n' do incr j done;
      let stop = ref !j in
      while !stop > !i && (s.[!stop - 1] = ' ' || s.[!stop - 1] = '\t' || s.[!stop - 1] = '\r') do decr stop done;
      emit Line_comment !i !stop;
      i := !j )
    else if c = '/' && next = '*' then (
      let stop = match find_sub s "*/" (!i + 2) with Some q -> q + 2 | None -> n in
      let start = !i in
      emit Block_comment start stop;
      note_newlines start stop )
    else if is_digit c || (c = '.' && is_digit next) then (
      let j = ref (!i + 1) in
      let continues () =
        !j < n
        &&
        let d = s.[!j] in
        is_ident_char d || d = '.'
        || (d = '\'' && !j + 1 < n && is_ident_char s.[!j + 1])
        || ((d = '+' || d = '-') && String.contains "eEpP" s.[!j - 1])
      in
      while continues () do incr j done;
      emit Word !i !j )
    else if is_ident_start c then (
      let j = suffix !i in
      let word = String.sub s !i (j - !i) in
      if j < n && s.[j] = '"' && List.mem word string_prefixes then
        let stop = if word.[String.length word - 1] = 'R' then raw_string j else quoted '"' (j + 1) in
        emit Literal !i (suffix stop)
      else if j < n && s.[j] = '\'' && List.mem word ["L"; "u"; "U"; "u8"] then
        emit Literal !i (suffix (quoted '\'' (j + 1)))
      else emit Word !i j )
    else if c = '"' then emit Literal !i (suffix (quoted '"' (!i + 1)))
    else if c = '\'' then emit Literal !i (suffix (quoted '\'' (!i + 1)))
    else
      let has p = !i + String.length p <= n && String.sub s !i (String.length p) = p in
      match List.find_opt has puncts3 with
      | Some p -> emit Punct !i (!i + String.length p)
      | None -> (
        match List.find_opt has puncts2 with
        | Some _ -> emit Punct !i (!i + 2)
        | None -> emit Punct !i (!i + 1) )
  done;
  Array.of_list (List.rev !toks)

let is_punct t p = t.kind = Punct && t.text = p
let is_word t w = t.kind = Word && t.text = w

(** Keywords after which a token is an operand, not a declarator. *)
let operand_keywords =
  ["return"; "throw"; "co_return"; "co_yield"; "co_await"; "case"; "delete"; "new"; "operator"; "sizeof"]

(** The output spacing, from the input's: [template <], and a reference or
    pointer declarator next to its name ([T &x], [auto *p], [const A &>])
    rather than its type. *)
let normalise_spacing (toks : token array) =
  let n = Array.length toks in
  for k = 0 to n - 1 do
    let t = toks.(k) in
    let prev = if k > 0 then Some toks.(k - 1) else None in
    let next = if k + 1 < n then Some toks.(k + 1) else None in
    ( match prev with
    | Some p when is_word p "template" && is_punct t "<" -> t.gap <- true
    | _ -> () );
    if t.kind = Punct && (t.text = "&" || t.text = "&&" || t.text = "*") && not t.space then
      match prev with
      | Some p
        when (p.kind = Word && not (List.mem p.text operand_keywords)) || is_punct p ">" ->
        t.gap <- true;
        ( match next with
        | Some x when x.space && (x.kind = Word || is_punct x "[" || is_punct x "...") -> x.gap <- false
        | _ -> () )
      | _ -> ()
  done

(** {2 Lines}

    The token stream cut into clang-format's unwrapped lines: an item is one
    line of the output unless it opens a block, whose contents are items
    again. *)

type block_kind =
  | Control  (** the body of [if], [else], [for], [while], [do], [switch], [try], [catch] *)
  | Record  (** a struct, class or union *)
  | Enum
  | Namespace  (** also [extern "C"] *)
  | Lambda
  | Function
  | Requirement  (** the body of a requires-expression *)
  | Compound  (** a compound requirement [{ e }] in a requires-expression *)
  | Plain  (** a block statement *)

type item =
  | Stmt of elem list  (** a statement, declaration or definition *)
  | Pp of token  (** a preprocessor directive *)
  | Comment of token  (** a comment on a line of its own *)
  | Label of token list  (** an access specifier or a case label *)
  | Blank  (** an empty line *)

and elem =
  | Tok of token
  | Block of block

and block = {
  bkind : block_kind;
  opening : token;
  lead : token option;  (** a comment on the line of the opening brace *)
  items : item list;
  closing : token option;
}

type parser = {
  toks : token array;
  mutable pos : int;
}

let peek p = if p.pos < Array.length p.toks then Some p.toks.(p.pos) else None
let advance p = p.pos <- p.pos + 1

(** Words a [{] after which opens a braced list, not a block. *)
let list_keywords = ["return"; "throw"; "co_return"; "co_yield"; "case"]

(** Whether the [{] [t], after [prev] in the statement, opens a block rather
    than a braced initialiser: the printer writes a space before a block's
    brace and none before an initialiser's, except after a word that takes
    a braced list as its operand. *)
let opens_block ~prev ~lambda t =
  match prev with
  | None -> true
  | Some p -> (
    (lambda && (t.space || is_punct p ")" || is_punct p "]"))
    || is_punct p ")"
    || t.space
       &&
       match p.kind with
       | Word -> not (List.mem p.text list_keywords)
       | Literal -> true
       | Punct -> List.mem p.text [")"; "]"; ">"; "}"; "&"; "&&"; "*"]
       | _ -> false )

let control_words = ["if"; "else"; "for"; "while"; "do"; "switch"; "try"; "catch"]

(** The kind of the block a statement's [header] tokens open. *)
let classify ~lambda ~depth (header : token list) =
  let has w = List.exists (fun t -> is_word t w) header in
  let has_paren = List.exists (fun t -> is_punct t "(") header in
  if lambda || depth > 0 then Lambda
  else if header = [] then Plain
  else
    match header with
    | t :: _ when t.kind = Word && List.mem t.text control_words -> Control
    | _ -> (
      match List.rev header with
      | t :: _ when is_word t "requires" -> Requirement
      | t :: _ when is_punct t ")" && has "requires" ->
        (* [requires (T x) {]: the parameter list of a requires-expression *)
        let rec before_paren depth = function
          | x :: rest when is_punct x ")" -> before_paren (depth + 1) rest
          | x :: rest when is_punct x "(" -> if depth = 1 then rest else before_paren (depth - 1) rest
          | _ :: rest -> before_paren depth rest
          | [] -> []
        in
        ( match before_paren 0 (List.rev header) with
        | x :: _ when is_word x "requires" -> Requirement
        | _ -> Function )
      | _ ->
        if has "namespace" || (has "extern" && List.exists (fun t -> t.kind = Literal) header) then Namespace
        else if has "enum" then Enum
        else if (has "struct" || has "class" || has "union") && not has_paren then Record
        else Function )

(** Whether a statement goes on after the block of kind [k] just closed. *)
let continues_after k ~header next =
  match next with
  | None -> false
  | Some t -> (
    if is_word t "else" || is_word t "catch" || is_punct t ";" then true
    else if is_word t "while" then (match header with h :: _ -> is_word h "do" | [] -> false)
    else
      match k with
      | Record | Enum | Lambda | Requirement | Compound -> not (is_punct t "}")
      | Control | Namespace | Function | Plain -> false )

(** Whether the [[] [t] after [prev] introduces a lambda rather than
    subscripting, or opening an attribute or a structured binding. *)
let lambda_introducer ~prev ~next =
  (match next with Some x -> not (is_punct x "[") | None -> true)
  &&
  match prev with
  | None -> true
  | Some p -> (
    match p.kind with
    | Word -> List.mem p.text ["return"; "co_return"; "co_yield"; "throw"]
    | Punct -> not (List.mem p.text [")"; "]"; ">"; "["; "&"; "&&"; "*"])
    | _ -> false )

let rec parse_items p ~inside ~kind : item list =
  let items = ref [] in
  let fin = ref false in
  let attach t =
    match !items with
    | Stmt elems :: rest -> items := Stmt (elems @ [Tok t]) :: rest
    | _ -> items := Comment t :: !items
  in
  while not !fin do
    match peek p with
    | None -> fin := true
    | Some t when inside && is_punct t "}" -> fin := true
    | Some t ->
      if t.lines >= 2 && (inside || !items <> []) then items := Blank :: !items;
      if t.kind = Directive then (
        advance p;
        items := Pp t :: !items )
      else if (t.kind = Line_comment || t.kind = Block_comment) && t.lines = 0 && !items <> [] then (
        advance p;
        attach t )
      else if t.kind = Line_comment || t.kind = Block_comment then (
        advance p;
        items := Comment t :: !items )
      else if
        t.kind = Word
        && List.mem t.text ["public"; "private"; "protected"]
        && p.pos + 1 < Array.length p.toks
        && is_punct p.toks.(p.pos + 1) ":"
      then (
        let colon = p.toks.(p.pos + 1) in
        p.pos <- p.pos + 2;
        items := Label [t; colon] :: !items )
      else if (is_word t "case" || is_word t "default") && kind = Control then (
        let label = ref [t] in
        advance p;
        let depth = ref 0 and stop = ref false in
        while not !stop do
          match peek p with
          | None -> stop := true
          | Some x ->
            advance p;
            label := x :: !label;
            if is_punct x "(" || is_punct x "[" then incr depth
            else if is_punct x ")" || is_punct x "]" then decr depth
            else if is_punct x ":" && !depth = 0 then stop := true
        done;
        items := Label (List.rev !label) :: !items )
      else items := Stmt (parse_stmt p ~kind ~comma:(kind = Enum)) :: !items
  done;
  List.rev !items

and parse_stmt ?(comma = false) p ~kind : elem list =
  let elems = ref [] in
  let header = ref [] (* tokens since the last block, reversed *) in
  let stack = ref [] in
  let lambdas = ref [] in
  let prev = ref None in
  let push t =
    elems := Tok t :: !elems;
    header := t :: !header;
    prev := Some t;
    advance p
  in
  let fin = ref false in
  while not !fin do
    match peek p with
    | None -> fin := true
    | Some t -> (
      let depth = List.length !stack in
      let at_start = !elems = [] in
      match t.kind with
      | Directive -> if at_start then push t else fin := true
      | Line_comment when not at_start ->
        push t
      | _ ->
        if (is_punct t ";" || (comma && is_punct t ",")) && !stack = [] then (
          push t;
          fin := true )
        else if is_punct t "(" || is_punct t "[" then (
          let next = if p.pos + 1 < Array.length p.toks then Some p.toks.(p.pos + 1) else None in
          if is_punct t "[" && lambda_introducer ~prev:!prev ~next then lambdas := depth :: !lambdas;
          stack := t.text :: !stack;
          push t )
        else if is_punct t ")" || is_punct t "]" then (
          (match !stack with _ :: rest -> stack := rest | [] -> ());
          push t )
        else if is_punct t "{" then (
          let lambda = List.mem depth !lambdas in
          let compound = at_start && kind = Requirement in
          if compound || opens_block ~prev:!prev ~lambda t then (
            let hdr = List.rev !header in
            let bkind = if compound then Compound else classify ~lambda ~depth hdr in
            lambdas := List.filter (fun d -> d <> depth) !lambdas;
            advance p;
            let items =
              if bkind = Compound then [Stmt (parse_stmt p ~kind:Compound)] else parse_items p ~inside:true ~kind:bkind
            in
            let closing =
              match peek p with
              | Some c when is_punct c "}" ->
                advance p;
                Some c
              | _ -> None
            in
            let lead, items =
              match items with
              | Comment c :: rest when c.lines = 0 -> (Some c, rest)
              | _ -> (None, items)
            in
            elems := Block {bkind; opening = t; lead; items; closing} :: !elems;
            prev := closing;
            let first_header = hdr in
            header := [];
            if !stack = [] && not (continues_after bkind ~header:first_header (peek p)) then fin := true )
          else (
            stack := "{" :: !stack;
            push t ) )
        else if is_punct t "}" then
          if !stack = [] then (if at_start then push t else fin := true)
          else (
            stack := List.tl !stack;
            push t )
        else push t )
  done;
  List.rev !elems

(** {2 Documents}

    A statement is laid out as a document: text with the places it may
    break, grouped so that a break is decided for the group as a whole or
    for each separator of a list in turn. *)

type doc =
  | Text of string
  | Lit of string  (** a string literal, which may be split between words *)
  | Cat of doc list
  | Break of string  (** the string when flat, a line break when broken *)
  | Hard  (** a line break *)
  | Group of doc  (** flat when it fits, else its own breaks broken *)
  | Fill of doc list
      (** content, separator, content...: each separator breaks when the
          content after it does not fit, or when the content before it took
          more than one line *)
  | Fill_next of doc * doc list * int ref
      (** a {!Fill} at a separator, with the line the content before it
          started on *)
  | Nest of int * doc  (** indented past the enclosing indentation *)
  | Align of doc  (** indented to the column it starts at *)
  | Args of doc list * string * bool
      (** the items of a bracketed list, each but the last ending with its
          comma, after the opening bracket; the closing bracket; and whether
          the list is a braced list with no name before it *)
  | Rhs of doc  (** the right side of an assignment, after the operator *)
  | Ternary of doc * doc  (** the branches of a conditional, after its condition *)
  | Body of block * bool  (** a block, whose brace takes a space before it *)
  | Anchor of doc  (** a block inside is indented from where this starts *)
  | Unanchor
  | Flatten of doc
      (** laid out flat: lists nested deeper than breaking could fit in the
          width (see {!nests_deeper}) *)
  | Choose of doc * doc
      (** the first layout, or the second when it is laid out better *)
  | Depth of int * int  (** restores the bracket depths after a list ({!out.depth}, {!out.angles}) *)
  | Last_space of int  (** restores {!out.last_space} after a list *)
  | Operand  (** an operand or a list item starts: {!out.last_space} moves here *)
  | Mark of int ref  (** records the line a call starts on *)
  | Mark_column of int ref  (** records the column a chain of calls starts at *)
  | Member_break of int ref * int ref
      (** a line break before a member access, to the column of the chain's
          start, when the call before it took more than one line *)

type mode =
  | Flat
  | Broken

(** The width of [s] in columns: UTF-8 continuation bytes take none. *)
let width s =
  let w = ref 0 in
  String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr w) s;
  !w

let interleave sep = function
  | [] -> []
  | d :: ds -> d :: List.concat_map (fun d -> [sep; d]) ds

(** Whether a block is laid out on more than one line however wide the
    line: it holds more than one item, or a block. *)
let multiline_block b =
  match List.filter (fun it -> it <> Blank) b.items with
  | [] -> false
  | [Stmt elems] -> List.exists (function Block _ -> true | Tok t -> t.kind = Line_comment) elems
  | _ -> true

(** The width of block [b] merged into one line, [{ s }], as near as the
    tokens tell, if the style may merge it. *)
let merged_width b =
  let items = List.filter (fun it -> it <> Blank) b.items in
  let toks_width elems =
    List.fold_left
      (fun acc e ->
        match (acc, e) with
        | Some w, Tok t when t.kind <> Line_comment -> Some (w + width t.text + if t.gap && w > 0 then 1 else 0)
        | _ -> None)
      (Some 0) elems
  in
  if b.lead <> None || b.bkind = Control then None
  else
    match items with
    | [] -> Some 2
    | [Stmt elems] -> Option.map (fun w -> w + 4) (toks_width elems)
    | _ when b.bkind = Enum ->
      List.fold_left
        (fun acc it ->
          match (acc, it) with
          | Some w, Stmt elems -> Option.map (fun x -> w + x + 1) (toks_width elems)
          | _ -> None)
        (Some 3) items
    | _ -> None

(** Whether [cmds] fit in [rem] columns up to their first line break, and
    the commands [rest] after them up to the first place they may break.  A
    construct of [cmds] not yet decided is measured flat, or, with [head],
    as far as the first place it may break; a block as far as its opening
    brace.  A lambda's block is measured merged into one line when the
    style merges it; after one laid out on more than one line, the commands
    go on from its closing brace with [after] columns left (by default
    [rem]). *)
let fits ?(head = false) ?after rem (cmds : (mode * doc) list) (rest : (int * mode * doc) list) =
  let after = match after with Some a -> a | None -> rem in
  let rem = ref rem in
  let head = ref head and in_rest = ref false in
  let undecided m = if m = Flat || not !head then Flat else Broken in
  let rec go cmds rest =
    if !rem < 0 then false
    else
      match cmds with
      | [] -> (
        match rest with
        | [] -> true
        | (_, m, d) :: rest ->
          head := true;
          in_rest := true;
          go [(m, d)] rest )
      | (m, d) :: cmds -> (
        match d with
        | Text s | Lit s ->
          rem := !rem - width s;
          !rem >= 0 && go cmds rest
        | Cat ds -> go (List.map (fun d -> (m, d)) ds @ cmds) rest
        | Break s -> (
          match m with
          | Broken -> true
          | Flat ->
            rem := !rem - String.length s;
            go cmds rest )
        | Hard -> !in_rest
        | Group d -> go ((undecided m, d) :: cmds) rest
        | Nest (_, d) | Align d | Anchor d -> go ((m, d) :: cmds) rest
        | Fill ds -> go (List.map (fun d -> (undecided m, d)) ds @ cmds) rest
        | Fill_next (s, ds, _) -> go (List.map (fun d -> (undecided m, d)) (s :: ds) @ cmds) rest
        | Choose (a, _) -> go ((m, a) :: cmds) rest
        | Flatten d -> go ((Flat, d) :: cmds) rest
        | Args (items, close, _) ->
          if undecided m = Broken then true
          else go (List.map (fun d -> (Flat, d)) (interleave (Text " ") items @ [Text close]) @ cmds) rest
        | Rhs d -> if undecided m = Broken then true else go ((Flat, Text " ") :: (Flat, d) :: cmds) rest
        | Ternary (a, b) ->
          if undecided m = Broken then go ((Flat, Text " ? ") :: (Broken, a) :: cmds) rest
          else go ((Flat, Cat [Text " ? "; a; Text " : "; b]) :: cmds) rest
        | Body (b, sp) -> (
          match if b.bkind = Lambda || b.bkind = Compound then merged_width b else None with
          | Some w ->
            rem := !rem - w - if sp then 1 else 0;
            go cmds rest
          | None ->
            rem := !rem - (if sp then 2 else 1) - (match b.lead with Some c -> 1 + min 40 (width c.text) | None -> 0);
            !rem >= 0
            && ((b.bkind <> Lambda && b.bkind <> Compound)
               ||
               ( rem := after - 1;
                 go cmds rest )) )
        | Unanchor | Mark _ | Mark_column _ | Member_break _ | Depth _ | Last_space _ | Operand -> go cmds rest )
  in
  go cmds rest

(** The text of [d] laid out flat, or [None] if it holds a line break. *)
let flat_text d =
  let b = Buffer.create 80 in
  let rec go = function
    | Text s | Lit s | Break s -> Buffer.add_string b s
    | Cat ds -> List.iter go ds
    | Hard | Body _ -> raise Exit
    | Group d | Nest (_, d) | Align d | Anchor d | Flatten d -> go d
    | Fill ds -> List.iter go ds
    | Fill_next (s, ds, _) -> List.iter go (s :: ds)
    | Choose (a, _) -> go a
    | Args (items, close, _) ->
      List.iter go (interleave (Text " ") items);
      Buffer.add_string b close
    | Rhs d ->
      Buffer.add_char b ' ';
      go d
    | Ternary (a, x) ->
      Buffer.add_string b " ? ";
      go a;
      Buffer.add_string b " : ";
      go x
    | Unanchor | Mark _ | Mark_column _ | Member_break _ | Depth _ | Last_space _ | Operand -> ()
  in
  match go d with
  | () -> Some (Buffer.contents b)
  | exception Exit -> None

(** {2 From tokens to documents} *)

(** A statement's tokens with brackets matched. *)
type node =
  | Atom of token
  | Brack of token * node list list * token option
      (** an opening bracket, the items between it and its closing bracket
          split after commas, and the closing bracket *)
  | Blk of block

let closer_of = function
  | "(" -> ")"
  | "[" -> "]"
  | "{" -> "}"
  | _ -> ">"

(** Whether the [<] at [elems.(i)] opens a template argument list: the
    printer writes one with no space before it, after a name, and a
    template's parameter list after [template]. *)
let template_open (elems : elem array) i =
  match elems.(i) with
  | Tok t when is_punct t "<" -> (
    i > 0
    && match elems.(i - 1) with Tok p -> is_word p "template" || (p.kind = Word && not t.space) | _ -> false )
  | _ -> false

exception Mismatch

(** Matches the brackets of [elems] from [i] up to [closer], if any; returns
    the items found, split after commas when inside brackets, the closer
    and the index after it. *)
let rec bracket (elems : elem array) i ~closer : node list list * token option * int =
  let n = Array.length elems in
  let items = ref [] and cur = ref [] in
  let flush () =
    items := List.rev !cur :: !items;
    cur := []
  in
  let rec go i =
    if i >= n then if closer <> None then raise Mismatch else (None, i)
    else
      match elems.(i) with
      | Block b ->
        cur := Blk b :: !cur;
        go (i + 1)
      | Tok t -> (
        match closer with
        | Some c when t.kind = Punct && t.text = c && (c <> ">" || not t.space) -> (Some t, i + 1)
        | _ ->
          if t.kind = Punct && List.mem t.text [")"; "]"; "}"] && closer <> None then raise Mismatch
          else if t.kind = Punct && List.mem t.text ["("; "["; "{"] then (
            match bracket elems (i + 1) ~closer:(Some (closer_of t.text)) with
            | inner, cl, j ->
              cur := Brack (t, inner, cl) :: !cur;
              go j
            | exception Mismatch when closer = None ->
              cur := Atom t :: !cur;
              go (i + 1) )
          else if template_open elems i then (
            match bracket elems (i + 1) ~closer:(Some ">") with
            | inner, cl, j ->
              cur := Brack (t, inner, cl) :: !cur;
              go j
            | exception Mismatch ->
              cur := Atom t :: !cur;
              go (i + 1) )
          else if is_punct t "," && closer <> None then (
            cur := Atom t :: !cur;
            flush ();
            go (i + 1) )
          else (
            cur := Atom t :: !cur;
            go (i + 1) ) )
  in
  let cl, j = go i in
  if !cur <> [] || !items <> [] then flush ();
  (List.rev !items, cl, j)

(** A statement's nodes. *)
let nodes_of (elems : elem list) : node list =
  match bracket (Array.of_list elems) 0 ~closer:None with
  | [items], _, _ -> items
  | [], _, _ -> []
  | items, _, _ -> List.concat items

let first_token = function
  | Atom t | Brack (t, _, _) -> t
  | Blk b -> b.opening

(** Whether a space goes before node [nd]. *)
let gap_before nd = (first_token nd).gap

(** Binary operators by precedence, loosest first. *)
let binary_levels =
  [ ["||"]; ["&&"]; ["|"]; ["^"]; ["&"]; ["=="; "!="]; ["<"; ">"; "<="; ">="; "<=>"]; ["<<"; ">>"]; ["+"; "-"];
    ["*"; "/"; "%"]; [".*"; "->*"] ]

let assignment_ops = ["="; "+="; "-="; "*="; "/="; "%="; "&="; "|="; "^="; "<<="; ">>="]

(** Whether node [k] of [nodes] is a binary operator in [ops]: one written
    with a space on both sides. *)
let is_binary (nodes : node array) k ops =
  match nodes.(k) with
  | Atom t when t.kind = Punct && List.mem t.text ops && t.space && k > 0 && k + 1 < Array.length nodes ->
    gap_before nodes.(k + 1)
  | _ -> false

let sub_list arr i j = Array.to_list (Array.sub arr i (j - i))

(** Words after which a parenthesis groups or holds a condition rather than
    calling. *)
let grouping_keywords = control_words @ ["return"; "co_return"; "co_yield"; "co_await"; "throw"; "case"]

let leading_keywords = ["return"; "throw"; "co_return"; "co_yield"; "co_await"; "else"; "delete"; "new"; "requires"]

(** The document of a run of nodes.  Words and operators are joined as the
    input spaced them; the structure that may break is, loosest first: a
    leading keyword, an assignment, a conditional, binary operators by
    precedence, bracketed lists. *)
let rec seq_doc (nodes : node list) : doc =
  match nodes with
  | [] -> Text ""
  | Atom t :: (nd :: _ as rest) when t.kind = Word && List.mem t.text leading_keywords ->
    Cat [Text t.text; (if gap_before nd then Text " " else Text ""); seq_doc rest]
  | _ -> (
    let arr = Array.of_list nodes in
    let n = Array.length arr in
    let first ops =
      let r = ref (-1) in
      for k = n - 1 downto 0 do
        if is_binary arr k ops then r := k
      done;
      !r
    in
    let assign = first assignment_ops in
    if assign > 0 then
      let op = (first_token arr.(assign)).text in
      Cat [seq_doc (sub_list arr 0 assign); Text (" " ^ op); Rhs (seq_doc (sub_list arr (assign + 1) n))]
    else
      let q = first ["?"] in
      let colon =
        if q < 0 then -1
        else
          let depth = ref 0 and found = ref (-1) in
          for k = q + 1 to n - 1 do
            if !found < 0 then
              if is_binary arr k ["?"] then incr depth
              else if is_binary arr k [":"] then if !depth = 0 then found := k else decr depth
          done;
          !found
      in
      if colon > 0 then
        Cat
          [ seq_doc (sub_list arr 0 q);
            Ternary (seq_doc (sub_list arr (q + 1) colon), seq_doc (sub_list arr (colon + 1) n)) ]
      else
        let has ops =
          let r = ref false in
          for k = 0 to n - 1 do
            if is_binary arr k ops then r := true
          done;
          !r
        in
        match List.find_opt has binary_levels with
        | Some ops ->
          let parts = ref [] and start = ref 0 in
          for k = 0 to n - 1 do
            if is_binary arr k ops then (
              parts := Cat [seq_doc (sub_list arr !start k); Text (" " ^ (first_token arr.(k)).text)] :: !parts;
              start := k + 1 )
          done;
          let parts = List.rev (seq_doc (sub_list arr !start n) :: !parts) in
          Align (Fill (interleave (Break " ") parts))
        | None -> atoms_doc nodes )

(** Nodes joined as the input spaced them. *)
and atoms_doc nodes =
  let arr = Array.of_list nodes in
  let n = Array.length arr in
  let is_call k = k >= 0 && k < n && match arr.(k) with Brack (o, _ :: _, _) -> is_punct o "(" | _ -> false in
  let is_member k = k < n && match arr.(k) with Atom t -> is_punct t "." || is_punct t "->" | _ -> false in
  let chained = ref false in
  let start = ref 0 in
  let marks = Array.make n None in
  for k = 0 to n - 1 do
    if is_member k && is_call (k - 1) then (
      chained := true;
      let r = ref 0 in
      marks.(k - 1) <- Some r;
      marks.(k) <- Some r )
  done;
  let parts =
    List.mapi
      (fun i nd ->
        let sp = if i > 0 && gap_before nd then Text " " else Text "" in
        let d =
          match nd with
          | Atom t -> Cat [sp; atom_doc t]
          | Brack (o, items, cl) ->
            let grouping =
              is_punct o "("
              &&
              match if i > 0 then Some arr.(i - 1) else None with
              | None -> true
              | Some (Atom p) when p.kind = Word -> List.mem p.text grouping_keywords
              | Some (Atom p) -> not (is_punct p ">" || is_punct p ")" || is_punct p "]")
              | Some _ -> false
            in
            Cat [sp; brack_doc ~grouping o items cl]
          | Blk b -> Body (b, i > 0)
        in
        match marks.(i) with
        | Some r when is_member i -> Cat [Member_break (r, start); d]
        | Some r -> Cat [Mark r; d]
        | None -> d)
      nodes
  in
  if !chained then Cat (Mark start :: Mark_column start :: parts) else Cat parts

and atom_doc t =
  match t.kind with
  | Literal -> Lit t.text
  | Line_comment -> if t.lines > 0 then Cat [Hard; Text t.text; Hard] else Cat [Text " "; Text t.text; Hard]
  | _ -> Text t.text

(** A bracketed list: the items packed after the opening bracket.  The
    contents of a [grouping] parenthesis, one that does not call, are an
    operand ({!Operand}). *)
and brack_doc ?(grouping = false) o items cl =
  let close = match cl with Some c -> c.text | None -> "" in
  match List.map item_doc items with
  | [] -> Text (o.text ^ close)
  | first :: more ->
    let first = if grouping then Cat [Operand; first] else first in
    Cat [Text o.text; Args (first :: more, close, is_punct o "{" && o.gap)]

(** An item of a list, ending with its comma if it has one. *)
and item_doc part =
  match List.rev part with
  | Atom c :: rest when is_punct c "," -> Cat [seq_doc (List.rev rest); Text ","]
  | _ -> seq_doc part

(** {2 Statements} *)

(** Splits off a leading [template <...>] and, after it, a requires-clause:
    a conjunction or disjunction of primaries, each a qualified name with
    template arguments or a parenthesised expression. *)
let template_parts (nodes : node list) =
  match nodes with
  | Atom t :: (Brack (o, _, _) as params) :: rest when is_word t "template" && is_punct o "<" -> (
    let head = [Atom t; params] in
    match rest with
    | Atom r :: after when is_word r "requires" ->
      let rec primary = function
        | (Brack (o, _, _) as b) :: rest when is_punct o "(" -> ([b], rest)
        | (Atom w as wn) :: rest when w.kind = Word ->
          let rec more acc = function
            | (Atom c as cn) :: (Atom w2 as wn) :: rest when is_punct c "::" && w2.kind = Word ->
              more (wn :: cn :: acc) rest
            | (Brack (o, _, _) as b) :: rest when is_punct o "<" -> more (b :: acc) rest
            | rest -> (List.rev acc, rest)
          in
          more [wn] rest
        | (Atom bang as bn) :: rest when is_punct bang "!" ->
          let p, rest = primary rest in
          (bn :: p, rest)
        | rest -> ([], rest)
      in
      let rec clause acc rest =
        let p, rest = primary rest in
        let acc = List.rev_append p acc in
        match rest with
        | (Atom op as o) :: rest when is_punct op "&&" || is_punct op "||" -> clause (o :: acc) rest
        | _ -> (List.rev acc, rest)
      in
      let req, decl = clause [] after in
      Some (head, Some (Atom r :: req), decl)
    | _ -> Some (head, None, rest) )
  | _ -> None

(** Splits a function header at its constructor-initialiser colon. *)
let ctor_init_split (nodes : node list) =
  let rec go acc seen_paren = function
    | Atom c :: rest when is_punct c ":" && seen_paren -> Some (List.rev acc, rest)
    | (Brack (o, _, _) as b) :: rest -> go (b :: acc) (seen_paren || is_punct o "(") rest
    | nd :: rest -> go (nd :: acc) seen_paren rest
    | [] -> None
  in
  go [] false nodes

(** Splits [nodes] after top-level commas. *)
let comma_parts (nodes : node list) =
  let parts = ref [] and cur = ref [] in
  List.iter
    (fun nd ->
      match nd with
      | Atom c when is_punct c "," ->
        parts := List.rev (nd :: !cur) :: !parts;
        cur := []
      | _ -> cur := nd :: !cur)
    nodes;
  if !cur <> [] then parts := List.rev !cur :: !parts;
  List.rev !parts

let packed items = Align (Fill (interleave (Break " ") items))

(** The document of a run of a statement's nodes that holds no block of its
    own, its top-level commas separating a packed list. *)
let header_doc nodes =
  match comma_parts nodes with
  | [] | [_] -> seq_doc nodes
  | parts -> packed (List.map item_doc parts)

let specifiers = ["static"; "inline"; "constexpr"; "consteval"; "virtual"; "explicit"; "friend"; "extern"]

(** A function header's nodes split before the function's name, when a
    return type precedes it: the name is the qualified name before the last
    parameter list. *)
let return_type_split (nodes : node list) =
  let arr = Array.of_list nodes in
  let n = Array.length arr in
  let paren = ref (-1) in
  Array.iteri (fun k nd -> match nd with Brack (o, _, _) when is_punct o "(" -> paren := k | _ -> ()) arr;
  let p = !paren in
  let is_word_at k = k >= 0 && match arr.(k) with Atom t -> t.kind = Word | _ -> false in
  let is_at k p = k >= 0 && match arr.(k) with Atom t -> is_punct t p | _ -> false in
  let is_angle k = k >= 0 && match arr.(k) with Brack (o, _, _) -> is_punct o "<" | _ -> false in
  if p < 1 || not (is_word_at (p - 1)) then None
  else
    let q = ref (p - 1) in
    let continue = ref true in
    while !continue do
      if is_at (!q - 1) "::" && is_word_at (!q - 2) then q := !q - 2
      else if is_at (!q - 1) "::" && is_angle (!q - 2) && is_word_at (!q - 3) then q := !q - 3
      else continue := false
    done;
    if is_at (!q - 1) "~" then decr q;
    let ret = sub_list arr 0 !q in
    let typed =
      List.exists
        (function Atom t -> t.kind = Word && not (List.mem t.text specifiers) | Brack _ -> true | Blk _ -> false)
        ret
    in
    let expression =
      List.exists
        (function
          | Atom t ->
            List.mem t.text ["return"; "co_return"; "throw"; "delete"; "new"; "."; "->"; "="; "?"; "<<"; "co_await"]
          | _ -> false)
        ret
    in
    if !q = 0 || (not typed) || expression then None else Some (ret, sub_list arr !q n)

(** A function header that may put its name on a line of its own, after
    the return type. *)
let header_with_return nodes =
  match return_type_split nodes with
  | Some (ret, rest) ->
    let r = seq_doc ret and d = seq_doc rest in
    let sp = match rest with nd :: _ when gap_before nd -> Text " " | _ -> Text "" in
    Choose (Cat [r; sp; d], Cat [r; Hard; d])
  | None -> header_doc nodes

(** A declaration's document after its template head: a constructor's
    initialiser list goes on a line of its own, indented by four, when
    the declaration does not fit. *)
let decl_doc ~kind nodes =
  match (kind, ctor_init_split nodes) with
  | Some Function, Some (before, inits) ->
    let has_block = List.exists (function Blk _ -> true | _ -> false) in
    let rec deep = function
      | Blk _ -> true
      | Brack (_, items, _) -> List.exists (List.exists deep) items
      | Atom _ -> false
    in
    let multiline = List.exists deep inits || has_block inits in
    let inits = packed (List.map (fun p -> Anchor (item_doc p)) (comma_parts inits)) in
    let colon = Nest (continuation_width, Cat [(if multiline then Hard else Break " "); Text ": "; inits]) in
    Cat [header_with_return before; (if multiline then colon else Group colon)]
  | Some Function, None -> header_with_return nodes
  | None, None
    when match List.rev nodes with
         | Atom t :: Brack (o, _, _) :: _ -> is_punct t ";" && is_punct o "("
         | Atom t :: Atom c :: Brack (o, _, _) :: _ -> is_punct t ";" && is_word c "const" && is_punct o "("
         | _ -> false ->
    header_with_return nodes
  | _ -> header_doc nodes

(** The document of a statement's first header: its template head, the
    template's requires-clause on a line of its own indented by two, and
    the declaration.  The declaration goes on a line of its own after a
    requires-clause, after a concept's template head, and when it does not
    fit. *)
let head_doc ~kind nodes =
  match template_parts nodes with
  | Some (head, req, decl) -> (
    let head_d = atoms_doc head and decl_d = decl_doc ~kind decl in
    let is_concept = match decl with Atom t :: _ -> is_word t "concept" | _ -> false in
    match req with
    | Some r -> Cat [head_d; Nest (indent_width, Cat [Hard; seq_doc r]); Hard; decl_d]
    | None when decl = [] -> head_d
    | None when is_concept -> Cat [head_d; Hard; decl_d]
    | None -> Group (Cat [head_d; Break " "; decl_d]) )
  | None -> decl_doc ~kind nodes

(** The document of a statement: headers and the blocks after them. *)
let stmt_doc (elems : elem list) : doc =
  let nodes = nodes_of elems in
  let nodes, trailing =
    match List.rev nodes with
    | Atom t :: rest when t.kind = Line_comment -> (List.rev rest, [Text (" " ^ t.text)])
    | _ -> (nodes, [])
  in
  let kind = List.find_map (function Blk b -> Some b.bkind | _ -> None) nodes in
  let rec segments cur acc = function
    | Blk b :: rest -> segments [] (`Block b :: `Header (List.rev cur) :: acc) rest
    | nd :: rest -> segments (nd :: cur) acc rest
    | [] -> List.rev (if cur = [] then acc else `Header (List.rev cur) :: acc)
  in
  let rec docs first after_text = function
    | [] -> []
    | `Header [] :: rest -> docs first after_text rest
    | `Header seg :: rest ->
      let d =
        if first then head_doc ~kind seg
        else Cat [(if gap_before (List.hd seg) then Text " " else Text ""); header_doc seg]
      in
      d :: docs false true rest
    | `Block b :: rest -> Body (b, after_text) :: docs false true rest
  in
  Cat (docs true false (segments [] [] nodes) @ trailing)

(** {2 Rendering} *)

type out = {
  buf : Buffer.t;  (** the text, written only outside trials *)
  mutable col : int;
  mutable line : int;  (** lines started so far *)
  mutable line_indent : int;  (** the indentation of the current line *)
  mutable pending : int option;  (** indentation not yet written on a line still empty *)
  mutable anchors : (int * int) list;  (** column and line of each open {!Anchor} *)
  mutable stmt_indent : int;  (** the indentation of the statement being laid out *)
  mutable stmt_line : int;  (** the line the statement being laid out starts on *)
  trial : int;  (** how many trial layouts this one is nested in *)
  origin : int;  (** the line a trial started on *)
  mutable excess : int;  (** on trial, the columns past the limit of the lines finished *)
  bound : (int * int * int) option;
      (** on trial, the excess, breaks inside template arguments and line
          count past which the layout is abandoned: as each only grows, it
          already loses to the alternative it is compared with *)
  mutable depth : int;  (** how many broken bracketed lists the position is in *)
  mutable depth_sum : int;  (** the sum of {!depth} at each line break so far *)
  mutable angles : int;  (** how many broken template argument lists the position is in *)
  mutable angle_breaks : int;
      (** how many line breaks so far were inside a template argument list,
          which reads worst: clang-format penalises them heavily too *)
  mutable opens : int;  (** how many lists broke after their opening bracket *)
  mutable last_space : int;
      (** the column a list breaking after its opening bracket indents from,
          as clang-format's [LastSpace]: the start of the statement, of the
          line a list broke onto, or of the operand or list item the position
          is in; a bracket opened without a break keeps it, so brackets
          opened on one line share one continuation and indentation grows
          by four a line rather than by the width of each bracket *)
}

(** Raised by a trial layout that exceeds its {!out.bound}. *)
exception Abandoned

(** Adds the current line's columns past the limit to a trial's excess. *)
let finish_line o = if o.col > column_limit then o.excess <- o.excess + o.col - column_limit

let newline o ind =
  if o.trial > 0 then (
    finish_line o;
    match o.bound with
    | Some b when (o.excess, o.angle_breaks + Bool.to_int (o.angles > 0), o.line + 1 - o.origin) > b ->
      raise Abandoned
    | _ -> () )
  else if Buffer.length o.buf > 0 || o.pending = None then Buffer.add_char o.buf '\n';
  o.line <- o.line + 1;
  o.depth_sum <- o.depth_sum + o.depth;
  if o.angles > 0 then o.angle_breaks <- o.angle_breaks + 1;
  o.pending <- Some ind;
  o.col <- ind;
  o.line_indent <- ind

let emit o s =
  if s <> "" then (
    if o.trial = 0 then (
      ( match o.pending with
      | Some ind -> Buffer.add_string o.buf (String.make ind ' ')
      | None -> () );
      Buffer.add_string o.buf s );
    o.pending <- None;
    o.col <- o.col + width s )

let fits_line ?head o cmds rest = fits ?head ~after:(column_limit - o.line_indent) (column_limit - o.col) cmds rest

(** Splits the plain string literal [s], to start at column [col], after
    spaces into pieces that each fit the line. *)
let split_literal s ~col =
  let n = String.length s in
  if n < 2 || s.[0] <> '"' || s.[n - 1] <> '"' then [s]
  else
    let avail = column_limit - col - 2 in
    if avail < 16 then [s]
    else
      let rec go r acc =
        if width r <= avail then List.rev (r :: acc)
        else
          let cut = ref (-1) in
          String.iteri (fun i c -> if c = ' ' && i + 1 <= avail && i > 0 then cut := i) r;
          if !cut <= 0 then List.rev (r :: acc)
          else
            let piece = String.sub r 0 (!cut + 1) and rest = String.sub r (!cut + 1) (String.length r - !cut - 1) in
            if rest = "" then List.rev (piece :: acc) else go rest (piece :: acc)
      in
      List.map (fun p -> "\"" ^ p ^ "\"") (go (String.sub s 1 (n - 2)) [])

(** Splits the line comment [text] between words into lines fitting from
    column [col]. *)
let reflow_comment text ~col =
  if col + width text <= column_limit then [text]
  else
    let prefix_len =
      let k = ref 0 in
      while !k < String.length text && text.[!k] = '/' do incr k done;
      !k
    in
    let prefix = String.sub text 0 prefix_len in
    let words = String.split_on_char ' ' (String.sub text prefix_len (String.length text - prefix_len)) in
    let words = List.filter (( <> ) "") words in
    let lines = ref [] and cur = ref prefix in
    List.iter
      (fun w ->
        if !cur = prefix then cur := prefix ^ " " ^ w
        else if col + width !cur + 1 + width w <= column_limit then cur := !cur ^ " " ^ w
        else (
          lines := !cur :: !lines;
          cur := prefix ^ " " ^ w ))
      words;
    List.rev (!cur :: !lines)

let is_access = function
  | Label (t :: _) -> List.mem t.text ["public"; "private"; "protected"]
  | _ -> false

(** Whether an item is a definition: a function or record with
    its body. *)
let is_definition = function
  | Stmt elems -> List.exists (function Block b -> List.mem b.bkind [Function; Record] | Tok _ -> false) elems
  | _ -> false

(** The items of a block with blank lines where the style puts them: at
    most one in a row, none at the end of a block or after an access
    specifier; one around each definition (before the comments leading
    it) and before an access specifier that follows members. *)
let space_items (items : item list) =
  let arr = Array.of_list items in
  let n = Array.length arr in
  let out = ref [] in
  let last = ref None in
  let push_blank () =
    match !out with
    | Blank :: _ | [] -> ()
    | _ -> out := Blank :: !out
  in
  (* whether the comments from [i] lead a definition *)
  let rec leads_definition i =
    i < n && match arr.(i) with Comment _ -> leads_definition (i + 1) | it -> is_definition it
  in
  for i = 0 to n - 1 do
    match arr.(i) with
    | Blank -> ( match !last with Some (Label _) -> () | _ -> if i < n - 1 then push_blank () )
    | it ->
      let opens_definition =
        match it with
        | Comment _ -> ( match !last with Some (Comment _) -> false | _ -> leads_definition i )
        | _ -> is_definition it && (match !last with Some (Comment _) -> false | _ -> true)
      in
      ( match !last with
      | None | Some (Label _) -> ()
      | Some l -> if is_definition l || opens_definition || is_access it then push_blank () );
      out := it :: !out;
      last := Some it
  done;
  (* no blank at the end *)
  let rec drop = function Blank :: rest -> drop rest | l -> l in
  List.rev (drop !out)

(** The sort key of an [#include] line: quoted before angled (the file's
    own header first), then by name. *)
let include_key ~stem text =
  let s = String.trim (String.sub text 1 (String.length text - 1)) in
  let s =
    if String.length s >= 7 && String.sub s 0 7 = "include" then String.trim (String.sub s 7 (String.length s - 7))
    else s
  in
  let prio =
    if s <> "" && s.[0] = '<' then 3
    else
      let name = if String.length s >= 2 then String.sub s 1 (String.length s - 2) else s in
      if stem <> "" && Filename.remove_extension (Filename.basename name) = stem then 0 else 1
  in
  (prio, s)

let is_include = function
  | Pp t ->
    let s = String.trim (String.sub t.text 1 (String.length t.text - 1)) in
    String.length s >= 7 && String.sub s 0 7 = "include"
  | _ -> false

(** Sorts each run of [#include] lines and drops repeated ones. *)
let sort_includes ~stem items =
  let rec go acc = function
    | [] -> List.rev acc
    | it :: _ as l when is_include it ->
      let rec take run = function
        | it :: rest when is_include it -> take (it :: run) rest
        | rest -> (List.rev run, rest)
      in
      let run, rest = take [] l in
      let keyed = List.map (fun it -> match it with Pp t -> (include_key ~stem t.text, it) | _ -> assert false) run in
      let sorted = List.stable_sort (fun (a, _) (b, _) -> compare a b) keyed in
      let rec dedup = function
        | (k1, _) :: ((k2, _) :: _ as rest) when k1 = k2 -> dedup rest
        | (_, it) :: rest -> it :: dedup rest
        | [] -> []
      in
      go (List.rev_append (dedup sorted) acc) rest
    | it :: rest -> go (it :: acc) rest
  in
  go [] items

(** Whether [d] holds a block laid out on more than one line. *)
let rec multiline_body = function
  | Body (b, _) -> multiline_block b
  | Cat ds | Fill ds -> List.exists multiline_body ds
  | Fill_next (s, ds, _) -> List.exists multiline_body (s :: ds)
  | Choose (a, _) -> multiline_body a
  | Args (ds, _, _) -> List.exists multiline_body ds
  | Group d | Nest (_, d) | Align d | Anchor d | Rhs d | Flatten d -> multiline_body d
  | Ternary (a, b) -> multiline_body a || multiline_body b
  | Text _ | Lit _ | Break _ | Hard | Unanchor | Mark _ | Mark_column _ | Member_break _ | Depth _ | Last_space _
  | Operand ->
    false

(** The string literal [d] is, if it is one ({!is_literal}). *)
let rec literal_text = function
  | Lit s -> Some s
  | Cat ds -> List.find_map literal_text ds
  | _ -> None

(** Whether [d] holds a chain of member calls. *)
let rec has_chain = function
  | Member_break _ -> true
  | Cat ds | Fill ds -> List.exists has_chain ds
  | Fill_next (s, ds, _) -> List.exists has_chain (s :: ds)
  | Choose (a, _) -> has_chain a
  | Group d | Nest (_, d) | Align d | Anchor d | Flatten d -> has_chain d
  | _ -> false

(** Whether [d] is a string literal, with its comma: an item the layout may
    split rather than move. *)
let rec is_literal = function
  | Lit _ -> true
  | Cat ds -> (
    match List.filter (function Text "" -> false | Text "," -> false | _ -> true) ds with
    | [d] -> is_literal d
    | _ -> false )
  | _ -> false

(** The leading closing text of the commands after a construct, which a
    trial layout of the construct takes with it. *)
let rec closers = function
  | ((_, _, Text _) as c) :: rest -> c :: closers rest
  | (i, m, Body (b, sp)) :: _ ->
    let lead =
      match b.lead with
      | Some c -> " " ^ if String.length c.text > 40 then String.sub c.text 0 40 else c.text
      | None -> ""
    in
    [(i, m, Text ((if sp then " {" else "{") ^ lead))]
  | _ -> []

(** Whether bracketed lists nest more than [k] deep somewhere in [d]. *)
let nests_deeper d k =
  let rec go k d =
    k < 0
    ||
    match d with
    | Args (ds, _, _) -> List.exists (go (k - 1)) ds
    | Cat ds | Fill ds -> List.exists (go k) ds
    | Fill_next (x, ds, _) -> List.exists (go k) (x :: ds)
    | Group d | Nest (_, d) | Align d | Anchor d | Rhs d | Choose (d, _) | Flatten d -> go k d
    | Ternary (a, b) -> go k a || go k b
    | _ -> false
  in
  go k d

(** How many trial layouts may nest: a choice made on trial makes the
    choices inside it on trial too, but no deeper. *)
let trial_depth = 2

(** The largest construct laid out on trial, in characters of its text, at
    the outermost trial; a nested trial takes a quarter of its enclosing
    one's, which bounds the work a choice costs. *)
let trial_limit = 1500

(** Whether the size of [d] in characters of its text, blocks included, is
    at most [limit]. *)
let smaller_than limit d =
  let n = ref 0 in
  let add k =
    n := !n + k;
    if !n > limit then raise Exit
  in
  let rec elems es = List.iter (function Tok t -> add (String.length t.text + 1) | Block b -> block b) es
  and block b =
    add 4;
    List.iter (function Stmt es -> elems es | Pp t | Comment t -> add (String.length t.text) | _ -> ()) b.items
  and go = function
    | Text s | Lit s | Break s -> add (String.length s)
    | Cat ds | Fill ds | Args (ds, _, _) -> List.iter go ds
    | Fill_next (x, ds, _) -> List.iter go (x :: ds)
    | Group d | Nest (_, d) | Align d | Anchor d | Rhs d | Choose (d, _) | Flatten d -> go d
    | Ternary (a, b) ->
      go a;
      go b
    | Body (b, _) -> block b
    | Hard | Unanchor | Mark _ | Mark_column _ | Member_break _ | Depth _ | Last_space _ | Operand -> ()
  in
  match go d with
  | () -> true
  | exception Exit -> false

(** Whether the choice of a layout for [d] at [o] may be made by laying out
    the alternatives on trial. *)
let may_try o d = o.trial < trial_depth && smaller_than (trial_limit lsr (2 * o.trial)) d

let rec run o (cmds : (int * mode * doc) list) =
  match cmds with
  | [] -> ()
  | (ind, m, d) :: rest -> (
    match d with
    | Text s ->
      emit o s;
      run o rest
    | Lit s ->
      if m = Flat || o.col + width s <= column_limit then emit o s
      else (
        let col = o.col in
        match split_literal s ~col with
        | first :: more ->
          emit o first;
          List.iter
            (fun p ->
              newline o col;
              emit o p)
            more
        | [] -> () );
      run o rest
    | Cat ds -> run o (List.map (fun d -> (ind, m, d)) ds @ rest)
    | Break s ->
      if m = Flat then emit o s else newline o ind;
      run o rest
    | Hard ->
      newline o ind;
      run o rest
    | Nest (k, d) -> run o ((ind + k, m, d) :: rest)
    | Align d -> run o ((o.col, m, d) :: rest)
    | Flatten d -> run o ((ind, Flat, d) :: rest)
    | Group d ->
      let m = if m = Flat || fits_line o [(Flat, d)] rest then Flat else Broken in
      run o ((ind, m, d) :: rest)
    | Fill [] -> run o rest
    | Fill (c :: more) ->
      let cm = if m = Flat || fits_line o [(Flat, c)] (if more = [] then rest else []) then Flat else Broken in
      let rest =
        match more with
        | s :: more -> (ind, m, Fill_next (s, more, ref o.line)) :: rest
        | [] -> rest
      in
      run o ((ind, cm, c) :: rest)
    | Fill_next (s, more, start) ->
      let next = match more with c :: _ -> c | [] -> Text "" in
      let last = List.length more <= 1 in
      let sm =
        if m = Flat then Flat
        else if o.line <> !start then Broken
        else if fits_line o [(Flat, s); (Flat, next)] (if last then rest else []) then Flat
        else if
          (not (fits (column_limit - ind) [(Flat, next)] (if last then closers rest else [])))
          && fits_line ~head:true o [(Flat, s); (Broken, next)] []
        then
          (* the next item breaks either way: on this line or the next *)
          if may_try o (Fill more) then
            let tail = closers rest in
            let trial sm = (ind, sm, s) :: (ind, m, Operand) :: (ind, m, Fill more) :: tail in
            if first_better o (trial Flat) (trial Broken) then Flat else Broken
          else Flat
        else Broken
      in
      run o ((ind, sm, s) :: (ind, m, Operand) :: (ind, m, Fill more) :: rest)
    | Args (items, close, anonymous) ->
      let rec but_last = function [_] | [] -> [] | x :: xs -> x :: but_last xs in
      let lambda_inside = List.exists multiline_body (but_last items) in
      if (not lambda_inside) && (m = Flat || fits_line o [(Flat, d)] rest) then
        run o ((ind, Flat, Cat (interleave (Text " ") items @ [Text close])) :: rest)
      else
        let rest = (ind, m, Depth (o.depth, o.angles)) :: (ind, m, Last_space o.last_space) :: rest in
        o.depth <- (o.depth + if close = ">" then 3 else 1);
        if close = ">" then o.angles <- o.angles + 1;
        let ni = o.last_space + continuation_width in
        let fill items = Cat [Fill (interleave (Break " ") items); Text close] in
        let one_per_line items = Cat (interleave (Break " ") (List.map (fun i -> Anchor i) items) @ [Text close]) in
        let aligned d = run o ((o.col, Broken, d) :: rest) in
        (* lists nested deeper than the room left could hold, a level a
           line, are laid out flat: breaking them would only add lines.  A
           list of one such item is itself a chain too deep; in a longer
           list, the items too deep are *)
        let budget = (column_limit - ni) / continuation_width in
        let too_deep item = (not lambda_inside) && nests_deeper item (budget - 1) in
        let hopeless = match items with [item] -> too_deep item | _ -> false in
        let items = List.map (fun item -> if too_deep item then Flatten item else item) items in
        let broken d =
          o.opens <- o.opens + 1;
          newline o ni;
          o.last_space <- ni;
          run o ((ni, Broken, d) :: rest)
        in
        if hopeless then run o ((ind, Flat, Cat (interleave (Text " ") items @ [Text close])) :: rest)
        else if lambda_inside && anonymous then aligned (one_per_line items)
        else if lambda_inside then broken (one_per_line items)
        else if may_try o (fill items) then
          let tail = closers rest in
          if
            first_better o
              ((o.col, Broken, fill items) :: tail)
              ((ni, Broken, Cat [Hard; Last_space ni; fill items]) :: tail)
          then aligned (fill items) else broken (fill items)
        else
          let n = List.length items in
          let fits_aligned i item =
            is_literal item || fits_line o [(Flat, item)] (if i = n - 1 then [(ind, Flat, Text close)] else [])
          in
          let is_aligned =
            match items with
            | [item] when is_literal item -> (
              match literal_text item with
              | Some l -> List.length (split_literal l ~col:o.col) <= List.length (split_literal l ~col:ni)
              | None -> true )
            | [item] ->
              fits_aligned 0 item
              || not (fits (column_limit - ni) [(Flat, item)] [(ind, Flat, Text close)])
            | _ -> List.for_all Fun.id (List.mapi fits_aligned items)
          in
          if is_aligned then aligned (fill items) else broken (fill items)
    | Rhs r ->
      if m = Flat || fits_line o [(Flat, Text " "); (Flat, r)] rest then (
        emit o " ";
        run o ((ind, Flat, r) :: rest) )
      else
        let ni = ind + continuation_width in
        let own_line =
          if fits (column_limit - ni) [(Flat, r)] rest || has_chain r then true
          else if may_try o r then
            let tail = closers rest in
            first_better o
              ((ni, Broken, Cat [Hard; Last_space ni; r]) :: tail)
              ((ind, Flat, Text " ") :: (ind, Broken, r) :: tail)
          else not (fits_line ~head:true o [(Flat, Text " "); (Broken, r)] [])
        in
        if own_line then (
          newline o ni;
          o.last_space <- ni;
          run o ((ni, Broken, r) :: rest) )
        else (
          emit o " ";
          run o ((ind, Broken, r) :: rest) )
    | Ternary (a, b) ->
      let flat = Cat [Text " ? "; a; Text " : "; b] in
      if m = Flat || fits_line o [(Flat, flat)] rest then run o ((ind, Flat, flat) :: rest)
      else
        let broken = Cat [Text "? "; Operand; a; Break " "; Text ": "; Operand; b] in
        let col = o.col + 1 in
        if
          fits_line ~head:true o [(Flat, Text " ? "); (Broken, a)] []
          && fits (column_limit - col) [(Flat, Text ": "); (Flat, b)] (closers rest)
        then (
          emit o " ";
          run o ((o.col, Broken, broken) :: rest) )
        else
          let ni = ind + continuation_width in
          newline o ni;
          run o ((ni, Broken, broken) :: rest)
    | Body (b, sp) ->
      render_block o b ~space:sp ~rest;
      run o rest
    | Anchor d ->
      o.anchors <- (o.col, o.line) :: o.anchors;
      run o ((ind, m, d) :: (ind, m, Unanchor) :: rest)
    | Unanchor ->
      (match o.anchors with _ :: a -> o.anchors <- a | [] -> ());
      run o rest
    | Mark r ->
      r := o.line;
      run o rest
    | Depth (k, a) ->
      o.depth <- k;
      o.angles <- a;
      run o rest
    | Last_space c ->
      o.last_space <- c;
      run o rest
    | Operand ->
      o.last_space <- o.col;
      run o rest
    | Choose (a, b) ->
      let pick =
        if m = Flat || not (may_try o a) then a
        else
          let tail = closers rest in
          let ea, ta, la, _, ka = measure o ((ind, m, a) :: tail) in
          let eb, tb, lb, _, kb = measure ~bound:(ea, max_int, max_int) o ((ind, m, b) :: tail) in
          if (eb, tb, kb, lb) < (ea, ta, ka, la) then b else a
      in
      run o ((ind, m, pick) :: rest)
    | Mark_column r ->
      r := o.col;
      run o rest
    | Member_break (r, c) ->
      if o.line <> !r && m = Broken then newline o (!c + continuation_width);
      run o rest )

(** Lays [cmds] out on trial from where [o] stands, giving up past
    [bound]: the columns its lines run past the limit, its line breaks
    inside template argument lists, how many lines it starts, the sum of
    the bracket depths of its breaks and how many lists it breaks after
    their opening bracket, compared in that order. *)
and measure ?bound o cmds =
  let t =
    {o with trial = o.trial + 1; origin = o.line; excess = 0; bound; depth_sum = 0; opens = 0; angle_breaks = 0}
  in
  match run t cmds with
  | () ->
    finish_line t;
    (t.excess, t.angle_breaks, t.line - o.line, t.depth_sum, t.opens)
  | exception Abandoned -> (max_int, max_int, max_int, max_int, max_int)

(** Whether the layout [a] is no worse than [b], both laid out on trial
    from where [o] stands; [b] is abandoned once it is worse. *)
and first_better o a b =
  let ((e, t, l, _, _) as x) = measure o a in
  x <= measure ~bound:(e, t, l) o b

(** Lays out block [b] at the current position, merged into the line when
    the style allows and it fits before [rest]. *)
and render_block o b ~space ~rest =
  let base =
    match (b.bkind, o.anchors) with
    | (Lambda | Compound), (c, l) :: _ when l = o.line -> c
    | (Lambda | Compound), _ -> min o.last_space o.line_indent
    | _ -> o.stmt_indent
  in
  let items = List.filter (fun it -> it <> Blank) b.items in
  let simple = function
    | Stmt elems -> List.for_all (function Tok t -> t.kind <> Line_comment | Block _ -> false) elems
    | _ -> false
  in
  let merged =
    match (b.bkind, items) with
    | _ when b.lead <> None -> None
    | Control, _ -> None
    | _, [] -> Some "{}"
    | Function, _ when o.line <> o.stmt_line -> None
    | (Function | Lambda | Compound), [(Stmt elems as it)] when simple it ->
      Option.map (fun s -> "{ " ^ s ^ " }") (flat_text (stmt_doc elems))
    | Enum, _ when List.for_all simple items ->
      let texts = List.filter_map (function Stmt e -> flat_text (stmt_doc e) | _ -> None) items in
      if List.length texts = List.length items then Some ("{ " ^ String.concat " " texts ^ " }") else None
    | _ -> None
  in
  let closing = match b.closing with Some c -> c.text | None -> "" in
  let closing = if merged = Some "{}" then "" else closing in
  let rest = if b.bkind = Compound then List.map (fun (i, _, d) -> (i, Flat, d)) rest else rest in
  match merged with
  | Some s when fits_line o [(Flat, Text ((if space then " " else "") ^ s))] rest ->
    emit o ((if space then " " else "") ^ s)
  | _ ->
    emit o (if space then " {" else "{");
    ( match b.lead with
    | Some c ->
      emit o " ";
      let col = o.col in
      List.iteri
        (fun k l ->
          if k > 0 then newline o col;
          emit o l)
        (reflow_comment c.text ~col)
    | None -> () );
    let inner = if b.bkind = Namespace then base else base + indent_width in
    render_items o inner ~kind:b.bkind ~stem:"" b.items;
    newline o base;
    emit o (if closing = "" then "}" else closing)

(** Lays out the items of a block, or of the file, at indentation [ind]. *)
and render_items o ind ~kind ~stem items =
  ignore kind;
  let items = Array.of_list (space_items (sort_includes ~stem items)) in
  let n = Array.length items in
  let i = ref 0 in
  while !i < n do
    ( match items.(!i) with
    | Blank -> if o.trial = 0 && Buffer.length o.buf > 0 then Buffer.add_char o.buf '\n'
    | Pp t ->
      newline o 0;
      emit o t.text
    | Comment t -> render_comment o ind t
    | Label toks -> (
      newline o (max 0 (ind - indent_width));
      List.iteri (fun k t -> emit o ((if k > 0 && t.gap then " " else "") ^ t.text)) toks;
      (* a block statement after a case label opens on the label's line *)
      match if !i + 1 < n then Some items.(!i + 1) else None with
      | Some (Stmt [Block b]) when b.bkind = Plain ->
        incr i;
        render_block o b ~space:true ~rest:[]
      | _ -> () )
    | Stmt elems ->
      newline o ind;
      let saved = o.stmt_indent and saved_space = o.last_space in
      o.stmt_indent <- ind;
      o.stmt_line <- o.line;
      o.last_space <- ind;
      run o [(ind, Broken, stmt_doc elems)];
      o.stmt_indent <- saved;
      o.last_space <- saved_space );
    incr i
  done

(** Lays out a comment on a line of its own at indentation [ind]: a long
    line comment reflowed, a block comment's lines moved with its first. *)
and render_comment o ind t =
  newline o ind;
  match t.kind with
  | Line_comment -> List.iteri (fun k l -> if k > 0 then newline o ind; emit o l) (reflow_comment t.text ~col:ind)
  | _ ->
    let lines = String.split_on_char '\n' t.text in
    List.iteri
      (fun k l ->
        if k = 0 then emit o l
        else
          let trimmed = String.trim l in
          let lead = ref 0 in
          while !lead < String.length l && (l.[!lead] = ' ' || l.[!lead] = '\t') do incr lead done;
          if trimmed = "" then (if o.trial = 0 then Buffer.add_char o.buf '\n')
          else if trimmed.[0] = '*' then (
            newline o (ind + 1);
            emit o trimmed )
          else (
            newline o (max 0 (!lead - t.column + ind));
            emit o trimmed ))
      lines

(** Lays out C++ source [text], from the file named [file] if given (an
    implementation file's own header is included first). *)
let layout ?(file = "") text =
  let toks = lex text in
  normalise_spacing toks;
  let p = {toks; pos = 0} in
  let items = parse_items p ~inside:false ~kind:Namespace in
  let stem =
    if List.exists (Filename.check_suffix file) [".cpp"; ".cc"; ".cxx"; ".c"] then
      Filename.remove_extension (Filename.basename file)
    else ""
  in
  let o =
    { buf = Buffer.create (String.length text + 1024);
      col = 0;
      line = 0;
      line_indent = 0;
      pending = None;
      anchors = [];
      stmt_indent = 0;
      stmt_line = 0;
      trial = 0;
      origin = 0;
      excess = 0;
      bound = None;
      depth = 0;
      depth_sum = 0;
      angles = 0;
      angle_breaks = 0;
      opens = 0;
      last_space = 0 }
  in
  o.pending <- Some 0;
  render_items o 0 ~kind:Namespace ~stem items;
  Buffer.add_char o.buf '\n';
  Buffer.contents o.buf
