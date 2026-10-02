(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The placeholder syntax of custom mappings, parsed into tokens.

    A mapping's text is parsed once per category -- a type template, a term
    template, a match template -- and the tokens are cached by text, so the
    printer folds over tokens rather than scanning the text again where it
    is spelled.  Literal C++ between placeholders stays opaque. *)

(** Custom extraction syntax placeholder types for template string substitution.
*)
type custom_case =
  | CCscrut
  | CCty
  | CCbody of int
  | CCty_arg of int
  | CCelem of int
  | CCbr_var of int * int
  | CCbr_var_ty of int * int
  | CCstring of string
  | CCarg of int

(** Test whether a character is an ASCII digit. *)
let is_digit c = c >= '0' && c <= '9'

(** Parses an integer starting at [i], returns [(value, next_index)] or [None]
    if no digit is found at [i].

    @param s  the string being scanned
    @param i  starting position in [s]
    @param n  length of [s] (upper bound for the scan) *)
let parse_number s i n =
  let rec aux j = if j < n && is_digit s.[j] then aux (j + 1) else j in
  let j = aux i in
  if j = i then
    None
  else
    let num_str = String.sub s i (j - i) in
    Some (int_of_string num_str, j)

(* The following functions parse custom placeholders in extraction syntax
   strings: - parse_custom_fixed: parses fixed placeholders like %scrut or %ty -
   parse_numbered_args: parses placeholders like %a0, %t12 (single argument) -
   parse_custom_numbered_binders: parses placeholders like %b0a1, %b10a20 (two
   arguments) *)

(** Parses fixed custom placeholders like [%scrut] or [%ty] in a custom
    extraction syntax string. Returns a list of {!custom_case} chunks.

    @param esc  the fixed keyword after [%] (e.g. ["scrut"] or ["ty"])
    @param cc   the {!custom_case} token to emit when the placeholder is found
    @param s    the raw template string to scan *)
let parse_custom_fixed esc cc s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start chunks_rev =
    if i >= n then
      let last_chunk = String.sub s start (n - start) in
      List.rev (CCstring last_chunk :: chunks_rev)
    else
      match
        (s.[i], i + esc_len + 1 <= n)
      with
      | '%', true ->
        if esc = String.sub s (i + 1) esc_len then
          let chunk = String.sub s start (i - start) in
          aux
            (i + esc_len + 1)
            (i + esc_len + 1)
            (cc :: CCstring chunk :: chunks_rev)
        else
          aux (i + 1) start chunks_rev
      | _ -> aux (i + 1) start chunks_rev
  in
  aux 0 0 []

(** Parses single-argument custom placeholders like [%a0], [%t12].

    @param esc  the letter immediately after [%] (e.g. ["a"] or ["t"])
    @param f    maps the parsed integer index to a {!custom_case} token
    @param s    the raw template string to scan *)
let parse_numbered_args esc f s =
  let n = String.length s in
  let esc_len = String.length esc in
  let rec aux i start acc =
    if i >= n then
      List.rev
        ( if start < n then
            CCstring (String.sub s start (n - start)) :: acc
          else
            acc )
    else if s.[i] = '%' && i + esc_len < n && String.sub s (i + 1) esc_len = esc
    then
      match
        parse_number s (i + 1 + esc_len) n
      with
      | Some (idx, j) ->
        let chunk = String.sub s start (i - start) in
        aux j j (f idx :: CCstring chunk :: acc)
      | None -> aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

(** Parses double-argument custom placeholders like [%b0a1], [%b10a20].

    @param esc1  the letter after [%] for the first index (e.g. ["b"])
    @param esc2  the letter after the first index for the second (e.g. ["a"])
    @param f     maps [(idx1, idx2)] to a {!custom_case} token
    @param s     the raw template string to scan *)
let parse_custom_numbered_binders esc1 esc2 f s =
  let n = String.length s in
  let len1 = String.length esc1 in
  let len2 = String.length esc2 in
  let rec aux i start acc =
    if i >= n then
      List.rev
        ( if start < n then
            CCstring (String.sub s start (n - start)) :: acc
          else
            acc )
    else if s.[i] = '%' && i + len1 < n && String.sub s (i + 1) len1 = esc1 then
      match
        parse_number s (i + 1 + len1) n
      with
      | Some (idx1, j) when j + len2 <= n && String.sub s j len2 = esc2 ->
        ( match parse_number s (j + len2) n with
        | Some (idx2, k) ->
          let chunk = String.sub s start (i - start) in
          aux k k (f idx1 idx2 :: CCstring chunk :: acc)
        | None -> aux (i + 1) start acc )
      | _ -> aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

(** Expand placeholders in a command list using a parser function.
    For each [CCstring] chunk, apply [parser] to produce new chunks.
    Non-string chunks are passed through unchanged.

    @param parser  function that splits a raw string into {!custom_case} chunks
    @param cmds    existing command list to expand *)
let expand_custom_chunks parser cmds =
  List.fold_left
    (fun prev curr ->
      match curr with
      | CCstring s -> prev @ parser s
      | _ -> prev @ [curr] )
    []
    cmds

(** Expand single-argument numbered placeholders (e.g. [%a0], [%t1]) in a
    command list. *)
let expand_numbered_args esc f = expand_custom_chunks (parse_numbered_args esc f)

(** Expand double-argument binder placeholders (e.g. [%b0a1]) in a command
    list. *)
let expand_custom_binders esc1 esc2 f = expand_custom_chunks (parse_custom_numbered_binders esc1 esc2 f)

(** Expand fixed-name placeholders (e.g. [%scrut], [%ty]) in a command list. *)
let expand_custom_fixed esc cc = expand_custom_chunks (parse_custom_fixed esc cc)

(** Expand [%elem] / [%elem{i}] placeholders (completeness-aware element
    wrapping, WRAP.md): like [%t{i}] but rendered boxed when the element type
    recurses through a boxed-element container. Bare [%elem] means index 0. *)
let expand_elem_args cmds =
  let cmds = expand_numbered_args "elem" (fun i -> CCelem i) cmds in
  expand_custom_fixed "elem" (CCelem 0) cmds

(** Parse a custom {e type} template: the [%t{i}] and [%elem{i}] holes of a
    mapping such as ["std::pair<%t0,%t1>"].  This and {!parse_term_template}
    are the only places that know the syntax; consumers fold over the tokens
    rather than scanning the text again. *)
let parse_type_template s =
  expand_elem_args (parse_numbered_args "t" (fun i -> CCty_arg i) s)

(** A custom mapping that names a template without saying where its arguments
    go still takes them: ["Sum1"] applied to [E], [F] means ["Sum1<E, F>"],
    exactly as a non-custom name would.  Normalising the mapping here, before
    it is parsed, is what keeps every printer of a custom type spelling it the
    same way -- a type spelled one way in a signature and another in a body is
    two types. *)
let custom_template_with_args s nargs =
  if nargs = 0 || String.contains s '%' then s
  else
    s
    ^ "<"
    ^ String.concat ", " (List.init nargs (fun i -> Printf.sprintf "%%t%d" i))
    ^ ">"

(** Parse a custom {e term} template: {!parse_type_template} plus the [%a{i}]
    holes that splice value arguments. *)
let parse_term_template s =
  expand_elem_args
    (expand_numbered_args "t" (fun i -> CCty_arg i)
       (parse_numbered_args "a" (fun i -> CCarg i) s))

(** Flatten a token list known to hold only literal text back into a string. *)
let flatten_custom_strings cmds =
  String.concat ""
    (List.map (function CCstring s -> s
      | _ -> CErrors.anomaly (Pp.str "flatten_custom_strings: non-string command")) cmds)

(** A memoized parser: a mapping's text parses to the same tokens every time. *)
let memoized parse =
  let cache = Hashtbl.create 64 in
  fun s ->
    match Hashtbl.find_opt cache s with
    | Some tokens -> tokens
    | None ->
      let tokens = parse s in
      Hashtbl.add cache s tokens;
      tokens

let type_template = memoized parse_type_template
let term_template = memoized parse_term_template

let match_template =
  memoized (fun s ->
      parse_custom_fixed "scrut" CCscrut s
      |> expand_custom_fixed "ty" CCty
      |> expand_numbered_args "t" (fun i -> CCty_arg i)
      |> expand_numbered_args "br" (fun i -> CCbody i)
      |> expand_custom_binders "b" "a" (fun i j -> CCbr_var (i, j))
      |> expand_custom_binders "b" "t" (fun i j -> CCbr_var_ty (i, j)) )

let with_result name s =
  flatten_custom_strings (parse_custom_fixed "result" (CCstring name) s)

type drain_token = Drain_text of string | Drain_yield of string

let drain_template s =
  let n = String.length s in
  let yield = "%yield(" in
  let yl = String.length yield in
  let tokens = ref [] in
  let buf = Buffer.create 64 in
  let flush () =
    if Buffer.length buf > 0 then begin
      tokens := Drain_text (Buffer.contents buf) :: !tokens;
      Buffer.clear buf
    end
  in
  let i = ref 0 in
  while !i < n do
    if !i + yl <= n && String.equal (String.sub s !i yl) yield then begin
      (* The argument runs to the matching parenthesis, so it may itself
         contain parentheses. *)
      let j = ref (!i + yl) in
      let depth = ref 1 in
      while !j < n && !depth > 0 do
        (match s.[!j] with '(' -> incr depth | ')' -> decr depth | _ -> ());
        if !depth > 0 then incr j
      done;
      flush ();
      tokens := Drain_yield (String.sub s (!i + yl) (!j - (!i + yl))) :: !tokens;
      i := !j + 1
    end else begin
      Buffer.add_char buf s.[!i];
      incr i
    end
  done;
  flush ();
  List.rev !tokens
