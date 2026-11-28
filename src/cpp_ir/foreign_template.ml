(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The placeholder syntax of custom mappings, parsed into tokens.

    A mapping's text is parsed once per category -- a type template, a term
    template, a match template -- and the tokens are cached by text, so the
    printer folds over tokens rather than scanning the text again where it
    is spelled.  Literal C++ between placeholders stays opaque. *)

(** One token of a parsed mapping: a placeholder, or literal text
    ([Text]).  Each constructor is documented in [foreign_template.mli]. *)
type custom_case =
  | Scrut
  | Ty
  | Body of int
  | Ty_arg of int
  | Elem of int
  | Br_var of int * int
  | Br_var_ty of int * int
  | Text of string
  | Arg of int
  | Ret
  | Result

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

(* Three scanners split a template's text at its placeholders:
   [parse_custom_fixed] at fixed ones like [%scrut] or [%ty],
   [parse_numbered_args] at one-index ones like [%a0] or [%t12], and
   [parse_custom_numbered_binders] at two-index ones like [%b0a1] or
   [%b10a20]. *)

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
      List.rev (Text last_chunk :: chunks_rev)
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
            (cc :: Text chunk :: chunks_rev)
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
            Text (String.sub s start (n - start)) :: acc
          else
            acc )
    else if s.[i] = '%' && i + esc_len < n && String.sub s (i + 1) esc_len = esc
    then
      match
        parse_number s (i + 1 + esc_len) n
      with
      | Some (idx, j) ->
        let chunk = String.sub s start (i - start) in
        aux j j (f idx :: Text chunk :: acc)
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
            Text (String.sub s start (n - start)) :: acc
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
          aux k k (f idx1 idx2 :: Text chunk :: acc)
        | None -> aux (i + 1) start acc )
      | _ -> aux (i + 1) start acc
    else
      aux (i + 1) start acc
  in
  aux 0 0 []

(** Expand placeholders in a command list using a parser function.
    For each [Text] chunk, apply [parser] to produce new chunks.
    Non-string chunks are passed through unchanged.

    @param parser  function that splits a raw string into {!custom_case} chunks
    @param cmds    existing command list to expand *)
let expand_custom_chunks parser cmds =
  List.fold_left
    (fun prev curr ->
      match curr with
      | Text s -> prev @ parser s
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

(** Expand [%elem] / [%elem{i}] placeholders: like [%t{i}], but the element
    type is written inside the container's element box ([BoxedComponent]) where it
    recurses through the container.  Bare [%elem] means index 0. *)
let expand_elem_args cmds =
  let cmds = expand_numbered_args "elem" (fun i -> Elem i) cmds in
  expand_custom_fixed "elem" (Elem 0) cmds

(** Parse a custom {e type} template: the [%t{i}] and [%elem{i}] holes of a
    mapping such as ["std::pair<%t0,%t1>"].  The parsers of this module are
    the only places that know the syntax; consumers fold over the tokens
    rather than scanning the text again. *)
let parse_type_template s =
  expand_elem_args (parse_numbered_args "t" (fun i -> Ty_arg i) s)

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

let type_arity tokens =
  List.fold_left (fun n -> function Ty_arg i | Elem i -> max n (i + 1) | _ -> n) 0 tokens

(** Parse a custom {e term} template: {!parse_type_template} plus the [%a{i}]
    holes that splice value arguments and the [%ret] hole that spells the
    type the call yields. *)
let parse_term_template s =
  expand_custom_fixed "ret" Ret
    (expand_elem_args
       (expand_numbered_args "t" (fun i -> Ty_arg i)
          (parse_numbered_args "a" (fun i -> Arg i) s)))

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

(* A match template: [%scrut], [%ty], [%t{i}], [%br{i}] and the binder
   holes [%b{i}a{j}] and [%b{i}t{j}]. *)
let match_template =
  memoized (fun s ->
      parse_custom_fixed "scrut" Scrut s
      |> expand_custom_fixed "ty" Ty
      |> expand_numbered_args "t" (fun i -> Ty_arg i)
      |> expand_numbered_args "br" (fun i -> Body i)
      |> expand_custom_binders "b" "a" (fun i j -> Br_var (i, j))
      |> expand_custom_binders "b" "t" (fun i j -> Br_var_ty (i, j)) )

(* Split [tokens] into statements at the top-level semicolons of their
   literal text, tracking quotes and parentheses; see
   {!block_statements}. *)
let statements tokens =
  let depth = ref 0 in
  let quote = ref None in
  let stmts = ref [] in
  let current = ref [] in
  let text = Buffer.create 64 in
  let flush_text () =
    if Buffer.length text > 0 then begin
      current := Text (Buffer.contents text) :: !current;
      Buffer.clear text
    end
  in
  let end_statement () =
    flush_text ();
    stmts := List.rev !current :: !stmts;
    current := []
  in
  let literal s =
    let n = String.length s in
    let i = ref 0 in
    while !i < n do
      let c = s.[!i] in
      ( match !quote with
      | Some q ->
        Buffer.add_char text c;
        if c = '\\' && !i + 1 < n then begin
          Buffer.add_char text s.[!i + 1];
          incr i
        end
        else if c = q then quote := None
      | None ->
        if c = ';' && !depth = 0 then end_statement ()
        else begin
          if c = '"' || c = '\'' then quote := Some c
          else if c = '(' then incr depth
          else if c = ')' then decr depth;
          Buffer.add_char text c
        end );
      incr i
    done
  in
  List.iter
    (function
      | Text s -> literal s
      | hole ->
        flush_text ();
        current := hole :: !current)
    tokens;
  end_statement ();
  (* The blanks [String.trim] removes. *)
  let blank c = c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\012' in
  let ltrim s =
    let n = String.length s in
    let i = ref 0 in
    while !i < n && blank s.[!i] do incr i done;
    String.sub s !i (n - !i)
  in
  let rtrim s =
    let n = ref (String.length s) in
    while !n > 0 && blank s.[!n - 1] do decr n done;
    String.sub s 0 !n
  in
  let trim stmt =
    let stmt = match stmt with Text s :: rest -> Text (ltrim s) :: rest | _ -> stmt in
    let stmt =
      match List.rev stmt with Text s :: rest -> List.rev (Text (rtrim s) :: rest) | _ -> stmt
    in
    List.filter (function Text "" -> false | _ -> true) stmt
  in
  List.filter (fun stmt -> stmt <> []) (List.map trim (List.rev !stmts))

(* [%result] is read first: the term placeholders are read in the text
   around it. *)
let block_statements =
  memoized (fun s ->
      statements
        (expand_custom_fixed "ret" Ret
           (expand_elem_args
              (expand_numbered_args "t" (fun i -> Ty_arg i)
                 (expand_numbered_args "a" (fun i -> Arg i) (parse_custom_fixed "result" Result s))))))

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

let passes_through s =
  match
    List.filter (function Text t -> String.trim t <> "" | _ -> true) (term_template s)
  with
  | [Arg i] -> Some i
  | _ -> None

let pair_projection_field s =
  match term_template s with
  | [Text ""; Arg 0; Text ((".first" | ".second") as f)]
  | [Arg 0; Text ((".first" | ".second") as f)] ->
    Some (String.sub f 1 (String.length f - 1))
  | _ -> None

let is_pair_projection s = Option.has_some (pair_projection_field s)

let unbraced_binders s =
  let depth = ref 0 in
  List.filter_map
    (function
      | Text t ->
        String.iter (function '{' -> incr depth | '}' -> decr depth | _ -> ()) t;
        None
      | Br_var (i, j) when !depth = 0 -> Some (i, j)
      | _ -> None)
    (match_template s)

let arg_mentions s =
  let tokens = term_template s in
  let holes = List.filter_map (function Arg j -> Some j | _ -> None) tokens in
  let last = List.fold_left max (-1) holes in
  fun i ->
    if i > last then 1
    else List.length (List.filter (Int.equal i) holes)

let mentions_each_arg_once s =
  let rec go seen = function
    | [] -> true
    | Arg i :: rest -> (not (List.mem i seen)) && go (i :: seen) rest
    | _ :: rest -> go seen rest
  in
  go [] (term_template s)

type binding = By_reference | By_value

(* A structured binding of the scrutinee in front of the branch:
   [<declarator> [%b0a0, ..., %b0aN] = %scrut; %br0], read with its spacing
   ignored. *)
let structured_binding s =
  let squeeze t = String.of_seq (Seq.filter (fun c -> not (List.mem c [' '; '\t'; '\n'; '\r'])) (String.to_seq t)) in
  let tokens =
    List.filter_map
      (function Text t -> if squeeze t = "" then None else Some (Text (squeeze t)) | t -> Some t)
      (match_template s)
  in
  let rec binders j = function
    | Br_var (0, j') :: rest when j' = j -> (
      match rest with Text "," :: rest -> binders (j + 1) rest | _ -> Some rest )
    | _ -> None
  in
  let mode = function "constauto&[" -> Some By_reference | "auto[" -> Some By_value | _ -> None in
  match tokens with
  | Text declarator :: rest -> (
    match (mode declarator, binders 0 rest) with
    | Some m, Some [Text "]="; Scrut; Text ";"; Body 0] -> Some m
    | _ -> None )
  | _ -> None

(* [<type> %b{i}a{j} = ...], the binder's one mention, its type [auto], a
   type argument or its own type hole, with nothing else between it and the
   statement's start: a variable of its own, initialised by a copy. *)
let declared_by_value s i j =
  let squeeze t = String.of_seq (Seq.filter (fun c -> not (List.mem c [' '; '\t'; '\n'; '\r'])) (String.to_seq t)) in
  let tokens = match_template s in
  let is_binder = function Br_var (i', j') -> i' = i && j' = j | _ -> false in
  (* The tokens of the statement before the binder, innermost first: up to
     the last [;], [{] or [}] of the literal text. *)
  let rec prefix acc = function
    | [] -> acc
    | Text t :: rest -> (
      match List.filter_map (fun c -> String.rindex_opt t c) [';'; '{'; '}'] with
      | [] -> prefix (Text t :: acc) rest
      | ks ->
        let k = List.fold_left max 0 ks in
        Text (String.sub t (k + 1) (String.length t - k - 1)) :: acc )
    | tok :: rest -> prefix (tok :: acc) rest
  in
  let rec find before = function
    | [] -> None
    | tok :: rest when is_binder tok -> Some (before, rest)
    | tok :: rest -> find (tok :: before) rest
  in
  List.length (List.filter is_binder tokens) = 1
  &&
  match find [] tokens with
  | Some (before, Text after :: _) ->
    let after = squeeze after in
    let declared =
      List.filter (function Text t -> squeeze t <> "" | _ -> true) (prefix [] before)
    in
    String.length after >= 1 && after.[0] = '='
    && (String.length after < 2 || after.[1] <> '=')
    && (match declared with
        | [Text t] -> squeeze t = "auto"
        | [Ty_arg _] | [Ty] -> true
        | [Br_var_ty (i', j')] -> i' = i && j' = j
        | _ -> false)
  | _ -> false

let bound_by_value s = "auto " ^ String.sub s (String.index s '[') (String.length s - String.index s '[')

(* What the language spells without a declaration: a type template naming
   only these, its holes and punctuation needs no header. *)
let builtin_type_words =
  [ "auto"; "bool"; "char"; "char8_t"; "char16_t"; "char32_t"; "class"; "const"; "decltype"; "double"; "enum";
    "float"; "int"; "long"; "short"; "signed"; "struct"; "typename"; "unsigned"; "void"; "volatile"; "wchar_t" ]

let declared_type_names s =
  let is_start c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_' in
  let is_part c = is_start c || (c >= '0' && c <= '9') || c = ':' in
  (* A name right after [::] -- [%t0::type] -- is a member of what is in
     front of it, not something a header declares. *)
  let names lit =
    let n = String.length lit in
    let rec go i acc =
      if i >= n then acc
      else if is_start lit.[i] && (i = 0 || not (is_part lit.[i - 1])) then
        let rec stop j = if j < n && is_part lit.[j] then stop (j + 1) else j in
        let j = stop i in
        go j (String.sub lit i (j - i) :: acc)
      else go (i + 1) acc
    in
    List.rev (go 0 [])
  in
  List.filter
    (fun w -> not (List.mem w builtin_type_words))
    (List.concat_map (function Text lit -> names lit | _ -> []) (type_template s))

(* The header declaring a standard-library name, by what follows [std::] in
   it -- a nested namespace ([chrono], [filesystem]) stands for every name
   in it.  Only names mappings are seen to write: a name missing here is not
   checked. *)
let standard_headers =
  [ ("utility", ["move"; "forward"; "pair"; "make_pair"; "swap"; "exchange"; "declval"; "in_place"]);
    ("string", ["string"; "to_string"; "getline"; "stoi"; "stol"; "stoll"; "stoul"; "stoull"; "stod"]);
    ("string_view", ["string_view"; "basic_string_view"]);
    ("optional", ["optional"; "make_optional"; "nullopt"; "nullopt_t"; "bad_optional_access"]);
    ("memory", ["shared_ptr"; "make_shared"; "unique_ptr"; "make_unique"; "weak_ptr"; "enable_shared_from_this"]);
    ("functional", ["function"; "invoke"; "equal_to"; "hash"; "bad_function_call"]);
    ("vector", ["vector"]);
    ("deque", ["deque"]);
    ("array", ["array"]);
    ("map", ["map"]);
    ("set", ["set"]);
    ("unordered_map", ["unordered_map"]);
    ("variant", ["variant"; "monostate"; "visit"; "get_if"; "holds_alternative"; "bad_variant_access"]);
    ("any", ["any"; "any_cast"; "bad_any_cast"; "make_any"]);
    ("algorithm", ["max"; "min"; "clamp"; "reverse"; "sort"; "find"; "copy"]);
    ("numeric", ["accumulate"; "gcd"; "lcm"]);
    ("stdexcept", ["runtime_error"; "logic_error"; "out_of_range"; "length_error"; "invalid_argument"]);
    ("iostream", ["cout"; "cin"; "cerr"; "clog"]);
    ("fstream", ["ifstream"; "ofstream"; "fstream"]);
    ("sstream", ["stringstream"; "istringstream"; "ostringstream"]);
    ("iterator", ["istreambuf_iterator"; "back_inserter"]);
    ("thread", ["thread"; "this_thread"]);
    ("future", ["future"; "shared_future"; "async"; "launch"; "promise"]);
    ("mutex", ["mutex"; "lock_guard"; "unique_lock"]);
    ("atomic", ["atomic"]);
    ("chrono", ["chrono"]);
    ("filesystem", ["filesystem"]);
    ("system_error", ["error_code"; "system_error"]);
    ("random", ["random_device"; "mt19937"; "uniform_int_distribution"]);
    ("complex", ["complex"]);
    ("cmath", ["sqrt"; "pow"; "floor"; "ceil"; "signbit"; "fpclassify"; "isnan"; "isinf"; "fabs"]);
    ("cstdlib", ["getenv"; "rand"; "srand"; "exit"; "abort"]);
    ("cstdint", ["int8_t"; "int16_t"; "int32_t"; "int64_t"; "uint8_t"; "uint16_t"; "uint32_t"; "uint64_t"]);
    ("cstddef", ["size_t"; "ptrdiff_t"; "nullptr_t"; "byte"]);
    ("limits", ["numeric_limits"]);
    ("exception", ["terminate"; "exception"; "exception_ptr"]);
    ("bit", ["bit_cast"; "popcount"; "countl_zero"; "countr_zero"]);
    ("type_traits",
      [ "type_identity_t"; "remove_pointer_t"; "remove_cvref_t"; "decay_t"; "invoke_result_t"; "is_invocable_r_v";
        "is_same_v"; "conditional_t"; "enable_if_t" ]) ]

let standard_header_of =
  let by_name = Hashtbl.create 128 in
  List.iter (fun (header, names) -> List.iter (fun n -> Hashtbl.replace by_name n header) names) standard_headers;
  Hashtbl.find_opt by_name

let standard_names_written tokens =
  let is_word c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' in
  let names lit =
    let n = String.length lit in
    let rec go i acc =
      match CString.string_index_from lit i "std::" with
      | j ->
        let stop = let rec stop k = if k < n && is_word lit.[k] then stop (k + 1) else k in stop (j + 5) in
        (* [crane::std::x] or [mystd::x] is not the standard library's. *)
        let at_start = j = 0 || not (is_word lit.[j - 1] || lit.[j - 1] = ':') in
        let name = String.sub lit (j + 5) (stop - j - 5) in
        go stop (if at_start && name <> "" then name :: acc else acc)
      | exception Not_found -> acc
    in
    go 0 []
  in
  List.sort_uniq compare
    (List.concat_map
       (function
         | Text lit ->
           List.filter_map (fun name -> Option.map (fun h -> ("std::" ^ name, h)) (standard_header_of name)) (names lit)
         | _ -> [])
       tokens)

(* A match template's tokens as characters of its literal text and holes. *)
type chain_item = Char of char | Hole of custom_case

let conditional_chain s =
  let items =
    List.concat_map
      (function Text t -> List.init (String.length t) (fun i -> Char t.[i]) | h -> [Hole h])
      (match_template s)
  in
  let rec ws = function Char (' ' | '\t' | '\n' | '\r') :: rest -> ws rest | l -> l in
  let rec word w i l =
    if i = String.length w then Some l
    else match l with Char c :: rest when c = w.[i] -> word w (i + 1) rest | _ -> None
  in
  let ( let* ) = Option.bind in
  (* the test up to the parenthesis closing the one already opened *)
  let rec test depth acc = function
    | Char ')' :: rest when depth = 0 -> Some (List.rev acc, rest)
    | (Char c as x) :: rest ->
      let depth = if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth in
      test depth (x :: acc) rest
    | (Hole Scrut as x) :: rest -> test depth (x :: acc) rest
    | _ -> None
  in
  let braced l =
    let* l = word "{" 0 (ws l) in
    match ws l with
    | Hole (Body i) :: rest ->
      let* rest = word "}" 0 (ws rest) in
      Some (i, ws rest)
    | _ -> None
  in
  let tokens items =
    let flush buf acc = if Buffer.length buf = 0 then acc else Text (Buffer.contents buf) :: acc in
    let buf = Buffer.create 16 in
    let acc =
      List.fold_left
        (fun acc -> function
          | Char c ->
            Buffer.add_char buf c;
            acc
          | Hole h ->
            let acc = flush buf acc in
            Buffer.clear buf;
            h :: acc )
        [] items
    in
    List.rev (flush buf acc)
  in
  let rec conditional l =
    let* l = word "if" 0 (ws l) in
    let* l = word "(" 0 (ws l) in
    let* cond, l = test 0 [] l in
    let* i, l = braced l in
    match l with
    | [] -> Some ([(tokens cond, i)], None)
    | l -> (
      let* l = word "else" 0 l in
      match ws l with
      | Char '{' :: _ as l ->
        let* j, l = braced l in
        if l = [] then Some ([(tokens cond, i)], Some j) else None
      | l ->
        let* tests, final = conditional l in
        Some ((tokens cond, i) :: tests, final) )
  in
  conditional items
