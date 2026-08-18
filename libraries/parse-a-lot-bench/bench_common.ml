(* SPDX-License-Identifier: BSD-3-Clause *)
module Yb = Yojson.Basic
module Yu = Yojson.Basic.Util

(***********************************************************************)
(* Coq string utilities                                                *)
(***********************************************************************)

type coq_string = char list

let coqstr_of_str (s : string) : coq_string =
  List.init (String.length s) (String.get s)

(* Char.escaped per byte — only for diagnostic/display use *)
let str_of_coqstr (c : coq_string) : string =
  String.concat "" (List.map Char.escaped c)

(* Lossless round-trip: coq_string -> original raw bytes *)
let raw_str_of_coqstr (c : coq_string) : string =
  let b = Buffer.create (List.length c) in
  List.iter (Buffer.add_char b) c;
  Buffer.contents b

(* The lexer/parser produced by standard Coq->OCaml extraction is genuinely
   non-tail recursive, so it consumes O(n) native stack.  On the largest
   inputs (~200k tokens) this overflows the default 8 MB main-thread stack.
   Re-exec ourselves once under a raised stack rlimit (macOS caps this near
   64 MB, which is sufficient here; Linux honours a larger value) so every input
   can be parsed.  Guarded by an env var so the re-exec happens at most once. *)
let ensure_big_stack () =
  if Sys.getenv_opt "PA_BIGSTACK" = None then begin
    let quoted =
      Array.to_list Sys.argv |> List.map Filename.quote |> String.concat " "
    in
    let cmd =
      Printf.sprintf
        "ulimit -s 1048576 2>/dev/null || ulimit -s 65500 2>/dev/null; exec %s"
        quoted
    in
    Unix.putenv "PA_BIGSTACK" "1";
    (try Unix.execv "/bin/sh" [| "/bin/sh"; "-c"; cmd |] with _ -> ())
  end

let chars_from_file (fname : string) : coq_string =
  let ic = open_in fname in
  let cs = really_input_string ic (in_channel_length ic) |> coqstr_of_str in
  let () = close_in ic in
  cs

(***********************************************************************)
(* Runner output type                                                  *)
(***********************************************************************)

type parse_metadata = {
  parse_result : string;     (* "unique" | "ambig" | "result_reject:…" | "result_error:…" *)
  num_tokens   : int;
  parse_nodes  : int option; (* AST node count from our parser *)
  ref_nodes    : int option; (* cross-validation count (JSON only) *)
}

let json_of_int_opt = function
  | None   -> `Null
  | Some n -> `Int n

let metadata_to_json_line (m : parse_metadata) : string =
  let j = `Assoc
    [ ("parse_result", `String m.parse_result)
    ; ("num_tokens",   `Int    m.num_tokens)
    ; ("parse_nodes",  json_of_int_opt m.parse_nodes)
    ; ("ref_nodes",    json_of_int_opt m.ref_nodes)
    ] in
  Yb.to_string j

let metadata_of_json_line (s : string) : parse_metadata =
  let j = Yb.from_string s in
  { parse_result = j |> Yu.member "parse_result" |> Yu.to_string
  ; num_tokens   = j |> Yu.member "num_tokens"   |> Yu.to_int
  ; parse_nodes  = j |> Yu.member "parse_nodes"  |> Yu.to_int_option
  ; ref_nodes    = j |> Yu.member "ref_nodes"    |> Yu.to_int_option
  }
