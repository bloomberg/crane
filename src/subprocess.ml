(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Shell-free subprocess execution and argument handling.

    All child processes receive explicit argv arrays. Temporary files are used
    only to capture streams for callers that need complete output. *)

(** Captured termination status, stdout, and stderr from one child process. *)
type captured_output = {
  status : Unix.process_status;  (** Status returned by [waitpid]. *)
  stdout : string;  (** Complete standard-output stream. *)
  stderr : string;  (** Complete standard-error stream. *)
}

(** Malformed quoted or escaped input supplied to {!split_arguments}. *)
exception Invalid_arguments of string

(** [read_file filename] returns the complete binary contents of [filename] and
    closes the input channel on both success and failure. *)
let read_file filename =
  let ic = open_in_bin filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(** Remove [filename] when it exists; otherwise do nothing. *)
let remove_if_exists filename =
  if Sys.file_exists filename then Sys.remove filename

(** Test whether [filename] identifies an executable non-directory entry. *)
let executable_file filename =
  try
    Unix.access filename [Unix.X_OK];
    not (Sys.is_directory filename)
  with Unix.Unix_error _ -> false

(** Locate an executable either at its explicit path or by searching [PATH]. *)
let executable_available executable =
  if String.contains executable Filename.dir_sep.[0] then
    executable_file executable
  else
    match Sys.getenv_opt "PATH" with
    | None -> false
    | Some path ->
      String.split_on_char ':' path
      |> List.exists (fun directory ->
           executable_file (Filename.concat directory executable) )

(** Execute a program directly, with optional file redirection, and wait for
    its termination. Open redirection descriptors are always closed. *)
let run ?stdin_file ?stdout_file ?stderr_file program args =
  let open_output filename =
    Unix.openfile
      filename
      [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_TRUNC]
      0o600
  in
  let stdin_fd =
    Option.map (fun filename -> Unix.openfile filename [Unix.O_RDONLY] 0) stdin_file
  in
  let stdout_fd = Option.map open_output stdout_file in
  let stderr_fd = Option.map open_output stderr_file in
  let close_redirects () =
    Option.iter Unix.close stdin_fd;
    Option.iter Unix.close stdout_fd;
    Option.iter Unix.close stderr_fd
  in
  Fun.protect
    ~finally:close_redirects
    (fun () ->
      let stdin_fd = match stdin_fd with Some fd -> fd | None -> Unix.stdin in
      let stdout_fd = match stdout_fd with Some fd -> fd | None -> Unix.stdout in
      let stderr_fd = match stderr_fd with Some fd -> fd | None -> Unix.stderr in
      let argv = Array.of_list (program :: args) in
      let pid = Unix.create_process program argv stdin_fd stdout_fd stderr_fd in
      CUnix.waitpid_non_intr pid )

(** Execute a program while capturing stdout and stderr in separate temporary
    files. The temporary files are deleted after their contents are read. *)
let capture program args =
  let stdout_file = Filename.temp_file "crane_process_stdout" ".log" in
  let stderr_file = Filename.temp_file "crane_process_stderr" ".log" in
  Fun.protect
    ~finally:(fun () ->
      remove_if_exists stdout_file;
      remove_if_exists stderr_file )
    (fun () ->
      let status = run ~stdout_file ~stderr_file program args in
      {
        status;
        stdout = read_file stdout_file;
        stderr = read_file stderr_file;
      } )

(** Run [program] with [input] fed on standard input, capturing stdout and
    stderr. The child never sees a shell: [input] is staged through a temporary
    file wired directly to the child's stdin descriptor. All temporary files are
    removed even when execution raises. *)
let filter program args input =
  let stdin_file = Filename.temp_file "crane_process_stdin" ".in" in
  let stdout_file = Filename.temp_file "crane_process_stdout" ".log" in
  let stderr_file = Filename.temp_file "crane_process_stderr" ".log" in
  Fun.protect
    ~finally:(fun () ->
      remove_if_exists stdin_file;
      remove_if_exists stdout_file;
      remove_if_exists stderr_file )
    (fun () ->
      let oc = open_out_bin stdin_file in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () -> output_string oc input);
      let status = run ~stdin_file ~stdout_file ~stderr_file program args in
      {
        status;
        stdout = read_file stdout_file;
        stderr = read_file stderr_file;
      } )

(** Convert Unix termination states to conventional integer exit codes. *)
let exit_code = function
  | Unix.WEXITED n -> n
  | Unix.WSIGNALED n -> 128 + n
  | Unix.WSTOPPED n -> 128 + n

(** Tokenize shell-like argument text without executing or expanding it.

    The parser implements quoting and escaping only: it deliberately performs
    no variable, wildcard, command, or tilde expansion. *)
let split_arguments arguments =
  let args = ref [] in
  let token = Buffer.create (String.length arguments) in
  let token_started = ref false in
  let push_token () =
    if !token_started then (
      args := Buffer.contents token :: !args;
      Buffer.clear token;
      token_started := false )
  in
  let add_char c =
    token_started := true;
    Buffer.add_char token c
  in
  let invalid message = raise (Invalid_arguments message) in
  let rec loop i quote =
    if i = String.length arguments then
      match quote with
      | Some _ -> invalid "unterminated quoted argument"
      | None -> push_token ()
    else
      let c = arguments.[i] in
      match (quote, c) with
      | None, (' ' | '\t' | '\n' | '\r') ->
        push_token ();
        loop (i + 1) None
      | None, ('\'' | '"' as q) ->
        token_started := true;
        loop (i + 1) (Some q)
      | Some q, c when Char.equal q c -> loop (i + 1) None
      | (None | Some '"'), '\\' ->
        if i + 1 = String.length arguments then
          invalid "trailing backslash"
        else (
          add_char arguments.[i + 1];
          loop (i + 2) quote )
      | _, c ->
        add_char c;
        loop (i + 1) quote
  in
  loop 0 None;
  List.rev !args
