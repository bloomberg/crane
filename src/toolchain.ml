(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Native C++ and OCaml compiler integration.

    Compiler commands are assembled as argv lists and executed through
    {!Subprocess}. The selected Crane standard-library mode controls whether
    standard or BDE-specific C++ arguments are emitted. *)

(** Raised when the Clang C++ compiler is not available. *)
exception NoClangFound

(** Non-zero Clang exit code paired with captured diagnostics. *)
exception ClangError of int * string

(** Raised when the native OCaml compiler is not available. *)
exception NoOcamloptFound

(** Non-zero [ocamlopt] exit code paired with captured diagnostics. *)
exception OcamloptError of int * string

(** Read an entire binary file, closing its channel reliably. *)
let read_file filename =
  let ic = open_in_bin filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(** Remove a file when present. *)
let remove_if_exists filename =
  if Sys.file_exists filename then Sys.remove filename

(** Allocate a temporary file whose name identifies the compiler and input. *)
let make_error_file prefix infile =
  Filename.temp_file (prefix ^ Filename.basename infile ^ "_error") ".log"

(** Report whether Crane is currently targeting the BDE standard library. *)
let is_bde () = String.equal (Table.std_lib ()) "BDE"

(** Return the configured BDE root without a trailing slash. *)
let normalize_bde_dir () =
  let directory = Table.bde_dir () in
  let length = String.length directory in
  if length > 0 && Char.equal directory.[length - 1] '/' then
    String.sub directory 0 (length - 1)
  else
    directory

(** Convert values into alternating [prefix; value] argument pairs. *)
let prepend_to_all prefix values =
  List.fold_right (fun value result -> prefix :: value :: result) values []

(** Run a compiler with stderr redirected to [errfile], then return its status
    and diagnostics. The diagnostics file is removed on every handled path. *)
let compiler_output errfile program args =
  let status =
    try Subprocess.run ~stderr_file:errfile program args
    with exn ->
      remove_if_exists errfile;
      raise exn
  in
  let errors = if Sys.file_exists errfile then read_file errfile else "" in
  remove_if_exists errfile;
  (status, errors)

(** Compile or link one C++ source file with [clang++].

    Include directories and user flags are kept as distinct argv entries. BDE
    mode selects C++20 and the configured BDE headers/libraries; standard mode
    selects C++23. *)
let compile_cpp
    ?(shouldlink = false)
    ?(includes = [])
    ?(flags = [])
    ?outfile
    ?errfile
    infile =
  if not (Subprocess.executable_available "clang++") then raise NoClangFound;
  let errfile =
    match errfile with
    | Some filename -> filename
    | None -> make_error_file "cpp_" infile
  in
  let outfile =
    match outfile with
    | Some filename -> filename
    | None ->
      Filename.chop_suffix infile ".cpp" ^ if shouldlink then "" else ".o"
  in
  let args =
    if is_bde () then
      let bde_dir = normalize_bde_dir () in
      prepend_to_all "-I" includes
      @ (if shouldlink then [] else ["-c"])
      @ [
          "-std=c++20";
          "-Wno-deprecated-literal-operator";
          "-Wno-unused-command-line-argument";
          "-I";
          bde_dir ^ "/include";
        ]
      @ flags
      @ [
          infile;
          "-L";
          bde_dir ^ "/lib";
          "-lbsl";
          "-lbal";
          "-lbdl";
          "-lbbl";
          "-lbbryu";
          "-linteldfp";
          "-lpcre2";
          "-o";
          outfile;
        ]
    else
      prepend_to_all "-I" includes
      @ (if shouldlink then [] else ["-c"])
      @ ["-std=c++23"]
      @ flags
      @ [infile; "-o"; outfile]
  in
  match compiler_output errfile "clang++" args with
  | Unix.WEXITED 0, _ -> ()
  | status, errors ->
    raise (ClangError (Subprocess.exit_code status, errors))

(** Compile or link one OCaml source file through [ocamlfind ocamlopt].

    Linked executables include [rocq-runtime.kernel] and thread support. *)
let compile_ocaml
    ?(shouldlink = false)
    ?(includes = [])
    ?(flags = [])
    ?outfile
    ?errfile
    infile =
  if not (Subprocess.executable_available "ocamlopt") then
    raise NoOcamloptFound;
  let errfile =
    match errfile with
    | Some filename -> filename
    | None -> make_error_file "ocaml_" infile
  in
  let outfile =
    match outfile with
    | Some filename -> filename
    | None -> Filename.chop_suffix infile ".ml"
  in
  let args =
    ["ocamlopt"; "-thread"; "-package"; "rocq-runtime.kernel"; "-linkpkg"]
    @ prepend_to_all "-I" includes
    @ (if shouldlink then [] else ["-c"])
    @ flags
    @ ["-o"; outfile; infile]
  in
  match compiler_output errfile (Envars.ocamlfind ()) args with
  | Unix.WEXITED 0, _ -> ()
  | status, errors ->
    raise (OcamloptError (Subprocess.exit_code status, errors))

(** Link the object and [.t.cpp] driver adjacent to [infile], execute the test,
    and return its captured output. A non-zero test exit raises [Failure]. *)
let compile_and_test ?outfile ?errfile infile =
  if not (Subprocess.executable_available "clang++") then raise NoClangFound;
  let directory = Filename.dirname infile in
  let errfile =
    match errfile with
    | Some filename -> filename
    | None -> make_error_file "cpp_" infile
  in
  let executable =
    match outfile with
    | Some filename -> filename
    | None -> Filename.chop_suffix infile ".cpp" ^ ".t.exe"
  in
  let object_file = Filename.chop_suffix infile ".cpp" ^ ".o" in
  let test_file = Filename.chop_suffix infile ".cpp" ^ ".t.cpp" in
  let args =
    if is_bde () then
      let bde_dir = normalize_bde_dir () in
      [
        "-O2";
        "-std=c++20";
        "-Wno-deprecated-literal-operator";
        "-Wno-unused-command-line-argument";
        "-I";
        directory;
        "-I";
        bde_dir ^ "/include";
        object_file;
        test_file;
        "-L";
        bde_dir ^ "/lib";
        "-lbsl";
        "-lbal";
        "-lbdl";
        "-lbbl";
        "-lbbryu";
        "-linteldfp";
        "-lpcre2";
        "-o";
        executable;
      ]
    else
      [
        "-O2";
        "-std=c++23";
        "-I";
        directory;
        object_file;
        test_file;
        "-o";
        executable;
      ]
  in
  ( match compiler_output errfile "clang++" args with
  | Unix.WEXITED 0, _ -> ()
  | status, errors ->
    raise (ClangError (Subprocess.exit_code status, errors)) );
  let output = Subprocess.capture executable [] in
  ( match output.status with
  | Unix.WEXITED 0 -> ()
  | status ->
    raise
      (Failure
         ( "Test assertions failed (exit code "
         ^ string_of_int (Subprocess.exit_code status)
         ^ ")" )) );
  output.stdout ^ output.stderr
