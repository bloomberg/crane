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

(** Raised when [ocamlfind], which runs the native OCaml compiler, is not
    available. *)
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
let is_bde () = String.equal (Base.Table.std_lib ()) "BDE"

(** Return the configured BDE root without a trailing slash, a leading [~]
    expanded to [HOME] as a shell would: the compiler is run without one, and
    [Set Crane BDE Directory "~/bde_install/"] is how BDE roots are given. *)
let normalize_bde_dir () =
  let directory = Base.Table.bde_dir () in
  let directory =
    match Sys.getenv_opt "HOME" with
    | Some home when String.equal directory "~" -> home
    | Some home when String.starts_with ~prefix:"~/" directory ->
      home ^ String.sub directory 1 (String.length directory - 1)
    | _ -> directory
  in
  let length = String.length directory in
  if length > 0 && Char.equal directory.[length - 1] '/' then
    String.sub directory 0 (length - 1)
  else
    directory

(** The library ABI a BDE program is compiled for: the one the BDE libraries
    are built with (C++17), whatever [-std] says; otherwise the program
    references a C++20 ABI tag the libraries do not define and fails to link
    (scripts/compile-bde.sh passes the same). *)
let bde_abi = "-DBSLS_LIBRARYFEATURES_FORCE_ABI_CPP17"

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

(** The [-isysroot] arguments a [clang++] invocation needs, or none.

    On macOS a Homebrew [clang++] defaults to an SDK named after the running OS
    version, which need not be installed; without a sysroot the libc++ headers
    fail to find [memcpy] and [mbstate_t]. The SDK actually present is what
    [SDKROOT] names, falling back on [xcrun]. Elsewhere the compiler's own
    default is right and this is empty.

    The shell scripts under [scripts/] resolve the sysroot the same way for the
    compilations they drive; this covers the ones Crane runs itself. *)
let sysroot_args =
  let cached = ref None in
  fun () ->
    match !cached with
    | Some args -> args
    | None ->
      let args =
        if not (String.equal Sys.os_type "Unix" && Sys.file_exists "/usr/bin/xcrun")
        then []
        else
          let sdk =
            match Sys.getenv_opt "SDKROOT" with
            | Some dir when not (String.equal dir "") -> Some dir
            | _ -> (
              match Subprocess.capture "/usr/bin/xcrun" ["--show-sdk-path"] with
              | {status = Unix.WEXITED 0; stdout; _} -> (
                match String.trim stdout with "" -> None | dir -> Some dir )
              | _ | (exception _) -> None )
          in
          match sdk with
          | Some dir when Sys.file_exists dir -> ["-isysroot"; dir]
          | _ -> []
      in
      cached := Some args;
      args

(** Locate Crane's C++ runtime header directory ([theories/cpp]).

    Generated C++ sources [#include "crane_fn.h"] and other Crane runtime
    headers, so the C++ compiler must be pointed at the directory that holds
    them. This takes the project root, drops a
    trailing [_build/default] build-context segment so a dune build maps back to
    the source tree, and appends [theories/cpp]. Recovers the
    root from the physical location of the loaded [Crane] theory. *)
let crane_runtime_include () =
  let crane_dp = Names.DirPath.make [Names.Id.of_string "Crane"] in
  match Loadpath.find_with_logical_path crane_dp with
  | [] -> None
  | lp :: _ ->
    (* [Loadpath.physical] is the theory root, e.g. [<root>/theories] or, under
       a dune build, [<root>/_build/default/theories]. *)
    let project_root = Filename.dirname (Loadpath.physical lp) in
    let build_suffix =
      Filename.dir_sep ^ "_build" ^ Filename.dir_sep ^ "default"
    in
    let project_root =
      if Filename.check_suffix project_root build_suffix then
        Filename.chop_suffix project_root build_suffix
      else
        project_root
    in
    Some (Filename.concat (Filename.concat project_root "theories") "cpp")

(** Compile or link one C++ source file with [clang++].

    Include directories and user flags are kept as distinct argv entries. BDE
    mode selects C++20 and the configured BDE headers/libraries; standard mode
    selects C++26 ([-std=c++2c]). *)
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
          bde_abi;
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
      @ ["-std=c++2c"]
      @ flags
      @ [infile; "-o"; outfile]
  in
  match compiler_output errfile "clang++" (sysroot_args () @ args) with
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
  (* Probe the binary actually invoked below ([ocamlfind]), not [ocamlopt] on
     PATH: otherwise a missing ocamlfind slips past this check and fails later
     with a raw error instead of the friendly [NoOcamloptFound] handled by
     callers. *)
  let ocamlfind = Option.default Coq_config.ocamlfind (Sys.getenv_opt "OCAMLFIND") in
  if not (Subprocess.executable_available ocamlfind) then
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
  match compiler_output errfile ocamlfind args with
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
        bde_abi;
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
        "-std=c++2c";
        "-I";
        directory;
        object_file;
        test_file;
        "-o";
        executable;
      ]
  in
  ( match compiler_output errfile "clang++" (sysroot_args () @ args) with
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
