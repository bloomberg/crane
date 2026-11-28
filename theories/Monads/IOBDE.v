(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   IO effect events for the BDE flavor.

   Re-exports shared definitions from [IODefs.v] and adds C++ extraction
   mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.IODefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** [consoleE] events on [bsl::cout] and [bsl::cin]. *)
#[export] Instance consoleE_mapping (T : Type) : TypeMapping (consoleE T) :=
  event_family ["bsl_iostream.h"]
    [event (Ref (@Print)) "bsl::cout << %a0";
     event (Ref (@PrintEndline)) "bsl::cout << %a0 << '\n'";
     event (Ref (@GetLine)) "[&]() -> bsl::string { bsl::string s; bsl::getline(bsl::cin, s); return s; }()"].

(** [fileE] events: [bsl] streams for contents,
    [bdls::FilesystemUtil] for existence and removal. *)
#[export] Instance fileE_mapping (T : Type) : TypeMapping (fileE T) :=
  event_family ["fstream"; "bsl_iostream.h"; "bdls_filesystemutil.h"]
    [event (Ref (@ReadFile)) "[&]() -> bsl::string {
  bsl::ifstream file(%a0);
  if (!file) {
      bsl::cerr << ""Failed to open file "" << %a0 << '\n';
      return bsl::string{};
  }
  return bsl::string(
      bsl::istreambuf_iterator<char>(file),
      bsl::istreambuf_iterator<char>());
}()";
     event (Ref (@WriteFile)) "[&]() {
  bsl::ofstream file(%a0);
  file << %a1;
}()";
     event (Ref (@AppendFile)) "[&]() {
  bsl::ofstream file(%a0, bsl::ios::app);
  file << %a1;
}()";
     event (Ref (@FileExists)) "bdls::FilesystemUtil::exists(%a0)";
     event (Ref (@RemoveFile)) "bdls::FilesystemUtil::remove(%a0)"].

(** [print] streams to [bsl::cout]. *)
#[export] Instance print_mapping : OperationMapping (Ref (@print)) :=
  effect_cpp ["bsl_iostream.h"] ["s"]
    (Structured (Binop Shl (Verbatim "bsl::cout") (Arg "s"))).
(** [print_endline] streams the string and
    ['\n'] to [bsl::cout], without flushing. *)
#[export] Instance print_endline_mapping : OperationMapping (Ref (@print_endline)) :=
  effect_cpp ["bsl_iostream.h"] ["s"]
    (Structured (Binop Shl (Binop Shl (Verbatim "bsl::cout") (Arg "s")) (Verbatim "'\n'"))).
(** [get_line] reads into the result with [bsl::getline]. *)
#[export] Instance get_line_mapping : OperationMapping (Ref (@get_line)) :=
  effect_cpp ["bsl_iostream.h"] []
    (WithBody "" "bsl::getline(bsl::cin, %result)").

(** [read]: the whole file, or the empty string and a message on [bsl::cerr]
    if it cannot be opened. *)
#[export] Instance read_mapping : OperationMapping (Ref (@read)) :=
  effect_cpp ["fstream"; "bsl_iostream.h"] ["path"]
    (Expr "[&]() -> bsl::string {
  bsl::ifstream file(%arg(path));
  if (!file) {
      bsl::cerr << ""Failed to open file "" << %arg(path) << '\n';
      return bsl::string{};
  }
  return bsl::string(
      bsl::istreambuf_iterator<char>(file),
      bsl::istreambuf_iterator<char>());
}()").

(** [write_file] truncates and writes through a [bsl::ofstream]. *)
#[export] Instance write_file_mapping : OperationMapping (Ref (@write_file)) :=
  effect_cpp ["fstream"] ["path"; "content"]
    (Expr "[&]() {
  bsl::ofstream file(%arg(path));
  file << %arg(content);
}()").

(** [append_file] writes through a [bsl::ofstream] in append mode. *)
#[export] Instance append_file_mapping : OperationMapping (Ref (@append_file)) :=
  effect_cpp ["fstream"] ["path"; "content"]
    (Expr "[&]() {
  bsl::ofstream file(%arg(path), bsl::ios::app);
  file << %arg(content);
}()").

(** [file_exists] is [bdls::FilesystemUtil::exists]. *)
#[export] Instance file_exists_mapping : OperationMapping (Ref (@file_exists)) :=
  effect_cpp ["bdls_filesystemutil.h"] ["path"]
    (Expr "bdls::FilesystemUtil::exists(%arg(path))").
(** [remove_file] is [bdls::FilesystemUtil::remove], ignoring failure. *)
#[export] Instance remove_file_mapping : OperationMapping (Ref (@remove_file)) :=
  effect_cpp ["bdls_filesystemutil.h"] ["path"]
    (Expr "bdls::FilesystemUtil::remove(%arg(path))").
