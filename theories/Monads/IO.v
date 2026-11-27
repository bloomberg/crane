(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   IO effect events for the standard library flavor.

   Re-exports shared definitions from [IODefs.v] and adds C++ extraction
   mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
From Crane Require Import Mapping.Std Mapping.Descriptor Mapping.Cpp.
From Crane Require Export Monads.IODefs.
Import ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

Definition read_file_cpp : string := "[&]() -> std::string {
  std::ifstream file(%arg(path));
  if (!file) {
      std::cerr << ""Failed to open file "" << %arg(path) << '\n';
      return std::string{};
  }
  return std::string(
      std::istreambuf_iterator<char>(file),
      std::istreambuf_iterator<char>());
}()".

Definition write_file_cpp : string := "[&]() {
  std::ofstream file(%arg(path));
  file << %arg(content);
}()".

Definition append_file_cpp : string := "[&]() {
  std::ofstream file(%arg(path), std::ios::app);
  file << %arg(content);
}()".

(* [file_exists]/[remove_file] use the non-throwing [std::error_code] overload:
   the Rocq effects return plain [bool]/[unit] with no error channel, so an
   invalid, inaccessible, or raced path must not raise a [std::filesystem_error]
   that terminates the generated process (CWE-248 / CWE-755). *)
Definition file_exists_cpp : string :=
  "[&]() -> bool { std::error_code _ec; return std::filesystem::exists(std::filesystem::path(%arg(path)), _ec); }()".
Definition remove_file_cpp : string :=
  "[&]() { std::error_code _ec; std::filesystem::remove(std::filesystem::path(%arg(path)), _ec); }()".

Definition get_line_cpp : string :=
  "[&]() -> std::string { std::string s; std::getline(std::cin, s); return s; }()".

#[export] Instance consoleE_mapping (X : Type) : TypeMapping (consoleE X) :=
  event_family ["iostream"]
    [event (Ref (@Print)) "std::cout << %a0";
     event (Ref (@PrintEndline)) "std::cout << %a0 << '\n'";
     event (Ref (@GetLine)) get_line_cpp].

#[export] Instance fileE_mapping (X : Type) : TypeMapping (fileE X) :=
  event_family ["fstream"; "iostream"; "iterator"; "filesystem"; "system_error"]
    [event (Ref (@ReadFile)) "[&]() -> std::string {
  std::ifstream file(%a0);
  if (!file) {
      std::cerr << ""Failed to open file "" << %a0 << '\n';
      return std::string{};
  }
  return std::string(
      std::istreambuf_iterator<char>(file),
      std::istreambuf_iterator<char>());
}()";
     event (Ref (@WriteFile)) "[&]() {
  std::ofstream file(%a0);
  file << %a1;
}()";
     event (Ref (@AppendFile)) "[&]() {
  std::ofstream file(%a0, std::ios::app);
  file << %a1;
}()";
     event (Ref (@FileExists)) "[&]() -> bool { std::error_code _ec; return std::filesystem::exists(std::filesystem::path(%a0), _ec); }()";
     event (Ref (@RemoveFile)) "[&]() { std::error_code _ec; std::filesystem::remove(std::filesystem::path(%a0), _ec); }()"].

#[export] Instance print_mapping : OperationMapping (Ref (@print)) :=
  effect_cpp ["iostream"] ["s"] (Structured (Binop Shl (Verbatim "std::cout") (Arg "s"))).
#[export] Instance print_endline_mapping : OperationMapping (Ref (@print_endline)) :=
  effect_cpp ["iostream"] ["s"] (Structured (Binop Shl (Binop Shl (Verbatim "std::cout") (Arg "s")) (Verbatim "'\n'"))).
#[export] Instance get_line_mapping : OperationMapping (Ref (@get_line)) :=
  effect_cpp ["iostream"] [] (WithBody "" "std::getline(std::cin, %result)").
#[export] Instance read_mapping : OperationMapping (Ref (@read)) :=
  effect_cpp ["fstream"; "iostream"; "iterator"] ["path"] (Expr read_file_cpp).
#[export] Instance write_file_mapping : OperationMapping (Ref (@write_file)) :=
  effect_cpp ["fstream"] ["path"; "content"] (Expr write_file_cpp).
#[export] Instance append_file_mapping : OperationMapping (Ref (@append_file)) :=
  effect_cpp ["fstream"] ["path"; "content"] (Expr append_file_cpp).
#[export] Instance file_exists_mapping : OperationMapping (Ref (@file_exists)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"] (Expr file_exists_cpp).
#[export] Instance remove_file_mapping : OperationMapping (Ref (@remove_file)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"] (Expr remove_file_cpp).
