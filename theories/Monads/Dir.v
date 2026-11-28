(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Directory effects using [std::filesystem].

   Re-exports shared definitions from [DirDefs.v] and adds C++ extraction
   mappings targeting the standard library.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.DirDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(**
   Safety: every mapping uses the non-throwing [std::error_code] overload so an
   invalid, inaccessible, or raced path degrades to the neutral result
   ([false] / empty list / empty string) instead of raising a
   [std::filesystem_error] that terminates the generated process (CWE-248 /
   CWE-755). [list_directory] additionally caps the number of
   entries it accumulates so a huge or adversarial directory cannot exhaust
   memory (CWE-400); on the cap or on any iteration error it
   returns the entries gathered so far.
*)
#[export] Instance dirE_mapping (T : Type) : TypeMapping (dirE T) :=
  event_family ["filesystem"; "system_error"; "cstddef"; "utility"]
    [event (Ref (@CreateDirectory)) "[&]() -> bool { std::error_code _ec; std::filesystem::create_directories(std::filesystem::path(%a0), _ec); return !_ec; }()";
     event (Ref (@RemoveDirectory)) "[&]() -> bool { std::error_code _ec; std::filesystem::remove_all(std::filesystem::path(%a0), _ec); return !_ec; }()";
     event (Ref (@ListDirectory)) "[&]() -> List<std::string> {
  auto result = List<std::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%a0), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<std::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()";
     event (Ref (@CurrentPath)) "[&]() -> std::string { std::error_code _ec; auto _p = std::filesystem::current_path(_ec); return _ec ? std::string{} : _p.string(); }()"].

(** [create_directory] is [std::filesystem::create_directories]. *)
#[export] Instance create_directory_mapping : OperationMapping (Ref (@create_directory)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> bool { std::error_code _ec; std::filesystem::create_directories(std::filesystem::path(%arg(path)), _ec); return !_ec; }()").

(** [remove_directory] is [std::filesystem::remove_all]. *)
#[export] Instance remove_directory_mapping : OperationMapping (Ref (@remove_directory)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> bool { std::error_code _ec; std::filesystem::remove_all(std::filesystem::path(%arg(path)), _ec); return !_ec; }()").

(** [list_directory] walks a [std::filesystem::directory_iterator],
    keeping at most 65536 names. *)
#[export] Instance list_directory_mapping : OperationMapping (Ref (@list_directory)) :=
  effect_cpp ["filesystem"; "system_error"; "cstddef"; "utility"] ["path"]
    (Expr "[&]() -> List<std::string> {
  auto result = List<std::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%arg(path)), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<std::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()").

(** [current_path] is [std::filesystem::current_path], empty on error. *)
#[export] Instance current_path_mapping : OperationMapping (Ref (@current_path)) :=
  effect_cpp ["filesystem"; "system_error"] []
    (Expr "[&]() -> std::string { std::error_code _ec; auto _p = std::filesystem::current_path(_ec); return _ec ? std::string{} : _p.string(); }()").
