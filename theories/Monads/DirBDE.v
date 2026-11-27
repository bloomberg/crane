(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Directory effects for the BDE flavor.

   Re-exports shared definitions from [DirDefs.v] and adds C++ extraction
   mappings targeting BDE.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.DirDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(**
   Safety: the BDE create/remove/getWorkingDirectory mappings already report
   failure by return value rather than throwing. [list_directory] uses the
   non-throwing [std::error_code] overload of [directory_iterator] so an
   invalid or raced path degrades to an empty list instead of terminating the
   process (CWE-248 / CWE-755), and caps the number of entries it
   accumulates so a huge or adversarial directory cannot exhaust memory
   (CWE-400).
*)
#[export] Instance dirE_mapping (T : Type) : TypeMapping (dirE T) :=
  event_family ["bdls_filesystemutil.h"; "filesystem"; "system_error"]
    [event (Ref (@CreateDirectory)) "(bdls::FilesystemUtil::createDirectories(%a0.c_str(), true) == 0)";
     event (Ref (@RemoveDirectory)) "(bdls::FilesystemUtil::remove(%a0.c_str(), true) == 0)";
     event (Ref (@ListDirectory)) "[&]() -> List<bsl::string> {
  auto result = List<bsl::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%a0), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<bsl::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()";
     event (Ref (@CurrentPath)) "[&]() -> bsl::string { bsl::string s; bdls::FilesystemUtil::getWorkingDirectory(&s); return s; }()"].

#[export] Instance create_directory_mapping : OperationMapping (Ref (@create_directory)) :=
  effect_cpp ["bdls_filesystemutil.h"] ["path"]
    (Expr "(bdls::FilesystemUtil::createDirectories(%arg(path).c_str(), true) == 0)").

#[export] Instance remove_directory_mapping : OperationMapping (Ref (@remove_directory)) :=
  effect_cpp ["bdls_filesystemutil.h"] ["path"]
    (Expr "(bdls::FilesystemUtil::remove(%arg(path).c_str(), true) == 0)").

#[export] Instance list_directory_mapping : OperationMapping (Ref (@list_directory)) :=
  effect_cpp ["bdls_filesystemutil.h"; "filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> List<bsl::string> {
  auto result = List<bsl::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%arg(path)), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<bsl::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()").

#[export] Instance current_path_mapping : OperationMapping (Ref (@current_path)) :=
  effect_cpp ["bdls_filesystemutil.h"] []
    (Expr "[&]() -> bsl::string { bsl::string s; bdls::FilesystemUtil::getWorkingDirectory(&s); return s; }()").
