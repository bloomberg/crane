(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Filesystem path effects for the standard library flavor.

   Re-exports shared definitions from [PathDefs.v] and adds C++ extraction
   mappings targeting [std::filesystem].
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.PathDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(**
   Safety: every mapping uses the non-throwing [std::error_code] overload so
   that an ordinary invalid, inaccessible, or raced path cannot raise a
   [std::filesystem_error] that terminates the generated process. The Rocq
   effects return a plain [string]/[bool] with no error channel, so a failed
   query degrades to the neutral result (empty string / [false]) instead of
   crashing (CWE-248 / CWE-755).
*)
#[export] Instance pathE_mapping (T : Type) : TypeMapping (pathE T) :=
  event_family ["filesystem"; "system_error"]
    [event (Ref (@Canonical)) "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::canonical(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()";
     event (Ref (@Relative)) "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::relative(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()";
     event (Ref (@Absolute)) "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::absolute(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()";
     event (Ref (@IsDirectory)) "[&]() -> bool { std::error_code _ec; return std::filesystem::is_directory(std::filesystem::path(%a0), _ec); }()";
     event (Ref (@IsRegularFile)) "[&]() -> bool { std::error_code _ec; return std::filesystem::is_regular_file(std::filesystem::path(%a0), _ec); }()"].

#[export] Instance canonical_mapping : OperationMapping (Ref (@canonical)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::canonical(std::filesystem::path(%arg(path)), _ec); return _ec ? std::string{} : _r.string(); }()").
#[export] Instance relative_mapping : OperationMapping (Ref (@relative)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::relative(std::filesystem::path(%arg(path)), _ec); return _ec ? std::string{} : _r.string(); }()").
#[export] Instance absolute_mapping : OperationMapping (Ref (@absolute)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::absolute(std::filesystem::path(%arg(path)), _ec); return _ec ? std::string{} : _r.string(); }()").
#[export] Instance is_directory_mapping : OperationMapping (Ref (@is_directory)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> bool { std::error_code _ec; return std::filesystem::is_directory(std::filesystem::path(%arg(path)), _ec); }()").
#[export] Instance is_regular_file_mapping : OperationMapping (Ref (@is_regular_file)) :=
  effect_cpp ["filesystem"; "system_error"] ["path"]
    (Expr "[&]() -> bool { std::error_code _ec; return std::filesystem::is_regular_file(std::filesystem::path(%arg(path)), _ec); }()").
