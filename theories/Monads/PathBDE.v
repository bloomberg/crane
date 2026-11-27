(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Filesystem path effects for the BDE flavor.

   Re-exports shared definitions from [PathDefs.v] and adds C++ extraction
   mappings targeting BDE where available, falling back to [std::filesystem]
   for operations without BDE equivalents.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.PathDefs.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
Import PrimString.PStringNotations.
From Stdlib Require List.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(**
   Safety: the [std::filesystem] path-normalization mappings use the
   non-throwing [std::error_code] overload so an invalid or inaccessible path
   degrades to the empty string rather than raising a [std::filesystem_error]
   that terminates the generated process. The Rocq effects carry no error
   channel (CWE-248 / CWE-755). The BDE predicate mappings
   ([isDirectory]/[isRegularFile]) already report failure by return value.
*)
#[export] Instance pathE_mapping (T : Type) : TypeMapping (pathE T) :=
  event_family ["filesystem"; "system_error"; "bdls_filesystemutil.h"]
    [event (Ref (@Canonical)) "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::canonical(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()";
     event (Ref (@Relative)) "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::relative(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()";
     event (Ref (@Absolute)) "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::absolute(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()";
     event (Ref (@IsDirectory)) "bdls::FilesystemUtil::isDirectory(%a0)";
     event (Ref (@IsRegularFile)) "bdls::FilesystemUtil::isRegularFile(%a0)"].

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
  effect_cpp ["bdls_filesystemutil.h"] ["path"]
    (Expr "bdls::FilesystemUtil::isDirectory(%arg(path))").
#[export] Instance is_regular_file_mapping : OperationMapping (Ref (@is_regular_file)) :=
  effect_cpp ["bdls_filesystemutil.h"] ["path"]
    (Expr "bdls::FilesystemUtil::isRegularFile(%arg(path))").
