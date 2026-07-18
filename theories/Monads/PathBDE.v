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

(**
   Safety: the [std::filesystem] path-normalization mappings use the
   non-throwing [std::error_code] overload so an invalid or inaccessible path
   degrades to the empty string rather than raising a [std::filesystem_error]
   that terminates the generated process. The Rocq effects carry no error
   channel (CWE-248 / CWE-755). The BDE predicate mappings
   ([isDirectory]/[isRegularFile]) already report failure by return value.
*)
Crane Extract Inductive pathE => ""
  [ "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::canonical(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
    "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::relative(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
    "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::absolute(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
    "bdls::FilesystemUtil::isDirectory(%a0)"
    "bdls::FilesystemUtil::isRegularFile(%a0)" ]
  From "filesystem" "system_error" "bdls_filesystemutil.h".

Crane Extract Inlined Constant canonical =>
  "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::canonical(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
  From "filesystem" "system_error".
Crane Extract Inlined Constant relative =>
  "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::relative(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
  From "filesystem" "system_error".
Crane Extract Inlined Constant absolute =>
  "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::absolute(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
  From "filesystem" "system_error".
Crane Extract Inlined Constant is_directory =>
  "bdls::FilesystemUtil::isDirectory(%a0)"
  From "bdls_filesystemutil.h".
Crane Extract Inlined Constant is_regular_file =>
  "bdls::FilesystemUtil::isRegularFile(%a0)"
  From "bdls_filesystemutil.h".
