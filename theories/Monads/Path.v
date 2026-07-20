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

(**
   Safety: every mapping uses the non-throwing [std::error_code] overload so
   that an ordinary invalid, inaccessible, or raced path cannot raise a
   [std::filesystem_error] that terminates the generated process. The Rocq
   effects return a plain [string]/[bool] with no error channel, so a failed
   query degrades to the neutral result (empty string / [false]) instead of
   crashing (CWE-248 / CWE-755).
*)
Crane Extract Inductive pathE => ""
  [ "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::canonical(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
    "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::relative(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
    "[&]() -> std::string { std::error_code _ec; auto _r = std::filesystem::absolute(std::filesystem::path(%a0), _ec); return _ec ? std::string{} : _r.string(); }()"
    "[&]() -> bool { std::error_code _ec; return std::filesystem::is_directory(std::filesystem::path(%a0), _ec); }()"
    "[&]() -> bool { std::error_code _ec; return std::filesystem::is_regular_file(std::filesystem::path(%a0), _ec); }()" ]
  From "filesystem" "system_error".

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
  "[&]() -> bool { std::error_code _ec; return std::filesystem::is_directory(std::filesystem::path(%a0), _ec); }()"
  From "filesystem" "system_error".
Crane Extract Inlined Constant is_regular_file =>
  "[&]() -> bool { std::error_code _ec; return std::filesystem::is_regular_file(std::filesystem::path(%a0), _ec); }()"
  From "filesystem" "system_error".
