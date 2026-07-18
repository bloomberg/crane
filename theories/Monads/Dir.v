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
Crane Extract Inductive dirE => ""
  [ "[&]() -> bool { std::error_code _ec; std::filesystem::create_directories(std::filesystem::path(%a0), _ec); return !_ec; }()"
    "[&]() -> bool { std::error_code _ec; std::filesystem::remove_all(std::filesystem::path(%a0), _ec); return !_ec; }()"
    "[&]() -> List<std::string> {
  auto result = List<std::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%a0), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<std::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()"
    "[&]() -> std::string { std::error_code _ec; auto _p = std::filesystem::current_path(_ec); return _ec ? std::string{} : _p.string(); }()" ]
  From "filesystem" "system_error".

Crane Extract Inlined Constant create_directory =>
  "[&]() -> bool { std::error_code _ec; std::filesystem::create_directories(std::filesystem::path(%a0), _ec); return !_ec; }()"
  From "filesystem" "system_error".

Crane Extract Inlined Constant remove_directory =>
  "[&]() -> bool { std::error_code _ec; std::filesystem::remove_all(std::filesystem::path(%a0), _ec); return !_ec; }()"
  From "filesystem" "system_error".

Crane Extract Inlined Constant list_directory =>
"[&]() -> List<std::string> {
  auto result = List<std::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%a0), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<std::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()" From "filesystem" "system_error".

Crane Extract Inlined Constant current_path =>
  "[&]() -> std::string { std::error_code _ec; auto _p = std::filesystem::current_path(_ec); return _ec ? std::string{} : _p.string(); }()"
  From "filesystem" "system_error".
