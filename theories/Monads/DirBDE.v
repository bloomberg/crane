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

(**
   Safety: the BDE create/remove/getWorkingDirectory mappings already report
   failure by return value rather than throwing. [list_directory] uses the
   non-throwing [std::error_code] overload of [directory_iterator] so an
   invalid or raced path degrades to an empty list instead of terminating the
   process (CWE-248 / CWE-755), and caps the number of entries it
   accumulates so a huge or adversarial directory cannot exhaust memory
   (CWE-400).
*)
Crane Extract Inductive dirE => ""
  [ "(bdls::FilesystemUtil::createDirectories(%a0.c_str(), true) == 0)"
    "(bdls::FilesystemUtil::remove(%a0.c_str(), true) == 0)"
    "[&]() -> List<bsl::string> {
  auto result = List<bsl::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%a0), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<bsl::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()"
    "[&]() -> bsl::string { bsl::string s; bdls::FilesystemUtil::getWorkingDirectory(&s); return s; }()" ]
  From "bdls_filesystemutil.h" "filesystem" "system_error".

Crane Extract Inlined Constant create_directory =>
  "(bdls::FilesystemUtil::createDirectories(%a0.c_str(), true) == 0)"
  From "bdls_filesystemutil.h".

Crane Extract Inlined Constant remove_directory =>
  "(bdls::FilesystemUtil::remove(%a0.c_str(), true) == 0)"
  From "bdls_filesystemutil.h".

Crane Extract Inlined Constant list_directory =>
"[&]() -> List<bsl::string> {
  auto result = List<bsl::string>::nil();
  std::error_code _ec;
  std::size_t _count = 0;
  std::filesystem::directory_iterator _it(std::filesystem::path(%a0), _ec), _end;
  for (; !_ec && _it != _end && _count < 65536; _it.increment(_ec), ++_count) {
    result = List<bsl::string>::cons(_it->path().filename().string(), std::move(result));
  }
  return result;
}()" From "bdls_filesystemutil.h" "filesystem" "system_error".

Crane Extract Inlined Constant current_path =>
  "[&]() -> bsl::string { bsl::string s; bdls::FilesystemUtil::getWorkingDirectory(&s); return s; }()"
  From "bdls_filesystemutil.h".
