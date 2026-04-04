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

Crane Extract Inductive dirE => ""
  [ "(bdls::FilesystemUtil::createDirectories(%a0.c_str(), true) == 0)"
    "(bdls::FilesystemUtil::remove(%a0.c_str(), true) == 0)"
    "[&]() -> bsl::shared_ptr<List<bsl::string>> {
  auto result = List<bsl::string>::nil();
  for (const auto& entry : std::filesystem::directory_iterator(%a0)) {
    result = List<bsl::string>::cons(entry.path().filename().string(), std::move(result));
  }
  return result;
}()"
    "[&]() -> bsl::string { bsl::string s; bdls::FilesystemUtil::getWorkingDirectory(&s); return s; }()" ]
  From "bdls_filesystemutil.h" "filesystem".

Crane Extract Inlined Constant create_directory =>
  "(bdls::FilesystemUtil::createDirectories(%a0.c_str(), true) == 0)"
  From "bdls_filesystemutil.h".

Crane Extract Inlined Constant remove_directory =>
  "(bdls::FilesystemUtil::remove(%a0.c_str(), true) == 0)"
  From "bdls_filesystemutil.h".

Crane Extract Inlined Constant list_directory =>
"[&]() -> bsl::shared_ptr<List<bsl::string>> {
  auto result = List<bsl::string>::nil();
  for (const auto& entry : std::filesystem::directory_iterator(%a0)) {
    result = List<bsl::string>::cons(entry.path().filename().string(), std::move(result));
  }
  return result;
}()" From "bdls_filesystemutil.h" "filesystem".

Crane Extract Inlined Constant current_path =>
  "[&]() -> bsl::string { bsl::string s; bdls::FilesystemUtil::getWorkingDirectory(&s); return s; }()"
  From "bdls_filesystemutil.h".
