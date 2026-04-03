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

Crane Extract Inductive dirE => ""
  [ "std::filesystem::create_directories(std::filesystem::path(%a0))"
    "std::filesystem::remove_all(std::filesystem::path(%a0))"
    "[&]() -> std::shared_ptr<List<std::string>> {
  auto result = List<std::string>::nil();
  for (const auto& entry : std::filesystem::directory_iterator(%a0)) {
    result = List<std::string>::cons(entry.path().filename().string(), std::move(result));
  }
  return result;
}()"
    "std::filesystem::current_path().string()" ]
  From "filesystem".

Crane Extract Inlined Constant create_directory =>
  "std::filesystem::create_directories(std::filesystem::path(%a0))"
  From "filesystem".

Crane Extract Inlined Constant remove_directory =>
  "std::filesystem::remove_all(std::filesystem::path(%a0))"
  From "filesystem".

Crane Extract Inlined Constant list_directory =>
"[&]() -> std::shared_ptr<List<std::string>> {
  auto result = List<std::string>::nil();
  for (const auto& entry : std::filesystem::directory_iterator(%a0)) {
    result = List<std::string>::cons(entry.path().filename().string(), std::move(result));
  }
  return result;
}()" From "filesystem".

Crane Extract Inlined Constant current_path =>
  "std::filesystem::current_path().string()" From "filesystem".
