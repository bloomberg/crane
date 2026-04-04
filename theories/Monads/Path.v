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

Crane Extract Inductive pathE => ""
  [ "std::filesystem::canonical(std::filesystem::path(%a0)).string()"
    "std::filesystem::relative(std::filesystem::path(%a0)).string()"
    "std::filesystem::absolute(std::filesystem::path(%a0)).string()"
    "std::filesystem::is_directory(std::filesystem::path(%a0))"
    "std::filesystem::is_regular_file(std::filesystem::path(%a0))" ]
  From "filesystem".

Crane Extract Inlined Constant canonical =>
  "std::filesystem::canonical(std::filesystem::path(%a0)).string()"
  From "filesystem".
Crane Extract Inlined Constant relative =>
  "std::filesystem::relative(std::filesystem::path(%a0)).string()"
  From "filesystem".
Crane Extract Inlined Constant absolute =>
  "std::filesystem::absolute(std::filesystem::path(%a0)).string()"
  From "filesystem".
Crane Extract Inlined Constant is_directory =>
  "std::filesystem::is_directory(std::filesystem::path(%a0))"
  From "filesystem".
Crane Extract Inlined Constant is_regular_file =>
  "std::filesystem::is_regular_file(std::filesystem::path(%a0))"
  From "filesystem".
