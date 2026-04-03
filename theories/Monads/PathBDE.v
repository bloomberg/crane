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

Crane Extract Inductive pathE => ""
  [ "std::filesystem::canonical(std::filesystem::path(%a0)).string()"
    "std::filesystem::relative(std::filesystem::path(%a0)).string()"
    "std::filesystem::absolute(std::filesystem::path(%a0)).string()"
    "bdls::FilesystemUtil::isDirectory(%a0)"
    "bdls::FilesystemUtil::isRegularFile(%a0)" ]
  From "filesystem" "bdls_filesystemutil.h".

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
  "bdls::FilesystemUtil::isDirectory(%a0)"
  From "bdls_filesystemutil.h".
Crane Extract Inlined Constant is_regular_file =>
  "bdls::FilesystemUtil::isRegularFile(%a0)"
  From "bdls_filesystemutil.h".
