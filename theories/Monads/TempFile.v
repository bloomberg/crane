(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Temporary file effects for the standard library flavor.

   Re-exports shared definitions from [TempFileDefs.v] and adds C++
   extraction mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.TempFileDefs.

Crane Extract Inductive tempFileE => ""
  [ "[&]() -> std::string {
  auto p = std::filesystem::temp_directory_path() / (%a0 + ""XXXXXX"");
  std::string s = p.string();
  int fd = mkstemp(s.data());
  if (fd >= 0) ::close(fd);
  return s;
}()"
    "[&]() -> std::string {
  auto p = std::filesystem::temp_directory_path() / (%a0 + ""XXXXXX"");
  std::string s = p.string();
  return std::string(mkdtemp(s.data()));
}()" ]
  From "filesystem" "cstdlib" "unistd.h".

Crane Extract Inlined Constant create_temp_file =>
"[&]() -> std::string {
  auto p = std::filesystem::temp_directory_path() / (%a0 + ""XXXXXX"");
  std::string s = p.string();
  int fd = mkstemp(s.data());
  if (fd >= 0) ::close(fd);
  return s;
}()" From "filesystem" "cstdlib" "unistd.h".

Crane Extract Inlined Constant create_temp_dir =>
"[&]() -> std::string {
  auto p = std::filesystem::temp_directory_path() / (%a0 + ""XXXXXX"");
  std::string s = p.string();
  return std::string(mkdtemp(s.data()));
}()" From "filesystem" "cstdlib".
