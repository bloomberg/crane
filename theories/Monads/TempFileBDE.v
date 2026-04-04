(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Temporary file effects for the BDE flavor.

   Re-exports shared definitions from [TempFileDefs.v] and adds C++
   extraction mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.TempFileDefs.

Crane Extract Inductive tempFileE => ""
  [ "[&]() -> bsl::string {
  bsl::string dir;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&dir);
  bsl::string s = dir + ""/"" + %a0 + ""XXXXXX"";
  int fd = mkstemp(s.data());
  if (fd >= 0) ::close(fd);
  return s;
}()"
    "[&]() -> bsl::string {
  bsl::string dir;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&dir);
  bsl::string s = dir + ""/"" + %a0 + ""XXXXXX"";
  return bsl::string(mkdtemp(s.data()));
}()" ]
  From "bdls_filesystemutil.h" "cstdlib" "unistd.h".

Crane Extract Inlined Constant create_temp_file =>
"[&]() -> bsl::string {
  bsl::string dir;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&dir);
  bsl::string s = dir + ""/"" + %a0 + ""XXXXXX"";
  int fd = mkstemp(s.data());
  if (fd >= 0) ::close(fd);
  return s;
}()" From "bdls_filesystemutil.h" "cstdlib" "unistd.h".

Crane Extract Inlined Constant create_temp_dir =>
"[&]() -> bsl::string {
  bsl::string dir;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&dir);
  bsl::string s = dir + ""/"" + %a0 + ""XXXXXX"";
  return bsl::string(mkdtemp(s.data()));
}()" From "bdls_filesystemutil.h" "cstdlib".
