(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Temporary file effects for the standard library flavor.

   Re-exports shared definitions from [TempFileDefs.v] and adds C++
   extraction mappings targeting the standard library ([std::]).

   Safety: the caller-supplied prefix is reduced to a single filename
   component ([std::filesystem::path::filename]) so directory separators,
   [..], or an absolute path cannot place the entry outside the system
   temporary directory (CWE-22). Entries are created with an unpredictable
   name and O_EXCL / mkdir, which fail atomically if the path already exists
   (so a pre-created file or symlink is never followed), and with owner-only
   permissions. Failure is reported by exception rather than returning an
   invalid path.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.TempFileDefs.

Crane Extract Inductive tempFileE => ""
  [ "[&]() -> std::string {
  std::string _n = std::filesystem::path(%a0).filename().string();
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::filesystem::path _dir = std::filesystem::temp_directory_path();
  std::random_device _rng;
  for (;;) {
    std::string _p =
      (_dir / (_n + std::to_string(_rng()) + std::to_string(_rng()))).string();
    int _fd = ::open(_p.c_str(), O_CREAT | O_EXCL | O_RDWR, 0600);
    if (_fd >= 0) { ::close(_fd); return _p; }
    if (errno != EEXIST)
      throw std::runtime_error(""crane: failed to create temporary file"");
  }
}()"
    "[&]() -> std::string {
  std::string _n = std::filesystem::path(%a0).filename().string();
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::filesystem::path _dir = std::filesystem::temp_directory_path();
  std::random_device _rng;
  for (;;) {
    std::string _p =
      (_dir / (_n + std::to_string(_rng()) + std::to_string(_rng()))).string();
    if (::mkdir(_p.c_str(), 0700) == 0) return _p;
    if (errno != EEXIST)
      throw std::runtime_error(""crane: failed to create temporary directory"");
  }
}()" ]
  From "filesystem" "random" "string" "fcntl.h" "sys/stat.h" "unistd.h"
       "cerrno" "stdexcept".

Crane Extract Inlined Constant create_temp_file =>
"[&]() -> std::string {
  std::string _n = std::filesystem::path(%a0).filename().string();
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::filesystem::path _dir = std::filesystem::temp_directory_path();
  std::random_device _rng;
  for (;;) {
    std::string _p =
      (_dir / (_n + std::to_string(_rng()) + std::to_string(_rng()))).string();
    int _fd = ::open(_p.c_str(), O_CREAT | O_EXCL | O_RDWR, 0600);
    if (_fd >= 0) { ::close(_fd); return _p; }
    if (errno != EEXIST)
      throw std::runtime_error(""crane: failed to create temporary file"");
  }
}()" From "filesystem" "random" "string" "fcntl.h" "unistd.h" "cerrno"
       "stdexcept".

Crane Extract Inlined Constant create_temp_dir =>
"[&]() -> std::string {
  std::string _n = std::filesystem::path(%a0).filename().string();
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::filesystem::path _dir = std::filesystem::temp_directory_path();
  std::random_device _rng;
  for (;;) {
    std::string _p =
      (_dir / (_n + std::to_string(_rng()) + std::to_string(_rng()))).string();
    if (::mkdir(_p.c_str(), 0700) == 0) return _p;
    if (errno != EEXIST)
      throw std::runtime_error(""crane: failed to create temporary directory"");
  }
}()" From "filesystem" "random" "string" "sys/stat.h" "cerrno" "stdexcept".
