(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Temporary file effects for the BDE flavor.

   Re-exports shared definitions from [TempFileDefs.v] and adds C++
   extraction mappings targeting BDE ([bsl::]).

   Safety:
   - The caller-supplied prefix is reduced to a single filename component
     (everything after the last ['/']) so directory separators, [..], or an
     absolute path cannot escape the system temporary directory (CWE-22).
   - Entries are created with an unpredictable name and O_EXCL / mkdir, which
     fail atomically if the path already exists (so a pre-created file or
     symlink is never followed), and with owner-only permissions.
   - A temporary *file* is created inside a fresh owner-only (0700) directory.
     Because no other user can traverse that directory, the returned path
     cannot be swapped or symlink-raced by a local attacker before the caller
     reopens it -- the effect returns a path rather than the secure descriptor,
     so this containment is what keeps later opens safe (CWE-367 / CWE-377).
   - Failures are reported by exception rather than returning an invalid path.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.TempFileDefs.

Crane Extract Inductive tempFileE => ""
  [ "[&]() -> bsl::string {
  bsl::string _base;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&_base);
  bsl::string _n = %a0;
  bsl::string::size_type _sl = _n.find_last_of('/');
  if (_sl != bsl::string::npos) _n = _n.substr(_sl + 1);
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::random_device _rng;
  for (;;) {
    bsl::string _d =
      _base + ""/"" + _n + bsl::to_string(_rng()) + bsl::to_string(_rng());
    if (::mkdir(_d.c_str(), 0700) != 0) {
      if (errno == EEXIST) continue;
      throw std::runtime_error(""crane: failed to create temporary directory"");
    }
    bsl::string _p = _d + ""/"" + _n;
    int _fd = ::open(_p.c_str(), O_CREAT | O_EXCL | O_RDWR, 0600);
    if (_fd < 0)
      throw std::runtime_error(""crane: failed to create temporary file"");
    ::close(_fd);
    return _p;
  }
}()"
    "[&]() -> bsl::string {
  bsl::string _base;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&_base);
  bsl::string _n = %a0;
  bsl::string::size_type _sl = _n.find_last_of('/');
  if (_sl != bsl::string::npos) _n = _n.substr(_sl + 1);
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::random_device _rng;
  for (;;) {
    bsl::string _p =
      _base + ""/"" + _n + bsl::to_string(_rng()) + bsl::to_string(_rng());
    if (::mkdir(_p.c_str(), 0700) == 0) return _p;
    if (errno != EEXIST)
      throw std::runtime_error(""crane: failed to create temporary directory"");
  }
}()" ]
  From "bdls_filesystemutil.h" "bsl_string.h" "random" "fcntl.h" "sys/stat.h"
       "unistd.h" "cerrno" "stdexcept".

Crane Extract Inlined Constant create_temp_file =>
"[&]() -> bsl::string {
  bsl::string _base;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&_base);
  bsl::string _n = %a0;
  bsl::string::size_type _sl = _n.find_last_of('/');
  if (_sl != bsl::string::npos) _n = _n.substr(_sl + 1);
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::random_device _rng;
  for (;;) {
    bsl::string _d =
      _base + ""/"" + _n + bsl::to_string(_rng()) + bsl::to_string(_rng());
    if (::mkdir(_d.c_str(), 0700) != 0) {
      if (errno == EEXIST) continue;
      throw std::runtime_error(""crane: failed to create temporary directory"");
    }
    bsl::string _p = _d + ""/"" + _n;
    int _fd = ::open(_p.c_str(), O_CREAT | O_EXCL | O_RDWR, 0600);
    if (_fd < 0)
      throw std::runtime_error(""crane: failed to create temporary file"");
    ::close(_fd);
    return _p;
  }
}()" From "bdls_filesystemutil.h" "bsl_string.h" "random" "fcntl.h"
       "sys/stat.h" "unistd.h" "cerrno" "stdexcept".

Crane Extract Inlined Constant create_temp_dir =>
"[&]() -> bsl::string {
  bsl::string _base;
  bdls::FilesystemUtil::getSystemTemporaryDirectory(&_base);
  bsl::string _n = %a0;
  bsl::string::size_type _sl = _n.find_last_of('/');
  if (_sl != bsl::string::npos) _n = _n.substr(_sl + 1);
  if (_n.empty() || _n == ""."" || _n == "".."") _n = ""tmp"";
  std::random_device _rng;
  for (;;) {
    bsl::string _p =
      _base + ""/"" + _n + bsl::to_string(_rng()) + bsl::to_string(_rng());
    if (::mkdir(_p.c_str(), 0700) == 0) return _p;
    if (errno != EEXIST)
      throw std::runtime_error(""crane: failed to create temporary directory"");
  }
}()" From "bdls_filesystemutil.h" "bsl_string.h" "random" "sys/stat.h"
       "cerrno" "stdexcept".
