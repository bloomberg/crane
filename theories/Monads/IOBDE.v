(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   IO effect events for the BDE flavor.

   Re-exports shared definitions from [IODefs.v] and adds C++ extraction
   mappings targeting BDE ([bsl::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE.
From Crane Require Export Monads.IODefs.

Crane Extract Inductive consoleE => ""
  [ "bsl::cout << %a0"
    "bsl::cout << %a0 << '\n'"
    "[&]() -> bsl::string { bsl::string s; bsl::getline(bsl::cin, s); return s; }()" ]
  From "bsl_iostream.h".

Crane Extract Inductive fileE => ""
  [ "[&]() -> bsl::string {
  bsl::ifstream file(%a0);
  if (!file) {
      bsl::cerr << ""Failed to open file "" << %a0 << '\n';
      return bsl::string{};
  }
  return bsl::string(
      bsl::istreambuf_iterator<char>(file),
      bsl::istreambuf_iterator<char>());
}()"
    "[&]() {
  bsl::ofstream file(%a0);
  file << %a1;
}()"
    "[&]() {
  bsl::ofstream file(%a0, bsl::ios::app);
  file << %a1;
}()"
    "bdls::FilesystemUtil::exists(%a0)"
    "bdls::FilesystemUtil::remove(%a0)" ]
  From "fstream" "bdls_filesystemutil.h".

Crane Extract Inlined Constant print => "bsl::cout << %a0" From "bsl_iostream.h".
Crane Extract Inlined Constant print_endline => "bsl::cout << %a0 << '\n'" From "bsl_iostream.h".
Crane Extract Inlined Constant get_line =>
  "bsl::getline(bsl::cin, %result)" From "bsl_iostream.h".

Crane Extract Inlined Constant read =>
"[&]() -> bsl::string {
  bsl::ifstream file(%a0);
  if (!file) {
      bsl::cerr << ""Failed to open file "" << %a0 << '\n';
      return bsl::string{};
  }
  return bsl::string(
      bsl::istreambuf_iterator<char>(file),
      bsl::istreambuf_iterator<char>());
}()" From "fstream".

Crane Extract Inlined Constant write_file =>
"[&]() {
  bsl::ofstream file(%a0);
  file << %a1;
}()" From "fstream".

Crane Extract Inlined Constant append_file =>
"[&]() {
  bsl::ofstream file(%a0, bsl::ios::app);
  file << %a1;
}()" From "fstream".

Crane Extract Inlined Constant file_exists =>
  "bdls::FilesystemUtil::exists(%a0)" From "bdls_filesystemutil.h".
Crane Extract Inlined Constant remove_file =>
  "bdls::FilesystemUtil::remove(%a0)" From "bdls_filesystemutil.h".
