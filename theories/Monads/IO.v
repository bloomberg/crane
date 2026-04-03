(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   IO effect events for the standard library flavor.

   Re-exports shared definitions from [IODefs.v] and adds C++ extraction
   mappings targeting the standard library ([std::]).
*)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Export Monads.IODefs.

Crane Extract Inductive consoleE => ""
  [ "std::cout << %a0"
    "std::cout << %a0 << '\n'"
    "[&]() -> std::string { std::string s; std::getline(std::cin, s); return s; }()" ]
  From "iostream".

Crane Extract Inductive fileE => ""
  [ "[]() -> std::string {
  std::ifstream file(%a0);
  if (!file) {
      std::cerr << ""Failed to open file "" << %a0 << '\n';
      return std::string{};
  }
  return std::string(
      std::istreambuf_iterator<char>(file),
      std::istreambuf_iterator<char>());
}()"
    "[&]() {
  std::ofstream file(%a0);
  file << %a1;
}()"
    "[&]() {
  std::ofstream file(%a0, std::ios::app);
  file << %a1;
}()"
    "std::filesystem::exists(std::filesystem::path(%a0))"
    "std::filesystem::remove(std::filesystem::path(%a0))" ]
  From "fstream" "filesystem".

Crane Extract Inlined Constant print => "std::cout << %a0" From "iostream".
Crane Extract Inlined Constant print_endline => "std::cout << %a0 << '\n'" From "iostream".
Crane Extract Inlined Constant get_line =>
  "std::getline(std::cin, %result)" From "iostream".

Crane Extract Inlined Constant read =>
"[]() -> std::string {
  std::ifstream file(%a0);
  if (!file) {
      std::cerr << ""Failed to open file "" << %a0 << '\n';
      return std::string{};
  }
  return std::string(
      std::istreambuf_iterator<char>(file),
      std::istreambuf_iterator<char>());
}()" From "fstream".

Crane Extract Inlined Constant write_file =>
"[&]() {
  std::ofstream file(%a0);
  file << %a1;
}()" From "fstream".

Crane Extract Inlined Constant append_file =>
"[&]() {
  std::ofstream file(%a0, std::ios::app);
  file << %a1;
}()" From "fstream".

Crane Extract Inlined Constant file_exists =>
  "std::filesystem::exists(std::filesystem::path(%a0))" From "filesystem".
Crane Extract Inlined Constant remove_file =>
  "std::filesystem::remove(std::filesystem::path(%a0))" From "filesystem".
