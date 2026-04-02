(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   IO effect events for the BDE flavor.

   Provides IO effects ([iIO]) as composable inductives with smart constructors
   and C++ extraction mappings. Use [itree iIO A] as the monadic type.

   Smart constructors are polymorphic over the effect type [E] via [-<],
   so they can be used in any composed effect that includes the relevant
   sub-effect.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.ITree.

Inductive consoleE : Type -> Type :=
| Print : string -> consoleE unit
| PrintEndline : string -> consoleE unit
| GetLine : consoleE string.

Inductive fileE : Type -> Type :=
| ReadFile : string -> fileE string
| WriteFile : string -> string -> fileE unit
| AppendFile : string -> string -> fileE unit
| FileExists : string -> fileE bool
| RemoveFile : string -> fileE unit.

Crane Extract Skip consoleE.
Crane Extract Skip fileE.

Definition iIO := consoleE +' fileE.
Crane Extract Skip iIO.

Definition print {E} `{consoleE -< E} (s : string) : itree E unit := embed (Print s).
Definition print_endline {E} `{consoleE -< E} (s : string) : itree E unit := embed (PrintEndline s).
Definition get_line {E} `{consoleE -< E} : itree E string := embed GetLine.

Definition read {E} `{fileE -< E} (path : string) : itree E string := embed (ReadFile path).
Definition write_file {E} `{fileE -< E} (path content : string) : itree E unit := embed (WriteFile path content).
Definition append_file {E} `{fileE -< E} (path content : string) : itree E unit := embed (AppendFile path content).
Definition file_exists {E} `{fileE -< E} (path : string) : itree E bool := embed (FileExists path).
Definition remove_file {E} `{fileE -< E} (path : string) : itree E unit := embed (RemoveFile path).

Crane Extract Inlined Constant print => "bsl::cout << %a1".
Crane Extract Inlined Constant print_endline => "bsl::cout << %a1 << '\n'".
Crane Extract Inlined Constant get_line =>
"((void)sizeof(%a0), []() -> bsl::string {
    bsl::string s;
    bsl::getline(bsl::cin, s);
    return s;
}())".

Crane Extract Inlined Constant read =>
"[]() -> bsl::string {
  bsl::ifstream file(%a1);
  if (!file) {
      bsl::cerr << ""Failed to open file "" << %a1 << '\n';
      return bsl::string{};
  }
  return bsl::string(
      bsl::istreambuf_iterator<char>(file),
      bsl::istreambuf_iterator<char>());
}()" From "fstream".

Crane Extract Inlined Constant write_file =>
"[&]() {
  bsl::ofstream file(%a1);
  file << %a2;
}()" From "fstream".

Crane Extract Inlined Constant append_file =>
"[&]() {
  bsl::ofstream file(%a1, bsl::ios::app);
  file << %a2;
}()" From "fstream".

Crane Extract Inlined Constant file_exists =>
  "std::filesystem::exists(std::filesystem::path(%a1))" From "filesystem".

Crane Extract Inlined Constant remove_file =>
  "std::filesystem::remove(std::filesystem::path(%a1))" From "filesystem".
