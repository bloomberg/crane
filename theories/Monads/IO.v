(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree.

Module IO_axioms.
  Axiom iIO : Type -> Type.
  Axiom iprint : string -> iIO void.
  Axiom iprint_endline : string -> iIO void.
  Axiom iget_line : iIO string.
  Axiom iread : string -> iIO string.

End IO_axioms.

Crane Extract Skip Module IO_axioms.
Import IO_axioms.

Definition IO : Type -> Type := itree iIO.
Definition print (s : string) : IO void := trigger (iprint s).
Definition print_endline (s : string) : IO void := trigger (iprint_endline s).
Definition get_line : IO string := trigger iget_line.
Definition read (s : string) : IO string := trigger (iread s).

Crane Extract Monad IO [bind := bind , ret := Ret].
Crane Extract Inlined Constant print => "std::cout << %a0".
Crane Extract Inlined Constant print_endline => "std::cout << %a0 << '\n'".
Crane Extract Inlined Constant get_line =>
"[]() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
}()".
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
