(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   IO effect events for the standard library flavor.

   Provides axiomatized IO effects ([iIO]) with smart constructors
   and C++ extraction mappings. Use [itree iIO A] as the monadic type.
*)
From Corelib Require Import PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree.

Module IO_axioms.
  Axiom iIO : Type -> Type.
  Axiom iprint : string -> iIO unit.
  Axiom iprint_endline : string -> iIO unit.
  Axiom iget_line : iIO string.
  Axiom iread : string -> iIO string.

End IO_axioms.

Crane Extract Skip Module IO_axioms.
Export IO_axioms.

Definition print (s : string) : itree iIO unit := ITree.trigger (iprint s).
Definition print_endline (s : string) : itree iIO unit := ITree.trigger (iprint_endline s).
Definition get_line : itree iIO string := ITree.trigger iget_line.
Definition read (s : string) : itree iIO string := ITree.trigger (iread s).

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
