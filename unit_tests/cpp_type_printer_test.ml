(* The type printer writes a compound type around a declarator hole: a
   [const] on a pointer or reference qualifies the declarator, one on any
   other type stays in front ({!Emit.Print.pp_cpp_type}). *)

open Crane_plugin
open Names
module T = Cpp_ir.Type

let check name (ty : Cpp_ir.Resolved.Type.t) expected =
  let got =
    Pp.string_of_ppcmds
      (Emit.Print.pp_cpp_type Unit_plan.Context.detached Unit_plan.Cpp_state.no_plans false [] ty)
  in
  if not (String.equal got expected) then (
    Printf.eprintf "cpp_type_printer: %s: got %S, expected %S\n" name got expected;
    exit 1 )

let t : Cpp_ir.Resolved.Type.t = Variable (Named (Id.of_string "T"))
let ext s args : Cpp_ir.Resolved.Type.t = External (s, args)
let lref x : Cpp_ir.Resolved.Type.t = Reference (Lvalue, x)
let rref x : Cpp_ir.Resolved.Type.t = Reference (Forwarding, x)

let () =
  check "pointer" (Pointer t) "T*";
  check "pointer to const" (Pointer (Const t)) "const T*";
  check "const pointer" (Const (Pointer t)) "T* const";
  check "reference to pointer" (lref (Pointer t)) "T*&";
  check "reference to const pointer" (lref (Const (Pointer t))) "T* const&";
  check "reference to pointer to const" (lref (Pointer (Const t))) "const T*&";
  check "const pointer to const" (Const (Pointer (Const t))) "const T* const";
  check "pointer to const pointer" (Pointer (Const (Pointer t))) "T* const*";
  check "reference to const" (lref (Const t)) "const T&";
  check "forwarding reference" (rref t) "T&&";
  check "reference to const shared_ptr"
    (lref (Const (ext "std::shared_ptr" [t])))
    "const std::shared_ptr<T>&";
  check "span of const" (ext "std::span" [Const t]) "std::span<const T>";
  check "span" (ext "std::span" [t]) "std::span<T>";
  check "span of const pointers" (ext "std::span" [Const (Pointer t)]) "std::span<T* const>"

(* Laid out, the declarators bind to the name as clang-format's LLVM style
   writes them. *)
let () =
  let input = "void f(T* const& a, const T*& b, T* const c, const T& d);" in
  let expected = "void f(T *const &a, const T *&b, T *const c, const T &d);\n" in
  let got = Emit.Layout.layout input in
  if got <> expected then (
    Printf.eprintf "cpp_type_printer: layout: got %S, expected %S\n" got expected;
    exit 1 )
