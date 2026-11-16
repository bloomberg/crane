(* The layout of generated C++: printer text in, LLVM-style lines out. *)

open Crane_plugin

let check name ~input ~expected =
  let got = Emit.Layout.layout input in
  if got <> expected then (
    Printf.eprintf "cpp_layout: %s\n--- expected\n%s--- got\n%s" name expected got;
    exit 1 )

let () =
  check "blocks indent, short bodies merge, definitions are separated"
    ~input:"struct A {\nint x;\nint get() const {\nreturn x;}\nvoid set(int y) {\nx = y;\nx += 1;}\n};"
    ~expected:
      "struct A {\n\
      \  int x;\n\
       \n\
      \  int get() const { return x; }\n\
       \n\
      \  void set(int y) {\n\
      \    x = y;\n\
      \    x += 1;\n\
      \  }\n\
       };\n";
  check "declarators bind to the name, template lists get a space"
    ~input:"template<typename T>\nconst T& f(T&& x, T* p);"
    ~expected:"template <typename T> const T &f(T &&x, T *p);\n";
  check "includes sorted, quoted first, duplicates dropped"
    ~input:"#include <vector>\n#include \"b.h\"\n#include <memory>\n#include \"a.h\"\n#include <vector>\n"
    ~expected:"#include \"a.h\"\n#include \"b.h\"\n#include <memory>\n#include <vector>\n";
  check "access specifiers and case labels sit one level out"
    ~input:
      "struct S {\nprivate:\nint v_;\npublic:\nint f(int c) {\nswitch (c) {\ncase 1: {\nreturn 2;\n}\n\
       default:\nreturn 0;\n}\n}\n};"
    ~expected:
      "struct S {\n\
       private:\n\
      \  int v_;\n\
       \n\
       public:\n\
      \  int f(int c) {\n\
      \    switch (c) {\n\
      \    case 1: {\n\
      \      return 2;\n\
      \    }\n\
      \    default:\n\
      \      return 0;\n\
      \    }\n\
      \  }\n\
       };\n";
  check "long argument lists pack and align after the bracket"
    ~input:
      "int r = compute_something(first_argument_value, second_argument_value, third_argument_value);"
    ~expected:
      "int r = compute_something(first_argument_value, second_argument_value,\n\
      \                          third_argument_value);\n";
  check "a requires-clause goes on its own line"
    ~input:"template <typename F>  requires std::is_invocable_v<F>\nint call(F&& f) {\nreturn f();}"
    ~expected:"template <typename F>\n  requires std::is_invocable_v<F>\nint call(F &&f) {\n  return f();\n}\n";
  check "a lambda body indents from the line it starts on"
    ~input:"auto g = [&](int a) -> int {\nint b = a;\nreturn b + 1;\n};"
    ~expected:"auto g = [&](int a) -> int {\n  int b = a;\n  return b + 1;\n};\n";
  check "brackets opened on one line share a continuation, four columns in"
    ~input:"int r = outer_function_name(inner_function_name(argument_number_one, argument_number_two, argument_three));"
    ~expected:
      "int r = outer_function_name(inner_function_name(\n\
      \    argument_number_one, argument_number_two, argument_three));\n";
  check "an argument after one that took several lines starts a line"
    ~input:
      "auto p = String::string0(Ascii::ascii0(Bool0::FALSE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_, \
       Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_), string_of_uint(a0));"
    ~expected:
      "auto p = String::string0(\n\
      \    Ascii::ascii0(Bool0::FALSE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_,\n\
      \                  Bool0::TRUE_, Bool0::TRUE_, Bool0::FALSE_, Bool0::FALSE_),\n\
      \    string_of_uint(a0));\n";
  check "a call nested in a grouping parenthesis breaks from the operand"
    ~input:
      "Node &n = (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(std::move(_cell))) \
       : _root.emplace(std::move(_cell)));"
    ~expected:
      "Node &n = (_write ? *(*_write = std::make_shared<LoopifyLists::list<uint64_t>>(\n\
      \                          std::move(_cell)))\n\
      \                  : _root.emplace(std::move(_cell)));\n";
  check "nested calls holding lambdas break after the outer bracket, not per template argument"
    ~input:
      "Nat f(const Nat &x0_) {\nstatic const auto apply_all_1 = crane::immortal(apply_all<crane::fn<Nat(Nat)>>(\
       List<crane::fn<crane::fn<Nat(Nat)>(crane::fn<Nat(Nat)>)>>::cons([](crane::fn<Nat(Nat)> g) {\nreturn g;\n}, \
       List<crane::fn<crane::fn<Nat(Nat)>(crane::fn<Nat(Nat)>)>>::nil()), [](const Nat &x) {\nreturn Nat::s(x);\n}));\n\
       return apply_all_1(x0_);}"
    ~expected:
      "Nat f(const Nat &x0_) {\n\
      \  static const auto apply_all_1 =\n\
      \      crane::immortal(apply_all<crane::fn<Nat(Nat)>>(\n\
      \          List<crane::fn<crane::fn<Nat(Nat)>(crane::fn<Nat(Nat)>)>>::cons(\n\
      \              [](crane::fn<Nat(Nat)> g) { return g; },\n\
      \              List<crane::fn<crane::fn<Nat(Nat)>(crane::fn<Nat(Nat)>)>>::nil()),\n\
      \          [](const Nat &x) { return Nat::s(x); }));\n\
      \  return apply_all_1(x0_);\n\
       }\n";
  let chain n = String.concat "" (List.init n (fun _ -> "Nat::s(")) ^ "x" ^ String.make n ')' in
  check "a chain nested deeper than breaking could fit stays on one line"
    ~input:("auto v = List::cons(" ^ chain 40 ^ ", List::nil());")
    ~expected:("auto v = List::cons(\n    " ^ chain 40 ^ ",\n    List::nil());\n")
