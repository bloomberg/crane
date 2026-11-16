(* The layout of generated C++: printer text in, LLVM-style lines out. *)

open Crane_plugin

let check name ~input ~expected =
  let got = Cpp_layout.layout input in
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
    ~expected:"auto g = [&](int a) -> int {\n  int b = a;\n  return b + 1;\n};\n"
