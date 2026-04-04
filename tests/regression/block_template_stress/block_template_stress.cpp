#include <block_template_stress.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Block template in a fixpoint body
std::shared_ptr<List<std::string>>
BlockTemplateStress::read_n_lines(const unsigned int n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    unsigned int n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    std::shared_ptr<List<std::string>> rest = read_n_lines(n_);
    return List<std::string>::cons(line, rest);
  }
}

/// 2. Block template inside a monadic if-then-else
std::string BlockTemplateStress::conditional_read(const bool do_read) {
  if (do_read) {
    std::string s;
    std::getline(std::cin, s);
    return s + "!"s;
  } else {
    return "skipped";
  }
}

/// 3. Block template of non-string type (nat) in bind
unsigned int BlockTemplateStress::read_and_add() {
  unsigned int n;
  std::cin >> n;
  return (n + 1u);
}

/// 4. Block template used in multiple match arms
std::string BlockTemplateStress::branch_read(const unsigned int choice) {
  if (choice <= 0) {
    std::string a;
    std::getline(std::cin, a);
    return "zero: "s + a;
  } else {
    unsigned int n = choice - 1;
    if (n <= 0) {
      std::string b;
      std::getline(std::cin, b);
      return "one: "s + b;
    } else {
      unsigned int _x = n - 1;
      std::string c;
      std::getline(std::cin, c);
      return "other: "s + c;
    }
  }
}

/// 5. Block template in nested bind chain with arithmetic
unsigned int BlockTemplateStress::read_two_nats() {
  unsigned int a;
  std::cin >> a;
  unsigned int b;
  std::cin >> b;
  return (a + b);
}

/// 6. Block template result fed to another function
void BlockTemplateStress::block_result_as_arg() {
  unsigned int _x;
  std::cin >> _x;
  std::string s;
  std::getline(std::cin, s);
  std::cout << s + " read"s << '\n';
  return;
}

/// 9. Block template with %a0 inside a fixpoint
std::shared_ptr<List<std::string>> BlockTemplateStress::read_files(
    const std::shared_ptr<List<std::string>> &paths) {
  return std::visit(Overloaded{[](const typename List<std::string>::Nil _args)
                                   -> std::shared_ptr<List<std::string>> {
                                 return List<std::string>::nil();
                               },
                               [](const typename List<std::string>::Cons _args)
                                   -> std::shared_ptr<List<std::string>> {
                                 std::string content;
                                 {
                                   std::ifstream _f(_args.d_a0);
                                   if (_f.good())
                                     std::getline(_f, content);
                                   else
                                     content = _args.d_a0;
                                 };
                                 std::shared_ptr<List<std::string>> rest =
                                     read_files(_args.d_a1);
                                 return List<std::string>::cons(content, rest);
                               }},
                    paths->v());
}

/// 10. Block template interleaved with void calls
std::string BlockTemplateStress::interleaved_void() {
  std::cout << "Enter name:"s << '\n';
  std::string name;
  std::getline(std::cin, name);
  std::cout << "Hello, "s + name << '\n';
  std::cout << "Enter age:"s << '\n';
  std::string age;
  std::getline(std::cin, age);
  return name + " is "s + age;
}
