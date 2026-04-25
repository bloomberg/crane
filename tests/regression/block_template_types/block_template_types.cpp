#include <block_template_types.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>

/// %result inferred as unsigned int.
unsigned int BlockTemplateTypes::test_read_nat() {
  unsigned int n;
  std::cin >> n;
  return (n + 1u);
}

/// %result inferred as bool, with unsigned int in same scope.
std::string BlockTemplateTypes::test_is_positive() {
  unsigned int n;
  std::cin >> n;
  bool b;
  b = (n > 0u);
  return [=]() mutable -> std::string {
    if (b) {
      return "positive";
    } else {
      return "zero";
    }
  }();
}

/// %result inferred as unsigned int from string argument.
/// Tests %a0 and %result together with nat return type.
unsigned int BlockTemplateTypes::test_parse_nat() {
  std::string s;
  std::getline(std::cin, s);
  unsigned int n;
  n = static_cast<unsigned int>(std::stoul(s));
  return (n + 2u);
}

/// Three different block template types in one function:
/// std::string (get_line), unsigned int (read_nat), bool (is_positive).
std::string BlockTemplateTypes::test_mixed() {
  std::string name;
  std::getline(std::cin, name);
  unsigned int n;
  std::cin >> n;
  bool b;
  b = (n > 0u);
  return name + [=]() mutable -> std::string {
    if (b) {
      return " wins";
    } else {
      return " loses";
    }
  }();
}

/// Two unsigned int block templates with arithmetic on results.
unsigned int BlockTemplateTypes::test_nat_arith() {
  unsigned int a;
  std::cin >> a;
  unsigned int b;
  std::cin >> b;
  return (a + b);
}
