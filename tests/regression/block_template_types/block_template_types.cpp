#include "block_template_types.h"

/// %result inferred as unsigned int.
uint64_t BlockTemplateTypes::test_read_nat() {
  uint64_t n;
  std::cin >> n;
  return (n + UINT64_C(1));
}

/// %result inferred as bool, with unsigned int in same scope.
std::string BlockTemplateTypes::test_is_positive() {
  uint64_t n;
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
uint64_t BlockTemplateTypes::test_parse_nat() {
  std::string s;
  std::getline(std::cin, s);
  uint64_t n;
  n = static_cast<unsigned int>(std::stoul(s));
  return (n + UINT64_C(2));
}

/// Three different block template types in one function:
/// std::string (get_line), unsigned int (read_nat), bool (is_positive).
std::string BlockTemplateTypes::test_mixed() {
  std::string name;
  std::getline(std::cin, name);
  uint64_t n;
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
uint64_t BlockTemplateTypes::test_nat_arith() {
  uint64_t a;
  std::cin >> a;
  uint64_t b;
  std::cin >> b;
  return (a + b);
}
