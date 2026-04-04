// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for block template (%result) type inference.
// Verifies that %result expansion emits the correct C++ type declaration
// for non-string return types.

#include <block_template_types.h>

#include <cassert>
#include <iostream>
#include <sstream>
#include <string>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__)

struct CinRedirect {
  std::streambuf *orig;
  std::istringstream iss;
  CinRedirect(const std::string &input) : orig(std::cin.rdbuf()), iss(input) {
    std::cin.rdbuf(iss.rdbuf());
  }
  ~CinRedirect() { std::cin.rdbuf(orig); }
};

void test_read_nat() {
  CinRedirect redir("42\n");
  auto n = BlockTemplateTypes::test_read_nat();
  ASSERT(n == 43u);
  std::cout << "PASS: test_read_nat (%result as unsigned int)\n";
}

void test_is_positive_true() {
  CinRedirect redir("5\n");
  auto s = BlockTemplateTypes::test_is_positive();
  ASSERT(s == "positive");
  std::cout << "PASS: test_is_positive true (%result as bool)\n";
}

void test_is_positive_zero() {
  CinRedirect redir("0\n");
  auto s = BlockTemplateTypes::test_is_positive();
  ASSERT(s == "zero");
  std::cout << "PASS: test_is_positive zero (%result as bool)\n";
}

void test_parse_nat() {
  CinRedirect redir("10\n");
  auto n = BlockTemplateTypes::test_parse_nat();
  ASSERT(n == 12u);
  std::cout << "PASS: test_parse_nat (%result as unsigned int from string)\n";
}

void test_mixed() {
  CinRedirect redir("Alice\n7\n");
  auto s = BlockTemplateTypes::test_mixed();
  ASSERT(s == "Alice wins");
  std::cout << "PASS: test_mixed (string + unsigned int + bool in one fn)\n";
}

void test_nat_arith() {
  CinRedirect redir("3\n4\n");
  auto n = BlockTemplateTypes::test_nat_arith();
  ASSERT(n == 7u);
  std::cout << "PASS: test_nat_arith (two unsigned int block templates)\n";
}

int main() {
  test_read_nat();
  test_is_positive_true();
  test_is_positive_zero();
  test_parse_nat();
  test_mixed();
  test_nat_arith();

  std::cout << (testStatus ? "FAIL" : "PASS")
            << ": block_template_types\n";
  return testStatus;
}
