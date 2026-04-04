// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression test for block template (%result) hygiene.
// Verifies that %result expansion does not cause variable shadowing,
// name collisions, or scoping errors.

#include <block_template_hygiene.h>

#include <cassert>
#include <fstream>
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

// Helper: redirect std::cin to read from a string.
struct CinRedirect {
  std::streambuf *orig;
  std::istringstream iss;
  CinRedirect(const std::string &input) : orig(std::cin.rdbuf()), iss(input) {
    std::cin.rdbuf(iss.rdbuf());
  }
  ~CinRedirect() { std::cin.rdbuf(orig); }
};

void test_same_name_twice() {
  CinRedirect redir("first\nsecond\n");
  auto s = BlockTemplateHygiene::same_name_twice();
  ASSERT(s == "second (second)");
  std::cout << "PASS: same_name_twice\n";
}

void test_same_name_thrice() {
  CinRedirect redir("one\ntwo\nthree\n");
  auto s = BlockTemplateHygiene::same_name_thrice();
  ASSERT(s == "three (third)");
  std::cout << "PASS: same_name_thrice\n";
}

void test_shadow_internal_name() {
  CinRedirect redir("hello\n");
  auto s = BlockTemplateHygiene::shadow_internal_name();
  ASSERT(s == "hello!");
  std::cout << "PASS: shadow_internal_name\n";
}

void test_interleaved_templates() {
  CinRedirect redir("alpha\nbeta\ngamma\n");
  // Suppress stdout from print/print_endline
  std::ostringstream devnull;
  auto orig_cout = std::cout.rdbuf(devnull.rdbuf());
  auto s = BlockTemplateHygiene::interleaved_templates();
  std::cout.rdbuf(orig_cout);
  ASSERT(s == "alphabetagamma");
  std::cout << "PASS: interleaved_templates\n";
}

void test_block_with_args() {
  // Create a temp file "data.txt" with content
  { std::ofstream f("data.txt"); f << "file_content"; }
  auto s = BlockTemplateHygiene::block_with_args();
  ASSERT(s == "file_content read");
  std::remove("data.txt");
  std::cout << "PASS: block_with_args\n";
}

void test_block_with_args_same_name() {
  { std::ofstream f("a.txt"); f << "aaa"; }
  { std::ofstream f("b.txt"); f << "bbb"; }
  auto s = BlockTemplateHygiene::block_with_args_same_name();
  ASSERT(s == "bbb done");
  std::remove("a.txt");
  std::remove("b.txt");
  std::cout << "PASS: block_with_args_same_name\n";
}

void test_result_in_expr() {
  CinRedirect redir("World\n");
  std::ostringstream capture;
  auto orig_cout = std::cout.rdbuf(capture.rdbuf());
  BlockTemplateHygiene::result_in_expr();
  std::cout.rdbuf(orig_cout);
  // print_endline outputs "Hello, World\n"
  ASSERT(capture.str().find("Hello, World") != std::string::npos);
  std::cout << "PASS: result_in_expr\n";
}

void test_let_after_block() {
  CinRedirect redir("Jane\nDoe\n");
  auto s = BlockTemplateHygiene::let_after_block();
  ASSERT(s == "Jane Doe");
  std::cout << "PASS: let_after_block\n";
}

void test_bind_named_result() {
  CinRedirect redir("okay\n");
  auto s = BlockTemplateHygiene::bind_named_result();
  ASSERT(s == "okay!");
  std::cout << "PASS: bind_named_result\n";
}

void test_bind_named_underscore_r() {
  CinRedirect redir("underscore\n");
  auto s = BlockTemplateHygiene::bind_named_underscore_r();
  ASSERT(s == "underscore!");
  std::cout << "PASS: bind_named_underscore_r\n";
}

void test_expr_position_iife() {
  CinRedirect redir("iife\n");
  // get_line in expression position (Ret get_line) uses IIFE fallback
  auto s = BlockTemplateHygiene::expr_position_iife();
  ASSERT(s == "iife");
  std::cout << "PASS: expr_position_iife\n";
}

int main() {
  test_same_name_twice();
  test_same_name_thrice();
  test_shadow_internal_name();
  test_interleaved_templates();
  test_block_with_args();
  test_block_with_args_same_name();
  test_result_in_expr();
  test_let_after_block();
  test_bind_named_result();
  test_bind_named_underscore_r();
  test_expr_position_iife();

  std::cout << (testStatus ? "FAIL" : "PASS") << ": block_template_hygiene ("
            << (testStatus ? "some" : "all") << " tests passed)\n";
  return testStatus;
}
