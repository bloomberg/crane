// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <io.h>

#include <functional>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

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

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // Feed stdin so get_line returns "Alice"
  std::istringstream fake_input("Alice\n");
  std::cin.rdbuf(fake_input.rdbuf());

  auto s = iotest::test4();
  ASSERT(s == "I read the name Alice from the command line!");
  std::cout << (testStatus ? "FAIL" : "PASS") << ": io get_line test\n";
  return testStatus;
}

// clang++ -I. -std=c++23 io.o io.t.cpp -o io.t.o; ./io.t.o
