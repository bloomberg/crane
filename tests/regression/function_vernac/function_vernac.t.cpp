// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "function_vernac.h"

#include <iostream>
#include <variant>
#include <vector>

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

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

List<unsigned int>
vector_to_list(const std::vector<unsigned int> &vec) {
  auto result = List<unsigned int>::nil();
  for (auto it = vec.rbegin(); it != vec.rend(); ++it) {
    result = List<unsigned int>::cons(*it, std::move(result));
  }
  return result;
}

int main() {
  // Test 1: div2
  {
    ASSERT(FunctionVernac::div2(0) == 0);
    ASSERT(FunctionVernac::div2(1) == 0);
    ASSERT(FunctionVernac::div2(6) == 3);
    ASSERT(FunctionVernac::div2(7) == 3);
    ASSERT(FunctionVernac::div2(10) == 5);
    std::cout << "Test 1 (div2): PASSED" << std::endl;
  }

  // Test 2: list_sum
  {
    auto l = vector_to_list({1, 2, 3, 4, 5});
    ASSERT(FunctionVernac::list_sum(l) == 15);
    std::cout << "Test 2 (list_sum): PASSED" << std::endl;
  }

  // Test 3: test constants
  {
    ASSERT(FunctionVernac::test_div2 == 5);
    ASSERT(FunctionVernac::test_sum == 15);
    std::cout << "Test 3 (constants): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll Function vernacular tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
