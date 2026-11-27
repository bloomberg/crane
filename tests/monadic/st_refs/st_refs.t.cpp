// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "st_refs.h"

#include <iostream>

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
  {
    auto result = StRefs::new_and_read_both_nat;
    ASSERT(result.first == 5);
    ASSERT(result.second == 6);
    std::cout << "new_and_read_both_nat: (" << result.first << ", "
              << result.second << ")" << std::endl;
  }

  {
    auto result = StRefs::tree_simp_nat;
    ASSERT(result == 5);
    std::cout << "tree_simp_nat: " << result << std::endl;
  }

  {
    auto result = StRefs::tree_simp_another_nat;
    ASSERT(result == 6);
    std::cout << "tree_simp_another_nat: " << result << std::endl;
  }

  {
    auto result = StRefs::new_and_read_both_bool;
    ASSERT(result.first == false);
    ASSERT(result.second == true);
    std::cout << "new_and_read_both_bool: (" << result.first << ", "
              << result.second << ")" << std::endl;
  }

  {
    auto result = StRefs::tree_simp_bool;
    ASSERT(result == true);
    std::cout << "tree_simp_bool: " << result << std::endl;
  }

  {
    auto result = StRefs::swapped;
    ASSERT(result.first == 2);
    ASSERT(result.second == 1);
    std::cout << "swapped: (" << result.first << ", " << result.second << ")"
              << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll st_refs tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
