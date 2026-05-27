// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "stmonad.h"


#include <iostream>
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

int natToInt(const Nat &n) {
  int count = 0;
  const Nat *cur = &n;
  while (std::holds_alternative<Nat::S>(cur->v())) {
    ++count;
    cur = std::get<Nat::S>(cur->v()).d_a0.get();
  }
  return count;
}

int main() {
  // Test 1: newAndReadBoth returns (5, 6)
  {
    auto result = newAndReadBoth<Nat, Nat>();
    const auto &[fst, snd] = std::get<Prod<Nat, Nat>::Pair>(result.v());
    ASSERT(natToInt(fst) == 5);
    ASSERT(natToInt(snd) == 6);
    std::cout << "Test 1 (newAndReadBoth): (" << natToInt(fst) << ", "
              << natToInt(snd) << ") PASSED" << std::endl;
  }

  // Test 2: tree_simp returns 5
  {
    auto result = tree_simp<Nat, Nat>();
    ASSERT(natToInt(result) == 5);
    std::cout << "Test 2 (tree_simp): " << natToInt(result) << " PASSED"
              << std::endl;
  }

  // Test 3: tree_simp_another returns 6
  {
    auto result = tree_simp_another<Nat, Nat>();
    ASSERT(natToInt(result) == 6);
    std::cout << "Test 3 (tree_simp_another): " << natToInt(result)
              << " PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll stmonad tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}

