// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <pstring.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {
  std::cout << "Testing PString functions...\n";

  // Test nat_to_int
  auto zero_nat = std::make_shared<Nat::nat>(Nat::nat::O_{});
  ASSERT(PString::nat_to_int(zero_nat) == 0);

  auto one_nat = std::make_shared<Nat::nat>(Nat::nat::S_{zero_nat});
  ASSERT(PString::nat_to_int(one_nat) == 1);

  auto two_nat = std::make_shared<Nat::nat>(Nat::nat::S_{one_nat});
  ASSERT(PString::nat_to_int(two_nat) == 2);

  if (testStatus == 0) {
    std::cout << "All PString tests passed!\n";
  }

  return testStatus;
}
