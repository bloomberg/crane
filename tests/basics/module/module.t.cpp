// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <module.h>

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
  std::cout << "Starting tests...\n";

  // Test: NatMap.find 2 mymap   (* Should output Some 20 *)
  auto result1 = NatMap::find(2, mymap);
  ASSERT(result1.has_value());
  ASSERT(result1.value() == 20);
  std::cout << "NatMap.find(2, mymap) = ";
  if (result1.has_value()) {
    std::cout << "Some(" << result1.value() << ")" << std::endl;
  } else {
    std::cout << "None" << std::endl;
  }

  // Test: NatMap.find 4 mymap   (* Should output None *)
  auto result2 = NatMap::find(4, mymap);
  ASSERT(!result2.has_value());
  std::cout << "NatMap.find(4, mymap) = ";
  if (result2.has_value()) {
    std::cout << "Some(" << result2.value() << ")" << std::endl;
  } else {
    std::cout << "None" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "All tests passed!" << std::endl;
  }
  return testStatus;
}
