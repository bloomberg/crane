// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <ack.h>

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
  std::cout << "Testing Ackermann function...\n";

  // Test base cases
  ASSERT(Ack::ack(0, 0) == 1);
  ASSERT(Ack::ack(0, 1) == 2);
  ASSERT(Ack::ack(0, 5) == 6);

  // Test recursive cases
  ASSERT(Ack::ack(1, 0) == 2);
  ASSERT(Ack::ack(1, 1) == 3);
  ASSERT(Ack::ack(1, 5) == 7);

  ASSERT(Ack::ack(2, 0) == 3);
  ASSERT(Ack::ack(2, 1) == 5);
  ASSERT(Ack::ack(2, 2) == 7);
  ASSERT(Ack::ack(2, 4) == 11);

  ASSERT(Ack::ack(3, 0) == 5);
  ASSERT(Ack::ack(3, 1) == 13);
  ASSERT(Ack::ack(3, 2) == 29);
  ASSERT(Ack::ack(3, 3) == 61);
  ASSERT(Ack::ack(3, 7) == 1021);

  if (testStatus == 0) {
    std::cout << "All Ackermann tests passed!\n";
  }

  return testStatus;
}
