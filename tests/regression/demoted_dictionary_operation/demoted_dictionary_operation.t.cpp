// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <demoted_dictionary_operation.h>

#include <iostream>

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
  ASSERT(DemotedDictionaryOperation::seven == 7u);
  ASSERT(DemotedDictionaryOperation::seventeen == 17u);

  if (testStatus == 0) {
    std::cout << "All demoted_dictionary_operation tests passed!\n";
  }
  return testStatus;
}
