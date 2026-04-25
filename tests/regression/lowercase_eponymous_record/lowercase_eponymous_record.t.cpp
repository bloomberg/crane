// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <lowercase_eponymous_record.h>

#include <iostream>
#include <memory>

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
  // The bug: struct is defined as 'state' but type references use 'State'.
  // This test will fail to compile until the naming is consistent.
  auto result = LowercaseEponymousRecord::example;
  ASSERT(result.x == 42);
  ASSERT(result.y == 0);

  return testStatus;
}
