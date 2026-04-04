// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <unit_void_edge2.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

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
  ASSERT(UnitVoidEdge2::test_let_use == 42u);
  ASSERT(UnitVoidEdge2::test_let_match == 3u);
  ASSERT(UnitVoidEdge2::test_let_chain == 42u);
  ASSERT(UnitVoidEdge2::test_let_if_t == 42u);
  ASSERT(UnitVoidEdge2::test_let_if_f == 0u);
  ASSERT(UnitVoidEdge2::test_call_fix == 7u);
  ASSERT(UnitVoidEdge2::test_fix_used == 42u);
  ASSERT(UnitVoidEdge2::test_call_discard == 11u);
  ASSERT(UnitVoidEdge2::test_call_use == 42u);
  ASSERT(UnitVoidEdge2::test_apply_take == 42u);
  ASSERT(UnitVoidEdge2::test_option_use == 42u);
  ASSERT(UnitVoidEdge2::test_compose == 42u);
  ASSERT(UnitVoidEdge2::test_use_pair == 7u);

  return testStatus;
}
