// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <unit_void_edge.h>

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
  // 1. let-binding void call result
  ASSERT(UnitVoidEdge::test_let_bind == 42u);

  // 4. map_to_unit
  ASSERT(UnitVoidEdge::test_map == 42u);

  // 6. nested lets
  ASSERT(UnitVoidEdge::test_nested == 42u);

  // 7. option unit matching
  ASSERT(UnitVoidEdge::test_match_some == 1u);
  ASSERT(UnitVoidEdge::test_match_none == 0u);

  // 10. use_helper
  ASSERT(UnitVoidEdge::test_use_helper == 7u);

  // 11. match_unit_nontail
  ASSERT(UnitVoidEdge::test_match_nontail == 7u);

  // 15. poly_take tt
  ASSERT(UnitVoidEdge::test_take_tt == 42u);

  // 17. double match unit
  ASSERT(UnitVoidEdge::test_double_match == 99u);

  // 19. record with unit field
  ASSERT(UnitVoidEdge::test_record_unit == 99u);

  return testStatus;
}
