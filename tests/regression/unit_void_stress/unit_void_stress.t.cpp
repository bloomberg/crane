// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <unit_void_stress.h>

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
  // test_let_void: void side effect then pair
  ASSERT(UnitVoidStress::test_let_void.first == 7u);
  ASSERT(UnitVoidStress::test_let_void.second == 42u);

  // test_seq: sequential voids then value
  ASSERT(UnitVoidStress::test_seq == 42u);

  // test_branch: void in one branch
  ASSERT(UnitVoidStress::test_branch == 42u);

  // make_some_tt: option unit should have value
  ASSERT(UnitVoidStress::make_some_tt.has_value());

  // make_unit_pair: pair of units
  // Just verify it compiles and doesn't crash

  // test_apply_in_pair_void: polymorphic HOF with void callback
  ASSERT(UnitVoidStress::test_apply_in_pair_void.first == 5u);

  // test_apply_result_void: polymorphic apply with void callback
  // Just verify it compiles and doesn't crash (returns monostate)

  return testStatus;
}
