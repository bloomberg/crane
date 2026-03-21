// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_numeric_misc.h>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using UIntList = List<unsigned int>;

int main() {
  auto nil = UIntList::ctor::Nil_();
  auto l5 = UIntList::ctor::Cons_(1u, UIntList::ctor::Cons_(2u, UIntList::ctor::Cons_(
    3u, UIntList::ctor::Cons_(4u, UIntList::ctor::Cons_(5u, nil)))));

  // sum_abs
  ASSERT(LoopifyNumericMisc::sum_abs(l5) == 15u);

  // alternating_ops
  ASSERT(LoopifyNumericMisc::alternating_ops(5u) > 0u);

  // count_even
  ASSERT(LoopifyNumericMisc::count_even(l5) == 2u);

  // count_odd
  ASSERT(LoopifyNumericMisc::count_odd(l5) == 3u);

  // product
  ASSERT(LoopifyNumericMisc::product(l5) == 120u);

  // sum_of_squares
  ASSERT(LoopifyNumericMisc::sum_of_squares(l5) == 55u);

  // max_two
  ASSERT(LoopifyNumericMisc::max_two(10u, 20u) == 20u);

  // list_max
  ASSERT(LoopifyNumericMisc::list_max(l5) == 5u);

  // list_min
  ASSERT(LoopifyNumericMisc::list_min(l5) == 1u);

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
