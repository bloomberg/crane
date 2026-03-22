// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <iostream>
#include <loopify_nested_constructs.h>

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

int main() {
  // multi_let
  ASSERT(LoopifyNestedConstructs::multi_let(0u) == 0u);
  ASSERT(LoopifyNestedConstructs::multi_let(1u) == 3u);  // a=0, b=0, c=3
  ASSERT(LoopifyNestedConstructs::multi_let(2u) == 8u);  // c=5 + multi_let(1)=3

  // nested_if
  ASSERT(LoopifyNestedConstructs::nested_if(0u) == 0u);
  ASSERT(LoopifyNestedConstructs::nested_if(1u) == 1u);
  ASSERT(LoopifyNestedConstructs::nested_if(2u) == 1u);
  ASSERT(LoopifyNestedConstructs::nested_if(5u) == 1u);

  // deep_nest
  ASSERT(LoopifyNestedConstructs::deep_nest(0u) == 0u);
  ASSERT(LoopifyNestedConstructs::deep_nest(1u) == 2u);
  ASSERT(LoopifyNestedConstructs::deep_nest(2u) == 6u);
  ASSERT(LoopifyNestedConstructs::deep_nest(3u) == 14u);

  // let_nested
  ASSERT(LoopifyNestedConstructs::let_nested(0u) == 0u);
  ASSERT(LoopifyNestedConstructs::let_nested(1u) == 1u);
  ASSERT(LoopifyNestedConstructs::let_nested(3u) == 6u);  // 3+2+1+0

  // mod_pattern
  ASSERT(LoopifyNestedConstructs::mod_pattern(1u) == 1u);
  ASSERT(LoopifyNestedConstructs::mod_pattern(2u) == 0u);
  ASSERT(LoopifyNestedConstructs::mod_pattern(3u) == 0u);  // 3 mod (1+0) = 0

  // tuple_constr
  auto t0 = LoopifyNestedConstructs::tuple_constr(0u);
  ASSERT(t0.first.first == 0u);
  ASSERT(t0.first.second == 0u);
  ASSERT(t0.second == 0u);

  auto t3 = LoopifyNestedConstructs::tuple_constr(3u);
  ASSERT(t3.first.first == 3u);
  ASSERT(t3.first.second == 6u);  // 1+2+3
  ASSERT(t3.second == 14u);  // 1+4+9

  // alternating_ops
  ASSERT(LoopifyNestedConstructs::alternating_ops(0u) == 0u);
  ASSERT(LoopifyNestedConstructs::alternating_ops(1u) == 2u);
  ASSERT(LoopifyNestedConstructs::alternating_ops(2u) == 4u);
  ASSERT(LoopifyNestedConstructs::alternating_ops(3u) == 10u);  // 6 + 2 + 2

  // chained_comp
  ASSERT(LoopifyNestedConstructs::chained_comp(0u) == 1u);
  ASSERT(LoopifyNestedConstructs::chained_comp(1u) == 1u);
  ASSERT(LoopifyNestedConstructs::chained_comp(2u) == 1u);

  // compute_with_lets
  ASSERT(LoopifyNestedConstructs::compute_with_lets(0u) == 0u);
  ASSERT(LoopifyNestedConstructs::compute_with_lets(1u) == 1u);
  ASSERT(LoopifyNestedConstructs::compute_with_lets(2u) == 2u);
  ASSERT(LoopifyNestedConstructs::compute_with_lets(5u) == 44u);  // (f(4)+f(3))*2 = (16+6)*2

  // nested_match
  ASSERT(LoopifyNestedConstructs::nested_match(0u) == 0u);
  ASSERT(LoopifyNestedConstructs::nested_match(1u) == 1u);
  ASSERT(LoopifyNestedConstructs::nested_match(5u) == 9u);  // 5+nested_match(3) = 5+3+1 = 9

  if (testStatus > 0) {
    std::cerr << "Error: " << testStatus << " test(s) failed." << std::endl;
    return testStatus;
  }
  return 0;
}
