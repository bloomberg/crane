#include <nested_partial_app.h>

#include <cassert>
#include <iostream>

int main() {
  using NPA = NestedPartialApp;

  // nested_partial_bug: g = build_node t1, h = g 42, invoke h twice
  // BUG: g is std::function<R(A,B)>, g(42u) tries partial application
  // which std::function doesn't support → compile error
  // Expected: (10 + 42 + 1) + (10 + 42 + 2) = 53 + 54 = 107
  auto r1 = NPA::nested_partial_bug;
  std::cout << "nested_partial_bug = " << r1 << std::endl;
  assert(r1 == 107u);

  // nested_partial_reuse: g used twice for different partial apps
  // Expected: (10 + 42 + 1) + (10 + 99 + 2) = 53 + 111 = 164
  auto r2 = NPA::nested_partial_reuse;
  std::cout << "nested_partial_reuse = " << r2 << std::endl;
  assert(r2 == 164u);

  // triple_partial: 4-arg function, triple nesting
  // Expected: (10 + 20 + 30 + 1) + (10 + 20 + 30 + 2) = 61 + 62 = 123
  auto r3 = NPA::triple_partial;
  std::cout << "triple_partial = " << r3 << std::endl;
  assert(r3 == 123u);

  std::cout << "All nested_partial_app tests passed!" << std::endl;
  return 0;
}
