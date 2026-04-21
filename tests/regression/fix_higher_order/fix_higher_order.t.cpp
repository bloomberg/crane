#include <fix_higher_order.h>

#include <cassert>
#include <iostream>

int main() {
  using FHO = FixHigherOrder;

  // test1: make_wrapped(5) -> Some(go), go(3) = 5+3 = 8.
  // BUG: fixpoint escapes through wrapper function call.
  auto r1 = FHO::test1;
  std::cout << "test1 = " << r1 << " (expected 8)" << std::endl;
  assert(r1 == 8u);

  // test2: make_wrapped(42), noise=15, go(10) = 42+10 = 52, +15 = 67.
  auto r2 = FHO::test2;
  std::cout << "test2 = " << r2 << " (expected 67)" << std::endl;
  assert(r2 == 67u);

  // test3: Doubly wrapped, go(7) = 100+7 = 107.
  auto r3 = FHO::test3;
  std::cout << "test3 = " << r3 << " (expected 107)" << std::endl;
  assert(r3 == 107u);

  std::cout << "All fix_higher_order tests passed!" << std::endl;
  return 0;
}
