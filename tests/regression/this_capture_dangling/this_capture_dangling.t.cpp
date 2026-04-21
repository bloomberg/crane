#include <this_capture_dangling.h>

#include <cassert>
#include <iostream>

int main() {
  using TCD = ThisCaptureDangling;

  // test1: get_fn on temporary tree (sum=42).
  // BUG: if methodified, closure captures dangling raw 'this'.
  // Expected: 10 + 42 = 52.
  auto r1 = TCD::test1;
  std::cout << "test1 = " << r1 << " (expected 52)" << std::endl;
  assert(r1 == 52u);

  // test2: get_fn on larger temporary tree (sum=42).
  // Expected: 5 + 42 = 47.
  auto r2 = TCD::test2;
  std::cout << "test2 = " << r2 << " (expected 47)" << std::endl;
  assert(r2 == 47u);

  // test3: Extra allocation between closure creation and use.
  // Expected: 6 + 100 = 106.
  auto r3 = TCD::test3;
  std::cout << "test3 = " << r3 << " (expected 106)" << std::endl;
  assert(r3 == 106u);

  std::cout << "All this_capture_dangling tests passed!" << std::endl;
  return 0;
}
