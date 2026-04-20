#include <accum_closure_capture.h>

#include <cassert>
#include <iostream>

int main() {
  using ACC = AccumClosureCapture;

  // test1: extract_closures on temporary tree (sum=42).
  // Closures stored in fn_list capture dangling this.
  // Expected: 0 + 42 + 20 + 42 = 104.
  auto r1 = ACC::test1;
  std::cout << "test1 = " << r1 << " (expected 104)" << std::endl;
  assert(r1 == 104u);

  // test2: Extra allocation between extracting closures and applying them.
  // Expected: 999 + 100 + 100 + 100 = 1299.
  auto r2 = ACC::test2;
  std::cout << "test2 = " << r2 << " (expected 1299)" << std::endl;
  assert(r2 == 1299u);

  std::cout << "All accum_closure_capture tests passed!" << std::endl;
  return 0;
}
