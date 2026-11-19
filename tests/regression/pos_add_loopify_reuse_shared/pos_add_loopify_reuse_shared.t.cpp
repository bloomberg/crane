// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <pos_add_loopify_reuse_shared.h>

#include <cstdint>
#include <initializer_list>
#include <iostream>

#define M PosAddLoopifyReuseShared

// pos_add x y adds x + 1 and y + 1, pos_add_carry one more; n_add adds x
// and y.  Each is checked against the machine's own sum.
static int check(uint64_t x, uint64_t y) {
  int fails = 0;
  if (M::pos_add(x, y) != x + y + 2) {
    std::cout << "FAIL: pos_add " << x << " " << y << std::endl;
    ++fails;
  }
  if (M::pos_add_carry(x, y) != x + y + 3) {
    std::cout << "FAIL: pos_add_carry " << x << " " << y << std::endl;
    ++fails;
  }
  if (M::n_add(x, y) != x + y) {
    std::cout << "FAIL: n_add " << x << " " << y << std::endl;
    ++fails;
  }
  return fails;
}

int main() {
  int fails = 0;
  if (!(M::a == 28)) { std::cout << "FAIL: M::a" << std::endl; ++fails; }
  if (!(M::b == 28)) { std::cout << "FAIL: M::b" << std::endl; ++fails; }
  if (!(M::c == 2)) { std::cout << "FAIL: M::c" << std::endl; ++fails; }
  if (!(M::d == 29)) { std::cout << "FAIL: M::d" << std::endl; ++fails; }
  if (!(M::e == 256)) { std::cout << "FAIL: M::e" << std::endl; ++fails; }
  if (!(M::f == 2048)) { std::cout << "FAIL: M::f" << std::endl; ++fails; }

  for (uint64_t x = 0; x < 70; ++x)
    for (uint64_t y = 0; y < 70; ++y)
      fails += check(x, y);
  for (uint64_t x : {UINT64_C(1022), UINT64_C(4095), UINT64_C(65534)})
    for (uint64_t y : {UINT64_C(0), UINT64_C(1), UINT64_C(4096), x})
      fails += check(x, y);

  if (fails == 0) std::cout << "All pos_add_loopify_reuse_shared tests passed!" << std::endl;
  return fails;
}
