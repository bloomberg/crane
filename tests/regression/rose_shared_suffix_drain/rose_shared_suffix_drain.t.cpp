#include <rose_shared_suffix_drain.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // t = [Node 5 []; Node 6 []; Node 7 []], so rsum over t is 5 + 6 + 7 = 18.
  // a = rsum (Node 1 t) = 1 + 18 = 19
  // b = rsum (Node 2 t) = 2 + 18 = 20
  // a + b = 39
  const uint64_t r = RoseSharedSuffixDrain::run(UINT64_C(5));
  std::cout << "run(5) = " << r << std::endl;
  assert(r == UINT64_C(39));
  return 0;
}
