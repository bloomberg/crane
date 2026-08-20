#include <rose_shared_suffix_drain_size.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // t has four leaf roses, so rsize (Node k t) = 1 + 4 = 5 for each k.
  // a + b + c = 15
  const uint64_t r = RoseSharedSuffixDrainSize::run(UINT64_C(5));
  std::cout << "run(5) = " << r << std::endl;
  assert(r == UINT64_C(15));
  return 0;
}
