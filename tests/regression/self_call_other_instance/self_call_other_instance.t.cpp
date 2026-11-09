#include <self_call_other_instance.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = SelfCallOtherInstance;

int main() {
  // run 0 is the list's length; past it f goes on at bool and ends in the
  // lambda's 10.
  assert(M::run(0) == 3);
  for (uint64_t n = 1; n < 32; n++)
    assert(M::run(n) == 10);
  std::cout << "run 7 = " << M::run(7) << " (want 10)" << std::endl;
  return 0;
}
