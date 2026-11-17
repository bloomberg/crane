#include <local_mutual_callable_param_capture.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LocalMutualCallableParamCapture;

int main() {
  // f n is h 0 = 3 at 0 and g (n-1) + k past it; g n is h 1 = 4 at 0 and
  // f (n-1) past it.
  const uint64_t want[] = {3, 5, 4, 6, 5, 7};
  for (uint64_t n = 0; n < 6; n++)
    assert(M::run(1, n) == want[n]);
  std::cout << "run 1 5 = " << M::run(1, 5) << " (want 7)" << std::endl;
  return 0;
}
