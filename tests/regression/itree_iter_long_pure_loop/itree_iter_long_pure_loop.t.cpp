#include "itree_iter_long_pure_loop.h"
#include <cassert>

int main() {
  using M = ItreeIterLongPureLoop;
  assert(M::count_down(UINT64_C(1000000))->run() == 0);
  assert(M::after_taus(UINT64_C(1000000))->run() == 1);
  return 0;
}
