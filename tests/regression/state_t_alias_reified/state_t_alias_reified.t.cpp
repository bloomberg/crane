#include "state_t_alias_reified.h"
#include <cassert>

int main() {
  using M = StateTAliasReified;
  auto r = M::run(UINT64_C(3))->run();
  assert(r.first == 5);
  assert(r.second == 7);
  assert(M::seeded(UINT64_C(1))->run() == 9);
  return 0;
}
