#include "rc_policy_names_every_block.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <cassert>
#include <type_traits>

static_assert(!crane::rc_is_atomic);
static_assert(std::is_same_v<crane::fn<int(int)>, crane::rc_local::fn<int(int)>>);
static_assert(std::is_same_v<crane::obj, crane::rc_local::obj>);
static_assert(std::is_same_v<crane::lazy<int>, crane::rc_local::lazy<int>>);

int main() {
  using M = RcPolicyNamesEveryBlock;
  assert(M::hd(M::from(3)) == 3);
  assert(M::twice([](uint64_t x) { return x + 2; }, 1) == 5);
  return 0;
}
