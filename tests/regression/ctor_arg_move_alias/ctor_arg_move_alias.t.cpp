#include <ctor_arg_move_alias.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // In Rocq: o = [ICons 1 (ICons 2 INil)], osum o = 3, isum h = 3,
  // so run 1 = 3 + 3 = 6.
  //
  // The extracted C++ builds the result with
  //   pack::pack0(std::move(a0), osum(o))
  // where a0 is a reference into o.  The two arguments are unsequenced, so
  // osum(o) may observe o's head element after it has been moved from.  A
  // moved-from `inner` still reports the ICons alternative but holds a null
  // tail pointer, so isum dereferences null.
  auto r = CtorArgMoveAlias::run(UINT64_C(1));
  std::cout << "run(1) = " << r << std::endl;
  assert(r == 6);

  return 0;
}
