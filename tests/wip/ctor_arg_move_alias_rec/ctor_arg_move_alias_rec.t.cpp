#include <ctor_arg_move_alias_rec.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  // In Rocq: annotate [I 1; I 2] = [I 1; I 3; I 2; I 2], so run 1 = 8.
  //
  // The extracted C++ builds each cell with
  //   mycons(std::move(a0), mycons(icons(osum(o), inil()), annotate(*a1)))
  // where a0 is a reference into o.  The move and osum(o) are unsequenced,
  // so osum may walk o after its head element has been moved from, and a
  // moved-from `inner` carries a null tail pointer.
  auto r = CtorArgMoveAliasRec::run(UINT64_C(1));
  std::cout << "run(1) = " << r << std::endl;
  assert(r == 8);

  return 0;
}
