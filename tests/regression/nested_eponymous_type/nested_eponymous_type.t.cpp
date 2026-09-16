#include <nested_eponymous_type.h>

#include <cassert>

int main() {
  assert(NestedEponymousType::use(Nat::o(), Nat::o(), Compare<Nat>::lt()) ==
         true);
  return 0;
}
