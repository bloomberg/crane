#include <nested_eponymous_type.h>

#include <cassert>

int main() {
  assert(NestedEponymousType::use(Compare<Nat>::lt()) == true);
  return 0;
}
