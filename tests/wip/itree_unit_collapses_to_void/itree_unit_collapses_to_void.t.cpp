#include <itree_unit_collapses_to_void.h>

#include <cassert>

int main() {
  // The point is that [prog] has a tree at all: [put]'s effect must reach it
  // rather than being built and dropped inside a [void] call.
  auto t = ItreeUnitCollapsesToVoid::prog();
  assert(t);
  return 0;
}
