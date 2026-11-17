#include <tt_at_computed_type.h>
#include <cassert>

using M = TtAtComputedType;

int main() {
  assert(M::first == 1);
  assert(M::second == 1);
  return 0;
}
