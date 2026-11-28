#include <twice_curried_slot_flat_args.h>

#include <cassert>

int main() {
  using M = TwiceCurriedSlotFlatArgs;
  assert(M::d == 4);
  return 0;
}
