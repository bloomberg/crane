#include "nullary_unit_effect_dropped.h"
#include <cassert>

int main() {
  try {
    NullaryUnitEffectDropped::f(Unit::TT);
  } catch (int) {
    return 0;
  }
  assert(false && "f returned instead of throwing");
}
