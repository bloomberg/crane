#include "erased_enum_switch.h"

Nat ErasedEnumSwitch::run(const ErasedEnumSwitch::dep &d) {
  const auto &[a, a1] = d;
  return a1(a);
}
