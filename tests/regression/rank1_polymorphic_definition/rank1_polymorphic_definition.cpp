#include "rank1_polymorphic_definition.h"

crane::obj
Rank1PolymorphicDefinition::three(crane::fn<crane::obj(crane::obj)> f,
                                  crane::obj x) {
  return f(f(f(x)));
}

uint64_t
Rank1PolymorphicDefinition::to_nat(Rank1PolymorphicDefinition::church c) {
  return crane::any_cast<uint64_t>(
      c(crane_erase_fn([](uint64_t x) { return (x + 1); }), UINT64_C(0)));
}

bool Rank1PolymorphicDefinition::to_bool(Rank1PolymorphicDefinition::church c) {
  return crane::any_cast<bool>(
      c(crane_erase_fn([](bool _x0) -> bool { return !(_x0); }), false));
}
