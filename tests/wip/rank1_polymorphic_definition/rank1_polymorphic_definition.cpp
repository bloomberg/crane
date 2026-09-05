#include "rank1_polymorphic_definition.h"

uint64_t
Rank1PolymorphicDefinition::to_nat(Rank1PolymorphicDefinition::church c) {
  return c([](uint64_t x) { return (x + 1); }, UINT64_C(0));
}

bool Rank1PolymorphicDefinition::to_bool(Rank1PolymorphicDefinition::church c) {
  return c([](bool _x0) -> bool { return !(_x0); }, false);
}
