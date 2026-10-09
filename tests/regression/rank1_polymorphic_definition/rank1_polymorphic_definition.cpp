#include "rank1_polymorphic_definition.h"

crane::obj
Rank1PolymorphicDefinition::three(const crane::fn<crane::obj(crane::obj)> &f,
                                  crane::obj x) {
  return f(f(f(x)));
}

uint64_t
Rank1PolymorphicDefinition::to_nat(Rank1PolymorphicDefinition::church c) {
  static const auto erased_fn =
      crane::immortal(crane_erase_fn([](uint64_t x) { return (x + 1); }));
  return crane::any_cast<uint64_t>(c(erased_fn, UINT64_C(0)));
}

bool Rank1PolymorphicDefinition::to_bool(Rank1PolymorphicDefinition::church c) {
  static const auto erased_fn =
      crane::immortal(crane_erase_fn([](bool _x0) -> bool { return !(_x0); }));
  return crane::any_cast<bool>(c(erased_fn, false));
}
