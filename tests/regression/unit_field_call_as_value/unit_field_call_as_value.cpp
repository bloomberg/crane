#include "unit_field_call_as_value.h"

std::pair<Nat, std::monostate> UnitFieldCallAsValue::update(const Nat &gs) {
  return std::make_pair(gs, [&]() {
    globals_object.globals_set(gs);
    return std::monostate{};
  }());
}
