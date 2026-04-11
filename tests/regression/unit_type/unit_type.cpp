#include <unit_type.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

void UnitType::return_unit(const unsigned int _x) { return; }

__attribute__((pure)) unsigned int
UnitType::take_unit(const std::monostate _x) {
  return 5u;
}

__attribute__((pure)) unsigned int
UnitType::match_unit(const std::monostate u) {
  {
    return 7u;
  }
}

void UnitType::unit_to_unit(const std::monostate u) { return; }
