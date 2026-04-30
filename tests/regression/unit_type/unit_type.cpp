#include <unit_type.h>

void UnitType::return_unit(const unsigned int &) { return; }

unsigned int UnitType::take_unit(const std::monostate &) { return 5u; }

unsigned int UnitType::match_unit(const std::monostate &) {
  {
    return 7u;
  }
}

void UnitType::unit_to_unit(std::monostate) { return; }
