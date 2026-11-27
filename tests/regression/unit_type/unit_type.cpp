#include "unit_type.h"

void UnitType::return_unit(uint64_t) {}

uint64_t UnitType::take_unit() { return UINT64_C(5); }

uint64_t UnitType::match_unit() { return UINT64_C(7); }

void UnitType::unit_to_unit() {}
