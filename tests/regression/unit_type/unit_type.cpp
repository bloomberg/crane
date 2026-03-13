#include <unit_type.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) Unit UnitType::return_unit(const unsigned int _x) {
  return Unit::e_TT;
}

__attribute__((pure)) unsigned int UnitType::take_unit(const Unit _x) {
  return 5u;
}

__attribute__((pure)) unsigned int UnitType::match_unit(const Unit u) {
  return [&](void) {
    switch (u) {
    case Unit::e_TT: {
      return 7u;
    }
    }
  }();
}

__attribute__((pure)) Unit UnitType::unit_to_unit(const Unit u) { return u; }
