#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <unit_type.h>
#include <utility>
#include <variant>

unit UnitType::return_unit(const unsigned int _x) { return unit::tt; }

unsigned int UnitType::take_unit(const unit _x) { return 5u; }

unsigned int UnitType::match_unit(const unit u) {
  return [&](void) {
    switch (u) {
    case unit::tt: {
      return 7u;
    }
    }
  }();
}

unit UnitType::unit_to_unit(const unit u) { return u; }
